theory ElabTerm
  imports ElabType Unify ElabPattern "../core/TypeSubstTerm"
begin

(* Convert BabUnop to CoreUnop *)
fun unop_to_core :: "BabUnop \<Rightarrow> CoreUnop" where
  "unop_to_core BabUnop_Negate = CoreUnop_Negate"
| "unop_to_core BabUnop_Complement = CoreUnop_Complement"
| "unop_to_core BabUnop_Not = CoreUnop_Not"

(* Default type for unary operators when the operand type is ambiguous (a unifiable variable).
   Negate and Complement default to i32, Not defaults to Bool. *)
fun default_type_for_unop :: "CoreUnop \<Rightarrow> CoreType" where
  "default_type_for_unop CoreUnop_Negate = CoreTy_FiniteInt Signed IntBits_32"
| "default_type_for_unop CoreUnop_Complement = CoreTy_FiniteInt Signed IntBits_32"
| "default_type_for_unop CoreUnop_Not = CoreTy_Bool"

lemma default_type_for_unop_is_runtime: "is_runtime_type env (default_type_for_unop op)"
  by (cases op) simp_all

lemma default_type_for_unop_is_well_kinded: "is_well_kinded env (default_type_for_unop op)"
  by (cases op) simp_all


(* Resolve type arguments for a polymorphic entity (function or data constructor).
   If the user omitted type arguments and there are type parameters, generate fresh metavariables.
   If the user provided type arguments, elaborate them and check the arity.
   Returns the elaborated type arguments and the updated next_mv counter. *)
definition resolve_type_args ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> string
   \<Rightarrow> string list \<Rightarrow> BabType list \<Rightarrow> nat
   \<Rightarrow> TypeError list + (CoreType list \<times> nat)" where
  "resolve_type_args env elabEnv ghost loc name tyvars tyArgs next_mv =
    (let numTyParams = length tyvars in
     if tyArgs = [] \<and> numTyParams > 0 then
       \<comment> \<open>Generate fresh metavariables for the type arguments\<close>
       Inr (mv_block next_mv (next_mv + numTyParams), next_mv + numTyParams)
     else if numTyParams = length tyArgs then
       \<comment> \<open>Elaborate the user's provided type arguments\<close>
       (case elab_type_list env elabEnv ghost tyArgs of
           Inl errs \<Rightarrow> Inl errs
         | Inr newTyArgs \<Rightarrow>
             \<comment> \<open>Type arguments may only be instantiated at complete types\<close>
             if \<not> list_all is_complete_type newTyArgs
             then Inl [TyErr_IncompleteTypeArgument loc]
             else Inr (newTyArgs, next_mv))
     else
       Inl [TyErr_WrongNumberOfTypeArgs loc name numTyParams (length tyArgs)])"


(* Information about a resolved callee: either a function or a data constructor. *)
datatype CalleeInfo =
  \<comment> \<open>Function call: fnName, tyArgs (pre-subst), retType (pre-subst)\<close>
  CI_Function string "CoreType list" CoreType
  \<comment> \<open>Data constructor call: ctorName, dtName, tyArgs (pre-subst)\<close>
| CI_DataCtor string string "CoreType list"


(* Resolve a function callee. Checks purity, ghost, resolves type args,
   and computes expected argument types. *)
definition resolve_callee_function ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> string \<Rightarrow> BabType list \<Rightarrow> nat
   \<Rightarrow> TypeError list + (string \<times> CoreType list \<times> CalleeInfo \<times> nat)" where
  "resolve_callee_function env elabEnv ghost loc name tyArgs next_mv =
    (case fmlookup (TE_Functions env) name of
      Some funInfo \<Rightarrow>
        \<comment> \<open>A desugared ghost constant is not callable: `c` is a constant, not a
            function (the same error as \"calling\" a local variable).\<close>
        if name |\<in>| EE_GhostConstants elabEnv then
          Inl [TyErr_CalleeNotFunction loc]
        else if name |\<in>| EE_VoidFunctions elabEnv then
          Inl [TyErr_FunctionNoReturnType loc name]
        else if FI_Impure funInfo then
          Inl [TyErr_ImpureFunctionInTermContext loc name]
        else if \<not> list_all (\<lambda>(_, vor, _). vor = Var) (FI_TmArgs funInfo) then
          Inl [TyErr_RefArgInTermContext loc name]
        else if ghost = NotGhost \<and> FI_Ghost funInfo = Ghost then
          Inl [TyErr_GhostFunctionInNonGhost loc name]
        else
          (case resolve_type_args env elabEnv ghost loc name (FI_TyArgs funInfo) tyArgs next_mv of
            Inl errs \<Rightarrow> Inl errs
          | Inr (newTyArgs, next_mv') \<Rightarrow>
              let subst = fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs);
                  expArgTypes = map (\<lambda>(ty, _). apply_subst subst ty) (FI_TmArgs funInfo);
                  retType = apply_subst subst (FI_ReturnType funInfo)
              in Inr (name, expArgTypes, CI_Function name newTyArgs retType, next_mv'))
    | None \<Rightarrow> Inl [TyErr_NameNotFound loc name])"


(* Resolve a data constructor callee. Checks ghost, rejects payload-less
   constructors (which are not callable), resolves type args, and expects
   exactly one argument, of the payload type. *)
definition resolve_callee_data_ctor ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> string \<Rightarrow> BabType list \<Rightarrow> nat
   \<Rightarrow> TypeError list + (string \<times> CoreType list \<times> CalleeInfo \<times> nat)" where
  "resolve_callee_data_ctor env elabEnv ghost loc name tyArgs next_mv =
    (case fmlookup (TE_DataCtors env) name of
      Some (dtName, tyvars, payloadTy) \<Rightarrow>
        if ghost = NotGhost \<and> dtName |\<in>| TE_GhostDatatypes env then
          Inl [TyErr_GhostVariableInNonGhost loc name]
        else if name |\<in>| EE_NullaryDataCtors elabEnv then
          Inl [TyErr_DataCtorNotCallable loc name]
        else
          (case resolve_type_args env elabEnv ghost loc name tyvars tyArgs next_mv of
            Inl errs \<Rightarrow> Inl errs
          | Inr (newTyArgs, next_mv') \<Rightarrow>
              let subst = fmap_of_list (zip tyvars newTyArgs);
                  expArgTypes = [apply_subst subst payloadTy]
              in Inr (name, expArgTypes, CI_DataCtor name dtName newTyArgs, next_mv'))
    | None \<Rightarrow> Inl [TyErr_NameNotFound loc name])"


(* Resolve the callee of a call expression.
   Dispatches to data constructor or function resolution.
   Returns: (calleeName, expArgTypes, calleeInfo, next_mv'). *)
definition resolve_callee ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> BabTerm \<Rightarrow> nat
   \<Rightarrow> TypeError list + (string \<times> CoreType list \<times> CalleeInfo \<times> nat)" where
  "resolve_callee env elabEnv ghost callee next_mv =
    (case callee of
      BabTm_Name loc name tyArgs \<Rightarrow>
        (case fmlookup (TE_DataCtors env) name of
          Some _ \<Rightarrow> resolve_callee_data_ctor env elabEnv ghost loc name tyArgs next_mv
        | None \<Rightarrow> resolve_callee_function env elabEnv ghost loc name tyArgs next_mv)
    | _ \<Rightarrow> Inl [TyErr_CalleeNotFunction (bab_term_location callee)])"


(* ========================================================================== *)
(* Ghost arguments of executable calls *)
(* ========================================================================== *)

(* In an executable call, the argument of a ghost parameter is ghost code. It
   is elaborated in Ghost mode, and it is checked against the type of its
   parameter without being allowed to determine the type arguments of the call
   (which are runtime data). These are the "special" arguments of the call; all
   other arguments are "plain".

   call_special_flags gives one flag for each argument of a call: True if the
   argument is special. n is the number of arguments. In ghost code no argument
   is special. Data constructors do not have ghost parameters. *)
definition call_special_flags :: "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> BabTerm \<Rightarrow> nat \<Rightarrow> bool list" where
  "call_special_flags env ghost callee n =
    (case callee of
       BabTm_Name _ name _ \<Rightarrow>
         (case fmlookup (TE_DataCtors env) name of
            Some _ \<Rightarrow> replicate n False
          | None \<Rightarrow>
              (case fmlookup (TE_Functions env) name of
                 Some funInfo \<Rightarrow>
                   map (\<lambda>(_, _, gh). ghost = NotGhost \<and> gh = Ghost) (FI_TmArgs funInfo)
               | None \<Rightarrow> replicate n False))
     | _ \<Rightarrow> replicate n False)"

(* Split a list by flags: the elements whose flag is False, and the elements
   whose flag is True. *)
fun plain_args :: "bool list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "plain_args (f # fs) (x # xs) = (if f then plain_args fs xs else x # plain_args fs xs)"
| "plain_args [] xs = xs"
| "plain_args fs [] = []"

fun special_args :: "bool list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "special_args (f # fs) (x # xs) = (if f then x # special_args fs xs else special_args fs xs)"
| "special_args _ _ = []"

(* Put the two parts back together, in the original order. *)
fun merge_args :: "bool list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "merge_args (True # fs) ps (s # ss) = s # merge_args fs ps ss"
| "merge_args (False # fs) (p # ps) ss = p # merge_args fs ps ss"
| "merge_args [] ps ss = ps"
| "merge_args _ _ _ = []"

(* The parts are no bigger than the whole (for the termination of elab_term). *)
lemma size_list_plain_args_le:
  "size_list f (plain_args fs xs) \<le> size_list f xs"
  by (induction fs xs rule: plain_args.induct) auto

lemma size_list_special_args_le:
  "size_list f (special_args fs xs) \<le> size_list f xs"
  by (induction fs xs rule: special_args.induct) auto


(* Build the final term and type from a resolved callee and coerced arguments. *)
definition build_call_result ::
  "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> CalleeInfo \<Rightarrow> TypeSubst \<Rightarrow> CoreTerm list
   \<Rightarrow> CoreTerm \<times> CoreType" where
  "build_call_result env ghost loc ci finalSubst finalArgTms =
    (case ci of
      CI_Function fnName tyArgs retType \<Rightarrow>
        let finalTyArgs = map (apply_subst finalSubst) tyArgs;
            finalRetType = apply_subst finalSubst retType
        in (CoreTm_FunctionCall fnName finalTyArgs finalArgTms, finalRetType)
    | CI_DataCtor ctorName dtName tyArgs \<Rightarrow>
        let finalTyArgs = map (apply_subst finalSubst) tyArgs
        in (CoreTm_VariantCtor ctorName finalTyArgs (hd finalArgTms),
            CoreTy_Datatype dtName finalTyArgs))"


(* ========================================================================== *)
(* Type checking (unification and implicit coercions) *)
(* ========================================================================== *)

(* When type unification fails, the elaborator may still bridge the gap with an
   inserted cast. The following predicate defines when this is allowed.
   Currently includes:
    - conversions from one finite integer type to another;
    - conversions between array types (see `array_cast_ok`).
*)
definition coercible :: "CoreType \<Rightarrow> CoreType \<Rightarrow> bool" where
  "coercible actualTy expectedTy =
    (is_finite_integer_type actualTy \<and> is_finite_integer_type expectedTy
     \<or> array_cast_ok actualTy expectedTy)"

(* Convert `tm`, of type actualTy, to expectedTy. Returns the term itself if the two
   types already agree, otherwise a CoreTm_Cast to expectedTy. Only meaningful when
   actualTy = expectedTy \<or> coercible actualTy expectedTy. *)
definition insert_cast :: "CoreType \<Rightarrow> CoreType \<Rightarrow> CoreTerm \<Rightarrow> CoreTerm" where
  "insert_cast actualTy expectedTy tm =
    (if actualTy = expectedTy then tm else CoreTm_Cast expectedTy tm)"

(* Unify two types, ignoring the dimensions of a top-level array type on each side.
   Used in the implementation of unify_upto_coercion. *)
fun unify_modulo_array_dims :: "(string \<Rightarrow> bool) \<Rightarrow> CoreType \<Rightarrow> CoreType \<Rightarrow> TypeSubst option" where
  "unify_modulo_array_dims is_flex (CoreTy_Array elemTy1 dims1) (CoreTy_Array elemTy2 dims2) =
     unify is_flex elemTy1 elemTy2"
| "unify_modulo_array_dims is_flex ty1 ty2 = unify is_flex ty1 ty2"

(* Unify two types, up to a possible implicit coercion between them.
   If a substitution \<theta> exists such that \<theta>(actualTy) and \<theta>(expectedTy) are either equal or
   coercible, then return it; otherwise, return None.
   (See also theorems unify_upto_coercion_sound and unify_upto_coercion_complete
   in ElabTermCorrectHelpers.thy.) *)
definition unify_upto_coercion :: "(string \<Rightarrow> bool) \<Rightarrow> CoreType \<Rightarrow> CoreType \<Rightarrow> TypeSubst option" where
  "unify_upto_coercion is_flex actualTy expectedTy =
    (let subst = (case unify_modulo_array_dims is_flex actualTy expectedTy of
                    Some s \<Rightarrow> s
                  | None \<Rightarrow> fmempty)
     in if apply_subst subst actualTy = apply_subst subst expectedTy
           \<or> coercible (apply_subst subst actualTy) (apply_subst subst expectedTy)
        then Some subst
        else None)"

(* Unify a list of actual types with expected types, pairwise.
   For each pair, calls unify_upto_coercion, accumulating the substitution.
   (Casts can be inserted later by apply_call_coercions if needed.)

   Errors are reported at the location of the offending pair: locOf maps a
   pair's index to its source location, and the nat parameter is the index of
   the first pair in the lists.

   A metavariable is never bound to an incomplete type. Violations of this
   rule are reported as TyErr_IncompleteTypeArgument. *)
fun unify_type_lists :: "(string \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> Location) \<Rightarrow> nat
                        \<Rightarrow> CoreType list \<Rightarrow> CoreType list
                        \<Rightarrow> TypeSubst \<Rightarrow> TypeError list + TypeSubst" where
  "unify_type_lists is_flex locOf idx [] [] accSubst = Inr accSubst"
| "unify_type_lists is_flex locOf idx (actualTy # actualTys) (expectedTy # expectedTys) accSubst =
    (let actualTy' = apply_subst accSubst actualTy;
         expectedTy' = apply_subst accSubst expectedTy
     in case unify_upto_coercion is_flex actualTy' expectedTy' of
       Some newSubst \<Rightarrow>
         \<comment> \<open>Ensure that unification didn't bind a metavar to an incomplete type\<close>
         if \<not> typesubst_complete newSubst
         then Inl [TyErr_IncompleteTypeArgument (locOf idx)]
         else unify_type_lists is_flex locOf (idx + 1) actualTys expectedTys
                (compose_subst newSubst accSubst)
     | None \<Rightarrow> Inl [TyErr_TypeMismatch (locOf idx) expectedTy' actualTy'])"
| "unify_type_lists _ _ _ _ _ _ = undefined"

(* After a successful call to unify_type_lists, this applies the substitution
   to each term, and inserts casts if required. *)
fun apply_call_coercions :: "TypeSubst \<Rightarrow> CoreTerm list \<Rightarrow> CoreType list \<Rightarrow> CoreType list
                            \<Rightarrow> CoreTerm list" where
  "apply_call_coercions subst [] [] [] = []"
| "apply_call_coercions subst (tm # tms) (actualTy # actualTys) (expectedTy # expectedTys) =
    (insert_cast (apply_subst subst actualTy) (apply_subst subst expectedTy)
                 (apply_subst_to_term subst tm)
     # apply_call_coercions subst tms actualTys expectedTys)"
| "apply_call_coercions _ _ _ _ = undefined"

(* Combine unify_type_lists and apply_call_coercions into a single function.
   This is the main entry point for type checking.
   Given a list of terms and their actual types, along with the expected types, this
   applies both unification and implicit casting to make the terms match the expected
   types.
   On success, returns the new terms (with type substitutions and/or implicit casts applied),
   and the final substitution. On failure, returns a list of type errors. *)
definition unify_and_coerce :: "(string \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> Location)
                              \<Rightarrow> CoreTerm list \<Rightarrow> CoreType list
                              \<Rightarrow> CoreType list \<Rightarrow> TypeSubst
                              \<Rightarrow> TypeError list + (CoreTerm list \<times> TypeSubst)" where
  "unify_and_coerce is_flex locOf tms actualTys expectedTys accSubst =
    (case unify_type_lists is_flex locOf 0 actualTys expectedTys accSubst of
       Inl errs \<Rightarrow> Inl errs
     | Inr finalSubst \<Rightarrow> Inr (apply_call_coercions finalSubst tms actualTys expectedTys, finalSubst))"

(* Type-check the arguments of a call, once they have been elaborated, and build
   the result.

   The plain arguments are unified with their parameter types in the usual way.
   This is what determines the type arguments of the call.

   Then the special arguments (see call_special_flags) are checked as a closed
   unit. They were elaborated after the plain arguments, with the metavariable
   counter going from lo to hi, so the metavariables in [lo, hi) are exactly
   the ones they created. Only those are flexible when a special argument is
   unified with its parameter type. So a special argument can be checked
   against the type arguments of the call, but cannot determine them. The
   substitution found is applied to the special arguments only, and none of
   their own metavariables may remain afterwards.

   (Note: The reason for the split between "plain" and "special" arguments is as follows.
   If ghost arguments were allowed to influence the inferred type of a NotGhost call, then
   a function f<T>(ghost x: T), called as f(int(1)), would be inferred as f<int>; but the
   type arguments to NotGhost functions must be runtime (int is not a runtime type). There
   are ways to work around this, but the simplest solution is just to ban ghost parameters
   from affecting the type inference entirely.)
*)
definition finish_call ::
  "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> BabTerm list \<Rightarrow> bool list \<Rightarrow> CoreType list
   \<Rightarrow> CalleeInfo \<Rightarrow> CoreTerm list \<Rightarrow> CoreType list \<Rightarrow> nat
   \<Rightarrow> CoreTerm list \<Rightarrow> CoreType list \<Rightarrow> nat
   \<Rightarrow> TypeError list + (CoreTerm \<times> CoreType)" where
  "finish_call env ghost loc args flags expArgTypes calleeInfo
               plainTms plainTys lo specialTms specialTys hi =
    (case unify_and_coerce (\<lambda>n. n |\<notin>| TE_TypeVars env)
            (\<lambda>idx. bab_term_location (plain_args flags args ! idx))
            plainTms plainTys (plain_args flags expArgTypes) fmempty of
       Inl errs \<Rightarrow> Inl errs
     | Inr (plainFinal, finalSubst) \<Rightarrow>
         (case unify_and_coerce (\<lambda>n. n |\<in>| mv_fset lo hi)
                 (\<lambda>idx. bab_term_location (special_args flags args ! idx))
                 specialTms specialTys
                 (map (apply_subst finalSubst) (special_args flags expArgTypes)) fmempty of
            Inl errs \<Rightarrow> Inl errs
          | Inr (specialFinal, _) \<Rightarrow>
              if \<not> list_all (\<lambda>tm. list_all (\<lambda>n. n |\<notin>| mv_fset lo hi)
                                           (core_term_free_tyvars_list tm))
                            specialFinal
              then Inl [TyErr_CannotInferType loc]
              else Inr (build_call_result env ghost loc calleeInfo finalSubst
                          (merge_args flags plainFinal specialFinal))))"


(* ========================================================================== *)
(* Binary operator helpers *)
(* ========================================================================== *)

(* Coerce two terms to a common integer type by inserting implicit casts if needed.
   Used for binops and for if/then/else terms.
   Only applies when both types are CoreTy_FiniteInt (returns None otherwise). *)
fun coerce_to_common_int_type :: "CoreTerm \<Rightarrow> CoreType \<Rightarrow> CoreTerm \<Rightarrow> CoreType
                                  \<Rightarrow> (CoreTerm \<times> CoreTerm \<times> CoreType) option" where
  "coerce_to_common_int_type tm1 (CoreTy_FiniteInt sign1 bits1)
                             tm2 (CoreTy_FiniteInt sign2 bits2) =
    (case combine_int_types_u64 sign1 bits1 sign2 bits2 of
      (commonSign, commonBits) \<Rightarrow>
        let commonTy1 = CoreTy_FiniteInt commonSign commonBits;
            commonTy2 = CoreTy_FiniteInt commonSign commonBits;
            \<comment> \<open>Only wrap in cast if type differs from common type\<close>
            newTm1 = (if sign1 = commonSign \<and> bits1 = commonBits then tm1
                      else CoreTm_Cast commonTy1 tm1);
            newTm2 = (if sign2 = commonSign \<and> bits2 = commonBits then tm2
                      else CoreTm_Cast commonTy2 tm2)
        in Some (newTm1, newTm2, commonTy1))"
| "coerce_to_common_int_type _ _ _ _ = None"

(* Helper for binary operator elaboration: check that both operands satisfy a type predicate,
   then either use them directly (if same type) or try coercion to a common int type.
   - type_pred: the predicate both operand types must satisfy
   - resultTyOverride: if None, the result type is the (common) operand type;
                        if Some ty, the result type is always ty (e.g. Bool for ordering ops)
   - errMsg: the error constructor to use when the type predicate fails (applied to the
             offending operand type) *)
definition check_and_coerce_binop ::
  "(CoreType \<Rightarrow> bool) \<Rightarrow> CoreType option
    \<Rightarrow> (Location \<Rightarrow> CoreType \<Rightarrow> TypeError)
    \<Rightarrow> CoreBinop \<Rightarrow> CoreTerm \<Rightarrow> CoreType \<Rightarrow> CoreTerm \<Rightarrow> CoreType
    \<Rightarrow> Location \<Rightarrow> BabBinop
    \<Rightarrow> TypeError list + (CoreTerm \<times> CoreType)" where
  "check_and_coerce_binop type_pred resultTyOverride errMsg cop
      lhsTm lhsTy rhsTm rhsTy loc babOp =
    (if type_pred lhsTy \<and> type_pred rhsTy then
       if lhsTy = rhsTy then
         let resTy = (case resultTyOverride of None \<Rightarrow> lhsTy | Some ty \<Rightarrow> ty)
         in Inr (CoreTm_Binop cop lhsTm rhsTm, resTy)
       else
         (case coerce_to_common_int_type lhsTm lhsTy rhsTm rhsTy of
           Some (newLhs, newRhs, commonTy) \<Rightarrow>
             let resTy = (case resultTyOverride of None \<Rightarrow> commonTy | Some ty \<Rightarrow> ty)
             in Inr (CoreTm_Binop cop newLhs newRhs, resTy)
         | None \<Rightarrow> Inl [TyErr_BinopCannotCombineTypes loc babOp lhsTy rhsTy])
     else Inl [errMsg loc (if type_pred lhsTy then rhsTy else lhsTy)])"

(* Convert BabBinop to CoreBinop. Returns None for operators that need special handling. *)
fun binop_to_core :: "BabBinop \<Rightarrow> CoreBinop option" where
  "binop_to_core BabBinop_Add = Some CoreBinop_Add"
| "binop_to_core BabBinop_Subtract = Some CoreBinop_Subtract"
| "binop_to_core BabBinop_Multiply = Some CoreBinop_Multiply"
| "binop_to_core BabBinop_Divide = Some CoreBinop_Divide"
| "binop_to_core BabBinop_Modulo = Some CoreBinop_Modulo"
| "binop_to_core BabBinop_BitAnd = Some CoreBinop_BitAnd"
| "binop_to_core BabBinop_BitOr = Some CoreBinop_BitOr"
| "binop_to_core BabBinop_BitXor = Some CoreBinop_BitXor"
| "binop_to_core BabBinop_ShiftLeft = Some CoreBinop_ShiftLeft"
| "binop_to_core BabBinop_ShiftRight = Some CoreBinop_ShiftRight"
| "binop_to_core BabBinop_Equal = Some CoreBinop_Equal"
| "binop_to_core BabBinop_NotEqual = Some CoreBinop_NotEqual"
| "binop_to_core BabBinop_Less = Some CoreBinop_Less"
| "binop_to_core BabBinop_LessEqual = Some CoreBinop_LessEqual"
| "binop_to_core BabBinop_Greater = Some CoreBinop_Greater"
| "binop_to_core BabBinop_GreaterEqual = Some CoreBinop_GreaterEqual"
| "binop_to_core BabBinop_And = Some CoreBinop_And"
| "binop_to_core BabBinop_Or = Some CoreBinop_Or"
| "binop_to_core BabBinop_Implies = Some CoreBinop_Implies"
| "binop_to_core BabBinop_ImpliedBy = None"
| "binop_to_core BabBinop_Iff = None"

(* Check if a term is simple enough to duplicate without let-binding *)
fun is_simple_term :: "CoreTerm \<Rightarrow> bool" where
  "is_simple_term (CoreTm_Var _) = True"
| "is_simple_term (CoreTm_LitBool _) = True"
| "is_simple_term (CoreTm_LitInt _) = True"
| "is_simple_term _ = False"

(* Direction of a comparison operator in a chain.
   Left-pointing: <, <= (ascending chain)
   Right-pointing: >, >= (descending chain)
   Neutral: ==, != (compatible with either direction)
   None: not a comparison operator *)
datatype ChainDirection = ChainLeft | ChainRight | ChainNeutral

fun comparison_direction :: "BabBinop \<Rightarrow> ChainDirection option" where
  "comparison_direction BabBinop_Less = Some ChainLeft"
| "comparison_direction BabBinop_LessEqual = Some ChainLeft"
| "comparison_direction BabBinop_Greater = Some ChainRight"
| "comparison_direction BabBinop_GreaterEqual = Some ChainRight"
| "comparison_direction BabBinop_Equal = Some ChainNeutral"
| "comparison_direction BabBinop_NotEqual = Some ChainNeutral"
| "comparison_direction _ = None"

(* Check if a comparison direction is compatible with a given non-neutral direction *)
fun direction_compatible :: "ChainDirection \<Rightarrow> ChainDirection \<Rightarrow> bool" where
  "direction_compatible ChainNeutral _ = True"
| "direction_compatible _ ChainNeutral = True"
| "direction_compatible ChainLeft ChainLeft = True"
| "direction_compatible ChainRight ChainRight = True"
| "direction_compatible _ _ = False"

(* Check that all operators in a list are comparisons with compatible directions.
   Returns the resolved direction (Left or Right), or None if all neutral. *)
fun check_comparison_chain_directions :: "(BabBinop \<times> 'a \<times> 'b) list \<Rightarrow> ChainDirection \<Rightarrow> bool" where
  "check_comparison_chain_directions [] _ = True"
| "check_comparison_chain_directions ((op, _, _) # rest) accDir =
    (case comparison_direction op of
      None \<Rightarrow> False
    | Some dir \<Rightarrow>
        direction_compatible dir accDir \<and>
        check_comparison_chain_directions rest
          (if dir = ChainNeutral then accDir else dir))"

(* Check that all operators in a list are implies or all are implied-by *)
fun check_implies_chain :: "(BabBinop \<times> 'a \<times> 'b) list \<Rightarrow> bool" where
  "check_implies_chain [] = True"
| "check_implies_chain ((op, _, _) # rest) =
    ((op = BabBinop_Implies \<or> op = BabBinop_ImpliedBy)
     \<and> list_all (\<lambda>(op2, _, _). op2 = op) rest)"

(* Is this a comparison BabBinop? (not implies/implied-by) *)
fun is_comparison_bab_binop :: "BabBinop \<Rightarrow> bool" where
  "is_comparison_bab_binop op = (comparison_direction op \<noteq> None)"

(* Resolve metavariables in binary operator operands using unification.
   1. Try to unify the two operand types.
   2. If unification succeeds, apply the unifier to both operands and use the
      unified type. Any metavariables that remain in the unified type are left
      in place: there is no default type, so an operand type that is still
      unresolved is rejected downstream (by the operator's own operand-type
      check, or by the statement-level "unable to infer type" check).
   3. If unification fails, pass through unchanged (downstream checks will
      report the appropriate type error). A unifier that would bind a
      metavariable to an incomplete array type is treated as a failure too
      (a metavariable is never bound to an incomplete type). *)
fun resolve_binop_metas :: "(string \<Rightarrow> bool)
    \<Rightarrow> CoreTerm \<Rightarrow> CoreType \<Rightarrow> CoreTerm \<Rightarrow> CoreType
    \<Rightarrow> (CoreTerm \<times> CoreType \<times> CoreTerm \<times> CoreType)" where
  "resolve_binop_metas is_flex lhsTm lhsTy rhsTm rhsTy =
    (case unify is_flex lhsTy rhsTy of
       Some unifSubst \<Rightarrow>
         if \<not> typesubst_complete unifSubst then (lhsTm, lhsTy, rhsTm, rhsTy)
         else
         let unifiedTy = apply_subst unifSubst lhsTy
         in (apply_subst_to_term unifSubst lhsTm, unifiedTy,
             apply_subst_to_term unifSubst rhsTm, unifiedTy)
     | None \<Rightarrow> (lhsTm, lhsTy, rhsTm, rhsTy))"

(* Elaborate a single binary operation on already-elaborated operands.
   Handles metavariable resolution, type coercion, and type checking.
   ImpliedBy and Iff are handled before calling this function. *)
fun elab_single_binop :: "(string \<Rightarrow> bool) \<Rightarrow> Location \<Rightarrow> GhostOrNot \<Rightarrow> BabBinop
    \<Rightarrow> CoreTerm \<Rightarrow> CoreType \<Rightarrow> CoreTerm \<Rightarrow> CoreType
    \<Rightarrow> TypeError list + (CoreTerm \<times> CoreType)" where
  "elab_single_binop is_flex loc ghost babOp lhsTm lhsTy rhsTm rhsTy =
    (let (lhsTm', lhsTy', rhsTm', rhsTy') =
           resolve_binop_metas is_flex lhsTm lhsTy rhsTm rhsTy
     in
      case binop_to_core babOp of
        None \<Rightarrow> undefined \<comment> \<open>should not happen\<close>
      | Some cop \<Rightarrow>
        \<comment> \<open>Type-check based on operator category\<close>
        if is_arithmetic_binop cop then
          check_and_coerce_binop is_numeric_type None
            TyErr_NumericTypeRequired cop lhsTm' lhsTy' rhsTm' rhsTy' loc babOp

        else if is_modulo_binop cop then
          check_and_coerce_binop is_integer_type None
            TyErr_IntegerTypeRequired cop lhsTm' lhsTy' rhsTm' rhsTy' loc babOp

        else if is_bitwise_binop cop then
          check_and_coerce_binop is_finite_integer_type None
            TyErr_FiniteIntegerTypeRequired cop lhsTm' lhsTy' rhsTm' rhsTy' loc babOp

        else if is_shift_binop cop then
          \<comment> \<open>Shift: both finite integer, cast RHS to LHS type\<close>
          if is_finite_integer_type lhsTy' \<and> is_finite_integer_type rhsTy' then
            let castRhs = (if lhsTy' = rhsTy' then rhsTm' else CoreTm_Cast lhsTy' rhsTm')
            in Inr (CoreTm_Binop cop lhsTm' castRhs, lhsTy')
          else Inl [TyErr_FiniteIntegerTypeRequired loc
                      (if is_finite_integer_type lhsTy' then rhsTy' else lhsTy')]

        else if is_ordering_binop cop then
          check_and_coerce_binop is_numeric_type (Some CoreTy_Bool)
            TyErr_NumericTypeRequired cop lhsTm' lhsTy' rhsTm' rhsTy' loc babOp

        else if is_eq_neq_binop cop then
          \<comment> \<open>Equality: ghost allows any type, non-ghost requires bool or numeric\<close>
          if lhsTy' = rhsTy' then
            if ghost = Ghost \<or> lhsTy' = CoreTy_Bool \<or> is_numeric_type lhsTy' then
              Inr (CoreTm_Binop cop lhsTm' rhsTm', CoreTy_Bool)
            else Inl [TyErr_EqualityRequiresBoolOrNumeric loc]
          else if is_finite_integer_type lhsTy' \<and> is_finite_integer_type rhsTy' then
            (case coerce_to_common_int_type lhsTm' lhsTy' rhsTm' rhsTy' of
              Some (newLhs, newRhs, _) \<Rightarrow>
                Inr (CoreTm_Binop cop newLhs newRhs, CoreTy_Bool)
            | None \<Rightarrow> Inl [TyErr_BinopCannotCombineTypes loc babOp lhsTy' rhsTy'])
          else Inl [TyErr_BinopCannotCombineTypes loc babOp lhsTy' rhsTy']

        else if is_logical_binop cop then
          \<comment> \<open>Logical: both Bool\<close>
          if lhsTy' = CoreTy_Bool \<and> rhsTy' = CoreTy_Bool then
            Inr (CoreTm_Binop cop lhsTm' rhsTm', CoreTy_Bool)
          else Inl [TyErr_TypeMismatch loc CoreTy_Bool
                      (if lhsTy' \<noteq> CoreTy_Bool then lhsTy' else rhsTy')]

        else undefined)"  \<comment> \<open>should be exhaustive\<close>

(* Elaborate a single binary operation, handling ImpliedBy and Iff specially *)
fun elab_binop_with_special :: "(string \<Rightarrow> bool) \<Rightarrow> Location \<Rightarrow> GhostOrNot \<Rightarrow> BabBinop
    \<Rightarrow> CoreTerm \<Rightarrow> CoreType \<Rightarrow> CoreTerm \<Rightarrow> CoreType
    \<Rightarrow> TypeError list + (CoreTerm \<times> CoreType)" where
  "elab_binop_with_special is_flex loc ghost BabBinop_ImpliedBy lhsTm lhsTy rhsTm rhsTy =
    \<comment> \<open>A <== B becomes B ==> A\<close>
    elab_single_binop is_flex loc ghost BabBinop_Implies rhsTm rhsTy lhsTm lhsTy"
| "elab_binop_with_special is_flex loc ghost BabBinop_Iff lhsTm lhsTy rhsTm rhsTy =
    \<comment> \<open>A <==> B becomes A == B (both must be Bool)\<close>
    (let (lhs', lTy, rhs', rTy) = resolve_binop_metas is_flex lhsTm lhsTy rhsTm rhsTy
     in if lTy = CoreTy_Bool \<and> rTy = CoreTy_Bool
        then Inr (CoreTm_Binop CoreBinop_Equal lhs' rhs', CoreTy_Bool)
        else Inl [TyErr_TypeMismatch loc CoreTy_Bool
                    (if lTy \<noteq> CoreTy_Bool then lTy else rTy)])"
| "elab_binop_with_special is_flex loc ghost op lhsTm lhsTy rhsTm rhsTy =
    elab_single_binop is_flex loc ghost op lhsTm lhsTy rhsTm rhsTy"

(* Process a chain of left-associative binary operations on already-elaborated terms.
   Takes the list of (BabBinop, elaboratedTerm, elaboratedType) triples
   and the accumulated LHS term/type.
   Left-associates: a + b + c becomes (a + b) + c.
*)
fun fold_binop_left :: "(string \<Rightarrow> bool) \<Rightarrow> Location \<Rightarrow> GhostOrNot
    \<Rightarrow> CoreTerm \<Rightarrow> CoreType
    \<Rightarrow> (BabBinop \<times> CoreTerm \<times> CoreType) list
    \<Rightarrow> TypeError list + (CoreTerm \<times> CoreType)" where
  "fold_binop_left is_flex loc ghost accTm accTy [] = Inr (accTm, accTy)"
| "fold_binop_left is_flex loc ghost accTm accTy ((op, rhsTm, rhsTy) # rest) =
    (case elab_binop_with_special is_flex loc ghost op accTm accTy rhsTm rhsTy of
      Inl errs \<Rightarrow> Inl errs
    | Inr (resultTm, resultTy) \<Rightarrow>
        fold_binop_left is_flex loc ghost resultTm resultTy rest)"

(* Check whether a term has any free variable starting with "chain@@"
   other than a single allowed name. Returns True if an unexpected chain variable is found.
   This is used as a runtime check in build_comparison_chain to ensure that the
   let-bound chain@@ variables do not clash with any existing free variables. *)
definition has_unexpected_chain_var :: "CoreTerm \<Rightarrow> string \<Rightarrow> bool" where
  "has_unexpected_chain_var tm allowed =
    (\<exists>v |\<in>| core_term_free_vars tm. take 7 v = ''chain@@'' \<and> v \<noteq> allowed)"

(* Build a comparison chain: a < b < c becomes (a < b) && (b < c).
   Uses let-binding for complex middle terms to avoid duplicate evaluation.
   chainCounter is used to generate unique variable names. *)
fun build_comparison_chain :: "(string \<Rightarrow> bool) \<Rightarrow> Location \<Rightarrow> GhostOrNot \<Rightarrow> nat
    \<Rightarrow> CoreTerm \<Rightarrow> CoreType
    \<Rightarrow> (BabBinop \<times> CoreTerm \<times> CoreType) list
    \<Rightarrow> TypeError list + CoreTerm" where
  "build_comparison_chain is_flex loc ghost chainCtr accTm accTy [] = Inl []"
| "build_comparison_chain is_flex loc ghost chainCtr lhsTm lhsTy ((op, rhsTm, rhsTy) # rest) =
    (let lhsAllowed = (if chainCtr = 0 then '''' else ''chain@@'' @ nat_to_string (chainCtr - 1))
     in if has_unexpected_chain_var lhsTm lhsAllowed
            \<or> has_unexpected_chain_var rhsTm '''' then
       \<comment> \<open>This should be impossible on normal input (parser doesn't allow @@ in names)\<close>
       Inl [TyErr_UnexpectedNameClash loc]
     else
     case rest of
      [] \<Rightarrow>
        \<comment> \<open>Last comparison: just elaborate normally, discard type\<close>
        (case elab_binop_with_special is_flex loc ghost op lhsTm lhsTy rhsTm rhsTy of
          Inl errs \<Rightarrow> Inl errs
        | Inr (cmpTm, _) \<Rightarrow> Inr cmpTm)
    | _ \<Rightarrow>
        \<comment> \<open>More comparisons follow - need to reuse rhsTm as next LHS.
           Resolve metas first (unifying the RHS type with the LHS type) so that
           the RHS type is as resolved as it can be before it is let-bound and
           passed to the next comparison.\<close>
        let (_, _, resolvedRhs, resolvedRhsTy) =
              resolve_binop_metas is_flex lhsTm lhsTy rhsTm rhsTy
        in if is_simple_term resolvedRhs then
          \<comment> \<open>Simple term: duplicate directly, using resolvedRhs in both comparisons\<close>
          (case elab_binop_with_special is_flex loc ghost op lhsTm lhsTy resolvedRhs resolvedRhsTy of
            Inl errs \<Rightarrow> Inl errs
          | Inr (cmpTm, _) \<Rightarrow>
              (case build_comparison_chain is_flex loc ghost chainCtr resolvedRhs resolvedRhsTy rest of
                Inl errs \<Rightarrow> Inl errs
              | Inr restTm \<Rightarrow>
                  Inr (CoreTm_Binop CoreBinop_And cmpTm restTm)))
        else if \<not> list_all (\<lambda>n. \<not> is_flex n) (type_tyvars_list resolvedRhsTy) then
          \<comment> \<open>The RHS is about to be let-bound, and let-bound names must have a
             metavariable-free type (as in BabTm_Let); e.g. `h() < h() < h()` with
             `h<U>(): U` is rejected here.\<close>
          Inl [TyErr_CannotInferType loc]
        else
          \<comment> \<open>Complex term: introduce let-binding, use variable in both comparisons\<close>
          let varName = ''chain@@'' @ nat_to_string chainCtr;
              varTm = CoreTm_Var varName
          in (case elab_binop_with_special is_flex loc ghost op lhsTm lhsTy varTm resolvedRhsTy of
            Inl errs \<Rightarrow> Inl errs
          | Inr (cmpTm, _) \<Rightarrow>
              (case build_comparison_chain is_flex loc ghost (chainCtr + 1) varTm resolvedRhsTy rest of
                Inl errs \<Rightarrow> Inl errs
              | Inr restTm \<Rightarrow>
                  Inr (CoreTm_Let varName resolvedRhs
                        (CoreTm_Binop CoreBinop_And cmpTm restTm)))))"

(* Right-associate an implies chain: a ==> b ==> c becomes a ==> (b ==> c) *)
fun fold_implies_right :: "(string \<Rightarrow> bool) \<Rightarrow> Location \<Rightarrow> GhostOrNot
    \<Rightarrow> CoreTerm \<Rightarrow> CoreType
    \<Rightarrow> (BabBinop \<times> CoreTerm \<times> CoreType) list
    \<Rightarrow> TypeError list + (CoreTerm \<times> CoreType)" where
  "fold_implies_right is_flex loc ghost lhsTm lhsTy [] = Inr (lhsTm, lhsTy)"
| "fold_implies_right is_flex loc ghost lhsTm lhsTy ((op, rhsTm, rhsTy) # rest) =
    (case rest of
      [] \<Rightarrow> elab_binop_with_special is_flex loc ghost op lhsTm lhsTy rhsTm rhsTy
    | _ \<Rightarrow>
        \<comment> \<open>First, build the right side recursively\<close>
        (case fold_implies_right is_flex loc ghost rhsTm rhsTy rest of
          Inl errs \<Rightarrow> Inl errs
        | Inr (rightTm, rightTy) \<Rightarrow>
            elab_binop_with_special is_flex loc ghost op lhsTm lhsTy rightTm rightTy))"

(* Process a binop chain: elaborate the operator list given already-elaborated operands.
   Decides whether to chain (comparisons), right-associate (implies), or left-associate.
   Validates that all operators in a chain are consistent:
   - Implies chains: all operators must be ==> or <==
   - Comparison chains: all operators must be comparisons with compatible directions
     (e.g. a < b <= c is ok, a < b > c is not) *)
fun process_binop_chain :: "(string \<Rightarrow> bool) \<Rightarrow> Location \<Rightarrow> GhostOrNot
    \<Rightarrow> CoreTerm \<Rightarrow> CoreType
    \<Rightarrow> (BabBinop \<times> CoreTerm \<times> CoreType) list
    \<Rightarrow> TypeError list + (CoreTerm \<times> CoreType)" where
  "process_binop_chain is_flex loc ghost lhsTm lhsTy [] = Inr (lhsTm, lhsTy)"
| "process_binop_chain is_flex loc ghost lhsTm lhsTy ops =
    (let firstOp = fst (hd ops) in
     if firstOp = BabBinop_Implies \<or> firstOp = BabBinop_ImpliedBy then
       \<comment> \<open>Implies chains: validate all ops, then right-associate\<close>
       if check_implies_chain ops
       then fold_implies_right is_flex loc ghost lhsTm lhsTy ops
       else Inl [TyErr_MixedOperatorsInChain loc]
     else if is_comparison_bab_binop firstOp \<and> length ops > 1 then
       \<comment> \<open>Comparison chains: validate directions, then chain\<close>
       if check_comparison_chain_directions ops ChainNeutral
       then (case build_comparison_chain is_flex loc ghost 0 lhsTm lhsTy ops of
               Inl errs \<Rightarrow> Inl errs
             | Inr resultTm \<Rightarrow> Inr (resultTm, CoreTy_Bool))
       else Inl [TyErr_MixedDirectionsInChain loc]
     else
       \<comment> \<open>Everything else left-associates\<close>
       fold_binop_left is_flex loc ghost lhsTm lhsTy ops)"


(* ========================================================================== *)
(* Record update helpers *)
(* ========================================================================== *)

(* Check that every update field name exists in the parent record type.
   Returns the first field name that is not found, if any. *)
fun check_update_fields_exist :: "(string \<times> 'a) list \<Rightarrow> (string \<times> 'b) list \<Rightarrow> string option" where
  "check_update_fields_exist [] _ = None"
| "check_update_fields_exist ((name, _) # rest) parentFields =
    (if map_of parentFields name = None
     then Some name
     else check_update_fields_exist rest parentFields)"

(* Build the final record field list for a record update.
   For each field in the parent type, use the update term if present, otherwise
   project from the parent term. *)
fun build_record_update :: "CoreTerm \<Rightarrow> (string \<times> CoreType) list \<Rightarrow> (string \<times> CoreTerm) list
                           \<Rightarrow> (string \<times> CoreTerm) list" where
  "build_record_update _ [] _ = []"
| "build_record_update parent ((name, _) # rest) updates =
    (case map_of updates name of
       Some newTm \<Rightarrow> (name, newTm) # build_record_update parent rest updates
     | None \<Rightarrow> (name, CoreTm_RecordProj parent name) # build_record_update parent rest updates)"

(* Given the parent term, parent field types, substitution, and coerced update map,
   build the final CoreTm_Record and its type. *)
definition build_updated_record ::
  "TypeSubst \<Rightarrow> CoreTerm \<Rightarrow> (string \<times> CoreType) list
   \<Rightarrow> (string \<times> CoreTerm) list
   \<Rightarrow> CoreTerm \<times> CoreType" where
  "build_updated_record subst parentTm parentFields coercedUpdates =
    (let finalParentFields = map (\<lambda>(n, ty). (n, apply_subst subst ty)) parentFields;
         finalParentTm = apply_subst_to_term subst parentTm;
         resultFlds = build_record_update finalParentTm finalParentFields coercedUpdates
     in (CoreTm_Record resultFlds, CoreTy_Record finalParentFields))"


(* ========================================================================== *)
(* Metavariable resolution check for types *)
(* ========================================================================== *)

(* Check that a type was fully inferred, i.e., no type metavariables remain in
   it. Variables not in TE_TypeVars env are assumed to be metavariables. *)
definition type_inferred :: "CoreTyEnv \<Rightarrow> CoreType \<Rightarrow> bool" where
  "type_inferred env ty = list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list ty)"


(* ========================================================================== *)
(* Match helpers *)
(* ========================================================================== *)

(* Final-stage helper for term-context match elaboration. Takes the elaborated
   scrutinee, and the per-arm results as two parallel lists (the decorated
   patterns, and the arm bodies already converted to the common body type
   bodyTy), and produces the elaborated match term.

   Steps:
   1. Mint a fresh scrutinee binding name (match@@<n>) and validate that it
      doesn't clash with any free var of the scrutinee or of an arm body, or
      with any pattern variable.
   2. Build the elaborated match: a CoreTm_Let binds the scrutinee to the
      fresh name, then CoreTm_Match dispatches on the (binder-free) Core
      patterns. Each arm's body is wrapped in a CoreTm_Let per surface
      pattern variable, projecting from the fresh scrutinee.

   The `nextMv` argument is the next metavariable counter at entry; the
   returned counter is `nextMv + 1` (one more, for the synthesised name's
   numeric suffix). *)
definition finalize_match_term ::
  "Location \<Rightarrow> CoreTerm \<Rightarrow> DecPattern list \<Rightarrow> CoreTerm list \<Rightarrow> CoreType \<Rightarrow> nat
   \<Rightarrow> TypeError list + (CoreTerm \<times> CoreType \<times> nat)" where
  "finalize_match_term loc scrutTm dps bodies bodyTy nextMv =
    (let freshName = ''match@@'' @ nat_to_string nextMv
     in if freshName |\<in>| core_term_free_vars scrutTm
           \<or> list_ex (\<lambda>dp. freshName |\<in>| dec_pattern_var_names dp) dps
           \<or> list_ex (\<lambda>body. freshName |\<in>| core_term_free_vars body) bodies
        then Inl [TyErr_UnexpectedNameClash loc]
        else
          let armPats = map dec_to_core_pat dps;
              armBodies = map (\<lambda>(dp, body). wrap_lets freshName dp body)
                              (zip dps bodies);
              matchTm = CoreTm_Match (CoreTm_Var freshName)
                                     (zip armPats armBodies);
              resultTm = CoreTm_Let freshName scrutTm matchTm
          in Inr (resultTm, bodyTy, nextMv + 1))"


(* ========================================================================== *)
(* Main recursive term elaboration functions *)
(* ========================================================================== *)

(* Elaborate a (pure) term. Returns elaborated (core) term and type, or error.
   The nat parameter is the "next metavariable" counter - all generated metavariables
   will be >= this value, and the returned counter is the next available one. *)
function (sequential)
  elab_term :: "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> BabTerm \<Rightarrow> nat
                 \<Rightarrow> TypeError list + (CoreTerm \<times> CoreType \<times> nat)"
and elab_term_list :: "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> BabTerm list \<Rightarrow> nat
                      \<Rightarrow> TypeError list + (CoreTerm list \<times> CoreType list \<times> nat)"
and elab_term_list_with_envs ::
  "(CoreTyEnv \<times> BabTerm) list \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> nat
   \<Rightarrow> TypeError list + (CoreTerm list \<times> CoreType list \<times> nat)"
where

  (* Literals *)
  "elab_term env elabEnv ghost (BabTm_Literal loc lit) next_mv =
    (case lit of
      BabLit_Bool b \<Rightarrow> Inr (CoreTm_LitBool b, CoreTy_Bool, next_mv)
    | BabLit_Int i \<Rightarrow>
        (case get_type_for_int i of
          Some (sign, bits) \<Rightarrow> Inr (CoreTm_LitInt i, CoreTy_FiniteInt sign bits, next_mv)
        | None \<Rightarrow> Inl [TyErr_IntLiteralOutOfRange loc])
    | BabLit_Array tms \<Rightarrow>
        \<comment> \<open>Allocate a fresh metavariable for the element type, then unify each
            element's type against it (with integer coercion).\<close>
        if \<not> int_in_range (int_range Unsigned IntBits_64) (int (length tms)) then
          Inl [TyErr_InvalidArrayDimension loc]
        else
          let elemTy = CoreTy_Var (mv_name next_mv) in
          (case elab_term_list env elabEnv ghost tms (next_mv + 1) of
            Inl errs \<Rightarrow> Inl errs
          | Inr (elabTms, actualTys, next_mv') \<Rightarrow>
              let expectedTys = replicate (length elabTms) elemTy in
              (case unify_and_coerce (\<lambda>n. n |\<notin>| TE_TypeVars env)
                      (\<lambda>idx. bab_term_location (tms ! idx))
                      elabTms actualTys expectedTys fmempty of
                Inl errs \<Rightarrow> Inl errs
              | Inr (coercedTms, finalSubst) \<Rightarrow>
                  let finalElemTy = apply_subst finalSubst elemTy
                  in Inr (CoreTm_LitArray finalElemTy coercedTms,
                          CoreTy_Array finalElemTy
                                       [CoreDim_Fixed (int (length coercedTms))],
                          next_mv')))
    | BabLit_String chars \<Rightarrow>
        \<comment> \<open>String literal: array of u8 containing the bytes of the string plus a
            null terminator. Each byte is emitted as a cast from i32 to u8.\<close>
        if \<not> int_in_range (int_range Unsigned IntBits_64) (int (length chars + 1)) then
          Inl [TyErr_InvalidArrayDimension loc]
        else
          let u8_ty = CoreTy_FiniteInt Unsigned IntBits_8;
              bytes = chars @ [CHR 0x00];
              elemTms = map (\<lambda>c. CoreTm_Cast u8_ty (CoreTm_LitInt (int (of_char c)))) bytes
          in Inr (CoreTm_LitArray u8_ty elemTms,
                  CoreTy_Array u8_ty [CoreDim_Fixed (int (length bytes))],
                  next_mv))"

  (* Variables and data constructors *)
| "elab_term env elabEnv ghost (BabTm_Name loc name tyArgs) next_mv =
    (case tyenv_lookup_var env name of
      Some ty \<Rightarrow>
        if tyArgs \<noteq> [] then Inl [TyErr_WrongNumberOfTypeArgs loc name 0 (length tyArgs)]
        else if ghost = NotGhost \<and> tyenv_var_ghost env name
             then Inl [TyErr_GhostVariableInNonGhost loc name]
        else Inr (CoreTm_Var name, ty, next_mv)
    | None \<Rightarrow>
        \<comment> \<open>Ghost constants are desugared to nullary ghost functions, so a
            reference to one becomes a call. (This is checked after the
            variable lookup, so local shadowing behaves as for any global.)\<close>
        if name |\<in>| EE_GhostConstants elabEnv then
          (case fmlookup (TE_Functions env) name of
             Some funInfo \<Rightarrow>
               if tyArgs \<noteq> [] then Inl [TyErr_WrongNumberOfTypeArgs loc name 0 (length tyArgs)]
               else if ghost = NotGhost then Inl [TyErr_GhostVariableInNonGhost loc name]
               else Inr (CoreTm_FunctionCall name [] [], FI_ReturnType funInfo, next_mv)
           | None \<Rightarrow> Inl [TyErr_NameNotFound loc name])
        else
        (case fmlookup (TE_DataCtors env) name of
          Some (dtName, tyvars, _) \<Rightarrow>
            if name |\<notin>| EE_NullaryDataCtors elabEnv then
              Inl [TyErr_DataCtorHasPayload loc name]
            else if ghost = NotGhost \<and> dtName |\<in>| TE_GhostDatatypes env then
              Inl [TyErr_GhostVariableInNonGhost loc name]
            else
              (case resolve_type_args env elabEnv ghost loc name tyvars tyArgs next_mv of
                Inl errs \<Rightarrow> Inl errs
              | Inr (newTyArgs, next_mv') \<Rightarrow>
                    Inr (CoreTm_VariantCtor name newTyArgs (CoreTm_Record []),
                         CoreTy_Datatype dtName newTyArgs, next_mv'))
        | None \<Rightarrow> Inl [TyErr_NameNotFound loc name]))"

  (* Casts *)
| "elab_term env elabEnv ghost (BabTm_Cast loc targetTy operand) next_mv = 
    (case elab_type env elabEnv ghost targetTy of
      Inl errs \<Rightarrow> Inl errs
    | Inr newTargetTy \<Rightarrow>
        (case elab_term env elabEnv ghost operand next_mv of
          Inl errs \<Rightarrow> Inl errs
        | Inr (newOperand, operandTy, next_mv') \<Rightarrow>
            if is_numeric_type newTargetTy then
              (case unify (\<lambda>n. n |\<notin>| TE_TypeVars env) operandTy newTargetTy of
                Some subst \<Rightarrow>
                  \<comment> \<open>Unification succeeded - we can eliminate the cast\<close>
                  Inr (apply_subst_to_term subst newOperand, newTargetTy, next_mv')
              | None \<Rightarrow>
                  if is_numeric_type operandTy then
                    \<comment> \<open>Casting one numeric type (finite int, int or real) to another\<close>
                    Inr (CoreTm_Cast newTargetTy newOperand, newTargetTy, next_mv')
                  else
                    Inl [TyErr_InvalidCast loc])
            else
              Inl [TyErr_InvalidCast loc]))"

  (* If/then/else - elaborates to CoreTm_Match with True and False patterns *)
| "elab_term env elabEnv ghost (BabTm_If loc condTm thenTm elseTm) next_mv =
    (case elab_term env elabEnv ghost condTm next_mv of
      Inl errs \<Rightarrow> Inl errs
    | Inr (newCond, condTy, next_mv1) \<Rightarrow>
      (case elab_term env elabEnv ghost thenTm next_mv1 of
        Inl errs \<Rightarrow> Inl errs
      | Inr (newThen, thenTy, next_mv2) \<Rightarrow>
        (case elab_term env elabEnv ghost elseTm next_mv2 of
          Inl errs \<Rightarrow> Inl errs
        | Inr (newElse, elseTy, next_mv3) \<Rightarrow>
            \<comment> \<open>Unify the condition type against Bool. If the condition is already
                Bool this is a no-op; if it is a flex metavariable it gets bound. \<close>
            (case unify (\<lambda>n. n |\<notin>| TE_TypeVars env) condTy CoreTy_Bool of
              None \<Rightarrow> Inl [TyErr_TypeMismatch loc CoreTy_Bool condTy]
            | Some condSubst \<Rightarrow>
              let finalCond = apply_subst_to_term condSubst newCond in
                \<comment> \<open>Try to unify branch types\<close>
                (case unify (\<lambda>n. n |\<notin>| TE_TypeVars env) thenTy elseTy of
                  Some branchSubst \<Rightarrow>
                    \<comment> \<open>A metavariable may not be bound to an incomplete array type.\<close>
                    if \<not> typesubst_complete branchSubst
                    then Inl [TyErr_IncompleteTypeArgument loc]
                    else
                    let resultTy = apply_subst branchSubst thenTy;
                        newThen' = apply_subst_to_term branchSubst newThen;
                        newElse' = apply_subst_to_term branchSubst newElse;
                        \<comment> \<open>Build CoreTm_Match with True and False patterns\<close>
                        matchArms = [(CorePat_Bool True, newThen'), (CorePat_Bool False, newElse')]
                    in Inr (CoreTm_Match finalCond matchArms, resultTy, next_mv3)
                | None \<Rightarrow>
                    \<comment> \<open>Unification failed - try implicit integer coercion\<close>
                    (case coerce_to_common_int_type newThen thenTy newElse elseTy of
                      Some (coercedThen, coercedElse, commonTy) \<Rightarrow>
                        let matchArms = [(CorePat_Bool True, coercedThen), (CorePat_Bool False, coercedElse)]
                        in Inr (CoreTm_Match finalCond matchArms, commonTy, next_mv3)
                    | None \<Rightarrow>
                        Inl [TyErr_TypeMismatch loc thenTy elseTy]))))))"

  (* Unary operator *)
| "elab_term env elabEnv ghost (BabTm_Unop loc op operand) next_mv =
    (case elab_term env elabEnv ghost operand next_mv of
      Inl errs \<Rightarrow> Inl errs
    | Inr (newOperand, operandTy, next_mv') \<Rightarrow>
        let cop = unop_to_core op;
            defaultTy = default_type_for_unop cop
        in
        \<comment> \<open>Try to unify the operand type with the operator's default type. This
            is a no-op when the operand is already the default type, and binds
            the operand's metavariable when it is a flex meta. \<close>
        (case unify (\<lambda>n. n |\<notin>| TE_TypeVars env) operandTy defaultTy of
          Some subst \<Rightarrow>
            Inr (CoreTm_Unop cop (apply_subst_to_term subst newOperand),
                 defaultTy, next_mv')
        | None \<Rightarrow>
          \<comment> \<open>Unification failed - operand has a different concrete type. Check
              whether it is acceptable for this operator. \<close>
          (case op of
            BabUnop_Negate \<Rightarrow>
              if is_signed_numeric_type operandTy then
                Inr (CoreTm_Unop CoreUnop_Negate newOperand, operandTy, next_mv')
              else
                Inl [TyErr_SignedTypeRequired loc operandTy]
          | BabUnop_Complement \<Rightarrow>
              if is_finite_integer_type operandTy then
                Inr (CoreTm_Unop CoreUnop_Complement newOperand, operandTy, next_mv')
              else
                Inl [TyErr_FiniteIntegerTypeRequired loc operandTy]
          | BabUnop_Not \<Rightarrow>
              Inl [TyErr_TypeMismatch loc CoreTy_Bool operandTy])))"

  (* Binary operator *)
| "elab_term env elabEnv ghost (BabTm_Binop loc lhs operands) next_mv =
    (case elab_term env elabEnv ghost lhs next_mv of
      Inl errs \<Rightarrow> Inl errs
    | Inr (newLhs, lhsTy, next_mv1) \<Rightarrow>
        \<comment> \<open>Elaborate all RHS terms using elab_term_list\<close>
        (case elab_term_list env elabEnv ghost (map snd operands) next_mv1 of
          Inl errs \<Rightarrow> Inl errs
        | Inr (rhsTms, rhsTys, next_mv2) \<Rightarrow>
            \<comment> \<open>Zip the operators back together with elaborated terms and types\<close>
            let opTriples = zip (map fst operands) (zip rhsTms rhsTys);
                opList = map (\<lambda>(op, tm_ty). (op, fst tm_ty, snd tm_ty)) opTriples
            in (case process_binop_chain (\<lambda>n. n |\<notin>| TE_TypeVars env) loc ghost newLhs lhsTy opList of
              Inl errs \<Rightarrow> Inl errs
            | Inr (resultTm, resultTy) \<Rightarrow>
                Inr (resultTm, resultTy, next_mv2))))"

  (* Let *)
| "elab_term env elabEnv ghost (BabTm_Let loc varName rhs body) next_mv =
    (case elab_term env elabEnv ghost rhs next_mv of
      Inl errs \<Rightarrow> Inl errs
    | Inr (rhsTm, rhsTy, next_mv1) \<Rightarrow>
        if \<not> list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)
        then Inl [TyErr_CannotInferType loc]
        else let env' = env \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars env),
                              TE_GhostLocals := (if ghost = Ghost
                                               then finsert varName (TE_GhostLocals env)
                                               else fminus (TE_GhostLocals env) {|varName|}),
                              TE_ConstLocals := finsert varName (TE_ConstLocals env) \<rparr>
             in (case elab_term env' elabEnv ghost body next_mv1 of
                  Inl errs \<Rightarrow> Inl errs
                | Inr (bodyTm, bodyTy, next_mv2) \<Rightarrow>
                    Inr (CoreTm_Let varName rhsTm bodyTm, bodyTy, next_mv2)))"

  (* Quantifier: ghost-only, body must be Bool. The bound variable is a const
     local, as for Let. *)
| "elab_term env elabEnv ghost (BabTm_Quantifier loc quant name ty tm) next_mv =
    (if ghost \<noteq> Ghost then Inl [TyErr_RequiresGhostContext loc]
     else case elab_type env elabEnv ghost ty of
       Inl errs \<Rightarrow> Inl errs
     | Inr varTy \<Rightarrow>
         let env' = env \<lparr> TE_LocalVars := fmupd name varTy (TE_LocalVars env),
                          TE_GhostLocals := finsert name (TE_GhostLocals env),
                          TE_ConstLocals := finsert name (TE_ConstLocals env) \<rparr>
         in (case elab_term env' elabEnv ghost tm next_mv of
               Inl errs \<Rightarrow> Inl errs
             | Inr (bodyTm, bodyTy, next_mv') \<Rightarrow>
                 (case unify (\<lambda>n. n |\<notin>| TE_TypeVars env) bodyTy CoreTy_Bool of
                    None \<Rightarrow> Inl [TyErr_TypeMismatch loc CoreTy_Bool bodyTy]
                  | Some bodySubst \<Rightarrow>
                      let finalBody = apply_subst_to_term bodySubst bodyTm;
                          finalVarTy = apply_subst bodySubst varTy
                      in Inr (CoreTm_Quantifier quant name finalVarTy finalBody,
                              CoreTy_Bool, next_mv'))))"

  (* Function call or data constructor call *)
| "elab_term env elabEnv ghost (BabTm_Call loc callee args) next_mv =
    (case resolve_callee env elabEnv ghost callee next_mv of
      Inl errs \<Rightarrow> Inl errs
    | Inr (calleeName, expArgTypes, calleeInfo, next_mv1) \<Rightarrow>
        if length args \<noteq> length expArgTypes then
          Inl [TyErr_WrongNumberOfArgs loc calleeName (length expArgTypes) (length args)]
        else
          \<comment> \<open>Elaborate the plain arguments, in the mode of the call; then the
              special arguments (the arguments of ghost parameters, in an
              executable call) in Ghost mode. See finish_call for the rest.\<close>
          (case elab_term_list env elabEnv ghost
                  (plain_args (call_special_flags env ghost callee (length args)) args)
                  next_mv1 of
            Inl errs \<Rightarrow> Inl errs
          | Inr (plainTms, plainTys, next_mvP) \<Rightarrow>
              (case elab_term_list env elabEnv Ghost
                      (special_args (call_special_flags env ghost callee (length args)) args)
                      next_mvP of
                Inl errs \<Rightarrow> Inl errs
              | Inr (specialTms, specialTys, next_mv2) \<Rightarrow>
                  (case finish_call env ghost loc args
                          (call_special_flags env ghost callee (length args))
                          expArgTypes calleeInfo
                          plainTms plainTys next_mvP specialTms specialTys next_mv2 of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr (resultTm, resultTy) \<Rightarrow> Inr (resultTm, resultTy, next_mv2)))))"

  (* Tuple: elaborated to a record with synthetic field names "0", "1", ... *)
| "elab_term env elabEnv ghost (BabTm_Tuple loc tms) next_mv =
    (case elab_term_list env elabEnv ghost tms next_mv of
      Inl errs \<Rightarrow> Inl errs
    | Inr (newTms, tys, next_mv') \<Rightarrow>
        let names = tuple_field_names (length tms) in
        Inr (CoreTm_Record (zip names newTms),
             CoreTy_Record (zip names tys),
             next_mv'))"

  (* Record *)
| "elab_term env elabEnv ghost (BabTm_Record loc flds) next_mv =
    (case first_duplicate_name fst flds of
      Some dupName \<Rightarrow> Inl [TyErr_DuplicateFieldName loc dupName]
    | None \<Rightarrow>
        (case elab_term_list env elabEnv ghost (map snd flds) next_mv of
          Inl errs \<Rightarrow> Inl errs
        | Inr (newTms, tys, next_mv') \<Rightarrow>
            let names = map fst flds in
            Inr (CoreTm_Record (zip names newTms),
                 CoreTy_Record (zip names tys),
                 next_mv')))"

  (* Record update *)
| "elab_term env elabEnv ghost (BabTm_RecordUpdate loc tm flds) next_mv =
    (case first_duplicate_name fst flds of
      Some dupName \<Rightarrow> Inl [TyErr_DuplicateFieldName loc dupName]
    | None \<Rightarrow>
      (case elab_term env elabEnv ghost tm next_mv of
        Inl errs \<Rightarrow> Inl errs
      | Inr (parentTm, parentTy, next_mv1) \<Rightarrow>
          (case parentTy of
            CoreTy_Record parentFields \<Rightarrow>
              (case check_update_fields_exist flds parentFields of
                Some badName \<Rightarrow> Inl [TyErr_FieldNotFound loc badName parentTy]
              | None \<Rightarrow>
                  (case elab_term_list env elabEnv ghost (map snd flds) next_mv1 of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr (newUpdateTms, actualTypes, next_mv2) \<Rightarrow>
                      let expectedTypes = map (\<lambda>(name, _). the (map_of parentFields name)) flds
                      in (case unify_and_coerce (\<lambda>n. n |\<notin>| TE_TypeVars env)
                                  (\<lambda>idx. bab_term_location (snd (flds ! idx)))
                                  newUpdateTms actualTypes expectedTypes fmempty of
                        Inl errs \<Rightarrow> Inl errs
                      | Inr (coercedTms, finalSubst) \<Rightarrow>
                          let coercedUpdates = zip (map fst flds) coercedTms;
                              (resultTm, resultTy) =
                                build_updated_record finalSubst parentTm parentFields coercedUpdates
                          in Inr (resultTm, resultTy, next_mv2))))
          | _ \<Rightarrow> Inl [TyErr_NotARecordType loc parentTy])))"

  (* Tuple projection: tuples are records with synthetic field names "0", "1", ... *)
| "elab_term env elabEnv ghost (BabTm_TupleProj loc tm idx) next_mv =
    (case elab_term env elabEnv ghost tm next_mv of
      Inl errs \<Rightarrow> Inl errs
    | Inr (newTm, tmTy, next_mv') \<Rightarrow>
        (case tmTy of
          CoreTy_Record fieldTypes \<Rightarrow>
            (case map_of fieldTypes (nat_to_string idx) of
              Some fldTy \<Rightarrow> Inr (CoreTm_RecordProj newTm (nat_to_string idx), fldTy, next_mv')
            | None \<Rightarrow> Inl [TyErr_TupleIndexOutOfRange loc idx tmTy])
        | _ \<Rightarrow> Inl [TyErr_NotARecordType loc tmTy]))"

  (* Record projection *)
| "elab_term env elabEnv ghost (BabTm_RecordProj loc tm fldName) next_mv =
    (case elab_term env elabEnv ghost tm next_mv of
      Inl errs \<Rightarrow> Inl errs
    | Inr (newTm, tmTy, next_mv') \<Rightarrow>
        (case tmTy of
          CoreTy_Record fieldTypes \<Rightarrow>
            (case map_of fieldTypes fldName of
              Some fldTy \<Rightarrow> Inr (CoreTm_RecordProj newTm fldName, fldTy, next_mv')
            | None \<Rightarrow> Inl [TyErr_FieldNotFound loc fldName tmTy])
        | _ \<Rightarrow> Inl [TyErr_NotARecordType loc tmTy]))"

  (* Array projection (indexing) *)
| "elab_term env elabEnv ghost (BabTm_ArrayProj loc tm idxs) next_mv =
    (case elab_term env elabEnv ghost tm next_mv of
      Inl errs \<Rightarrow> Inl errs
    | Inr (newArr, arrTy, next_mv1) \<Rightarrow>
        (case arrTy of
          CoreTy_Array elemTy dims \<Rightarrow>
            if length idxs \<noteq> length dims then
              Inl [TyErr_WrongNumberOfIndices loc (length dims) (length idxs)]
            else
              (case elab_term_list env elabEnv ghost idxs next_mv1 of
                Inl errs \<Rightarrow> Inl errs
              | Inr (elabIdxTms, actualTypes, next_mv2) \<Rightarrow>
                  (case unify_and_coerce (\<lambda>n. n |\<notin>| TE_TypeVars env)
                          (\<lambda>idx. bab_term_location (idxs ! idx))
                          elabIdxTms actualTypes (replicate (length dims) u64_type) fmempty of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr (coercedIdxTms, _) \<Rightarrow>
                      Inr (CoreTm_ArrayProj newArr coercedIdxTms, elemTy, next_mv2)))
        | _ \<Rightarrow> Inl [TyErr_NotAnArrayType loc arrTy]))"

  (* Match: elaborate the scrutinee, decorate every arm's pattern against the
     scrutinee type, and elaborate every arm's body under the env extended with
     that arm's pattern variables (every pattern variable is const, as for Let).

     The scrutinee's type must be fully determined by the scrutinee itself.

     The type of the match is the first arm's body type. Every arm body is
     converted to it, using the same implicit conversions as function arguments.

     The result is handed off to finalize_match_term (which translates
     DecPatterns to CorePatterns and emits the binder-projection Lets). *)
| "elab_term env elabEnv ghost (BabTm_Match loc scrut arms) next_mv =
    (if arms = [] then Inl [TyErr_EmptyMatch loc]
     else case elab_term env elabEnv ghost scrut next_mv of
       Inl errs \<Rightarrow> Inl errs
     | Inr (scrutTm, scrutTy, mv1) \<Rightarrow>
         if \<not> type_inferred env scrutTy
         then Inl [TyErr_CannotInferType (bab_term_location scrut)]
         else
         (case decorate_match_arms env elabEnv ghost scrutTy False arms of
            Inl errs \<Rightarrow> Inl errs
          | Inr decoratedRows \<Rightarrow>
              \<comment> \<open>Build body-elaboration jobs from the per-arm envs and the original
                  body terms (from arms). Constructing the body list directly from
                  arms keeps it syntactically derived, so termination is easy to
                  verify. \<close>
              let dps = map fst decoratedRows;
                  bodyJobs = zip (map (\<lambda>dp. extend_env_with_pattern_vars
                                              env (\<lambda>_. True) ghost [dp]) dps)
                                 (map snd arms) in
              (case elab_term_list_with_envs bodyJobs elabEnv ghost mv1 of
                 Inl errs \<Rightarrow> Inl errs
               | Inr (bodyTms, bodyTys, mv2) \<Rightarrow>
                   (case unify_and_coerce (\<lambda>n. n |\<notin>| TE_TypeVars env)
                           (\<lambda>idx. bab_term_location (snd (arms ! idx)))
                           bodyTms bodyTys
                           (replicate (length bodyTms) (hd bodyTys)) fmempty of
                      Inl errs \<Rightarrow> Inl errs
                    | Inr (coercedBodies, finalSubst) \<Rightarrow>
                        finalize_match_term loc scrutTm dps coercedBodies
                          (apply_subst finalSubst (hd bodyTys)) mv2))))"

  (* Sizeof: operand must be an array; allocatable dims require lvalue or ghost *)
| "elab_term env elabEnv ghost (BabTm_Sizeof loc tm) next_mv =
    (case elab_term env elabEnv ghost tm next_mv of
      Inl errs \<Rightarrow> Inl errs
    | Inr (newTm, tmTy, next_mv') \<Rightarrow>
        (case tmTy of
          CoreTy_Array _ dims \<Rightarrow>
            if list_ex (\<lambda>d. d = CoreDim_Allocatable) dims \<and> \<not> is_lvalue newTm \<and> ghost = NotGhost
            then Inl [TyErr_SizeofRequiresLvalue loc]
            else Inr (CoreTm_Sizeof newTm, sizeof_type dims, next_mv')
        | _ \<Rightarrow> Inl [TyErr_NotAnArrayType loc tmTy]))"

  (* Allocated: ghost-only, operand must be of complete type, result is Bool.
     The operand's type is recorded in the Core term. *)
| "elab_term env elabEnv ghost (BabTm_Allocated loc tm) next_mv =
    (if ghost \<noteq> Ghost then Inl [TyErr_RequiresGhostContext loc]
     else case elab_term env elabEnv ghost tm next_mv of
       Inl errs \<Rightarrow> Inl errs
     | Inr (newTm, tmTy, next_mv') \<Rightarrow>
         if \<not> is_complete_type tmTy then Inl [TyErr_IncompleteArrayType loc]
         else Inr (CoreTm_Allocated tmTy newTm, CoreTy_Bool, next_mv'))"

  (* Old: ghost-only, result has same type as operand *)
| "elab_term env elabEnv ghost (BabTm_Old loc tm) next_mv =
    (if ghost \<noteq> Ghost then Inl [TyErr_RequiresGhostContext loc]
     else case elab_term env elabEnv ghost tm next_mv of
       Inl errs \<Rightarrow> Inl errs
     | Inr (newTm, tmTy, next_mv') \<Rightarrow>
         Inr (CoreTm_Old newTm, tmTy, next_mv'))"

  (* elab_term_list - Empty list case *)
| "elab_term_list _ _ _ [] next_mv = Inr ([], [], next_mv)"

  (* elab_term_list - Non-empty list case *)
| "elab_term_list env elabEnv ghost (tm # tms) next_mv =
    (case elab_term env elabEnv ghost tm next_mv of
      Inl errs1 \<Rightarrow>
        \<comment> \<open>Error in first term - continue processing rest to collect all errors\<close>
        (case elab_term_list env elabEnv ghost tms next_mv of
          Inl errs2 \<Rightarrow> Inl (errs1 @ errs2)
        | Inr _ \<Rightarrow> Inl errs1)
    | Inr (tm', ty', next_mv') \<Rightarrow>
        \<comment> \<open>First term successful - collect results from remaining terms\<close>
        (case elab_term_list env elabEnv ghost tms next_mv' of
          Inl errs \<Rightarrow> Inl errs
        | Inr (tms', tys', next_mv'') \<Rightarrow> Inr (tm' # tms', ty' # tys', next_mv'')))"

  (* elab_term_list_with_envs - Empty list case. *)
| "elab_term_list_with_envs [] _ _ next_mv = Inr ([], [], next_mv)"

  (* elab_term_list_with_envs - Non-empty list case. Each term is elaborated
     under its own env (paired with it in the input list). Otherwise behaves
     like elab_term_list, including error-collection on first-element failure. *)
| "elab_term_list_with_envs ((env, tm) # rest) elabEnv ghost next_mv =
    (case elab_term env elabEnv ghost tm next_mv of
      Inl errs1 \<Rightarrow>
        (case elab_term_list_with_envs rest elabEnv ghost next_mv of
          Inl errs2 \<Rightarrow> Inl (errs1 @ errs2)
        | Inr _ \<Rightarrow> Inl errs1)
    | Inr (tm', ty', next_mv') \<Rightarrow>
        (case elab_term_list_with_envs rest elabEnv ghost next_mv' of
          Inl errs \<Rightarrow> Inl errs
        | Inr (tms', tys', next_mv'') \<Rightarrow> Inr (tm' # tms', ty' # tys', next_mv'')))"
  by pat_completeness auto

(* Helper for termination of elab_term & friends: the body-only size used as
   the measure for elab_term_list_with_envs is bounded above by the standard
   pair-list size used by Isabelle's automatic size definitions. *)
lemma size_list_size_snd_le_size_prod:
  "size_list (size \<circ> snd) xs \<le> size_list (size_prod f size) xs"
  by (induction xs) (auto simp: comp_def)

lemma size_list_size_snd_zip_map_snd_le:
  "size_list (size \<circ> snd) (zip as (map snd bs)) \<le> size_list (size_prod f size) bs"
proof -
  have "size_list (size \<circ> snd) (zip as (map snd bs)) \<le> size_list size (map snd bs)"
    by (induction as bs rule: list_induct2') (auto simp: comp_def)
  also have "\<dots> \<le> size_list (size_prod f size) bs"
    by (induction bs) auto
  finally show ?thesis .
qed

termination
proof (relation
        "measure (case_sum (\<lambda>(_, _, _, tm, _). size tm)
                 (case_sum (\<lambda>(_, _, _, tms, _). size_list size tms)
                           (\<lambda>(jobs, _, _, _). size_list (size \<circ> snd) jobs)))",
       goal_cases)
  case (9 env elabEnv ghost loc lhs operands next_mv b x y xa ya)
  \<comment> \<open>BabTm_Call args sub-call. \<close>
  show ?case
    using size_list_size_snd_le_size_prod[where xs=operands and f="\<lambda>_. 0"] by simp
next
  case (13 env elabEnv ghost loc callee args)
  \<comment> \<open>BabTm_Call: the plain arguments. \<close>
  show ?case
    using size_list_plain_args_le
            [of size "call_special_flags env ghost callee (length args)" args]
    by simp
next
  case (14 env elabEnv ghost loc callee args)
  \<comment> \<open>BabTm_Call: the special arguments. \<close>
  show ?case
    using size_list_special_args_le
            [of size "call_special_flags env ghost callee (length args)" args]
    by simp
next
  case (16 env elabEnv ghost loc flds next_mv)
  \<comment> \<open>BabTm_Record fields sub-call. \<close>
  show ?case
    using size_list_size_snd_le_size_prod[where xs=flds and f="\<lambda>_. 0"] by simp
next
  case (18 env elabEnv ghost loc tm flds next_mv b x y xa ya x6)
  \<comment> \<open>BabTm_RecordUpdate update-fields sub-call. \<close>
  show ?case
    using size_list_size_snd_le_size_prod[where xs=flds and f="\<lambda>_. 0"] by simp
next
  case (24 env elabEnv ghost loc scrut arms next_mv b x y xa ya ba dps bodyJobs)
  \<comment> \<open>BabTm_Match body-elaboration sub-call: bodies (taken syntactically from arms,
      zipped with the per-arm envs) sum to less than the whole BabTm_Match. \<close>
  have helper:
    "size_list (size \<circ> snd)
       (zip (map (\<lambda>dp. extend_env_with_pattern_vars env (\<lambda>_. True) ghost [dp]) dps)
            (map snd arms))
       \<le> size_list (size_prod (\<lambda>x. 0) size) arms"
    by (rule size_list_size_snd_zip_map_snd_le)
  from 24 helper show ?case by simp
qed (simp_all add: comp_def)


end
