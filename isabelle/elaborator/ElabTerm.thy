theory ElabTerm
  imports ElabType Unify "../core/CoreTypeSubst"
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


(* Coerce two terms to a common integer type by inserting implicit casts if needed.
   Used for if/then/else or match terms.
   Only applies when both types are CoreTy_FiniteInt. Returns None if no common type exists. *)
fun coerce_to_common_int_type :: "CoreTerm \<Rightarrow> CoreType \<Rightarrow> CoreTerm \<Rightarrow> CoreType
                                  \<Rightarrow> (CoreTerm \<times> CoreTerm \<times> CoreType) option" where
  "coerce_to_common_int_type tm1 (CoreTy_FiniteInt sign1 bits1)
                             tm2 (CoreTy_FiniteInt sign2 bits2) =
    (case combine_int_types sign1 bits1 sign2 bits2 of
      None \<Rightarrow> None
    | Some (commonSign, commonBits) \<Rightarrow>
        let commonTy1 = CoreTy_FiniteInt commonSign commonBits;
            commonTy2 = CoreTy_FiniteInt commonSign commonBits;
            \<comment> \<open>Only wrap in cast if type differs from common type\<close>
            newTm1 = (if sign1 = commonSign \<and> bits1 = commonBits then tm1
                      else CoreTm_Cast commonTy1 tm1);
            newTm2 = (if sign2 = commonSign \<and> bits2 = commonBits then tm2
                      else CoreTm_Cast commonTy2 tm2)
        in Some (newTm1, newTm2, commonTy1))"
| "coerce_to_common_int_type _ _ _ _ = None"


(* This helper takes a "function term" and (if successful) returns function name, 
   elaborated type args, expected arg types, return type, and next metavariable number. *)
fun determine_fun_call_type :: "CoreTyEnv \<Rightarrow> Typedefs \<Rightarrow> GhostOrNot \<Rightarrow> BabTerm \<Rightarrow> nat \<Rightarrow>
        (TypeError list + string \<times> CoreType list \<times> CoreType list \<times> CoreType \<times> nat)"
where
  "determine_fun_call_type env typedefs ghost (BabTm_Name fnLoc fnName tyArgs) next_mv =
    \<comment> \<open>Look up function in environment\<close>
    (case fmlookup (TE_Functions env) fnName of
      Some funInfo \<Rightarrow>
        \<comment> \<open>TODO: Check purity: only pure functions allowed in term context\<close>
        \<comment> \<open>(Error: TyErr_ImpureFunctionInTermContext fnLoc fnName)\<close>
        \<comment> \<open>TODO: Check ref args: not allowed in term context\<close>
        \<comment> \<open>(Error: TyErr_RefArgInTermContext fnLoc fnName)\<close>
        \<comment> \<open>TODO: Check return type provided\<close>
        \<comment> \<open>(Error: TyErr_FunctionNoReturnType fnLoc fnName)\<close>

        \<comment> \<open>Check ghost constraint\<close>
        if ghost = NotGhost \<and> FI_Ghost funInfo = Ghost then
          Inl [TyErr_GhostFunctionInNonGhost fnLoc fnName]

        else
            (let numTyParams = length (FI_TyArgs funInfo) in
            \<comment> \<open>Handle type arguments: infer if omitted, elaborate if provided\<close>
            \<comment> \<open>This next `case` returns the new actual ty args and the new next_mv\<close>
            case
              (if tyArgs = [] \<and> numTyParams > 0 then
                \<comment> \<open>Generate fresh metavariables for the function's type arguments\<close>
                Inr (map CoreTy_Var [next_mv..<next_mv + numTyParams], next_mv + numTyParams)
              else if numTyParams = length tyArgs then
                \<comment> \<open>Elaborate the user's provided type arguments\<close>
                (case elab_type_list env typedefs ghost tyArgs of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr newTyArgs \<Rightarrow> Inr (newTyArgs, next_mv))
              else
                Inl [TyErr_WrongTypeArity fnLoc fnName numTyParams (length tyArgs)])
            of
              Inl errs \<Rightarrow> Inl errs
            | Inr (newTyArgs, next_mv') \<Rightarrow>
                \<comment> \<open>Now just substitute the resolved type arguments into the original
                   function's argument and return types\<close>
                let subst = fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs);
                    newArgTypes = map (\<lambda>(_, ty, _). apply_subst subst ty) (FI_TmArgs funInfo);
                    newRetType = apply_subst subst (FI_ReturnType funInfo)
                in Inr (fnName, newTyArgs, newArgTypes, newRetType, next_mv'))
    \<comment> \<open>TODO: Check datatypes as well\<close>
    | None \<Rightarrow> Inl [TyErr_UnknownFunction fnLoc fnName])"
| "determine_fun_call_type _ _ _ tm _ =
    Inl [TyErr_CalleeNotFunction (bab_term_location tm)]"

(* Phase 1 of function call typechecking:
   Unify actual argument types with expected types, accumulating substitutions.
   For each pair of types:
   1. Try unification - if it succeeds, accumulate the substitution
   2. If unification fails but both are finite integer types, that's OK (coercion will be inserted later)
   3. If both fail, return an error
   Returns the final substitution. *)
fun unify_call_types :: "(nat \<Rightarrow> bool) \<Rightarrow> Location \<Rightarrow> string \<Rightarrow> nat
                        \<Rightarrow> CoreType list \<Rightarrow> CoreType list
                        \<Rightarrow> TypeSubst \<Rightarrow> TypeError list + TypeSubst" where
  "unify_call_types is_flex loc fnName argIdx [] [] accSubst = Inr accSubst"
| "unify_call_types is_flex loc fnName argIdx (actualTy # actualTys) (expectedTy # expectedTys) accSubst =
    \<comment> \<open>Apply accumulated substitution to both types before unifying\<close>
    (let actualTy' = apply_subst accSubst actualTy;
         expectedTy' = apply_subst accSubst expectedTy
     in case unify is_flex actualTy' expectedTy' of
       Some newSubst \<Rightarrow>
         \<comment> \<open>Unification succeeded - compose substitutions and continue\<close>
         let composedSubst = compose_subst newSubst accSubst
         in unify_call_types is_flex loc fnName (argIdx + 1) actualTys expectedTys composedSubst
     | None \<Rightarrow>
         \<comment> \<open>Unification failed - check if implicit integer coercion is possible\<close>
         (if is_finite_integer_type actualTy' \<and> is_finite_integer_type expectedTy' then
            \<comment> \<open>Both are finite integers - coercion will be inserted later\<close>
            unify_call_types is_flex loc fnName (argIdx + 1) actualTys expectedTys accSubst
          else
            Inl [TyErr_ArgTypeMismatch loc argIdx expectedTy' actualTy']))"
| "unify_call_types _ _ _ _ _ _ _ = undefined"

(* Phase 2 of function call argument typechecking:
   Apply substitution to terms and insert coercions where needed.
   For each term, apply the substitution. If the resulting actual type differs from
   the expected type (both must be finite integers at this point), insert a cast. *)
fun apply_call_coercions :: "TypeSubst \<Rightarrow> CoreTerm list \<Rightarrow> CoreType list \<Rightarrow> CoreType list
                            \<Rightarrow> CoreTerm list" where
  "apply_call_coercions subst [] [] [] = []"
| "apply_call_coercions subst (tm # tms) (actualTy # actualTys) (expectedTy # expectedTys) =
    (let tm' = apply_subst_to_term subst tm;
         actualTy' = apply_subst subst actualTy;
         expectedTy' = apply_subst subst expectedTy;
         \<comment> \<open>Insert cast if types differ (must be compatible integers at this point)\<close>
         finalTm = (if actualTy' = expectedTy' then tm'
                    else CoreTm_Cast expectedTy' tm')
     in finalTm # apply_call_coercions subst tms actualTys expectedTys)"
| "apply_call_coercions _ _ _ _ = undefined"

(* Combine unify_call_types and apply_call_coercions into a single function *)
definition unify_call_args :: "(nat \<Rightarrow> bool) \<Rightarrow> Location \<Rightarrow> string \<Rightarrow> nat
                              \<Rightarrow> CoreTerm list \<Rightarrow> CoreType list
                              \<Rightarrow> CoreType list \<Rightarrow> TypeSubst
                              \<Rightarrow> TypeError list + (CoreTerm list \<times> TypeSubst)" where
  "unify_call_args is_flex loc fnName argIdx tms actualTys expectedTys accSubst =
    (case unify_call_types is_flex loc fnName argIdx actualTys expectedTys accSubst of
       Inl errs \<Rightarrow> Inl errs
     | Inr finalSubst \<Rightarrow> Inr (apply_call_coercions finalSubst tms actualTys expectedTys, finalSubst))"


(* ========================================================================== *)
(* Binary operator helpers *)
(* ========================================================================== *)

(* Helper for binary operator elaboration: check that both operands satisfy a type predicate,
   then either use them directly (if same type) or try coercion to a common int type.
   - type_pred: the predicate both operand types must satisfy
   - resultTyOverride: if None, the result type is the (common) operand type;
                        if Some ty, the result type is always ty (e.g. Bool for ordering ops)
   - errMsg: the error constructor to use when the type predicate fails *)
definition check_and_coerce_binop ::
  "(CoreType \<Rightarrow> bool) \<Rightarrow> CoreType option
    \<Rightarrow> (Location \<Rightarrow> BabBinop \<Rightarrow> TypeError)
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
     else Inl [errMsg loc babOp])"

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

(* Default type for binary operators when both operands are metavariables.
   Logical/iff/implied-by default to Bool, everything else defaults to i32. *)
definition default_type_for_binop :: "BabBinop \<Rightarrow> CoreType" where
  "default_type_for_binop op =
    (case binop_to_core op of
      Some cop \<Rightarrow>
        if is_logical_binop cop then CoreTy_Bool
        else CoreTy_FiniteInt Signed IntBits_32
    | None \<Rightarrow> CoreTy_Bool)"  \<comment> \<open>ImpliedBy and Iff default to Bool\<close>

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
    ((op = BabBinop_Implies \<or> op = BabBinop_ImpliedBy) \<and> check_implies_chain rest)"

(* Is this a comparison BabBinop? (not implies/implied-by) *)
fun is_comparison_bab_binop :: "BabBinop \<Rightarrow> bool" where
  "is_comparison_bab_binop op = (comparison_direction op \<noteq> None)"

(* Build a substitution that maps every flexible metavariable in a type to a
   given default type. Rigid type-variable metas are skipped. *)
definition const_subst_for :: "(nat \<Rightarrow> bool) \<Rightarrow> CoreType \<Rightarrow> CoreType \<Rightarrow> TypeSubst" where
  "const_subst_for is_flex ty defaultTy =
     fmap_of_list (map (\<lambda>n. (n, defaultTy)) (filter is_flex (type_tyvars_list ty)))"

(* Resolve metavariables in binary operator operands using unification.
   1. Try to unify the two operand types.
   2. If unification succeeds and the result is ground (contains no unifiable metavariables), 
      use the unified type.
   3. If unification succeeds but metavariables remain, fill them with the
      default type for the operator.
   4. If unification fails, pass through unchanged (downstream checks will
      report the appropriate type error). *)
fun resolve_binop_metas :: "(nat \<Rightarrow> bool) \<Rightarrow> BabBinop
    \<Rightarrow> CoreTerm \<Rightarrow> CoreType \<Rightarrow> CoreTerm \<Rightarrow> CoreType
    \<Rightarrow> (CoreTerm \<times> CoreType \<times> CoreTerm \<times> CoreType)" where
  "resolve_binop_metas is_flex babOp lhsTm lhsTy rhsTm rhsTy =
    (case unify is_flex lhsTy rhsTy of
       Some unifSubst \<Rightarrow>
         let unifiedTy = apply_subst unifSubst lhsTy
         in if list_all (\<lambda>n. \<not> is_flex n) (type_tyvars_list unifiedTy) then
              (apply_subst_to_term unifSubst lhsTm, unifiedTy,
               apply_subst_to_term unifSubst rhsTm, unifiedTy)
            else
              let defaultTy = default_type_for_binop babOp;
                  fillSubst = const_subst_for is_flex unifiedTy defaultTy;
                  fullSubst = compose_subst fillSubst unifSubst
              in (apply_subst_to_term fullSubst lhsTm,
                  apply_subst fillSubst unifiedTy,
                  apply_subst_to_term fullSubst rhsTm,
                  apply_subst fillSubst unifiedTy)
     | None \<Rightarrow> (lhsTm, lhsTy, rhsTm, rhsTy))"

(* Elaborate a single binary operation on already-elaborated operands.
   Handles metavariable resolution, type coercion, and type checking.
   ImpliedBy and Iff are handled before calling this function. *)
fun elab_single_binop :: "(nat \<Rightarrow> bool) \<Rightarrow> Location \<Rightarrow> GhostOrNot \<Rightarrow> BabBinop
    \<Rightarrow> CoreTerm \<Rightarrow> CoreType \<Rightarrow> CoreTerm \<Rightarrow> CoreType
    \<Rightarrow> TypeError list + (CoreTerm \<times> CoreType)" where
  "elab_single_binop is_flex loc ghost babOp lhsTm lhsTy rhsTm rhsTy =
    (let (lhsTm', lhsTy', rhsTm', rhsTy') =
           resolve_binop_metas is_flex babOp lhsTm lhsTy rhsTm rhsTy
     in
      case binop_to_core babOp of
        None \<Rightarrow> undefined \<comment> \<open>should not happen\<close>
      | Some cop \<Rightarrow>
        \<comment> \<open>Type-check based on operator category\<close>
        if is_arithmetic_binop cop then
          check_and_coerce_binop is_numeric_type None
            TyErr_BinopRequiresNumeric cop lhsTm' lhsTy' rhsTm' rhsTy' loc babOp

        else if is_modulo_binop cop then
          check_and_coerce_binop is_integer_type None
            TyErr_BinopRequiresInteger cop lhsTm' lhsTy' rhsTm' rhsTy' loc babOp

        else if is_bitwise_binop cop then
          check_and_coerce_binop is_finite_integer_type None
            TyErr_BinopRequiresFiniteInteger cop lhsTm' lhsTy' rhsTm' rhsTy' loc babOp

        else if is_shift_binop cop then
          \<comment> \<open>Shift: both finite integer, cast RHS to LHS type\<close>
          if is_finite_integer_type lhsTy' \<and> is_finite_integer_type rhsTy' then
            let castRhs = (if lhsTy' = rhsTy' then rhsTm' else CoreTm_Cast lhsTy' rhsTm')
            in Inr (CoreTm_Binop cop lhsTm' castRhs, lhsTy')
          else Inl [TyErr_BinopRequiresFiniteInteger loc babOp]

        else if is_ordering_binop cop then
          check_and_coerce_binop is_numeric_type (Some CoreTy_Bool)
            TyErr_BinopRequiresNumeric cop lhsTm' lhsTy' rhsTm' rhsTy' loc babOp

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
          else Inl [TyErr_BinopRequiresBool loc babOp]

        else undefined)"  \<comment> \<open>should be exhaustive\<close>

(* Elaborate a single binary operation, handling ImpliedBy and Iff specially *)
fun elab_binop_with_special :: "(nat \<Rightarrow> bool) \<Rightarrow> Location \<Rightarrow> GhostOrNot \<Rightarrow> BabBinop
    \<Rightarrow> CoreTerm \<Rightarrow> CoreType \<Rightarrow> CoreTerm \<Rightarrow> CoreType
    \<Rightarrow> TypeError list + (CoreTerm \<times> CoreType)" where
  "elab_binop_with_special is_flex loc ghost BabBinop_ImpliedBy lhsTm lhsTy rhsTm rhsTy =
    \<comment> \<open>A <== B becomes B ==> A\<close>
    elab_single_binop is_flex loc ghost BabBinop_Implies rhsTm rhsTy lhsTm lhsTy"
| "elab_binop_with_special is_flex loc ghost BabBinop_Iff lhsTm lhsTy rhsTm rhsTy =
    \<comment> \<open>A <==> B becomes A == B (both must be Bool)\<close>
    (let (lhs', lTy, rhs', rTy) = resolve_binop_metas is_flex BabBinop_Iff lhsTm lhsTy rhsTm rhsTy
     in if lTy = CoreTy_Bool \<and> rTy = CoreTy_Bool
        then Inr (CoreTm_Binop CoreBinop_Equal lhs' rhs', CoreTy_Bool)
        else Inl [TyErr_BinopRequiresBool loc BabBinop_Iff])"
| "elab_binop_with_special is_flex loc ghost op lhsTm lhsTy rhsTm rhsTy =
    elab_single_binop is_flex loc ghost op lhsTm lhsTy rhsTm rhsTy"

(* Process a chain of left-associative binary operations on already-elaborated terms.
   Takes the list of (BabBinop, elaboratedTerm, elaboratedType) triples
   and the accumulated LHS term/type.
   Left-associates: a + b + c becomes (a + b) + c.
*)
fun fold_binop_left :: "(nat \<Rightarrow> bool) \<Rightarrow> Location \<Rightarrow> GhostOrNot
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
    (\<exists>v \<in> core_term_free_vars tm. take 7 v = ''chain@@'' \<and> v \<noteq> allowed)"

(* Build a comparison chain: a < b < c becomes (a < b) && (b < c).
   Uses let-binding for complex middle terms to avoid duplicate evaluation.
   chainCounter is used to generate unique variable names. *)
fun build_comparison_chain :: "(nat \<Rightarrow> bool) \<Rightarrow> Location \<Rightarrow> GhostOrNot \<Rightarrow> nat
    \<Rightarrow> CoreTerm \<Rightarrow> CoreType
    \<Rightarrow> (BabBinop \<times> CoreTerm \<times> CoreType) list
    \<Rightarrow> TypeError list + CoreTerm" where
  "build_comparison_chain is_flex loc ghost chainCtr accTm accTy [] = Inl []"
| "build_comparison_chain is_flex loc ghost chainCtr lhsTm lhsTy ((op, rhsTm, rhsTy) # rest) =
    (let lhsAllowed = (if chainCtr = 0 then '''' else ''chain@@'' @ nat_to_string (chainCtr - 1))
     in if has_unexpected_chain_var lhsTm lhsAllowed
            \<or> has_unexpected_chain_var rhsTm '''' then
       Inl [TyErr_InternalError_UnexpectedChainVar loc]
     else
     case rest of
      [] \<Rightarrow>
        \<comment> \<open>Last comparison: just elaborate normally, discard type\<close>
        (case elab_binop_with_special is_flex loc ghost op lhsTm lhsTy rhsTm rhsTy of
          Inl errs \<Rightarrow> Inl errs
        | Inr (cmpTm, _) \<Rightarrow> Inr cmpTm)
    | _ \<Rightarrow>
        \<comment> \<open>More comparisons follow - need to reuse rhsTm as next LHS.
           Resolve metas first so the RHS type is ground (needed for let-binding
           and to pass a concrete type to the next comparison).\<close>
        let (_, _, resolvedRhs, resolvedRhsTy) =
              resolve_binop_metas is_flex op lhsTm lhsTy rhsTm rhsTy
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
          \<comment> \<open>This check is now effectively dead code since resolve_binop_metas
             produces resolved types, but keeping it simplifies the correctness proof.\<close>
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
fun fold_implies_right :: "(nat \<Rightarrow> bool) \<Rightarrow> Location \<Rightarrow> GhostOrNot
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
fun process_binop_chain :: "(nat \<Rightarrow> bool) \<Rightarrow> Location \<Rightarrow> GhostOrNot
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

(* Phase 1: Unify each update field's actual type with the expected type from the parent,
   accumulating substitutions. Like unify_call_types but keyed by field name. *)
fun unify_update_types :: "(nat \<Rightarrow> bool) \<Rightarrow> Location
                          \<Rightarrow> (string \<times> CoreType) list \<Rightarrow> (string \<times> CoreType) list
                          \<Rightarrow> TypeSubst \<Rightarrow> TypeError list + TypeSubst" where
  "unify_update_types is_flex loc [] _ accSubst = Inr accSubst"
| "unify_update_types is_flex loc ((name, actualTy) # rest) parentFields accSubst =
    (case map_of parentFields name of
       Some expectedTy \<Rightarrow>
         let actualTy' = apply_subst accSubst actualTy;
             expectedTy' = apply_subst accSubst expectedTy
         in (case unify is_flex actualTy' expectedTy' of
               Some newSubst \<Rightarrow>
                 unify_update_types is_flex loc rest parentFields (compose_subst newSubst accSubst)
             | None \<Rightarrow>
                 if is_finite_integer_type actualTy' \<and> is_finite_integer_type expectedTy' then
                   \<comment> \<open>Cast will be inserted later\<close>
                   unify_update_types is_flex loc rest parentFields accSubst
                 else
                   Inl [TyErr_UpdateFieldTypeMismatch loc name expectedTy' actualTy'])
     | None \<Rightarrow> undefined)"  (* should not happen after check_update_fields_exist *)

(* Phase 2: Apply substitution to update terms and insert coercions where needed. *)
fun apply_update_coercions :: "TypeSubst \<Rightarrow> (string \<times> CoreTerm) list
                              \<Rightarrow> (string \<times> CoreType) list \<Rightarrow> (string \<times> CoreType) list
                              \<Rightarrow> (string \<times> CoreTerm) list" where
  "apply_update_coercions subst [] [] [] = []"
| "apply_update_coercions subst ((name, tm) # rest) ((_, actualTy) # actualRest) ((_, expectedTy) # expectedRest) =
    (let tm' = apply_subst_to_term subst tm;
         actualTy' = apply_subst subst actualTy;
         expectedTy' = apply_subst subst expectedTy;
         finalTm = (if actualTy' = expectedTy' then tm' else CoreTm_Cast expectedTy' tm')
     in (name, finalTm) # apply_update_coercions subst rest actualRest expectedRest)"
| "apply_update_coercions _ _ _ _ = undefined"

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

(* Combine unify_update_types and apply_update_coercions into a single function.
   Input: update field names + elaborated terms + actual types, and the parent field types.
   Output: coerced update terms (as a name-to-term map) and the final substitution. *)
definition unify_update_args ::
  "(nat \<Rightarrow> bool) \<Rightarrow> Location
   \<Rightarrow> string list \<Rightarrow> CoreTerm list \<Rightarrow> CoreType list
   \<Rightarrow> (string \<times> CoreType) list
   \<Rightarrow> TypeError list + ((string \<times> CoreTerm) list \<times> TypeSubst)" where
  "unify_update_args is_flex loc names tms actualTys parentFields =
    (let expectedTys = map (\<lambda>n. case map_of parentFields n of Some ty \<Rightarrow> ty) names
     in case unify_update_types is_flex loc (zip names actualTys) parentFields fmempty of
       Inl errs \<Rightarrow> Inl errs
     | Inr finalSubst \<Rightarrow>
         Inr (apply_update_coercions finalSubst (zip names tms)
                (zip names actualTys) (zip names expectedTys),
              finalSubst))"

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


(* Elaborate a term. Returns elaborated (core) term and type, or error.
   The nat parameter is the "next metavariable" counter - all generated metavariables
   will be >= this value, and the returned counter is the next available one. *)
fun elab_term :: "CoreTyEnv \<Rightarrow> Typedefs \<Rightarrow> GhostOrNot \<Rightarrow> BabTerm \<Rightarrow> nat
                 \<Rightarrow> TypeError list + (CoreTerm \<times> CoreType \<times> nat)"
and elab_term_list :: "CoreTyEnv \<Rightarrow> Typedefs \<Rightarrow> GhostOrNot \<Rightarrow> BabTerm list \<Rightarrow> nat
                      \<Rightarrow> TypeError list + (CoreTerm list \<times> CoreType list \<times> nat)" where

  (* Literals *)
  "elab_term env typedefs ghost (BabTm_Literal loc lit) next_mv =
    (case lit of
      BabLit_Bool b \<Rightarrow> Inr (CoreTm_LitBool b, CoreTy_Bool, next_mv)
    | BabLit_Int i \<Rightarrow> 
        (case get_type_for_int i of
          Some (sign, bits) \<Rightarrow> Inr (CoreTm_LitInt i, CoreTy_FiniteInt sign bits, next_mv)
        | None \<Rightarrow> Inl [TyErr_IntLiteralOutOfRange loc])
    | _ \<Rightarrow> undefined)"  (* TODO: Other literals *)

  (* Variables, data ctors - TODO *)
| "elab_term env typedefs ghost (BabTm_Name loc name tyArgs) next_mv = undefined"

  (* Casts *)
| "elab_term env typedefs ghost (BabTm_Cast loc targetTy operand) next_mv = 
    (case elab_type env typedefs ghost targetTy of
      Inl errs \<Rightarrow> Inl errs
    | Inr newTargetTy \<Rightarrow>
        (case elab_term env typedefs ghost operand next_mv of
          Inl errs \<Rightarrow> Inl errs
        | Inr (newOperand, operandTy, next_mv') \<Rightarrow>
            if is_integer_type newTargetTy then
              (case unify (\<lambda>n. n |\<notin>| TE_TypeVars env) operandTy newTargetTy of
                Some subst \<Rightarrow>
                  \<comment> \<open>Unification succeeded - we can eliminate the cast\<close>
                  Inr (apply_subst_to_term subst newOperand, newTargetTy, next_mv')
              | None \<Rightarrow>
                  if is_integer_type operandTy then
                    \<comment> \<open>Casting one integer type to another\<close>
                    Inr (CoreTm_Cast newTargetTy newOperand, newTargetTy, next_mv')
                  else
                    Inl [TyErr_InvalidCast loc])
            else
              Inl [TyErr_InvalidCast loc]))"

  (* If/then/else - elaborates to CoreTm_Match with True and False patterns *)
| "elab_term env typedefs ghost (BabTm_If loc condTm thenTm elseTm) next_mv =
    (case elab_term env typedefs ghost condTm next_mv of
      Inl errs \<Rightarrow> Inl errs
    | Inr (newCond, condTy, next_mv1) \<Rightarrow>
      (case elab_term env typedefs ghost thenTm next_mv1 of
        Inl errs \<Rightarrow> Inl errs
      | Inr (newThen, thenTy, next_mv2) \<Rightarrow>
        (case elab_term env typedefs ghost elseTm next_mv2 of
          Inl errs \<Rightarrow> Inl errs
        | Inr (newElse, elseTy, next_mv3) \<Rightarrow>
            \<comment> \<open>Unify the condition type against Bool. If the condition is already
                Bool this is a no-op; if it is a flex metavariable it gets bound. \<close>
            (case unify (\<lambda>n. n |\<notin>| TE_TypeVars env) condTy CoreTy_Bool of
              None \<Rightarrow> Inl [TyErr_ConditionNotBool loc condTy]
            | Some condSubst \<Rightarrow>
              let finalCond = apply_subst_to_term condSubst newCond in
                \<comment> \<open>Try to unify branch types\<close>
                (case unify (\<lambda>n. n |\<notin>| TE_TypeVars env) thenTy elseTy of
                  Some branchSubst \<Rightarrow>
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
| "elab_term env typedefs ghost (BabTm_Unop loc op operand) next_mv =
    (case elab_term env typedefs ghost operand next_mv of
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
                Inl [TyErr_NegateRequiresSigned loc]
          | BabUnop_Complement \<Rightarrow>
              if is_finite_integer_type operandTy then
                Inr (CoreTm_Unop CoreUnop_Complement newOperand, operandTy, next_mv')
              else
                Inl [TyErr_ComplementRequiresFiniteInt loc]
          | BabUnop_Not \<Rightarrow>
              Inl [TyErr_NotRequiresBool loc])))"

  (* Binary operator *)
| "elab_term env typedefs ghost (BabTm_Binop loc lhs operands) next_mv =
    (case elab_term env typedefs ghost lhs next_mv of
      Inl errs \<Rightarrow> Inl errs
    | Inr (newLhs, lhsTy, next_mv1) \<Rightarrow>
        \<comment> \<open>Elaborate all RHS terms using elab_term_list\<close>
        (case elab_term_list env typedefs ghost (map snd operands) next_mv1 of
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
| "elab_term env typedefs ghost (BabTm_Let loc varName rhs body) next_mv =
    (case elab_term env typedefs ghost rhs next_mv of
      Inl errs \<Rightarrow> Inl errs
    | Inr (rhsTm, rhsTy, next_mv1) \<Rightarrow>
        if \<not> list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)
        then Inl [TyErr_CannotInferType loc]
        else let env' = env \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars env),
                              TE_GhostLocals := (if ghost = Ghost
                                               then finsert varName (TE_GhostLocals env)
                                               else fminus (TE_GhostLocals env) {|varName|}),
                              TE_ConstLocals := finsert varName (TE_ConstLocals env) \<rparr>
             in (case elab_term env' typedefs ghost body next_mv1 of
                  Inl errs \<Rightarrow> Inl errs
                | Inr (bodyTm, bodyTy, next_mv2) \<Rightarrow>
                    Inr (CoreTm_Let varName rhsTm bodyTm, bodyTy, next_mv2)))"

  (* Quantifier: ghost-only, body must be Bool *)
| "elab_term env typedefs ghost (BabTm_Quantifier loc quant name ty tm) next_mv =
    (if ghost \<noteq> Ghost then Inl [TyErr_RequiresGhostContext loc]
     else case elab_type env typedefs ghost ty of
       Inl errs \<Rightarrow> Inl errs
     | Inr varTy \<Rightarrow>
         let env' = env \<lparr> TE_LocalVars := fmupd name varTy (TE_LocalVars env),
                          TE_GhostLocals := finsert name (TE_GhostLocals env) \<rparr>
         in (case elab_term env' typedefs ghost tm next_mv of
               Inl errs \<Rightarrow> Inl errs
             | Inr (bodyTm, bodyTy, next_mv') \<Rightarrow>
                 (case unify (\<lambda>n. n |\<notin>| TE_TypeVars env) bodyTy CoreTy_Bool of
                    None \<Rightarrow> Inl [TyErr_QuantifierBodyNotBool loc bodyTy]
                  | Some bodySubst \<Rightarrow>
                      let finalBody = apply_subst_to_term bodySubst bodyTm;
                          finalVarTy = apply_subst bodySubst varTy
                      in Inr (CoreTm_Quantifier quant name finalVarTy finalBody,
                              CoreTy_Bool, next_mv'))))"

  (* Function call *)
| "elab_term env typedefs ghost (BabTm_Call loc callee args) next_mv =
    (case determine_fun_call_type env typedefs ghost callee next_mv of
      Inl errs \<Rightarrow> Inl errs
    | Inr (fnName, tyArgs, expArgTypes, retType, next_mv1) \<Rightarrow>
        \<comment> \<open>Check argument count\<close>
        if length args \<noteq> length expArgTypes then
          Inl [TyErr_WrongNumberOfArgs loc fnName (length expArgTypes) (length args)]
        else
          \<comment> \<open>Elaborate argument terms\<close>
          (case elab_term_list env typedefs ghost args next_mv1 of
            Inl errs \<Rightarrow> Inl errs
          | Inr (elabArgTms, actualTypes, next_mv2) \<Rightarrow>
              \<comment> \<open>Unify actual types with expected types, accumulating substitutions\<close>
              (case unify_call_args (\<lambda>n. n |\<notin>| TE_TypeVars env) loc fnName 0 elabArgTms actualTypes expArgTypes fmempty of
                Inl errs \<Rightarrow> Inl errs
              | Inr (finalArgTms, finalSubst) \<Rightarrow>
                  \<comment> \<open>Apply final substitution to the type args and return type\<close>
                  let finalTyArgs = map (apply_subst finalSubst) tyArgs;
                      finalRetType = apply_subst finalSubst retType
                  in Inr (CoreTm_FunctionCall fnName finalTyArgs finalArgTms, finalRetType, next_mv2))))"

  (* Tuple: elaborated to a record with synthetic field names "0", "1", ... *)
| "elab_term env typedefs ghost (BabTm_Tuple loc tms) next_mv =
    (case elab_term_list env typedefs ghost tms next_mv of
      Inl errs \<Rightarrow> Inl errs
    | Inr (newTms, tys, next_mv') \<Rightarrow>
        let names = tuple_field_names (length tms) in
        Inr (CoreTm_Record (zip names newTms),
             CoreTy_Record (zip names tys),
             next_mv'))"

  (* Record *)
| "elab_term env typedefs ghost (BabTm_Record loc flds) next_mv =
    (case first_duplicate_name fst flds of
      Some dupName \<Rightarrow> Inl [TyErr_DuplicateFieldName loc dupName]
    | None \<Rightarrow>
        (case elab_term_list env typedefs ghost (map snd flds) next_mv of
          Inl errs \<Rightarrow> Inl errs
        | Inr (newTms, tys, next_mv') \<Rightarrow>
            let names = map fst flds in
            Inr (CoreTm_Record (zip names newTms),
                 CoreTy_Record (zip names tys),
                 next_mv')))"

  (* Record update *)
| "elab_term env typedefs ghost (BabTm_RecordUpdate loc tm flds) next_mv =
    (case first_duplicate_name fst flds of
      Some dupName \<Rightarrow> Inl [TyErr_DuplicateFieldName loc dupName]
    | None \<Rightarrow>
      (case elab_term env typedefs ghost tm next_mv of
        Inl errs \<Rightarrow> Inl errs
      | Inr (parentTm, parentTy, next_mv1) \<Rightarrow>
          (case parentTy of
            CoreTy_Record parentFields \<Rightarrow>
              (case check_update_fields_exist flds parentFields of
                Some badName \<Rightarrow> Inl [TyErr_UpdateFieldNotFound loc badName parentTy]
              | None \<Rightarrow>
                  (case elab_term_list env typedefs ghost (map snd flds) next_mv1 of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr (newUpdateTms, actualTypes, next_mv2) \<Rightarrow>
                      (case unify_update_args (\<lambda>n. n |\<notin>| TE_TypeVars env) loc
                              (map fst flds) newUpdateTms actualTypes parentFields of
                        Inl errs \<Rightarrow> Inl errs
                      | Inr (coercedUpdates, finalSubst) \<Rightarrow>
                          let (resultTm, resultTy) =
                                build_updated_record finalSubst parentTm parentFields coercedUpdates
                          in Inr (resultTm, resultTy, next_mv2))))
          | _ \<Rightarrow> Inl [TyErr_NotARecordType loc parentTy])))"

  (* Tuple projection: tuples are records with synthetic field names "0", "1", ... *)
| "elab_term env typedefs ghost (BabTm_TupleProj loc tm idx) next_mv =
    (case elab_term env typedefs ghost tm next_mv of
      Inl errs \<Rightarrow> Inl errs
    | Inr (newTm, tmTy, next_mv') \<Rightarrow>
        (case tmTy of
          CoreTy_Record fieldTypes \<Rightarrow>
            (case map_of fieldTypes (nat_to_string idx) of
              Some fldTy \<Rightarrow> Inr (CoreTm_RecordProj newTm (nat_to_string idx), fldTy, next_mv')
            | None \<Rightarrow> Inl [TyErr_TupleIndexOutOfRange loc idx tmTy])
        | _ \<Rightarrow> Inl [TyErr_NotARecordType loc tmTy]))"

  (* Record projection *)
| "elab_term env typedefs ghost (BabTm_RecordProj loc tm fldName) next_mv =
    (case elab_term env typedefs ghost tm next_mv of
      Inl errs \<Rightarrow> Inl errs
    | Inr (newTm, tmTy, next_mv') \<Rightarrow>
        (case tmTy of
          CoreTy_Record fieldTypes \<Rightarrow>
            (case map_of fieldTypes fldName of
              Some fldTy \<Rightarrow> Inr (CoreTm_RecordProj newTm fldName, fldTy, next_mv')
            | None \<Rightarrow> Inl [TyErr_FieldNotFound loc fldName tmTy])
        | _ \<Rightarrow> Inl [TyErr_NotARecordType loc tmTy]))"

  (* Array projection - TODO *)
| "elab_term env typedefs ghost (BabTm_ArrayProj loc tm idxs) next_mv = undefined"

  (* Match - TODO *)
| "elab_term env typedefs ghost (BabTm_Match loc scrut arms) next_mv = undefined"

  (* Sizeof: operand must be an array; allocatable dims require lvalue or ghost *)
| "elab_term env typedefs ghost (BabTm_Sizeof loc tm) next_mv =
    (case elab_term env typedefs ghost tm next_mv of
      Inl errs \<Rightarrow> Inl errs
    | Inr (newTm, tmTy, next_mv') \<Rightarrow>
        (case tmTy of
          CoreTy_Array _ dims \<Rightarrow>
            if list_ex (\<lambda>d. d = CoreDim_Allocatable) dims \<and> \<not> is_lvalue newTm \<and> ghost = NotGhost
            then Inl [TyErr_SizeofRequiresLvalue loc]
            else Inr (CoreTm_Sizeof newTm, sizeof_type dims, next_mv')
        | _ \<Rightarrow> Inl [TyErr_NotAnArrayType loc tmTy]))"

  (* Allocated: ghost-only, any operand type, result is Bool *)
| "elab_term env typedefs ghost (BabTm_Allocated loc tm) next_mv =
    (if ghost \<noteq> Ghost then Inl [TyErr_RequiresGhostContext loc]
     else case elab_term env typedefs ghost tm next_mv of
       Inl errs \<Rightarrow> Inl errs
     | Inr (newTm, _, next_mv') \<Rightarrow>
         Inr (CoreTm_Allocated newTm, CoreTy_Bool, next_mv'))"

  (* Old: ghost-only, result has same type as operand *)
| "elab_term env typedefs ghost (BabTm_Old loc tm) next_mv =
    (if ghost \<noteq> Ghost then Inl [TyErr_RequiresGhostContext loc]
     else case elab_term env typedefs ghost tm next_mv of
       Inl errs \<Rightarrow> Inl errs
     | Inr (newTm, tmTy, next_mv') \<Rightarrow>
         Inr (CoreTm_Old newTm, tmTy, next_mv'))"

  (* elab_term_list - Empty list case *)
| "elab_term_list _ _ _ [] next_mv = Inr ([], [], next_mv)"

  (* elab_term_list - Non-empty list case *)
| "elab_term_list env typedefs ghost (tm # tms) next_mv =
    (case elab_term env typedefs ghost tm next_mv of
      Inl errs1 \<Rightarrow>
        \<comment> \<open>Error in first term - continue processing rest to collect all errors\<close>
        (case elab_term_list env typedefs ghost tms next_mv of
          Inl errs2 \<Rightarrow> Inl (errs1 @ errs2)
        | Inr _ \<Rightarrow> Inl errs1)
    | Inr (tm', ty', next_mv') \<Rightarrow>
        \<comment> \<open>First term successful - collect results from remaining terms\<close>
        (case elab_term_list env typedefs ghost tms next_mv' of
          Inl errs \<Rightarrow> Inl errs
        | Inr (tms', tys', next_mv'') \<Rightarrow> Inr (tm' # tms', ty' # tys', next_mv'')))"


end
