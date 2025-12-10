theory ElabTerm
  imports ElabType Unify SubstituteTypesInTerm
begin

(* Convert BabUnop to CoreUnop *)
fun unop_to_core :: "BabUnop \<Rightarrow> CoreUnop" where
  "unop_to_core BabUnop_Negate = CoreUnop_Negate"
| "unop_to_core BabUnop_Complement = CoreUnop_Complement"
| "unop_to_core BabUnop_Not = CoreUnop_Not"

(* Default type for unary operators when the operand type is ambiguous (a metavariable).
   Negate and Complement default to i32, Not defaults to Bool. *)
fun default_type_for_unop :: "CoreUnop \<Rightarrow> CoreType" where
  "default_type_for_unop CoreUnop_Negate = CoreTy_FiniteInt Signed IntBits_32"
| "default_type_for_unop CoreUnop_Complement = CoreTy_FiniteInt Signed IntBits_32"
| "default_type_for_unop CoreUnop_Not = CoreTy_Bool"

lemma default_type_for_unop_is_runtime: "is_runtime_type (default_type_for_unop op)"
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
                Inr (map CoreTy_Meta [next_mv..<next_mv + numTyParams], next_mv + numTyParams)
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
                    newArgTypes = map (apply_subst subst) (FI_TmArgs funInfo);
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
fun unify_call_types :: "Location \<Rightarrow> string \<Rightarrow> nat \<Rightarrow> CoreType list \<Rightarrow> CoreType list
                        \<Rightarrow> MetaSubst \<Rightarrow> TypeError list + MetaSubst" where
  "unify_call_types loc fnName argIdx [] [] accSubst = Inr accSubst"
| "unify_call_types loc fnName argIdx (actualTy # actualTys) (expectedTy # expectedTys) accSubst =
    \<comment> \<open>Apply accumulated substitution to both types before unifying\<close>
    (let actualTy' = apply_subst accSubst actualTy;
         expectedTy' = apply_subst accSubst expectedTy
     in case unify actualTy' expectedTy' of
       Some newSubst \<Rightarrow>
         \<comment> \<open>Unification succeeded - compose substitutions and continue\<close>
         let composedSubst = compose_subst newSubst accSubst
         in unify_call_types loc fnName (argIdx + 1) actualTys expectedTys composedSubst
     | None \<Rightarrow>
         \<comment> \<open>Unification failed - check if implicit integer coercion is possible\<close>
         (if is_finite_integer_type actualTy' \<and> is_finite_integer_type expectedTy' then
            \<comment> \<open>Both are finite integers - coercion will be inserted later\<close>
            unify_call_types loc fnName (argIdx + 1) actualTys expectedTys accSubst
          else
            Inl [TyErr_ArgTypeMismatch loc argIdx expectedTy' actualTy']))"
| "unify_call_types _ _ _ _ _ _ = undefined"

(* Phase 2 of function call argument typechecking:
   Apply substitution to terms and insert coercions where needed.
   For each term, apply the substitution. If the resulting actual type differs from
   the expected type (both must be finite integers at this point), insert a cast. *)
fun apply_call_coercions :: "MetaSubst \<Rightarrow> CoreTerm list \<Rightarrow> CoreType list \<Rightarrow> CoreType list
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
definition unify_call_args :: "Location \<Rightarrow> string \<Rightarrow> nat \<Rightarrow> CoreTerm list \<Rightarrow> CoreType list
                              \<Rightarrow> CoreType list \<Rightarrow> MetaSubst
                              \<Rightarrow> TypeError list + (CoreTerm list \<times> MetaSubst)" where
  "unify_call_args loc fnName argIdx tms actualTys expectedTys accSubst =
    (case unify_call_types loc fnName argIdx actualTys expectedTys accSubst of
       Inl errs \<Rightarrow> Inl errs
     | Inr finalSubst \<Rightarrow> Inr (apply_call_coercions finalSubst tms actualTys expectedTys, finalSubst))"


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
              (case operandTy of
                CoreTy_Meta n \<Rightarrow>
                  \<comment> \<open>We can just eliminate the cast in this case\<close>
                  Inr (apply_subst_to_term (singleton_subst n newTargetTy) newOperand,
                       newTargetTy, next_mv')
              | _ \<Rightarrow>
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
            \<comment> \<open>Specialize condition to Bool if it's a metavariable\<close>
            let (finalCond, finalCondTy) =
              (case condTy of
                CoreTy_Meta n \<Rightarrow>
                  (apply_subst_to_term (singleton_subst n CoreTy_Bool) newCond, CoreTy_Bool)
              | _ \<Rightarrow> (newCond, condTy))
            in
            \<comment> \<open>Check condition is Bool\<close>
            (case finalCondTy of
              CoreTy_Bool \<Rightarrow>
                \<comment> \<open>Try to unify branch types\<close>
                (case unify thenTy elseTy of
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
                        Inl [TyErr_TypeMismatch loc thenTy elseTy]))
            | _ \<Rightarrow> Inl [TyErr_ConditionNotBool loc finalCondTy]))))"

  (* Unary operator *)
| "elab_term env typedefs ghost (BabTm_Unop loc op operand) next_mv =
    (case elab_term env typedefs ghost operand next_mv of
      Inl errs \<Rightarrow> Inl errs
    | Inr (newOperand, operandTy, next_mv') \<Rightarrow>
        (case operandTy of
          CoreTy_Meta n \<Rightarrow>
            \<comment> \<open>Ambiguous operand type: use default type for this operator\<close>
            let cop = unop_to_core op;
                defaultTy = default_type_for_unop cop;
                newOperand2 = apply_subst_to_term (singleton_subst n defaultTy) newOperand
            in Inr (CoreTm_Unop cop newOperand2, defaultTy, next_mv')
        | _ \<Rightarrow>
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
              (case operandTy of
                CoreTy_Bool \<Rightarrow> Inr (CoreTm_Unop CoreUnop_Not newOperand, operandTy, next_mv')
              | _ \<Rightarrow> Inl [TyErr_NotRequiresBool loc]))))"

  (* Binary operator - TODO *)
| "elab_term env typedefs ghost (BabTm_Binop loc lhs operands) next_mv = undefined"

  (* Let - TODO *)
| "elab_term env typedefs ghost (BabTm_Let loc varName rhs body) next_mv = undefined"

  (* Quantifier - TODO *)
| "elab_term env typedefs ghost (BabTm_Quantifier loc quant name ty tm) next_mv = undefined"

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
              (case unify_call_args loc fnName 0 elabArgTms actualTypes expArgTypes fmempty of
                Inl errs \<Rightarrow> Inl errs
              | Inr (finalArgTms, finalSubst) \<Rightarrow>
                  \<comment> \<open>Apply final substitution to the type args and return type\<close>
                  let finalTyArgs = map (apply_subst finalSubst) tyArgs;
                      finalRetType = apply_subst finalSubst retType
                  in Inr (CoreTm_FunctionCall fnName finalTyArgs finalArgTms, finalRetType, next_mv2))))"

  (* Tuple - TODO *)
| "elab_term env typedefs ghost (BabTm_Tuple loc tms) next_mv = undefined"

  (* Record - TODO *)
| "elab_term env typedefs ghost (BabTm_Record loc flds) next_mv = undefined"

  (* Record update - TODO *)
| "elab_term env typedefs ghost (BabTm_RecordUpdate loc tm flds) next_mv = undefined"

  (* Tuple projection - TODO *)
| "elab_term env typedefs ghost (BabTm_TupleProj loc tm idx) next_mv = undefined"

  (* Record projection - TODO *)
| "elab_term env typedefs ghost (BabTm_RecordProj loc tm fldName) next_mv = undefined"

  (* Array projection - TODO *)
| "elab_term env typedefs ghost (BabTm_ArrayProj loc tm idxs) next_mv = undefined"

  (* Match - TODO *)
| "elab_term env typedefs ghost (BabTm_Match loc scrut arms) next_mv = undefined"

  (* Sizeof - TODO *)
| "elab_term env typedefs ghost (BabTm_Sizeof loc tm) next_mv = undefined"

  (* Allocated - TODO *)
| "elab_term env typedefs ghost (BabTm_Allocated loc tm) next_mv = undefined"

  (* Old - TODO *)
| "elab_term env typedefs ghost (BabTm_Old loc tm) next_mv = undefined"

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
