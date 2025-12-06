theory ElabTerm
  imports ElabType
begin

(* This "elaborates" a Babylon program by adding implicit casts, filling in missing type
   annotations, etc, until the program is well-typed according to BabTypecheck.thy
   (or an error is found).
*)

(* Default type for unary operators when the operand type is ambiguous (a metavariable).
   Negate and Complement default to i32, Not defaults to Bool. *)
fun default_type_for_unop :: "Location \<Rightarrow> BabUnop \<Rightarrow> BabType" where
  "default_type_for_unop loc BabUnop_Negate = BabTy_FiniteInt loc Signed IntBits_32"
| "default_type_for_unop loc BabUnop_Complement = BabTy_FiniteInt loc Signed IntBits_32"
| "default_type_for_unop loc BabUnop_Not = BabTy_Bool loc"

lemma default_type_for_unop_is_runtime: "is_runtime_type (default_type_for_unop loc op)"
  by (cases op) simp_all

lemma default_type_for_unop_is_well_kinded: "is_well_kinded env (default_type_for_unop loc op)"
  by (cases op) simp_all

(* Try to coerce an argument term to an expected type by inserting an implicit cast.
   Only applies for finite integer types. *)
fun try_implicit_int_coercion :: "BabTerm \<Rightarrow> BabType \<Rightarrow> BabType \<Rightarrow> (BabTerm \<times> BabType) option" where
  "try_implicit_int_coercion tm (BabTy_FiniteInt _ _ _) (BabTy_FiniteInt loc2 sign2 bits2) =
     Some (BabTm_Cast (bab_term_location tm) (BabTy_FiniteInt loc2 sign2 bits2) tm,
           BabTy_FiniteInt loc2 sign2 bits2)"
| "try_implicit_int_coercion _ _ _ = None"

(* Coerce two terms to a common integer type by inserting implicit casts if needed.
   Only applies when both types are BabTy_FiniteInt. Returns None if no common type exists. *)
fun coerce_to_common_int_type :: "BabTerm \<Rightarrow> BabType \<Rightarrow> BabTerm \<Rightarrow> BabType
                                  \<Rightarrow> (BabTerm \<times> BabTerm \<times> BabType) option" where
  "coerce_to_common_int_type tm1 (BabTy_FiniteInt loc1 sign1 bits1)
                             tm2 (BabTy_FiniteInt loc2 sign2 bits2) =
    (case combine_int_types sign1 bits1 sign2 bits2 of
      None \<Rightarrow> None
    | Some (commonSign, commonBits) \<Rightarrow>
        let commonTy1 = BabTy_FiniteInt loc1 commonSign commonBits;
            commonTy2 = BabTy_FiniteInt loc2 commonSign commonBits;
            \<comment> \<open>Only wrap in cast if type differs from common type\<close>
            newTm1 = (if sign1 = commonSign \<and> bits1 = commonBits then tm1
                      else BabTm_Cast (bab_term_location tm1) commonTy1 tm1);
            newTm2 = (if sign2 = commonSign \<and> bits2 = commonBits then tm2
                      else BabTm_Cast (bab_term_location tm2) commonTy2 tm2)
        in Some (newTm1, newTm2, commonTy1))"
| "coerce_to_common_int_type _ _ _ _ = None"

(* Phase 1 of function call typechecking: 
   Unify actual argument types with expected types, accumulating substitutions.
   For each pair of types:
   1. Try unification - if it succeeds, accumulate the substitution
   2. If unification fails but both are finite integer types, that's OK (coercion will be inserted later)
   3. If both fail, return an error
   Returns just the final substitution. *)
fun unify_call_types :: "Location \<Rightarrow> string \<Rightarrow> nat \<Rightarrow> BabType list \<Rightarrow> BabType list
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
fun apply_call_coercions :: "MetaSubst \<Rightarrow> BabTerm list \<Rightarrow> BabType list \<Rightarrow> BabType list
                            \<Rightarrow> BabTerm list" where
  "apply_call_coercions subst [] [] [] = []"
| "apply_call_coercions subst (tm # tms) (actualTy # actualTys) (expectedTy # expectedTys) =
    (let tm' = apply_subst_to_term subst tm;
         actualTy' = apply_subst subst actualTy;
         expectedTy' = apply_subst subst expectedTy;
         \<comment> \<open>Insert cast if types differ (must be compatible integers at this point)\<close>
         finalTm = (if types_equal actualTy' expectedTy' then tm'
                    else BabTm_Cast (bab_term_location tm) expectedTy' tm')
     in finalTm # apply_call_coercions subst tms actualTys expectedTys)"
| "apply_call_coercions _ _ _ _ = undefined"

(* Combine unify_call_types and apply_call_coercions into a single function *)
definition unify_call_args :: "Location \<Rightarrow> string \<Rightarrow> nat \<Rightarrow> BabTerm list \<Rightarrow> BabType list
                              \<Rightarrow> BabType list \<Rightarrow> MetaSubst
                              \<Rightarrow> TypeError list + (BabTerm list \<times> MetaSubst)" where
  "unify_call_args loc fnName argIdx tms actualTys expectedTys accSubst =
    (case unify_call_types loc fnName argIdx actualTys expectedTys accSubst of
       Inl errs \<Rightarrow> Inl errs
     | Inr finalSubst \<Rightarrow> Inr (apply_call_coercions finalSubst tms actualTys expectedTys, finalSubst))"

(* This helper takes a "function term" and returns elaborated version, expected arg types,
   expected return type, function name (for error messages), and next metavariable
   number (or error list). *)
fun determine_fun_call_type :: "nat \<Rightarrow> Typedefs \<Rightarrow> BabTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> BabTerm \<Rightarrow> nat \<Rightarrow>
                            (TypeError list + BabTerm \<times> BabType list \<times> BabType \<times> string \<times> nat)"
where
  "determine_fun_call_type fuel typedefs env ghost (BabTm_Name fnLoc fnName tyArgs) next_mv =
    \<comment> \<open>Look up function in environment\<close>
    (case fmlookup (TE_Functions env) fnName of
      None \<Rightarrow> Inl [TyErr_UnknownFunction fnLoc fnName]
    | Some funDecl \<Rightarrow>
        \<comment> \<open>Check purity: only pure functions allowed in term context\<close>
        if DF_Impure funDecl then
          Inl [TyErr_ImpureFunctionInTermContext fnLoc fnName]
        else if list_ex (\<lambda>(_, vr, _). vr = Ref) (DF_TmArgs funDecl) then
          Inl [TyErr_RefArgInTermContext fnLoc fnName]
        \<comment> \<open>Check ghost constraint\<close>
        else if ghost = NotGhost \<and> DF_Ghost funDecl = Ghost then
          Inl [TyErr_GhostFunctionInNonGhost fnLoc fnName]
        \<comment> \<open>Check return type exists\<close>
        else (case DF_ReturnType funDecl of
          None \<Rightarrow> Inl [TyErr_FunctionNoReturnType fnLoc fnName]
        | Some retTy \<Rightarrow>
            (let numTyParams = length (DF_TyArgs funDecl) in
            \<comment> \<open>Handle type arguments: infer if omitted, elaborate if provided\<close>
            \<comment> \<open>This next `case` returns the new actual ty args and the new next_mv\<close>
            case
              (if tyArgs = [] \<and> numTyParams > 0 then
                \<comment> \<open>Generate fresh metavariables for the function's type arguments\<close>
                Inr (map BabTy_Meta [next_mv..<next_mv + numTyParams], next_mv + numTyParams)
              else if numTyParams = length tyArgs then
                \<comment> \<open>Elaborate the user's provided type arguments\<close>
                (case elab_type_list fuel typedefs env ghost tyArgs of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr newTyArgs \<Rightarrow> Inr (newTyArgs, next_mv))
              else
                Inl [TyErr_WrongTypeArity fnLoc fnName numTyParams (length tyArgs)])
            of
              Inl errs \<Rightarrow> Inl errs
            | Inr (newTyArgs, next_mv') \<Rightarrow>
                \<comment> \<open>Now just substitute the resolved type arguments into the original
                   function's argument and return types.\<close>
                let subst = fmap_of_list (zip (DF_TyArgs funDecl) newTyArgs);
                    newArgTypes = map (\<lambda>(_, _, ty). substitute_bab_type subst ty) (DF_TmArgs funDecl);
                    newRetType = substitute_bab_type subst retTy;
                    newTerm = BabTm_Name fnLoc fnName newTyArgs
                in Inr (newTerm, newArgTypes, newRetType, fnName, next_mv'))))"
| "determine_fun_call_type _ _ _ _ tm _ =
    Inl [TyErr_CalleeNotFunction (bab_term_location tm)]"


(* Elaborate a term. Creates a well-typed elaborated term (and returns its type),
   or fails with an error. A "list" version is also provided.
   The nat parameter is the "next metavariable" counter - all generated metavariables
   will be >= this value, and the returned counter is the next available one. *)
fun elab_term :: "nat \<Rightarrow> Typedefs \<Rightarrow> BabTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> BabTerm \<Rightarrow> nat
                 \<Rightarrow> TypeError list + (BabTerm \<times> BabType \<times> nat)"
and elab_term_list :: "nat \<Rightarrow> Typedefs \<Rightarrow> BabTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> BabTerm list \<Rightarrow> nat
                      \<Rightarrow> TypeError list + (BabTerm list \<times> BabType list \<times> nat)"
  where

  "elab_term 0 _ _ _ tm next_mv = Inl [TyErr_OutOfFuel (bab_term_location tm)]"

| "elab_term (Suc fuel) typedefs env ghost tm next_mv =
    (case tm of
      BabTm_Literal loc lit \<Rightarrow>
        (case lit of
          BabLit_Bool b \<Rightarrow> Inr (tm, BabTy_Bool loc, next_mv)
        | BabLit_Int i \<Rightarrow>
            (case get_type_for_int i of
              Some (sign, bits) \<Rightarrow> Inr (tm, BabTy_FiniteInt loc sign bits, next_mv)
            | None \<Rightarrow> Inl [TyErr_IntLiteralOutOfRange loc])
        | _ \<Rightarrow> undefined)  \<comment> \<open>TODO: other literals\<close>

    | BabTm_Cast loc targetTy operand \<Rightarrow>
        \<comment> \<open>Elaborate target type (checks groundness, resolves typedefs, kind-checks)\<close>
        (case elab_type fuel typedefs env ghost targetTy of
          Inl errs \<Rightarrow> Inl errs
        | Inr resolvedTargetTy \<Rightarrow>
            (case elab_term fuel typedefs env ghost operand next_mv of
              Inl errs \<Rightarrow> Inl errs
            | Inr (newOperand, operandTy, next_mv') \<Rightarrow>
                if is_integer_type resolvedTargetTy then
                  \<comment> \<open>Runtime check already done by elab_type\<close>
                  (case operandTy of
                    BabTy_Meta n \<Rightarrow>
                      \<comment> \<open>We can just eliminate the cast in this case\<close>
                      Inr (apply_subst_to_term (singleton_subst n resolvedTargetTy) newOperand,
                           resolvedTargetTy, next_mv')
                  | _ \<Rightarrow>
                      if is_integer_type operandTy then
                        \<comment> \<open>Casting one integer type to another\<close>
                        Inr (BabTm_Cast loc resolvedTargetTy newOperand, resolvedTargetTy, next_mv')
                      else
                        Inl [TyErr_InvalidCast loc])
                else
                  Inl [TyErr_InvalidCast loc]))

    | BabTm_Unop loc op operand \<Rightarrow>
        (case elab_term fuel typedefs env ghost operand next_mv of
          Inl errs \<Rightarrow> Inl errs
        | Inr (newOperand, operandTy, next_mv') \<Rightarrow>
            (case operandTy of
              BabTy_Meta n \<Rightarrow>
                \<comment> \<open>Ambiguous operand type: use default type for this operator\<close>
                let defaultTy = default_type_for_unop loc op;
                    specializedOperand = apply_subst_to_term (singleton_subst n defaultTy) newOperand
                in Inr (BabTm_Unop loc op specializedOperand, defaultTy, next_mv')
            | _ \<Rightarrow>
                (case op of
                  BabUnop_Negate \<Rightarrow>
                    if is_signed_integer_type operandTy then
                      Inr (BabTm_Unop loc op newOperand, operandTy, next_mv')
                    else
                      Inl [TyErr_NegateRequiresSigned loc]
                | BabUnop_Complement \<Rightarrow>
                    if is_finite_integer_type operandTy then
                      Inr (BabTm_Unop loc op newOperand, operandTy, next_mv')
                    else
                      Inl [TyErr_ComplementRequiresFiniteInt loc]
                | BabUnop_Not \<Rightarrow>
                    (case operandTy of
                      BabTy_Bool _ \<Rightarrow> Inr (BabTm_Unop loc op newOperand, operandTy, next_mv')
                    | _ \<Rightarrow> Inl [TyErr_NotRequiresBool loc]))))

    | BabTm_Name loc name tyArgs \<Rightarrow>
        (case fmlookup (TE_TermVars env) name of
          Some ty \<Rightarrow>
            \<comment> \<open>Term variable case\<close>
            if tyArgs \<noteq> [] then
              Inl [TyErr_WrongNumberOfTypeArgs loc name 0 (length tyArgs)]
            else if ghost = NotGhost \<and> name |\<in>| TE_GhostVars env then
              Inl [TyErr_GhostVariableInNonGhost loc name]
            else
              Inr (tm, ty, next_mv)
        | None \<Rightarrow>
            \<comment> \<open>Not a variable: check nullary data constructors\<close>
            (case fmlookup (TE_DataCtors env) name of
              Some (dtName, numTyArgs, payload) \<Rightarrow>
                if payload \<noteq> None then
                  Inl [TyErr_DataCtorHasPayload loc name]
                else if tyArgs = [] \<and> numTyArgs > 0 then
                  \<comment> \<open>User omitted type args: generate metavariables (no elaboration needed)\<close>
                  let actualTyArgs = map BabTy_Meta [next_mv..<next_mv + numTyArgs]
                  in Inr (BabTm_Name loc name actualTyArgs, BabTy_Name loc dtName actualTyArgs, next_mv + numTyArgs)
                else
                  \<comment> \<open>User provided type args: elaborate them\<close>
                  (case elab_type_list fuel typedefs env ghost tyArgs of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr resolvedTyArgs \<Rightarrow>
                      if length resolvedTyArgs \<noteq> numTyArgs then
                        Inl [TyErr_WrongNumberOfTypeArgs loc name numTyArgs (length tyArgs)]
                      else
                        Inr (BabTm_Name loc name resolvedTyArgs, BabTy_Name loc dtName resolvedTyArgs, next_mv))
            | None \<Rightarrow>
                Inl [TyErr_UnknownName loc name]))

    | BabTm_If loc cond thenTm elseTm \<Rightarrow>
        (case elab_term fuel typedefs env ghost cond next_mv of
          Inl errs \<Rightarrow> Inl errs
        | Inr (newCond, condTy, next_mv1) \<Rightarrow>
          (case elab_term fuel typedefs env ghost thenTm next_mv1 of
            Inl errs \<Rightarrow> Inl errs
          | Inr (newThen, thenTy, next_mv2) \<Rightarrow>
            (case elab_term fuel typedefs env ghost elseTm next_mv2 of
              Inl errs \<Rightarrow> Inl errs
            | Inr (newElse, elseTy, next_mv3) \<Rightarrow>
                \<comment> \<open>Specialize condition to Bool if it's a metavariable\<close>
                let (finalCond, finalCondTy) =
                  (case condTy of
                    BabTy_Meta n \<Rightarrow>
                      (apply_subst_to_term (singleton_subst n (BabTy_Bool loc)) newCond,
                       BabTy_Bool loc)
                  | _ \<Rightarrow> (newCond, condTy))
                in
                \<comment> \<open>Check condition is Bool\<close>
                (case finalCondTy of
                  BabTy_Bool _ \<Rightarrow>
                    \<comment> \<open>Try to unify branch types\<close>
                    (case unify thenTy elseTy of
                      Some branchSubst \<Rightarrow>
                        let thenTy' = apply_subst branchSubst thenTy;
                            newThen' = apply_subst_to_term branchSubst newThen;
                            newElse' = apply_subst_to_term branchSubst newElse
                        in Inr (BabTm_If loc finalCond newThen' newElse', thenTy', next_mv3)
                    | None \<Rightarrow>
                        \<comment> \<open>Unification failed - try implicit integer coercion\<close>
                        (case coerce_to_common_int_type newThen thenTy newElse elseTy of
                          Some (finalThen, finalElse, commonTy) \<Rightarrow>
                            Inr (BabTm_If loc finalCond finalThen finalElse, commonTy, next_mv3)
                        | None \<Rightarrow>
                            Inl [TyErr_TypeMismatch loc thenTy elseTy]))
                | _ \<Rightarrow> Inl [TyErr_ConditionNotBool loc finalCondTy]))))

    | BabTm_Call loc callTm argTms \<Rightarrow>
        (case determine_fun_call_type fuel typedefs env ghost callTm next_mv of
          Inl errs \<Rightarrow> Inl errs
        | Inr (newCallTm, expArgTypes, retType, fnName, next_mv1) \<Rightarrow>
            \<comment> \<open>Check argument count\<close>
            if length argTms \<noteq> length expArgTypes then
              Inl [TyErr_WrongNumberOfArgs loc fnName (length expArgTypes) (length argTms)]
            else
              \<comment> \<open>Elaborate argument terms\<close>
              (case elab_term_list fuel typedefs env ghost argTms next_mv1 of
                 Inl errs \<Rightarrow> Inl errs
               | Inr (elabArgTms, actualTypes, next_mv2) \<Rightarrow>
                   \<comment> \<open>Unify actual types with expected types, accumulating substitutions\<close>
                   (case unify_call_args loc fnName 0 elabArgTms actualTypes expArgTypes empty_subst of
                      Inl errs \<Rightarrow> Inl errs
                    | Inr (finalArgTms, finalSubst) \<Rightarrow>
                        \<comment> \<open>Apply final substitution to the call term and return type\<close>
                        let finalCallTm = apply_subst_to_term finalSubst newCallTm;
                            finalRetType = apply_subst finalSubst retType
                        in Inr (BabTm_Call loc finalCallTm finalArgTms, finalRetType, next_mv2))))

    | _ \<Rightarrow> undefined)"  \<comment> \<open>TODO: other cases\<close>

| "elab_term_list 0 _ _ _ _ _ = Inl [TyErr_OutOfFuel no_loc]"
| "elab_term_list (Suc fuel) _ _ _ [] next_mv = Inr ([], [], next_mv)"
| "elab_term_list (Suc fuel) typedefs env ghost (tm # tms) next_mv =
    (case elab_term fuel typedefs env ghost tm next_mv of
      Inl errs \<Rightarrow> Inl errs
    | Inr (tm', ty', next_mv') \<Rightarrow>
        (case elab_term_list fuel typedefs env ghost tms next_mv' of
          Inl errs \<Rightarrow> Inl errs
        | Inr (tms', tys', next_mv'') \<Rightarrow> Inr (tm' # tms', ty' # tys', next_mv'')))"

end
