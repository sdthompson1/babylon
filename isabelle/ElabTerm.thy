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

(* Note: the type returned by elab_term is fully resolved (does not contain typedefs).
   The nat parameter is the "next metavariable" counter - all generated metavariables
   will be >= this value, and the returned counter is the next available one. *)
fun elab_term :: "nat \<Rightarrow> Typedefs \<Rightarrow> BabTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> BabTerm \<Rightarrow> nat
                 \<Rightarrow> TypeError list + (BabTerm \<times> BabType \<times> nat)"
  where

  \<comment> \<open>Out of fuel case\<close>
  "elab_term 0 _ _ _ tm next_mv = Inl [TyErr_OutOfFuel (bab_term_location tm)]"

  \<comment> \<open>Main case - valid fuel\<close>
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
            \<comment> \<open>Not a variable: check data constructors\<close>
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

    | _ \<Rightarrow> undefined)"  \<comment> \<open>TODO: other cases\<close>

end
