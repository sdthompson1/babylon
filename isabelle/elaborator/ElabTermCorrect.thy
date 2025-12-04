theory ElabTermCorrect
  imports "ElabTerm" "ElabTypeCorrect" "../type_system/BabTypecheck" "Unify3"
begin

theorem elab_term_correct:
  assumes "elab_term fuel typedefs env ghost tm next_mv = Inr (newTm, ty, next_mv')"
      and "tyenv_well_formed env"
  shows "bab_term_type env ghost newTm = Some ty"
using assms
proof (induction fuel arbitrary: env ghost tm newTm ty next_mv next_mv')
  case NoFuel: 0
  then show ?case by simp
next
  case Fuel: (Suc fuel)
  then show ?case
  proof (cases tm)
    case (BabTm_Literal loc lit)
    then show ?thesis
    proof (cases lit)
      case (BabLit_Bool b)
      thus ?thesis using BabTm_Literal Fuel.prems by auto
    next
      case (BabLit_Int i)
      thus ?thesis using BabTm_Literal Fuel.prems by (cases "get_type_for_int i"; auto)
    next
      case (BabLit_String str)
      then show ?thesis sorry
    next
      case (BabLit_Array arr)
      then show ?thesis sorry
    qed

  next
    case (BabTm_Name loc name tyArgs)
    show ?thesis
    proof (cases "fmlookup (TE_TermVars env) name")
      case (Some varTy)
      \<comment> \<open>Term variable case\<close>
      from Fuel.prems BabTm_Name Some
      have tyArgs_empty: "tyArgs = []"
        and ghost_ok: "ghost = NotGhost \<longrightarrow> name |\<notin>| TE_GhostVars env"
        and results: "newTm = tm" "ty = varTy"
        by (auto split: if_splits)
      show ?thesis using Some tyArgs_empty ghost_ok results BabTm_Name by auto
    next
      case None
      \<comment> \<open>Not a variable: must be a data constructor\<close>
      show ?thesis
      proof (cases "fmlookup (TE_DataCtors env) name")
        case None2: None
        \<comment> \<open>Unknown name - elaboration would fail\<close>
        from Fuel.prems BabTm_Name None None2 show ?thesis by (auto split: if_splits)
      next
        case (Some ctorInfo)
        obtain dtName numTyArgs payload where ctor: "ctorInfo = (dtName, numTyArgs, payload)"
          by (cases ctorInfo) auto
        from Fuel.prems BabTm_Name None Some ctor
        have payload_none: "payload = None"
          by (auto split: if_splits sum.splits simp: Let_def)
        show ?thesis
        proof (cases "tyArgs = [] \<and> numTyArgs > 0")
          case True
          \<comment> \<open>User omitted type args: generate metavariables\<close>
          let ?actualTyArgs = "map BabTy_Meta [next_mv..<next_mv + numTyArgs]"
          from Fuel.prems BabTm_Name None Some ctor payload_none True
          have results: "newTm = BabTm_Name loc name ?actualTyArgs" "ty = BabTy_Name loc dtName ?actualTyArgs"
            by (auto split: if_splits simp: Let_def)
          have len_ok: "length ?actualTyArgs = numTyArgs" by simp
          have runtime_ok: "ghost = NotGhost \<longrightarrow> list_all is_runtime_type ?actualTyArgs"
            by (simp add: list_all_iff)
          have wk_ok: "list_all (is_well_kinded env) ?actualTyArgs"
            using list_all_is_well_kinded_meta by simp
          show ?thesis using None Some ctor payload_none len_ok runtime_ok wk_ok results by auto
        next
          case False
          \<comment> \<open>User provided type args: use elab_type_list\<close>
          from Fuel.prems BabTm_Name None Some ctor payload_none False
          obtain resolvedTyArgs where
            elab_ok: "elab_type_list fuel typedefs env ghost tyArgs = Inr resolvedTyArgs"
            and len_ok: "length resolvedTyArgs = numTyArgs"
            and results: "newTm = BabTm_Name loc name resolvedTyArgs" "ty = BabTy_Name loc dtName resolvedTyArgs"
            by (auto split: if_splits sum.splits simp: Let_def)
          \<comment> \<open>Use correctness lemmas from ElabTypeCorrect\<close>
          have runtime_ok: "ghost = NotGhost \<longrightarrow> list_all is_runtime_type resolvedTyArgs"
            using elab_ok elab_type_is_runtime(2) by (cases ghost; auto)
          have wk_ok: "list_all (is_well_kinded env) resolvedTyArgs"
            using elab_ok elab_type_is_well_kinded(2) by auto
          show ?thesis using None Some ctor payload_none len_ok runtime_ok wk_ok results by auto
        qed
      qed
    qed

  next
    case (BabTm_Cast loc targetTy operand)
    \<comment> \<open>Extract info from elaborator success - now uses elab_type\<close>
    from Fuel.prems BabTm_Cast obtain resolvedTargetTy newOperand operandTy next_mv1 where
      elab_target: "elab_type fuel typedefs env ghost targetTy = Inr resolvedTargetTy"
      and elab_operand: "elab_term fuel typedefs env ghost operand next_mv = Inr (newOperand, operandTy, next_mv1)"
      and target_is_int: "is_integer_type resolvedTargetTy"
      and result_ty: "ty = resolvedTargetTy"
      by (auto split: sum.splits if_splits BabType.splits)
    \<comment> \<open>Use correctness lemmas from ElabTypeCorrect\<close>
    have runtime_ok: "ghost = NotGhost \<longrightarrow> is_runtime_type resolvedTargetTy"
      using elab_target elab_type_is_runtime(1) by (cases ghost; auto)
    have wk_ok: "is_well_kinded env resolvedTargetTy"
      using elab_target elab_type_is_well_kinded(1) by auto
    \<comment> \<open>By IH, the elaborated operand typechecks\<close>
    have ih: "bab_term_type env ghost newOperand = Some operandTy"
      using Fuel.IH elab_operand Fuel.prems(2) by blast
    \<comment> \<open>Case split on whether operandTy is a metavariable\<close>
    show ?thesis
    proof (cases "\<exists>n. operandTy = BabTy_Meta n")
      case True
      \<comment> \<open>Metavariable case: cast is eliminated, substitution is applied\<close>
      then obtain n where meta: "operandTy = BabTy_Meta n" by auto
      from Fuel.prems BabTm_Cast elab_target elab_operand target_is_int meta
      have result_tm: "newTm = apply_subst_to_term (singleton_subst n resolvedTargetTy) newOperand"
        by (auto split: sum.splits if_splits)
      \<comment> \<open>Use apply_subst_to_term_preserves_typing\<close>
      have subst_wk: "\<forall>ty' \<in> fmran' (singleton_subst n resolvedTargetTy). is_well_kinded env ty'"
        using wk_ok by (simp add: fmran'_singleton_subst)
      have subst_range: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' (singleton_subst n resolvedTargetTy). is_runtime_type ty')"
        using runtime_ok by (simp add: fmran'_singleton_subst)
      have "bab_term_type env ghost (apply_subst_to_term (singleton_subst n resolvedTargetTy) newOperand)
            = Some (apply_subst (singleton_subst n resolvedTargetTy) operandTy)"
        using ih apply_subst_to_term_preserves_typing Fuel.prems(2) subst_wk subst_range by blast
      also have "apply_subst (singleton_subst n resolvedTargetTy) operandTy = resolvedTargetTy"
        using meta apply_subst_singleton by auto
      finally show ?thesis using result_tm result_ty by simp
    next
      case False
      \<comment> \<open>Non-metavariable case: regular cast\<close>
      have operand_is_int: "is_integer_type operandTy"
        using Fuel.prems BabTm_Cast elab_target elab_operand False
        by (cases operandTy; auto split: sum.splits if_splits)
      have result_tm: "newTm = BabTm_Cast loc resolvedTargetTy newOperand"
        using Fuel.prems BabTm_Cast elab_target elab_operand False
        by (cases operandTy; auto split: sum.splits if_splits)
      show ?thesis
        using ih operand_is_int target_is_int runtime_ok result_tm result_ty by auto
    qed

  next
    case (BabTm_If loc cond thenTm elseTm)
    \<comment> \<open>Extract the elaboration results for all three subterms\<close>
    from Fuel.prems BabTm_If obtain newCond condTy next_mv1 newThen thenTy next_mv2 newElse elseTy next_mv3 where
      elab_cond: "elab_term fuel typedefs env ghost cond next_mv = Inr (newCond, condTy, next_mv1)"
      and elab_then: "elab_term fuel typedefs env ghost thenTm next_mv1 = Inr (newThen, thenTy, next_mv2)"
      and elab_else: "elab_term fuel typedefs env ghost elseTm next_mv2 = Inr (newElse, elseTy, next_mv3)"
      by (auto split: sum.splits option.splits if_splits BabType.splits)
    \<comment> \<open>By IH, all three elaborated subterms typecheck\<close>
    have ih_cond: "bab_term_type env ghost newCond = Some condTy"
      using Fuel.IH elab_cond Fuel.prems(2) by blast
    have ih_then: "bab_term_type env ghost newThen = Some thenTy"
      using Fuel.IH elab_then Fuel.prems(2) by blast
    have ih_else: "bab_term_type env ghost newElse = Some elseTy"
      using Fuel.IH elab_else Fuel.prems(2) by blast

    \<comment> \<open>Determine the final condition and its type after potential specialization\<close>
    define finalCond finalCondTy where
      "finalCond = (case condTy of BabTy_Meta n \<Rightarrow> apply_subst_to_term (singleton_subst n (BabTy_Bool loc)) newCond | _ \<Rightarrow> newCond)"
      and "finalCondTy = (case condTy of BabTy_Meta n \<Rightarrow> BabTy_Bool loc | _ \<Rightarrow> condTy)"

    \<comment> \<open>Show finalCond typechecks to finalCondTy\<close>
    have final_cond_typed: "bab_term_type env ghost finalCond = Some finalCondTy"
    proof (cases "\<exists>n. condTy = BabTy_Meta n")
      case True
      then obtain n where meta: "condTy = BabTy_Meta n" by auto
      have subst_wk: "\<forall>ty' \<in> fmran' (singleton_subst n (BabTy_Bool loc)). is_well_kinded env ty'"
        by (simp add: fmran'_singleton_subst)
      have subst_range: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' (singleton_subst n (BabTy_Bool loc)). is_runtime_type ty')"
        by (simp add: fmran'_singleton_subst)
      have "bab_term_type env ghost (apply_subst_to_term (singleton_subst n (BabTy_Bool loc)) newCond)
            = Some (apply_subst (singleton_subst n (BabTy_Bool loc)) condTy)"
        using ih_cond apply_subst_to_term_preserves_typing Fuel.prems(2) subst_wk subst_range by blast
      also have "apply_subst (singleton_subst n (BabTy_Bool loc)) condTy = BabTy_Bool loc"
        using meta apply_subst_singleton by auto
      finally show ?thesis using meta finalCond_def finalCondTy_def by simp
    next
      case False
      then show ?thesis using ih_cond finalCond_def finalCondTy_def by (cases condTy; simp)
    qed

    \<comment> \<open>The elaborator checks that finalCondTy is Bool\<close>
    from Fuel.prems BabTm_If elab_cond elab_then elab_else
    obtain cond_loc where finalCondTy_is_Bool: "finalCondTy = BabTy_Bool cond_loc"
      by (auto split: sum.splits option.splits BabType.splits simp: finalCondTy_def Let_def)

    \<comment> \<open>Now handle the two cases: unification succeeds, or coercion is used\<close>
    show ?thesis
    proof (cases "unify thenTy elseTy")
      case (Some branchSubst)
      \<comment> \<open>Unification succeeded\<close>
      from Fuel.prems BabTm_If elab_cond elab_then elab_else Some
      have result_tm: "newTm = BabTm_If loc finalCond
                                 (apply_subst_to_term branchSubst newThen)
                                 (apply_subst_to_term branchSubst newElse)"
        and result_ty: "ty = apply_subst branchSubst thenTy"
        by (auto split: sum.splits option.splits BabType.splits simp: finalCond_def Let_def)

      \<comment> \<open>From unify_sound, the substituted types are equal\<close>
      from unify_sound[OF Some]
      have types_eq: "types_equal (apply_subst branchSubst thenTy) (apply_subst branchSubst elseTy)" .

      \<comment> \<open>Show the substituted branches typecheck\<close>
      \<comment> \<open>First establish that thenTy and elseTy are runtime and well-kinded\<close>
      have thenTy_runtime: "ghost = NotGhost \<longrightarrow> is_runtime_type thenTy"
        using ih_then bab_term_type_runtime_invariant Fuel.prems(2) by fastforce
      have elseTy_runtime: "ghost = NotGhost \<longrightarrow> is_runtime_type elseTy"
        using ih_else bab_term_type_runtime_invariant Fuel.prems(2) by fastforce
      have thenTy_wk: "is_well_kinded env thenTy"
        using ih_then bab_term_type_well_kinded Fuel.prems(2) by fastforce
      have elseTy_wk: "is_well_kinded env elseTy"
        using ih_else bab_term_type_well_kinded Fuel.prems(2) by fastforce
      have subst_wk: "\<forall>ty' \<in> fmran' branchSubst. is_well_kinded env ty'"
        using Some thenTy_wk elseTy_wk unify_preserves_well_kinded by blast
      have subst_range: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' branchSubst. is_runtime_type ty')"
        using Some thenTy_runtime elseTy_runtime unify_preserves_runtime by blast
      have then_typed: "bab_term_type env ghost (apply_subst_to_term branchSubst newThen)
                        = Some (apply_subst branchSubst thenTy)"
        using ih_then apply_subst_to_term_preserves_typing Fuel.prems(2) subst_wk subst_range by blast
      have else_typed: "bab_term_type env ghost (apply_subst_to_term branchSubst newElse)
                        = Some (apply_subst branchSubst elseTy)"
        using ih_else apply_subst_to_term_preserves_typing Fuel.prems(2) subst_wk subst_range by blast

      show ?thesis
        using final_cond_typed finalCondTy_is_Bool then_typed else_typed types_eq result_tm result_ty
        by (simp del: types_equal.simps)
    next
      case None
      \<comment> \<open>Unification failed - try integer coercion\<close>
      from Fuel.prems BabTm_If elab_cond elab_then elab_else None
      obtain finalThen finalElse commonTy where
        coerce_ok: "coerce_to_common_int_type newThen thenTy newElse elseTy = Some (finalThen, finalElse, commonTy)"
        and result_tm: "newTm = BabTm_If loc finalCond finalThen finalElse"
        and result_ty: "ty = commonTy"
        by (auto split: sum.splits option.splits BabType.splits simp: finalCond_def Let_def)

      \<comment> \<open>Analyze coerce_to_common_int_type\<close>
      from coerce_ok obtain loc1 sign1 bits1 loc2 sign2 bits2 commonSign commonBits where
        thenTy_int: "thenTy = BabTy_FiniteInt loc1 sign1 bits1"
        and elseTy_int: "elseTy = BabTy_FiniteInt loc2 sign2 bits2"
        and combine_ok: "combine_int_types sign1 bits1 sign2 bits2 = Some (commonSign, commonBits)"
        and commonTy_def: "commonTy = BabTy_FiniteInt loc1 commonSign commonBits"
        by (cases thenTy; cases elseTy; auto split: option.splits simp: Let_def)

      \<comment> \<open>Determine what finalThen and finalElse are\<close>
      define thenNeedsCast elseNeedsCast where
        "thenNeedsCast = (sign1 \<noteq> commonSign \<or> bits1 \<noteq> commonBits)"
        and "elseNeedsCast = (sign2 \<noteq> commonSign \<or> bits2 \<noteq> commonBits)"

      from coerce_ok thenTy_int elseTy_int combine_ok
      have finalThen_def: "finalThen = (if thenNeedsCast
                             then BabTm_Cast (bab_term_location newThen) (BabTy_FiniteInt loc1 commonSign commonBits) newThen
                             else newThen)"
        and finalElse_def: "finalElse = (if elseNeedsCast
                              then BabTm_Cast (bab_term_location newElse) (BabTy_FiniteInt loc2 commonSign commonBits) newElse
                              else newElse)"
        by (auto simp: Let_def thenNeedsCast_def elseNeedsCast_def)

      \<comment> \<open>Show finalThen typechecks to commonTy (or a types_equal type)\<close>
      have thenTy_is_int: "is_integer_type thenTy" using thenTy_int by simp
      have elseTy_is_int: "is_integer_type elseTy" using elseTy_int by simp
      have commonTy_is_int: "is_integer_type commonTy" using commonTy_def by simp
      have commonTy_runtime: "is_runtime_type commonTy" using commonTy_def by simp

      have finalThen_typed: "bab_term_type env ghost finalThen = Some commonTy"
      proof (cases thenNeedsCast)
        case True
        hence "finalThen = BabTm_Cast (bab_term_location newThen) (BabTy_FiniteInt loc1 commonSign commonBits) newThen"
          using finalThen_def by simp
        moreover have "bab_term_type env ghost (BabTm_Cast (bab_term_location newThen) commonTy newThen) = Some commonTy"
          using ih_then thenTy_is_int commonTy_is_int commonTy_runtime commonTy_def by auto
        ultimately show ?thesis using commonTy_def by simp
      next
        case False
        hence "sign1 = commonSign" "bits1 = commonBits" using thenNeedsCast_def by auto
        hence "thenTy = commonTy" using thenTy_int commonTy_def by simp
        moreover have "finalThen = newThen" using False finalThen_def by simp
        ultimately show ?thesis using ih_then by simp
      qed

      have finalElse_typed: "bab_term_type env ghost finalElse = Some (BabTy_FiniteInt loc2 commonSign commonBits)"
      proof (cases elseNeedsCast)
        case True
        hence "finalElse = BabTm_Cast (bab_term_location newElse) (BabTy_FiniteInt loc2 commonSign commonBits) newElse"
          using finalElse_def by simp
        moreover have "bab_term_type env ghost (BabTm_Cast (bab_term_location newElse) (BabTy_FiniteInt loc2 commonSign commonBits) newElse)
                       = Some (BabTy_FiniteInt loc2 commonSign commonBits)"
          using ih_else elseTy_is_int commonTy_is_int commonTy_runtime commonTy_def by auto
        ultimately show ?thesis by simp
      next
        case False
        hence "sign2 = commonSign" "bits2 = commonBits" using elseNeedsCast_def by auto
        hence "elseTy = BabTy_FiniteInt loc2 commonSign commonBits" using elseTy_int by simp
        moreover have "finalElse = newElse" using False finalElse_def by simp
        ultimately show ?thesis using ih_else by simp
      qed

      \<comment> \<open>The two branch types are types_equal\<close>
      have branches_eq: "types_equal commonTy (BabTy_FiniteInt loc2 commonSign commonBits)"
        using commonTy_def by simp

      show ?thesis
        using final_cond_typed finalCondTy_is_Bool finalThen_typed finalElse_typed branches_eq result_tm result_ty
        by (simp del: types_equal.simps)
    qed

  next
    case (BabTm_Unop loc op operand)
    \<comment> \<open>Extract common info from elaborator success\<close>
    from Fuel.prems BabTm_Unop obtain newOperand operandTy next_mv1 where
      elab_operand: "elab_term fuel typedefs env ghost operand next_mv = Inr (newOperand, operandTy, next_mv1)"
      by (auto split: sum.splits)
    \<comment> \<open>By IH, the elaborated operand typechecks\<close>
    have ih: "bab_term_type env ghost newOperand = Some operandTy"
      using Fuel.IH elab_operand Fuel.prems(2) by blast
    \<comment> \<open>Case split on whether operandTy is a metavariable\<close>
    show ?thesis
    proof (cases "\<exists>n. operandTy = BabTy_Meta n")
      case True
      \<comment> \<open>Metavariable case: operand is specialized to default type\<close>
      then obtain n where meta: "operandTy = BabTy_Meta n" by auto
      let ?defaultTy = "default_type_for_unop loc op"
      let ?specializedOperand = "apply_subst_to_term (singleton_subst n ?defaultTy) newOperand"
      from Fuel.prems BabTm_Unop elab_operand meta
      have result_tm: "newTm = BabTm_Unop loc op ?specializedOperand"
        and result_ty: "ty = ?defaultTy"
        by (auto split: sum.splits simp: Let_def)
      \<comment> \<open>Use apply_subst_to_term_preserves_typing\<close>
      have subst_wk: "\<forall>ty' \<in> fmran' (singleton_subst n ?defaultTy). is_well_kinded env ty'"
        using default_type_for_unop_is_well_kinded by (simp add: fmran'_singleton_subst)
      have subst_range: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' (singleton_subst n ?defaultTy). is_runtime_type ty')"
        using default_type_for_unop_is_runtime by (simp add: fmran'_singleton_subst)
      have "bab_term_type env ghost ?specializedOperand
            = Some (apply_subst (singleton_subst n ?defaultTy) operandTy)"
        using ih apply_subst_to_term_preserves_typing Fuel.prems(2) subst_wk subst_range by blast
      also have "apply_subst (singleton_subst n ?defaultTy) operandTy = ?defaultTy"
        using meta apply_subst_singleton by auto
      finally have specialized_typed: "bab_term_type env ghost ?specializedOperand = Some ?defaultTy" .
      \<comment> \<open>Show the unop typechecks based on default_type_for_unop\<close>
      show ?thesis
        using specialized_typed result_tm result_ty
        by (cases op; auto)
    next
      case False
      \<comment> \<open>Non-metavariable case: regular unop checking\<close>
      from Fuel.prems BabTm_Unop elab_operand False
      have result_tm: "newTm = BabTm_Unop loc op newOperand"
        and result_ty: "ty = operandTy"
        and type_ok: "(op = BabUnop_Negate \<longrightarrow> is_signed_integer_type operandTy)
                    \<and> (op = BabUnop_Complement \<longrightarrow> is_finite_integer_type operandTy)
                    \<and> (op = BabUnop_Not \<longrightarrow> (\<exists>bloc. operandTy = BabTy_Bool bloc))"
        by (cases operandTy; auto split: sum.splits BabUnop.splits if_splits BabType.splits)+
      show ?thesis
        using ih type_ok result_tm result_ty
        by (auto split: BabUnop.splits BabType.splits)
    qed

  next
    case (BabTm_Binop x61 x62 x63)
    then show ?thesis sorry
  next
    case (BabTm_Let x71 x72 x73 x74)
    then show ?thesis sorry
  next
    case (BabTm_Quantifier x81 x82 x83 x84 x85)
    then show ?thesis sorry
  next
    case (BabTm_Call x91 x92 x93)
    then show ?thesis sorry
  next
    case (BabTm_Tuple x101 x102)
    then show ?thesis sorry
  next
    case (BabTm_Record x111 x112)
    then show ?thesis sorry
  next
    case (BabTm_RecordUpdate x121 x122 x123)
    then show ?thesis sorry
  next
    case (BabTm_TupleProj x131 x132 x133)
    then show ?thesis sorry
  next
    case (BabTm_RecordProj x141 x142 x143)
    then show ?thesis sorry
  next
    case (BabTm_ArrayProj x151 x152 x153)
    then show ?thesis sorry
  next
    case (BabTm_Match x161 x162 x163)
    then show ?thesis sorry
  next
    case (BabTm_Sizeof x171 x172)
    then show ?thesis sorry
  next
    case (BabTm_Allocated x181 x182)
    then show ?thesis sorry
  next
    case (BabTm_Old x191 x192)
    then show ?thesis sorry
  qed
qed


end
