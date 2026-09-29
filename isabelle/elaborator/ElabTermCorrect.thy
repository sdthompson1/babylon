theory ElabTermCorrect
  imports ElabTermCorrectBinop
begin

(* ========================================================================== *)
(* Record update helper lemmas *)
(* ========================================================================== *)

(* A substitution whose domain is disjoint from TE_TypeVars env
   is the identity on all local variable types and the return type.
   This pattern recurs in If, Quantifier, Call, RecordUpdate, etc. *)
lemma flex_subst_identity_on_env:
  assumes dom_flex: "\<forall>n. n |\<in>| fmdom subst \<longrightarrow> n |\<notin>| TE_TypeVars env"
      and wf: "tyenv_well_formed env"
      and locals_eq: "TE_LocalVars env' = TE_LocalVars env"
      and ret_eq: "TE_ReturnType env' = TE_ReturnType env"
  shows "(\<forall>vname vty. fmlookup (TE_LocalVars env') vname = Some vty
                       \<longrightarrow> apply_subst subst vty = vty)
       \<and> apply_subst subst (TE_ReturnType env') = TE_ReturnType env'"
proof (intro conjI allI impI)
  fix vname vty
  assume lk: "fmlookup (TE_LocalVars env') vname = Some vty"
  with locals_eq have lk_env: "fmlookup (TE_LocalVars env) vname = Some vty" by simp
  from wf have "tyenv_vars_well_kinded env" unfolding tyenv_well_formed_def by simp
  with lk_env have "is_well_kinded env vty" unfolding tyenv_vars_well_kinded_def by blast
  hence "type_tyvars vty \<subseteq> fset (TE_TypeVars env)"
    using is_well_kinded_type_tyvars_subset by blast
  hence "type_tyvars vty \<inter> fset (fmdom subst) = {}" using dom_flex by auto
  thus "apply_subst subst vty = vty" by (rule apply_subst_disjoint_id)
next
  from wf have "tyenv_return_type_well_kinded env" unfolding tyenv_well_formed_def by simp
  hence "is_well_kinded env (TE_ReturnType env)" unfolding tyenv_return_type_well_kinded_def .
  hence "type_tyvars (TE_ReturnType env) \<subseteq> fset (TE_TypeVars env)"
    using is_well_kinded_type_tyvars_subset by blast
  hence "type_tyvars (TE_ReturnType env) \<inter> fset (fmdom subst) = {}" using dom_flex by auto
  hence "apply_subst subst (TE_ReturnType env) = TE_ReturnType env"
    by (rule apply_subst_disjoint_id)
  thus "apply_subst subst (TE_ReturnType env') = TE_ReturnType env'" using ret_eq by simp
qed


lemma check_update_fields_exist_sound:
  "check_update_fields_exist flds parentFields = None \<Longrightarrow>
   \<forall>(name, _) \<in> set flds. map_of parentFields name \<noteq> None"
  by (induction flds) (auto split: if_splits)

lemma build_record_update_map_fst:
  "map fst (build_record_update parentTm iterFields updates) = map fst iterFields"
  by (induction parentTm iterFields updates rule: build_record_update.induct)
     (auto split: option.splits)

lemma build_record_update_length:
  "length (build_record_update parentTm iterFields updates) = length iterFields"
  using build_record_update_map_fst by (metis length_map)

(* Correctness of build_record_update:
   For each field in parentFields, the result term is either a projection from the
   parent (for unchanged fields) or the corresponding update term. In either case,
   it typechecks to the field's type. *)
lemma build_record_update_correct_aux:
  assumes parent_typed: "core_term_type env ghost parentTm = Some (CoreTy_Record allFields)"
      and updates_typed: "\<forall>(name, tm) \<in> set updates.
             \<exists>ty. map_of allFields name = Some ty
                \<and> core_term_type env ghost tm = Some ty"
      and iterFields_subset: "\<forall>(name, ty) \<in> set iterFields. map_of allFields name = Some ty"
  shows "list_all2 (\<lambda>(name, tm) (_, ty). core_term_type env ghost tm = Some ty)
           (build_record_update parentTm iterFields updates) iterFields"
  using iterFields_subset updates_typed parent_typed
proof (induction parentTm iterFields updates rule: build_record_update.induct)
  case (1 parent updates)
  then show ?case by simp
next
  case (2 parent name ty rest updates)
  have name_in: "map_of allFields name = Some ty"
    using "2.prems"(1) by simp
  have rest_subset: "\<forall>(n, t) \<in> set rest. map_of allFields n = Some t"
    using "2.prems"(1) by simp

  show ?case
  proof (cases "map_of updates name")
    case (Some newTm)
    from Some have in_updates: "(name, newTm) \<in> set updates" by (rule map_of_SomeD)
    from "2.prems"(2) in_updates
    have "\<exists>ty'. map_of allFields name = Some ty'
                \<and> core_term_type env ghost newTm = Some ty'"
      by auto
    with name_in have head_typed: "core_term_type env ghost newTm = Some ty" by simp
    have "list_all2 (\<lambda>(name, tm) (_, ty). core_term_type env ghost tm = Some ty)
                     (build_record_update parent rest updates) rest"
      using "2.IH"(2)[OF Some] rest_subset "2.prems"(2,3) by simp
    with head_typed show ?thesis using Some by simp
  next
    case None
    have proj_typed: "core_term_type env ghost (CoreTm_RecordProj parent name) = Some ty"
      using "2.prems"(3) name_in by simp
    have "list_all2 (\<lambda>(name, tm) (_, ty). core_term_type env ghost tm = Some ty)
                     (build_record_update parent rest updates) rest"
      using "2.IH"(1)[OF None] rest_subset "2.prems"(2,3) by simp
    with proj_typed show ?thesis using None by simp
  qed
qed

lemma build_record_update_correct:
  assumes "core_term_type env ghost parentTm = Some (CoreTy_Record parentFields)"
      and "\<forall>(name, tm) \<in> set updates.
             \<exists>ty. map_of parentFields name = Some ty
                \<and> core_term_type env ghost tm = Some ty"
      and "distinct (map fst parentFields)"
  shows "list_all2 (\<lambda>(name, tm) (_, ty). core_term_type env ghost tm = Some ty)
           (build_record_update parentTm parentFields updates) parentFields"
proof -
  have "\<forall>(name, ty) \<in> set parentFields. map_of parentFields name = Some ty"
    using assms(3) by simp
  thus ?thesis using build_record_update_correct_aux[OF assms(1) assms(2)] by simp
qed


(* ========================================================================== *)
(* Helper lemmas for specific cases of elab_term_correct *)
(* ========================================================================== *)

(* Helper lemma for BabTm_Call case of elab_term_correct.
   Given that the arg terms are already well-typed in env',
   and the elaboration of the Call succeeds, the result typechecks. *)
lemma elab_term_correct_call:
  assumes
    elab_eq: "elab_term env elabEnv ghost (BabTm_Call loc callee args) next_mv
              = Inr (newTm, ty, next_mv')"
    and wf: "tyenv_well_formed env"
    and td_wf: "elabenv_well_formed env elabEnv"
    and fresh: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n next_mv"
    \<comment> \<open>Sub-elaboration results\<close>
    and resolve_eq: "resolve_callee env elabEnv ghost callee next_mv
                     = Inr (calleeName, expArgTypes, calleeInfo, next_mv1)"
    and elab_args: "elab_term_list env elabEnv ghost args next_mv1
                    = Inr (elabArgTms, actualTypes, next_mv2)"
    \<comment> \<open>IH result lifted to the full extended env\<close>
    and ih_args: "list_all2 (\<lambda>tm ty. core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost tm = Some ty)
                  elabArgTms actualTypes"
  shows "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost newTm = Some ty"
proof -
  let ?is_flex = "(\<lambda>n. n |\<notin>| TE_TypeVars env)"
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"

  \<comment> \<open>Extract shared results from the elaboration\<close>
  from elab_eq resolve_eq have len_args: "length args = length expArgTypes"
    by (auto simp: build_call_result_def Let_def split: if_splits sum.splits CalleeInfo.splits prod.splits)
  from elab_eq resolve_eq len_args elab_args obtain finalArgTms finalSubst where
    unify_args: "unify_and_coerce ?is_flex (\<lambda>idx. bab_term_location (args ! idx))
                     elabArgTms actualTypes expArgTypes fmempty
                 = Inr (finalArgTms, finalSubst)"
    by (auto simp: build_call_result_def Let_def split: sum.splits CalleeInfo.splits prod.splits)
  obtain resultTm resultTy where
    build_eq: "build_call_result env ghost loc calleeInfo finalSubst finalArgTms
               = (resultTm, resultTy)"
    by (cases "build_call_result env ghost loc calleeInfo finalSubst finalArgTms") auto
  from elab_eq resolve_eq len_args elab_args unify_args build_eq
  have result_eq: "newTm = resultTm" "ty = resultTy" "next_mv' = next_mv2"
    by (auto simp: build_call_result_def Let_def unify_and_coerce_def
             split: sum.splits CalleeInfo.splits if_splits prod.splits)

  \<comment> \<open>Properties from resolve_callee_correct (at next_mv1)\<close>
  let ?env1 = "extend_env_with_tyvars env ghost next_mv next_mv1"
  have rc: "next_mv \<le> next_mv1
          \<and> callee_info_valid ?env1 ghost calleeInfo expArgTypes
          \<and> list_all (is_well_kinded ?env1) expArgTypes
          \<and> (ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env1) expArgTypes)"
    using resolve_callee_correct[OF resolve_eq wf td_wf] by simp
  have mono_1: "next_mv \<le> next_mv1" using rc by simp
  have mono_2: "next_mv1 \<le> next_mv2"
    using elab_term_list_next_mv_monotone[OF elab_args] .
  have wf': "tyenv_well_formed ?env'"
    using wf tyenv_well_formed_extend_env_with_tyvars by blast

  \<comment> \<open>next_mv' = next_mv2, so ?env' = extend_env_with_tyvars env ghost next_mv next_mv2\<close>
  have env'_eq: "?env' = extend_env_with_tyvars env ghost next_mv next_mv2"
    using result_eq by simp

  \<comment> \<open>Lift expArgTypes well-kindedness/runtime from ?env1 to ?env'\<close>
  have expArgTypes_wk: "list_all (is_well_kinded ?env') expArgTypes"
  proof (simp add: list_all_iff env'_eq, intro ballI)
    fix t assume "t \<in> set expArgTypes"
    with rc have "is_well_kinded ?env1 t" by (simp add: list_all_iff)
    thus "is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv2) t"
      using is_well_kinded_extend_env_with_tyvars_mono mono_2 by blast
  qed
  have expArgTypes_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env') expArgTypes"
  proof (intro impI)
    assume ng: "ghost = NotGhost"
    show "list_all (is_runtime_type ?env') expArgTypes"
      unfolding list_all_iff env'_eq
    proof (intro ballI)
      fix t assume "t \<in> set expArgTypes"
      with rc ng have "is_runtime_type ?env1 t" by (simp add: list_all_iff)
      thus "is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv2) t"
        using is_runtime_type_extend_env_with_tyvars_mono mono_2 by blast
    qed
  qed

  \<comment> \<open>Lift callee_info_valid from ?env1 to ?env'\<close>
  have civ: "callee_info_valid ?env' ghost calleeInfo expArgTypes"
    using callee_info_valid_mono[OF _ mono_1 mono_2] rc env'_eq
    by (metis callee_info_valid_mono mono_2 order_refl)

  \<comment> \<open>Well-kindedness and runtime for actualTypes in ?env'\<close>
  have len_elabArgTms: "length elabArgTms = length actualTypes"
    using ih_args by (simp add: list_all2_lengthD)
  have len_actualTypes: "length actualTypes = length expArgTypes"
    using len_args elab_args by (simp add: elab_term_list_length)

  have actualTypes_wk: "list_all (is_well_kinded ?env') actualTypes"
  proof (simp add: list_all_length, intro allI impI)
    fix i assume "i < length actualTypes"
    with ih_args have "core_term_type ?env' ghost (elabArgTms ! i) = Some (actualTypes ! i)"
      by (simp add: list_all2_conv_all_nth)
    thus "is_well_kinded ?env' (actualTypes ! i)"
      using wf' core_term_type_well_kinded by blast
  qed
  have actualTypes_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env') actualTypes"
    using ih_args wf' core_term_type_notghost_runtime
    by (auto simp: list_all2_conv_all_nth list_all_length)

  \<comment> \<open>Extract unify_type_lists from unify_and_coerce\<close>
  obtain unifySubst where
    unify_types: "unify_type_lists ?is_flex (\<lambda>idx. bab_term_location (args ! idx)) 0
                     actualTypes expArgTypes fmempty = Inr unifySubst" and
    finalArgTms_eq: "finalArgTms = apply_call_coercions unifySubst elabArgTms actualTypes expArgTypes" and
    finalSubst_eq: "finalSubst = unifySubst"
  proof -
    from unify_args show ?thesis
      by (auto simp: unify_and_coerce_def split: sum.splits intro: that)
  qed

  \<comment> \<open>Apply unify_type_lists_correct\<close>
  have empty_dom_flex: "\<forall>n. n |\<in>| fmdom (fmempty :: TypeSubst) \<longrightarrow> ?is_flex n" by simp
  have empty_cp: "\<forall>ty \<in> fmran' (fmempty :: TypeSubst). is_complete_type ty"
    by (simp add: fmran'_def)
  have unify_correct: "(\<forall>ty \<in> fmran' finalSubst. is_well_kinded ?env' ty)
       \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type ?env' ty))
       \<and> list_all2 (\<lambda>actualTy expectedTy.
           apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
           \<or> coercible (apply_subst finalSubst actualTy) (apply_subst finalSubst expectedTy))
         actualTypes expArgTypes
       \<and> (\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> ?is_flex n)
       \<and> (\<forall>ty \<in> fmran' finalSubst. is_complete_type ty)"
    using unify_type_lists_correct[OF unify_types wf' len_actualTypes
            actualTypes_wk expArgTypes_wk _ actualTypes_rt expArgTypes_rt _ empty_dom_flex]
          finalSubst_eq empty_cp by fastforce

  from unify_correct have
    finalSubst_wk: "\<forall>ty \<in> fmran' finalSubst. is_well_kinded ?env' ty" and
    finalSubst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type ?env' ty)" and
    types_unified: "list_all2 (\<lambda>actualTy expectedTy.
           apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
           \<or> coercible (apply_subst finalSubst actualTy) (apply_subst finalSubst expectedTy))
         actualTypes expArgTypes" and
    finalSubst_dom_flex: "\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> ?is_flex n" and
    finalSubst_cp: "\<forall>ty \<in> fmran' finalSubst. is_complete_type ty"
    by blast+

  \<comment> \<open>Subst doesn't affect locals or return type\<close>
  have env'_locals: "TE_LocalVars ?env' = TE_LocalVars env"
    unfolding extend_env_with_tyvars_def by simp
  have env'_ret: "TE_ReturnType ?env' = TE_ReturnType env"
    unfolding extend_env_with_tyvars_def by simp
  from flex_subst_identity_on_env[OF finalSubst_dom_flex wf env'_locals env'_ret]
  have locals_unaffected: "\<And>name ty'. fmlookup (TE_LocalVars ?env') name = Some ty'
                                      \<Longrightarrow> apply_subst finalSubst ty' = ty'"
    and ret_unaffected: "apply_subst finalSubst (TE_ReturnType ?env') = TE_ReturnType ?env'"
    by blast+
  have env'_abs: "TE_AbstractTypes ?env' = TE_AbstractTypes env"
    unfolding extend_env_with_tyvars_def by simp
  have abs_no_subst: "\<And>n. n |\<in>| TE_AbstractTypes ?env' \<Longrightarrow> fmlookup finalSubst n = None"
    using flex_subst_abs_no_subst[OF finalSubst_dom_flex[rule_format] wf env'_abs] .

  \<comment> \<open>Coerced args typecheck with substituted expected types\<close>
  have coerce_correct: "list_all2 (\<lambda>tm expectedTy.
           core_term_type ?env' ghost tm = Some (apply_subst finalSubst expectedTy))
         finalArgTms expArgTypes"
    using apply_call_coercions_correct[OF ih_args types_unified wf'
            finalSubst_wk finalSubst_rt len_elabArgTms len_actualTypes
            locals_unaffected ret_unaffected abs_no_subst expArgTypes_wk expArgTypes_rt
            finalSubst_cp]
          finalArgTms_eq finalSubst_eq by simp

  \<comment> \<open>env' extends env with only type variables\<close>
  have env'_locals: "TE_LocalVars ?env' = TE_LocalVars env"
    unfolding extend_env_with_tyvars_def by simp
  have env'_ret: "TE_ReturnType ?env' = TE_ReturnType env"
    unfolding extend_env_with_tyvars_def by simp
  have env'_abs: "TE_AbstractTypes ?env' = TE_AbstractTypes env"
    unfolding extend_env_with_tyvars_def by simp

  \<comment> \<open>Apply build_call_result_correct\<close>
  show ?thesis
    using build_call_result_correct[OF build_eq civ wf' wf coerce_correct
            finalSubst_wk finalSubst_rt finalSubst_dom_flex env'_locals env'_ret env'_abs
            finalSubst_cp]
          result_eq by simp
qed

(* Helper lemma for BabTm_ArrayProj case of elab_term_correct.
   Given that the array and index sub-terms are already well-typed in env',
   and the elaboration of the ArrayProj succeeds, the result typechecks. *)
lemma elab_term_correct_array_proj:
  assumes
    elab_eq: "elab_term env elabEnv ghost (BabTm_ArrayProj loc tm idxs) next_mv
              = Inr (newTm, ty, next_mv')"
    and wf: "tyenv_well_formed env"
    and fresh: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n next_mv"
    \<comment> \<open>Sub-elaboration results\<close>
    and elab_arr: "elab_term env elabEnv ghost tm next_mv = Inr (newArr, arrTy, next_mv1)"
    and elab_idxs: "elab_term_list env elabEnv ghost idxs next_mv1
                    = Inr (elabIdxTms, actualTypes, next_mv2)"
    \<comment> \<open>IH results lifted to the full extended env\<close>
    and ih_arr: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost newArr
                 = Some arrTy"
    and ih_idxs: "list_all2 (\<lambda>tm ty. core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost tm = Some ty)
                  elabIdxTms actualTypes"
  shows "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost newTm = Some ty"
proof -
  let ?is_flex = "(\<lambda>n. n |\<notin>| TE_TypeVars env)"
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  let ?locOf = "(\<lambda>idx. bab_term_location (idxs ! idx))"

  \<comment> \<open>Extract array type\<close>
  from elab_eq elab_arr obtain elemTy dims where
    arr_ty: "arrTy = CoreTy_Array elemTy dims"
    by (auto simp: unify_and_coerce_def split: sum.splits CoreType.splits if_splits)
  from elab_eq elab_arr arr_ty have len_eq: "length idxs = length dims"
    by (auto simp: unify_and_coerce_def split: sum.splits if_splits)

  let ?expectedTypes = "replicate (length dims) u64_type"

  from elab_eq elab_arr arr_ty len_eq elab_idxs
  obtain coercedIdxTms finalSubst where
    unify_result: "unify_and_coerce ?is_flex ?locOf elabIdxTms actualTypes ?expectedTypes fmempty
                   = Inr (coercedIdxTms, finalSubst)"
    by (auto simp: unify_and_coerce_def split: sum.splits)
  from elab_eq elab_arr arr_ty len_eq elab_idxs unify_result
  have result_eq: "newTm = CoreTm_ArrayProj newArr coercedIdxTms" "ty = elemTy"
    by auto

  have wf': "tyenv_well_formed ?env'"
    using wf tyenv_well_formed_extend_env_with_tyvars by blast

  \<comment> \<open>Lengths\<close>
  have len_elabIdxTms: "length elabIdxTms = length actualTypes"
    using ih_idxs by (simp add: list_all2_lengthD)
  have len_idxs_actual: "length elabIdxTms = length idxs"
    using elab_idxs elab_term_list_length by fastforce
  have len_actual_expected: "length actualTypes = length ?expectedTypes"
    using len_elabIdxTms len_idxs_actual len_eq by simp

  \<comment> \<open>Well-kindedness and runtime for actualTypes\<close>
  have actualTypes_wk: "list_all (is_well_kinded ?env') actualTypes"
  proof (simp add: list_all_length, intro allI impI)
    fix i assume "i < length actualTypes"
    with ih_idxs have "core_term_type ?env' ghost (elabIdxTms ! i) = Some (actualTypes ! i)"
      by (simp add: list_all2_conv_all_nth len_elabIdxTms)
    thus "is_well_kinded ?env' (actualTypes ! i)"
      using core_term_type_well_kinded wf' by blast
  qed
  have actualTypes_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env') actualTypes"
    using ih_idxs wf' core_term_type_notghost_runtime
    by (auto simp: list_all2_conv_all_nth list_all_length len_elabIdxTms)

  \<comment> \<open>Well-kindedness and runtime for expectedTypes (replicate of u64_type) — trivial\<close>
  have expectedTypes_wk: "list_all (is_well_kinded ?env') ?expectedTypes"
    by (simp add: list_all_length u64_type_def)
  have expectedTypes_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env') ?expectedTypes"
    by (simp add: list_all_length u64_type_def)

  \<comment> \<open>Extract unify_type_lists result from unify_and_coerce\<close>
  obtain unifySubst where
    unify_types: "unify_type_lists ?is_flex ?locOf 0 actualTypes ?expectedTypes fmempty = Inr unifySubst" and
    coercedIdxTms_eq: "coercedIdxTms = apply_call_coercions unifySubst elabIdxTms actualTypes ?expectedTypes" and
    finalSubst_eq: "finalSubst = unifySubst"
  proof -
    from unify_result show ?thesis
      by (auto simp: unify_and_coerce_def split: sum.splits intro: that)
  qed

  \<comment> \<open>Apply unify_type_lists_correct\<close>
  have empty_wk: "\<forall>ty \<in> fmran' (fmempty :: TypeSubst). is_well_kinded ?env' ty"
    by (simp add: fmran'_def)
  have empty_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' (fmempty :: TypeSubst). is_runtime_type ?env' ty)"
    by (simp add: fmran'_def)
  have empty_dom: "\<forall>n. n |\<in>| fmdom (fmempty :: TypeSubst) \<longrightarrow> ?is_flex n" by simp
  have empty_cp: "\<forall>ty \<in> fmran' (fmempty :: TypeSubst). is_complete_type ty"
    by (simp add: fmran'_def)

  have unify_correct: "(\<forall>ty \<in> fmran' unifySubst. is_well_kinded ?env' ty)
       \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' unifySubst. is_runtime_type ?env' ty))
       \<and> list_all2 (\<lambda>actualTy expectedTy.
           apply_subst unifySubst actualTy = apply_subst unifySubst expectedTy
           \<or> coercible (apply_subst unifySubst actualTy) (apply_subst unifySubst expectedTy))
         actualTypes ?expectedTypes
       \<and> (\<forall>n. n |\<in>| fmdom unifySubst \<longrightarrow> ?is_flex n)
       \<and> (\<forall>ty \<in> fmran' unifySubst. is_complete_type ty)"
    using unify_type_lists_correct[OF unify_types
            wf' len_actual_expected actualTypes_wk expectedTypes_wk empty_wk
            actualTypes_rt expectedTypes_rt empty_rt empty_dom] empty_cp by blast

  have finalSubst_wk: "\<forall>ty \<in> fmran' finalSubst. is_well_kinded ?env' ty"
    using unify_correct finalSubst_eq by simp
  have finalSubst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type ?env' ty)"
    using unify_correct finalSubst_eq by simp
  have finalSubst_dom_flex: "\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> ?is_flex n"
    using unify_correct finalSubst_eq by simp
  have finalSubst_cp: "\<forall>ty \<in> fmran' finalSubst. is_complete_type ty"
    using unify_correct finalSubst_eq by simp
  have types_unified: "list_all2 (\<lambda>actualTy expectedTy.
           apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
           \<or> coercible (apply_subst finalSubst actualTy) (apply_subst finalSubst expectedTy))
         actualTypes ?expectedTypes"
    using unify_correct finalSubst_eq by simp

  \<comment> \<open>Subst doesn't affect locals or return type\<close>
  have env'_locals: "TE_LocalVars ?env' = TE_LocalVars env"
    unfolding extend_env_with_tyvars_def by simp
  have env'_ret: "TE_ReturnType ?env' = TE_ReturnType env"
    unfolding extend_env_with_tyvars_def by simp
  from flex_subst_identity_on_env[OF finalSubst_dom_flex wf env'_locals env'_ret]
  have locals_unaffected: "\<And>vname vty. fmlookup (TE_LocalVars ?env') vname = Some vty
                                       \<Longrightarrow> apply_subst finalSubst vty = vty"
    and ret_unaffected: "apply_subst finalSubst (TE_ReturnType ?env') = TE_ReturnType ?env'"
    by blast+
  have env'_abs: "TE_AbstractTypes ?env' = TE_AbstractTypes env"
    unfolding extend_env_with_tyvars_def by simp
  have abs_no_subst: "\<And>n. n |\<in>| TE_AbstractTypes ?env' \<Longrightarrow> fmlookup finalSubst n = None"
    using flex_subst_abs_no_subst[OF finalSubst_dom_flex[rule_format] wf env'_abs] .

  \<comment> \<open>Apply apply_call_coercions_correct — coerced index terms have type u64_type\<close>
  have coerced_typed: "list_all2 (\<lambda>tm expectedTy.
           core_term_type ?env' ghost tm = Some (apply_subst finalSubst expectedTy))
         coercedIdxTms ?expectedTypes"
    using apply_call_coercions_correct[OF ih_idxs types_unified wf'
            finalSubst_wk finalSubst_rt len_elabIdxTms len_actual_expected
            locals_unaffected ret_unaffected abs_no_subst expectedTypes_wk expectedTypes_rt
            finalSubst_cp]
          coercedIdxTms_eq finalSubst_eq by simp

  \<comment> \<open>apply_subst on u64_type is identity\<close>
  have subst_u64: "apply_subst finalSubst u64_type = u64_type"
    by (simp add: u64_type_def)

  \<comment> \<open>Each coerced index term types to u64_type\<close>
  have idx_typed: "list_all (\<lambda>tm. core_term_type ?env' ghost tm = Some u64_type) coercedIdxTms"
  proof (simp add: list_all_length, intro allI impI)
    fix i assume i_lt: "i < length coercedIdxTms"
    have len_coerced: "length coercedIdxTms = length ?expectedTypes"
      using coerced_typed by (simp add: list_all2_lengthD)
    with i_lt have "core_term_type ?env' ghost (coercedIdxTms ! i)
                    = Some (apply_subst finalSubst (?expectedTypes ! i))"
      using coerced_typed by (simp add: list_all2_conv_all_nth)
    moreover have "?expectedTypes ! i = u64_type"
      using i_lt len_coerced by simp
    ultimately show "core_term_type ?env' ghost (coercedIdxTms ! i) = Some u64_type"
      using subst_u64 by simp
  qed

  \<comment> \<open>Array sub-term types to CoreTy_Array elemTy dims\<close>
  have ih_arr': "core_term_type ?env' ghost newArr = Some (CoreTy_Array elemTy dims)"
    using ih_arr arr_ty by simp

  \<comment> \<open>Length of coerced index terms = length of dims\<close>
  have len_coerced_dims: "length coercedIdxTms = length dims"
  proof -
    have "length coercedIdxTms = length ?expectedTypes"
      using coerced_typed by (simp add: list_all2_lengthD)
    thus ?thesis by simp
  qed

  \<comment> \<open>Put it together via the CoreTm_ArrayProj typing rule\<close>
  show ?thesis
    using result_eq ih_arr' idx_typed len_coerced_dims
    by (simp add: list_all_length u64_type_def)
qed


(* Helper lemma for BabLit_Array case of elab_term_correct.
   Given that the element sub-terms are already well-typed in env', and the
   elaboration of the array literal succeeds, the result typechecks. *)
lemma elab_term_correct_array_lit:
  assumes
    elab_eq: "elab_term env elabEnv ghost (BabTm_Literal loc (BabLit_Array tms)) next_mv
              = Inr (newTm, ty, next_mv')"
    and wf: "tyenv_well_formed env"
    and fresh: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n next_mv"
    \<comment> \<open>Sub-elaboration result: the element list elaborates using (next_mv + 1) for
        freshness, because next_mv itself is reserved for the element-type meta.\<close>
    and elab_elems: "elab_term_list env elabEnv ghost tms (next_mv + 1)
                     = Inr (elabTms, actualTypes, next_mv1)"
    \<comment> \<open>IH result lifted to the full extended env\<close>
    and ih_elems: "list_all2 (\<lambda>tm ty. core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost tm = Some ty)
                   elabTms actualTypes"
  shows "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost newTm = Some ty"
proof -
  let ?is_flex = "(\<lambda>n. n |\<notin>| TE_TypeVars env)"
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  let ?locOf = "(\<lambda>idx::nat. bab_term_location (tms ! idx))"
  let ?elemTy = "CoreTy_Var (mv_name next_mv)"
  let ?expectedTypes = "replicate (length elabTms) ?elemTy"

  \<comment> \<open>Length check holds (otherwise elab_eq would produce Inl)\<close>
  from elab_eq have len_ok: "int_in_range (int_range Unsigned IntBits_64) (int (length tms))"
    by (auto split: if_splits)

  \<comment> \<open>next_mv' = next_mv1 (no fresh metas after the element list)\<close>
  from elab_eq len_ok elab_elems obtain coercedTms finalSubst where
    unify_result: "unify_and_coerce ?is_flex ?locOf elabTms actualTypes ?expectedTypes fmempty
                   = Inr (coercedTms, finalSubst)"
    by (auto simp: Let_def unify_and_coerce_def split: sum.splits prod.splits)
  from elab_eq len_ok elab_elems unify_result have
    next_mv_eq: "next_mv' = next_mv1" and
    newTm_eq: "newTm = CoreTm_LitArray (apply_subst finalSubst ?elemTy) coercedTms" and
    ty_eq: "ty = CoreTy_Array (apply_subst finalSubst ?elemTy)
                              [CoreDim_Fixed (int (length coercedTms))]"
    by (auto simp: Let_def split: sum.splits prod.splits)

  have wf': "tyenv_well_formed ?env'"
    using wf tyenv_well_formed_extend_env_with_tyvars by blast

  \<comment> \<open>Fresh meta next_mv is a type var (and runtime in NotGhost mode) in ?env'\<close>
  have next_mv_lt: "next_mv < next_mv'"
  proof -
    from elab_term_list_next_mv_monotone[OF elab_elems] have "next_mv + 1 \<le> next_mv1" .
    thus ?thesis using next_mv_eq by simp
  qed
  have next_mv_in: "mv_name next_mv |\<in>| TE_TypeVars ?env'"
    unfolding extend_env_with_tyvars_def using next_mv_lt by auto
  have next_mv_rt: "ghost = NotGhost \<Longrightarrow> mv_name next_mv |\<in>| TE_RuntimeTypeVars ?env'"
    unfolding extend_env_with_tyvars_def using next_mv_lt by auto

  \<comment> \<open>Lengths\<close>
  have len_elabTms: "length elabTms = length actualTypes"
    using ih_elems by (simp add: list_all2_lengthD)
  have len_expected: "length actualTypes = length ?expectedTypes"
    using len_elabTms by simp

  \<comment> \<open>Well-kindedness and runtime for actualTypes in ?env'\<close>
  have actualTypes_wk: "list_all (is_well_kinded ?env') actualTypes"
  proof (simp add: list_all_length, intro allI impI)
    fix i assume "i < length actualTypes"
    with ih_elems have "core_term_type ?env' ghost (elabTms ! i) = Some (actualTypes ! i)"
      by (simp add: list_all2_conv_all_nth len_elabTms)
    thus "is_well_kinded ?env' (actualTypes ! i)"
      using core_term_type_well_kinded wf' by blast
  qed
  have actualTypes_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env') actualTypes"
    using ih_elems wf' core_term_type_notghost_runtime
    by (auto simp: list_all2_conv_all_nth list_all_length len_elabTms)

  \<comment> \<open>Well-kindedness and runtime for expectedTypes (replicate of CoreTy_Var next_mv)\<close>
  have elemTy_wk: "is_well_kinded ?env' ?elemTy"
    using next_mv_in by simp
  have elemTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type ?env' ?elemTy"
    using next_mv_rt by simp
  have expectedTypes_wk: "list_all (is_well_kinded ?env') ?expectedTypes"
    using elemTy_wk by (simp add: list_all_length)
  have expectedTypes_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env') ?expectedTypes"
    using elemTy_rt by (simp add: list_all_length)

  \<comment> \<open>Extract unify_type_lists result from unify_and_coerce\<close>
  obtain unifySubst where
    unify_types: "unify_type_lists ?is_flex ?locOf 0 actualTypes ?expectedTypes fmempty = Inr unifySubst" and
    coercedTms_eq: "coercedTms = apply_call_coercions unifySubst elabTms actualTypes ?expectedTypes" and
    finalSubst_eq: "finalSubst = unifySubst"
  proof -
    from unify_result show ?thesis
      by (auto simp: unify_and_coerce_def split: sum.splits intro: that)
  qed

  \<comment> \<open>Apply unify_type_lists_correct\<close>
  have empty_wk: "\<forall>ty \<in> fmran' (fmempty :: TypeSubst). is_well_kinded ?env' ty"
    by (simp add: fmran'_def)
  have empty_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' (fmempty :: TypeSubst). is_runtime_type ?env' ty)"
    by (simp add: fmran'_def)
  have empty_dom: "\<forall>n. n |\<in>| fmdom (fmempty :: TypeSubst) \<longrightarrow> ?is_flex n" by simp
  have empty_cp: "\<forall>ty \<in> fmran' (fmempty :: TypeSubst). is_complete_type ty"
    by (simp add: fmran'_def)

  have unify_correct: "(\<forall>ty \<in> fmran' unifySubst. is_well_kinded ?env' ty)
       \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' unifySubst. is_runtime_type ?env' ty))
       \<and> list_all2 (\<lambda>actualTy expectedTy.
           apply_subst unifySubst actualTy = apply_subst unifySubst expectedTy
           \<or> coercible (apply_subst unifySubst actualTy) (apply_subst unifySubst expectedTy))
         actualTypes ?expectedTypes
       \<and> (\<forall>n. n |\<in>| fmdom unifySubst \<longrightarrow> ?is_flex n)
       \<and> (\<forall>ty \<in> fmran' unifySubst. is_complete_type ty)"
    using unify_type_lists_correct[OF unify_types
            wf' len_expected actualTypes_wk expectedTypes_wk empty_wk
            actualTypes_rt expectedTypes_rt empty_rt empty_dom] empty_cp by blast

  have finalSubst_wk: "\<forall>ty \<in> fmran' finalSubst. is_well_kinded ?env' ty"
    using unify_correct finalSubst_eq by simp
  have finalSubst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type ?env' ty)"
    using unify_correct finalSubst_eq by simp
  have finalSubst_dom_flex: "\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> ?is_flex n"
    using unify_correct finalSubst_eq by simp
  have finalSubst_cp: "\<forall>ty \<in> fmran' finalSubst. is_complete_type ty"
    using unify_correct finalSubst_eq by simp
  have types_unified: "list_all2 (\<lambda>actualTy expectedTy.
           apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
           \<or> coercible (apply_subst finalSubst actualTy) (apply_subst finalSubst expectedTy))
         actualTypes ?expectedTypes"
    using unify_correct finalSubst_eq by simp

  \<comment> \<open>Subst doesn't affect locals or return type\<close>
  have env'_locals: "TE_LocalVars ?env' = TE_LocalVars env"
    unfolding extend_env_with_tyvars_def by simp
  have env'_ret: "TE_ReturnType ?env' = TE_ReturnType env"
    unfolding extend_env_with_tyvars_def by simp
  from flex_subst_identity_on_env[OF finalSubst_dom_flex wf env'_locals env'_ret]
  have locals_unaffected: "\<And>vname vty. fmlookup (TE_LocalVars ?env') vname = Some vty
                                       \<Longrightarrow> apply_subst finalSubst vty = vty"
    and ret_unaffected: "apply_subst finalSubst (TE_ReturnType ?env') = TE_ReturnType ?env'"
    by blast+
  have env'_abs: "TE_AbstractTypes ?env' = TE_AbstractTypes env"
    unfolding extend_env_with_tyvars_def by simp
  have abs_no_subst: "\<And>n. n |\<in>| TE_AbstractTypes ?env' \<Longrightarrow> fmlookup finalSubst n = None"
    using flex_subst_abs_no_subst[OF finalSubst_dom_flex[rule_format] wf env'_abs] .

  \<comment> \<open>Apply apply_call_coercions_correct — coerced element terms type to subst(elemTy)\<close>
  let ?finalElemTy = "apply_subst finalSubst ?elemTy"
  have coerced_typed: "list_all2 (\<lambda>tm expectedTy.
           core_term_type ?env' ghost tm = Some (apply_subst finalSubst expectedTy))
         coercedTms ?expectedTypes"
    using apply_call_coercions_correct[OF ih_elems types_unified wf'
            finalSubst_wk finalSubst_rt len_elabTms len_expected
            locals_unaffected ret_unaffected abs_no_subst expectedTypes_wk expectedTypes_rt
            finalSubst_cp]
          coercedTms_eq finalSubst_eq by simp

  have len_coerced: "length coercedTms = length elabTms"
    using coerced_typed by (simp add: list_all2_lengthD)

  \<comment> \<open>Each coerced element typechecks to finalElemTy\<close>
  have elems_typed: "\<forall>i < length coercedTms.
        core_term_type ?env' ghost (coercedTms ! i) = Some ?finalElemTy"
  proof (intro allI impI)
    fix i assume i_lt: "i < length coercedTms"
    from coerced_typed i_lt len_coerced
    have "core_term_type ?env' ghost (coercedTms ! i)
          = Some (apply_subst finalSubst (?expectedTypes ! i))"
      by (simp add: list_all2_conv_all_nth)
    moreover have "?expectedTypes ! i = ?elemTy"
      using i_lt len_coerced by simp
    ultimately show "core_term_type ?env' ghost (coercedTms ! i) = Some ?finalElemTy"
      by simp
  qed
  hence elems_typed_list: "list_all (\<lambda>tm. core_term_type ?env' ghost tm = Some ?finalElemTy) coercedTms"
    by (simp add: list_all_length)

  \<comment> \<open>finalElemTy is well-kinded and (in NotGhost mode) runtime\<close>
  have finalElemTy_wk: "is_well_kinded ?env' ?finalElemTy"
    using elemTy_wk finalSubst_wk
    by (auto intro!: apply_subst_preserves_well_kinded[where src="?env'" and tgt="?env'"]
             simp: fmran'I split: option.splits)
  have finalElemTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type ?env' ?finalElemTy"
  proof (intro impI)
    assume ng: "ghost = NotGhost"
    show "is_runtime_type ?env' ?finalElemTy"
      using elemTy_rt ng finalSubst_rt
      by (auto intro!: apply_subst_preserves_runtime[where src="?env'" and tgt="?env'"]
               simp: fmran'I split: option.splits)
  qed

  \<comment> \<open>Length of coerced list equals length of tms, so length check carries over\<close>
  have len_tms: "length tms = length elabTms"
    using elab_term_list_length[OF elab_elems] by simp
  have len_ok': "int_in_range (int_range Unsigned IntBits_64) (int (length coercedTms))"
    using len_ok len_tms len_coerced by simp

  \<comment> \<open>Assemble\<close>
  show ?thesis
    using newTm_eq ty_eq finalElemTy_wk finalElemTy_rt elems_typed_list len_ok'
    by simp
qed


(* Helper lemma for BabTm_RecordUpdate case of elab_term_correct.
   Given that the parent and update sub-terms are already well-typed in env',
   and the elaboration of the RecordUpdate succeeds, the result typechecks. *)
lemma elab_term_correct_record_update:
  assumes
    elab_eq: "elab_term env elabEnv ghost (BabTm_RecordUpdate loc tm flds) next_mv
              = Inr (newTm, ty, next_mv')"
    and wf: "tyenv_well_formed env"
    and fresh: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n next_mv"
    \<comment> \<open>Sub-elaboration results\<close>
    and elab_parent: "elab_term env elabEnv ghost tm next_mv = Inr (parentTm, parentTy, next_mv1)"
    and elab_updates: "elab_term_list env elabEnv ghost (map snd flds) next_mv1
                       = Inr (newUpdateTms, actualTypes, next_mv2)"
    \<comment> \<open>IH results lifted to the full extended env\<close>
    and ih_parent: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost parentTm
                    = Some parentTy"
    and ih_updates: "list_all2 (\<lambda>tm ty. core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost tm = Some ty)
                     newUpdateTms actualTypes"
  shows "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost newTm = Some ty"
proof -
  let ?is_flex = "(\<lambda>n. n |\<notin>| TE_TypeVars env)"
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  let ?locOf = "(\<lambda>idx. bab_term_location (snd (flds ! idx)))"

  \<comment> \<open>Extract elaboration sub-results from elab_eq\<close>
  from elab_eq have no_dup: "first_duplicate_name fst flds = None"
    by (auto split: option.splits)
  from elab_eq no_dup elab_parent obtain parentFields where
    parent_rec: "parentTy = CoreTy_Record parentFields"
    by (auto simp: Let_def unify_and_coerce_def build_updated_record_def
             split: sum.splits CoreType.splits option.splits if_splits prod.splits)
  from elab_eq no_dup elab_parent parent_rec have
    fields_exist: "check_update_fields_exist flds parentFields = None"
    by (auto simp: Let_def unify_and_coerce_def build_updated_record_def
             split: sum.splits option.splits if_splits prod.splits)

  let ?expectedTypes = "map (\<lambda>(name, _). the (map_of parentFields name)) flds"

  from elab_eq no_dup elab_parent parent_rec fields_exist elab_updates
  obtain coercedTms finalSubst where
    unify_result: "unify_and_coerce ?is_flex ?locOf newUpdateTms actualTypes ?expectedTypes fmempty
                   = Inr (coercedTms, finalSubst)"
    by (auto simp: Let_def build_updated_record_def
             split: sum.splits option.splits if_splits prod.splits)

  let ?coercedUpdates = "zip (map fst flds) coercedTms"

  from elab_eq no_dup elab_parent parent_rec fields_exist elab_updates unify_result
  have result_eq:
    "newTm = fst (build_updated_record finalSubst parentTm parentFields ?coercedUpdates)"
    "ty = snd (build_updated_record finalSubst parentTm parentFields ?coercedUpdates)"
    by (auto simp: Let_def split: prod.splits)

  \<comment> \<open>Specialize IH results to parentFields\<close>
  have ih_parent': "core_term_type ?env' ghost parentTm = Some (CoreTy_Record parentFields)"
    using ih_parent parent_rec by simp

  have wf': "tyenv_well_formed ?env'"
    using wf tyenv_well_formed_extend_env_with_tyvars by blast

  \<comment> \<open>Lengths\<close>
  have len_updates: "length newUpdateTms = length actualTypes"
    using ih_updates by (simp add: list_all2_lengthD)
  have len_flds: "length newUpdateTms = length flds"
    using elab_updates elab_term_list_length by fastforce
  have len_flds_actual: "length flds = length actualTypes"
    using len_flds len_updates by simp
  have len_expected: "length actualTypes = length ?expectedTypes"
    using len_flds_actual by simp

  \<comment> \<open>Well-kindedness and runtime for actualTypes in ?env'\<close>
  have actualTypes_wk: "list_all (is_well_kinded ?env') actualTypes"
  proof (simp add: list_all_length, intro allI impI)
    fix i assume "i < length actualTypes"
    with ih_updates have "core_term_type ?env' ghost (newUpdateTms ! i) = Some (actualTypes ! i)"
      by (simp add: list_all2_conv_all_nth len_updates)
    thus "is_well_kinded ?env' (actualTypes ! i)"
      using core_term_type_well_kinded wf' by blast
  qed

  have actualTypes_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env') actualTypes"
    using ih_updates wf' core_term_type_notghost_runtime
    by (auto simp: list_all2_conv_all_nth list_all_length len_updates)

  \<comment> \<open>Well-kindedness and runtime for parentFields in ?env'\<close>
  have parent_ty_wk: "is_well_kinded ?env' (CoreTy_Record parentFields)"
    using core_term_type_well_kinded[OF ih_parent' wf'] .
  hence parentFields_wk: "\<forall>(name, ty) \<in> set parentFields. is_well_kinded ?env' ty"
    by (auto simp: list_all_iff)

  have parentFields_rt: "ghost = NotGhost \<longrightarrow>
      (\<forall>(name, ty) \<in> set parentFields. is_runtime_type ?env' ty)"
  proof (intro impI)
    assume ng: "ghost = NotGhost"
    have "is_runtime_type ?env' (CoreTy_Record parentFields)"
      using core_term_type_notghost_runtime[OF _ wf'] ih_parent' ng by blast
    thus "\<forall>(n, t) \<in> set parentFields. is_runtime_type ?env' t"
      by (auto simp: list_all_iff)
  qed

  \<comment> \<open>Expected types are well-kinded and runtime\<close>
  have flds_found: "\<forall>(name, _) \<in> set flds. map_of parentFields name \<noteq> None"
    using check_update_fields_exist_sound[OF fields_exist] .

  have expectedTypes_wk: "list_all (is_well_kinded ?env') ?expectedTypes"
  proof (simp add: list_all_length, intro allI impI)
    fix i assume i_lt: "i < length flds"
    have "(flds ! i) \<in> set flds" using i_lt by simp
    with flds_found have "\<exists>ty. map_of parentFields (fst (flds ! i)) = Some ty"
      by (cases "flds ! i") auto
    then obtain ty where lk: "map_of parentFields (fst (flds ! i)) = Some ty" by blast
    hence "the (map_of parentFields (fst (flds ! i))) = ty" by simp
    moreover from parentFields_wk lk have "is_well_kinded ?env' ty"
      by (auto dest: map_of_SomeD)
    ultimately show "is_well_kinded ?env' (case flds ! i of (name, _) \<Rightarrow> the (map_of parentFields name))"
      by (cases "flds ! i") simp
  qed

  have expectedTypes_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env') ?expectedTypes"
  proof (intro impI)
    assume ng: "ghost = NotGhost"
    show "list_all (is_runtime_type ?env') ?expectedTypes"
    proof (simp add: list_all_length, intro allI impI)
      fix i assume i_lt: "i < length flds"
      have "(flds ! i) \<in> set flds" using i_lt by simp
      with flds_found have "\<exists>ty. map_of parentFields (fst (flds ! i)) = Some ty"
        by (cases "flds ! i") auto
      then obtain ty where lk: "map_of parentFields (fst (flds ! i)) = Some ty" by blast
      hence "the (map_of parentFields (fst (flds ! i))) = ty" by simp
      moreover from parentFields_rt ng lk have "is_runtime_type ?env' ty"
        by (auto dest: map_of_SomeD)
      ultimately show "is_runtime_type ?env' (case flds ! i of (name, _) \<Rightarrow> the (map_of parentFields name))"
        by (cases "flds ! i") simp
    qed
  qed

  \<comment> \<open>Extract unify_type_lists result from unify_and_coerce\<close>
  obtain unifySubst where
    unify_types: "unify_type_lists ?is_flex ?locOf 0 actualTypes ?expectedTypes fmempty = Inr unifySubst" and
    coercedTms_eq: "coercedTms = apply_call_coercions unifySubst newUpdateTms actualTypes ?expectedTypes" and
    finalSubst_eq: "finalSubst = unifySubst"
  proof -
    from unify_result show ?thesis
      by (auto simp: unify_and_coerce_def split: sum.splits intro: that)
  qed

  \<comment> \<open>Apply unify_type_lists_correct\<close>
  have empty_wk: "\<forall>ty \<in> fmran' (fmempty :: TypeSubst). is_well_kinded ?env' ty"
    by (simp add: fmran'_def)
  have empty_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' (fmempty :: TypeSubst). is_runtime_type ?env' ty)"
    by (simp add: fmran'_def)
  have empty_dom: "\<forall>n. n |\<in>| fmdom (fmempty :: TypeSubst) \<longrightarrow> ?is_flex n" by simp
  have empty_cp: "\<forall>ty \<in> fmran' (fmempty :: TypeSubst). is_complete_type ty"
    by (simp add: fmran'_def)

  have unify_correct: "(\<forall>ty \<in> fmran' unifySubst. is_well_kinded ?env' ty)
       \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' unifySubst. is_runtime_type ?env' ty))
       \<and> list_all2 (\<lambda>actualTy expectedTy.
           apply_subst unifySubst actualTy = apply_subst unifySubst expectedTy
           \<or> coercible (apply_subst unifySubst actualTy) (apply_subst unifySubst expectedTy))
         actualTypes ?expectedTypes
       \<and> (\<forall>n. n |\<in>| fmdom unifySubst \<longrightarrow> ?is_flex n)
       \<and> (\<forall>ty \<in> fmran' unifySubst. is_complete_type ty)"
    using unify_type_lists_correct[OF unify_types
            wf' len_expected actualTypes_wk expectedTypes_wk empty_wk
            actualTypes_rt expectedTypes_rt empty_rt empty_dom] empty_cp by blast

  have finalSubst_wk: "\<forall>ty \<in> fmran' finalSubst. is_well_kinded ?env' ty"
    using unify_correct finalSubst_eq by simp
  have finalSubst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type ?env' ty)"
    using unify_correct finalSubst_eq by simp
  have finalSubst_dom_flex: "\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> ?is_flex n"
    using unify_correct finalSubst_eq by simp
  have finalSubst_cp: "\<forall>ty \<in> fmran' finalSubst. is_complete_type ty"
    using unify_correct finalSubst_eq by simp
  have types_unified: "list_all2 (\<lambda>actualTy expectedTy.
           apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
           \<or> coercible (apply_subst finalSubst actualTy) (apply_subst finalSubst expectedTy))
         actualTypes ?expectedTypes"
    using unify_correct finalSubst_eq by simp

  \<comment> \<open>Subst doesn't affect locals or return type\<close>
  have env'_locals: "TE_LocalVars ?env' = TE_LocalVars env"
    unfolding extend_env_with_tyvars_def by simp
  have env'_ret: "TE_ReturnType ?env' = TE_ReturnType env"
    unfolding extend_env_with_tyvars_def by simp
  from flex_subst_identity_on_env[OF finalSubst_dom_flex wf env'_locals env'_ret]
  have locals_unaffected: "\<And>vname vty. fmlookup (TE_LocalVars ?env') vname = Some vty
                                       \<Longrightarrow> apply_subst finalSubst vty = vty"
    and ret_unaffected: "apply_subst finalSubst (TE_ReturnType ?env') = TE_ReturnType ?env'"
    by blast+
  have env'_abs: "TE_AbstractTypes ?env' = TE_AbstractTypes env"
    unfolding extend_env_with_tyvars_def by simp
  have abs_no_subst: "\<And>n. n |\<in>| TE_AbstractTypes ?env' \<Longrightarrow> fmlookup finalSubst n = None"
    using flex_subst_abs_no_subst[OF finalSubst_dom_flex[rule_format] wf env'_abs] .

  \<comment> \<open>Apply apply_call_coercions_correct\<close>
  have coerced_typed: "list_all2 (\<lambda>tm expectedTy.
           core_term_type ?env' ghost tm = Some (apply_subst finalSubst expectedTy))
         coercedTms ?expectedTypes"
    using apply_call_coercions_correct[OF ih_updates types_unified wf'
            finalSubst_wk finalSubst_rt len_updates len_expected
            locals_unaffected ret_unaffected abs_no_subst expectedTypes_wk expectedTypes_rt
            finalSubst_cp]
          coercedTms_eq finalSubst_eq by simp

  \<comment> \<open>Parent term after substitution\<close>
  let ?finalParentTm = "apply_subst_to_term finalSubst parentTm"
  let ?finalParentFields = "map (\<lambda>(n, ty). (n, apply_subst finalSubst ty)) parentFields"

  have finalParent_typed: "core_term_type ?env' ghost ?finalParentTm
                           = Some (CoreTy_Record ?finalParentFields)"
  proof -
    have "core_term_type ?env' ghost ?finalParentTm
          = Some (apply_subst finalSubst (CoreTy_Record parentFields))"
      using apply_subst_to_term_preserves_typing
              [OF ih_parent' wf' finalSubst_wk finalSubst_rt locals_unaffected ret_unaffected
                  abs_no_subst finalSubst_cp] .
    also have "apply_subst finalSubst (CoreTy_Record parentFields)
              = CoreTy_Record ?finalParentFields" by simp
    finally show ?thesis .
  qed

  \<comment> \<open>Distinctness\<close>
  have distinct_parent: "distinct (map fst parentFields)"
    using parent_ty_wk by simp
  have fst_final_eq: "map fst ?finalParentFields = map fst parentFields"
    by (induction parentFields) auto
  have distinct_final: "distinct (map fst ?finalParentFields)"
    using distinct_parent fst_final_eq by metis

  \<comment> \<open>map_of on finalParentFields gives apply_subst finalSubst of the original\<close>
  have map_of_final: "\<And>n ty. map_of parentFields n = Some ty \<Longrightarrow>
                              map_of ?finalParentFields n = Some (apply_subst finalSubst ty)"
    using distinct_parent by (induction parentFields) (auto split: if_splits)

  \<comment> \<open>Each coerced update term has the right type for build_record_update_correct\<close>
  have coerced_updates_for_build: "\<forall>(name, tm) \<in> set ?coercedUpdates.
         \<exists>ty. map_of ?finalParentFields name = Some ty
            \<and> core_term_type ?env' ghost tm = Some ty"
  proof (clarsimp)
    fix name tm assume in_set: "(name, tm) \<in> set ?coercedUpdates"
    from coerced_typed have len_coerced: "length coercedTms = length ?expectedTypes"
      by (simp add: list_all2_lengthD)
    from in_set obtain j where j_lt: "j < length coercedTms"
      and j_name: "name = map fst flds ! j"
      and j_tm: "tm = coercedTms ! j"
      using len_coerced len_flds_actual by (auto simp: set_zip in_set_conv_nth)
    from coerced_typed j_lt have
      "core_term_type ?env' ghost (coercedTms ! j)
         = Some (apply_subst finalSubst (?expectedTypes ! j))"
      by (simp add: list_all2_conv_all_nth)
    moreover have "?expectedTypes ! j = (case flds ! j of (name, _) \<Rightarrow> the (map_of parentFields name))"
      using j_lt len_coerced len_flds_actual by simp
    moreover have "(flds ! j) \<in> set flds"
      using j_lt len_coerced len_flds_actual by simp
    with flds_found have "\<exists>ety. map_of parentFields (fst (flds ! j)) = Some ety"
      by (cases "flds ! j") auto
    then obtain ety where ety: "map_of parentFields (fst (flds ! j)) = Some ety" by blast
    ultimately have tm_typed: "core_term_type ?env' ghost tm = Some (apply_subst finalSubst ety)"
      using j_tm by (cases "flds ! j") simp
    have fst_nth: "fst (flds ! j) = map fst flds ! j"
      using j_lt len_coerced len_flds_actual by simp
    have "map_of ?finalParentFields name = Some (apply_subst finalSubst ety)"
      using map_of_final ety j_name fst_nth by simp
    with tm_typed show "\<exists>ty. map_of ?finalParentFields name = Some ty
                           \<and> core_term_type ?env' ghost tm = Some ty"
      by blast
  qed

  \<comment> \<open>Apply build_record_update_correct\<close>
  let ?resultFlds = "build_record_update ?finalParentTm ?finalParentFields ?coercedUpdates"

  have result_typed: "list_all2 (\<lambda>(name, tm) (_, ty). core_term_type ?env' ghost tm = Some ty)
           ?resultFlds ?finalParentFields"
    using build_record_update_correct[OF finalParent_typed coerced_updates_for_build distinct_final] .

  have fst_result: "map fst ?resultFlds = map fst ?finalParentFields"
    using build_record_update_map_fst fst_final_eq by simp
  have distinct_result: "distinct (map fst ?resultFlds)"
    using distinct_final fst_result by simp
  have len_result: "length ?resultFlds = length ?finalParentFields"
    using build_record_update_length by simp

  have those_ok: "those (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) ?resultFlds)
                  = Some (map snd ?finalParentFields)"
  proof -
    have "list_all2 (\<lambda>x y. x = Some y)
            (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) ?resultFlds)
            (map snd ?finalParentFields)"
      unfolding list_all2_conv_all_nth
    proof (intro conjI allI impI)
      show "length (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) ?resultFlds)
            = length (map snd ?finalParentFields)"
        using len_result by simp
    next
      fix i assume i_lt: "i < length (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) ?resultFlds)"
      hence i_flds: "i < length ?finalParentFields" using len_result by simp
      from result_typed have "(case ?resultFlds ! i of (name, tm) \<Rightarrow> \<lambda>(_, ty).
              core_term_type ?env' ghost tm = Some ty) (?finalParentFields ! i)"
        using i_flds by (meson list_all2_nthD2)
      thus "map (\<lambda>(name, tm). core_term_type ?env' ghost tm) ?resultFlds ! i
            = Some (map snd ?finalParentFields ! i)"
        using i_flds len_result by (auto split: prod.splits)
    qed
    thus ?thesis by (simp add: those_eq_Some)
  qed

  have zip_reconstruct: "zip (map fst ?resultFlds) (map snd ?finalParentFields) = ?finalParentFields"
    using fst_result by (metis zip_map_fst_snd)

  have "core_term_type ?env' ghost (CoreTm_Record ?resultFlds) = Some (CoreTy_Record ?finalParentFields)"
    using distinct_result those_ok zip_reconstruct by simp

  thus ?thesis using result_eq
    by (simp add: build_updated_record_def Let_def)
qed


(* ========================================================================== *)
(* Correctness for the match helpers *)
(* ========================================================================== *)

(* Converting the arm bodies of a match to the first arm's body type.

   Arm body i is typed at bodyTys ! i, under envAmbient extended with the pattern
   variables of arm i. After a successful unify_and_coerce against the first
   arm's body type, every converted body has the (substituted) first arm's body
   type, under the same per-arm env.

   envOuter governs the unification flex predicate; envAmbient (in practice,
   envOuter extended with the fresh metavariables in scope) is where the typing
   lives. The pattern variables have types without metavariables
   (dps_meta_safe), so the unifier leaves the per-arm envs alone. *)
lemma coerce_match_arm_bodies_correct:
  assumes uc:
    "unify_and_coerce (\<lambda>n. n |\<notin>| TE_TypeVars envOuter) locOf
       bodyTms bodyTys (replicate (length bodyTms) (hd bodyTys)) fmempty
     = Inr (coercedBodies, finalSubst)"
      and outer_wf: "tyenv_well_formed envOuter"
      and ambient_wf: "tyenv_well_formed envAmbient"
      \<comment> \<open>envAmbient's locals/return type/abstract types come from envOuter unchanged. \<close>
      and ambient_locals_eq: "TE_LocalVars envAmbient = TE_LocalVars envOuter"
      and ambient_ret_eq: "TE_ReturnType envAmbient = TE_ReturnType envOuter"
      and ambient_abs_eq: "TE_AbstractTypes envAmbient = TE_AbstractTypes envOuter"
      and lengths: "length dps = length bodyTms" "length dps = length bodyTys"
      and dps_ne: "dps \<noteq> []"
      and dps_bind_wk:
        "\<And>dp. dp \<in> set dps \<Longrightarrow>
           list_all (\<lambda>(_, _, vTy). is_well_kinded envAmbient vTy)
                    (dec_pattern_var_bindings dp)"
      and dps_bind_rt:
        "\<And>dp. dp \<in> set dps \<Longrightarrow> ghost = NotGhost \<Longrightarrow>
           list_all (\<lambda>(_, _, vTy). is_runtime_type envAmbient vTy)
                    (dec_pattern_var_bindings dp)"
      and dps_meta_safe:
        "\<And>dp. dp \<in> set dps \<Longrightarrow>
           list_all (\<lambda>(_, _, vTy).
                       list_all (\<lambda>n. n |\<in>| TE_TypeVars envOuter) (type_tyvars_list vTy))
                    (dec_pattern_var_bindings dp)"
      and bodies_typed:
        "\<And>i. i < length dps \<Longrightarrow>
           core_term_type (extend_env_with_pattern_vars envAmbient (\<lambda>_. True) ghost [dps ! i])
                          ghost (bodyTms ! i)
           = Some (bodyTys ! i)"
  shows "length coercedBodies = length dps"
    and "\<And>i. i < length dps \<Longrightarrow>
           core_term_type (extend_env_with_pattern_vars envAmbient (\<lambda>_. True) ghost [dps ! i])
                          ghost (coercedBodies ! i)
           = Some (apply_subst finalSubst (hd bodyTys))"
proof -
  let ?is_flex = "\<lambda>n. n |\<notin>| TE_TypeVars envOuter"
  let ?expTy = "hd bodyTys"
  let ?expTys = "replicate (length bodyTms) ?expTy"

  \<comment> \<open>Unpack unify_and_coerce. \<close>
  have unify_types:
    "unify_type_lists ?is_flex locOf 0 bodyTys ?expTys fmempty = Inr finalSubst"
   and coerced_eq:
    "coercedBodies = apply_call_coercions finalSubst bodyTms bodyTys ?expTys"
    using uc by (auto simp: unify_and_coerce_def split: sum.splits)

  have len_tms_tys: "length bodyTms = length bodyTys" using lengths by simp
  have len_exp: "length bodyTys = length ?expTys" using len_tms_tys by simp

  \<comment> \<open>Each per-arm env is well-formed. \<close>
  have env_pat_wf:
    "\<And>dp. dp \<in> set dps \<Longrightarrow>
       tyenv_well_formed (extend_env_with_pattern_vars envAmbient (\<lambda>_. True) ghost [dp])"
  proof -
    fix dp assume dp_in: "dp \<in> set dps"
    have wk_list: "list_all (\<lambda>(_, _, ty). is_well_kinded envAmbient ty)
                            (dec_pattern_var_bindings_list [dp])"
      using dps_bind_wk[OF dp_in] by simp
    have rt_list: "ghost = NotGhost \<Longrightarrow>
                     list_all (\<lambda>(_, _, ty). is_runtime_type envAmbient ty)
                              (dec_pattern_var_bindings_list [dp])"
      using dps_bind_rt[OF dp_in] by simp
    show "tyenv_well_formed (extend_env_with_pattern_vars envAmbient (\<lambda>_. True) ghost [dp])"
      using tyenv_well_formed_extend_env_with_pattern_vars[OF ambient_wf wk_list rt_list] .
  qed

  \<comment> \<open>Each body type is well-kinded, and runtime in NotGhost mode, in envAmbient
      (the pattern-variable extension does not affect either). \<close>
  have bodyTy_wk_rt:
    "\<And>i. i < length dps \<Longrightarrow>
       is_well_kinded envAmbient (bodyTys ! i)
       \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type envAmbient (bodyTys ! i))"
  proof -
    fix i assume i_lt: "i < length dps"
    have dp_in: "dps ! i \<in> set dps" using i_lt by simp
    from core_term_type_well_kinded_and_runtime[OF bodies_typed[OF i_lt] env_pat_wf[OF dp_in]]
    show "is_well_kinded envAmbient (bodyTys ! i)
          \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type envAmbient (bodyTys ! i))"
      by simp
  qed
  have actualTys_wk: "list_all (is_well_kinded envAmbient) bodyTys"
  proof (simp add: list_all_length, intro allI impI)
    fix i assume "i < length bodyTys"
    hence "i < length dps" using lengths by simp
    thus "is_well_kinded envAmbient (bodyTys ! i)" using bodyTy_wk_rt by blast
  qed
  have actualTys_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type envAmbient) bodyTys"
  proof
    assume ng: "ghost = NotGhost"
    show "list_all (is_runtime_type envAmbient) bodyTys"
    proof (simp add: list_all_length, intro allI impI)
      fix i assume "i < length bodyTys"
      hence "i < length dps" using lengths by simp
      thus "is_runtime_type envAmbient (bodyTys ! i)" using bodyTy_wk_rt ng by blast
    qed
  qed

  \<comment> \<open>The expected type is the first arm's body type. \<close>
  have zero_lt: "0 < length dps" using dps_ne by simp
  have bodyTys_ne: "bodyTys \<noteq> []" using zero_lt lengths by auto
  have expTy_eq: "?expTy = bodyTys ! 0" using bodyTys_ne by (simp add: hd_conv_nth)
  have expTy_wk: "is_well_kinded envAmbient ?expTy"
    unfolding expTy_eq using bodyTy_wk_rt[OF zero_lt] by simp
  have expTy_rt: "ghost = NotGhost \<Longrightarrow> is_runtime_type envAmbient ?expTy"
    unfolding expTy_eq using bodyTy_wk_rt[OF zero_lt] by simp
  have expectedTys_wk: "list_all (is_well_kinded envAmbient) ?expTys"
    using expTy_wk by (simp add: list_all_length)
  have expectedTys_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type envAmbient) ?expTys"
    using expTy_rt by (simp add: list_all_length)

  \<comment> \<open>Apply unify_type_lists_correct. \<close>
  have empty_wk: "\<forall>ty \<in> fmran' (fmempty :: TypeSubst). is_well_kinded envAmbient ty"
    by (simp add: fmran'_def)
  have empty_rt: "ghost = NotGhost \<longrightarrow>
                    (\<forall>ty \<in> fmran' (fmempty :: TypeSubst). is_runtime_type envAmbient ty)"
    by (simp add: fmran'_def)
  have empty_dom: "\<forall>n. n |\<in>| fmdom (fmempty :: TypeSubst) \<longrightarrow> ?is_flex n" by simp
  have empty_cp: "\<forall>ty \<in> fmran' (fmempty :: TypeSubst). is_complete_type ty"
    by (simp add: fmran'_def)

  have unify_correct:
    "(\<forall>ty \<in> fmran' finalSubst. is_well_kinded envAmbient ty)
     \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type envAmbient ty))
     \<and> list_all2 (\<lambda>actualTy expectedTy.
         apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
         \<or> coercible (apply_subst finalSubst actualTy) (apply_subst finalSubst expectedTy))
       bodyTys ?expTys
     \<and> (\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> ?is_flex n)
     \<and> (\<forall>ty \<in> fmran' finalSubst. is_complete_type ty)"
    using unify_type_lists_correct[OF unify_types
            ambient_wf len_exp actualTys_wk expectedTys_wk empty_wk
            actualTys_rt expectedTys_rt empty_rt empty_dom] empty_cp by blast

  have finalSubst_wk: "\<forall>ty \<in> fmran' finalSubst. is_well_kinded envAmbient ty"
    using unify_correct by simp
  have finalSubst_rt:
    "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type envAmbient ty)"
    using unify_correct by simp
  have finalSubst_dom_flex: "\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> ?is_flex n"
    using unify_correct by simp
  have finalSubst_cp: "\<forall>ty \<in> fmran' finalSubst. is_complete_type ty"
    using unify_correct by simp
  have types_unified:
    "list_all2 (\<lambda>actualTy expectedTy.
         apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
         \<or> coercible (apply_subst finalSubst actualTy) (apply_subst finalSubst expectedTy))
       bodyTys ?expTys"
    using unify_correct by simp
  have finalSubst_dom: "fmdom finalSubst |\<inter>| TE_TypeVars envOuter = {||}"
    using finalSubst_dom_flex by auto

  \<comment> \<open>envAmbient's locals / return type / abstract types are unaffected by finalSubst. \<close>
  have ambient_locals_unaffected:
    "\<And>name ty'. fmlookup (TE_LocalVars envAmbient) name = Some ty'
                  \<Longrightarrow> apply_subst finalSubst ty' = ty'"
       and ambient_ret_unaffected:
    "apply_subst finalSubst (TE_ReturnType envAmbient) = TE_ReturnType envAmbient"
    using flex_subst_identity_on_env[OF finalSubst_dom_flex outer_wf
                                        ambient_locals_eq ambient_ret_eq]
    by auto
  have ambient_abs_no_subst:
    "\<And>n. n |\<in>| TE_AbstractTypes envAmbient \<Longrightarrow> fmlookup finalSubst n = None"
    using flex_subst_abs_no_subst[OF finalSubst_dom_flex[rule_format] outer_wf ambient_abs_eq] .

  \<comment> \<open>The substituted expected type is well-kinded / runtime: it is the cast target. \<close>
  have final_wk: "is_well_kinded envAmbient (apply_subst finalSubst ?expTy)"
    using apply_subst_preserves_well_kinded_same_env[OF expTy_wk finalSubst_wk] .
  have final_rt: "ghost = NotGhost \<Longrightarrow> is_runtime_type envAmbient (apply_subst finalSubst ?expTy)"
  proof -
    assume ng: "ghost = NotGhost"
    have "\<forall>ty \<in> fmran' finalSubst. is_runtime_type envAmbient ty"
      using finalSubst_rt ng by simp
    thus "is_runtime_type envAmbient (apply_subst finalSubst ?expTy)"
      using apply_subst_preserves_runtime_same_env[OF expTy_rt[OF ng]] by blast
  qed

  show "length coercedBodies = length dps"
    unfolding coerced_eq
    using apply_call_coercions_length[OF len_tms_tys len_exp] lengths by simp

  show "\<And>i. i < length dps \<Longrightarrow>
          core_term_type (extend_env_with_pattern_vars envAmbient (\<lambda>_. True) ghost [dps ! i])
                         ghost (coercedBodies ! i)
          = Some (apply_subst finalSubst (hd bodyTys))"
  proof -
    fix i assume i_lt: "i < length dps"
    let ?dp = "dps ! i"
    let ?btm = "bodyTms ! i"
    let ?bty = "bodyTys ! i"
    let ?env_pat = "extend_env_with_pattern_vars envAmbient (\<lambda>_. True) ghost [?dp]"
    have dp_in: "?dp \<in> set dps" using i_lt by simp
    have i_tms: "i < length bodyTms" using i_lt lengths by simp
    have i_tys: "i < length bodyTys" using i_lt lengths by simp

    \<comment> \<open>finalSubst's range is well-kinded / runtime under ?env_pat. \<close>
    have finalSubst_wk_pat: "\<forall>ty' \<in> fmran' finalSubst. is_well_kinded ?env_pat ty'"
      using finalSubst_wk by simp
    have finalSubst_rt_pat:
      "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' finalSubst. is_runtime_type ?env_pat ty')"
      using finalSubst_rt by simp

    \<comment> \<open>?env_pat's locals are unaffected by finalSubst:
        - the original envAmbient locals are unaffected (ambient_locals_unaffected);
        - the dp's pattern vars added on top have no metavariables (dps_meta_safe). \<close>
    have dp_bindings_unaffected:
      "list_all (\<lambda>(_, _, vTy). apply_subst finalSubst vTy = vTy)
                (dec_pattern_var_bindings ?dp)"
      using dec_pattern_var_bindings_apply_subst_id_of_meta_safe
              [OF dps_meta_safe[OF dp_in] finalSubst_dom] .
    have env_pat_locals_unaffected:
      "\<And>name ty'. fmlookup (TE_LocalVars ?env_pat) name = Some ty'
                    \<Longrightarrow> apply_subst finalSubst ty' = ty'"
    proof -
      fix name ty'
      assume lookup_pat: "fmlookup (TE_LocalVars ?env_pat) name = Some ty'"
      show "apply_subst finalSubst ty' = ty'"
      proof (cases "map_of (map (\<lambda>(vr, n, ty). (n, ty)) (dec_pattern_var_bindings ?dp)) name")
        case None
        have "fmlookup (TE_LocalVars envAmbient) name = Some ty'"
          using lookup_pat None
          unfolding extend_env_with_pattern_vars_def
          by (simp add: fmlookup_TE_LocalVars_foldr_extend_env_one_var)
        thus ?thesis using ambient_locals_unaffected by simp
      next
        case (Some ty_pat)
        have ty_eq: "ty' = ty_pat"
          using lookup_pat Some
          unfolding extend_env_with_pattern_vars_def
          by (simp add: fmlookup_TE_LocalVars_foldr_extend_env_one_var)
        from Some have name_in_pairs:
          "(name, ty_pat) \<in> set (map (\<lambda>(vr, n, ty). (n, ty)) (dec_pattern_var_bindings ?dp))"
          by (rule map_of_SomeD)
        then obtain vr where triple_in:
          "(vr, name, ty_pat) \<in> set (dec_pattern_var_bindings ?dp)"
          by auto
        have "apply_subst finalSubst ty_pat = ty_pat"
          using dp_bindings_unaffected triple_in by (auto simp: list_all_iff)
        thus ?thesis using ty_eq by simp
      qed
    qed

    have env_pat_ret_unaffected:
      "apply_subst finalSubst (TE_ReturnType ?env_pat) = TE_ReturnType ?env_pat"
      using ambient_ret_unaffected by simp

    have foldr_abs_eq:
      "\<And>bs e. TE_AbstractTypes (foldr (extend_env_one_var (\<lambda>_. True) ghost) bs e)
                = TE_AbstractTypes e"
      subgoal for bs e
        by (induction bs arbitrary: e)
           (auto simp: extend_env_one_var_def split: prod.splits)
      done
    have env_pat_abs: "TE_AbstractTypes ?env_pat = TE_AbstractTypes envAmbient"
      unfolding extend_env_with_pattern_vars_def by (rule foldr_abs_eq)
    have env_pat_abs_no_subst:
      "\<And>n. n |\<in>| TE_AbstractTypes ?env_pat \<Longrightarrow> fmlookup finalSubst n = None"
      using ambient_abs_no_subst env_pat_abs by simp

    \<comment> \<open>The substituted body has the substituted body type. \<close>
    have body_substituted:
      "core_term_type ?env_pat ghost (apply_subst_to_term finalSubst ?btm)
         = Some (apply_subst finalSubst ?bty)"
      using apply_subst_to_term_preserves_typing[OF bodies_typed[OF i_lt] env_pat_wf[OF dp_in]
                                                    finalSubst_wk_pat finalSubst_rt_pat
                                                    env_pat_locals_unaffected
                                                    env_pat_ret_unaffected
                                                    env_pat_abs_no_subst finalSubst_cp] .

    \<comment> \<open>That type is equal to, or coercible to, the substituted expected type. \<close>
    have exp_at_i: "?expTys ! i = ?expTy" using i_tms by simp
    have unified_i:
      "apply_subst finalSubst ?bty = apply_subst finalSubst ?expTy
       \<or> coercible (apply_subst finalSubst ?bty) (apply_subst finalSubst ?expTy)"
      using list_all2_nthD[OF types_unified i_tys] exp_at_i by simp

    have final_wk_pat: "is_well_kinded ?env_pat (apply_subst finalSubst ?expTy)"
      using final_wk by simp
    have final_rt_pat:
      "ghost = NotGhost \<longrightarrow> is_runtime_type ?env_pat (apply_subst finalSubst ?expTy)"
      using final_rt by simp

    \<comment> \<open>So the converted body (the substituted body, cast if needed) has the
        substituted expected type. \<close>
    have coerced_i:
      "coercedBodies ! i
       = insert_cast (apply_subst finalSubst ?bty) (apply_subst finalSubst (?expTys ! i))
                     (apply_subst_to_term finalSubst ?btm)"
      unfolding coerced_eq
      by (rule apply_call_coercions_nth[OF len_tms_tys len_exp i_tms])
    have coerced_i':
      "coercedBodies ! i
       = insert_cast (apply_subst finalSubst ?bty) (apply_subst finalSubst ?expTy)
                     (apply_subst_to_term finalSubst ?btm)"
      using coerced_i exp_at_i by simp
    show "core_term_type ?env_pat ghost (coercedBodies ! i)
          = Some (apply_subst finalSubst (hd bodyTys))"
      unfolding coerced_i'
      using insert_cast_typed[OF body_substituted unified_i final_wk_pat final_rt_pat] .
  qed
qed

(* Correctness for finalize_match_term: freshness validation, and the typing
   rule for the resulting Let + Match + per-arm-wrap_lets shape.

   Every pattern is compatible with the scrutinee type, and arm body i (already
   converted to the common body type) is typed under envAmbient extended with the
   pattern variables of arm i. *)
lemma finalize_match_term_correct:
  assumes finalize_eq:
    "finalize_match_term loc scrutTm dps bodies bodyTy nextMv
     = Inr (resultTm, resultTy, nextMv')"
      and ambient_wf: "tyenv_well_formed envAmbient"
      and scrut_typed: "core_term_type envAmbient ghost scrutTm = Some scrutTy"
      and lengths: "length dps = length bodies"
      and dps_compat:
        "\<And>dp. dp \<in> set dps \<Longrightarrow> dec_pattern_compatible envAmbient dp scrutTy"
      and dps_distinct:
        "\<And>dp. dp \<in> set dps \<Longrightarrow> pattern_var_names_distinct [dp]"
      and bodies_typed:
        "\<And>i. i < length dps \<Longrightarrow>
           core_term_type (extend_env_with_pattern_vars envAmbient (\<lambda>_. True) ghost [dps ! i])
                          ghost (bodies ! i)
           = Some bodyTy"
      \<comment> \<open>dps is non-empty (mirrored from arms_ne in BabTm_Match). \<close>
      and dps_ne: "dps \<noteq> []"
  shows "core_term_type envAmbient ghost resultTm = Some bodyTy
       \<and> resultTy = bodyTy
       \<and> nextMv' = nextMv + 1"
proof -
  \<comment> \<open>Names from the body of finalize_match_term. \<close>
  define freshName where "freshName = ''match@@'' @ nat_to_string nextMv"
  define armPats where "armPats = map dec_to_core_pat dps"
  define armBodies where
    "armBodies = map (\<lambda>(dp, body). wrap_lets freshName dp body) (zip dps bodies)"

  have body_unfolded:
    "finalize_match_term loc scrutTm dps bodies bodyTy nextMv
     = (if freshName |\<in>| core_term_free_vars scrutTm
           \<or> list_ex (\<lambda>dp. freshName |\<in>| dec_pattern_var_names dp) dps
           \<or> list_ex (\<lambda>body. freshName |\<in>| core_term_free_vars body) bodies
        then Inl [TyErr_UnexpectedNameClash loc]
        else Inr (CoreTm_Let freshName scrutTm
                    (CoreTm_Match (CoreTm_Var freshName) (zip armPats armBodies)),
                  bodyTy, nextMv + 1))"
    unfolding finalize_match_term_def
    by (simp add: Let_def freshName_def armPats_def armBodies_def)

  have eq2:
    "(if freshName |\<in>| core_term_free_vars scrutTm
        \<or> list_ex (\<lambda>dp. freshName |\<in>| dec_pattern_var_names dp) dps
        \<or> list_ex (\<lambda>body. freshName |\<in>| core_term_free_vars body) bodies
      then Inl [TyErr_UnexpectedNameClash loc]
      else Inr (CoreTm_Let freshName scrutTm
                  (CoreTm_Match (CoreTm_Var freshName) (zip armPats armBodies)),
                bodyTy, nextMv + 1))
     = Inr (resultTm, resultTy, nextMv')"
    using finalize_eq body_unfolded by simp

  \<comment> \<open>The freshness check passed (else result would be Inl). \<close>
  have freshness_check:
    "\<not> (freshName |\<in>| core_term_free_vars scrutTm
        \<or> list_ex (\<lambda>dp. freshName |\<in>| dec_pattern_var_names dp) dps
        \<or> list_ex (\<lambda>body. freshName |\<in>| core_term_free_vars body) bodies)"
    using eq2 by (simp split: if_splits)
  have not_in_scrut: "freshName |\<notin>| core_term_free_vars scrutTm"
    using freshness_check by simp
  have not_in_dps:
    "list_all (\<lambda>dp. freshName |\<notin>| dec_pattern_var_names dp) dps"
    using freshness_check by (auto simp: list_ex_iff list_all_iff)
  have not_in_bodies:
    "list_all (\<lambda>body. freshName |\<notin>| core_term_free_vars body) bodies"
    using freshness_check by (auto simp: list_ex_iff list_all_iff)

  have resultTm_eq:
    "resultTm = CoreTm_Let freshName scrutTm
                  (CoreTm_Match (CoreTm_Var freshName) (zip armPats armBodies))"
   and resultTy_eq: "resultTy = bodyTy"
   and nextMv'_eq: "nextMv' = nextMv + 1"
    using eq2 freshness_check by simp_all

  \<comment> \<open>The env under which the Match is typed: envAmbient + freshName : scrutTy. \<close>
  let ?env' = "extend_env_one_var (\<lambda>_. True) ghost (Var, freshName, scrutTy) envAmbient"

  have scrutTy_wk: "is_well_kinded envAmbient scrutTy"
    using core_term_type_well_kinded[OF scrut_typed ambient_wf] .
  have scrutTy_rt: "ghost = NotGhost \<Longrightarrow> is_runtime_type envAmbient scrutTy"
    using core_term_type_well_kinded_and_runtime[OF scrut_typed ambient_wf] by blast

  have env'_wf: "tyenv_well_formed ?env'"
  proof (cases "ghost = Ghost")
    case True
    have ext_eq: "?env' = (envAmbient \<lparr> TE_LocalVars := fmupd freshName scrutTy (TE_LocalVars envAmbient),
                                         TE_GhostLocals := finsert freshName (TE_GhostLocals envAmbient) \<rparr>)
                              \<lparr> TE_ConstLocals := finsert freshName (TE_ConstLocals envAmbient) \<rparr>"
      using True by (simp add: extend_env_one_var_def)
    show ?thesis
      using True tyenv_well_formed_add_ghost_var[OF ambient_wf scrutTy_wk] ext_eq
            tyenv_well_formed_TE_ConstLocals_irrelevant
      by simp
  next
    case False
    hence ng: "ghost = NotGhost" by (cases ghost) auto
    have ext_eq: "?env' = (envAmbient \<lparr> TE_LocalVars := fmupd freshName scrutTy (TE_LocalVars envAmbient),
                                         TE_GhostLocals := fminus (TE_GhostLocals envAmbient) {|freshName|} \<rparr>)
                              \<lparr> TE_ConstLocals := finsert freshName (TE_ConstLocals envAmbient) \<rparr>"
      using ng by (simp add: extend_env_one_var_def)
    show ?thesis
      using tyenv_well_formed_add_var[OF ambient_wf scrutTy_wk scrutTy_rt[OF ng]]
            ext_eq tyenv_well_formed_TE_ConstLocals_irrelevant
      by simp
  qed

  have env'_tv: "TE_TypeVars ?env' = TE_TypeVars envAmbient"
    by (simp add: extend_env_one_var_def)
  have env'_dt: "TE_Datatypes ?env' = TE_Datatypes envAmbient"
    by (simp add: extend_env_one_var_def)
  have scrutTy_wk_env': "is_well_kinded ?env' scrutTy"
    using scrutTy_wk is_well_kinded_cong_env[OF env'_tv env'_dt] by simp

  have base_var_typed:
    "core_term_type ?env' ghost (CoreTm_Var freshName) = Some scrutTy"
    by (simp add: extend_env_one_var_def tyenv_lookup_var_def
                   tyenv_var_ghost_def split: option.splits)

  \<comment> \<open>Lengths. \<close>
  have len_armPats: "length armPats = length dps"
    by (simp add: armPats_def)
  have len_armBodies: "length armBodies = length dps"
    by (simp add: armBodies_def lengths)
  have len_zip_arms: "length (zip armPats armBodies) = length dps"
    using len_armPats len_armBodies by simp

  \<comment> \<open>Each match arm (armPat, armBody) is pattern-compatible / body-well-typed under ?env'. \<close>
  have arms_well_typed:
    "list_all (\<lambda>(p, body). pattern_compatible ?env' p scrutTy
                          \<and> core_term_type ?env' ghost body = Some bodyTy)
              (zip armPats armBodies)"
  proof -
    have "\<forall>i < length (zip armPats armBodies).
            case (zip armPats armBodies) ! i of (p, body) \<Rightarrow>
              pattern_compatible ?env' p scrutTy
              \<and> core_term_type ?env' ghost body = Some bodyTy"
    proof (intro allI impI)
      fix i assume i_lt: "i < length (zip armPats armBodies)"
      have i_lt': "i < length dps" using i_lt len_zip_arms by auto
      have i_lt_pats: "i < length armPats" using i_lt by simp
      have i_lt_bodies: "i < length armBodies" using i_lt by simp
      let ?dp = "dps ! i"
      let ?body = "bodies ! i"
      have armPat_eq: "armPats ! i = dec_to_core_pat ?dp"
        unfolding armPats_def using i_lt' by simp
      have armBody_eq: "armBodies ! i = wrap_lets freshName ?dp ?body"
        unfolding armBodies_def
        using i_lt' lengths by simp
      have arm_at_i: "(zip armPats armBodies) ! i = (dec_to_core_pat ?dp, wrap_lets freshName ?dp ?body)"
        using i_lt_pats i_lt_bodies armPat_eq armBody_eq by simp

      have dp_in: "?dp \<in> set dps" using i_lt' nth_mem by simp
      have dp_compat: "dec_pattern_compatible envAmbient ?dp scrutTy"
        using dps_compat[OF dp_in] .
      have dp_compat_env': "dec_pattern_compatible ?env' ?dp scrutTy"
        using dp_compat by (simp add: dec_pattern_compatible_extend_env_one_var)

      have pat_compat: "pattern_compatible ?env' (dec_to_core_pat ?dp) scrutTy"
        using dec_to_core_pat_pattern_compatible[OF dp_compat_env' scrutTy_wk_env' env'_wf] .

      \<comment> \<open>Body well-typed under ?env'. Apply wrap_lets_preserves_typing. \<close>
      have fresh_not_in_dp: "freshName |\<notin>| dec_pattern_var_names ?dp"
        using not_in_dps i_lt'
        by (auto simp: list_all_length)

      have base_fresh_disjoint:
        "core_term_free_vars (CoreTm_Var freshName) |\<inter>| dec_pattern_var_names ?dp = {||}"
        using fresh_not_in_dp by auto

      \<comment> \<open>?body is well-typed at bodyTy in env_pat(?env',?dp). \<close>
      have body_at_pat_env':
        "core_term_type (extend_env_with_pattern_vars ?env' (\<lambda>_. True) ghost [?dp]) ghost ?body = Some bodyTy"
      proof -
        \<comment> \<open>From bodies_typed: typed in extend_env_with_pattern_vars envAmbient (\<lambda>_. True) ghost [?dp]. \<close>
        have base_typed: "core_term_type (extend_env_with_pattern_vars envAmbient (\<lambda>_. True) ghost [?dp]) ghost ?body = Some bodyTy"
          using bodies_typed[OF i_lt'] .
        \<comment> \<open>Lift to env' by freshness: freshName isn't a free var of ?body. \<close>
        have body_not_in: "freshName |\<notin>| core_term_free_vars ?body"
          using not_in_bodies i_lt' lengths
          by (auto simp: list_all_length)
        \<comment> \<open>Use extend_env_with_pattern_vars_extend_env_one_var_swap to swap the order. \<close>
        have env_swap:
          "extend_env_with_pattern_vars ?env' (\<lambda>_. True) ghost [?dp]
           = extend_env_one_var (\<lambda>_. True) ghost (Var, freshName, scrutTy)
                                (extend_env_with_pattern_vars envAmbient (\<lambda>_. True) ghost [?dp])"
        proof -
          have dp_names_no_fresh: "freshName |\<notin>| dec_pattern_var_names_list [?dp]"
            using fresh_not_in_dp by simp
          show ?thesis
            using extend_env_with_pattern_vars_extend_env_one_var_swap[OF dp_names_no_fresh] .
        qed
        show ?thesis
          unfolding env_swap
          using core_term_type_extend_env_one_var_irrelevant[OF body_not_in base_typed] .
      qed

      \<comment> \<open>Now apply wrap_lets_preserves_typing. \<close>
      have dp_distinct: "distinct (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings ?dp))"
        using dps_distinct[OF dp_in]
        by (simp add: pattern_var_names_distinct_def)
      have body_at_pat_env'_foldr:
        "core_term_type
           (foldr (extend_env_one_var (\<lambda>_. True) ghost) (dec_pattern_var_bindings ?dp) ?env')
           ghost ?body = Some bodyTy"
        using body_at_pat_env' by (simp add: extend_env_with_pattern_vars_def)
      have body_wrapped:
        "core_term_type ?env' ghost (wrap_lets freshName ?dp ?body) = Some bodyTy"
        using wrap_lets_preserves_typing[OF dp_compat_env' base_var_typed env'_wf
                                            scrutTy_wk_env' base_fresh_disjoint
                                            body_at_pat_env'_foldr dp_distinct] .

      show "case (zip armPats armBodies) ! i of (p, body) \<Rightarrow>
              pattern_compatible ?env' p scrutTy
              \<and> core_term_type ?env' ghost body = Some bodyTy"
        using arm_at_i pat_compat body_wrapped by simp
    qed
    thus ?thesis unfolding list_all_length .
  qed

  \<comment> \<open>arms non-empty. \<close>
  have arms_ne: "zip armPats armBodies \<noteq> []"
    using dps_ne len_zip_arms by (cases dps) auto

  \<comment> \<open>Result type is the Match's. \<close>
  let ?match = "CoreTm_Match (CoreTm_Var freshName) (zip armPats armBodies)"
  have match_typed: "core_term_type ?env' ghost ?match = Some bodyTy"
  proof -
    have all_compat:
      "list_all (\<lambda>p. pattern_compatible ?env' p scrutTy)
                (map fst (zip armPats armBodies))"
      using arms_well_typed
      by (auto simp: list_all_iff in_set_conv_nth split: prod.splits)
    have all_body_ty:
      "list_all (\<lambda>body. core_term_type ?env' ghost body = Some bodyTy)
                (map snd (zip armPats armBodies))"
      using arms_well_typed
      by (auto simp: list_all_iff in_set_conv_nth split: prod.splits)
    \<comment> \<open>The Match typing rule asks for: (a) all pats compatible (got it),
        (b) hd's body has some type resultTy, (c) all other bodies have that
        type. From all_body_ty plus arms non-empty, hd's body has bodyTy
        and (after a tl) the rest also have bodyTy. \<close>
    have arms_split: "armBodies = hd armBodies # tl armBodies"
      using arms_ne by (cases armBodies; cases armPats) simp_all
    have hd_in: "hd armBodies \<in> set armBodies"
      using arms_ne by (cases armBodies) auto
    have hd_arm_eq: "snd (hd (zip armPats armBodies)) = hd armBodies"
      using arms_ne by (cases armPats; cases armBodies) auto
    have hd_typed: "core_term_type ?env' ghost (hd armBodies) = Some bodyTy"
      using all_body_ty hd_in
      by (metis (full_types, lifting) arms_split len_armBodies len_armPats list_all_simps(1) map_snd_zip)
    have tl_typed:
      "list_all (\<lambda>body. core_term_type ?env' ghost body = Some bodyTy)
                (tl (map snd (zip armPats armBodies)))"
      using all_body_ty
      by (cases "map snd (zip armPats armBodies)") (auto simp: list_all_iff)
    show ?thesis
      using arms_ne base_var_typed all_compat hd_arm_eq hd_typed tl_typed
      by (simp add: Let_def)
  qed

  \<comment> \<open>Result is the outer Let wrapping ?match. \<close>
  have result_typed: "core_term_type envAmbient ghost resultTm = Some bodyTy"
    unfolding resultTm_eq
    using scrut_typed match_typed
    by (simp add: Let_def extend_env_one_var_def)

  show ?thesis using result_typed resultTy_eq nextMv'_eq by simp
qed


(* ========================================================================== *)
(* Main correctness theorem *)
(* ========================================================================== *)

(* Correctness theorem for elab_term and elab_term_list.
   If elaboration succeeds, the resulting term(s) are well-typed in env extended
   with the fresh metavariables introduced during elaboration (the interval
   [next_mv ..< next_mv']).

   The freshness precondition (fourth assumption) says that next_mv is strictly
   greater than every type variable already in env. This ensures that the fresh
   metas the elaborator generates don't collide with existing ones. *)
theorem elab_term_correct:
  "elab_term env elabEnv ghost tm next_mv = Inr (newTm, ty, next_mv') \<Longrightarrow>
   tyenv_well_formed env \<Longrightarrow>
   elabenv_well_formed env elabEnv \<Longrightarrow>
   (\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n next_mv) \<Longrightarrow>
   core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost newTm = Some ty"
and elab_term_list_correct:
  "elab_term_list env elabEnv ghost tms next_mv = Inr (newTms, tys, next_mv') \<Longrightarrow>
   tyenv_well_formed env \<Longrightarrow>
   elabenv_well_formed env elabEnv \<Longrightarrow>
   (\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n next_mv) \<Longrightarrow>
   list_all2 (\<lambda>tm ty. core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost tm = Some ty) newTms tys"
and elab_term_list_with_envs_correct:
  \<comment> \<open>For each (env_i, term_i) in the input job list, the corresponding
      output term has the corresponding output type under env_i extended with
      the fresh tyvar interval [next_mv, next_mv'). Each env_i is required
      to be well-formed and tyvar-bounded. \<close>
  "elab_term_list_with_envs jobs elabEnv ghost next_mv = Inr (newTms, tys, next_mv') \<Longrightarrow>
   list_all (\<lambda>(env_i, _). tyenv_well_formed env_i) jobs \<Longrightarrow>
   list_all (\<lambda>(env_i, _). elabenv_well_formed env_i elabEnv) jobs \<Longrightarrow>
   list_all (\<lambda>(env_i, _). \<forall>n. n |\<in>| TE_TypeVars env_i \<longrightarrow> tyvar_fresh_ok n next_mv) jobs \<Longrightarrow>
   list_all2
     (\<lambda>(env_i, _) (tm', ty').
        core_term_type (extend_env_with_tyvars env_i ghost next_mv next_mv') ghost tm'
        = Some ty')
     jobs (zip newTms tys)"
proof (induction env elabEnv ghost tm next_mv
       and env elabEnv ghost tms next_mv
       and jobs elabEnv ghost next_mv
       arbitrary: newTm ty next_mv'
       and newTms tys next_mv'
       and newTms tys next_mv'
       rule: elab_term_elab_term_list_elab_term_list_with_envs.induct)
  \<comment> \<open>Case: BabTm_Literal\<close>
  case (1 env elabEnv ghost loc lit next_mv)
  show ?case
  proof (cases lit)
    case (BabLit_Bool b)
    with "1.prems"(1) have "newTm = CoreTm_LitBool b" and "ty = CoreTy_Bool"
      by auto
    thus ?thesis by simp
  next
    case (BabLit_Int i)
    with "1.prems"(1) obtain sign bits where
      get_type: "get_type_for_int i = Some (sign, bits)" and
      newTm_eq: "newTm = CoreTm_LitInt i" and
      ty_eq: "ty = CoreTy_FiniteInt sign bits"
      by (auto split: option.splits)
    thus ?thesis using get_type by simp
  next
    case (BabLit_String chars)
    let ?u8_ty = "CoreTy_FiniteInt Unsigned IntBits_8"
    let ?bytes = "chars @ [CHR 0x00]"
    let ?elemTms = "map (\<lambda>c. CoreTm_Cast ?u8_ty (CoreTm_LitInt (int (of_char c)))) ?bytes"
    from "1.prems"(1) BabLit_String have
      len_ok: "int_in_range (int_range Unsigned IntBits_64) (int (length chars + 1))"
      by (auto split: if_splits)
    from "1.prems"(1) BabLit_String len_ok have
      newTm_eq: "newTm = CoreTm_LitArray ?u8_ty ?elemTms" and
      ty_eq: "ty = CoreTy_Array ?u8_ty [CoreDim_Fixed (int (length ?bytes))]"
      by (auto simp: Let_def)
    let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
    \<comment> \<open>Each char's int literal is in i32 range (since of_char c < 256)\<close>
    have each_char: "\<And>c. core_term_type ?env' ghost
                           (CoreTm_Cast ?u8_ty (CoreTm_LitInt (int (of_char c))))
                         = Some ?u8_ty"
    proof -
      fix c :: char
      have c_bound: "int (of_char c) \<le> 255"
        using nat_of_char_less_256[of c] by linarith
      have c_nn: "0 \<le> int (of_char c)" by simp
      have fits_i32: "get_type_for_int (int (of_char c)) = Some (Signed, IntBits_32)"
        using c_bound c_nn by simp
      show "core_term_type ?env' ghost
              (CoreTm_Cast ?u8_ty (CoreTm_LitInt (int (of_char c))))
            = Some ?u8_ty"
        using fits_i32 by simp
    qed
    have elem_typed: "list_all (\<lambda>tm. core_term_type ?env' ghost tm = Some ?u8_ty) ?elemTms"
      using each_char by (auto simp: list_all_iff)
    show ?thesis
      using newTm_eq ty_eq elem_typed len_ok by simp
  next
    case (BabLit_Array tms)
    \<comment> \<open>Extract the element-list elaboration result\<close>
    from "1.prems"(1) BabLit_Array have
      len_ok: "int_in_range (int_range Unsigned IntBits_64) (int (length tms))"
      by (auto split: if_splits)
    from "1.prems"(1) BabLit_Array len_ok obtain elabTms actualTypes next_mv1 where
      elab_elems: "elab_term_list env elabEnv ghost tms (next_mv + 1)
                   = Inr (elabTms, actualTypes, next_mv1)"
      by (auto simp: Let_def split: sum.splits)
    \<comment> \<open>Freshness carries over (next_mv + 1 is still above every existing tyvar)\<close>
    have fresh': "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n (next_mv + 1)"
      using "1.prems"(4) tyvar_fresh_ok_mono by fastforce
    \<comment> \<open>Apply IH to obtain typing of elabTms in the (next_mv + 1, next_mv1) env\<close>
    have ih_narrow: "list_all2 (\<lambda>tm ty. core_term_type
                      (extend_env_with_tyvars env ghost (next_mv + 1) next_mv1) ghost tm = Some ty)
                     elabTms actualTypes"
      using "1.IH"[OF BabLit_Array _ refl elab_elems "1.prems"(2,3) fresh'] len_ok by simp
    \<comment> \<open>Widen to the full (next_mv, next_mv') env\<close>
    have ih_elems: "list_all2 (\<lambda>tm ty. core_term_type
                      (extend_env_with_tyvars env ghost next_mv next_mv') ghost tm = Some ty)
                    elabTms actualTypes"
    proof -
      \<comment> \<open>next_mv' = next_mv1 from the definition\<close>
      from "1.prems"(1) BabLit_Array len_ok elab_elems have next_mv_eq: "next_mv' = next_mv1"
        by (auto simp: Let_def unify_and_coerce_def split: sum.splits prod.splits)
      have len_eq: "length elabTms = length actualTypes"
        using ih_narrow by (simp add: list_all2_lengthD)
      show ?thesis
        unfolding list_all2_conv_all_nth
      proof (intro conjI allI impI)
        show "length elabTms = length actualTypes" by (rule len_eq)
      next
        fix i assume i_lt: "i < length elabTms"
        have "core_term_type (extend_env_with_tyvars env ghost (next_mv + 1) next_mv1) ghost
                  (elabTms ! i) = Some (actualTypes ! i)"
          using ih_narrow i_lt len_eq by (simp add: list_all2_conv_all_nth)
        from core_term_type_extend_env_with_tyvars_mono[OF this, of next_mv next_mv']
        show "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost
                (elabTms ! i) = Some (actualTypes ! i)"
          using next_mv_eq by simp
      qed
    qed
    show ?thesis
      using elab_term_correct_array_lit[OF _ "1.prems"(2,4) elab_elems ih_elems]
            "1.prems"(1) BabLit_Array by simp
  qed
next
  \<comment> \<open>Case: BabTm_Name (variable or nullary data constructor)\<close>
  case (2 env elabEnv ghost loc name tyArgs next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  show ?case
  proof (cases "tyenv_lookup_var env name")
    case (Some varTy)
    \<comment> \<open>Variable case\<close>
    from "2.prems"(1) Some have
      ghost_ok: "ghost = NotGhost \<longrightarrow> \<not> tyenv_var_ghost env name" and
      newTm_eq: "newTm = CoreTm_Var name" and
      ty_eq: "ty = varTy" and
      next_mv_eq: "next_mv' = next_mv"
      by (auto split: if_splits)
    show ?thesis using Some ghost_ok newTm_eq ty_eq next_mv_eq by simp
  next
    case None
    show ?thesis
    proof (cases "name |\<in>| EE_GhostConstants elabEnv")
      case True
      \<comment> \<open>Ghost constant: the reference elaborates to a nullary ghost call.\<close>
      from "2.prems"(1) None True obtain funInfo where
        fn_lookup: "fmlookup (TE_Functions env) name = Some funInfo" and
        ghost_eq: "ghost = Ghost" and
        result_eq: "newTm = CoreTm_FunctionCall name [] []"
                   "ty = FI_ReturnType funInfo"
                   "next_mv' = next_mv"
        by (cases ghost) (auto split: option.splits if_splits)
      \<comment> \<open>From elabenv_well_formed: the desugared FunInfo is nullary, ghost, pure.\<close>
      from "2.prems"(3) True fn_lookup obtain retTy where
        info_eq: "funInfo = \<lparr> FI_TyArgs = [], FI_TmArgs = [], FI_ReturnType = retTy,
                              FI_Ghost = Ghost, FI_Impure = False \<rparr>"
        unfolding elabenv_well_formed_def ghost_constants_consistent_def by force
      have fn_lookup': "fmlookup (TE_Functions (extend_env_with_tyvars env ghost next_mv next_mv'))
                          name = Some funInfo"
        using fn_lookup by (simp add: extend_env_with_tyvars_def)
      show ?thesis
        using result_eq ghost_eq fn_lookup' info_eq by simp
    next
      case gcFalse: False
    \<comment> \<open>Constructor case\<close>
    from "2.prems"(1) None gcFalse obtain dtName tyvars payloadTy where
      ctor_lookup: "fmlookup (TE_DataCtors env) name = Some (dtName, tyvars, payloadTy)"
      by (auto simp: resolve_type_args_def Let_def
               split: option.splits if_splits sum.splits prod.splits)
    from "2.prems"(1) None gcFalse ctor_lookup have
      nullary_mem: "name |\<in>| EE_NullaryDataCtors elabEnv"
      by (auto simp: resolve_type_args_def Let_def
               split: if_splits sum.splits prod.splits option.splits)
    from "2.prems"(1) None gcFalse ctor_lookup nullary_mem have
      ghost_ok: "ghost = NotGhost \<longrightarrow> dtName |\<notin>| TE_GhostDatatypes env"
      by (auto simp: resolve_type_args_def Let_def
               split: if_splits sum.splits prod.splits)

    \<comment> \<open>Extract resolve_type_args result\<close>
    from "2.prems"(1) None gcFalse ctor_lookup nullary_mem ghost_ok
    obtain newTyArgs next_mv1 where
      resolve_eq: "resolve_type_args env elabEnv ghost loc name tyvars tyArgs next_mv
                   = Inr (newTyArgs, next_mv1)"
      by (auto simp: resolve_type_args_def Let_def
               split: if_splits sum.splits prod.splits)
    from "2.prems"(1) None gcFalse ctor_lookup nullary_mem ghost_ok resolve_eq have
      result_eq: "newTm = CoreTm_VariantCtor name newTyArgs (CoreTm_Record [])"
                 "ty = CoreTy_Datatype dtName newTyArgs"
                 "next_mv' = next_mv1"
      by (auto simp: resolve_type_args_def Let_def
               split: if_splits sum.splits prod.splits)

    \<comment> \<open>From elabenv_well_formed + nullary membership: payloadTy = CoreTy_Record []\<close>
    from "2.prems"(3) nullary_mem ctor_lookup have
      payload_eq: "payloadTy = CoreTy_Record []"
      unfolding elabenv_well_formed_def nullary_data_ctors_consistent_def by force

    \<comment> \<open>From resolve_type_args_correct: type args are well-kinded, runtime (in
        NotGhost mode) and complete in ?env'\<close>
    have td_wf: "typedefs_well_formed env (EE_Typedefs elabEnv)"
      using "2.prems"(3) unfolding elabenv_well_formed_def by simp
    have rta: "next_mv \<le> next_mv'
             \<and> length newTyArgs = length tyvars
             \<and> list_all (is_well_kinded ?env') newTyArgs
             \<and> (ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env') newTyArgs)
             \<and> list_all is_complete_type newTyArgs"
      using resolve_type_args_correct[OF resolve_eq "2.prems"(2) td_wf] result_eq by simp

    \<comment> \<open>TE_DataCtors is unchanged by extend_env_with_tyvars\<close>
    have ctor_lookup': "fmlookup (TE_DataCtors ?env') name = Some (dtName, tyvars, payloadTy)"
      using ctor_lookup by (simp add: extend_env_with_tyvars_def)

    \<comment> \<open>TE_GhostDatatypes is unchanged\<close>
    have ghost_ok': "ghost = NotGhost \<longrightarrow> dtName |\<notin>| TE_GhostDatatypes ?env'"
      using ghost_ok by (simp add: extend_env_with_tyvars_def)

    \<comment> \<open>Payload types match: apply_subst tySubst (CoreTy_Record []) = CoreTy_Record []\<close>
    have payload_match: "CoreTy_Record [] = apply_subst (fmap_of_list (zip tyvars newTyArgs)) (CoreTy_Record [])"
      by simp

    \<comment> \<open>Put it together\<close>
    show ?thesis
      using result_eq ctor_lookup' rta ghost_ok' payload_eq payload_match
      by simp
    qed
  qed

next
  \<comment> \<open>Case: BabTm_Cast\<close>
  case (3 env elabEnv ghost loc targetTy operand next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  \<comment> \<open>Extract intermediate results\<close>
  from "3.prems"(1) obtain newTargetTy where
    elab_target: "elab_type env elabEnv ghost targetTy = Inr newTargetTy"
    by (auto split: sum.splits)
  from "3.prems"(1) elab_target obtain newOperand operandTy next_mv'' where
    elab_operand: "elab_term env elabEnv ghost operand next_mv = Inr (newOperand, operandTy, next_mv'')"
    by (auto split: sum.splits)
  \<comment> \<open>Cast forwards the operand's next_mv, so next_mv' = next_mv''\<close>
  from "3.prems"(1) elab_target elab_operand have next_mv_eq: "next_mv' = next_mv''"
    by (auto split: if_splits option.splits)
  from "3.prems"(1) elab_target elab_operand have
    target_is_int: "is_integer_type newTargetTy"
    by (auto split: if_splits)

  \<comment> \<open>IH: operand has its type in the extended env\<close>
  have ih: "core_term_type ?env' ghost newOperand = Some operandTy"
    by (simp add: "3.IH" "3.prems"(2,3,4) elab_operand elab_target next_mv_eq)

  \<comment> \<open>Target type is well-kinded / runtime in the original env and so also in ?env'\<close>
  have td_wf: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using "3.prems"(3) unfolding elabenv_well_formed_def by simp
  have target_wk_env: "is_well_kinded env newTargetTy"
    using elab_target "3.prems"(2) td_wf elab_type_is_well_kinded by simp
  have target_rt_env: "ghost = NotGhost \<longrightarrow> is_runtime_type env newTargetTy"
    using elab_target "3.prems"(2) td_wf elab_type_notghost_is_runtime by (cases ghost) auto
  have target_wk: "is_well_kinded ?env' newTargetTy"
    using target_wk_env is_well_kinded_extend_tyvars
    unfolding extend_env_with_tyvars_def
    by (simp add: is_integer_type_well_kinded target_is_int)
  have target_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type ?env' newTargetTy"
    using target_rt_env is_runtime_type_extend_runtime_tyvars
    unfolding extend_env_with_tyvars_def by auto

  have wf': "tyenv_well_formed ?env'"
    using "3.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast

  let ?is_flex = "(\<lambda>n. n |\<notin>| TE_TypeVars env)"

  show ?case
  proof (cases "unify ?is_flex operandTy newTargetTy")
    case (Some subst)
    \<comment> \<open>Unification succeeded: cast is eliminated via the unifier's substitution\<close>
    from "3.prems"(1) elab_target elab_operand target_is_int Some have
      result: "newTm = apply_subst_to_term subst newOperand" "ty = newTargetTy"
      by (auto split: if_splits)

    \<comment> \<open>operandTy is well-kinded in ?env'\<close>
    have operand_wk: "is_well_kinded ?env' operandTy"
      using core_term_type_well_kinded[OF ih wf'] .
    have operand_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type ?env' operandTy"
      using core_term_type_notghost_runtime ih wf' by auto

    \<comment> \<open>The unifier's substitution range is well-kinded and runtime in ?env'\<close>
    have subst_wk: "\<forall>ty' \<in> fmran' subst. is_well_kinded ?env' ty'"
      using unify_preserves_well_kinded[OF Some operand_wk target_wk] .
    have subst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type ?env' ty')"
    proof
      assume ng: "ghost = NotGhost"
      show "\<forall>ty' \<in> fmran' subst. is_runtime_type ?env' ty'"
        using unify_preserves_runtime[OF Some] operand_rt target_rt ng by blast
    qed

    \<comment> \<open>The unifier only binds flex metas; locals and return type are unaffected. \<close>
    have unif_dom_flex: "\<forall>n. n |\<in>| fmdom subst \<longrightarrow> ?is_flex n"
      using unify_unify_list_dom_flex(1)[OF Some] .
    have env'_locals: "TE_LocalVars ?env' = TE_LocalVars env"
      unfolding extend_env_with_tyvars_def by simp
    have env'_ret: "TE_ReturnType ?env' = TE_ReturnType env"
      unfolding extend_env_with_tyvars_def by simp
    from flex_subst_identity_on_env[OF unif_dom_flex "3.prems"(2) env'_locals env'_ret]
    have locals_unaffected: "\<And>name ty'. fmlookup (TE_LocalVars ?env') name = Some ty'
                                        \<Longrightarrow> apply_subst subst ty' = ty'"
      and ret_unaffected: "apply_subst subst (TE_ReturnType ?env') = TE_ReturnType ?env'"
      by blast+
    have env'_abs: "TE_AbstractTypes ?env' = TE_AbstractTypes env"
      unfolding extend_env_with_tyvars_def by simp
    have abs_no_subst: "\<And>n. n |\<in>| TE_AbstractTypes ?env' \<Longrightarrow> fmlookup subst n = None"
      using flex_subst_abs_no_subst[OF unif_dom_flex[rule_format] "3.prems"(2) env'_abs] .

    \<comment> \<open>The target is an (atomic) integer type, so the unifier's range is complete. \<close>
    have subst_cp: "\<forall>ty' \<in> fmran' subst. is_complete_type ty'"
      using unify_atomic_range_complete[OF Some is_integer_type_atomic[OF target_is_int]] .

    have subst_applied:
      "core_term_type ?env' ghost (apply_subst_to_term subst newOperand)
         = Some (apply_subst subst operandTy)"
      using apply_subst_to_term_preserves_typing
              [OF ih wf' subst_wk subst_rt locals_unaffected ret_unaffected abs_no_subst subst_cp] .
    also have "apply_subst subst operandTy = apply_subst subst newTargetTy"
      using unify_sound[OF Some] .
    also have "apply_subst subst newTargetTy = newTargetTy"
      using target_is_int is_integer_type_apply_subst by simp
    finally show ?thesis using result by simp

  next
    case None
    \<comment> \<open>Unification failed: fall through to the integer-cast branch\<close>
    from "3.prems"(1) elab_target elab_operand target_is_int None have
      result: "newTm = CoreTm_Cast newTargetTy newOperand" "ty = newTargetTy"
      and operand_is_int: "is_integer_type operandTy"
      by (auto split: if_splits)
    show ?thesis using result ih operand_is_int target_is_int target_rt by auto
  qed

next
  \<comment> \<open>Case: BabTm_If - elaborates to CoreTm_Match with True/False patterns\<close>
  case (4 env elabEnv ghost loc condTm thenTm elseTm next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"

  \<comment> \<open>Extract intermediate elaboration results\<close>
  from "4.prems"(1) obtain newCond condTy next_mv1 where
    elab_cond: "elab_term env elabEnv ghost condTm next_mv = Inr (newCond, condTy, next_mv1)"
    by (auto split: sum.splits)
  from "4.prems"(1) elab_cond obtain newThen thenTy next_mv2 where
    elab_then: "elab_term env elabEnv ghost thenTm next_mv1 = Inr (newThen, thenTy, next_mv2)"
    by (auto split: sum.splits)
  from "4.prems"(1) elab_cond elab_then obtain newElse elseTy next_mv3 where
    elab_else: "elab_term env elabEnv ghost elseTm next_mv2 = Inr (newElse, elseTy, next_mv3)"
    by (auto split: sum.splits)

  let ?is_flex = "(\<lambda>n. n |\<notin>| TE_TypeVars env)"

  \<comment> \<open>Elaboration only succeeds if the condition unifies with Bool. \<close>
  from "4.prems"(1) elab_cond elab_then elab_else obtain condSubst where
    cond_unify: "unify ?is_flex condTy CoreTy_Bool = Some condSubst"
    by (auto simp: Let_def split: sum.splits option.splits)

  define finalCond where
    "finalCond = apply_subst_to_term condSubst newCond"

  \<comment> \<open>If forwards elseTm's next_mv so outer next_mv' = next_mv3\<close>
  from "4.prems"(1) elab_cond elab_then elab_else cond_unify have next_mv_eq: "next_mv' = next_mv3"
    by (auto simp: Let_def split: option.splits if_splits)

  \<comment> \<open>Monotonicity: next_mv \<le> next_mv1 \<le> next_mv2 \<le> next_mv3\<close>
  have mono_12: "next_mv \<le> next_mv1"
    using elab_term_next_mv_monotone[OF elab_cond] .
  have mono_23: "next_mv1 \<le> next_mv2"
    using elab_term_next_mv_monotone[OF elab_then] .
  have mono_34: "next_mv2 \<le> next_mv3"
    using elab_term_next_mv_monotone[OF elab_else] .

  \<comment> \<open>Freshness preconditions for each sub-call\<close>
  have fresh_1: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n next_mv1"
    using "4.prems"(4) mono_12 tyvar_fresh_ok_mono by fastforce
  have fresh_2: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n next_mv2"
    using "4.prems"(4) mono_12 mono_23 tyvar_fresh_ok_mono by fastforce

  \<comment> \<open>IH: elaborated subterms have their claimed types in their respective sub-envs\<close>
  have ih_cond_sub: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv1) ghost newCond = Some condTy"
    using "4.IH"(1) elab_cond "4.prems"(2,3,4) by simp
  have ih_then_sub: "core_term_type (extend_env_with_tyvars env ghost next_mv1 next_mv2) ghost newThen = Some thenTy"
    using "4.IH"(2) elab_cond elab_then "4.prems"(2,3) fresh_1 by simp
  have ih_else_sub: "core_term_type (extend_env_with_tyvars env ghost next_mv2 next_mv3) ghost newElse = Some elseTy"
    using "4.IH"(3) elab_cond elab_then elab_else "4.prems"(2,3) fresh_2 by simp

  \<comment> \<open>Lift all IHs into the outer extended env\<close>
  have ih_cond: "core_term_type ?env' ghost newCond = Some condTy"
    using core_term_type_extend_env_with_tyvars_mono[OF ih_cond_sub, where lo'=next_mv and hi'=next_mv']
          mono_12 mono_23 mono_34 next_mv_eq by simp
  have ih_then: "core_term_type ?env' ghost newThen = Some thenTy"
    using core_term_type_extend_env_with_tyvars_mono[OF ih_then_sub, where lo'=next_mv and hi'=next_mv']
          mono_12 mono_23 mono_34 next_mv_eq by simp
  have ih_else: "core_term_type ?env' ghost newElse = Some elseTy"
    using core_term_type_extend_env_with_tyvars_mono[OF ih_else_sub, where lo'=next_mv and hi'=next_mv']
          mono_12 mono_23 mono_34 next_mv_eq by simp

  have wf': "tyenv_well_formed ?env'"
    using "4.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast

  \<comment> \<open>A generic helper: any substitution whose domain is disjoint from
      TE_TypeVars env leaves locals and the return type unchanged. \<close>
  have unif_id_on_env:
    "\<And>s ty'. \<forall>n. n |\<in>| fmdom (s :: (string, CoreType) fmap) \<longrightarrow> ?is_flex n
              \<Longrightarrow> type_tyvars ty' \<subseteq> fset (TE_TypeVars env)
              \<Longrightarrow> apply_subst s ty' = ty'"
  proof -
    fix s :: "(string, CoreType) fmap" and ty'
    assume dom_flex: "\<forall>n. n |\<in>| fmdom s \<longrightarrow> ?is_flex n"
    assume mvs: "type_tyvars ty' \<subseteq> fset (TE_TypeVars env)"
    have "type_tyvars ty' \<inter> fset (fmdom s) = {}"
      using mvs dom_flex by auto
    thus "apply_subst s ty' = ty'" by (rule apply_subst_disjoint_id)
  qed
  have locals_unaffected_for:
    "\<And>s name ty'. \<forall>n. n |\<in>| fmdom (s :: (string, CoreType) fmap) \<longrightarrow> ?is_flex n
                 \<Longrightarrow> fmlookup (TE_LocalVars ?env') name = Some ty'
                 \<Longrightarrow> apply_subst s ty' = ty'"
  proof -
    fix s :: "(string, CoreType) fmap" and name ty'
    assume dom_flex: "\<forall>n. n |\<in>| fmdom s \<longrightarrow> ?is_flex n"
    assume lk: "fmlookup (TE_LocalVars ?env') name = Some ty'"
    have "TE_LocalVars ?env' = TE_LocalVars env"
      unfolding extend_env_with_tyvars_def by simp
    with lk have lk_env: "fmlookup (TE_LocalVars env) name = Some ty'" by simp
    from "4.prems"(2) have "tyenv_vars_well_kinded env"
      unfolding tyenv_well_formed_def by simp
    with lk_env have "is_well_kinded env ty'"
      unfolding tyenv_vars_well_kinded_def by blast
    from is_well_kinded_type_tyvars_subset[OF this]
    have "type_tyvars ty' \<subseteq> fset (TE_TypeVars env)" .
    thus "apply_subst s ty' = ty'"
      using unif_id_on_env[OF dom_flex] by blast
  qed
  have ret_unaffected_for:
    "\<And>s. \<forall>n. n |\<in>| fmdom (s :: (string, CoreType) fmap) \<longrightarrow> ?is_flex n
         \<Longrightarrow> apply_subst s (TE_ReturnType ?env') = TE_ReturnType ?env'"
  proof -
    fix s :: "(string, CoreType) fmap"
    assume dom_flex: "\<forall>n. n |\<in>| fmdom s \<longrightarrow> ?is_flex n"
    have ret_eq: "TE_ReturnType ?env' = TE_ReturnType env"
      unfolding extend_env_with_tyvars_def by simp
    from "4.prems"(2) have "tyenv_return_type_well_kinded env"
      unfolding tyenv_well_formed_def by simp
    hence "is_well_kinded env (TE_ReturnType env)"
      unfolding tyenv_return_type_well_kinded_def .
    from is_well_kinded_type_tyvars_subset[OF this]
    have "type_tyvars (TE_ReturnType env) \<subseteq> fset (TE_TypeVars env)" .
    hence "apply_subst s (TE_ReturnType env) = TE_ReturnType env"
      using unif_id_on_env[OF dom_flex] by blast
    thus "apply_subst s (TE_ReturnType ?env') = TE_ReturnType ?env'"
      using ret_eq by simp
  qed
  have abs_no_subst_for:
    "\<And>s n. \<forall>n. n |\<in>| fmdom (s :: (string, CoreType) fmap) \<longrightarrow> ?is_flex n
         \<Longrightarrow> n |\<in>| TE_AbstractTypes ?env' \<Longrightarrow> fmlookup s n = None"
  proof -
    fix s :: "(string, CoreType) fmap" and n
    assume dom_flex: "\<forall>n. n |\<in>| fmdom s \<longrightarrow> ?is_flex n"
    assume n_abs: "n |\<in>| TE_AbstractTypes ?env'"
    have abs_eq: "TE_AbstractTypes ?env' = TE_AbstractTypes env"
      unfolding extend_env_with_tyvars_def by simp
    show "fmlookup s n = None"
      using flex_subst_abs_no_subst[OF dom_flex[rule_format] "4.prems"(2) abs_eq n_abs] .
  qed

  \<comment> \<open>condSubst range is well-kinded / runtime in ?env'. \<close>
  have cond_wk: "is_well_kinded ?env' condTy"
    using core_term_type_well_kinded[OF ih_cond wf'] .
  have cond_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type ?env' condTy"
    using core_term_type_notghost_runtime ih_cond wf' by auto
  have bool_wk: "is_well_kinded ?env' CoreTy_Bool" by simp
  have bool_rt: "is_runtime_type ?env' CoreTy_Bool" by simp
  have condSubst_wk: "\<forall>ty' \<in> fmran' condSubst. is_well_kinded ?env' ty'"
    using unify_preserves_well_kinded[OF cond_unify cond_wk bool_wk] .
  have condSubst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' condSubst. is_runtime_type ?env' ty')"
  proof
    assume ng: "ghost = NotGhost"
    show "\<forall>ty' \<in> fmran' condSubst. is_runtime_type ?env' ty'"
      using unify_preserves_runtime[OF cond_unify] cond_rt bool_rt ng by blast
  qed
  have condSubst_dom_flex: "\<forall>n. n |\<in>| fmdom condSubst \<longrightarrow> ?is_flex n"
    using unify_unify_list_dom_flex(1)[OF cond_unify] .
  have condSubst_locals: "\<And>name ty'. fmlookup (TE_LocalVars ?env') name = Some ty'
                                     \<Longrightarrow> apply_subst condSubst ty' = ty'"
    using locals_unaffected_for[OF condSubst_dom_flex] .
  have condSubst_ret: "apply_subst condSubst (TE_ReturnType ?env') = TE_ReturnType ?env'"
    using ret_unaffected_for[OF condSubst_dom_flex] .
  have condSubst_abs: "\<And>n. n |\<in>| TE_AbstractTypes ?env' \<Longrightarrow> fmlookup condSubst n = None"
    using abs_no_subst_for[OF condSubst_dom_flex] .
  have condSubst_cp: "\<forall>ty' \<in> fmran' condSubst. is_complete_type ty'"
    using unify_bool_range_complete[OF cond_unify] .

  \<comment> \<open>Final condition has type Bool in ?env'. \<close>
  have finalCond_typed: "core_term_type ?env' ghost finalCond = Some CoreTy_Bool"
  proof -
    have "core_term_type ?env' ghost (apply_subst_to_term condSubst newCond)
            = Some (apply_subst condSubst condTy)"
      using apply_subst_to_term_preserves_typing
              [OF ih_cond wf' condSubst_wk condSubst_rt condSubst_locals condSubst_ret condSubst_abs
                  condSubst_cp] .
    also have "apply_subst condSubst condTy = apply_subst condSubst CoreTy_Bool"
      using unify_sound[OF cond_unify] .
    also have "apply_subst condSubst CoreTy_Bool = CoreTy_Bool" by simp
    finally show ?thesis unfolding finalCond_def .
  qed

  \<comment> \<open>Now handle the two cases: unification succeeds or integer coercion\<close>
  show ?case
  proof (cases "unify ?is_flex thenTy elseTy")
    case (Some branchSubst)
    \<comment> \<open>Unification succeeded\<close>
    let ?resultTy = "apply_subst branchSubst thenTy"
    let ?newThen' = "apply_subst_to_term branchSubst newThen"
    let ?newElse' = "apply_subst_to_term branchSubst newElse"
    let ?matchArms = "[(CorePat_Bool True, ?newThen'), (CorePat_Bool False, ?newElse')]"

    from "4.prems"(1) elab_cond elab_then elab_else cond_unify Some have
      branchSubst_complete: "typesubst_complete branchSubst" and
      result_eq: "newTm = CoreTm_Match finalCond ?matchArms" "ty = ?resultTy"
      by (auto simp: finalCond_def Let_def split: option.splits if_splits)
    have branchSubst_cp: "\<forall>ty' \<in> fmran' branchSubst. is_complete_type ty'"
      using branchSubst_complete unfolding typesubst_complete_def .

    \<comment> \<open>From unify_sound: applying branchSubst unifies the types\<close>
    from unify_sound[OF Some] have unified: "apply_subst branchSubst thenTy = apply_subst branchSubst elseTy" .

    \<comment> \<open>branchSubst range is well-kinded / runtime in ?env'. \<close>
    have then_wk: "is_well_kinded ?env' thenTy"
      using core_term_type_well_kinded[OF ih_then wf'] .
    have else_wk: "is_well_kinded ?env' elseTy"
      using core_term_type_well_kinded[OF ih_else wf'] .
    have branchSubst_wk: "\<forall>ty \<in> fmran' branchSubst. is_well_kinded ?env' ty"
      using unify_preserves_well_kinded[OF Some then_wk else_wk] .
    have branchSubst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' branchSubst. is_runtime_type ?env' ty)"
    proof
      assume ng: "ghost = NotGhost"
      have "is_runtime_type ?env' thenTy"
        using core_term_type_notghost_runtime ih_then wf' ng by auto
      moreover have "is_runtime_type ?env' elseTy"
        using core_term_type_notghost_runtime ih_else wf' ng by auto
      ultimately show "\<forall>ty \<in> fmran' branchSubst. is_runtime_type ?env' ty"
        using unify_preserves_runtime[OF Some] by blast
    qed
    have branchSubst_dom_flex: "\<forall>n. n |\<in>| fmdom branchSubst \<longrightarrow> ?is_flex n"
      using unify_unify_list_dom_flex(1)[OF Some] .
    have branchSubst_locals:
      "\<And>name ty'. fmlookup (TE_LocalVars ?env') name = Some ty'
                    \<Longrightarrow> apply_subst branchSubst ty' = ty'"
      using locals_unaffected_for[OF branchSubst_dom_flex] .
    have branchSubst_ret: "apply_subst branchSubst (TE_ReturnType ?env') = TE_ReturnType ?env'"
      using ret_unaffected_for[OF branchSubst_dom_flex] .
    have branchSubst_abs: "\<And>n. n |\<in>| TE_AbstractTypes ?env' \<Longrightarrow> fmlookup branchSubst n = None"
      using abs_no_subst_for[OF branchSubst_dom_flex] .

    have then'_typed: "core_term_type ?env' ghost ?newThen' = Some ?resultTy"
      using apply_subst_to_term_preserves_typing
              [OF ih_then wf' branchSubst_wk branchSubst_rt branchSubst_locals branchSubst_ret
                  branchSubst_abs branchSubst_cp] .
    have else'_typed: "core_term_type ?env' ghost ?newElse' = Some ?resultTy"
      using apply_subst_to_term_preserves_typing
              [OF ih_else wf' branchSubst_wk branchSubst_rt branchSubst_locals branchSubst_ret
                  branchSubst_abs branchSubst_cp]
            unified by simp

    \<comment> \<open>The match typechecks\<close>
    have "core_term_type ?env' ghost (CoreTm_Match finalCond ?matchArms) = Some ?resultTy"
    proof -
      have "?matchArms \<noteq> []" by simp
      have pats_compat: "list_all (\<lambda>p. pattern_compatible ?env' p CoreTy_Bool) (map fst ?matchArms)"
        by simp
      have bodies_typed: "list_all (\<lambda>body. core_term_type ?env' ghost body = Some ?resultTy) (map snd ?matchArms)"
        using then'_typed else'_typed by simp
      show ?thesis
        using finalCond_typed \<open>?matchArms \<noteq> []\<close> pats_compat bodies_typed
        by (simp add: then'_typed)
    qed
    thus ?thesis using result_eq by simp

  next
    case None
    \<comment> \<open>Unification failed - try integer coercion\<close>
    from "4.prems"(1) elab_cond elab_then elab_else cond_unify None
    obtain coercedThen coercedElse commonTy where
      coerce: "coerce_to_common_int_type newThen thenTy newElse elseTy = Some (coercedThen, coercedElse, commonTy)"
      by (auto simp: finalCond_def Let_def split: option.splits if_splits)

    let ?matchArms = "[(CorePat_Bool True, coercedThen), (CorePat_Bool False, coercedElse)]"

    from "4.prems"(1) elab_cond elab_then elab_else cond_unify None coerce have
      result_eq: "newTm = CoreTm_Match finalCond ?matchArms" "ty = commonTy"
      by (auto simp: finalCond_def Let_def split: option.splits if_splits)

    \<comment> \<open>From coerce_to_common_int_type_correct: coerced terms have common type\<close>
    have coerced_typed: "core_term_type ?env' ghost coercedThen = Some commonTy
                       \<and> core_term_type ?env' ghost coercedElse = Some commonTy"
      using coerce_to_common_int_type_correct[OF coerce ih_then ih_else wf'] .
    hence coerced_then_typed: "core_term_type ?env' ghost coercedThen = Some commonTy"
      and coerced_else_typed: "core_term_type ?env' ghost coercedElse = Some commonTy"
      by simp_all

    \<comment> \<open>The match typechecks\<close>
    have "core_term_type ?env' ghost (CoreTm_Match finalCond ?matchArms) = Some commonTy"
    proof -
      have "?matchArms \<noteq> []" by simp
      have pats_compat: "list_all (\<lambda>p. pattern_compatible ?env' p CoreTy_Bool) (map fst ?matchArms)"
        by simp
      have bodies_typed: "list_all (\<lambda>body. core_term_type ?env' ghost body = Some commonTy) (map snd ?matchArms)"
        using coerced_then_typed coerced_else_typed by simp
      show ?thesis
        using finalCond_typed \<open>?matchArms \<noteq> []\<close> pats_compat bodies_typed
        by (simp add: coerced_then_typed)
    qed
    thus ?thesis using result_eq by simp
  qed

next
  \<comment> \<open>Case: BabTm_Unop\<close>
  case (5 env elabEnv ghost loc op operand next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  \<comment> \<open>Extract intermediate results\<close>
  from "5.prems"(1) obtain newOperand operandTy next_mv'' where
    elab_operand: "elab_term env elabEnv ghost operand next_mv = Inr (newOperand, operandTy, next_mv'')"
    by (auto split: sum.splits)
  \<comment> \<open>Unop forwards the operand's next_mv\<close>
  from "5.prems"(1) elab_operand have next_mv_eq: "next_mv' = next_mv''"
    by (auto simp: Let_def split: option.splits BabUnop.splits if_splits)

  have wf': "tyenv_well_formed ?env'"
    using "5.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast

  \<comment> \<open>IH: operand has its type in the extended env\<close>
  have ih: "core_term_type ?env' ghost newOperand = Some operandTy"
    using "5.IH"[OF elab_operand "5.prems"(2,3,4)] next_mv_eq by simp

  let ?cop = "unop_to_core op"
  let ?defaultTy = "default_type_for_unop ?cop"
  let ?is_flex = "(\<lambda>n. n |\<notin>| TE_TypeVars env)"

  show ?case
  proof (cases "unify ?is_flex operandTy ?defaultTy")
    case (Some subst)
    \<comment> \<open>Unification succeeded: operand is either already the default type or a
        flex metavariable. The substitution resolves it to defaultTy. \<close>
    let ?newOperand2 = "apply_subst_to_term subst newOperand"
    from "5.prems"(1) elab_operand Some have
      result: "newTm = CoreTm_Unop ?cop ?newOperand2" "ty = ?defaultTy"
      by (auto simp: Let_def)

    \<comment> \<open>operandTy is well-kinded / runtime in ?env'\<close>
    have operand_wk: "is_well_kinded ?env' operandTy"
      using core_term_type_well_kinded[OF ih wf'] .
    have operand_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type ?env' operandTy"
      using core_term_type_notghost_runtime ih wf' by auto
    have default_wk: "is_well_kinded ?env' ?defaultTy"
      by (rule default_type_for_unop_is_well_kinded)
    have default_rt: "is_runtime_type ?env' ?defaultTy"
      by (rule default_type_for_unop_is_runtime)

    \<comment> \<open>subst range is well-kinded / runtime in ?env'\<close>
    have subst_wk: "\<forall>ty' \<in> fmran' subst. is_well_kinded ?env' ty'"
      using unify_preserves_well_kinded[OF Some operand_wk default_wk] .
    have subst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type ?env' ty')"
    proof
      assume ng: "ghost = NotGhost"
      show "\<forall>ty' \<in> fmran' subst. is_runtime_type ?env' ty'"
        using unify_preserves_runtime[OF Some] operand_rt default_rt ng by blast
    qed

    \<comment> \<open>subst has flex domain, so locals and return type are unaffected. \<close>
    have subst_dom_flex: "\<forall>n. n |\<in>| fmdom subst \<longrightarrow> ?is_flex n"
      using unify_unify_list_dom_flex(1)[OF Some] .
    have env'_locals: "TE_LocalVars ?env' = TE_LocalVars env"
      unfolding extend_env_with_tyvars_def by simp
    have env'_ret: "TE_ReturnType ?env' = TE_ReturnType env"
      unfolding extend_env_with_tyvars_def by simp
    from flex_subst_identity_on_env[OF subst_dom_flex "5.prems"(2) env'_locals env'_ret]
    have locals_unaffected: "\<And>name ty'. fmlookup (TE_LocalVars ?env') name = Some ty'
                                        \<Longrightarrow> apply_subst subst ty' = ty'"
      and ret_unaffected: "apply_subst subst (TE_ReturnType ?env') = TE_ReturnType ?env'"
      by blast+
    have env'_abs: "TE_AbstractTypes ?env' = TE_AbstractTypes env"
      unfolding extend_env_with_tyvars_def by simp
    have abs_no_subst: "\<And>n. n |\<in>| TE_AbstractTypes ?env' \<Longrightarrow> fmlookup subst n = None"
      using flex_subst_abs_no_subst[OF subst_dom_flex[rule_format] "5.prems"(2) env'_abs] .

    \<comment> \<open>The default type is atomic (i32 or Bool), so the unifier's range is complete. \<close>
    have default_atomic: "is_atomic_type ?defaultTy"
      by (cases ?cop) simp_all
    have subst_cp: "\<forall>ty' \<in> fmran' subst. is_complete_type ty'"
      using unify_atomic_range_complete[OF Some default_atomic] .

    \<comment> \<open>After substitution, newOperand has type defaultTy in ?env'\<close>
    have operand2_typed: "core_term_type ?env' ghost ?newOperand2 = Some ?defaultTy"
    proof -
      have "core_term_type ?env' ghost ?newOperand2 = Some (apply_subst subst operandTy)"
        using apply_subst_to_term_preserves_typing
                [OF ih wf' subst_wk subst_rt locals_unaffected ret_unaffected abs_no_subst subst_cp] .
      also have "apply_subst subst operandTy = apply_subst subst ?defaultTy"
        using unify_sound[OF Some] .
      also have "apply_subst subst ?defaultTy = ?defaultTy"
        by (cases ?cop) simp_all
      finally show ?thesis .
    qed

    \<comment> \<open>The default type satisfies the operator's requirement\<close>
    have op_ok: "(case ?cop of
        CoreUnop_Negate \<Rightarrow> is_signed_numeric_type ?defaultTy
      | CoreUnop_Complement \<Rightarrow> is_finite_integer_type ?defaultTy
      | CoreUnop_Not \<Rightarrow> ?defaultTy = CoreTy_Bool)"
      by (cases op) simp_all

    show ?thesis using result operand2_typed op_ok by (cases ?cop) auto

  next
    case None
    \<comment> \<open>Unification failed: operand is a concrete type different from defaultTy.
        Case-split on the operator and the operand type. \<close>
    show ?thesis
    proof (cases op)
      case BabUnop_Negate
      \<comment> \<open>Negate: must be signed numeric (not defaultTy = i32).\<close>
      from "5.prems"(1) elab_operand None BabUnop_Negate have
        signed: "is_signed_numeric_type operandTy"
        and result: "newTm = CoreTm_Unop CoreUnop_Negate newOperand" "ty = operandTy"
        by (auto simp: Let_def split: if_splits)
      show ?thesis using result ih signed by simp
    next
      case BabUnop_Complement
      \<comment> \<open>Complement: must be a finite integer type (not defaultTy = i32).\<close>
      from "5.prems"(1) elab_operand None BabUnop_Complement have
        finite: "is_finite_integer_type operandTy"
        and result: "newTm = CoreTm_Unop CoreUnop_Complement newOperand" "ty = operandTy"
        by (auto simp: Let_def split: if_splits)
      show ?thesis using result ih finite by simp
    next
      case BabUnop_Not
      \<comment> \<open>Not: elaborator errors since unify against Bool failed. \<close>
      from "5.prems"(1) elab_operand None BabUnop_Not show ?thesis
        by (auto simp: Let_def)
    qed
  qed

next
  \<comment> \<open>Case: BabTm_Binop\<close>
  case (6 env elabEnv ghost loc lhs operands next_mv)
  let ?is_flex = "(\<lambda>n. n |\<notin>| TE_TypeVars env)"
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  \<comment> \<open>Extract elaboration of LHS\<close>
  from "6.prems"(1) obtain newLhs lhsTy next_mv1 where
    elab_lhs: "elab_term env elabEnv ghost lhs next_mv = Inr (newLhs, lhsTy, next_mv1)"
    by (auto split: sum.splits)
  \<comment> \<open>Extract elaboration of RHS terms\<close>
  from "6.prems"(1) elab_lhs obtain rhsTms rhsTys next_mv2 where
    elab_rhs_list: "elab_term_list env elabEnv ghost (map snd operands) next_mv1
                    = Inr (rhsTms, rhsTys, next_mv2)"
    by (auto split: sum.splits)
  \<comment> \<open>Build the operator list\<close>
  let ?opTriples = "zip (map fst operands) (zip rhsTms rhsTys)"
  let ?opList = "map (\<lambda>(op, tm_ty). (op, fst tm_ty, snd tm_ty)) ?opTriples"
  \<comment> \<open>Extract process_binop_chain success\<close>
  from "6.prems"(1) elab_lhs elab_rhs_list obtain resultTm resultTy where
    process_result: "process_binop_chain ?is_flex loc ghost newLhs lhsTy ?opList = Inr (resultTm, resultTy)"
    and result_eq: "newTm = resultTm" "ty = resultTy"
    by (auto simp: Let_def split: sum.splits)
  \<comment> \<open>Binop forwards elab_term_list's next_mv\<close>
  from "6.prems"(1) elab_lhs elab_rhs_list process_result have next_mv_eq: "next_mv' = next_mv2"
    by (auto simp: Let_def split: sum.splits)
  have mono_1: "next_mv \<le> next_mv1"
    using elab_term_next_mv_monotone[OF elab_lhs] .
  have mono_2: "next_mv1 \<le> next_mv2"
    using elab_term_list_next_mv_monotone[OF elab_rhs_list] .
  have wf': "tyenv_well_formed ?env'"
    using "6.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast
  \<comment> \<open>IH on LHS: newLhs has type lhsTy in the extended env\<close>
  have lhs_typing_sub: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv1) ghost newLhs = Some lhsTy"
    using "6.IH"(1)[OF elab_lhs "6.prems"(2,3,4)] .
  have lhs_typing: "core_term_type ?env' ghost newLhs = Some lhsTy"
    using core_term_type_extend_env_with_tyvars_mono[OF lhs_typing_sub, where lo'=next_mv and hi'=next_mv']
          mono_1 mono_2 next_mv_eq by simp
  \<comment> \<open>Freshness carries forward through the lhs sub-call\<close>
  have fresh_1: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n next_mv1"
    using "6.prems"(4) mono_1 tyvar_fresh_ok_mono by fastforce
  \<comment> \<open>IH on RHS list: each rhsTm has its corresponding type in the extended env\<close>
  have rhs_typing_sub: "list_all2 (\<lambda>tm ty. core_term_type
                                      (extend_env_with_tyvars env ghost next_mv1 next_mv2) ghost tm = Some ty)
                                    rhsTms rhsTys"
    using "6.IH"(2) "6.prems"(2,3) elab_lhs elab_rhs_list fresh_1 by simp
  have rhs_typing: "list_all2 (\<lambda>tm ty. core_term_type ?env' ghost tm = Some ty) rhsTms rhsTys"
  proof -
    have "\<And>tm ty. core_term_type (extend_env_with_tyvars env ghost next_mv1 next_mv2) ghost tm = Some ty \<Longrightarrow>
                  core_term_type ?env' ghost tm = Some ty"
      using core_term_type_extend_env_with_tyvars_mono mono_1 mono_2 next_mv_eq by blast
    thus ?thesis using rhs_typing_sub by (auto elim!: list_all2_mono)
  qed
  \<comment> \<open>Convert list_all2 on rhsTms/rhsTys to list_all on opList\<close>
  have rhs_len: "length rhsTms = length rhsTys"
    using rhs_typing by (auto dest: list_all2_lengthD)
  have ops_typed: "list_all (\<lambda>(op, tm, ty). core_term_type ?env' ghost tm = Some ty) ?opList"
  proof (unfold list_all_iff, intro ballI, clarify)
    fix op tm tyR
    assume in_set: "(op, tm, tyR) \<in> set ?opList"
    from in_set obtain tmTy where
      tmTy_in: "(op, tmTy) \<in> set (zip (map fst operands) (zip rhsTms rhsTys))" and
      tmTy_eq: "tm = fst tmTy" "tyR = snd tmTy"
      by auto
    from tmTy_in have "tmTy \<in> set (zip rhsTms rhsTys)"
      using set_zip_rightD by metis
    then obtain i where i_bound: "i < length rhsTms" and "i < length rhsTys"
      and tm_eq: "tm = rhsTms ! i" and ty_eq: "tyR = rhsTys ! i"
      using tmTy_eq rhs_len by (auto simp: set_zip in_set_conv_nth)
    thus "core_term_type ?env' ghost tm = Some tyR"
      using rhs_typing by (auto dest: list_all2_nthD)
  qed
  \<comment> \<open>Locals and return type of ?env' come from env (unchanged by the
      extension) and are well-kinded in env, so their type variables lie in
      TE_TypeVars env. The Binop case's is_flex is (\<lambda>n. n |\<notin>| TE_TypeVars env),
      so none of those type variables are flex. \<close>
  have env'_locals_rigid:
    "\<forall>name ty' n. fmlookup (TE_LocalVars ?env') name = Some ty'
                    \<longrightarrow> n \<in> type_tyvars ty' \<longrightarrow> \<not> ?is_flex n"
  proof (intro allI impI)
    fix name ty' n
    assume lk: "fmlookup (TE_LocalVars ?env') name = Some ty'"
    assume n_mv: "n \<in> type_tyvars ty'"
    have "TE_LocalVars ?env' = TE_LocalVars env"
      unfolding extend_env_with_tyvars_def by simp
    with lk have lk_env: "fmlookup (TE_LocalVars env) name = Some ty'" by simp
    from "6.prems"(2) have "tyenv_vars_well_kinded env"
      unfolding tyenv_well_formed_def by simp
    with lk_env have "is_well_kinded env ty'"
      unfolding tyenv_vars_well_kinded_def by blast
    from is_well_kinded_type_tyvars_subset[OF this] n_mv
    have "n \<in> fset (TE_TypeVars env)" by blast
    thus "\<not> ?is_flex n" by simp
  qed
  have env'_ret_rigid: "\<forall>n. n \<in> type_tyvars (TE_ReturnType ?env') \<longrightarrow> \<not> ?is_flex n"
  proof (intro allI impI)
    fix n assume n_mv: "n \<in> type_tyvars (TE_ReturnType ?env')"
    have "TE_ReturnType ?env' = TE_ReturnType env"
      unfolding extend_env_with_tyvars_def by simp
    with n_mv have n_mv': "n \<in> type_tyvars (TE_ReturnType env)" by simp
    from "6.prems"(2) have "tyenv_return_type_well_kinded env"
      unfolding tyenv_well_formed_def by simp
    hence "is_well_kinded env (TE_ReturnType env)"
      unfolding tyenv_return_type_well_kinded_def .
    from is_well_kinded_type_tyvars_subset[OF this] n_mv'
    have "n \<in> fset (TE_TypeVars env)" by blast
    thus "\<not> ?is_flex n" by simp
  qed
  have env'_abs_rigid: "\<forall>n. n |\<in>| TE_AbstractTypes ?env' \<longrightarrow> \<not> ?is_flex n"
  proof (intro allI impI)
    fix n assume n_abs: "n |\<in>| TE_AbstractTypes ?env'"
    have "TE_AbstractTypes ?env' = TE_AbstractTypes env"
      unfolding extend_env_with_tyvars_def by simp
    with n_abs have "n |\<in>| TE_AbstractTypes env" by simp
    with "6.prems"(2) have "n |\<in>| TE_TypeVars env"
      unfolding tyenv_well_formed_def tyenv_abstract_types_subset_def by blast
    thus "\<not> ?is_flex n" by simp
  qed

  \<comment> \<open>Apply process_binop_chain_correct\<close>
  have "core_term_type ?env' ghost resultTm = Some resultTy"
    using process_binop_chain_correct
            [OF process_result lhs_typing ops_typed wf' env'_locals_rigid env'_ret_rigid env'_abs_rigid] .
  thus ?case using result_eq by simp

next
  \<comment> \<open>Case: BabTm_Let\<close>
  case (7 env elabEnv ghost loc varName rhs body next_mv)
  let ?env_ext = "extend_env_with_tyvars env ghost next_mv next_mv'"

  \<comment> \<open>Extract rhs elaboration and the resolved-type check\<close>
  from "7.prems"(1) obtain rhsTm rhsTy next_mv1 where
    elab_rhs: "elab_term env elabEnv ghost rhs next_mv = Inr (rhsTm, rhsTy, next_mv1)"
    by (auto split: sum.splits)
  from "7.prems"(1) elab_rhs have rhs_resolved:
    "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)"
    by (auto split: if_splits)

  \<comment> \<open>Build the let-body env (as used in both elab_term and core_term_type)\<close>
  let ?body_env = "env \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars env),
                         TE_GhostLocals := (if ghost = Ghost
                                             then finsert varName (TE_GhostLocals env)
                                             else fminus (TE_GhostLocals env) {|varName|}),
                         TE_ConstLocals := finsert varName (TE_ConstLocals env) \<rparr>"

  from "7.prems"(1) elab_rhs rhs_resolved obtain bodyTm bodyTy next_mv2 where
    elab_body: "elab_term ?body_env elabEnv ghost body next_mv1 = Inr (bodyTm, bodyTy, next_mv2)" and
    result_eq: "newTm = CoreTm_Let varName rhsTm bodyTm" "ty = bodyTy"
    by (auto simp: Let_def split: sum.splits)

  \<comment> \<open>Let forwards body's next_mv\<close>
  from "7.prems"(1) elab_rhs rhs_resolved elab_body have next_mv_eq: "next_mv' = next_mv2"
    by (auto simp: Let_def split: sum.splits)

  \<comment> \<open>Monotonicity\<close>
  have mono_1: "next_mv \<le> next_mv1"
    using elab_term_next_mv_monotone[OF elab_rhs] .
  have mono_2: "next_mv1 \<le> next_mv2"
    using elab_term_next_mv_monotone[OF elab_body] .

  \<comment> \<open>IH on rhs: rhsTm has type rhsTy in extend_env_with_tyvars env ghost next_mv next_mv1\<close>
  have rhs_typing_sub: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv1) ghost rhsTm = Some rhsTy"
    using "7.IH"(1)[OF elab_rhs "7.prems"(2,3,4)] .
  \<comment> \<open>Lift to ?env_ext\<close>
  have rhs_typing: "core_term_type ?env_ext ghost rhsTm = Some rhsTy"
    using core_term_type_extend_env_with_tyvars_mono[OF rhs_typing_sub, where lo'=next_mv and hi'=next_mv']
          mono_1 mono_2 next_mv_eq by simp

  \<comment> \<open>Well-kindedness of rhsTy in env: follows directly from rhs_resolved via is_well_kinded_transfer.\<close>
  have rhs_wk_env: "is_well_kinded env rhsTy"
  proof -
    have wf_sub: "tyenv_well_formed (extend_env_with_tyvars env ghost next_mv next_mv1)"
      using "7.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast
    have rhs_wk_sub: "is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv1) rhsTy"
      using core_term_type_well_kinded[OF "7.IH"(1)[OF elab_rhs "7.prems"(2,3,4)] wf_sub] .
    have tyvars_in_env: "type_tyvars rhsTy \<subseteq> fset (TE_TypeVars env)"
      using rhs_resolved
      by (auto simp: set_type_tyvars_list[symmetric] list_all_iff fset_of_list_elem)
    show ?thesis
      using is_well_kinded_transfer[OF rhs_wk_sub tyvars_in_env]
      by (simp add: extend_env_with_tyvars_def)
  qed

  \<comment> \<open>In non-ghost context, rhsTy is also runtime in env.
     rhs_resolved pins rhsTy's type variables into env.TE_TypeVars, and freshness (prems(4))
     says those are all strictly below next_mv, so they're disjoint from the fresh
     range [next_mv..<next_mv1]. Hence any type variable in rhsTy that's runtime in the
     sub-extended env is also runtime in the original env.\<close>
  have rhs_rt_env: "ghost = NotGhost \<longrightarrow> is_runtime_type env rhsTy"
  proof
    assume ng: "ghost = NotGhost"
    have wf_sub: "tyenv_well_formed (extend_env_with_tyvars env ghost next_mv next_mv1)"
      using "7.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast
    have rhs_rt_sub: "is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv1) rhsTy"
      using core_term_type_notghost_runtime ng rhs_typing_sub wf_sub by auto
    \<comment> \<open>Every type variable in rhsTy is in env.TE_TypeVars (from rhs_resolved)\<close>
    have tyvars_in_env_tv: "\<forall>n \<in> type_tyvars rhsTy. n |\<in>| TE_TypeVars env"
      using rhs_resolved by (auto simp: set_type_tyvars_list[symmetric] list_all_iff)
    \<comment> \<open>And every such type variable is fresh-ok at next_mv (by freshness)\<close>
    have tyvars_fresh: "\<forall>n \<in> type_tyvars rhsTy. tyvar_fresh_ok n next_mv"
      using tyvars_in_env_tv "7.prems"(4) by blast
    \<comment> \<open>In the sub-extended env, TE_RuntimeTypeVars = env.TE_RuntimeTypeVars \<union> mv_fset next_mv next_mv1.
       Combined with tyvars_fresh, any type variable in rhsTy that's runtime in the sub-extended env
       is also in env.TE_RuntimeTypeVars (it cannot lie in the fresh interval).\<close>
    have tyvars_in_env_rtv: "type_tyvars rhsTy \<subseteq> fset (TE_RuntimeTypeVars env)"
    proof
      fix n assume n_in: "n \<in> type_tyvars rhsTy"
      \<comment> \<open>From rhs_rt_sub we know n is in the sub-extended env's RT set\<close>
      have rhs_tyvars_rt: "type_tyvars rhsTy \<subseteq>
                          fset (TE_RuntimeTypeVars (extend_env_with_tyvars env ghost next_mv next_mv1))"
        using is_runtime_type_tyvars_subset[OF rhs_rt_sub] .
      from rhs_tyvars_rt n_in
      have "n |\<in>| TE_RuntimeTypeVars (extend_env_with_tyvars env ghost next_mv next_mv1)"
        by auto
      hence n_in_ext_rtv: "n |\<in>| TE_RuntimeTypeVars env |\<union>| mv_fset next_mv next_mv1"
        using ng unfolding extend_env_with_tyvars_def by simp
      from tyvars_fresh n_in have "tyvar_fresh_ok n next_mv" by blast
      hence "n |\<notin>| mv_fset next_mv next_mv1" by (rule tyvar_fresh_ok_notin_mv_fset)
      with n_in_ext_rtv have "n |\<in>| TE_RuntimeTypeVars env" by blast
      thus "n \<in> fset (TE_RuntimeTypeVars env)" by simp
    qed
    show "is_runtime_type env rhsTy"
      using is_runtime_type_transfer[OF rhs_rt_sub tyvars_in_env_rtv]
      unfolding extend_env_with_tyvars_def by simp
  qed

  have wf_body_env: "tyenv_well_formed ?body_env"
  proof (cases "ghost = Ghost")
    case True
    thus ?thesis
      using "7.prems"(2) rhs_wk_env tyenv_well_formed_add_ghost_var
      by (simp add: tyenv_well_formed_TE_ConstLocals_irrelevant)
  next
    case False
    hence ng: "ghost = NotGhost" by (cases ghost) simp_all
    with rhs_rt_env have rhs_rt: "is_runtime_type env rhsTy" by simp
    have wf_no_cn: "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars env),
                                              TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|} \<rparr>)"
      using tyenv_well_formed_add_var[OF "7.prems"(2) rhs_wk_env rhs_rt] .
    have env_rewrite: "?body_env =
      (env \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars env),
              TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|} \<rparr>)
      \<lparr> TE_ConstLocals := finsert varName (TE_ConstLocals env) \<rparr>"
      using ng by simp
    show ?thesis
      using wf_no_cn tyenv_well_formed_TE_ConstLocals_irrelevant env_rewrite by simp
  qed

  have td_wf_body: "elabenv_well_formed ?body_env elabEnv"
    using "7.prems"(3) elabenv_well_formed_cong_env[where env' = ?body_env and env = env]
    by simp

  \<comment> \<open>Freshness carries through to next_mv1; ?body_env has same TE_TypeVars as env\<close>
  have fresh_body: "\<forall>n. n |\<in>| TE_TypeVars ?body_env \<longrightarrow> tyvar_fresh_ok n next_mv1"
    using "7.prems"(4) mono_1 tyvar_fresh_ok_mono by fastforce

  \<comment> \<open>IH on body: bodyTm has type bodyTy in extend_env_with_tyvars ?body_env ghost next_mv1 next_mv2\<close>
  have body_typing_sub: "core_term_type (extend_env_with_tyvars ?body_env ghost next_mv1 next_mv2) ghost bodyTm = Some bodyTy"
    using "7.IH"(2) elab_body elab_rhs rhs_resolved td_wf_body wf_body_env fresh_body by simp

  \<comment> \<open>Show extend_env_with_tyvars ?body_env ghost next_mv1 next_mv2 equals the Let-extended ?env_ext\<close>
  let ?core_body_env = "?env_ext \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars ?env_ext),
                                    TE_GhostLocals := (if ghost = Ghost
                                                        then finsert varName (TE_GhostLocals ?env_ext)
                                                        else fminus (TE_GhostLocals ?env_ext) {|varName|}),
                                    TE_ConstLocals := finsert varName (TE_ConstLocals ?env_ext) \<rparr>"

  have env_widen_body: "core_term_type (extend_env_with_tyvars ?body_env ghost next_mv next_mv') ghost bodyTm = Some bodyTy"
    using core_term_type_extend_env_with_tyvars_mono[OF body_typing_sub,
              where lo'=next_mv and hi'=next_mv']
          mono_1 mono_2 next_mv_eq by simp

  have env_eq: "extend_env_with_tyvars ?body_env ghost next_mv next_mv' = ?core_body_env"
    unfolding extend_env_with_tyvars_def by simp

  have body_typing: "core_term_type ?core_body_env ghost bodyTm = Some bodyTy"
    using env_widen_body env_eq by simp

  \<comment> \<open>Final: core_term_type of CoreTm_Let unfolds to the check on rhs and body in ?core_body_env\<close>
  show ?case
    using result_eq rhs_typing body_typing
    by (simp add: Let_def)
next
  \<comment> \<open>Case: BabTm_Quantifier\<close>
  case (8 env elabEnv ghost loc quant name varTy tm next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  let ?is_flex = "(\<lambda>n. n |\<notin>| TE_TypeVars env)"

  \<comment> \<open>Ghost only\<close>
  from "8.prems"(1) have ghost_eq: "ghost = Ghost"
    by (auto split: if_splits)

  \<comment> \<open>Elaborate the type annotation\<close>
  from "8.prems"(1) ghost_eq obtain coreVarTy where
    elab_ty: "elab_type env elabEnv ghost varTy = Inr coreVarTy"
    by (auto split: sum.splits)

  \<comment> \<open>Body env\<close>
  let ?body_env = "env \<lparr> TE_LocalVars := fmupd name coreVarTy (TE_LocalVars env),
                         TE_GhostLocals := finsert name (TE_GhostLocals env) \<rparr>"

  \<comment> \<open>Elaborate the body\<close>
  from "8.prems"(1) ghost_eq elab_ty obtain bodyTm bodyTy next_mv_body where
    elab_body: "elab_term ?body_env elabEnv ghost tm next_mv = Inr (bodyTm, bodyTy, next_mv_body)"
    by (auto simp: Let_def split: sum.splits option.splits)

  \<comment> \<open>Unify body type with Bool\<close>
  from "8.prems"(1) ghost_eq elab_ty elab_body obtain bodySubst where
    body_unify: "unify ?is_flex bodyTy CoreTy_Bool = Some bodySubst"
    by (auto simp: Let_def split: sum.splits option.splits)

  \<comment> \<open>Extract the final results\<close>
  define finalBody where "finalBody = apply_subst_to_term bodySubst bodyTm"
  define finalVarTy where "finalVarTy = apply_subst bodySubst coreVarTy"

  from "8.prems"(1) ghost_eq elab_ty elab_body body_unify have
    newTm_eq: "newTm = CoreTm_Quantifier quant name finalVarTy finalBody" and
    ty_eq: "ty = CoreTy_Bool" and
    next_mv_eq: "next_mv' = next_mv_body"
    by (auto simp: Let_def finalBody_def finalVarTy_def)

  \<comment> \<open>varTy is well-kinded in env\<close>
  have td_wf: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using "8.prems"(3) unfolding elabenv_well_formed_def by simp
  have varTy_wk: "is_well_kinded env coreVarTy"
    using elab_ty "8.prems"(2) td_wf elab_type_is_well_kinded by simp

  \<comment> \<open>body_env is well-formed\<close>
  have wf_body_env: "tyenv_well_formed ?body_env"
    using tyenv_well_formed_add_ghost_var[OF "8.prems"(2) varTy_wk] .

  \<comment> \<open>elabenv is well-formed w.r.t. body_env\<close>
  have td_wf_body: "elabenv_well_formed ?body_env elabEnv"
    using "8.prems"(3) elabenv_well_formed_cong_env[where env' = ?body_env and env = env]
    by simp

  \<comment> \<open>Freshness for the body call\<close>
  have fresh_body: "\<forall>n. n |\<in>| TE_TypeVars ?body_env \<longrightarrow> tyvar_fresh_ok n next_mv"
    using "8.prems"(4) by simp

  \<comment> \<open>IH on body\<close>
  have ih_body_sub: "core_term_type (extend_env_with_tyvars ?body_env ghost next_mv next_mv_body) ghost bodyTm = Some bodyTy"
    using "8.IH" ghost_eq elab_ty elab_body wf_body_env td_wf_body fresh_body
    by (simp add: Let_def)

  \<comment> \<open>Widen to outer env — next_mv_body = next_mv' so this is trivial\<close>
  have ih_body: "core_term_type (extend_env_with_tyvars ?body_env ghost next_mv next_mv') ghost bodyTm = Some bodyTy"
    using ih_body_sub next_mv_eq by simp

  \<comment> \<open>The extended env for the body in core terms\<close>
  let ?env'_body = "?env' \<lparr> TE_LocalVars := fmupd name coreVarTy (TE_LocalVars ?env'),
                            TE_GhostLocals := finsert name (TE_GhostLocals ?env') \<rparr>"

  have env_eq: "extend_env_with_tyvars ?body_env ghost next_mv next_mv' = ?env'_body"
    unfolding extend_env_with_tyvars_def by simp

  have ih_body': "core_term_type ?env'_body ghost bodyTm = Some bodyTy"
    using ih_body env_eq by simp

  \<comment> \<open>?env' and ?env'_body are well-formed\<close>
  have wf': "tyenv_well_formed ?env'"
    using "8.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast

  have varTy_wk': "is_well_kinded ?env' coreVarTy"
    using varTy_wk is_well_kinded_cong_env[of ?env' env]
    by (metis extend_env_with_tyvars_empty is_well_kinded_extend_env_with_tyvars_mono
        nat_le_linear)

  have wf_body': "tyenv_well_formed ?env'_body"
    using tyenv_well_formed_add_ghost_var[OF wf' varTy_wk'] .

  \<comment> \<open>bodySubst properties\<close>
  have bodySubst_dom_flex: "\<forall>n. n |\<in>| fmdom bodySubst \<longrightarrow> ?is_flex n"
    using unify_unify_list_dom_flex(1)[OF body_unify] .

  have body_wk: "is_well_kinded ?env'_body bodyTy"
    using core_term_type_well_kinded[OF ih_body' wf_body'] .
  have bool_wk: "is_well_kinded ?env'_body CoreTy_Bool" by simp

  have bodySubst_wk: "\<forall>ty' \<in> fmran' bodySubst. is_well_kinded ?env'_body ty'"
    using unify_preserves_well_kinded[OF body_unify body_wk bool_wk] .

  \<comment> \<open>Since ghost = Ghost, runtime conditions are vacuous\<close>
  have bodySubst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' bodySubst. is_runtime_type ?env'_body ty')"
    using ghost_eq by simp

  \<comment> \<open>Generic helper: subst with flex domain is identity on types whose tyvars are in TE_TypeVars env\<close>
  have unif_id_on_env:
    "\<And>s ty'. \<forall>n. n |\<in>| fmdom (s :: (string, CoreType) fmap) \<longrightarrow> ?is_flex n
              \<Longrightarrow> type_tyvars ty' \<subseteq> fset (TE_TypeVars env)
              \<Longrightarrow> apply_subst s ty' = ty'"
  proof -
    fix s :: "(string, CoreType) fmap" and ty'
    assume dom_flex: "\<forall>n. n |\<in>| fmdom s \<longrightarrow> ?is_flex n"
    assume mvs: "type_tyvars ty' \<subseteq> fset (TE_TypeVars env)"
    have "type_tyvars ty' \<inter> fset (fmdom s) = {}"
      using mvs dom_flex by auto
    thus "apply_subst s ty' = ty'" by (rule apply_subst_disjoint_id)
  qed

  \<comment> \<open>Locals in ?env'_body: subst doesn't affect them (their tyvars are in TE_TypeVars env)\<close>
  have bodySubst_locals: "\<And>vname vty. fmlookup (TE_LocalVars ?env'_body) vname = Some vty
                                     \<Longrightarrow> apply_subst bodySubst vty = vty"
  proof -
    fix vname vty
    assume lk: "fmlookup (TE_LocalVars ?env'_body) vname = Some vty"
    have lv_eq: "TE_LocalVars ?env'_body = fmupd name coreVarTy (TE_LocalVars ?env')"
      by simp
    have lv_env_eq: "TE_LocalVars ?env' = TE_LocalVars env"
      unfolding extend_env_with_tyvars_def by simp
    from "8.prems"(2) have vwk: "tyenv_vars_well_kinded env"
      unfolding tyenv_well_formed_def by simp
    show "apply_subst bodySubst vty = vty"
    proof (cases "vname = name")
      case True
      with lk lv_eq have "vty = coreVarTy" by simp
      have "type_tyvars coreVarTy \<subseteq> fset (TE_TypeVars env)"
        using is_well_kinded_type_tyvars_subset[OF varTy_wk] .
      thus ?thesis using \<open>vty = coreVarTy\<close> unif_id_on_env[OF bodySubst_dom_flex] by simp
    next
      case False
      with lk lv_eq lv_env_eq have lk_env: "fmlookup (TE_LocalVars env) vname = Some vty"
        by simp
      from vwk lk_env have "is_well_kinded env vty"
        unfolding tyenv_vars_well_kinded_def by blast
      from is_well_kinded_type_tyvars_subset[OF this]
      have "type_tyvars vty \<subseteq> fset (TE_TypeVars env)" .
      thus ?thesis using unif_id_on_env[OF bodySubst_dom_flex] by simp
    qed
  qed

  have bodySubst_ret: "apply_subst bodySubst (TE_ReturnType ?env'_body) = TE_ReturnType ?env'_body"
  proof -
    have ret_eq: "TE_ReturnType ?env'_body = TE_ReturnType env"
      unfolding extend_env_with_tyvars_def by simp
    from "8.prems"(2) have "tyenv_return_type_well_kinded env"
      unfolding tyenv_well_formed_def by simp
    hence "is_well_kinded env (TE_ReturnType env)"
      unfolding tyenv_return_type_well_kinded_def .
    have "type_tyvars (TE_ReturnType env) \<subseteq> fset (TE_TypeVars env)"
      by (simp add: \<open>is_well_kinded env (TE_ReturnType env)\<close>
          is_well_kinded_type_tyvars_subset)
    thus ?thesis using ret_eq unif_id_on_env[OF bodySubst_dom_flex] by simp
  qed

  have env'_body_abs: "TE_AbstractTypes ?env'_body = TE_AbstractTypes env"
    unfolding extend_env_with_tyvars_def by simp
  have bodySubst_abs: "\<And>n. n |\<in>| TE_AbstractTypes ?env'_body \<Longrightarrow> fmlookup bodySubst n = None"
    using flex_subst_abs_no_subst[OF bodySubst_dom_flex[rule_format] "8.prems"(2) env'_body_abs] .
  have bodySubst_cp: "\<forall>ty' \<in> fmran' bodySubst. is_complete_type ty'"
    using unify_bool_range_complete[OF body_unify] .

  \<comment> \<open>Body substitution preserves typing\<close>
  have finalBody_typed: "core_term_type ?env'_body ghost finalBody = Some CoreTy_Bool"
  proof -
    have "core_term_type ?env'_body ghost (apply_subst_to_term bodySubst bodyTm)
            = Some (apply_subst bodySubst bodyTy)"
      using apply_subst_to_term_preserves_typing
              [OF ih_body' wf_body' bodySubst_wk bodySubst_rt bodySubst_locals bodySubst_ret
                  bodySubst_abs bodySubst_cp] .
    also have "apply_subst bodySubst bodyTy = apply_subst bodySubst CoreTy_Bool"
      using unify_sound[OF body_unify] .
    also have "apply_subst bodySubst CoreTy_Bool = CoreTy_Bool" by simp
    finally show ?thesis unfolding finalBody_def .
  qed

  \<comment> \<open>bodySubst is identity on coreVarTy (its tyvars are in TE_TypeVars env)\<close>
  have varTy_unchanged: "finalVarTy = coreVarTy"
    unfolding finalVarTy_def
    using unif_id_on_env[OF bodySubst_dom_flex is_well_kinded_type_tyvars_subset[OF varTy_wk]] .

  have finalVarTy_wk: "is_well_kinded ?env' finalVarTy"
    using varTy_unchanged varTy_wk' by simp

  show ?case
    using newTm_eq ty_eq ghost_eq finalVarTy_wk finalBody_typed varTy_unchanged
    by (simp add: Let_def)

next
  \<comment> \<open>Case: BabTm_Call (function call or data constructor call)\<close>
  case (9 env elabEnv ghost loc callee args next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  \<comment> \<open>Extract resolve_callee result\<close>
  from "9.prems"(1) obtain calleeName expArgTypes calleeInfo next_mv1 where
    resolve_eq: "resolve_callee env elabEnv ghost callee next_mv
                 = Inr (calleeName, expArgTypes, calleeInfo, next_mv1)"
    by (auto simp: build_call_result_def Let_def split: sum.splits CalleeInfo.splits prod.splits)
  from "9.prems"(1) resolve_eq have len_args: "length args = length expArgTypes"
    by (auto simp: build_call_result_def Let_def split: if_splits sum.splits CalleeInfo.splits prod.splits)
  from "9.prems"(1) resolve_eq len_args obtain elabArgTms actualTypes next_mv2 where
    elab_args: "elab_term_list env elabEnv ghost args next_mv1 = Inr (elabArgTms, actualTypes, next_mv2)"
    by (auto simp: build_call_result_def Let_def split: sum.splits CalleeInfo.splits prod.splits)
  from "9.prems"(1) resolve_eq len_args elab_args have next_mv_eq: "next_mv' = next_mv2"
    by (auto simp: build_call_result_def Let_def unify_and_coerce_def
             split: sum.splits CalleeInfo.splits prod.splits)

  \<comment> \<open>Monotonicity from resolve_callee\<close>
  have mono_1: "next_mv \<le> next_mv1"
    using resolve_callee_correct[OF resolve_eq "9.prems"(2,3)] by simp

  \<comment> \<open>Freshness carries through resolve_callee\<close>
  have fresh_1: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n next_mv1"
    using "9.prems"(4) mono_1 tyvar_fresh_ok_mono by fastforce
  \<comment> \<open>From IH on elab_term_list: elaborated args have their types in a sub-extended env\<close>
  have ih_args_sub: "list_all2 (\<lambda>tm ty. core_term_type
                                  (extend_env_with_tyvars env ghost next_mv1 next_mv2) ghost tm = Some ty)
                               elabArgTms actualTypes"
    using "9.IH" "9.prems"(2,3) resolve_eq elab_args len_args fresh_1
    by (auto simp: resolve_callee_def build_call_result_def Let_def
             split: sum.splits BabTerm.splits option.splits CalleeInfo.splits prod.splits)
  have mono_2: "next_mv1 \<le> next_mv2"
    using elab_term_list_next_mv_monotone[OF elab_args] .
  \<comment> \<open>Lift ih_args_sub to the outer extended env\<close>
  have ih_args: "list_all2 (\<lambda>tm ty. core_term_type ?env' ghost tm = Some ty)
                           elabArgTms actualTypes"
  proof -
    have "\<And>tm ty. core_term_type (extend_env_with_tyvars env ghost next_mv1 next_mv2) ghost tm = Some ty \<Longrightarrow>
                  core_term_type ?env' ghost tm = Some ty"
      using core_term_type_extend_env_with_tyvars_mono[where lo=next_mv1 and hi=next_mv2
                                                        and lo'=next_mv and hi'=next_mv']
            mono_1 mono_2 next_mv_eq by simp
    thus ?thesis using ih_args_sub by (auto elim!: list_all2_mono)
  qed

  (* Use the helper lemma to complete the proof *)
  show ?case
    using elab_term_correct_call[OF "9.prems"(1,2,3,4) resolve_eq elab_args ih_args] .

next
  \<comment> \<open>Case: BabTm_Tuple\<close>
  case (10 env elabEnv ghost loc tms next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  let ?names = "tuple_field_names (length tms)"
  \<comment> \<open>Extract elaboration results\<close>
  from "10.prems"(1) obtain newTms tys where
    elab_list: "elab_term_list env elabEnv ghost tms next_mv
                = Inr (newTms, tys, next_mv')" and
    newTm_eq: "newTm = CoreTm_Record (zip ?names newTms)" and
    ty_eq: "ty = CoreTy_Record (zip ?names tys)"
    by (auto simp: Let_def split: sum.splits)

  \<comment> \<open>IH on the element list\<close>
  have ih: "list_all2 (\<lambda>tm ty. core_term_type ?env' ghost tm = Some ty) newTms tys"
    using "10.IH"[OF elab_list "10.prems"(2,3,4)] .

  have len_eq: "length newTms = length tys"
    using ih by (simp add: list_all2_lengthD)
  have len_list: "length newTms = length tms"
    using elab_term_list_length[OF elab_list] by simp
  have len_tys: "length tys = length tms"
    using len_eq len_list by simp
  have len_names: "length ?names = length tms" by simp

  \<comment> \<open>Each field of zip names newTms typechecks to the matching type\<close>
  have each_field: "\<And>i. i < length tms \<Longrightarrow>
        core_term_type ?env' ghost (snd ((zip ?names newTms) ! i)) = Some (tys ! i)"
  proof -
    fix i assume i_lt: "i < length tms"
    have snd_eq: "snd ((zip ?names newTms) ! i) = newTms ! i"
      using i_lt len_list len_names by simp
    from ih have "core_term_type ?env' ghost (newTms ! i) = Some (tys ! i)"
      using i_lt len_list len_tys
      by (simp add: list_all2_conv_all_nth)
    with snd_eq show "core_term_type ?env' ghost (snd ((zip ?names newTms) ! i)) = Some (tys ! i)"
      by simp
  qed

  \<comment> \<open>those succeeds on the zipped list\<close>
  have those_ok: "those (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) (zip ?names newTms))
                  = Some tys"
  proof -
    have len_zip: "length (zip ?names newTms) = length tms"
      using len_list len_names by simp
    have la2: "list_all2 (\<lambda>x y. x = Some y)
                 (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) (zip ?names newTms)) tys"
      unfolding list_all2_conv_all_nth
    proof (intro conjI allI impI)
      show "length (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) (zip ?names newTms))
            = length tys"
        using len_zip len_tys by simp
    next
      fix i assume i_lt: "i < length (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) (zip ?names newTms))"
      from i_lt len_zip have i_tms: "i < length tms" by simp
      obtain n t where nt_eq: "(zip ?names newTms) ! i = (n, t)" by (cases "(zip ?names newTms) ! i")
      from nt_eq have snd_eq: "snd ((zip ?names newTms) ! i) = t" by simp
      from each_field[OF i_tms] snd_eq have t_ty: "core_term_type ?env' ghost t = Some (tys ! i)"
        by simp
      from nt_eq t_ty i_lt len_zip
      show "map (\<lambda>(name, tm). core_term_type ?env' ghost tm) (zip ?names newTms) ! i
            = Some (tys ! i)"
        by simp
    qed
    thus ?thesis by (simp add: those_eq_Some)
  qed

  \<comment> \<open>Distinctness: tuple_field_names is distinct, and equals map fst (zip ...) when lengths match\<close>
  have fst_zip_eq: "map fst (zip ?names newTms) = ?names"
    using len_list len_names by simp
  have distinct_zipped: "distinct (map fst (zip ?names newTms))"
    using fst_zip_eq distinct_tuple_field_names by simp

  show ?case
    using newTm_eq ty_eq those_ok distinct_zipped fst_zip_eq
    by simp
next
  \<comment> \<open>Case: BabTm_Record\<close>
  case (11 env elabEnv ghost loc flds next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  let ?names = "map fst flds"
  \<comment> \<open>Extract elaboration results\<close>
  from "11.prems"(1) have no_dup: "first_duplicate_name fst flds = None"
    by (auto split: option.splits)
  hence distinct_names: "distinct ?names"
    by (rule first_duplicate_name_None_implies_distinct)
  from "11.prems"(1) no_dup obtain newTms tys where
    elab_list: "elab_term_list env elabEnv ghost (map snd flds) next_mv
                = Inr (newTms, tys, next_mv')" and
    newTm_eq: "newTm = CoreTm_Record (zip ?names newTms)" and
    ty_eq: "ty = CoreTy_Record (zip ?names tys)"
    by (auto simp: Let_def split: sum.splits)

  \<comment> \<open>IH on the field term list\<close>
  have ih: "list_all2 (\<lambda>tm ty. core_term_type ?env' ghost tm = Some ty) newTms tys"
    using "11.IH"[OF no_dup elab_list "11.prems"(2,3,4)] .

  \<comment> \<open>Fields line up with tys after zipping\<close>
  have len_eq: "length newTms = length tys"
    using ih by (simp add: list_all2_lengthD)
  have len_names: "length ?names = length flds" by simp
  have len_list: "length newTms = length flds"
    using elab_term_list_length[OF elab_list] by simp
  have len_tys: "length tys = length flds"
    using len_eq len_list by simp

  \<comment> \<open>Each field of zip names newTms typechecks to the matching type\<close>
  have each_field: "\<And>i. i < length flds \<Longrightarrow>
        core_term_type ?env' ghost (snd ((zip ?names newTms) ! i)) = Some (tys ! i)"
  proof -
    fix i assume i_lt: "i < length flds"
    have snd_eq: "snd ((zip ?names newTms) ! i) = newTms ! i"
      using i_lt len_list by (simp add: len_names)
    from ih have "core_term_type ?env' ghost (newTms ! i) = Some (tys ! i)"
      using i_lt len_list len_tys
      by (simp add: list_all2_conv_all_nth)
    with snd_eq show "core_term_type ?env' ghost (snd ((zip ?names newTms) ! i)) = Some (tys ! i)"
      by simp
  qed

  \<comment> \<open>Hence `those` succeeds, via list_all2 + those_eq_Some\<close>
  have those_ok: "those (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) (zip ?names newTms))
                  = Some tys"
  proof -
    have len_zip: "length (zip ?names newTms) = length flds"
      using len_list len_names by simp
    have la2: "list_all2 (\<lambda>x y. x = Some y)
                 (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) (zip ?names newTms)) tys"
      unfolding list_all2_conv_all_nth
    proof (intro conjI allI impI)
      show "length (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) (zip ?names newTms))
            = length tys"
        using len_zip len_tys by simp
    next
      fix i assume i_lt: "i < length (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) (zip ?names newTms))"
      from i_lt len_zip have i_flds: "i < length flds" by simp
      obtain n t where nt_eq: "(zip ?names newTms) ! i = (n, t)" by (cases "(zip ?names newTms) ! i")
      from nt_eq have snd_eq: "snd ((zip ?names newTms) ! i) = t" by simp
      from each_field[OF i_flds] snd_eq have t_ty: "core_term_type ?env' ghost t = Some (tys ! i)"
        by simp
      from nt_eq t_ty i_lt len_zip
      show "map (\<lambda>(name, tm). core_term_type ?env' ghost tm) (zip ?names newTms) ! i
            = Some (tys ! i)"
        by simp
    qed
    thus ?thesis by (simp add: those_eq_Some)
  qed

  \<comment> \<open>Distinctness of the zipped names\<close>
  have distinct_zipped: "distinct (map fst (zip ?names newTms))"
    using distinct_names len_list len_names by simp

  \<comment> \<open>Zipped name list equals the original names, so the resulting record type matches\<close>
  have fst_zip_eq: "map fst (zip ?names newTms) = ?names"
    using len_list len_names by simp

  \<comment> \<open>Put it all together\<close>
  show ?case
    using newTm_eq ty_eq those_ok distinct_zipped fst_zip_eq
    by simp

next
  \<comment> \<open>Case: BabTm_RecordUpdate — delegate to helper lemma\<close>
  case (12 env elabEnv ghost loc tm flds next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"

  \<comment> \<open>Extract sub-elaboration results needed for IH setup\<close>
  from "12.prems"(1) have no_dup: "first_duplicate_name fst flds = None"
    by (auto split: option.splits)
  from "12.prems"(1) no_dup obtain parentTm parentTy next_mv1 where
    elab_parent: "elab_term env elabEnv ghost tm next_mv = Inr (parentTm, parentTy, next_mv1)"
    by (auto split: sum.splits)
  from "12.prems"(1) no_dup elab_parent obtain parentFields where
    parent_rec: "parentTy = CoreTy_Record parentFields"
    by (auto simp: Let_def unify_and_coerce_def build_updated_record_def
             split: sum.splits CoreType.splits option.splits if_splits prod.splits)
  from "12.prems"(1) no_dup elab_parent parent_rec have
    fields_exist: "check_update_fields_exist flds parentFields = None"
    by (auto simp: Let_def unify_and_coerce_def build_updated_record_def
             split: sum.splits option.splits if_splits prod.splits)
  from "12.prems"(1) no_dup elab_parent parent_rec fields_exist
  obtain newUpdateTms actualTypes next_mv2 where
    elab_updates: "elab_term_list env elabEnv ghost (map snd flds) next_mv1
                   = Inr (newUpdateTms, actualTypes, next_mv2)"
    by (auto simp: Let_def unify_and_coerce_def build_updated_record_def
             split: sum.splits option.splits if_splits prod.splits)
  from "12.prems"(1) no_dup elab_parent parent_rec fields_exist elab_updates
  have next_mv_eq: "next_mv' = next_mv2"
    by (auto simp: Let_def unify_and_coerce_def build_updated_record_def
             split: sum.splits option.splits if_splits prod.splits)

  \<comment> \<open>Monotonicity\<close>
  have mono_1: "next_mv \<le> next_mv1"
    using "12.IH"(1)[OF no_dup] elab_parent elab_term_next_mv_monotone by simp
  have pair1: "(parentTm, parentTy, next_mv1) = (parentTm, parentTy, next_mv1)" by simp
  have pair2: "(parentTy, next_mv1) = (parentTy, next_mv1)" by simp
  have mono_2: "next_mv1 \<le> next_mv2"
    using "12.IH"(2)[OF no_dup elab_parent pair1 pair2 parent_rec fields_exist] elab_updates
      elab_term_list_next_mv_monotone by simp

  \<comment> \<open>IH on parent, lifted to ?env'\<close>
  have ih_parent_sub: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv1) ghost parentTm
                       = Some parentTy"
    using "12.IH"(1)[OF no_dup elab_parent] "12.prems"(2,3,4) by simp
  have ih_parent: "core_term_type ?env' ghost parentTm = Some parentTy"
    using core_term_type_extend_env_with_tyvars_mono[OF ih_parent_sub, where lo'=next_mv and hi'=next_mv']
          mono_1 mono_2 next_mv_eq by simp

  \<comment> \<open>IH on update terms, lifted to ?env'\<close>
  have fresh_1: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n next_mv1"
    using "12.prems"(4) mono_1 tyvar_fresh_ok_mono by fastforce
  have ih_updates_sub: "list_all2 (\<lambda>tm ty. core_term_type
                          (extend_env_with_tyvars env ghost next_mv1 next_mv2) ghost tm = Some ty)
                        newUpdateTms actualTypes"
    using "12.IH"(2)[OF no_dup elab_parent pair1 pair2 parent_rec fields_exist elab_updates]
          "12.prems"(2,3) fresh_1 by simp
  have ih_updates: "list_all2 (\<lambda>tm ty. core_term_type ?env' ghost tm = Some ty)
                    newUpdateTms actualTypes"
  proof -
    have "\<And>tm ty. core_term_type (extend_env_with_tyvars env ghost next_mv1 next_mv2) ghost tm = Some ty \<Longrightarrow>
                  core_term_type ?env' ghost tm = Some ty"
      using core_term_type_extend_env_with_tyvars_mono[where lo=next_mv1 and hi=next_mv2
                                                        and lo'=next_mv and hi'=next_mv']
            mono_1 mono_2 next_mv_eq by simp
    thus ?thesis using ih_updates_sub by (auto elim!: list_all2_mono)
  qed

  show ?case
    using elab_term_correct_record_update[OF "12.prems"(1,2) "12.prems"(4)
            elab_parent elab_updates ih_parent ih_updates] .

next
  \<comment> \<open>Case: BabTm_TupleProj\<close>
  case (13 env elabEnv ghost loc tm idx next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  \<comment> \<open>Extract elaboration results\<close>
  from "13.prems"(1) obtain newSubTm subTy next_mv_sub where
    elab_sub: "elab_term env elabEnv ghost tm next_mv = Inr (newSubTm, subTy, next_mv_sub)"
    by (auto split: sum.splits)
  from "13.prems"(1) elab_sub obtain fieldTypes where
    sub_ty_eq: "subTy = CoreTy_Record fieldTypes"
    by (auto simp del: nat_to_string.simps split: CoreType.splits option.splits)
  from "13.prems"(1) elab_sub sub_ty_eq obtain fldTy where
    fld_lookup: "map_of fieldTypes (nat_to_string idx) = Some fldTy" and
    newTm_eq: "newTm = CoreTm_RecordProj newSubTm (nat_to_string idx)" and
    ty_eq: "ty = fldTy" and
    next_mv_eq: "next_mv' = next_mv_sub"
    by (auto simp del: nat_to_string.simps split: option.splits)

  \<comment> \<open>IH on the sub-term\<close>
  have ih: "core_term_type ?env' ghost newSubTm = Some (CoreTy_Record fieldTypes)"
    using "13.IH" elab_sub sub_ty_eq next_mv_eq "13.prems"(2,3,4)
    by (simp del: nat_to_string.simps)

  \<comment> \<open>Put it together\<close>
  show ?case
    using newTm_eq ty_eq ih fld_lookup by (simp del: nat_to_string.simps)
next
  \<comment> \<open>Case: BabTm_RecordProj\<close>
  case (14 env elabEnv ghost loc tm fldName next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  \<comment> \<open>Extract elaboration results\<close>
  from "14.prems"(1) obtain newSubTm subTy next_mv_sub where
    elab_sub: "elab_term env elabEnv ghost tm next_mv = Inr (newSubTm, subTy, next_mv_sub)"
    by (auto split: sum.splits)
  from "14.prems"(1) elab_sub obtain fieldTypes where
    sub_ty_eq: "subTy = CoreTy_Record fieldTypes"
    by (auto split: CoreType.splits option.splits)
  from "14.prems"(1) elab_sub sub_ty_eq obtain fldTy where
    fld_lookup: "map_of fieldTypes fldName = Some fldTy" and
    newTm_eq: "newTm = CoreTm_RecordProj newSubTm fldName" and
    ty_eq: "ty = fldTy" and
    next_mv_eq: "next_mv' = next_mv_sub"
    by (auto split: option.splits)

  \<comment> \<open>IH on the sub-term\<close>
  have ih: "core_term_type ?env' ghost newSubTm = Some (CoreTy_Record fieldTypes)"
    using "14.IH" elab_sub sub_ty_eq next_mv_eq "14.prems"(2,3,4) by simp

  \<comment> \<open>Put it together\<close>
  show ?case
    using newTm_eq ty_eq ih fld_lookup by simp
next
  \<comment> \<open>Case: BabTm_ArrayProj — delegate to helper lemma\<close>
  case (15 env elabEnv ghost loc tm idxs next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"

  \<comment> \<open>Extract sub-elaboration results\<close>
  from "15.prems"(1) obtain newArr arrTy next_mv1 where
    elab_arr: "elab_term env elabEnv ghost tm next_mv = Inr (newArr, arrTy, next_mv1)"
    by (auto split: sum.splits)
  from "15.prems"(1) elab_arr obtain elemTy dims where
    arr_ty: "arrTy = CoreTy_Array elemTy dims"
    by (auto simp: unify_and_coerce_def split: sum.splits CoreType.splits if_splits)
  from "15.prems"(1) elab_arr arr_ty have len_eq: "length idxs = length dims"
    by (auto simp: unify_and_coerce_def split: sum.splits if_splits)
  hence len_neq_false: "\<not> (length idxs \<noteq> length dims)" by simp
  from "15.prems"(1) elab_arr arr_ty len_eq
  obtain elabIdxTms actualTypes next_mv2 where
    elab_idxs: "elab_term_list env elabEnv ghost idxs next_mv1
                = Inr (elabIdxTms, actualTypes, next_mv2)"
    by (auto simp: unify_and_coerce_def split: sum.splits)
  from "15.prems"(1) elab_arr arr_ty len_eq elab_idxs
  have next_mv_eq: "next_mv' = next_mv2"
    by (auto simp: unify_and_coerce_def split: sum.splits)

  \<comment> \<open>Pair decomposition facts for IH application\<close>
  have pair1: "(newArr, arrTy, next_mv1) = (newArr, arrTy, next_mv1)" by simp
  have pair2: "(arrTy, next_mv1) = (arrTy, next_mv1)" by simp

  \<comment> \<open>Monotonicity\<close>
  have mono_1: "next_mv \<le> next_mv1"
    using "15.IH"(1) elab_arr elab_term_next_mv_monotone by simp
  have mono_2: "next_mv1 \<le> next_mv2"
    using "15.IH"(2)[OF elab_arr pair1 pair2 arr_ty len_neq_false] elab_idxs
      elab_term_list_next_mv_monotone by simp

  \<comment> \<open>IH on array term, lifted to ?env'\<close>
  have ih_arr_sub: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv1) ghost newArr
                    = Some arrTy"
    using "15.IH"(1) elab_arr "15.prems"(2,3,4) by simp
  have ih_arr: "core_term_type ?env' ghost newArr = Some arrTy"
    using core_term_type_extend_env_with_tyvars_mono[OF ih_arr_sub, where lo'=next_mv and hi'=next_mv']
          mono_1 mono_2 next_mv_eq by simp

  \<comment> \<open>IH on index terms, lifted to ?env'\<close>
  have fresh_1: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n next_mv1"
    using "15.prems"(4) mono_1 tyvar_fresh_ok_mono by fastforce
  have ih_idxs_sub: "list_all2 (\<lambda>tm ty. core_term_type
                       (extend_env_with_tyvars env ghost next_mv1 next_mv2) ghost tm = Some ty)
                     elabIdxTms actualTypes"
    using "15.IH"(2)[OF elab_arr pair1 pair2 arr_ty len_neq_false elab_idxs]
          "15.prems"(2,3) fresh_1 by simp
  have ih_idxs: "list_all2 (\<lambda>tm ty. core_term_type ?env' ghost tm = Some ty)
                 elabIdxTms actualTypes"
  proof -
    have "\<And>tm ty. core_term_type (extend_env_with_tyvars env ghost next_mv1 next_mv2) ghost tm = Some ty \<Longrightarrow>
                  core_term_type ?env' ghost tm = Some ty"
      using core_term_type_extend_env_with_tyvars_mono[where lo=next_mv1 and hi=next_mv2
                                                        and lo'=next_mv and hi'=next_mv']
            mono_1 mono_2 next_mv_eq by simp
    thus ?thesis using ih_idxs_sub by (auto elim!: list_all2_mono)
  qed

  show ?case
    using elab_term_correct_array_proj[OF "15.prems"(1,2) "15.prems"(4)
            elab_arr elab_idxs ih_arr ih_idxs] .
next
  \<comment> \<open>Case: BabTm_Match. Chains: scrutinee IH; decorate_match_arms_correct;
      elab_term_list_with_envs_correct (mutual IH); coerce_match_arm_bodies_correct;
      finalize_match_term_correct. \<close>
  case (16 env elabEnv ghost loc scrut arms next_mv)
  let ?is_flex = "\<lambda>n. n |\<notin>| TE_TypeVars env"
  let ?locOf = "\<lambda>idx. bab_term_location (snd (arms ! idx))"
  let ?armEnv = "\<lambda>dp. extend_env_with_pattern_vars env (\<lambda>_. True) ghost [dp]"

  \<comment> \<open>Extract elab sub-results. \<close>
  from "16.prems"(1) have arms_ne: "arms \<noteq> []" by (auto split: if_splits)
  from "16.prems"(1) arms_ne obtain scrutTm scrutTy mv1 where
    elab_scrut: "elab_term env elabEnv ghost scrut next_mv = Inr (scrutTm, scrutTy, mv1)"
    by (auto split: sum.splits)
  from "16.prems"(1) arms_ne elab_scrut obtain decoratedRows where
    decorate_eq: "decorate_match_arms env elabEnv ghost scrutTy False arms
                  = Inr decoratedRows"
    by (auto simp: Let_def split: sum.splits)
  let ?dps = "map fst decoratedRows"
  let ?bodyJobs = "zip (map ?armEnv ?dps) (map snd arms)"
  from "16.prems"(1) arms_ne elab_scrut decorate_eq
  obtain bodyTms bodyTys mv2 where
    elab_bodies: "elab_term_list_with_envs ?bodyJobs elabEnv ghost mv1
                  = Inr (bodyTms, bodyTys, mv2)"
    by (auto simp: Let_def split: sum.splits)
  from "16.prems"(1) arms_ne elab_scrut decorate_eq elab_bodies
  obtain coercedBodies finalSubst where
    uc: "unify_and_coerce ?is_flex ?locOf bodyTms bodyTys
           (replicate (length bodyTms) (hd bodyTys)) fmempty
         = Inr (coercedBodies, finalSubst)"
    by (auto simp: Let_def split: sum.splits prod.splits)
  have final_term_eq:
    "finalize_match_term loc scrutTm ?dps coercedBodies
                         (apply_subst finalSubst (hd bodyTys)) mv2
     = Inr (newTm, ty, next_mv')"
    using "16.prems"(1) arms_ne elab_scrut decorate_eq elab_bodies uc
    by (auto simp: Let_def split: sum.splits)

  \<comment> \<open>Monotonicity facts. \<close>
  have mono_1: "next_mv \<le> mv1"
    using elab_term_next_mv_monotone[OF elab_scrut] .
  have mono_2: "mv1 \<le> mv2"
    using elab_term_list_with_envs_next_mv_monotone[OF elab_bodies] .

  \<comment> \<open>The "ambient" env: env extended with all fresh tyvars [next_mv ..< mv2+1)
      introduced before finalize_match_term runs. This is the same as the target
      env (after we know next_mv' = mv2+1). \<close>
  define envAmbient where
    "envAmbient = extend_env_with_tyvars env ghost next_mv (mv2 + 1)"
  have envAmbient_wf: "tyenv_well_formed envAmbient"
    unfolding envAmbient_def
    using "16.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast
  have ambient_locals_eq: "TE_LocalVars envAmbient = TE_LocalVars env"
    unfolding envAmbient_def extend_env_with_tyvars_def by simp
  have ambient_ret_eq: "TE_ReturnType envAmbient = TE_ReturnType env"
    unfolding envAmbient_def extend_env_with_tyvars_def by simp
  have ambient_abs_eq: "TE_AbstractTypes envAmbient = TE_AbstractTypes env"
    unfolding envAmbient_def extend_env_with_tyvars_def by simp
  have ambient_dc_eq: "TE_DataCtors envAmbient = TE_DataCtors env"
    unfolding envAmbient_def extend_env_with_tyvars_def by simp

  \<comment> \<open>Scrutinee IH: scrutTm well-typed under env extended by [next_mv, mv1);
      hence also under envAmbient. \<close>
  have scrut_typed_at_mv1:
    "core_term_type (extend_env_with_tyvars env ghost next_mv mv1) ghost scrutTm = Some scrutTy"
    using "16.IH"(1)[OF arms_ne elab_scrut "16.prems"(2,3,4)] .
  have scrut_typed_amb: "core_term_type envAmbient ghost scrutTm = Some scrutTy"
    using core_term_type_extend_env_with_tyvars_mono[OF scrut_typed_at_mv1
              order_refl, of "mv2 + 1"]
          mono_2
    unfolding envAmbient_def by simp
  have scrutTy_wk_mv1:
    "is_well_kinded (extend_env_with_tyvars env ghost next_mv mv1) scrutTy"
    using core_term_type_well_kinded[OF scrut_typed_at_mv1
              tyenv_well_formed_extend_env_with_tyvars[OF "16.prems"(2)]] .
  have scrutTy_rt_mv1: "ghost = NotGhost \<longrightarrow>
                          is_runtime_type (extend_env_with_tyvars env ghost next_mv mv1) scrutTy"
    using core_term_type_well_kinded_and_runtime[OF scrut_typed_at_mv1
              tyenv_well_formed_extend_env_with_tyvars[OF "16.prems"(2)]]
    by blast

  \<comment> \<open>Pattern decoration facts. The pattern-variable types contain no
      metavariables, so they are well-kinded / runtime in env itself. \<close>
  note dma = decorate_match_arms_correct[OF decorate_eq "16.prems"(2)
                                            scrutTy_wk_mv1 scrutTy_rt_mv1 "16.prems"(4)]
  have len_dps: "length ?dps = length arms"
    using dma(1) by simp
  have dps_ne: "?dps \<noteq> []"
    using arms_ne len_dps by (cases ?dps) auto
  have dps_compat_amb:
    "\<And>dp. dp \<in> set ?dps \<Longrightarrow> dec_pattern_compatible envAmbient dp scrutTy"
    using dma(3) dec_pattern_compatible_TE_DataCtors_cong[OF ambient_dc_eq] by simp
  have dps_bind_wk_amb:
    "\<And>dp. dp \<in> set ?dps \<Longrightarrow>
       list_all (\<lambda>(_, _, vTy). is_well_kinded envAmbient vTy) (dec_pattern_var_bindings dp)"
  proof -
    fix dp assume dp_in: "dp \<in> set ?dps"
    show "list_all (\<lambda>(_, _, vTy). is_well_kinded envAmbient vTy) (dec_pattern_var_bindings dp)"
      using dma(6)[OF dp_in]
      unfolding envAmbient_def
      by (auto simp: list_all_iff intro: is_well_kinded_extend_env_with_tyvars)
  qed
  have dps_bind_rt_amb:
    "\<And>dp. dp \<in> set ?dps \<Longrightarrow> ghost = NotGhost \<Longrightarrow>
       list_all (\<lambda>(_, _, vTy). is_runtime_type envAmbient vTy) (dec_pattern_var_bindings dp)"
  proof -
    fix dp assume dp_in: "dp \<in> set ?dps" and ng: "ghost = NotGhost"
    show "list_all (\<lambda>(_, _, vTy). is_runtime_type envAmbient vTy) (dec_pattern_var_bindings dp)"
      using dma(7)[OF dp_in ng]
      unfolding envAmbient_def
      by (auto simp: list_all_iff intro: is_runtime_type_extend_env_with_tyvars)
  qed

  \<comment> \<open>The per-arm envs satisfy the premises of the with-envs IH. \<close>
  have arm_env_wf: "\<And>dp. dp \<in> set ?dps \<Longrightarrow> tyenv_well_formed (?armEnv dp)"
  proof -
    fix dp assume dp_in: "dp \<in> set ?dps"
    have wk_list: "list_all (\<lambda>(_, _, ty). is_well_kinded env ty)
                            (dec_pattern_var_bindings_list [dp])"
      using dma(6)[OF dp_in] by simp
    have rt_list: "ghost = NotGhost \<Longrightarrow>
                     list_all (\<lambda>(_, _, ty). is_runtime_type env ty)
                              (dec_pattern_var_bindings_list [dp])"
      using dma(7)[OF dp_in] by simp
    show "tyenv_well_formed (?armEnv dp)"
      using tyenv_well_formed_extend_env_with_pattern_vars[OF "16.prems"(2) wk_list rt_list] .
  qed
  have arm_env_elab_wf: "\<And>dp. elabenv_well_formed (?armEnv dp) elabEnv"
    using elabenv_well_formed_extend_env_with_pattern_vars[OF "16.prems"(3)] .
  have arm_env_fresh:
    "\<And>dp. \<forall>n. n |\<in>| TE_TypeVars (?armEnv dp) \<longrightarrow> tyvar_fresh_ok n mv1"
    using "16.prems"(4) mono_1 tyvar_fresh_ok_mono by fastforce

  have len_jobs: "length ?bodyJobs = length arms"
    using len_dps by simp
  have job_at:
    "\<And>i. i < length arms \<Longrightarrow> ?bodyJobs ! i = (?armEnv (?dps ! i), snd (arms ! i))"
    using len_dps by simp

  have jobs_envs_wf:
    "list_all (\<lambda>(env_i, _). tyenv_well_formed env_i) ?bodyJobs"
    unfolding list_all_length
  proof (intro allI impI)
    fix i assume i_lt: "i < length ?bodyJobs"
    have i_lt_arms: "i < length arms" using i_lt len_jobs by simp
    have dp_in: "?dps ! i \<in> set ?dps" using i_lt_arms len_dps by (metis nth_mem)
    show "case ?bodyJobs ! i of (env_i, uu_) \<Rightarrow> tyenv_well_formed env_i"
      unfolding job_at[OF i_lt_arms] using arm_env_wf[OF dp_in] by simp
  qed
  have jobs_envs_elab_wf:
    "list_all (\<lambda>(env_i, _). elabenv_well_formed env_i elabEnv) ?bodyJobs"
    unfolding list_all_length
  proof (intro allI impI)
    fix i assume i_lt: "i < length ?bodyJobs"
    have i_lt_arms: "i < length arms" using i_lt len_jobs by simp
    show "case ?bodyJobs ! i of (env_i, uu_) \<Rightarrow> elabenv_well_formed env_i elabEnv"
      unfolding job_at[OF i_lt_arms] using arm_env_elab_wf by simp
  qed
  have jobs_envs_fresh:
    "list_all (\<lambda>(env_i, _). \<forall>n. n |\<in>| TE_TypeVars env_i \<longrightarrow> tyvar_fresh_ok n mv1) ?bodyJobs"
    unfolding list_all_length
  proof (intro allI impI)
    fix i assume i_lt: "i < length ?bodyJobs"
    have i_lt_arms: "i < length arms" using i_lt len_jobs by simp
    show "case ?bodyJobs ! i of (env_i, uu_) \<Rightarrow>
            \<forall>n. n |\<in>| TE_TypeVars env_i \<longrightarrow> tyvar_fresh_ok n mv1"
      unfolding job_at[OF i_lt_arms] using arm_env_fresh by simp
  qed

  \<comment> \<open>Apply 16.IH(2) (the list_with_envs leg of the mutual induction). \<close>
  have bodies_ih:
    "list_all2
       (\<lambda>(env_i, _) (tm', ty').
          core_term_type (extend_env_with_tyvars env_i ghost mv1 mv2) ghost tm' = Some ty')
       ?bodyJobs (zip bodyTms bodyTys)"
    using "16.IH"(2)[OF arms_ne elab_scrut refl refl decorate_eq refl refl elab_bodies
                       jobs_envs_wf jobs_envs_elab_wf jobs_envs_fresh] .

  \<comment> \<open>Lengths. \<close>
  have len_bodyTms: "length bodyTms = length arms"
   and len_bodyTys: "length bodyTys = length arms"
    using elab_term_list_with_envs_length[OF elab_bodies] len_jobs by simp_all
  have lengths_dps: "length ?dps = length bodyTms" "length ?dps = length bodyTys"
    using len_dps len_bodyTms len_bodyTys by simp_all

  \<comment> \<open>Widen each body's typing from its arm env extended by [mv1, mv2) to
      envAmbient extended with the arm's pattern variables. \<close>
  have bodies_typed:
    "\<And>i. i < length ?dps \<Longrightarrow>
       core_term_type (extend_env_with_pattern_vars envAmbient (\<lambda>_. True) ghost [?dps ! i])
                      ghost (bodyTms ! i)
       = Some (bodyTys ! i)"
  proof -
    fix i assume i_lt: "i < length ?dps"
    have i_lt_arms: "i < length arms" using i_lt len_dps by simp
    have i_lt_jobs: "i < length ?bodyJobs" using i_lt_arms len_jobs by simp
    have zip_at_i: "(zip bodyTms bodyTys) ! i = (bodyTms ! i, bodyTys ! i)"
      using i_lt_arms len_bodyTms len_bodyTys by simp

    \<comment> \<open>From bodies_ih at index i. \<close>
    from list_all2_nthD[OF bodies_ih i_lt_jobs]
    have ih_at_i:
      "core_term_type (extend_env_with_tyvars (?armEnv (?dps ! i)) ghost mv1 mv2) ghost
                      (bodyTms ! i) = Some (bodyTys ! i)"
      unfolding job_at[OF i_lt_arms] zip_at_i by simp

    \<comment> \<open>Widen from [mv1, mv2) to [next_mv, mv2+1). \<close>
    have hi_mono: "mv2 \<le> mv2 + 1" by simp
    have env_widen:
      "core_term_type (extend_env_with_tyvars (?armEnv (?dps ! i)) ghost next_mv (mv2 + 1))
                      ghost (bodyTms ! i) = Some (bodyTys ! i)"
      using core_term_type_extend_env_with_tyvars_mono[OF ih_at_i mono_1 hi_mono] .

    \<comment> \<open>The tyvar extension and the pattern-variable extension commute. \<close>
    have target_eq:
      "extend_env_with_pattern_vars envAmbient (\<lambda>_. True) ghost [?dps ! i]
       = extend_env_with_tyvars (?armEnv (?dps ! i)) ghost next_mv (mv2 + 1)"
      unfolding envAmbient_def
      using extend_env_with_tyvars_extend_env_with_pattern_vars_commute by metis

    show "core_term_type (extend_env_with_pattern_vars envAmbient (\<lambda>_. True) ghost [?dps ! i])
                         ghost (bodyTms ! i)
          = Some (bodyTys ! i)"
      using env_widen target_eq by simp
  qed

  \<comment> \<open>Convert every arm body to the first arm's body type. \<close>
  note coerced = coerce_match_arm_bodies_correct
                   [OF uc "16.prems"(2) envAmbient_wf
                       ambient_locals_eq ambient_ret_eq ambient_abs_eq
                       lengths_dps dps_ne
                       dps_bind_wk_amb dps_bind_rt_amb dma(5) bodies_typed]
  have len_coerced': "length coercedBodies = length ?dps"
    by (rule coerced(1))
  have len_coerced: "length ?dps = length coercedBodies"
    using len_coerced' by simp
  have coerced_typed:
    "\<And>i. i < length ?dps \<Longrightarrow>
       core_term_type (extend_env_with_pattern_vars envAmbient (\<lambda>_. True) ghost [?dps ! i])
                      ghost (coercedBodies ! i)
       = Some (apply_subst finalSubst (hd bodyTys))"
    by (rule coerced(2))

  \<comment> \<open>Apply finalize_match_term_correct. \<close>
  have ft_concl:
    "core_term_type envAmbient ghost newTm = Some (apply_subst finalSubst (hd bodyTys))
     \<and> ty = apply_subst finalSubst (hd bodyTys)
     \<and> next_mv' = mv2 + 1"
    by (rule finalize_match_term_correct[OF final_term_eq envAmbient_wf scrut_typed_amb
                                            len_coerced dps_compat_amb dma(4)
                                            coerced_typed dps_ne])

  show ?case
    using ft_concl
    unfolding envAmbient_def by simp
next
  \<comment> \<open>Case: BabTm_Sizeof\<close>
  case (17 env elabEnv ghost loc tm next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  \<comment> \<open>Extract elaboration results\<close>
  from "17.prems"(1) obtain newSubTm subTy next_mv_sub where
    elab_sub: "elab_term env elabEnv ghost tm next_mv = Inr (newSubTm, subTy, next_mv_sub)"
    by (auto split: sum.splits)
  from "17.prems"(1) elab_sub obtain elemTy dims where
    sub_ty_eq: "subTy = CoreTy_Array elemTy dims"
    by (auto split: CoreType.splits option.splits if_splits)
  from "17.prems"(1) elab_sub sub_ty_eq have
    guard: "\<not> (list_ex (\<lambda>d. d = CoreDim_Allocatable) dims \<and> \<not> is_lvalue newSubTm \<and> ghost = NotGhost)" and
    newTm_eq: "newTm = CoreTm_Sizeof newSubTm" and
    ty_eq: "ty = sizeof_type dims" and
    next_mv_eq: "next_mv' = next_mv_sub"
    by (auto split: if_splits)

  \<comment> \<open>IH on the sub-term\<close>
  have ih: "core_term_type ?env' ghost newSubTm = Some (CoreTy_Array elemTy dims)"
    using "17.IH" elab_sub sub_ty_eq next_mv_eq "17.prems"(2,3,4) by simp

  \<comment> \<open>Put it together\<close>
  show ?case
    using newTm_eq ty_eq ih guard by simp
next
  \<comment> \<open>Case: BabTm_Allocated\<close>
  case (18 env elabEnv ghost loc tm next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  from "18.prems"(1) have ghost_eq: "ghost = Ghost"
    by (auto split: if_splits)
  from "18.prems"(1) ghost_eq obtain newSubTm subTy next_mv_sub where
    elab_sub: "elab_term env elabEnv ghost tm next_mv = Inr (newSubTm, subTy, next_mv_sub)" and
    sub_cp: "is_complete_type subTy" and
    newTm_eq: "newTm = CoreTm_Allocated newSubTm" and
    ty_eq: "ty = CoreTy_Bool" and
    next_mv_eq: "next_mv' = next_mv_sub"
    by (auto split: sum.splits if_splits)
  have ih: "core_term_type ?env' ghost newSubTm = Some subTy"
    using "18.IH" ghost_eq elab_sub next_mv_eq "18.prems"(2,3,4) by simp
  show ?case
    using newTm_eq ty_eq ghost_eq ih sub_cp by simp
next
  \<comment> \<open>Case: BabTm_Old\<close>
  case (19 env elabEnv ghost loc tm next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  from "19.prems"(1) have ghost_eq: "ghost = Ghost"
    by (auto split: if_splits)
  from "19.prems"(1) ghost_eq obtain newSubTm subTy next_mv_sub where
    elab_sub: "elab_term env elabEnv ghost tm next_mv = Inr (newSubTm, subTy, next_mv_sub)" and
    newTm_eq: "newTm = CoreTm_Old newSubTm" and
    ty_eq: "ty = subTy" and
    next_mv_eq: "next_mv' = next_mv_sub"
    by (auto split: sum.splits)
  have ih: "core_term_type ?env' ghost newSubTm = Some subTy"
    using "19.IH" ghost_eq elab_sub next_mv_eq "19.prems"(2,3,4) by simp
  show ?case
    using newTm_eq ty_eq ghost_eq ih by simp
next
  \<comment> \<open>Case: elab_term_list empty\<close>
  case (20 env elabEnv ghost next_mv)
  from "20.prems"(1) have "newTms = []" and "tys = []" by simp_all
  thus ?case by simp
next
  \<comment> \<open>Case: elab_term_list cons\<close>
  case (21 env elabEnv ghost tm tms next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  from "21.prems"(1) obtain tm' ty' next_mv1 tms' tys' next_mv'' where
    elab_head: "elab_term env elabEnv ghost tm next_mv = Inr (tm', ty', next_mv1)" and
    elab_tail: "elab_term_list env elabEnv ghost tms next_mv1 = Inr (tms', tys', next_mv'')" and
    results: "newTms = tm' # tms'" "tys = ty' # tys'"
    by (auto split: sum.splits)
  \<comment> \<open>Cons forwards elab_term_list's next_mv, so next_mv' = next_mv''\<close>
  from "21.prems"(1) elab_head elab_tail results have next_mv_eq: "next_mv' = next_mv''"
    by (auto split: sum.splits)
  have mono_1: "next_mv \<le> next_mv1"
    using elab_term_next_mv_monotone[OF elab_head] .
  have mono_2: "next_mv1 \<le> next_mv''"
    using elab_term_list_next_mv_monotone[OF elab_tail] .
  \<comment> \<open>Freshness carries through the head sub-call\<close>
  have fresh_1: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n next_mv1"
    using "21.prems"(4) mono_1 tyvar_fresh_ok_mono by fastforce
  \<comment> \<open>IH for head, lifted to ?env'\<close>
  have ih_head_sub: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv1) ghost tm' = Some ty'"
    using "21.IH"(1) elab_head "21.prems"(2,3,4) by simp
  have ih_head: "core_term_type ?env' ghost tm' = Some ty'"
    using core_term_type_extend_env_with_tyvars_mono[OF ih_head_sub, where lo'=next_mv and hi'=next_mv']
          mono_1 mono_2 next_mv_eq by simp
  \<comment> \<open>IH for tail, lifted to ?env'\<close>
  have ih_tail_sub: "list_all2 (\<lambda>tm ty. core_term_type
                                  (extend_env_with_tyvars env ghost next_mv1 next_mv'') ghost tm = Some ty)
                               tms' tys'"
    using "21.IH"(3) elab_head elab_tail "21.prems"(2,3) fresh_1 by simp
  have ih_tail: "list_all2 (\<lambda>tm ty. core_term_type ?env' ghost tm = Some ty) tms' tys'"
  proof -
    have "\<And>tm ty. core_term_type (extend_env_with_tyvars env ghost next_mv1 next_mv'') ghost tm = Some ty \<Longrightarrow>
                  core_term_type ?env' ghost tm = Some ty"
      using core_term_type_extend_env_with_tyvars_mono[where lo=next_mv1 and hi=next_mv''
                                                        and lo'=next_mv and hi'=next_mv']
            mono_1 mono_2 next_mv_eq by simp
    thus ?thesis using ih_tail_sub by (auto elim!: list_all2_mono)
  qed
  show ?case using ih_head ih_tail results by simp
next
  \<comment> \<open>Case: elab_term_list_with_envs empty — empty list trivially satisfies the predicate.\<close>
  case ("22" elabEnv ghost next_mv)
  from "22.prems"(1) have "newTms = []" and "tys = []" by simp_all
  thus ?case by simp
next
  \<comment> \<open>Case: elab_term_list_with_envs cons — body of head elaborates under env_h;
      tail recurses with refreshed next_mv. \<close>
  case (23 env_h tm rest elabEnv ghost next_mv)
  from "23.prems"(1) obtain tm' ty' next_mv1 tms' tys' next_mv'' where
    elab_head: "elab_term env_h elabEnv ghost tm next_mv = Inr (tm', ty', next_mv1)" and
    elab_tail: "elab_term_list_with_envs rest elabEnv ghost next_mv1
                = Inr (tms', tys', next_mv'')" and
    results: "newTms = tm' # tms'" "tys = ty' # tys'"
    by (auto split: sum.splits)
  from "23.prems"(1) elab_head elab_tail results have next_mv_eq: "next_mv' = next_mv''"
    by (auto split: sum.splits)
  have mono_1: "next_mv \<le> next_mv1"
    using elab_term_next_mv_monotone[OF elab_head] .
  have mono_2: "next_mv1 \<le> next_mv''"
    using elab_term_list_with_envs_next_mv_monotone[OF elab_tail] .
  from "23.prems"(2) have wf_h: "tyenv_well_formed env_h" by simp
  from "23.prems"(3) have wf_elab_h: "elabenv_well_formed env_h elabEnv" by simp
  from "23.prems"(4) have fresh_h: "\<forall>n. n |\<in>| TE_TypeVars env_h \<longrightarrow> tyvar_fresh_ok n next_mv" by simp
  have ih_head_sub:
    "core_term_type (extend_env_with_tyvars env_h ghost next_mv next_mv1) ghost tm' = Some ty'"
    using "23.IH"(1) elab_head wf_h wf_elab_h fresh_h by simp
  have ih_head:
    "core_term_type (extend_env_with_tyvars env_h ghost next_mv next_mv') ghost tm' = Some ty'"
    using core_term_type_extend_env_with_tyvars_mono[OF ih_head_sub,
                                                       where lo'=next_mv and hi'=next_mv']
          mono_1 mono_2 next_mv_eq by simp
  from "23.prems"(2) have rest_wf: "list_all (\<lambda>(env_i, _). tyenv_well_formed env_i) rest" by simp
  from "23.prems"(3) have rest_wf_elab: "list_all (\<lambda>(env_i, _). elabenv_well_formed env_i elabEnv) rest"
    by simp
  from "23.prems"(4) have rest_fresh_at_next_mv:
    "list_all (\<lambda>(env_i, _). \<forall>n. n |\<in>| TE_TypeVars env_i \<longrightarrow> tyvar_fresh_ok n next_mv) rest"
    by simp
  have rest_fresh: "list_all (\<lambda>(env_i, _). \<forall>n. n |\<in>| TE_TypeVars env_i \<longrightarrow> tyvar_fresh_ok n next_mv1) rest"
    using rest_fresh_at_next_mv mono_1 tyvar_fresh_ok_mono
    by (induction rest) (auto split: prod.splits)
  have ih_tail_sub:
    "list_all2
       (\<lambda>(env_i, _) (tm'', ty'').
          core_term_type (extend_env_with_tyvars env_i ghost next_mv1 next_mv'') ghost tm''
          = Some ty'')
       rest (zip tms' tys')"
    using "23.IH"(3) elab_head elab_tail rest_wf rest_wf_elab rest_fresh by simp
  have ih_tail:
    "list_all2
       (\<lambda>(env_i, _) (tm'', ty'').
          core_term_type (extend_env_with_tyvars env_i ghost next_mv next_mv') ghost tm''
          = Some ty'')
       rest (zip tms' tys')"
  proof -
    have "\<And>env_i tm'' ty''.
            core_term_type (extend_env_with_tyvars env_i ghost next_mv1 next_mv'') ghost tm''
            = Some ty''
          \<Longrightarrow> core_term_type (extend_env_with_tyvars env_i ghost next_mv next_mv') ghost tm''
              = Some ty''"
      using core_term_type_extend_env_with_tyvars_mono[where lo=next_mv1 and hi=next_mv''
                                                        and lo'=next_mv and hi'=next_mv']
            mono_1 mono_2 next_mv_eq by simp
    thus ?thesis using ih_tail_sub
      by (auto elim!: list_all2_mono split: prod.splits)
  qed
  show ?case using ih_head ih_tail results by simp
qed


end
