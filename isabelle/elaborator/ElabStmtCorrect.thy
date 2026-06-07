theory ElabStmtCorrect
  imports ElabStmt ElabTermCorrect ElabTypeCorrect ElabPatternCorrect
    "../core/CoreStmtTypecheck"
begin

(* ========================================================================== *)
(* Lemmas about clear_metavars and clear_metavars_type *)
(* ========================================================================== *)

(* The statement elaborator applies clear_metavars next_mv next_mv' to each   *)
(* emitted initializer term, substituting the fresh-interval metavariables    *)
(* with CoreTy_Record []. The lemmas below show this makes the term typecheck *)
(* in the ORIGINAL env (no fresh-tyvar extension), which is what lets          *)
(* elab_statement_correct be stated over plain env.                           *)

(* The clearing substitution's domain is the interval, and its range is the
   single ground type CoreTy_Record []. *)
lemma clear_metavars_subst_dom:
  "fset (fmdom (fmap_of_list (map (\<lambda>n. (n, CoreTy_Record [])) [lo..<hi]))) = {lo..<hi}"
  by (simp add: fset_of_list.rep_eq)

lemma clear_metavars_subst_ran:
  "fmran' (fmap_of_list (map (\<lambda>n. (n, CoreTy_Record [])) [lo..<hi])) \<subseteq> {CoreTy_Record []}"
proof
  fix ty assume "ty \<in> fmran' (fmap_of_list (map (\<lambda>n. (n, CoreTy_Record [])) [lo..<hi]))"
  then obtain n where "fmlookup (fmap_of_list (map (\<lambda>n. (n, CoreTy_Record [])) [lo..<hi])) n = Some ty"
    by (auto simp: fmran'_def)
  hence "(n, ty) \<in> set (map (\<lambda>n. (n, CoreTy_Record [])) [lo..<hi])"
    by (rule fmap_of_list_SomeD)
  thus "ty \<in> {CoreTy_Record []}" by auto
qed

lemma clear_metavars_subst_range_tyvars:
  "subst_range_tyvars (fmap_of_list (map (\<lambda>n. (n, CoreTy_Record [])) [lo..<hi])) = {}"
  using clear_metavars_subst_ran[of lo hi]
  by (auto simp: subst_range_tyvars_def)

(* CoreTy_Record [] is well-kinded and a runtime type in any env. *)
lemma is_well_kinded_empty_record [simp]: "is_well_kinded env (CoreTy_Record [])"
  by simp
lemma is_runtime_type_empty_record [simp]: "is_runtime_type env (CoreTy_Record [])"
  by simp

(* The clearing substitution is identity on a type all of whose tyvars are below
   the interval start (in particular, on the env's stored local / return types,
   whose tyvars are < next_mv by the tyvar-bound premise). *)
lemma clear_metavars_subst_id_below:
  assumes "type_tyvars ty \<subseteq> {n. n < lo}"
  shows "apply_subst (fmap_of_list (map (\<lambda>n. (n, CoreTy_Record [])) [lo..<hi])) ty = ty"
proof (rule apply_subst_disjoint_id)
  have "type_tyvars ty \<inter> {lo..<hi} = {}" using assms by auto
  thus "type_tyvars ty \<inter> fset (fmdom (fmap_of_list (map (\<lambda>n. (n, CoreTy_Record [])) [lo..<hi]))) = {}"
    by (simp only: clear_metavars_subst_dom)
qed

(* Main bridge (general form): a term that typechecks (in a given ghost mode) under
   env extended with the fresh interval, once its interval metavariables are cleared,
   typechecks under the original env to the CLEARED type. Clearing removes the
   interval tyvars from the term, so the interval can be dropped via
   core_term_type_remove_unused_tyvars; the result type is whatever the cleared term
   produces, namely clear_metavars_type applied to the original result type. *)
lemma clear_metavars_typed_in_env_gen:
  assumes typed: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost coreTm
                    = Some ty"
    and wf: "tyenv_well_formed env"
    and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv"
  shows "core_term_type env ghost (clear_metavars next_mv next_mv' coreTm)
           = Some (clear_metavars_type next_mv next_mv' ty)"
proof -
  let ?envE = "extend_env_with_tyvars env ghost next_mv next_mv'"
  let ?subst = "fmap_of_list (map (\<lambda>n. (n, CoreTy_Record [])) [next_mv..<next_mv'])"
  have wfE: "tyenv_well_formed ?envE"
    using wf tyenv_well_formed_extend_env_with_tyvars by blast
  \<comment> \<open>The clearing subst's range is well-kinded and runtime in the extended env.\<close>
  have subst_wk: "\<forall>ty' \<in> fmran' ?subst. is_well_kinded ?envE ty'"
    using clear_metavars_subst_ran is_well_kinded_empty_record by blast
  have subst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' ?subst. is_runtime_type ?envE ty')"
    using clear_metavars_subst_ran is_runtime_type_empty_record by blast
  \<comment> \<open>The subst is identity on the extended env's locals and return type: their
     tyvars come from env (all < next_mv), outside the interval.\<close>
  have locals_below: "\<And>name ty'. fmlookup (TE_LocalVars ?envE) name = Some ty'
                                 \<Longrightarrow> type_tyvars ty' \<subseteq> {n. n < next_mv}"
  proof -
    fix name ty' assume "fmlookup (TE_LocalVars ?envE) name = Some ty'"
    hence look: "fmlookup (TE_LocalVars env) name = Some ty'"
      unfolding extend_env_with_tyvars_def by simp
    have "is_well_kinded env ty'"
      using wf look unfolding tyenv_well_formed_def tyenv_vars_well_kinded_def by blast
    hence "type_tyvars ty' \<subseteq> fset (TE_TypeVars env)"
      using is_well_kinded_type_tyvars_subset by simp
    thus "type_tyvars ty' \<subseteq> {n. n < next_mv}" using bound by auto
  qed
  have locals_unaffected: "\<And>name ty'. fmlookup (TE_LocalVars ?envE) name = Some ty'
                                      \<Longrightarrow> apply_subst ?subst ty' = ty'"
    using locals_below clear_metavars_subst_id_below by blast
  have ret_below: "type_tyvars (TE_ReturnType ?envE) \<subseteq> {n. n < next_mv}"
  proof -
    have "is_well_kinded env (TE_ReturnType env)"
      using wf unfolding tyenv_well_formed_def tyenv_return_type_well_kinded_def by blast
    hence "type_tyvars (TE_ReturnType env) \<subseteq> fset (TE_TypeVars env)"
      using is_well_kinded_type_tyvars_subset by simp
    thus ?thesis using bound unfolding extend_env_with_tyvars_def by auto
  qed
  have ret_unaffected: "apply_subst ?subst (TE_ReturnType ?envE) = TE_ReturnType ?envE"
    using clear_metavars_subst_id_below[OF ret_below] .
  \<comment> \<open>Cleared term typechecks (to apply_subst ?subst ty) under the extended env.\<close>
  have cleared_typedE: "core_term_type ?envE ghost (clear_metavars next_mv next_mv' coreTm)
                          = Some (clear_metavars_type next_mv next_mv' ty)"
    using apply_subst_to_term_preserves_typing
            [OF typed wfE subst_wk subst_rt locals_unaffected ret_unaffected]
    unfolding clear_metavars_def clear_metavars_type_def by simp
  \<comment> \<open>The cleared term has no interval tyvars, so the interval can be dropped.\<close>
  have free_gone: "core_term_free_tyvars (clear_metavars next_mv next_mv' coreTm) \<inter> {next_mv..<next_mv'} = {}"
  proof -
    have "core_term_free_tyvars (clear_metavars next_mv next_mv' coreTm)
            \<subseteq> core_term_free_tyvars coreTm - fset (fmdom ?subst)"
      using apply_subst_to_term_free_tyvars_ground[OF clear_metavars_subst_range_tyvars]
      unfolding clear_metavars_def by blast
    hence "core_term_free_tyvars (clear_metavars next_mv next_mv' coreTm)
            \<subseteq> core_term_free_tyvars coreTm - {next_mv..<next_mv'}"
      by (simp only: clear_metavars_subst_dom)
    thus ?thesis by auto
  qed
  have envE_shape: "?envE = env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list [next_mv..<next_mv'],
                                  TE_RuntimeTypeVars := TE_RuntimeTypeVars env
                                    |\<union>| (if ghost = NotGhost then fset_of_list [next_mv..<next_mv'] else {||}) \<rparr>"
    unfolding extend_env_with_tyvars_def by simp
  show ?thesis
    using core_term_type_remove_unused_tyvars[OF cleared_typedE[unfolded envE_shape] _ ]
          free_gone
    by (cases "ghost = NotGhost") (auto simp: fset_of_list.rep_eq)
qed

(* Corollary: when the result type is metavariable-free (its tyvars are < next_mv,
   hence outside the interval), clearing leaves it unchanged, so the cleared term
   typechecks to the SAME type in the original env. This is the form the pure /
   Ref / Assume VarDecl branches use. *)
lemma clear_metavars_typed_in_env:
  assumes typed: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost coreTm
                    = Some ty"
    and wf: "tyenv_well_formed env"
    and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv"
    and ty_below: "type_tyvars ty \<subseteq> {n. n < next_mv}"
  shows "core_term_type env ghost (clear_metavars next_mv next_mv' coreTm) = Some ty"
proof -
  have "clear_metavars_type next_mv next_mv' ty = ty"
    using clear_metavars_subst_id_below[OF ty_below] unfolding clear_metavars_type_def .
  thus ?thesis using clear_metavars_typed_in_env_gen[OF typed wf bound] by simp
qed


(* Clearing a type that is well-kinded in the fresh-tyvar-extended env yields a type
   well-kinded in the original env: the cleared interval metavariables become the
   ground type CoreTy_Record [] and every surviving tyvar is < next_mv, hence in
   TE_TypeVars env. (And likewise for runtime-ness, in NotGhost mode.) *)
lemma clear_metavars_type_well_kinded:
  assumes wk: "is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv') ty"
    and wf: "tyenv_well_formed env"
    and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv"
  shows "is_well_kinded env (clear_metavars_type next_mv next_mv' ty)"
proof -
  let ?envE = "extend_env_with_tyvars env ghost next_mv next_mv'"
  let ?subst = "fmap_of_list (map (\<lambda>n. (n, CoreTy_Record [])) [next_mv..<next_mv'])"
  show ?thesis
    unfolding clear_metavars_type_def
  proof (rule apply_subst_preserves_well_kinded[OF wk])
    show "TE_Datatypes env = TE_Datatypes ?envE" unfolding extend_env_with_tyvars_def by simp
  next
    fix n assume "n |\<in>| TE_TypeVars ?envE"
    hence n_in: "n |\<in>| TE_TypeVars env \<or> n \<in> {next_mv..<next_mv'}"
      unfolding extend_env_with_tyvars_def by (auto simp: fset_of_list.rep_eq)
    show "case fmlookup ?subst n of Some ty' \<Rightarrow> is_well_kinded env ty' | None \<Rightarrow> n |\<in>| TE_TypeVars env"
    proof (cases "fmlookup ?subst n")
      case None
      hence "n \<notin> {next_mv..<next_mv'}"
        by (metis clear_metavars_subst_dom fmdom_notI)
      thus ?thesis using None n_in by auto
    next
      case (Some ty')
      hence "ty' \<in> fmran' ?subst" by (auto simp: fmran'_def)
      with clear_metavars_subst_ran have "ty' = CoreTy_Record []" by blast
      thus ?thesis using Some by simp
    qed
  qed
qed

lemma clear_metavars_type_runtime:
  assumes rt: "is_runtime_type (extend_env_with_tyvars env NotGhost next_mv next_mv') ty"
    and wf: "tyenv_well_formed env"
    and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv"
    and rtbound: "\<forall>n. n |\<in>| TE_RuntimeTypeVars env \<longrightarrow> n < next_mv"
  shows "is_runtime_type env (clear_metavars_type next_mv next_mv' ty)"
proof -
  let ?envE = "extend_env_with_tyvars env NotGhost next_mv next_mv'"
  let ?subst = "fmap_of_list (map (\<lambda>n. (n, CoreTy_Record [])) [next_mv..<next_mv'])"
  show ?thesis
    unfolding clear_metavars_type_def
  proof (rule apply_subst_preserves_runtime[OF rt])
    show "TE_GhostDatatypes env = TE_GhostDatatypes ?envE" unfolding extend_env_with_tyvars_def by simp
  next
    fix n assume "n |\<in>| TE_RuntimeTypeVars ?envE"
    hence n_in: "n |\<in>| TE_RuntimeTypeVars env \<or> n \<in> {next_mv..<next_mv'}"
      unfolding extend_env_with_tyvars_def by (auto simp: fset_of_list.rep_eq)
    show "case fmlookup ?subst n of Some ty' \<Rightarrow> is_runtime_type env ty' | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars env"
    proof (cases "fmlookup ?subst n")
      case None
      hence "n \<notin> {next_mv..<next_mv'}"
        by (metis clear_metavars_subst_dom fmdom_notI)
      thus ?thesis using None n_in by auto
    next
      case (Some ty')
      hence "ty' \<in> fmran' ?subst" by (auto simp: fmran'_def)
      with clear_metavars_subst_ran have "ty' = CoreTy_Record []" by blast
      thus ?thesis using Some by simp
    qed
  qed
qed

(* is_writable_lvalue is unchanged by the fresh-tyvar extension (it ignores type
   variables); a corollary of is_writable_lvalue_irrelevant_tyvar. *)
lemma is_writable_lvalue_extend_env_with_tyvars [simp]:
  "is_writable_lvalue (extend_env_with_tyvars env ghost lo hi) tm = is_writable_lvalue env tm"
proof (cases ghost)
  case NotGhost
  thus ?thesis
    using is_writable_lvalue_irrelevant_tyvar
            [where env=env and extraTV="fset_of_list [lo..<hi]" and extraRT="fset_of_list [lo..<hi]"]
    by (simp add: extend_env_with_tyvars_def)
next
  case Ghost
  thus ?thesis
    using is_writable_lvalue_irrelevant_tyvar
            [where env=env and extraTV="fset_of_list [lo..<hi]" and extraRT="{||}"]
    by (simp add: extend_env_with_tyvars_def)
qed

(* Impure-call bridge: an impure call that typechecks (via core_impure_call_type)
   under env extended with the fresh interval, once its ty-args and arg-terms have
   their interval metavariables cleared, typechecks under the original env to the
   SAME return type (which is metavariable-free). This is the impure-call analog of
   clear_metavars_typed_in_env, and is what the VarDeclCall main sub-case needs. *)
lemma clear_metavars_impure_call_typed_in_env:
  assumes ct: "core_impure_call_type (extend_env_with_tyvars env ghost next_mv next_mv')
                 ghost fnName tyArgs argTms = Some retTy"
    and wf: "tyenv_well_formed env"
    and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv"
    and rtbound: "\<forall>n. n |\<in>| TE_RuntimeTypeVars env \<longrightarrow> n < next_mv"
    and ret_below: "type_tyvars retTy \<subseteq> {n. n < next_mv}"
  shows "core_impure_call_type env ghost fnName
           (map (clear_metavars_type next_mv next_mv') tyArgs)
           (map (clear_metavars next_mv next_mv') argTms) = Some retTy"
proof -
  let ?envE = "extend_env_with_tyvars env ghost next_mv next_mv'"
  let ?ct = "clear_metavars_type next_mv next_mv'"
  let ?ctm = "clear_metavars next_mv next_mv'"
  have wfE: "tyenv_well_formed ?envE" using wf tyenv_well_formed_extend_env_with_tyvars by blast
  from core_impure_call_type_fn_facts[OF ct] obtain funInfo where
    fiE: "fmlookup (TE_Functions ?envE) fnName = Some funInfo" and
    len_ty: "length tyArgs = length (FI_TyArgs funInfo)" and
    wk: "list_all (is_well_kinded ?envE) tyArgs" and
    rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?envE) tyArgs" and
    fn_ng: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost" and
    len_tm: "length argTms = length (FI_TmArgs funInfo)" and
    ty_eq: "retTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo)" and
    l2_pure: "list_all2 (\<lambda>tm expectedTy.
                  case core_term_type ?envE ghost tm of None \<Rightarrow> False
                  | Some actualTy \<Rightarrow> actualTy = expectedTy)
                argTms
                (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo))" and
    ref_lv: "\<forall>i < length argTms.
                snd (snd (FI_TmArgs funInfo ! i)) = Ref
                  \<longrightarrow> is_writable_lvalue ?envE (argTms ! i)"
    by blast
  have fi: "fmlookup (TE_Functions env) fnName = Some funInfo"
    using fiE unfolding extend_env_with_tyvars_def by simp

  \<comment> \<open>Signature facts for the substitution-composition step.\<close>
  have distinct_tyargs: "distinct (FI_TyArgs funInfo)"
    using wf fi unfolding tyenv_well_formed_def tyenv_fun_tyvars_distinct_def by blast
  have fi_args_wk: "\<forall>t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo).
            is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) t"
    using wf fi unfolding tyenv_well_formed_def tyenv_fun_types_well_kinded_def by blast
  have fi_ret_wk: "is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) (FI_ReturnType funInfo)"
    using wf fi unfolding tyenv_well_formed_def tyenv_fun_types_well_kinded_def by blast
  have fi_args_tyvars: "\<forall>t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo). type_tyvars t \<subseteq> set (FI_TyArgs funInfo)"
  proof
    fix t assume "t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)"
    with fi_args_wk have "is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) t" by blast
    from is_well_kinded_type_tyvars_subset[OF this]
    show "type_tyvars t \<subseteq> set (FI_TyArgs funInfo)" by (simp add: fset_of_list.rep_eq)
  qed
  have fi_ret_tyvars: "type_tyvars (FI_ReturnType funInfo) \<subseteq> set (FI_TyArgs funInfo)"
    using is_well_kinded_type_tyvars_subset[OF fi_ret_wk] by (simp add: fset_of_list.rep_eq)

  \<comment> \<open>Cleared ty-args are well-kinded / runtime in env.\<close>
  have len_cty: "length (map ?ct tyArgs) = length (FI_TyArgs funInfo)" using len_ty by simp
  have cty_wk: "list_all (is_well_kinded env) (map ?ct tyArgs)"
    using wk clear_metavars_type_well_kinded[OF _ wf bound] by (auto simp: list_all_iff)
  have cty_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) (map ?ct tyArgs)"
  proof
    assume ng: "ghost = NotGhost"
    have "list_all (is_runtime_type env) (map ?ct tyArgs)"
      using rt[rule_format, OF ng] clear_metavars_type_runtime[OF _ wf bound rtbound]
      by (auto simp: list_all_iff ng)
    thus "list_all (is_runtime_type env) (map ?ct tyArgs)" .
  qed

  \<comment> \<open>The return type is unchanged by clearing (metavar-free) and equals the
      recomputation from the cleared ty-args.\<close>
  have tysubst_eq: "fmap_of_list (zip (FI_TyArgs funInfo) (map ?ct tyArgs))
                      = fmap_of_list (zip (FI_TyArgs funInfo) (map (apply_subst
                          (fmap_of_list (map (\<lambda>n. (n, CoreTy_Record [])) [next_mv..<next_mv']))) tyArgs))"
    unfolding clear_metavars_type_def by simp
  let ?cs = "fmap_of_list (map (\<lambda>n. (n, CoreTy_Record [])) [next_mv..<next_mv'])"
  have ret_recompute:
    "apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) (map ?ct tyArgs))) (FI_ReturnType funInfo) = retTy"
  proof -
    have "apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) (map ?ct tyArgs))) (FI_ReturnType funInfo)
            = apply_subst ?cs (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo))"
      using apply_subst_compose_zip[OF len_ty[symmetric] fi_ret_tyvars distinct_tyargs]
      unfolding clear_metavars_type_def by simp
    also have "\<dots> = apply_subst ?cs retTy" using ty_eq by simp
    also have "\<dots> = retTy" using clear_metavars_subst_id_below[OF ret_below]
      unfolding clear_metavars_type_def by simp
    finally show ?thesis .
  qed

  \<comment> \<open>Per-argument check survives clearing: the cleared arg term typechecks in env to
      the cleared expected type, which is the recomputed expected type from cleared
      ty-args (substitution composition).\<close>
  let ?exps0 = "map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty) (FI_TmArgs funInfo)"
  let ?expsC = "map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) (map ?ct tyArgs))) ty) (FI_TmArgs funInfo)"
  have exps_recompute: "?expsC = map ?ct ?exps0"
  proof -
    have "?expsC = map (\<lambda>(_, ty, _). apply_subst ?cs
            (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)) (FI_TmArgs funInfo)"
    proof (rule map_cong[OF refl])
      fix x assume "x \<in> set (FI_TmArgs funInfo)"
      obtain n t v where x_eq: "x = (n, t, v)" by (cases x)
      with \<open>x \<in> set (FI_TmArgs funInfo)\<close> have "t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)"
        by (force simp: rev_image_eqI)
      with fi_args_tyvars have "type_tyvars t \<subseteq> set (FI_TyArgs funInfo)" by blast
      thus "(case x of (_, ty, _) \<Rightarrow> apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) (map ?ct tyArgs))) ty)
            = (case x of (_, ty, _) \<Rightarrow> apply_subst ?cs (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty))"
        using x_eq apply_subst_compose_zip[OF len_ty[symmetric] _ distinct_tyargs]
        unfolding clear_metavars_type_def by simp
    qed
    also have "\<dots> = map ?ct ?exps0"
      unfolding clear_metavars_type_def by (simp add: case_prod_unfold comp_def)
    finally show ?thesis .
  qed
  have len_pure: "length argTms = length ?exps0" using l2_pure by (simp add: list_all2_lengthD)
  have l2_clear: "list_all2 (\<lambda>tm expectedTy.
                    case core_term_type env ghost tm of None \<Rightarrow> False
                    | Some actualTy \<Rightarrow> actualTy = expectedTy)
                  (map ?ctm argTms) ?expsC"
    unfolding list_all2_conv_all_nth
  proof (intro conjI allI impI)
    show "length (map ?ctm argTms) = length ?expsC" using len_tm by simp
  next
    fix i assume i_lt: "i < length (map ?ctm argTms)"
    hence i_tm: "i < length argTms" by simp
    \<comment> \<open>The original arg types to its expected type in the extended env.\<close>
    have "case core_term_type ?envE ghost (argTms ! i) of None \<Rightarrow> False
          | Some actualTy \<Rightarrow> actualTy = ?exps0 ! i"
      using list_all2_nthD[OF l2_pure] i_tm len_pure by simp
    then obtain actualTy where
      tm_typed: "core_term_type ?envE ghost (argTms ! i) = Some actualTy" and
      aeq: "actualTy = ?exps0 ! i"
      by (auto split: option.splits)
    \<comment> \<open>Clearing the arg term types it (in env) to the cleared expected type.\<close>
    have "core_term_type env ghost (?ctm (argTms ! i)) = Some (?ct actualTy)"
      using clear_metavars_typed_in_env_gen[OF tm_typed wf bound] .
    moreover have "?ct (?exps0 ! i) = ?expsC ! i"
      using exps_recompute i_tm len_pure len_tm by simp
    ultimately show "case core_term_type env ghost (map ?ctm argTms ! i) of None \<Rightarrow> False
                     | Some actualTy' \<Rightarrow> actualTy' = ?expsC ! i"
      using i_tm aeq by simp
  qed

  \<comment> \<open>Ref positions stay writable lvalues under clearing.\<close>
  have ref_lv_clear: "\<forall>i < length (map ?ctm argTms).
                        snd (snd (FI_TmArgs funInfo ! i)) = Ref
                          \<longrightarrow> is_writable_lvalue env ((map ?ctm argTms) ! i)"
  proof (intro allI impI)
    fix i assume i_lt: "i < length (map ?ctm argTms)" and ref: "snd (snd (FI_TmArgs funInfo ! i)) = Ref"
    hence i_lt_tm: "i < length argTms" by simp
    have "is_writable_lvalue ?envE (argTms ! i)" using ref_lv i_lt_tm ref by simp
    hence "is_writable_lvalue env (argTms ! i)" by simp
    thus "is_writable_lvalue env ((map ?ctm argTms) ! i)"
      using i_lt_tm unfolding clear_metavars_def by simp
  qed

  \<comment> \<open>Reassemble core_impure_call_type from the cleared pieces, mirroring
      core_impure_call_type_irrelevant_tyvar's reconstruction.\<close>
  let ?P = "\<lambda>(tm, vor) expectedTy.
                 case vor of
                   Var \<Rightarrow> (case core_term_type env ghost tm of None \<Rightarrow> False
                            | Some actualTy \<Rightarrow> actualTy = expectedTy)
                 | Ref \<Rightarrow> is_writable_lvalue env tm \<and> core_term_type env ghost tm = Some expectedTy"
  let ?zts = "zip (map ?ctm argTms) (map (\<lambda>(_, _, vor). vor) (FI_TmArgs funInfo))"
  have len_zts: "length ?zts = length ?expsC" using len_tm by simp
  have nth_pred: "\<And>i. i < length ?zts \<Longrightarrow> ?P (?zts ! i) (?expsC ! i)"
  proof -
    fix i assume i_lt: "i < length ?zts"
    hence i_lt_tm: "i < length argTms" using len_tm by simp
    with len_tm have i_lt_fi: "i < length (FI_TmArgs funInfo)" by simp
    obtain n ti vor where fi_arg: "FI_TmArgs funInfo ! i = (n, ti, vor)"
      by (cases "FI_TmArgs funInfo ! i") auto
    have zip_nth: "?zts ! i = ((map ?ctm argTms) ! i, vor)"
      using i_lt_tm i_lt_fi fi_arg by simp
    have exp_nth: "?expsC ! i = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) (map ?ct tyArgs))) ti"
      using i_lt_fi fi_arg by simp
    have pure_i: "case core_term_type env ghost ((map ?ctm argTms) ! i) of None \<Rightarrow> False
                  | Some actualTy \<Rightarrow> actualTy = ?expsC ! i"
      using list_all2_nthD[OF l2_clear] i_lt_tm by simp
    show "?P (?zts ! i) (?expsC ! i)"
    proof (cases vor)
      case Var with zip_nth pure_i show ?thesis by simp
    next
      case Ref
      have "is_writable_lvalue env ((map ?ctm argTms) ! i)"
        using ref_lv_clear i_lt_tm fi_arg Ref by simp
      moreover from pure_i have
        "core_term_type env ghost ((map ?ctm argTms) ! i) = Some (?expsC ! i)"
        by (auto split: option.splits)
      ultimately show ?thesis using Ref zip_nth by simp
    qed
  qed
  have l2_full: "list_all2 ?P ?zts ?expsC"
    using len_zts nth_pred by (simp add: list_all2_conv_all_nth)

  show ?thesis
    unfolding core_impure_call_type_def
    using fi cty_wk cty_rt fn_ng len_cty len_tm l2_full ret_recompute
    by (auto simp: Let_def)
qed


(* ========================================================================== *)
(* Monotonicity of elab_impure_call *)
(* ========================================================================== *)

(* resolve_type_args only advances the counter (by the number of omitted args). *)
lemma resolve_type_args_next_mv:
  "resolve_type_args env elabEnv ghost loc name tyvars tyArgs next_mv = Inr (newTyArgs, next_mv')
     \<Longrightarrow> next_mv \<le> next_mv'"
  by (auto simp: resolve_type_args_def Let_def split: if_splits sum.splits)

(* resolve_impure_callee only advances the counter through resolve_type_args. *)
lemma resolve_impure_callee_next_mv:
  "resolve_impure_callee env elabEnv ghost callee next_mv
     = Inr (name, newTyArgs, expArgTypes, varOrRefs, retType0, next_mv')
     \<Longrightarrow> next_mv \<le> next_mv'"
  by (auto simp: resolve_impure_callee_def Let_def
           dest!: resolve_type_args_next_mv
           split: BabTerm.splits option.splits sum.splits prod.splits if_splits)

(* elab_impure_call_term advances the counter: resolve_impure_callee then
   elab_term_list (unify / validate_call_args do not allocate). *)
lemma elab_impure_call_term_next_mv:
  "elab_impure_call_term env elabEnv ghost loc callee args next_mv
     = Inr (fnName, tyArgs, argTms, retTy, next_mv')
     \<Longrightarrow> next_mv \<le> next_mv'"
proof -
  assume elab: "elab_impure_call_term env elabEnv ghost loc callee args next_mv
                  = Inr (fnName, tyArgs, argTms, retTy, next_mv')"
  from elab obtain name newTyArgs expArgTypes varOrRefs retType0 next_mv1 where
    rc: "resolve_impure_callee env elabEnv ghost callee next_mv
           = Inr (name, newTyArgs, expArgTypes, varOrRefs, retType0, next_mv1)"
    by (auto simp: elab_impure_call_term_def split: sum.splits prod.splits)
  from elab rc obtain elabArgTms actualTypes next_mv2 where
    el: "elab_term_list env elabEnv ghost args next_mv1 = Inr (elabArgTms, actualTypes, next_mv2)" and
    nmv': "next_mv' = next_mv2"
    by (auto simp: elab_impure_call_term_def Let_def
             split: sum.splits prod.splits if_splits)
  have "next_mv \<le> next_mv1" using resolve_impure_callee_next_mv[OF rc] .
  moreover have "next_mv1 \<le> next_mv2" using elab_term_list_next_mv_monotone[OF el] .
  ultimately show ?thesis using nmv' by simp
qed


(* ========================================================================== *)
(* Correctness of the impure-call helpers *)
(* ========================================================================== *)

(* Correctness of resolve_impure_callee. Mirrors resolve_callee_function_correct
   but for the impure path (which does NOT reject impure / Ref-arg functions).
   It exposes the raw facts the impure-call assembly needs: the function exists,
   the resolved type args are well-kinded / runtime, the expected argument types
   and return type are the function's signature specialized by those type args,
   and (for the substitution-composition step) the signature's tyvars are
   distinct and its component types only mention those tyvars. *)
lemma resolve_impure_callee_correct:
  assumes rc: "resolve_impure_callee env elabEnv ghost callee next_mv
                 = Inr (fnName, newTyArgs, expArgTypes, varOrRefs, retType0, next_mv')"
    and wf: "tyenv_well_formed env"
    and ee_wf: "elabenv_well_formed env elabEnv"
  shows "\<exists>funInfo.
            fmlookup (TE_Functions env) fnName = Some funInfo
          \<and> next_mv \<le> next_mv'
          \<and> length newTyArgs = length (FI_TyArgs funInfo)
          \<and> list_all (is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv')) newTyArgs
          \<and> (ghost = NotGhost \<longrightarrow>
               list_all (is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv')) newTyArgs)
          \<and> (ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost)
          \<and> expArgTypes = map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) ty)
                              (FI_TmArgs funInfo)
          \<and> varOrRefs = map (\<lambda>(_, _, vor). vor) (FI_TmArgs funInfo)
          \<and> retType0 = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) (FI_ReturnType funInfo)
          \<and> distinct (FI_TyArgs funInfo)
          \<and> (\<forall>t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo). type_tyvars t \<subseteq> set (FI_TyArgs funInfo))
          \<and> type_tyvars (FI_ReturnType funInfo) \<subseteq> set (FI_TyArgs funInfo)"
proof -
  have td_wf: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using ee_wf unfolding elabenv_well_formed_def by simp
  from rc obtain nloc tyArgs where
    callee_eq: "callee = BabTm_Name nloc fnName tyArgs"
    by (auto simp: resolve_impure_callee_def Let_def
             split: BabTerm.splits option.splits if_splits sum.splits prod.splits)
  from rc callee_eq obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo"
    by (auto simp: resolve_impure_callee_def split: option.splits if_splits sum.splits prod.splits)
  from rc callee_eq fn_lookup have not_void: "fnName |\<notin>| EE_VoidFunctions elabEnv"
    by (auto simp: resolve_impure_callee_def split: if_splits sum.splits prod.splits)
  from rc callee_eq fn_lookup not_void have ghost_ok: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost"
    by (auto simp: resolve_impure_callee_def split: if_splits sum.splits prod.splits)
  from rc callee_eq fn_lookup not_void ghost_ok obtain next_mv1 where
    resolve_eq: "resolve_type_args env elabEnv ghost nloc fnName (FI_TyArgs funInfo) tyArgs next_mv
                 = Inr (newTyArgs, next_mv1)" and
    next_mv_eq: "next_mv' = next_mv1" and
    expArg_eq: "expArgTypes = map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) ty)
                                  (FI_TmArgs funInfo)" and
    vor_eq: "varOrRefs = map (\<lambda>(_, _, vor). vor) (FI_TmArgs funInfo)" and
    ret_eq: "retType0 = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) (FI_ReturnType funInfo)"
    by (auto simp: resolve_impure_callee_def Let_def
             split: sum.splits prod.splits if_splits)
  have rta: "next_mv \<le> next_mv'
           \<and> length newTyArgs = length (FI_TyArgs funInfo)
           \<and> list_all (is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv')) newTyArgs
           \<and> (ghost = NotGhost \<longrightarrow>
                list_all (is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv')) newTyArgs)"
    using resolve_type_args_correct[OF resolve_eq wf td_wf] next_mv_eq by simp
  \<comment> \<open>Signature tyvars are distinct and the component types only mention them.\<close>
  have distinct_tyargs: "distinct (FI_TyArgs funInfo)"
    using wf fn_lookup unfolding tyenv_well_formed_def tyenv_fun_tyvars_distinct_def by blast
  have fi_args_wk: "\<forall>t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo).
            is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) t"
    using wf fn_lookup unfolding tyenv_well_formed_def tyenv_fun_types_well_kinded_def by blast
  have fi_ret_wk: "is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) (FI_ReturnType funInfo)"
    using wf fn_lookup unfolding tyenv_well_formed_def tyenv_fun_types_well_kinded_def by blast
  have fi_args_tyvars: "\<forall>t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo). type_tyvars t \<subseteq> set (FI_TyArgs funInfo)"
  proof
    fix t assume "t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)"
    with fi_args_wk have "is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) t" by blast
    from is_well_kinded_type_tyvars_subset[OF this]
    show "type_tyvars t \<subseteq> set (FI_TyArgs funInfo)" by (simp add: fset_of_list.rep_eq)
  qed
  have fi_ret_tyvars: "type_tyvars (FI_ReturnType funInfo) \<subseteq> set (FI_TyArgs funInfo)"
    using is_well_kinded_type_tyvars_subset[OF fi_ret_wk] by (simp add: fset_of_list.rep_eq)
  show ?thesis
    using fn_lookup rta ghost_ok expArg_eq vor_eq ret_eq distinct_tyargs fi_args_tyvars fi_ret_tyvars
    by blast
qed

(* validate_call_args returns a list as long as its input term list (the four
   input lists must have equal length, else the function is undefined). *)
lemma validate_call_args_length:
  "validate_call_args env loc subst tms actualTys expectedTys varOrRefs = Inr finalArgTms
     \<Longrightarrow> length tms = length actualTys \<Longrightarrow> length actualTys = length expectedTys
     \<Longrightarrow> length expectedTys = length varOrRefs
     \<Longrightarrow> length finalArgTms = length tms"
  by (induction env loc subst tms actualTys expectedTys varOrRefs arbitrary: finalArgTms
      rule: validate_call_args.induct)
     (auto simp: Let_def split: VarOrRef.splits sum.splits if_splits)

(* validate_call_args depends on env only through is_writable_lvalue (in the Ref
   arm), which is tyvar-irrelevant, so its result is unchanged in the
   fresh-tyvar-extended env. This lets us move the call from the un-extended
   caller env to the extended env where the argument typing facts live. *)
lemma validate_call_args_extend_env_with_tyvars:
  "validate_call_args (extend_env_with_tyvars env ghost lo hi)
     loc subst tms actualTys expectedTys varOrRefs
   = validate_call_args env loc subst tms actualTys expectedTys varOrRefs"
  by (induction env loc subst tms actualTys expectedTys varOrRefs rule: validate_call_args.induct)
     (auto simp: Let_def split: VarOrRef.splits sum.splits)

(* Correctness of validate_call_args: given that the (pre-coercion) terms type
   to their actual types, the unify substitution reconciles each actual/expected
   pair (equal after subst, or both finite integers), and the subst is harmless
   on the env, the validated terms type to the substituted expected types — and
   Ref positions are writable lvalues. The conclusion is the per-argument shape
   that core_impure_call_type's list_all2 check requires. *)
lemma validate_call_args_correct:
  assumes vca: "validate_call_args env loc subst tms actualTys expectedTys varOrRefs
                  = Inr finalArgTms"
      and ih: "list_all2 (\<lambda>tm ty. core_term_type env ghost tm = Some ty) tms actualTys"
      and unified: "list_all2 (\<lambda>actualTy expectedTy.
             apply_subst subst actualTy = apply_subst subst expectedTy
             \<or> (is_finite_integer_type (apply_subst subst actualTy)
                \<and> is_finite_integer_type (apply_subst subst expectedTy)))
           actualTys expectedTys"
      and wf: "tyenv_well_formed env"
      and subst_wk: "\<forall>ty \<in> fmran' subst. is_well_kinded env ty"
      and subst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' subst. is_runtime_type env ty)"
      and len1: "length tms = length actualTys"
      and len2: "length actualTys = length expectedTys"
      and len3: "length expectedTys = length varOrRefs"
      and locals_unaffected:
        "\<And>name ty'. fmlookup (TE_LocalVars env) name = Some ty'
                      \<Longrightarrow> apply_subst subst ty' = ty'"
      and ret_unaffected: "apply_subst subst (TE_ReturnType env) = TE_ReturnType env"
  shows "list_all2 (\<lambda>(tm, vor) expectedTy.
           case vor of
             Var \<Rightarrow> (case core_term_type env ghost tm of
                       None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
           | Ref \<Rightarrow> is_writable_lvalue env tm
                    \<and> core_term_type env ghost tm = Some expectedTy)
         (zip finalArgTms varOrRefs)
         (map (apply_subst subst) expectedTys)"
  using assms
proof (induction env loc subst tms actualTys expectedTys varOrRefs
       arbitrary: finalArgTms rule: validate_call_args.induct)
  case (1 env loc subst)
  then show ?case by simp
next
  case (2 env loc subst tm tms actualTy actualTys expectedTy expectedTys vor vors)
  let ?tm' = "apply_subst_to_term subst tm"
  let ?actualTy' = "apply_subst subst actualTy"
  let ?expectedTy' = "apply_subst subst expectedTy"

  from "2.prems"(2) have
    head_typed: "core_term_type env ghost tm = Some actualTy" and
    tail_typed: "list_all2 (\<lambda>tm ty. core_term_type env ghost tm = Some ty) tms actualTys"
    by simp_all
  from "2.prems"(3) have
    head_unif: "?actualTy' = ?expectedTy'
                \<or> (is_finite_integer_type ?actualTy' \<and> is_finite_integer_type ?expectedTy')" and
    tail_unif: "list_all2 (\<lambda>actualTy expectedTy.
                  apply_subst subst actualTy = apply_subst subst expectedTy
                  \<or> (is_finite_integer_type (apply_subst subst actualTy)
                     \<and> is_finite_integer_type (apply_subst subst expectedTy)))
                actualTys expectedTys"
    by simp_all
  from "2.prems"(7,8,9) have
    len_tms: "length tms = length actualTys" and
    len_tys: "length actualTys = length expectedTys" and
    len_vor: "length expectedTys = length vors"
    by simp_all

  \<comment> \<open>The head term, substitution applied, typechecks at the substituted actual type.\<close>
  have head_tm'_typed: "core_term_type env ghost ?tm' = Some ?actualTy'"
    using apply_subst_to_term_preserves_typing[OF head_typed "2.prems"(4,5,6)
            "2.prems"(10) "2.prems"(11)] .

  show ?case
  proof (cases vor)
    case Var
    \<comment> \<open>Var: validate_call_args inserts a cast iff the types differ; the tail recurses.\<close>
    from "2.prems"(1) Var obtain rest where
      tail_vca: "validate_call_args env loc subst tms actualTys expectedTys vors = Inr rest" and
      finalArgTms_eq: "finalArgTms
                         = (if ?actualTy' = ?expectedTy' then ?tm'
                            else CoreTm_Cast ?expectedTy' ?tm') # rest"
      by (auto simp: Let_def split: sum.splits)
    have ih: "list_all2 (\<lambda>(tm, vor) expectedTy.
                case vor of
                  Var \<Rightarrow> (case core_term_type env ghost tm of
                            None \<Rightarrow> False | Some t \<Rightarrow> t = expectedTy)
                | Ref \<Rightarrow> is_writable_lvalue env tm
                         \<and> core_term_type env ghost tm = Some expectedTy)
              (zip rest vors) (map (apply_subst subst) expectedTys)"
      using "2.IH"(1)[OF refl refl refl Var refl tail_vca tail_typed tail_unif "2.prems"(4,5,6)
                          len_tms len_tys len_vor "2.prems"(10) "2.prems"(11)] .
    \<comment> \<open>The head (cast or not) typechecks to the substituted expected type.\<close>
    have head_result: "core_term_type env ghost
                         (if ?actualTy' = ?expectedTy' then ?tm' else CoreTm_Cast ?expectedTy' ?tm')
                       = Some ?expectedTy'"
    proof (cases "?actualTy' = ?expectedTy'")
      case True
      thus ?thesis using head_tm'_typed by simp
    next
      case False
      from head_unif False have
        actual_fin: "is_finite_integer_type ?actualTy'" and
        expected_fin: "is_finite_integer_type ?expectedTy'" by simp_all
      have actual_int: "is_integer_type ?actualTy'"
        using actual_fin finite_integer_type_is_integer_type by blast
      have expected_int: "is_integer_type ?expectedTy'"
        using expected_fin finite_integer_type_is_integer_type by blast
      have expected_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env ?expectedTy'"
        using expected_fin by (cases ?expectedTy') auto
      show ?thesis using head_tm'_typed actual_int expected_int expected_rt False
        by (auto split: option.splits)
    qed
    show ?thesis using finalArgTms_eq head_result ih Var by simp
  next
    case Ref
    \<comment> \<open>Ref: validate_call_args requires exact match (no cast) and a writable lvalue.\<close>
    from "2.prems"(1) Ref obtain rest where
      eq_types: "?actualTy' = ?expectedTy'" and
      writ: "is_writable_lvalue env ?tm'" and
      tail_vca: "validate_call_args env loc subst tms actualTys expectedTys vors = Inr rest" and
      finalArgTms_eq: "finalArgTms = ?tm' # rest"
      by (auto simp: Let_def split: sum.splits if_splits)
    have g1: "\<not> ?actualTy' \<noteq> ?expectedTy'" using eq_types by simp
    have g2: "\<not> \<not> is_writable_lvalue env ?tm'" using writ by simp
    have ih: "list_all2 (\<lambda>(tm, vor) expectedTy.
                case vor of
                  Var \<Rightarrow> (case core_term_type env ghost tm of
                            None \<Rightarrow> False | Some t \<Rightarrow> t = expectedTy)
                | Ref \<Rightarrow> is_writable_lvalue env tm
                         \<and> core_term_type env ghost tm = Some expectedTy)
              (zip rest vors) (map (apply_subst subst) expectedTys)"
      using "2.IH"(2)[OF refl refl refl Ref g1 g2 tail_vca tail_typed tail_unif "2.prems"(4,5,6)
                          len_tms len_tys len_vor "2.prems"(10) "2.prems"(11)] .
    have head_typed': "core_term_type env ghost ?tm' = Some ?expectedTy'"
      using head_tm'_typed eq_types by simp
    show ?thesis using finalArgTms_eq head_typed' writ ih Ref by simp
  qed
qed (simp_all)


(* Main correctness of elab_impure_call_term: its output is accepted by
   core_impure_call_type in the env extended with the fresh tyvar interval. *)
lemma elab_impure_call_term_correct:
  assumes elab: "elab_impure_call_term env elabEnv ghost loc callee args next_mv
                   = Inr (fnName, finalTyArgs, finalArgTms, retTy, next_mv')"
    and wf: "tyenv_well_formed env"
    and ee_wf: "elabenv_well_formed env elabEnv"
    and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv"
  shows "core_impure_call_type (extend_env_with_tyvars env ghost next_mv next_mv')
           ghost fnName finalTyArgs finalArgTms = Some retTy"
proof -
  let ?is_flex = "(\<lambda>n. n |\<notin>| TE_TypeVars env)"
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  let ?mk_err = "(\<lambda>idx exp act. [TyErr_TypeMismatch (bab_term_location (args ! idx)) exp act])"

  \<comment> \<open>Extract the three sub-results of elab_impure_call_term.\<close>
  from elab obtain newTyArgs expArgTypes varOrRefs retType0 next_mv1 where
    rc: "resolve_impure_callee env elabEnv ghost callee next_mv
           = Inr (fnName, newTyArgs, expArgTypes, varOrRefs, retType0, next_mv1)"
    by (auto simp: elab_impure_call_term_def split: if_splits sum.splits prod.splits)
  from elab rc have len_args: "length args = length expArgTypes"
    by (auto simp: elab_impure_call_term_def split: if_splits sum.splits prod.splits)
  from elab rc len_args obtain elabArgTms actualTypes next_mv2 where
    el: "elab_term_list env elabEnv ghost args next_mv1 = Inr (elabArgTms, actualTypes, next_mv2)"
    by (auto simp: elab_impure_call_term_def split: if_splits sum.splits prod.splits)
  from elab rc len_args el obtain finalSubst where
    unify_eq: "unify_type_lists ?is_flex ?mk_err 0 actualTypes expArgTypes fmempty = Inr finalSubst"
    by (auto simp: elab_impure_call_term_def split: if_splits sum.splits prod.splits)
  from elab rc len_args el unify_eq have
    vca: "validate_call_args env loc finalSubst elabArgTms actualTypes expArgTypes varOrRefs
            = Inr finalArgTms" and
    tyargs_eq: "finalTyArgs = map (apply_subst finalSubst) newTyArgs" and
    retTy_eq: "retTy = apply_subst finalSubst retType0" and
    next_mv2_eq: "next_mv' = next_mv2"
    by (auto simp: elab_impure_call_term_def split: if_splits sum.splits prod.splits)

  \<comment> \<open>Facts from resolve_impure_callee_correct (at next_mv1).\<close>
  from resolve_impure_callee_correct[OF rc wf ee_wf] obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
    mono_1: "next_mv \<le> next_mv1" and
    len_tyargs: "length newTyArgs = length (FI_TyArgs funInfo)" and
    newTyArgs_wk1: "list_all (is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv1)) newTyArgs" and
    newTyArgs_rt1: "ghost = NotGhost \<longrightarrow>
                      list_all (is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv1)) newTyArgs" and
    ghost_ok: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost" and
    expArg_eq: "expArgTypes = map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) ty)
                                  (FI_TmArgs funInfo)" and
    vor_eq: "varOrRefs = map (\<lambda>(_, _, vor). vor) (FI_TmArgs funInfo)" and
    ret0_eq: "retType0 = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) (FI_ReturnType funInfo)" and
    distinct_tyargs: "distinct (FI_TyArgs funInfo)" and
    fi_args_tyvars: "\<forall>t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo). type_tyvars t \<subseteq> set (FI_TyArgs funInfo)" and
    fi_ret_tyvars: "type_tyvars (FI_ReturnType funInfo) \<subseteq> set (FI_TyArgs funInfo)"
    by blast

  have mono_2: "next_mv1 \<le> next_mv2" using elab_term_list_next_mv_monotone[OF el] .
  have env'_eq2: "?env' = extend_env_with_tyvars env ghost next_mv next_mv2"
    using next_mv2_eq by simp
  have wf': "tyenv_well_formed ?env'"
    using wf tyenv_well_formed_extend_env_with_tyvars by blast

  \<comment> \<open>The fresh interval bound carries through resolve to next_mv1.\<close>
  have fresh_1: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv1" using bound mono_1 by fastforce

  \<comment> \<open>IH from elab_term_list: elaborated args type to their actual types at ?env1,
      lifted to ?env'.\<close>
  have ih_args_1: "list_all2 (\<lambda>tm ty. core_term_type
                       (extend_env_with_tyvars env ghost next_mv1 next_mv2) ghost tm = Some ty)
                     elabArgTms actualTypes"
    using elab_term_list_correct[OF el wf ee_wf fresh_1] .
  have ih_args: "list_all2 (\<lambda>tm ty. core_term_type ?env' ghost tm = Some ty) elabArgTms actualTypes"
  proof -
    have "\<And>tm ty. core_term_type (extend_env_with_tyvars env ghost next_mv1 next_mv2) ghost tm = Some ty
                  \<Longrightarrow> core_term_type ?env' ghost tm = Some ty"
      using core_term_type_extend_env_with_tyvars_mono[where lo=next_mv1 and hi=next_mv2
              and lo'=next_mv and hi'=next_mv'] mono_1 mono_2 next_mv2_eq by simp
    thus ?thesis using ih_args_1 by (auto elim!: list_all2_mono)
  qed

  \<comment> \<open>Lengths.\<close>
  have len_elab: "length elabArgTms = length actualTypes"
    using ih_args by (simp add: list_all2_lengthD)
  have len_actual_exp: "length actualTypes = length expArgTypes"
    using len_args el by (simp add: elab_term_list_length)
  have len_exp_vor: "length expArgTypes = length varOrRefs"
    using expArg_eq vor_eq by simp

  \<comment> \<open>Well-kindedness / runtime of actual and expected types at ?env'.\<close>
  have actualTypes_wk: "list_all (is_well_kinded ?env') actualTypes"
  proof (simp add: list_all_length, intro allI impI)
    fix i assume "i < length actualTypes"
    with ih_args have "core_term_type ?env' ghost (elabArgTms ! i) = Some (actualTypes ! i)"
      by (simp add: list_all2_conv_all_nth len_elab)
    thus "is_well_kinded ?env' (actualTypes ! i)"
      using wf' core_term_type_well_kinded by blast
  qed
  have actualTypes_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env') actualTypes"
    using ih_args wf' core_term_type_notghost_runtime
    by (auto simp: list_all2_conv_all_nth list_all_length len_elab)

  \<comment> \<open>newTyArgs well-kinded / runtime at ?env' (lift from ?env1).\<close>
  have newTyArgs_wk: "list_all (is_well_kinded ?env') newTyArgs"
    unfolding list_all_iff env'_eq2
  proof
    fix t assume "t \<in> set newTyArgs"
    with newTyArgs_wk1 have "is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv1) t"
      by (simp add: list_all_iff)
    thus "is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv2) t"
      using is_well_kinded_extend_env_with_tyvars_mono mono_2 by blast
  qed
  have newTyArgs_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env') newTyArgs"
  proof
    assume ng: "ghost = NotGhost"
    show "list_all (is_runtime_type ?env') newTyArgs"
      unfolding list_all_iff env'_eq2
    proof
      fix t assume "t \<in> set newTyArgs"
      with newTyArgs_rt1 ng have "is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv1) t"
        by (simp add: list_all_iff)
      thus "is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv2) t"
        using is_runtime_type_extend_env_with_tyvars_mono mono_2 by blast
    qed
  qed

  \<comment> \<open>Expected types well-kinded / runtime at ?env' (each is apply_subst of a param type).\<close>
  have expArgTypes_wk: "list_all (is_well_kinded ?env') expArgTypes"
  proof -
    have fi_args_wk_inner: "\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo).
            is_well_kinded (?env' \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) ty"
      using wf' fn_lookup unfolding tyenv_well_formed_def tyenv_fun_types_well_kinded_def
      by (simp add: extend_env_with_tyvars_def)
    have "list_all (\<lambda>(_, ty, _). is_well_kinded ?env'
            (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) ty)) (FI_TmArgs funInfo)"
    proof (unfold list_all_iff, intro ballI, clarify)
      fix n t v assume "(n, t, v) \<in> set (FI_TmArgs funInfo)"
      hence "t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)" by (force simp: rev_image_eqI)
      with fi_args_wk_inner
      have "is_well_kinded (?env' \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) t" by blast
      thus "is_well_kinded ?env' (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) t)"
        using apply_subst_specializes_well_kinded[OF _ newTyArgs_wk len_tyargs[symmetric]] by simp
    qed
    thus ?thesis using expArg_eq by (auto simp: list_all_iff)
  qed
  have expArgTypes_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env') expArgTypes"
  proof
    assume ng: "ghost = NotGhost"
    hence fg_ng: "FI_Ghost funInfo = NotGhost" using GhostOrNot.exhaust ghost_ok by auto
    have fi_args_rt_inner: "\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo).
            is_runtime_type (?env' \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo),
                                     TE_RuntimeTypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) ty"
      using wf' fn_lookup fg_ng unfolding tyenv_well_formed_def tyenv_fun_ghost_constraint_def
      by (simp add: extend_env_with_tyvars_def Let_def)
    have tyargs_rt: "list_all (is_runtime_type ?env') newTyArgs" using newTyArgs_rt ng by simp
    have "list_all (\<lambda>(_, ty, _). is_runtime_type ?env'
            (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) ty)) (FI_TmArgs funInfo)"
    proof (unfold list_all_iff, intro ballI, clarify)
      fix n t v assume "(n, t, v) \<in> set (FI_TmArgs funInfo)"
      hence "t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)" by (force simp: rev_image_eqI)
      with fi_args_rt_inner
      have "is_runtime_type (?env' \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo),
                                     TE_RuntimeTypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) t" by blast
      thus "is_runtime_type ?env' (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) t)"
        using apply_subst_specializes_runtime[OF _ tyargs_rt len_tyargs[symmetric]] by simp
    qed
    thus "list_all (is_runtime_type ?env') expArgTypes" using expArg_eq by (auto simp: list_all_iff)
  qed

  \<comment> \<open>unify_type_lists facts at ?env'.\<close>
  have empty_wk: "\<forall>ty \<in> fmran' (fmempty :: TypeSubst). is_well_kinded ?env' ty" by (simp add: fmran'_def)
  have empty_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' (fmempty :: TypeSubst). is_runtime_type ?env' ty)"
    by (simp add: fmran'_def)
  have empty_dom: "\<forall>n. n |\<in>| fmdom (fmempty :: TypeSubst) \<longrightarrow> ?is_flex n" by simp
  have unify_correct:
    "(\<forall>ty \<in> fmran' finalSubst. is_well_kinded ?env' ty)
     \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type ?env' ty))
     \<and> list_all2 (\<lambda>actualTy expectedTy.
         apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
         \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
            \<and> is_finite_integer_type (apply_subst finalSubst expectedTy)))
       actualTypes expArgTypes
     \<and> (\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> ?is_flex n)"
    using unify_type_lists_correct[OF unify_eq wf' len_actual_exp actualTypes_wk expArgTypes_wk
            empty_wk actualTypes_rt expArgTypes_rt empty_rt empty_dom] by blast
  from unify_correct have
    finalSubst_wk: "\<forall>ty \<in> fmran' finalSubst. is_well_kinded ?env' ty" and
    finalSubst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type ?env' ty)" and
    types_unified: "list_all2 (\<lambda>actualTy expectedTy.
         apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
         \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
            \<and> is_finite_integer_type (apply_subst finalSubst expectedTy)))
       actualTypes expArgTypes" and
    finalSubst_dom_flex: "\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> ?is_flex n"
    by blast+

  \<comment> \<open>finalSubst is identity on locals / return type of ?env'.\<close>
  have env'_locals: "TE_LocalVars ?env' = TE_LocalVars env" unfolding extend_env_with_tyvars_def by simp
  have env'_ret: "TE_ReturnType ?env' = TE_ReturnType env" unfolding extend_env_with_tyvars_def by simp
  from flex_subst_identity_on_env[OF finalSubst_dom_flex wf env'_locals env'_ret]
  have locals_unaffected: "\<And>name ty'. fmlookup (TE_LocalVars ?env') name = Some ty'
                                      \<Longrightarrow> apply_subst finalSubst ty' = ty'"
    and ret_unaffected: "apply_subst finalSubst (TE_ReturnType ?env') = TE_ReturnType ?env'"
    by blast+

  \<comment> \<open>Move the call into the extended env (validate_call_args is tyvar-irrelevant),
      so it can be combined with the extended-env typing facts.\<close>
  have vca': "validate_call_args ?env' loc finalSubst elabArgTms actualTypes expArgTypes varOrRefs
                = Inr finalArgTms"
    using vca by (simp add: validate_call_args_extend_env_with_tyvars)
  \<comment> \<open>The validated arg terms satisfy the per-argument core_impure_call_type check.\<close>
  have args_checked: "list_all2 (\<lambda>(tm, vor) expectedTy.
           case vor of
             Var \<Rightarrow> (case core_term_type ?env' ghost tm of
                       None \<Rightarrow> False | Some t \<Rightarrow> t = expectedTy)
           | Ref \<Rightarrow> is_writable_lvalue ?env' tm \<and> core_term_type ?env' ghost tm = Some expectedTy)
         (zip finalArgTms varOrRefs)
         (map (apply_subst finalSubst) expArgTypes)"
    using validate_call_args_correct[OF vca' ih_args types_unified wf' finalSubst_wk finalSubst_rt
            len_elab len_actual_exp len_exp_vor locals_unaffected ret_unaffected] .

  \<comment> \<open>The substituted expected types coincide with core_impure_call_type's recomputation
      from finalTyArgs (substitution composition).\<close>
  have tysubst_eq: "fmap_of_list (zip (FI_TyArgs funInfo) finalTyArgs)
                      = fmap_of_list (zip (FI_TyArgs funInfo) (map (apply_subst finalSubst) newTyArgs))"
    using tyargs_eq by simp
  have exp_recompute: "map (apply_subst finalSubst) expArgTypes
                       = map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) finalTyArgs)) ty)
                             (FI_TmArgs funInfo)"
  proof -
    have "map (apply_subst finalSubst) expArgTypes
            = map (apply_subst finalSubst)
                  (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) ty)
                       (FI_TmArgs funInfo))"
      using expArg_eq by simp
    also have "\<dots> = map (\<lambda>(_, ty, _). apply_subst finalSubst
                          (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) ty))
                        (FI_TmArgs funInfo)"
      by (simp add: case_prod_unfold comp_def)
    also have "\<dots> = map (\<lambda>(_, ty, _). apply_subst
                          (fmap_of_list (zip (FI_TyArgs funInfo) (map (apply_subst finalSubst) newTyArgs))) ty)
                        (FI_TmArgs funInfo)"
    proof (rule map_cong[OF refl])
      fix x assume "x \<in> set (FI_TmArgs funInfo)"
      obtain n t v where x_eq: "x = (n, t, v)" by (cases x)
      with \<open>x \<in> set (FI_TmArgs funInfo)\<close> have "t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)"
        by (force simp: rev_image_eqI)
      with fi_args_tyvars have t_tyvars: "type_tyvars t \<subseteq> set (FI_TyArgs funInfo)" by blast
      show "(case x of (_, ty, _) \<Rightarrow> apply_subst finalSubst
                (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) ty))
            = (case x of (_, ty, _) \<Rightarrow> apply_subst
                (fmap_of_list (zip (FI_TyArgs funInfo) (map (apply_subst finalSubst) newTyArgs))) ty)"
        using x_eq apply_subst_compose_zip[OF len_tyargs[symmetric] t_tyvars distinct_tyargs] by simp
    qed
    finally show ?thesis using tysubst_eq by simp
  qed

  \<comment> \<open>And the result type coincides with the recomputed return type.\<close>
  have ret_recompute: "retTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) finalTyArgs)) (FI_ReturnType funInfo)"
  proof -
    have "retTy = apply_subst finalSubst
                    (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) (FI_ReturnType funInfo))"
      using retTy_eq ret0_eq by simp
    also have "\<dots> = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) (map (apply_subst finalSubst) newTyArgs)))
                               (FI_ReturnType funInfo)"
      using apply_subst_compose_zip[OF len_tyargs[symmetric] fi_ret_tyvars distinct_tyargs] by simp
    finally show ?thesis using tysubst_eq by simp
  qed

  \<comment> \<open>finalTyArgs well-kinded / runtime at ?env' (subst applied to newTyArgs).\<close>
  have finalTyArgs_wk: "list_all (is_well_kinded ?env') finalTyArgs"
    unfolding tyargs_eq list_all_iff
  proof
    fix t assume "t \<in> set (map (apply_subst finalSubst) newTyArgs)"
    then obtain t0 where t0_in: "t0 \<in> set newTyArgs" and t_eq: "t = apply_subst finalSubst t0" by auto
    from t0_in newTyArgs_wk have "is_well_kinded ?env' t0" by (simp add: list_all_iff)
    thus "is_well_kinded ?env' t" using t_eq finalSubst_wk
      by (auto intro!: apply_subst_preserves_well_kinded[where src="?env'" and tgt="?env'"]
               simp: fmran'I split: option.splits)
  qed
  have finalTyArgs_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env') finalTyArgs"
  proof
    assume ng: "ghost = NotGhost"
    show "list_all (is_runtime_type ?env') finalTyArgs"
      unfolding tyargs_eq list_all_iff
    proof
      fix t assume "t \<in> set (map (apply_subst finalSubst) newTyArgs)"
      then obtain t0 where t0_in: "t0 \<in> set newTyArgs" and t_eq: "t = apply_subst finalSubst t0" by auto
      from t0_in newTyArgs_rt ng have "is_runtime_type ?env' t0" by (simp add: list_all_iff)
      thus "is_runtime_type ?env' t" using t_eq ng finalSubst_rt
        using apply_subst_preserves_runtime_same_env by auto
    qed
  qed

  \<comment> \<open>Lengths needed by core_impure_call_type.\<close>
  have len_finalTyArgs: "length finalTyArgs = length (FI_TyArgs funInfo)"
    using tyargs_eq len_tyargs by simp
  have len_finalArgTms: "length finalArgTms = length (FI_TmArgs funInfo)"
  proof -
    have "length finalArgTms = length elabArgTms"
      using validate_call_args_length[OF vca len_elab len_actual_exp len_exp_vor] .
    thus ?thesis using len_elab len_actual_exp vor_eq expArg_eq by simp
  qed
  have fn_lookup': "fmlookup (TE_Functions ?env') fnName = Some funInfo"
    using fn_lookup by (simp add: extend_env_with_tyvars_def)

  \<comment> \<open>Assemble: unfold core_impure_call_type with all the checks discharged.\<close>
  have check_l2: "list_all2 (\<lambda>(tm, vor) expectedTy.
           case vor of
             Var \<Rightarrow> (case core_term_type ?env' ghost tm of
                       None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
           | Ref \<Rightarrow> is_writable_lvalue ?env' tm \<and> core_term_type ?env' ghost tm = Some expectedTy)
         (zip finalArgTms varOrRefs)
         (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) finalTyArgs)) ty)
              (FI_TmArgs funInfo))"
    using args_checked exp_recompute by simp

  show ?thesis
    unfolding core_impure_call_type_def
    using fn_lookup' len_finalTyArgs finalTyArgs_wk finalTyArgs_rt ghost_ok len_finalArgTms
          vor_eq check_l2 ret_recompute
    by (auto simp: Let_def split: if_splits)
qed


(* Corollary for the inferred impure-call VarDecl branch: when the call's return
   type has no unresolved metavariables, it is well-kinded (runtime in NotGhost)
   in env itself — analogous to elab_term_inferred_type_well_kinded_runtime. *)
lemma elab_impure_call_term_inferred_type_well_kinded_runtime:
  assumes elab: "elab_impure_call_term env elabEnv ghost loc callee args next_mv
                   = Inr (fnName, finalTyArgs, finalArgTms, retTy, next_mv')"
    and wf: "tyenv_well_formed env"
    and ee_wf: "elabenv_well_formed env elabEnv"
    and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv"
    and no_meta: "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list retTy)"
  shows "is_well_kinded env retTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env retTy)"
proof -
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  have ct: "core_impure_call_type ?env' ghost fnName finalTyArgs finalArgTms = Some retTy"
    using elab_impure_call_term_correct[OF elab wf ee_wf bound] .
  have wf': "tyenv_well_formed ?env'"
    using wf tyenv_well_formed_extend_env_with_tyvars by blast
  \<comment> \<open>Well-kinded / runtime at the extended env, then transfer down to env.\<close>
  have wkrt': "is_well_kinded ?env' retTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type ?env' retTy)"
    using core_impure_call_type_well_kinded_and_runtime[OF ct wf'] .
  have tvs_sub: "type_tyvars retTy \<subseteq> fset (TE_TypeVars env)"
    using no_meta by (auto simp: set_type_tyvars_list[symmetric] list_all_iff)
  have dt_eq: "TE_Datatypes env = TE_Datatypes ?env'" unfolding extend_env_with_tyvars_def by simp
  have wk: "is_well_kinded env retTy"
    using is_well_kinded_transfer[OF conjunct1[OF wkrt'] tvs_sub dt_eq] .
  have rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env retTy"
  proof
    assume ng: "ghost = NotGhost"
    have rt': "is_runtime_type ?env' retTy" using wkrt' ng by simp
    have rtv_eq: "fset (TE_RuntimeTypeVars ?env')
                    = fset (TE_RuntimeTypeVars env) \<union> {next_mv..<next_mv'}"
      using ng unfolding extend_env_with_tyvars_def by (simp add: fset_of_list.rep_eq)
    have tvs_in_rt: "type_tyvars retTy \<subseteq> fset (TE_RuntimeTypeVars env)"
    proof
      fix n assume n_in: "n \<in> type_tyvars retTy"
      from n_in tvs_sub have "n |\<in>| TE_TypeVars env" by auto
      hence n_lt: "n < next_mv" using bound by simp
      from n_in is_runtime_type_tyvars_subset[OF rt'] rtv_eq
      have "n \<in> fset (TE_RuntimeTypeVars env) \<union> {next_mv..<next_mv'}" by auto
      with n_lt show "n \<in> fset (TE_RuntimeTypeVars env)" by auto
    qed
    have gd_eq: "TE_GhostDatatypes env = TE_GhostDatatypes ?env'"
      unfolding extend_env_with_tyvars_def by simp
    show "is_runtime_type env retTy"
      using is_runtime_type_transfer[OF rt' tvs_in_rt gd_eq] .
  qed
  from wk rt show ?thesis by blast
qed



(* ========================================================================== *)
(* Correctness of the VarDecl and Assign helpers *)
(* ========================================================================== *)

(* vardecl_add_local only touches the three local-variable fields. *)
lemma vardecl_add_local_fields [simp]:
  "TE_TypeVars (vardecl_add_local env ghost varName varTy) = TE_TypeVars env"
  "TE_RuntimeTypeVars (vardecl_add_local env ghost varName varTy) = TE_RuntimeTypeVars env"
  "TE_FunctionGhost (vardecl_add_local env ghost varName varTy) = TE_FunctionGhost env"
  "TE_ProofGoal (vardecl_add_local env ghost varName varTy) = TE_ProofGoal env"
  "TE_Datatypes (vardecl_add_local env ghost varName varTy) = TE_Datatypes env"
  "TE_DataCtors (vardecl_add_local env ghost varName varTy) = TE_DataCtors env"
  by (simp_all add: vardecl_add_local_def)

(* Adding a (well-kinded, and in the non-ghost case runtime) variable to a
   well-formed env keeps it well-formed, for both ghost and non-ghost decls and
   regardless of the TE_ConstLocals update — exactly the shape every successful
   VarDecl branch produces. *)
lemma tyenv_well_formed_vardecl_result:
  assumes wf: "tyenv_well_formed env"
    and wk: "is_well_kinded env varTy"
    and rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env varTy"
  shows "tyenv_well_formed
           (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                  TE_GhostLocals := (if ghost = Ghost
                                     then finsert varName (TE_GhostLocals env)
                                     else fminus (TE_GhostLocals env) {|varName|}) \<rparr>
              \<lparr> TE_ConstLocals := c \<rparr>)"
proof (cases ghost)
  case Ghost
  from tyenv_well_formed_add_ghost_var[OF wf wk]
  have "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                 TE_GhostLocals := finsert varName (TE_GhostLocals env) \<rparr>)" .
  from tyenv_well_formed_TE_ConstLocals_irrelevant[OF this] Ghost show ?thesis by simp
next
  case NotGhost
  with rt have rt': "is_runtime_type env varTy" by simp
  from tyenv_well_formed_add_var[OF wf wk rt']
  have "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                 TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|} \<rparr>)" .
  from tyenv_well_formed_TE_ConstLocals_irrelevant[OF this] NotGhost show ?thesis by simp
qed

(* vardecl_add_local applied to a well-kinded (runtime in NotGhost) type keeps
   the env well-formed; it is exactly the shape tyenv_well_formed_vardecl_result
   covers (with c the cleared const set). *)
lemma tyenv_well_formed_vardecl_add_local:
  assumes wf: "tyenv_well_formed env"
    and wk: "is_well_kinded env varTy"
    and rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env varTy"
  shows "tyenv_well_formed (vardecl_add_local env ghost varName varTy)"
  unfolding vardecl_add_local_def
  using tyenv_well_formed_vardecl_result[OF wf wk rt] by simp

(* Each VarDecl helper leaves the env's non-local-variable fields unchanged, with
   NO well-formedness hypotheses — every successful branch's result env is
   vardecl_add_local env \<dots> (the Ref branch additionally overrides TE_ConstLocals,
   which is none of the fields below). These let both
   elab_statement_preserves_elabenv_well_formed and elab_statement_preserves_TE_TypeVars
   stay hyp-light (so neither needs the well-formedness lemmas, avoiding a cycle). *)
lemma elab_vardecl_pure_cong_fields:
  "elab_vardecl_pure env elabEnv ghost loc varName tyOpt tm next_mv = Inr (coreStmt, env', next_mv')
     \<Longrightarrow> TE_TypeVars env' = TE_TypeVars env \<and> TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env
       \<and> TE_FunctionGhost env' = TE_FunctionGhost env \<and> TE_ProofGoal env' = TE_ProofGoal env
       \<and> TE_Datatypes env' = TE_Datatypes env \<and> TE_DataCtors env' = TE_DataCtors env"
  by (auto simp: elab_vardecl_pure_def coerce_term_to_type_def vardecl_add_local_def
           split: sum.splits prod.splits option.splits if_splits)

lemma elab_vardecl_ref_cong_fields:
  "elab_vardecl_ref env elabEnv ghost loc varName tmOpt next_mv = Inr (coreStmt, env', next_mv')
     \<Longrightarrow> TE_TypeVars env' = TE_TypeVars env \<and> TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env
       \<and> TE_FunctionGhost env' = TE_FunctionGhost env \<and> TE_ProofGoal env' = TE_ProofGoal env
       \<and> TE_Datatypes env' = TE_Datatypes env \<and> TE_DataCtors env' = TE_DataCtors env"
  by (auto simp: elab_vardecl_ref_def vardecl_add_local_def
           split: sum.splits prod.splits option.splits if_splits)

(* The impure helper is only reached for an is_impure_call rhs, which forces tm to
   be a BabTm_Call (so the undefined fallback branch is unreachable). *)
lemma elab_vardecl_impure_cong_fields:
  "elab_vardecl_impure env elabEnv ghost loc varName tyOpt tm next_mv = Inr (coreStmt, env', next_mv')
     \<Longrightarrow> is_impure_call env elabEnv tm
     \<Longrightarrow> TE_TypeVars env' = TE_TypeVars env \<and> TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env
       \<and> TE_FunctionGhost env' = TE_FunctionGhost env \<and> TE_ProofGoal env' = TE_ProofGoal env
       \<and> TE_Datatypes env' = TE_Datatypes env \<and> TE_DataCtors env' = TE_DataCtors env"
  by (auto simp: elab_vardecl_impure_def is_impure_call_def reconcile_call_result_def Let_def
                 vardecl_add_local_def
           split: BabTerm.splits sum.splits prod.splits option.splits if_splits)


(* Helper for the inferred-type VarDecl branches: when elab_term succeeds and its
   synthesized type has no unresolved metavariables (all its tyvars are already in
   TE_TypeVars env, the no-metavar check the elaborator performs), that type is
   well-kinded in env; and in NotGhost mode it is also a runtime type. The type
   typechecks under env extended with the fresh interval [next_mv, next_mv'); the
   bound (\<forall>n |\<in>| TE_TypeVars env. n < next_mv) lets us strip that interval back off,
   transferring well-kindedness / runtime-ness down to env itself. *)
lemma elab_term_inferred_type_well_kinded_runtime:
  assumes elab: "elab_term env elabEnv g tm next_mv = Inr (coreTm, rhsTy, next_mv')"
    and wf: "tyenv_well_formed env"
    and ee_wf: "elabenv_well_formed env elabEnv"
    and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv"
    and no_meta: "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)"
  shows "is_well_kinded env rhsTy
         \<and> (g = NotGhost \<longrightarrow> is_runtime_type env rhsTy)"
proof -
  let ?env1 = "extend_env_with_tyvars env g next_mv next_mv'"
  \<comment> \<open>The elaborated term typechecks under the extended env.\<close>
  have typed: "core_term_type ?env1 g coreTm = Some rhsTy"
    using elab_term_correct(1)[OF elab wf ee_wf] bound by simp
  have wf1: "tyenv_well_formed ?env1"
    using wf tyenv_well_formed_extend_env_with_tyvars by simp
  \<comment> \<open>All tyvars of rhsTy are in the original (un-extended) TE_TypeVars.\<close>
  have tvs_sub: "type_tyvars rhsTy \<subseteq> fset (TE_TypeVars env)"
    using no_meta by (auto simp: set_type_tyvars_list[symmetric] list_all_iff)
  have dt_eq: "TE_Datatypes env = TE_Datatypes ?env1"
    unfolding extend_env_with_tyvars_def by simp
  \<comment> \<open>Well-kinded under the extended env, then transferred down to env.\<close>
  have wk1: "is_well_kinded ?env1 rhsTy" using core_term_type_well_kinded[OF typed wf1] .
  have wk: "is_well_kinded env rhsTy"
    using is_well_kinded_transfer[OF wk1 tvs_sub dt_eq] .
  \<comment> \<open>Runtime in NotGhost mode.\<close>
  have rt: "g = NotGhost \<longrightarrow> is_runtime_type env rhsTy"
  proof
    assume ng: "g = NotGhost"
    have rt1: "is_runtime_type ?env1 rhsTy"
      using core_term_type_notghost_runtime[OF typed[unfolded ng] wf1[unfolded ng]]
      by (simp add: ng)
    \<comment> \<open>rhsTy's tyvars are runtime in the extended env; the fresh interval is above
        next_mv, but every tyvar of rhsTy is < next_mv, so they are runtime in env.\<close>
    have rtv1: "type_tyvars rhsTy \<subseteq> fset (TE_RuntimeTypeVars ?env1)"
      using is_runtime_type_tyvars_subset[OF rt1] .
    have rtv_eq: "fset (TE_RuntimeTypeVars ?env1)
                    = fset (TE_RuntimeTypeVars env) \<union> {next_mv..<next_mv'}"
      using ng unfolding extend_env_with_tyvars_def
      by (simp add: fset_of_list.rep_eq)
    have tvs_in_rt: "type_tyvars rhsTy \<subseteq> fset (TE_RuntimeTypeVars env)"
    proof
      fix n assume n_in: "n \<in> type_tyvars rhsTy"
      from n_in tvs_sub have "n |\<in>| TE_TypeVars env" by auto
      hence n_lt: "n < next_mv" using bound by simp
      from n_in rtv1 rtv_eq have "n \<in> fset (TE_RuntimeTypeVars env) \<union> {next_mv..<next_mv'}"
        by auto
      with n_lt show "n \<in> fset (TE_RuntimeTypeVars env)" by auto
    qed
    have gd_eq: "TE_GhostDatatypes env = TE_GhostDatatypes ?env1"
      unfolding extend_env_with_tyvars_def by simp
    show "is_runtime_type env rhsTy"
      using is_runtime_type_transfer[OF rt1 tvs_in_rt gd_eq] .
  qed
  from wk rt show ?thesis by blast
qed


(* ----- elab_vardecl_pure ----- *)

(* The pure helper advances the counter (via elab_term). *)
lemma elab_vardecl_pure_next_mv:
  "elab_vardecl_pure env elabEnv ghost loc varName tyOpt tm next_mv
     = Inr (coreStmt, env', next_mv') \<Longrightarrow> next_mv \<le> next_mv'"
  by (auto simp: elab_vardecl_pure_def coerce_term_to_type_def
           dest!: elab_term_next_mv_monotone
           split: sum.splits prod.splits option.splits if_splits)

(* On success the pure helper returns env' = vardecl_add_local env ghost varName
   <some well-kinded (runtime in NotGhost) type>. We expose the type as an
   existential so callers get both the env shape and the well-kindedness facts. *)
lemma elab_vardecl_pure_env:
  assumes elab: "elab_vardecl_pure env elabEnv ghost loc varName tyOpt tm next_mv
                   = Inr (coreStmt, env', next_mv')"
    and wf: "tyenv_well_formed env"
    and ee_wf: "elabenv_well_formed env elabEnv"
    and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv"
  shows "\<exists>varTy. env' = vardecl_add_local env ghost varName varTy
                 \<and> is_well_kinded env varTy
                 \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env varTy)"
proof -
  have td_wf: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using ee_wf unfolding elabenv_well_formed_def by simp
  from elab obtain coreTm rhsTy nmv where
    etm: "elab_term env elabEnv ghost tm next_mv = Inr (coreTm, rhsTy, nmv)"
    by (auto simp: elab_vardecl_pure_def split: sum.splits prod.splits)
  show ?thesis
  proof (cases tyOpt)
    case None
    \<comment> \<open>Inferred type = rhsTy; the no-metavar check makes it well-kinded / runtime.\<close>
    from elab None etm have
      env'_eq: "env' = vardecl_add_local env ghost varName rhsTy" and
      no_meta: "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)"
      by (auto simp: elab_vardecl_pure_def split: sum.splits prod.splits if_splits)
    have wkrt: "is_well_kinded env rhsTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env rhsTy)"
      using elab_term_inferred_type_well_kinded_runtime[OF etm wf ee_wf bound no_meta] .
    show ?thesis using env'_eq wkrt by blast
  next
    case (Some ty)
    \<comment> \<open>Annotated: recorded type = elaborated annotation, which is well-kinded / runtime.\<close>
    from elab Some etm obtain coreTy where
      ety: "elab_type env elabEnv ghost ty = Inr coreTy" and
      env'_eq: "env' = vardecl_add_local env ghost varName coreTy"
      by (auto simp: elab_vardecl_pure_def coerce_term_to_type_def
               split: sum.splits prod.splits option.splits if_splits)
    have wk: "is_well_kinded env coreTy"
      using elab_type_is_well_kinded(1)[OF td_wf wf ety] .
    have rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env coreTy"
      using elab_type_notghost_is_runtime(1)[OF td_wf wf] ety by auto
    show ?thesis using env'_eq wk rt by blast
  qed
qed

(* elab_vardecl_pure emits a CoreStmt_VarDecl(Var) that typechecks in env. *)
lemma elab_vardecl_pure_correct:
  assumes elab: "elab_vardecl_pure env elabEnv ghost loc varName tyOpt tm next_mv
                   = Inr (coreStmt, env', next_mv')"
    and wf: "tyenv_well_formed env"
    and ee_wf: "elabenv_well_formed env elabEnv"
    and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv"
  shows "core_statement_type env ghost coreStmt = Some env'"
proof -
  have td_wf: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using ee_wf unfolding elabenv_well_formed_def by simp
  from elab obtain coreTm rhsTy where
    etm: "elab_term env elabEnv ghost tm next_mv = Inr (coreTm, rhsTy, next_mv')"
    by (auto simp: elab_vardecl_pure_def coerce_term_to_type_def
             split: sum.splits prod.splits option.splits if_splits)
  have coreTm_typed_decl:
    "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost coreTm = Some rhsTy"
    using elab_term_correct(1)[OF etm wf ee_wf] bound by simp
  show ?thesis
  proof (cases tyOpt)
    case None
    \<comment> \<open>Inferred: coreTy = rhsTy (metavar-free), initTm = clear_metavars coreTm.\<close>
    from elab None etm have
      no_meta: "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)" and
      cs_eq: "coreStmt = CoreStmt_VarDecl ghost varName Var rhsTy
                            (clear_metavars next_mv next_mv' coreTm)" and
      env'_eq: "env' = vardecl_add_local env ghost varName rhsTy"
      by (auto simp: elab_vardecl_pure_def split: sum.splits prod.splits if_splits)
    have wkrt: "is_well_kinded env rhsTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env rhsTy)"
      using elab_term_inferred_type_well_kinded_runtime[OF etm wf ee_wf bound no_meta] .
    have wk: "is_well_kinded env rhsTy" using wkrt by simp
    have rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env rhsTy" using wkrt by auto
    have rhsTy_below: "type_tyvars rhsTy \<subseteq> {n. n < next_mv}"
      using is_well_kinded_type_tyvars_subset[OF wk] bound by auto
    have init_typed: "core_term_type env ghost (clear_metavars next_mv next_mv' coreTm) = Some rhsTy"
      using clear_metavars_typed_in_env[OF coreTm_typed_decl wf bound rhsTy_below] .
    show ?thesis using wk rt init_typed by (simp add: cs_eq env'_eq vardecl_add_local_def)
  next
    case (Some ty)
    \<comment> \<open>Annotated: coreTy = elaborated annotation; rhs coerced to it (unify or int cast).\<close>
    from elab Some etm obtain coreTy where
      ety: "elab_type env elabEnv ghost ty = Inr coreTy"
      by (auto simp: elab_vardecl_pure_def split: sum.splits prod.splits option.splits)
    have wk: "is_well_kinded env coreTy"
      using elab_type_is_well_kinded(1)[OF td_wf wf ety] .
    have rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env coreTy"
      using elab_type_notghost_is_runtime(1)[OF td_wf wf] ety by auto
    have coreTy_below: "type_tyvars coreTy \<subseteq> {n. n < next_mv}"
      using is_well_kinded_type_tyvars_subset[OF wk] bound by auto
    from elab Some etm ety have
      env'_eq: "env' = vardecl_add_local env ghost varName coreTy"
      by (auto simp: elab_vardecl_pure_def coerce_term_to_type_def
               split: sum.splits prod.splits option.splits if_splits)
    \<comment> \<open>The coerced+cleared initializer typechecks to coreTy in env.\<close>
    let ?envD = "extend_env_with_tyvars env ghost next_mv next_mv'"
    let ?is_flex = "\<lambda>n. n |\<notin>| TE_TypeVars env"
    have wfD: "tyenv_well_formed ?envD"
      using wf tyenv_well_formed_extend_env_with_tyvars by blast
    have rhsTy_wk: "is_well_kinded ?envD rhsTy"
      using core_term_type_well_kinded[OF coreTm_typed_decl wfD] .
    have rhsTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type ?envD rhsTy"
      using core_term_type_notghost_runtime coreTm_typed_decl wfD by auto
    have coreTy_wkD: "is_well_kinded ?envD coreTy"
    proof -
      have "type_tyvars coreTy \<subseteq> fset (TE_TypeVars ?envD)"
        using is_well_kinded_type_tyvars_subset[OF wk]
        unfolding extend_env_with_tyvars_def by auto
      moreover have "TE_Datatypes ?envD = TE_Datatypes env"
        unfolding extend_env_with_tyvars_def by simp
      ultimately show ?thesis using is_well_kinded_transfer[OF wk] by blast
    qed
    have coreTy_rtD: "ghost = NotGhost \<longrightarrow> is_runtime_type ?envD coreTy"
    proof
      assume dng: "ghost = NotGhost"
      have "is_runtime_type env coreTy"
        using elab_type_notghost_is_runtime(1)[OF td_wf wf ety[unfolded dng]] dng by simp
      thus "is_runtime_type ?envD coreTy"
        using is_runtime_type_extend_runtime_tyvars dng
        unfolding extend_env_with_tyvars_def by fastforce
    qed
    have init_typed:
      "core_term_type env ghost
         (clear_metavars next_mv next_mv'
            (case unify ?is_flex rhsTy coreTy of
               Some subst \<Rightarrow> apply_subst_to_term subst coreTm
             | None \<Rightarrow> CoreTm_Cast coreTy coreTm)) = Some coreTy"
    proof (cases "unify ?is_flex rhsTy coreTy")
      case (Some subst)
      have subst_wk: "\<forall>ty' \<in> fmran' subst. is_well_kinded ?envD ty'"
        using unify_preserves_well_kinded[OF Some rhsTy_wk coreTy_wkD] .
      have subst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type ?envD ty')"
        using unify_preserves_runtime[OF Some] rhsTy_rt coreTy_rtD by blast
      have dom_flex: "\<forall>n. n |\<in>| fmdom subst \<longrightarrow> ?is_flex n"
        using unify_unify_list_dom_flex(1)[OF Some] .
      have envD_locals: "TE_LocalVars ?envD = TE_LocalVars env"
        unfolding extend_env_with_tyvars_def by simp
      have envD_ret: "TE_ReturnType ?envD = TE_ReturnType env"
        unfolding extend_env_with_tyvars_def by simp
      from flex_subst_identity_on_env[OF dom_flex wf envD_locals envD_ret]
      have locals_unaffected: "\<And>name ty'. fmlookup (TE_LocalVars ?envD) name = Some ty'
                                          \<Longrightarrow> apply_subst subst ty' = ty'"
        and ret_unaffected: "apply_subst subst (TE_ReturnType ?envD) = TE_ReturnType ?envD"
        by blast+
      have subst_typed: "core_term_type ?envD ghost (apply_subst_to_term subst coreTm)
                           = Some (apply_subst subst rhsTy)"
        using apply_subst_to_term_preserves_typing
                [OF coreTm_typed_decl wfD subst_wk subst_rt locals_unaffected ret_unaffected] .
      have coreTy_tvs: "type_tyvars coreTy \<subseteq> fset (TE_TypeVars env)"
        using is_well_kinded_type_tyvars_subset[OF wk] .
      have dom_disj: "type_tyvars coreTy \<inter> fset (fmdom subst) = {}"
        using dom_flex coreTy_tvs by auto
      have "apply_subst subst rhsTy = apply_subst subst coreTy"
        using unify_sound[OF Some] .
      also have "apply_subst subst coreTy = coreTy"
        using apply_subst_disjoint_id[OF dom_disj] .
      finally have subst_typed_coreTy:
        "core_term_type ?envD ghost (apply_subst_to_term subst coreTm) = Some coreTy"
        using subst_typed by simp
      show ?thesis
        using clear_metavars_typed_in_env[OF subst_typed_coreTy wf bound coreTy_below] Some by simp
    next
      case None
      have ints: "is_integer_type rhsTy \<and> is_integer_type coreTy"
        using elab etm ety None Some
        by (auto simp: elab_vardecl_pure_def coerce_term_to_type_def
                 split: sum.splits prod.splits option.splits if_splits)
      have cast_typed: "core_term_type ?envD ghost (CoreTm_Cast coreTy coreTm) = Some coreTy"
        using coreTm_typed_decl ints coreTy_wkD coreTy_rtD by auto
      show ?thesis
        using clear_metavars_typed_in_env[OF cast_typed wf bound coreTy_below] None by simp
    qed
    \<comment> \<open>The emitted statement is the cleared coerced term wrapped in CoreStmt_VarDecl.\<close>
    have cs_eq: "coreStmt = CoreStmt_VarDecl ghost varName Var coreTy
                   (clear_metavars next_mv next_mv'
                      (case unify ?is_flex rhsTy coreTy of
                         Some subst \<Rightarrow> apply_subst_to_term subst coreTm
                       | None \<Rightarrow> CoreTm_Cast coreTy coreTm))"
      using elab Some etm ety
      by (auto simp: elab_vardecl_pure_def coerce_term_to_type_def
               split: sum.splits prod.splits option.splits if_splits)
    show ?thesis using wk rt init_typed by (simp add: cs_eq env'_eq vardecl_add_local_def)
  qed
qed


(* ----- elab_vardecl_impure ----- *)

lemma elab_vardecl_impure_next_mv:
  "elab_vardecl_impure env elabEnv ghost loc varName tyOpt tm next_mv
     = Inr (coreStmt, env', next_mv') \<Longrightarrow> is_impure_call env elabEnv tm \<Longrightarrow> next_mv \<le> next_mv'"
  by (auto simp: elab_vardecl_impure_def is_impure_call_def reconcile_call_result_def Let_def
           dest!: elab_impure_call_term_next_mv
           split: BabTerm.splits sum.splits prod.splits option.splits if_splits)

(* On success the impure helper returns env' = vardecl_add_local env ghost
   varName varTy, with varTy well-kinded (runtime in NotGhost) — for the inferred
   branch via the no-metavar return type, for the annotated branch via elab_type. *)
lemma elab_vardecl_impure_env:
  assumes elab: "elab_vardecl_impure env elabEnv ghost loc varName tyOpt tm next_mv
                   = Inr (coreStmt, env', next_mv')"
    and impure: "is_impure_call env elabEnv tm"
    and wf: "tyenv_well_formed env"
    and ee_wf: "elabenv_well_formed env elabEnv"
    and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv"
  shows "\<exists>varTy. env' = vardecl_add_local env ghost varName varTy
                 \<and> is_well_kinded env varTy
                 \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env varTy)"
proof -
  have td_wf: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using ee_wf unfolding elabenv_well_formed_def by simp
  from impure obtain rloc callee rargs where
    tm_eq: "tm = BabTm_Call rloc callee rargs"
    by (auto simp: is_impure_call_def split: BabTerm.splits)
  from elab tm_eq obtain fnName finalTyArgs finalArgTms retTy nmv where
    ec: "elab_impure_call_term env elabEnv ghost rloc callee rargs next_mv
           = Inr (fnName, finalTyArgs, finalArgTms, retTy, nmv)"
    by (auto simp: elab_vardecl_impure_def split: sum.splits prod.splits)
  show ?thesis
  proof (cases tyOpt)
    case None
    \<comment> \<open>Inferred: recorded type = retTy, which is metavar-free by the check.\<close>
    from elab tm_eq ec None have
      env'_eq: "env' = vardecl_add_local env ghost varName retTy" and
      no_meta: "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list retTy)"
      by (auto simp: elab_vardecl_impure_def Let_def split: sum.splits prod.splits if_splits)
    have wkrt: "is_well_kinded env retTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env retTy)"
      using elab_impure_call_term_inferred_type_well_kinded_runtime
              [OF ec wf ee_wf bound no_meta] .
    show ?thesis using env'_eq wkrt by blast
  next
    case (Some ty)
    \<comment> \<open>Annotated: recorded type = elaborated annotation, well-kinded / runtime.\<close>
    from elab tm_eq ec Some obtain coreTy where
      ety: "elab_type env elabEnv ghost ty = Inr coreTy" and
      env'_eq: "env' = vardecl_add_local env ghost varName coreTy"
      by (auto simp: elab_vardecl_impure_def reconcile_call_result_def Let_def
               split: sum.splits prod.splits option.splits if_splits)
    have wk: "is_well_kinded env coreTy"
      using elab_type_is_well_kinded(1)[OF td_wf wf ety] .
    have rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env coreTy"
      using elab_type_notghost_is_runtime(1)[OF td_wf wf] ety by auto
    show ?thesis using env'_eq wk rt by blast
  qed
qed

(* elab_vardecl_impure emits a CoreStmt_VarDeclCall that typechecks in env.
   Three flavors: inferred (no annotation, varTy = call return type, no cast);
   annotated with unify-success (varTy = annotation, args substitution-applied, no
   cast); annotated with integer cast (varTy = annotation, castOpt = annotation). *)
lemma elab_vardecl_impure_correct:
  assumes elab: "elab_vardecl_impure env elabEnv ghost loc varName tyOpt tm next_mv
                   = Inr (coreStmt, env', next_mv')"
    and impure: "is_impure_call env elabEnv tm"
    and wf: "tyenv_well_formed env"
    and ee_wf: "elabenv_well_formed env elabEnv"
    and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv"
  shows "core_statement_type env ghost coreStmt = Some env'"
proof -
  let ?envE = "extend_env_with_tyvars env ghost next_mv next_mv'"
  let ?is_flex = "\<lambda>n. n |\<notin>| TE_TypeVars env"
  have td_wf: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using ee_wf unfolding elabenv_well_formed_def by simp
  \<comment> \<open>The fresh interval is above TE_RuntimeTypeVars env too (runtime tyvars \<subseteq> tyvars).\<close>
  have rtbound: "\<forall>n. n |\<in>| TE_RuntimeTypeVars env \<longrightarrow> n < next_mv"
    using wf bound unfolding tyenv_well_formed_def tyenv_runtime_tyvars_subset_def by blast
  \<comment> \<open>The impure rhs is a call; extract the elaborated call and its facts.\<close>
  from impure obtain rloc callee rargs where tm_eq: "tm = BabTm_Call rloc callee rargs"
    by (auto simp: is_impure_call_def split: BabTerm.splits)
  from elab tm_eq obtain fnName finalTyArgs finalArgTms retTy where
    ec: "elab_impure_call_term env elabEnv ghost rloc callee rargs next_mv
           = Inr (fnName, finalTyArgs, finalArgTms, retTy, next_mv')"
    by (auto simp: elab_vardecl_impure_def reconcile_call_result_def Let_def
             split: sum.splits prod.splits option.splits if_splits)
  \<comment> \<open>The call typechecks in the extended env.\<close>
  have ctE: "core_impure_call_type ?envE ghost fnName finalTyArgs finalArgTms = Some retTy"
    using elab_impure_call_term_correct[OF ec wf ee_wf bound] .
  have wfE: "tyenv_well_formed ?envE" using wf tyenv_well_formed_extend_env_with_tyvars by blast
  show ?thesis
  proof (cases tyOpt)
    case None
    \<comment> \<open>Inferred: varTy = retTy (metavar-free), castOpt = None, args as-is.\<close>
    from elab tm_eq ec None have
      no_meta: "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list retTy)" and
      cs_eq: "coreStmt = CoreStmt_VarDeclCall ghost varName retTy None fnName
                            (map (clear_metavars_type next_mv next_mv') finalTyArgs)
                            (map (clear_metavars next_mv next_mv') finalArgTms)" and
      env'_eq: "env' = vardecl_add_local env ghost varName retTy"
      by (auto simp: elab_vardecl_impure_def Let_def split: sum.splits prod.splits if_splits)
    have wkrt: "is_well_kinded env retTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env retTy)"
      using elab_impure_call_term_inferred_type_well_kinded_runtime[OF ec wf ee_wf bound no_meta] .
    have retTy_below: "type_tyvars retTy \<subseteq> {n. n < next_mv}"
      using is_well_kinded_type_tyvars_subset[OF conjunct1[OF wkrt]] bound by auto
    have ct: "core_impure_call_type env ghost fnName
                (map (clear_metavars_type next_mv next_mv') finalTyArgs)
                (map (clear_metavars next_mv next_mv') finalArgTms) = Some retTy"
      using clear_metavars_impure_call_typed_in_env[OF ctE wf bound rtbound retTy_below] .
    show ?thesis using wkrt ct
      by (simp add: cs_eq env'_eq vardecl_add_local_def cast_result_type_def)
  next
    case (Some ty)
    \<comment> \<open>Annotated: varTy = elaborated annotation; reconcile_call_result picks the cast.\<close>
    from elab tm_eq ec Some obtain coreTy castOpt tyArgs' argTms' where
      ety: "elab_type env elabEnv ghost ty = Inr coreTy" and
      rcr: "reconcile_call_result env loc finalTyArgs finalArgTms retTy coreTy
              = Inr (castOpt, tyArgs', argTms')" and
      cs_eq: "coreStmt = CoreStmt_VarDeclCall ghost varName coreTy castOpt fnName
                            (map (clear_metavars_type next_mv next_mv') tyArgs')
                            (map (clear_metavars next_mv next_mv') argTms')" and
      env'_eq: "env' = vardecl_add_local env ghost varName coreTy"
      by (auto simp: elab_vardecl_impure_def Let_def split: sum.splits prod.splits option.splits)
    have wk: "is_well_kinded env coreTy"
      using elab_type_is_well_kinded(1)[OF td_wf wf ety] .
    have rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env coreTy"
      using elab_type_notghost_is_runtime(1)[OF td_wf wf] ety by auto
    have coreTy_below: "type_tyvars coreTy \<subseteq> {n. n < next_mv}"
      using is_well_kinded_type_tyvars_subset[OF wk] bound by auto
    show ?thesis
    proof (cases "unify ?is_flex retTy coreTy")
      case (Some subst)
      \<comment> \<open>unify success: castOpt = None, tyArgs'/argTms' substitution-applied.\<close>
      from rcr Some have
        castOpt_eq: "castOpt = None" and
        tyArgs'_eq: "tyArgs' = map (apply_subst subst) finalTyArgs" and
        argTms'_eq: "argTms' = map (apply_subst_to_term subst) finalArgTms"
        by (auto simp: reconcile_call_result_def)
      \<comment> \<open>The substitution is flex-only with wk/runtime range in the extended env.\<close>
      have retTy_wkE: "is_well_kinded ?envE retTy"
        using core_impure_call_type_well_kinded_and_runtime[OF ctE wfE] by simp
      have retTy_rtE: "ghost = NotGhost \<longrightarrow> is_runtime_type ?envE retTy"
        using core_impure_call_type_well_kinded_and_runtime[OF ctE wfE] by simp
      have coreTy_wkE: "is_well_kinded ?envE coreTy"
      proof -
        have "type_tyvars coreTy \<subseteq> fset (TE_TypeVars ?envE)"
          using is_well_kinded_type_tyvars_subset[OF wk] unfolding extend_env_with_tyvars_def by auto
        moreover have "TE_Datatypes ?envE = TE_Datatypes env" unfolding extend_env_with_tyvars_def by simp
        ultimately show ?thesis using is_well_kinded_transfer[OF wk] by blast
      qed
      have coreTy_rtE: "ghost = NotGhost \<longrightarrow> is_runtime_type ?envE coreTy"
      proof
        assume ng: "ghost = NotGhost"
        have "is_runtime_type env coreTy"
          using elab_type_notghost_is_runtime(1)[OF td_wf wf ety[unfolded ng]] ng by simp
        thus "is_runtime_type ?envE coreTy"
          using is_runtime_type_extend_runtime_tyvars ng unfolding extend_env_with_tyvars_def by fastforce
      qed
      have subst_wk: "\<forall>ty' \<in> fmran' subst. is_well_kinded ?envE ty'"
        using unify_preserves_well_kinded[OF Some retTy_wkE coreTy_wkE] .
      have subst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type ?envE ty')"
        using unify_preserves_runtime[OF Some] retTy_rtE coreTy_rtE by blast
      have dom_flex: "\<forall>n. n |\<in>| fmdom subst \<longrightarrow> ?is_flex n"
        using unify_unify_list_dom_flex(1)[OF Some] .
      have envE_locals: "TE_LocalVars ?envE = TE_LocalVars env" unfolding extend_env_with_tyvars_def by simp
      have envE_ret: "TE_ReturnType ?envE = TE_ReturnType env" unfolding extend_env_with_tyvars_def by simp
      from flex_subst_identity_on_env[OF dom_flex wf envE_locals envE_ret]
      have locals_unaffected: "\<And>name ty'. fmlookup (TE_LocalVars ?envE) name = Some ty'
                                          \<Longrightarrow> apply_subst subst ty' = ty'"
        and ret_unaffected: "apply_subst subst (TE_ReturnType ?envE) = TE_ReturnType ?envE"
        by blast+
      \<comment> \<open>The substituted call typechecks (in extended env) to apply_subst subst retTy = coreTy.\<close>
      have ctE': "core_impure_call_type ?envE ghost fnName tyArgs' argTms' = Some (apply_subst subst retTy)"
        using apply_subst_core_impure_call_type[OF ctE wfE subst_wk subst_rt locals_unaffected ret_unaffected]
        unfolding tyArgs'_eq argTms'_eq .
      have coreTy_tvs: "type_tyvars coreTy \<subseteq> fset (TE_TypeVars env)"
        using is_well_kinded_type_tyvars_subset[OF wk] .
      have "apply_subst subst retTy = apply_subst subst coreTy" using unify_sound[OF Some] .
      also have "apply_subst subst coreTy = coreTy"
        using apply_subst_disjoint_id dom_flex coreTy_tvs by auto
      finally have ret_is_coreTy: "apply_subst subst retTy = coreTy" .
      \<comment> \<open>coreTy is metavar-free, so the clearing bridge applies.\<close>
      have ct: "core_impure_call_type env ghost fnName
                  (map (clear_metavars_type next_mv next_mv') tyArgs')
                  (map (clear_metavars next_mv next_mv') argTms') = Some coreTy"
        using clear_metavars_impure_call_typed_in_env[OF ctE'[unfolded ret_is_coreTy] wf bound rtbound coreTy_below] .
      show ?thesis using wk rt ct
        by (simp add: cs_eq env'_eq castOpt_eq vardecl_add_local_def cast_result_type_def)
    next
      case None
      \<comment> \<open>integer cast: castOpt = Some coreTy, args unchanged; retTy/coreTy both integers.\<close>
      from rcr None have
        ints: "is_integer_type retTy \<and> is_integer_type coreTy" and
        castOpt_eq: "castOpt = Some coreTy" and
        tyArgs'_eq: "tyArgs' = finalTyArgs" and
        argTms'_eq: "argTms' = finalArgTms"
        by (auto simp: reconcile_call_result_def split: if_splits)
      \<comment> \<open>An integer return type is metavar-free, so the clearing bridge applies.\<close>
      have retTy_below: "type_tyvars retTy \<subseteq> {n. n < next_mv}"
        using ints by (cases retTy) auto
      have ct: "core_impure_call_type env ghost fnName
                  (map (clear_metavars_type next_mv next_mv') tyArgs')
                  (map (clear_metavars next_mv next_mv') argTms') = Some retTy"
        using clear_metavars_impure_call_typed_in_env[OF ctE wf bound rtbound retTy_below]
        unfolding tyArgs'_eq argTms'_eq .
      \<comment> \<open>cast_result_type for the integer cast: retTy and coreTy integers, coreTy runtime in NotGhost.\<close>
      have cast_ok: "cast_result_type env ghost retTy (Some coreTy) = Some coreTy"
        using ints rt by (simp add: cast_result_type_def)
      show ?thesis using wk rt ct cast_ok
        by (simp add: cs_eq env'_eq castOpt_eq vardecl_add_local_def)
    qed
  qed
qed


(* ----- elab_vardecl_ref ----- *)

lemma elab_vardecl_ref_next_mv:
  "elab_vardecl_ref env elabEnv ghost loc varName tmOpt next_mv
     = Inr (coreStmt, env', next_mv') \<Longrightarrow> next_mv \<le> next_mv'"
  by (auto simp: elab_vardecl_ref_def
           dest!: elab_term_next_mv_monotone
           split: sum.splits prod.splits option.splits if_splits)

(* On success the ref helper returns env' = (vardecl_add_local \<dots>) with the const
   field overridden — still of the well-formed-preserving shape. *)
lemma elab_vardecl_ref_env:
  assumes elab: "elab_vardecl_ref env elabEnv ghost loc varName tmOpt next_mv
                   = Inr (coreStmt, env', next_mv')"
    and wf: "tyenv_well_formed env"
    and ee_wf: "elabenv_well_formed env elabEnv"
    and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv"
  shows "\<exists>varTy c. env' = (vardecl_add_local env ghost varName varTy) \<lparr> TE_ConstLocals := c \<rparr>
                 \<and> is_well_kinded env varTy
                 \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env varTy)"
proof -
  from elab obtain tm coreTm rhsTy nmv where
    tm_eq: "tmOpt = Some tm" and
    etm: "elab_term env elabEnv ghost tm next_mv = Inr (coreTm, rhsTy, nmv)" and
    no_meta: "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)" and
    env'_eq: "env' = (vardecl_add_local env ghost varName rhsTy)
                       \<lparr> TE_ConstLocals := (if is_writable_lvalue env coreTm
                                            then fminus (TE_ConstLocals env) {|varName|}
                                            else finsert varName (TE_ConstLocals env)) \<rparr>"
    by (auto simp: elab_vardecl_ref_def vardecl_add_local_def
             split: sum.splits prod.splits option.splits if_splits)
  have wkrt: "is_well_kinded env rhsTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env rhsTy)"
    using elab_term_inferred_type_well_kinded_runtime[OF etm wf ee_wf bound no_meta] .
  show ?thesis using env'_eq wkrt by blast
qed

(* elab_vardecl_ref emits a CoreStmt_VarDecl(Ref) that typechecks in env. *)
lemma elab_vardecl_ref_correct:
  assumes elab: "elab_vardecl_ref env elabEnv ghost loc varName tmOpt next_mv
                   = Inr (coreStmt, env', next_mv')"
    and wf: "tyenv_well_formed env"
    and ee_wf: "elabenv_well_formed env elabEnv"
    and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv"
  shows "core_statement_type env ghost coreStmt = Some env'"
proof -
  from elab obtain tm coreTm rhsTy where
    tm_eq: "tmOpt = Some tm" and
    etm: "elab_term env elabEnv ghost tm next_mv = Inr (coreTm, rhsTy, next_mv')" and
    lv: "is_lvalue coreTm" and
    no_meta: "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)" and
    cs_eq: "coreStmt = CoreStmt_VarDecl ghost varName Ref rhsTy
                          (clear_metavars next_mv next_mv' coreTm)" and
    env'_eq: "env' = (vardecl_add_local env ghost varName rhsTy)
                       \<lparr> TE_ConstLocals := (if is_writable_lvalue env coreTm
                                            then fminus (TE_ConstLocals env) {|varName|}
                                            else finsert varName (TE_ConstLocals env)) \<rparr>"
    by (auto simp: elab_vardecl_ref_def vardecl_add_local_def
             split: sum.splits prod.splits option.splits if_splits)
  have wkrt: "is_well_kinded env rhsTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env rhsTy)"
    using elab_term_inferred_type_well_kinded_runtime[OF etm wf ee_wf bound no_meta] .
  have wk: "is_well_kinded env rhsTy" using wkrt by simp
  have rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env rhsTy" using wkrt by auto
  have rhsTy_below: "type_tyvars rhsTy \<subseteq> {n. n < next_mv}"
    using is_well_kinded_type_tyvars_subset[OF wk] bound by auto
  have coreTm_typed_decl:
    "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost coreTm = Some rhsTy"
    using elab_term_correct(1)[OF etm wf ee_wf] bound by simp
  have init_typed: "core_term_type env ghost (clear_metavars next_mv next_mv' coreTm) = Some rhsTy"
    using clear_metavars_typed_in_env[OF coreTm_typed_decl wf bound rhsTy_below] .
  have lv': "is_lvalue (clear_metavars next_mv next_mv' coreTm)"
    using lv unfolding clear_metavars_def by simp
  have wl_eq: "is_writable_lvalue env (clear_metavars next_mv next_mv' coreTm)
                 = is_writable_lvalue env coreTm"
    unfolding clear_metavars_def by simp
  show ?thesis using wk rt lv' init_typed wl_eq by (simp add: cs_eq env'_eq vardecl_add_local_def)
qed


(* ----- Assign branch helpers ----- *)

(* The pure helper advances the counter (from next_mv1, via elab_term) and
   leaves the env unchanged. *)
lemma elab_assign_pure_next_mv:
  "elab_assign_pure env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1
     = Inr (coreStmt, env', next_mv') \<Longrightarrow> next_mv1 \<le> next_mv'"
  by (auto simp: elab_assign_pure_def coerce_term_to_type_def
           dest!: elab_term_next_mv_monotone
           split: sum.splits prod.splits option.splits if_splits)

lemma elab_assign_pure_env:
  "elab_assign_pure env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1
     = Inr (coreStmt, env', next_mv') \<Longrightarrow> env' = env"
  by (auto simp: elab_assign_pure_def coerce_term_to_type_def
           split: sum.splits prod.splits option.splits if_splits)

(* elab_assign_pure emits a CoreStmt_Assign that typechecks in env. The lhs term
   (elaborated at next_mv, output next_mv1, a writable lvalue of the metavar-free
   type lhsTy) is widened to next_mv2 and cleared; the rhs is coerced to lhsTy. *)
lemma elab_assign_pure_correct:
  assumes elab: "elab_assign_pure env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1
                   = Inr (coreStmt, env', next_mv')"
    and lhs_typed: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv1) ghost lhsTm = Some lhsTy"
    and lhs_wl: "is_writable_lvalue env lhsTm"
    and lhs_below: "type_tyvars lhsTy \<subseteq> {n. n < next_mv}"
    and mono_lhs: "next_mv \<le> next_mv1"
    and wf: "tyenv_well_formed env"
    and ee_wf: "elabenv_well_formed env elabEnv"
    and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv"
  shows "core_statement_type env ghost coreStmt = Some env'"
proof -
  let ?is_flex = "\<lambda>n. n |\<notin>| TE_TypeVars env"
  from elab obtain rhsTm rhsTy rhsTm' where
    erhs: "elab_term env elabEnv ghost rhs next_mv1 = Inr (rhsTm, rhsTy, next_mv')" and
    coerce: "coerce_term_to_type env loc rhsTm rhsTy lhsTy = Inr rhsTm'" and
    cs_eq: "coreStmt = CoreStmt_Assign ghost
                          (clear_metavars next_mv next_mv' lhsTm)
                          (clear_metavars next_mv next_mv' rhsTm')" and
    env'_eq: "env' = env"
    by (auto simp: elab_assign_pure_def split: sum.splits prod.splits)
  let ?envD = "extend_env_with_tyvars env ghost next_mv next_mv'"
  have wfD: "tyenv_well_formed ?envD" using wf tyenv_well_formed_extend_env_with_tyvars by blast
  have mono_rhs: "next_mv1 \<le> next_mv'" using elab_term_next_mv_monotone[OF erhs] .
  \<comment> \<open>lhs: widen to next_mv', clear (lhsTy metavar-free), preserve writability.\<close>
  have lhs_typedD: "core_term_type ?envD ghost lhsTm = Some lhsTy"
    using core_term_type_extend_env_with_tyvars_mono[OF lhs_typed le_refl mono_rhs] .
  have lhs_init: "core_term_type env ghost (clear_metavars next_mv next_mv' lhsTm) = Some lhsTy"
    using clear_metavars_typed_in_env[OF lhs_typedD wf bound lhs_below] .
  have lhs_wl': "is_writable_lvalue env (clear_metavars next_mv next_mv' lhsTm)"
    using lhs_wl unfolding clear_metavars_def by simp
  \<comment> \<open>rhs: typed at extend env next_mv next_mv' (widen from next_mv1), then coerced
      to lhsTy and cleared — identical to elab_vardecl_pure_correct's annotated branch.\<close>
  have rhs_typed1: "core_term_type (extend_env_with_tyvars env ghost next_mv1 next_mv') ghost rhsTm = Some rhsTy"
    using elab_term_correct(1)[OF erhs wf ee_wf] bound mono_lhs order_less_le_trans by auto
  have coreTm_typed_decl: "core_term_type ?envD ghost rhsTm = Some rhsTy"
    using core_term_type_extend_env_with_tyvars_mono[OF rhs_typed1 mono_lhs le_refl] .
  have rhsTy_wk: "is_well_kinded ?envD rhsTy"
    using core_term_type_well_kinded[OF coreTm_typed_decl wfD] .
  have rhsTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type ?envD rhsTy"
    using core_term_type_notghost_runtime coreTm_typed_decl wfD by auto
  \<comment> \<open>lhsTy is well-kinded / runtime in ?envD (it is metavar-free and typed by the lhs).\<close>
  have lhsTy_wk: "is_well_kinded env lhsTy"
    using core_term_type_well_kinded lhs_init local.wf by blast
  have lhsTy_wkD: "is_well_kinded ?envD lhsTy"
    using core_term_type_well_kinded[OF lhs_typedD wfD] .
  have lhsTy_rtD: "ghost = NotGhost \<longrightarrow> is_runtime_type ?envD lhsTy"
    using core_term_type_notghost_runtime lhs_typedD wfD by auto
  have rhs_init: "core_term_type env ghost (clear_metavars next_mv next_mv' rhsTm') = Some lhsTy"
  proof (cases "unify ?is_flex rhsTy lhsTy")
    case (Some subst)
    from coerce Some have rhsTm'_eq: "rhsTm' = apply_subst_to_term subst rhsTm"
      by (simp add: coerce_term_to_type_def)
    have subst_wk: "\<forall>ty' \<in> fmran' subst. is_well_kinded ?envD ty'"
      using unify_preserves_well_kinded[OF Some rhsTy_wk lhsTy_wkD] .
    have subst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type ?envD ty')"
      using unify_preserves_runtime[OF Some] rhsTy_rt lhsTy_rtD by blast
    have dom_flex: "\<forall>n. n |\<in>| fmdom subst \<longrightarrow> ?is_flex n"
      using unify_unify_list_dom_flex(1)[OF Some] .
    have envD_locals: "TE_LocalVars ?envD = TE_LocalVars env" unfolding extend_env_with_tyvars_def by simp
    have envD_ret: "TE_ReturnType ?envD = TE_ReturnType env" unfolding extend_env_with_tyvars_def by simp
    from flex_subst_identity_on_env[OF dom_flex wf envD_locals envD_ret]
    have locals_unaffected: "\<And>name ty'. fmlookup (TE_LocalVars ?envD) name = Some ty'
                                        \<Longrightarrow> apply_subst subst ty' = ty'"
      and ret_unaffected: "apply_subst subst (TE_ReturnType ?envD) = TE_ReturnType ?envD" by blast+
    have subst_typed: "core_term_type ?envD ghost (apply_subst_to_term subst rhsTm) = Some (apply_subst subst rhsTy)"
      using apply_subst_to_term_preserves_typing
              [OF coreTm_typed_decl wfD subst_wk subst_rt locals_unaffected ret_unaffected] .
    have lhsTy_tvs: "type_tyvars lhsTy \<subseteq> fset (TE_TypeVars env)" using lhs_below bound
      using is_well_kinded_type_tyvars_subset lhsTy_wk by auto
    have dom_disj: "type_tyvars lhsTy \<inter> fset (fmdom subst) = {}" using dom_flex lhsTy_tvs by auto
    have "apply_subst subst rhsTy = apply_subst subst lhsTy" using unify_sound[OF Some] .
    also have "apply_subst subst lhsTy = lhsTy" using apply_subst_disjoint_id[OF dom_disj] .
    finally have "core_term_type ?envD ghost (apply_subst_to_term subst rhsTm) = Some lhsTy"
      using subst_typed by simp
    thus ?thesis using clear_metavars_typed_in_env[OF _ wf bound lhs_below] rhsTm'_eq by simp
  next
    case None
    from coerce None have ints: "is_integer_type rhsTy \<and> is_integer_type lhsTy" and rhsTm'_eq: "rhsTm' = CoreTm_Cast lhsTy rhsTm"
      by (auto simp: coerce_term_to_type_def split: if_splits)
    have cast_typed: "core_term_type ?envD ghost (CoreTm_Cast lhsTy rhsTm) = Some lhsTy"
      using coreTm_typed_decl ints lhsTy_wkD lhsTy_rtD by auto
    thus ?thesis using clear_metavars_typed_in_env[OF cast_typed wf bound lhs_below] rhsTm'_eq by simp
  qed
  show ?thesis using lhs_wl' lhs_init rhs_init by (simp add: cs_eq env'_eq)
qed

(* The impure helper is only reached for an is_impure_call rhs (forces rhs to be
   a BabTm_Call); it advances the counter (from next_mv1) and leaves env unchanged. *)
lemma elab_assign_impure_next_mv:
  "elab_assign_impure env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1
     = Inr (coreStmt, env', next_mv') \<Longrightarrow> is_impure_call env elabEnv rhs \<Longrightarrow> next_mv1 \<le> next_mv'"
  by (auto simp: elab_assign_impure_def is_impure_call_def reconcile_call_result_def Let_def
           dest!: elab_impure_call_term_next_mv
           split: BabTerm.splits sum.splits prod.splits option.splits if_splits)

lemma elab_assign_impure_env:
  "elab_assign_impure env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1
     = Inr (coreStmt, env', next_mv') \<Longrightarrow> is_impure_call env elabEnv rhs \<Longrightarrow> env' = env"
  by (auto simp: elab_assign_impure_def is_impure_call_def reconcile_call_result_def Let_def
           split: BabTerm.splits sum.splits prod.splits option.splits if_splits)

(* elab_assign_impure emits a CoreStmt_AssignCall that typechecks in env. The lhs is
   handled as in elab_assign_pure; the impure rhs reconciles to lhsTy via the same
   path as elab_vardecl_impure_correct (unify-then-subst or integer cast). *)
lemma elab_assign_impure_correct:
  assumes elab: "elab_assign_impure env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1
                   = Inr (coreStmt, env', next_mv')"
    and impure: "is_impure_call env elabEnv rhs"
    and lhs_typed: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv1) ghost lhsTm = Some lhsTy"
    and lhs_wl: "is_writable_lvalue env lhsTm"
    and lhs_below: "type_tyvars lhsTy \<subseteq> {n. n < next_mv}"
    and mono_lhs: "next_mv \<le> next_mv1"
    and wf: "tyenv_well_formed env"
    and ee_wf: "elabenv_well_formed env elabEnv"
    and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv"
  shows "core_statement_type env ghost coreStmt = Some env'"
proof -
  let ?is_flex = "\<lambda>n. n |\<notin>| TE_TypeVars env"
  have rtbound: "\<forall>n. n |\<in>| TE_RuntimeTypeVars env \<longrightarrow> n < next_mv"
    using wf bound unfolding tyenv_well_formed_def tyenv_runtime_tyvars_subset_def by blast
  from impure obtain rloc callee rargs where rhs_eq: "rhs = BabTm_Call rloc callee rargs"
    by (auto simp: is_impure_call_def split: BabTerm.splits)
  from elab rhs_eq obtain fnName finalTyArgs finalArgTms retTy castOpt tyArgs' argTms' where
    ec: "elab_impure_call_term env elabEnv ghost rloc callee rargs next_mv1
           = Inr (fnName, finalTyArgs, finalArgTms, retTy, next_mv')" and
    rcr: "reconcile_call_result env loc finalTyArgs finalArgTms retTy lhsTy
            = Inr (castOpt, tyArgs', argTms')" and
    cs_eq: "coreStmt = CoreStmt_AssignCall ghost (clear_metavars next_mv next_mv' lhsTm) castOpt fnName
                          (map (clear_metavars_type next_mv next_mv') tyArgs')
                          (map (clear_metavars next_mv next_mv') argTms')" and
    env'_eq: "env' = env"
    by (auto simp: elab_assign_impure_def split: sum.splits prod.splits)
  let ?envE = "extend_env_with_tyvars env ghost next_mv next_mv'"
  have wfE: "tyenv_well_formed ?envE" using wf tyenv_well_formed_extend_env_with_tyvars by blast
  have mono_rhs: "next_mv1 \<le> next_mv'" using elab_impure_call_term_next_mv[OF ec] .
  \<comment> \<open>lhs: widen to next_mv', clear, preserve writability + typing to lhsTy.\<close>
  have lhs_typedE: "core_term_type ?envE ghost lhsTm = Some lhsTy"
    using core_term_type_extend_env_with_tyvars_mono[OF lhs_typed le_refl mono_rhs] .
  have lhs_init: "core_term_type env ghost (clear_metavars next_mv next_mv' lhsTm) = Some lhsTy"
    using clear_metavars_typed_in_env[OF lhs_typedE wf bound lhs_below] .
  have lhs_wl': "is_writable_lvalue env (clear_metavars next_mv next_mv' lhsTm)"
    using lhs_wl unfolding clear_metavars_def by simp
  \<comment> \<open>The call typechecks (extended env), via elab_impure_call_term_correct at next_mv1.\<close>
  have ec_fresh: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv1" using bound mono_lhs by fastforce
  have ctE1: "core_impure_call_type (extend_env_with_tyvars env ghost next_mv1 next_mv') ghost fnName finalTyArgs finalArgTms = Some retTy"
    using elab_impure_call_term_correct[OF ec wf ee_wf ec_fresh] .
  have ctE: "core_impure_call_type ?envE ghost fnName finalTyArgs finalArgTms = Some retTy"
    using core_impure_call_type_extend_env_with_tyvars_mono ctE1 mono_lhs by blast
  \<comment> \<open>lhsTy well-kinded / runtime (metavar-free, typed by the lhs).\<close>
  have lhsTy_wkE: "is_well_kinded ?envE lhsTy" using core_term_type_well_kinded[OF lhs_typedE wfE] .
  have lhsTy_rtE: "ghost = NotGhost \<longrightarrow> is_runtime_type ?envE lhsTy"
    using core_term_type_notghost_runtime lhs_typedE wfE by auto
  show ?thesis
  proof (cases "unify ?is_flex retTy lhsTy")
    case (Some subst)
    \<comment> \<open>unify success: castOpt = None, args substitution-applied; call types to lhsTy.\<close>
    from rcr Some have castOpt_eq: "castOpt = None" and
      tyArgs'_eq: "tyArgs' = map (apply_subst subst) finalTyArgs" and
      argTms'_eq: "argTms' = map (apply_subst_to_term subst) finalArgTms"
      by (auto simp: reconcile_call_result_def)
    have retTy_wkE: "is_well_kinded ?envE retTy"
      using core_impure_call_type_well_kinded_and_runtime[OF ctE wfE] by simp
    have retTy_rtE: "ghost = NotGhost \<longrightarrow> is_runtime_type ?envE retTy"
      using core_impure_call_type_well_kinded_and_runtime[OF ctE wfE] by simp
    have subst_wk: "\<forall>ty' \<in> fmran' subst. is_well_kinded ?envE ty'"
      using unify_preserves_well_kinded[OF Some retTy_wkE lhsTy_wkE] .
    have subst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type ?envE ty')"
      using unify_preserves_runtime[OF Some] retTy_rtE lhsTy_rtE by blast
    have dom_flex: "\<forall>n. n |\<in>| fmdom subst \<longrightarrow> ?is_flex n" using unify_unify_list_dom_flex(1)[OF Some] .
    have envE_locals: "TE_LocalVars ?envE = TE_LocalVars env" unfolding extend_env_with_tyvars_def by simp
    have envE_ret: "TE_ReturnType ?envE = TE_ReturnType env" unfolding extend_env_with_tyvars_def by simp
    from flex_subst_identity_on_env[OF dom_flex wf envE_locals envE_ret]
    have locals_unaffected: "\<And>name ty'. fmlookup (TE_LocalVars ?envE) name = Some ty'
                                        \<Longrightarrow> apply_subst subst ty' = ty'"
      and ret_unaffected: "apply_subst subst (TE_ReturnType ?envE) = TE_ReturnType ?envE" by blast+
    have ctE': "core_impure_call_type ?envE ghost fnName tyArgs' argTms' = Some (apply_subst subst retTy)"
      using apply_subst_core_impure_call_type[OF ctE wfE subst_wk subst_rt locals_unaffected ret_unaffected]
      unfolding tyArgs'_eq argTms'_eq .
    have lhsTy_tvs: "type_tyvars lhsTy \<subseteq> fset (TE_TypeVars env)"
      using core_term_type_well_kinded_and_runtime is_well_kinded_type_tyvars_subset lhs_init
        local.wf by blast
    have "apply_subst subst retTy = apply_subst subst lhsTy" using unify_sound[OF Some] .
    also have "apply_subst subst lhsTy = lhsTy"
      using apply_subst_disjoint_id dom_flex lhsTy_tvs by blast
    finally have ret_is_lhsTy: "apply_subst subst retTy = lhsTy" .
    have ct: "core_impure_call_type env ghost fnName
                (map (clear_metavars_type next_mv next_mv') tyArgs')
                (map (clear_metavars next_mv next_mv') argTms') = Some lhsTy"
      using clear_metavars_impure_call_typed_in_env[OF ctE'[unfolded ret_is_lhsTy] wf bound rtbound lhs_below] .
    show ?thesis using lhs_wl' lhs_init ct
      by (simp add: cs_eq env'_eq castOpt_eq cast_result_type_def)
  next
    case None
    \<comment> \<open>integer cast: castOpt = Some lhsTy, args unchanged; retTy/lhsTy both integers.\<close>
    from rcr None have ints: "is_integer_type retTy \<and> is_integer_type lhsTy" and
      castOpt_eq: "castOpt = Some lhsTy" and tyArgs'_eq: "tyArgs' = finalTyArgs" and argTms'_eq: "argTms' = finalArgTms"
      by (auto simp: reconcile_call_result_def split: if_splits)
    have retTy_below: "type_tyvars retTy \<subseteq> {n. n < next_mv}" using ints by (cases retTy) auto
    have ct: "core_impure_call_type env ghost fnName
                (map (clear_metavars_type next_mv next_mv') tyArgs')
                (map (clear_metavars next_mv next_mv') argTms') = Some retTy"
      using clear_metavars_impure_call_typed_in_env[OF ctE wf bound rtbound retTy_below]
      unfolding tyArgs'_eq argTms'_eq .
    have lhsTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env lhsTy"
      using core_term_type_notghost_runtime lhs_init local.wf by auto
    have cast_ok: "cast_result_type env ghost retTy (Some lhsTy) = Some lhsTy"
      using ints lhsTy_rt by (simp add: cast_result_type_def)
    show ?thesis using lhs_wl' lhs_init ct cast_ok
      by (simp add: cs_eq env'_eq castOpt_eq)
  qed
qed


(* ========================================================================== *)
(* elab_statement monotonicity, well-formedness preservation, etc. *)
(* ========================================================================== *)

(* Monotonicity of the metavariable counter: elaboration only advances it. *)
lemma elab_statement_next_mv_monotone:
  "elab_statement env elabEnv ghost stmt next_mv = Inr (coreStmt, env', next_mv')
     \<Longrightarrow> next_mv \<le> next_mv'"
and elab_statement_list_next_mv_monotone:
  "elab_statement_list env elabEnv ghost stmts next_mv = Inr (coreStmts, env', next_mv')
     \<Longrightarrow> next_mv \<le> next_mv'"
proof (induction env elabEnv ghost stmt next_mv and env elabEnv ghost stmts next_mv
       arbitrary: coreStmt env' next_mv' and coreStmts env' next_mv'
       rule: elab_statement_elab_statement_list.induct)
  \<comment> \<open>VarDecl: each successful branch either keeps next_mv (default-init) or advances
      it via one of the three helpers.\<close>
  case (1 env elabEnv ghost loc varName vorf tyOpt tmOpt next_mv)
  show ?case
  proof (cases vorf)
    case Var
    consider (none) "tyOpt = None \<and> tmOpt = None"
      | (default) ty where "tyOpt = Some ty \<and> tmOpt = None"
      | (init) tm where "tmOpt = Some tm"
      by (cases tyOpt; cases tmOpt) auto
    thus ?thesis
    proof cases
      case none thus ?thesis using "1.prems" Var by simp
    next
      case default thus ?thesis using "1.prems" Var by (auto split: sum.splits)
    next
      case init
      show ?thesis
      proof (cases "is_impure_call env elabEnv tm")
        case True
        with "1.prems" Var init
        have "elab_vardecl_impure env elabEnv ghost loc varName tyOpt tm next_mv
                = Inr (coreStmt, env', next_mv')" by (simp split: option.splits)
        thus ?thesis using elab_vardecl_impure_next_mv[OF _ True] by simp
      next
        case False
        with "1.prems" Var init
        have "elab_vardecl_pure env elabEnv ghost loc varName tyOpt tm next_mv
                = Inr (coreStmt, env', next_mv')" by (simp split: option.splits)
        thus ?thesis using elab_vardecl_pure_next_mv by simp
      qed
    qed
  next
    case Ref
    thus ?thesis using "1.prems" by (auto dest!: elab_vardecl_ref_next_mv)
  qed
next
  case (2 env elabEnv ghost loc varName ty next_mv) thus ?case sorry  \<comment> \<open>Fix (unimplemented)\<close>
next
  \<comment> \<open>Obtain: next_mv advances only via the predicate's elab_term (elab_type and
      the unify do not touch the counter).\<close>
  case (3 env elabEnv ghost loc varName ty tm next_mv)
  show ?case
    using "3.prems"
    by (auto simp: Let_def dest!: elab_term_next_mv_monotone
             split: sum.splits prod.splits option.splits if_splits)
next
  case (4 env elabEnv ghost loc tm next_mv) thus ?case sorry  \<comment> \<open>Use\<close>
next
  \<comment> \<open>Assign: the lhs elaboration advances next_mv to next_mv1, then the chosen
      helper advances next_mv1 to next_mv'.\<close>
  case (5 env elabEnv ghost loc lhs rhs next_mv)
  from "5.prems" obtain lhsTm lhsTy next_mv1 where
    lhs_elab: "elab_term env elabEnv ghost lhs next_mv = Inr (lhsTm, lhsTy, next_mv1)"
    by (auto split: sum.splits prod.splits)
  have mono_lhs: "next_mv \<le> next_mv1" using elab_term_next_mv_monotone[OF lhs_elab] .
  show ?case
  proof (cases "is_impure_call env elabEnv rhs")
    case True
    with "5.prems" lhs_elab
    have "elab_assign_impure env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1
            = Inr (coreStmt, env', next_mv')"
      by (auto split: if_splits)
    thus ?thesis using mono_lhs elab_assign_impure_next_mv[OF _ True] by fastforce
  next
    case False
    with "5.prems" lhs_elab
    have "elab_assign_pure env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1
            = Inr (coreStmt, env', next_mv')"
      by (auto split: if_splits)
    thus ?thesis using mono_lhs elab_assign_pure_next_mv by fastforce
  qed
next
  case (6 env elabEnv ghost loc lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Swap\<close>
next
  case (7 env elabEnv ghost loc tmOpt next_mv) thus ?case sorry  \<comment> \<open>Return\<close>
next
  \<comment> \<open>Assert: in the "assert *" branch the counter advances only via the proof-body
      list elaboration; in the "assert cond" branch via the condition's elab_term then
      the proof-body list. Both list recursions are covered by the mutual IH.\<close>
  case (8 env elabEnv ghost loc condOpt proofBody next_mv)
  show ?case
  proof (cases condOpt)
    case None
    with "8.prems" obtain coreBody benv where
      goal: "TE_ProofGoal env \<noteq> None" and
      body: "elab_statement_list (env \<lparr> TE_ProofTopLevel := True \<rparr>) elabEnv Ghost proofBody next_mv
               = Inr (coreBody, benv, next_mv')"
      by (auto simp: Let_def split: if_splits sum.splits prod.splits)
    from goal have goal': "\<exists>y. TE_ProofGoal env = Some y" by auto
    show ?thesis using "8.IH"(1)[OF None] goal' body by simp
  next
    case (Some cond)
    with "8.prems" obtain coreCond condTy next_mv1 subst coreBody benv where
      etm: "elab_term env elabEnv Ghost cond next_mv = Inr (coreCond, condTy, next_mv1)" and
      unif: "unify (\<lambda>n. n |\<notin>| TE_TypeVars env) condTy CoreTy_Bool = Some subst" and
      body: "elab_statement_list
               (env \<lparr> TE_ProofGoal := Some (clear_metavars next_mv next_mv1
                                              (apply_subst_to_term subst coreCond)),
                      TE_ProofTopLevel := True \<rparr>)
               elabEnv Ghost proofBody next_mv1 = Inr (coreBody, benv, next_mv')"
      by (auto simp: Let_def split: sum.splits prod.splits option.splits)
    have mono1: "next_mv \<le> next_mv1" using elab_term_next_mv_monotone[OF etm] .
    have mono2: "next_mv1 \<le> next_mv'"
      using "8.IH"(2) Some etm unif body by simp
    from mono1 mono2 show ?thesis by simp
  qed
next
  \<comment> \<open>Assume: next_mv advances via elab_term.\<close>
  case (9 env elabEnv ghost loc tm next_mv)
  show ?case
    using "9.prems"
    by (auto dest!: elab_term_next_mv_monotone split: sum.splits prod.splits option.splits if_splits)
next
  case (10 env elabEnv ghost loc cond thenB elseB next_mv) thus ?case sorry  \<comment> \<open>If\<close>
next
  case (11 env elabEnv ghost loc cond attrs body next_mv) thus ?case sorry  \<comment> \<open>While\<close>
next
  case (12 env elabEnv ghost loc tm next_mv) thus ?case sorry  \<comment> \<open>Call\<close>
next
  case (13 env elabEnv ghost loc scrut arms next_mv) thus ?case sorry  \<comment> \<open>Match\<close>
next
  \<comment> \<open>ShowHide: next_mv unchanged.\<close>
  case (14 env elabEnv ghost loc sh name next_mv)
  from "14.prems" show ?case by simp
next
  \<comment> \<open>Ghost wrapper: re-elaborates inner in Ghost mode; next_mv advances per the IH.\<close>
  case (15 env elabEnv ghost loc inner next_mv)
  have inner_elab: "elab_statement env elabEnv Ghost inner next_mv = Inr (coreStmt, env', next_mv')"
    using "15.prems" by simp
  show ?case using "15.IH"[OF inner_elab] .
next
  \<comment> \<open>Empty statement list.\<close>
  case (16 env elabEnv ghost next_mv)
  from "16.prems" show ?case by simp
next
  \<comment> \<open>Cons: chain head and tail.\<close>
  case (17 env elabEnv ghost stmt stmts next_mv)
  show ?case
    using "17.prems" "17.IH"(1) "17.IH"(2)
    by (fastforce split: sum.splits prod.splits dest: order_trans)
qed

(* Elaboration never changes the in-scope type variables (TE_TypeVars /
   TE_RuntimeTypeVars), nor the function-ghost flag (TE_FunctionGhost) or the
   proof goal (TE_ProofGoal): a statement only touches the local-variable fields.
   The TE_FunctionGhost / TE_ProofGoal parts let the cons case thread the two
   entry invariants of elab_statement_correct through the head statement. *)
lemma elab_statement_preserves_TE_TypeVars:
  "elab_statement env elabEnv ghost stmt next_mv = Inr (coreStmt, env', next_mv')
     \<Longrightarrow> TE_TypeVars env' = TE_TypeVars env
       \<and> TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env
       \<and> TE_FunctionGhost env' = TE_FunctionGhost env
       \<and> TE_ProofGoal env' = TE_ProofGoal env"
and elab_statement_list_preserves_TE_TypeVars:
  "elab_statement_list env elabEnv ghost stmts next_mv = Inr (coreStmts, env', next_mv')
     \<Longrightarrow> TE_TypeVars env' = TE_TypeVars env
       \<and> TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env
       \<and> TE_FunctionGhost env' = TE_FunctionGhost env
       \<and> TE_ProofGoal env' = TE_ProofGoal env"
proof (induction env elabEnv ghost stmt next_mv and env elabEnv ghost stmts next_mv
       arbitrary: coreStmt env' next_mv' and coreStmts env' next_mv'
       rule: elab_statement_elab_statement_list.induct)
  \<comment> \<open>VarDecl: every successful branch returns env with only local-var fields changed
      (the cong-fields lemmas), so all four fields are unchanged.\<close>
  case (1 env elabEnv ghost loc varName vorf tyOpt tmOpt next_mv)
  show ?case
  proof (cases vorf)
    case Var
    consider (none) "tyOpt = None \<and> tmOpt = None"
      | (default) ty where "tyOpt = Some ty \<and> tmOpt = None"
      | (init) tm where "tmOpt = Some tm"
      by (cases tyOpt; cases tmOpt) auto
    thus ?thesis
    proof cases
      case none
      thus ?thesis using "1.prems"(1) Var by simp
    next
      case default
      \<comment> \<open>Default-init: env' = vardecl_add_local env ghost varName coreTy.\<close>
      thus ?thesis using "1.prems"(1) Var
        by (auto simp: vardecl_add_local_def split: sum.splits)
    next
      case init
      \<comment> \<open>Initializer present: routed to the pure or impure helper (cong-fields lemmas).\<close>
      show ?thesis
      proof (cases "is_impure_call env elabEnv tm")
        case True
        with "1.prems"(1) Var init
        have "elab_vardecl_impure env elabEnv ghost loc varName tyOpt tm next_mv
                = Inr (coreStmt, env', next_mv')" by (simp split: option.splits)
        thus ?thesis using elab_vardecl_impure_cong_fields[OF _ True] by simp
      next
        case False
        with "1.prems"(1) Var init
        have "elab_vardecl_pure env elabEnv ghost loc varName tyOpt tm next_mv
                = Inr (coreStmt, env', next_mv')" by (simp split: option.splits)
        thus ?thesis using elab_vardecl_pure_cong_fields by simp
      qed
    qed
  next
    case Ref
    \<comment> \<open>Ref: env' = (vardecl_add_local \<dots>) with TE_ConstLocals overridden.\<close>
    from "1.prems"(1) Ref
    have "elab_vardecl_ref env elabEnv ghost loc varName tmOpt next_mv
            = Inr (coreStmt, env', next_mv')" by simp
    thus ?thesis using elab_vardecl_ref_cong_fields by simp
  qed
next
  case (2 env elabEnv ghost loc varName ty next_mv) thus ?case sorry  \<comment> \<open>Fix\<close>
next
  \<comment> \<open>Obtain: env' = vardecl_add_local env Ghost varName coreTy, which touches only
      the local-var fields, so all four tracked fields are unchanged.\<close>
  case (3 env elabEnv ghost loc varName ty tm next_mv)
  show ?case using "3.prems"(1)
    by (auto simp: Let_def vardecl_add_local_def
             split: sum.splits prod.splits option.splits if_splits)
next
  case (4 env elabEnv ghost loc tm next_mv) thus ?case sorry  \<comment> \<open>Use\<close>
next
  \<comment> \<open>Assign: env unchanged (both helpers leave env alone).\<close>
  case (5 env elabEnv ghost loc lhs rhs next_mv)
  from "5.prems"(1) obtain lhsTm lhsTy next_mv1 where
    lhs_elab: "elab_term env elabEnv ghost lhs next_mv = Inr (lhsTm, lhsTy, next_mv1)"
    by (auto split: sum.splits prod.splits)
  have "env' = env"
  proof (cases "is_impure_call env elabEnv rhs")
    case True
    with "5.prems"(1) lhs_elab
    have "elab_assign_impure env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1
            = Inr (coreStmt, env', next_mv')" by (auto split: if_splits)
    thus ?thesis using elab_assign_impure_env[OF _ True] by simp
  next
    case False
    with "5.prems"(1) lhs_elab
    have "elab_assign_pure env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1
            = Inr (coreStmt, env', next_mv')" by (auto split: if_splits)
    thus ?thesis using elab_assign_pure_env by simp
  qed
  thus ?case by simp
next
  case (6 env elabEnv ghost loc lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Swap\<close>
next
  case (7 env elabEnv ghost loc tmOpt next_mv) thus ?case sorry  \<comment> \<open>Return\<close>
next
  \<comment> \<open>Assert: env' = env in every success path (the proof-body env is discarded), so
      all four tracked fields are trivially unchanged.\<close>
  case (8 env elabEnv ghost loc condOpt proofBody next_mv)
  show ?case using "8.prems"(1)
    by (cases condOpt)
       (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
next
  \<comment> \<open>Assume: env unchanged.\<close>
  case (9 env elabEnv ghost loc tm next_mv)
  show ?case using "9.prems"(1) by (auto split: sum.splits prod.splits option.splits if_splits)
next
  case (10 env elabEnv ghost loc cond thenB elseB next_mv) thus ?case sorry  \<comment> \<open>If\<close>
next
  case (11 env elabEnv ghost loc cond attrs body next_mv) thus ?case sorry  \<comment> \<open>While\<close>
next
  case (12 env elabEnv ghost loc tm next_mv) thus ?case sorry  \<comment> \<open>Call\<close>
next
  case (13 env elabEnv ghost loc scrut arms next_mv) thus ?case sorry  \<comment> \<open>Match\<close>
next
  \<comment> \<open>ShowHide: env unchanged.\<close>
  case (14 env elabEnv ghost loc sh name next_mv)
  from "14.prems"(1) show ?case by simp
next
  \<comment> \<open>Ghost wrapper: re-elaborates inner in Ghost mode (same env).\<close>
  case (15 env elabEnv ghost loc inner next_mv)
  have inner_elab: "elab_statement env elabEnv Ghost inner next_mv = Inr (coreStmt, env', next_mv')"
    using "15.prems"(1) by simp
  show ?case using "15.IH"[OF inner_elab] .
next
  \<comment> \<open>Empty statement list.\<close>
  case (16 env elabEnv ghost next_mv)
  from "16.prems"(1) show ?case by simp
next
  \<comment> \<open>Cons: each preserved field is preserved through head then tail.\<close>
  case (17 env elabEnv ghost stmt stmts next_mv)
  from "17.prems"(1) obtain coreStmt1 env1 next_mv1 coreStmts1 where
    head: "elab_statement env elabEnv ghost stmt next_mv = Inr (coreStmt1, env1, next_mv1)" and
    tail: "elab_statement_list env1 elabEnv ghost stmts next_mv1
             = Inr (coreStmts1, env', next_mv')"
    by (auto split: sum.splits prod.splits)
  have e1: "TE_TypeVars env1 = TE_TypeVars env \<and> TE_RuntimeTypeVars env1 = TE_RuntimeTypeVars env
              \<and> TE_FunctionGhost env1 = TE_FunctionGhost env \<and> TE_ProofGoal env1 = TE_ProofGoal env"
    using "17.IH"(1)[OF head] by simp
  moreover have "TE_TypeVars env' = TE_TypeVars env1 \<and> TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env1
                  \<and> TE_FunctionGhost env' = TE_FunctionGhost env1 \<and> TE_ProofGoal env' = TE_ProofGoal env1"
    using "17.IH"(2) head tail by blast
  ultimately show ?case by simp
qed

(* Elaboration preserves elabenv_well_formed. This needs no hypotheses about env
   beyond elabenv_well_formed itself: every statement form leaves TE_TypeVars,
   TE_Datatypes and TE_DataCtors unchanged (it only touches local-variable fields
   and TE_ProofGoal), and those three fields are all that elabenv_well_formed
   depends on (elabenv_well_formed_cong_env). *)
lemma elab_statement_preserves_elabenv_well_formed:
  "elab_statement env elabEnv ghost stmt next_mv = Inr (coreStmt, env', next_mv')
     \<Longrightarrow> elabenv_well_formed env elabEnv \<Longrightarrow> elabenv_well_formed env' elabEnv"
and elab_statement_list_preserves_elabenv_well_formed:
  "elab_statement_list env elabEnv ghost stmts next_mv = Inr (coreStmts, env', next_mv')
     \<Longrightarrow> elabenv_well_formed env elabEnv \<Longrightarrow> elabenv_well_formed env' elabEnv"
proof (induction env elabEnv ghost stmt next_mv and env elabEnv ghost stmts next_mv
       arbitrary: coreStmt env' next_mv' and coreStmts env' next_mv'
       rule: elab_statement_elab_statement_list.induct)
  \<comment> \<open>VarDecl: every successful branch leaves TE_TypeVars / TE_Datatypes / TE_DataCtors
      unchanged (cong-fields lemmas), so elabenv_well_formed is preserved by congruence.\<close>
  case (1 env elabEnv ghost loc varName vorf tyOpt tmOpt next_mv)
  have flds: "TE_TypeVars env' = TE_TypeVars env \<and> TE_Datatypes env' = TE_Datatypes env
                \<and> TE_DataCtors env' = TE_DataCtors env"
  proof (cases vorf)
    case Var
    consider (none) "tyOpt = None \<and> tmOpt = None"
      | (default) ty where "tyOpt = Some ty \<and> tmOpt = None"
      | (init) tm where "tmOpt = Some tm"
      by (cases tyOpt; cases tmOpt) auto
    thus ?thesis
    proof cases
      case none thus ?thesis using "1.prems"(1) Var by simp
    next
      case default thus ?thesis using "1.prems"(1) Var
        by (auto simp: vardecl_add_local_def split: sum.splits)
    next
      case init
      show ?thesis
      proof (cases "is_impure_call env elabEnv tm")
        case True
        with "1.prems"(1) Var init
        have "elab_vardecl_impure env elabEnv ghost loc varName tyOpt tm next_mv
                = Inr (coreStmt, env', next_mv')" by (simp split: option.splits)
        thus ?thesis using elab_vardecl_impure_cong_fields[OF _ True] by simp
      next
        case False
        with "1.prems"(1) Var init
        have "elab_vardecl_pure env elabEnv ghost loc varName tyOpt tm next_mv
                = Inr (coreStmt, env', next_mv')" by (simp split: option.splits)
        thus ?thesis using elab_vardecl_pure_cong_fields by simp
      qed
    qed
  next
    case Ref
    thus ?thesis using "1.prems"(1) elab_vardecl_ref_cong_fields by auto
  qed
  show ?case
    using "1.prems"(2) elabenv_well_formed_cong_env[OF conjunct1[OF flds]
            conjunct1[OF conjunct2[OF flds]] conjunct2[OF conjunct2[OF flds]]]
    by simp
next
  case (2 env elabEnv ghost loc varName ty next_mv) thus ?case sorry  \<comment> \<open>Fix\<close>
next
  \<comment> \<open>Obtain: env' = vardecl_add_local env Ghost varName coreTy leaves TE_TypeVars /
      TE_Datatypes / TE_DataCtors unchanged, so elabenv_well_formed is preserved.\<close>
  case (3 env elabEnv ghost loc varName ty tm next_mv)
  have flds: "TE_TypeVars env' = TE_TypeVars env \<and> TE_Datatypes env' = TE_Datatypes env
                \<and> TE_DataCtors env' = TE_DataCtors env"
    using "3.prems"(1)
    by (auto simp: Let_def vardecl_add_local_def
             split: sum.splits prod.splits option.splits if_splits)
  show ?case
    using "3.prems"(2) elabenv_well_formed_cong_env[OF conjunct1[OF flds]
            conjunct1[OF conjunct2[OF flds]] conjunct2[OF conjunct2[OF flds]]]
    by simp
next
  case (4 env elabEnv ghost loc tm next_mv) thus ?case sorry  \<comment> \<open>Use\<close>
next
  \<comment> \<open>Assign: env unchanged.\<close>
  case (5 env elabEnv ghost loc lhs rhs next_mv)
  from "5.prems"(1) obtain lhsTm lhsTy next_mv1 where
    lhs_elab: "elab_term env elabEnv ghost lhs next_mv = Inr (lhsTm, lhsTy, next_mv1)"
    by (auto split: sum.splits prod.splits)
  have "env' = env"
  proof (cases "is_impure_call env elabEnv rhs")
    case True
    with "5.prems"(1) lhs_elab
    have "elab_assign_impure env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1
            = Inr (coreStmt, env', next_mv')" by (auto split: if_splits)
    thus ?thesis using elab_assign_impure_env[OF _ True] by simp
  next
    case False
    with "5.prems"(1) lhs_elab
    have "elab_assign_pure env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1
            = Inr (coreStmt, env', next_mv')" by (auto split: if_splits)
    thus ?thesis using elab_assign_pure_env by simp
  qed
  thus ?case using "5.prems"(2) by simp
next
  case (6 env elabEnv ghost loc lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Swap\<close>
next
  case (7 env elabEnv ghost loc tmOpt next_mv) thus ?case sorry  \<comment> \<open>Return\<close>
next
  \<comment> \<open>Assert: env unchanged (the proof-body env is discarded).\<close>
  case (8 env elabEnv ghost loc condOpt proofBody next_mv)
  from "8.prems"(1) have "env' = env"
    by (cases condOpt)
       (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
  thus ?case using "8.prems"(2) by simp
next
  \<comment> \<open>Assume: env unchanged.\<close>
  case (9 env elabEnv ghost loc tm next_mv)
  from "9.prems"(1) have "env' = env" by (auto split: sum.splits prod.splits option.splits if_splits)
  thus ?case using "9.prems"(2) by simp
next
  case (10 env elabEnv ghost loc cond thenB elseB next_mv) thus ?case sorry  \<comment> \<open>If\<close>
next
  case (11 env elabEnv ghost loc cond attrs body next_mv) thus ?case sorry  \<comment> \<open>While\<close>
next
  case (12 env elabEnv ghost loc tm next_mv) thus ?case sorry  \<comment> \<open>Call\<close>
next
  case (13 env elabEnv ghost loc scrut arms next_mv) thus ?case sorry  \<comment> \<open>Match\<close>
next
  \<comment> \<open>ShowHide: env unchanged.\<close>
  case (14 env elabEnv ghost loc sh name next_mv)
  from "14.prems"(1) have "env' = env" by simp
  thus ?case using "14.prems"(2) by simp
next
  \<comment> \<open>Ghost wrapper: re-elaborates inner in Ghost mode (same env).\<close>
  case (15 env elabEnv ghost loc inner next_mv)
  have inner_elab: "elab_statement env elabEnv Ghost inner next_mv = Inr (coreStmt, env', next_mv')"
    using "15.prems"(1) by simp
  show ?case using "15.IH"[OF inner_elab "15.prems"(2)] .
next
  \<comment> \<open>Empty statement list.\<close>
  case (16 env elabEnv ghost next_mv)
  from "16.prems"(1) have "env' = env" by simp
  thus ?case using "16.prems"(2) by simp
next
  \<comment> \<open>Cons: thread elabenv_well_formed through head then tail.\<close>
  case (17 env elabEnv ghost stmt stmts next_mv)
  from "17.prems"(1) obtain coreStmt1 env1 next_mv1 coreStmts1 where
    head: "elab_statement env elabEnv ghost stmt next_mv = Inr (coreStmt1, env1, next_mv1)" and
    tail: "elab_statement_list env1 elabEnv ghost stmts next_mv1
             = Inr (coreStmts1, env', next_mv')"
    by (auto split: sum.splits prod.splits)
  have ee1: "elabenv_well_formed env1 elabEnv" using "17.IH"(1)[OF head "17.prems"(2)] .
  show ?case using "17.IH"(2) head tail ee1 by simp
qed

(* Elaboration preserves well-formedness of the type environment. *)
lemma elab_statement_preserves_well_formed:
  "elab_statement env elabEnv ghost stmt next_mv = Inr (coreStmt, env', next_mv')
     \<Longrightarrow> tyenv_well_formed env \<Longrightarrow> elabenv_well_formed env elabEnv
     \<Longrightarrow> (\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv)
     \<Longrightarrow> tyenv_well_formed env'"
and elab_statement_list_preserves_well_formed:
  "elab_statement_list env elabEnv ghost stmts next_mv = Inr (coreStmts, env', next_mv')
     \<Longrightarrow> tyenv_well_formed env \<Longrightarrow> elabenv_well_formed env elabEnv
     \<Longrightarrow> (\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv)
     \<Longrightarrow> tyenv_well_formed env'"
proof (induction env elabEnv ghost stmt next_mv and env elabEnv ghost stmts next_mv
       arbitrary: coreStmt env' next_mv' and coreStmts env' next_mv'
       rule: elab_statement_elab_statement_list.induct)
  \<comment> \<open>VarDecl: the chosen variable type is well-kinded (and runtime in NotGhost
      mode), so the resulting env is well-formed by tyenv_well_formed_vardecl_result.
      The per-helper *_env lemmas supply the variable type and its well-kindedness;
      the default-init branch handles its annotation type inline.\<close>
  case (1 env elabEnv ghost loc varName vorf tyOpt tmOpt next_mv)
  have td_wf: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using "1.prems"(3) unfolding elabenv_well_formed_def by simp
  show ?case
  proof (cases vorf)
    case Var
    consider (none) "tyOpt = None \<and> tmOpt = None"
      | (default) ty where "tyOpt = Some ty \<and> tmOpt = None"
      | (init) tm where "tmOpt = Some tm"
      by (cases tyOpt; cases tmOpt) auto
    thus ?thesis
    proof cases
      case none thus ?thesis using "1.prems"(1) Var by simp
    next
      case default
      \<comment> \<open>Default-init: env' = vardecl_add_local env ghost varName coreTy, coreTy from elab_type.\<close>
      from "1.prems"(1) Var default obtain coreTy where
        ety: "elab_type env elabEnv ghost ty = Inr coreTy" and
        env'_eq: "env' = vardecl_add_local env ghost varName coreTy"
        by (auto simp: vardecl_add_local_def split: sum.splits)
      have wk: "is_well_kinded env coreTy"
        using elab_type_is_well_kinded(1)[OF td_wf "1.prems"(2) ety] .
      have rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env coreTy"
        using elab_type_notghost_is_runtime(1)[OF td_wf "1.prems"(2)] ety by auto
      show ?thesis using env'_eq tyenv_well_formed_vardecl_add_local[OF "1.prems"(2) wk rt] by simp
    next
      case init
      have "\<exists>varTy. env' = vardecl_add_local env ghost varName varTy
                     \<and> is_well_kinded env varTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env varTy)"
      proof (cases "is_impure_call env elabEnv tm")
        case True
        with "1.prems"(1) Var init
        have "elab_vardecl_impure env elabEnv ghost loc varName tyOpt tm next_mv
                = Inr (coreStmt, env', next_mv')" by (simp split: option.splits)
        thus ?thesis using elab_vardecl_impure_env[OF _ True "1.prems"(2,3,4)] by auto
      next
        case False
        with "1.prems"(1) Var init
        have "elab_vardecl_pure env elabEnv ghost loc varName tyOpt tm next_mv
                = Inr (coreStmt, env', next_mv')" by (simp split: option.splits)
        thus ?thesis using elab_vardecl_pure_env[OF _ "1.prems"(2,3,4)] by auto
      qed
      then obtain varTy where
        env'_eq: "env' = vardecl_add_local env ghost varName varTy" and
        wk: "is_well_kinded env varTy" and
        rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env varTy" by blast
      show ?thesis using env'_eq tyenv_well_formed_vardecl_add_local[OF "1.prems"(2) wk rt] by simp
    qed
  next
    case Ref
    \<comment> \<open>Ref: env' = (vardecl_add_local \<dots>) with TE_ConstLocals overridden — the shape
        tyenv_well_formed_vardecl_result covers directly.\<close>
    from "1.prems"(1) Ref
    have rf: "elab_vardecl_ref env elabEnv ghost loc varName tmOpt next_mv
                = Inr (coreStmt, env', next_mv')" by simp
    obtain varTy c where
      env'_eq: "env' = (vardecl_add_local env ghost varName varTy) \<lparr> TE_ConstLocals := c \<rparr>" and
      wk: "is_well_kinded env varTy" and
      rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env varTy"
      using elab_vardecl_ref_env[OF rf "1.prems"(2,3,4)] by blast
    show ?thesis using env'_eq tyenv_well_formed_vardecl_result[OF "1.prems"(2) wk rt]
      by (simp add: vardecl_add_local_def)
  qed
next
  case (2 env elabEnv ghost loc varName ty next_mv) thus ?case sorry  \<comment> \<open>Fix\<close>
next
  \<comment> \<open>Obtain: env' = vardecl_add_local env Ghost varName coreTy, where coreTy is the
      Ghost-mode elaboration of the annotation (hence well-kinded). The runtime
      condition is vacuous (the local is ghost), so tyenv_well_formed is preserved.\<close>
  case (3 env elabEnv ghost loc varName ty tm next_mv)
  have td_wf: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using "3.prems"(3) unfolding elabenv_well_formed_def by simp
  from "3.prems"(1) obtain coreTy where
    ety: "elab_type env elabEnv Ghost ty = Inr coreTy" and
    env'_eq: "env' = vardecl_add_local env Ghost varName coreTy"
    by (auto simp: Let_def vardecl_add_local_def
             split: sum.splits prod.splits option.splits if_splits)
  have wk: "is_well_kinded env coreTy"
    using elab_type_is_well_kinded(1)[OF td_wf "3.prems"(2) ety] .
  show ?case
    using env'_eq tyenv_well_formed_vardecl_add_local[OF "3.prems"(2) wk] by simp
next
  case (4 env elabEnv ghost loc tm next_mv) thus ?case sorry  \<comment> \<open>Use\<close>
next
  \<comment> \<open>Assign: env unchanged.\<close>
  case (5 env elabEnv ghost loc lhs rhs next_mv)
  from "5.prems"(1) obtain lhsTm lhsTy next_mv1 where
    lhs_elab: "elab_term env elabEnv ghost lhs next_mv = Inr (lhsTm, lhsTy, next_mv1)"
    by (auto split: sum.splits prod.splits)
  have "env' = env"
  proof (cases "is_impure_call env elabEnv rhs")
    case True
    with "5.prems"(1) lhs_elab
    have "elab_assign_impure env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1
            = Inr (coreStmt, env', next_mv')" by (auto split: if_splits)
    thus ?thesis using elab_assign_impure_env[OF _ True] by simp
  next
    case False
    with "5.prems"(1) lhs_elab
    have "elab_assign_pure env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1
            = Inr (coreStmt, env', next_mv')" by (auto split: if_splits)
    thus ?thesis using elab_assign_pure_env by simp
  qed
  thus ?case using "5.prems"(2) by simp
next
  case (6 env elabEnv ghost loc lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Swap\<close>
next
  case (7 env elabEnv ghost loc tmOpt next_mv) thus ?case sorry  \<comment> \<open>Return\<close>
next
  \<comment> \<open>Assert: env unchanged (the proof-body env is discarded).\<close>
  case (8 env elabEnv ghost loc condOpt proofBody next_mv)
  from "8.prems"(1) have "env' = env"
    by (cases condOpt)
       (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
  thus ?case using "8.prems"(2) by simp
next
  \<comment> \<open>Assume: env unchanged.\<close>
  case (9 env elabEnv ghost loc tm next_mv)
  from "9.prems"(1) have "env' = env" by (auto split: sum.splits prod.splits option.splits if_splits)
  thus ?case using "9.prems"(2) by simp
next
  case (10 env elabEnv ghost loc cond thenB elseB next_mv) thus ?case sorry  \<comment> \<open>If\<close>
next
  case (11 env elabEnv ghost loc cond attrs body next_mv) thus ?case sorry  \<comment> \<open>While\<close>
next
  case (12 env elabEnv ghost loc tm next_mv) thus ?case sorry  \<comment> \<open>Call\<close>
next
  case (13 env elabEnv ghost loc scrut arms next_mv) thus ?case sorry  \<comment> \<open>Match\<close>
next
  \<comment> \<open>ShowHide: env unchanged.\<close>
  case (14 env elabEnv ghost loc sh name next_mv)
  from "14.prems"(1) have "env' = env" by simp
  thus ?case using "14.prems"(2) by simp
next
  \<comment> \<open>Ghost wrapper: re-elaborates inner in Ghost mode (same env).\<close>
  case (15 env elabEnv ghost loc inner next_mv)
  have inner_elab: "elab_statement env elabEnv Ghost inner next_mv = Inr (coreStmt, env', next_mv')"
    using "15.prems"(1) by simp
  show ?case using "15.IH"[OF inner_elab "15.prems"(2,3,4)] .
next
  \<comment> \<open>Empty statement list.\<close>
  case (16 env elabEnv ghost next_mv)
  from "16.prems"(1) have "env' = env" by simp
  thus ?case using "16.prems"(2) by simp
next
  \<comment> \<open>Cons: thread well-formedness (and the tyvar bound) through head then tail.\<close>
  case (17 env elabEnv ghost stmt stmts next_mv)
  from "17.prems"(1) obtain coreStmt1 env1 next_mv1 coreStmts1 where
    head: "elab_statement env elabEnv ghost stmt next_mv = Inr (coreStmt1, env1, next_mv1)" and
    tail: "elab_statement_list env1 elabEnv ghost stmts next_mv1
             = Inr (coreStmts1, env', next_mv')"
    by (auto split: sum.splits prod.splits)
  have wf1: "tyenv_well_formed env1"
    using "17.IH"(1)[OF head "17.prems"(2,3,4)] .
  have ee1: "elabenv_well_formed env1 elabEnv"
    using elab_statement_preserves_elabenv_well_formed(1)[OF head "17.prems"(3)] .
  \<comment> \<open>The tyvar bound transfers: TE_TypeVars is unchanged and next_mv only grows.\<close>
  have tv1: "TE_TypeVars env1 = TE_TypeVars env"
    using elab_statement_preserves_TE_TypeVars(1)[OF head] by simp
  have nmv1: "next_mv \<le> next_mv1" using elab_statement_next_mv_monotone(1)[OF head] .
  have bound1: "\<forall>n. n |\<in>| TE_TypeVars env1 \<longrightarrow> n < next_mv1"
    using "17.prems"(4) tv1 nmv1 by auto
  show ?case
    using "17.IH"(2) head tail wf1 ee1 bound1 by simp
qed


(* ========================================================================== *)
(* Main correctness theorem                                                   *)
(* ========================================================================== *)

(* If elaborating a statement (or statement list) succeeds in env producing env',
   then the resulting statement (or list) typechecks in env producing env', under
   these assumptions:
    - the env and elabEnv are well formed;
    - type variables from next_mv onwards are fresh;
    - TE_FunctionGhost = Ghost implies ghost = Ghost (i.e., ghost function bodies only
      ever run in Ghost mode);
    - ghost = NotGhost implies TE_ProofGoal env = None (i.e., executable / non-ghost
      statements never have an enclosing proof goal).
*)
theorem elab_statement_correct:
  "elab_statement env elabEnv ghost stmt next_mv = Inr (coreStmt, env', next_mv') \<Longrightarrow>
   tyenv_well_formed env \<Longrightarrow> elabenv_well_formed env elabEnv \<Longrightarrow>
   (\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv) \<Longrightarrow>
   (TE_FunctionGhost env = Ghost \<longrightarrow> ghost = Ghost) \<Longrightarrow>
   (ghost = NotGhost \<longrightarrow> TE_ProofGoal env = None) \<Longrightarrow>
   core_statement_type env ghost coreStmt = Some env'"
and elab_statement_list_correct:
  "elab_statement_list env elabEnv ghost stmts next_mv = Inr (coreStmts, env', next_mv') \<Longrightarrow>
   tyenv_well_formed env \<Longrightarrow> elabenv_well_formed env elabEnv \<Longrightarrow>
   (\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv) \<Longrightarrow>
   (TE_FunctionGhost env = Ghost \<longrightarrow> ghost = Ghost) \<Longrightarrow>
   (ghost = NotGhost \<longrightarrow> TE_ProofGoal env = None) \<Longrightarrow>
   core_statement_list_type env ghost coreStmts = Some env'"
proof (induction env elabEnv ghost stmt next_mv and env elabEnv ghost stmts next_mv
       arbitrary: coreStmt env' next_mv' and coreStmts env' next_mv'
       rule: elab_statement_elab_statement_list.induct)
case (1 env elabEnv ghost loc varName vorf tyOpt tmOpt next_mv)
  \<comment> \<open>VarDecl: dispatch on the helper used by the elaborator clause.\<close>
  show ?case
  proof (cases vorf)
    case Var
    consider (none) "tyOpt = None \<and> tmOpt = None"
      | (default) ty where "tyOpt = Some ty \<and> tmOpt = None"
      | (init) tm where "tmOpt = Some tm"
      by (cases tyOpt; cases tmOpt) auto
    thus ?thesis
    proof cases
      case none
      thus ?thesis using "1.prems"(1) Var by simp
    next
      case default
      \<comment> \<open>Default-init: coreTy = elaborated annotation; initTm = CoreTm_Default coreTy.\<close>
      have td_wf: "typedefs_well_formed env (EE_Typedefs elabEnv)"
        using "1.prems"(3) unfolding elabenv_well_formed_def by simp
      from "1.prems"(1) Var default obtain coreTy where
        ety: "elab_type env elabEnv ghost ty = Inr coreTy" and
        cs_eq: "coreStmt = CoreStmt_VarDecl ghost varName Var coreTy (CoreTm_Default coreTy)" and
        env'_eq: "env' = vardecl_add_local env ghost varName coreTy"
        by (auto simp: vardecl_add_local_def split: sum.splits)
      have wk: "is_well_kinded env coreTy"
        using elab_type_is_well_kinded(1)[OF td_wf "1.prems"(2) ety] .
      have rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env coreTy"
        using elab_type_notghost_is_runtime(1)[OF td_wf "1.prems"(2)] ety by auto
      have init_typed: "core_term_type env ghost (CoreTm_Default coreTy) = Some coreTy"
        using wk rt by simp
      show ?thesis using wk rt init_typed by (simp add: cs_eq env'_eq vardecl_add_local_def)
    next
      case init
      show ?thesis
      proof (cases "is_impure_call env elabEnv tm")
        case False
        \<comment> \<open>Pure initializer.\<close>
        from "1.prems"(1) Var init False
        have "elab_vardecl_pure env elabEnv ghost loc varName tyOpt tm next_mv
                = Inr (coreStmt, env', next_mv')" by (simp split: option.splits)
        thus ?thesis using elab_vardecl_pure_correct[OF _ "1.prems"(2,3,4)] by simp
      next
        case True
        \<comment> \<open>Impure initializer (CoreStmt_VarDeclCall).\<close>
        from "1.prems"(1) Var init True
        have "elab_vardecl_impure env elabEnv ghost loc varName tyOpt tm next_mv
                = Inr (coreStmt, env', next_mv')" by (simp split: option.splits)
        thus ?thesis using elab_vardecl_impure_correct[OF _ True "1.prems"(2,3,4)] by simp
      qed
    qed
  next
    case Ref
    from "1.prems"(1) Ref
    have "elab_vardecl_ref env elabEnv ghost loc varName tmOpt next_mv
            = Inr (coreStmt, env', next_mv')" by simp
    thus ?thesis using elab_vardecl_ref_correct[OF _ "1.prems"(2,3,4)] by simp
  qed
next
  case (2 env elabEnv ghost loc varName ty next_mv) thus ?case sorry  \<comment> \<open>Fix\<close>
next
  \<comment> \<open>Obtain: elaborate the annotation in Ghost mode to coreTy (well-kinded), then
      the predicate in Ghost mode under env_obtain = env extended with the ghost
      local varName : coreTy. Its type unifies with Bool; apply the unifier and
      clear interval metavariables, so it typechecks as Bool in env_obtain (the
      Assume reasoning, lifted to env_obtain). The Core Obtain rule fixes
      declGhost = Ghost, so env_obtain matches its result env exactly.\<close>
  case (3 env elabEnv ghost loc varName ty tm next_mv)
  have td_wf: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using "3.prems"(3) unfolding elabenv_well_formed_def by simp
  let ?is_flex = "\<lambda>n. n |\<notin>| TE_TypeVars env"
  from "3.prems"(1) obtain coreTy coreTm condTy subst where
    ety: "elab_type env elabEnv Ghost ty = Inr coreTy" and
    etm: "elab_term (vardecl_add_local env Ghost varName coreTy) elabEnv Ghost tm next_mv
            = Inr (coreTm, condTy, next_mv')" and
    unif: "unify ?is_flex condTy CoreTy_Bool = Some subst" and
    cs_eq: "coreStmt = CoreStmt_Obtain varName coreTy
                         (clear_metavars next_mv next_mv' (apply_subst_to_term subst coreTm))" and
    env'_eq: "env' = vardecl_add_local env Ghost varName coreTy"
    by (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
  \<comment> \<open>coreTy is well-kinded (Ghost-mode elaboration of the annotation).\<close>
  have wk: "is_well_kinded env coreTy"
    using elab_type_is_well_kinded(1)[OF td_wf "3.prems"(2) ety] .
  \<comment> \<open>env_obtain = the env extended with the ghost local. It differs from env only in
      the local-var fields, so it is well-formed, tyvar-bounded, and elabenv-compatible.\<close>
  let ?eo = "vardecl_add_local env Ghost varName coreTy"
  have flds: "TE_TypeVars ?eo = TE_TypeVars env \<and> TE_Datatypes ?eo = TE_Datatypes env
                \<and> TE_DataCtors ?eo = TE_DataCtors env"
    by (simp add: vardecl_add_local_def)
  have wf_obtain: "tyenv_well_formed ?eo"
    using tyenv_well_formed_vardecl_add_local[OF "3.prems"(2) wk] by simp
  have ee_obtain: "elabenv_well_formed ?eo elabEnv"
    using "3.prems"(3)
          elabenv_well_formed_cong_env[OF conjunct1[OF flds]
            conjunct1[OF conjunct2[OF flds]] conjunct2[OF conjunct2[OF flds]]] by simp
  have bound_obtain: "\<forall>n. n |\<in>| TE_TypeVars ?eo \<longrightarrow> n < next_mv"
    using "3.prems"(4) conjunct1[OF flds] by simp
  \<comment> \<open>From here, the Assume reasoning over env_obtain.\<close>
  let ?envD = "extend_env_with_tyvars ?eo Ghost next_mv next_mv'"
  have typed_ghost: "core_term_type ?envD Ghost coreTm = Some condTy"
    using elab_term_correct(1)[OF etm wf_obtain ee_obtain] bound_obtain by simp
  have wfD: "tyenv_well_formed ?envD"
    using wf_obtain tyenv_well_formed_extend_env_with_tyvars by blast
  have condTy_wk: "is_well_kinded ?envD condTy"
    using core_term_type_well_kinded[OF typed_ghost wfD] .
  have subst_wk: "\<forall>ty' \<in> fmran' subst. is_well_kinded ?envD ty'"
    using unify_preserves_well_kinded[OF unif condTy_wk] by simp
  \<comment> \<open>The flex predicate is stated over env, but TE_TypeVars ?eo = TE_TypeVars env.\<close>
  have dom_flex: "\<forall>n. n |\<in>| fmdom subst \<longrightarrow> n |\<notin>| TE_TypeVars ?eo"
    using unify_unify_list_dom_flex(1)[OF unif] conjunct1[OF flds] by simp
  have envD_locals: "TE_LocalVars ?envD = TE_LocalVars ?eo"
    unfolding extend_env_with_tyvars_def by simp
  have envD_ret: "TE_ReturnType ?envD = TE_ReturnType ?eo"
    unfolding extend_env_with_tyvars_def by simp
  from flex_subst_identity_on_env[OF dom_flex wf_obtain envD_locals envD_ret]
  have locals_unaffected: "\<And>name ty'. fmlookup (TE_LocalVars ?envD) name = Some ty'
                                        \<Longrightarrow> apply_subst subst ty' = ty'"
    and ret_unaffected: "apply_subst subst (TE_ReturnType ?envD) = TE_ReturnType ?envD"
    by blast+
  have subst_typed: "core_term_type ?envD Ghost (apply_subst_to_term subst coreTm)
                       = Some (apply_subst subst condTy)"
    using apply_subst_to_term_preserves_typing
            [OF typed_ghost wfD subst_wk _ locals_unaffected ret_unaffected] by simp
  have "apply_subst subst condTy = apply_subst subst CoreTy_Bool"
    using unify_sound[OF unif] .
  hence subst_typed_bool:
    "core_term_type ?envD Ghost (apply_subst_to_term subst coreTm) = Some CoreTy_Bool"
    using subst_typed by simp
  have cond_typed: "core_term_type ?eo Ghost
                      (clear_metavars next_mv next_mv' (apply_subst_to_term subst coreTm))
                        = Some CoreTy_Bool"
    using clear_metavars_typed_in_env[OF subst_typed_bool wf_obtain bound_obtain] by simp
  \<comment> \<open>Assemble the Core Obtain rule: is_well_kinded env coreTy plus the Bool-typed
      predicate under env_obtain, which is definitionally the rule's result env.\<close>
  show ?case using wk cond_typed
    by (simp add: cs_eq env'_eq vardecl_add_local_def)
next
  case (4 env elabEnv ghost loc tm next_mv) thus ?case sorry  \<comment> \<open>Use\<close>
next
  \<comment> \<open>Assign: elaborate the lhs (a writable lvalue of a metavar-free type), then
      dispatch the rhs to the pure or impure Assign helper.\<close>
  case (5 env elabEnv ghost loc lhs rhs next_mv)
  from "5.prems"(1) obtain lhsTm lhsTy next_mv1 where
    lhs_elab: "elab_term env elabEnv ghost lhs next_mv = Inr (lhsTm, lhsTy, next_mv1)" and
    lhs_wl: "is_writable_lvalue env lhsTm" and
    lhs_no_meta: "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list lhsTy)"
    by (auto split: sum.splits prod.splits if_splits)
  have mono_lhs: "next_mv \<le> next_mv1" using elab_term_next_mv_monotone[OF lhs_elab] .
  have lhs_typed: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv1) ghost lhsTm = Some lhsTy"
    using elab_term_correct(1)[OF lhs_elab "5.prems"(2,3)] "5.prems"(4) by simp
  have lhs_below: "type_tyvars lhsTy \<subseteq> {n. n < next_mv}"
    using lhs_no_meta "5.prems"(4)
    by (auto simp: set_type_tyvars_list[symmetric] list_all_iff)
  show ?case
  proof (cases "is_impure_call env elabEnv rhs")
    case True
    with "5.prems"(1) lhs_elab lhs_wl lhs_no_meta
    have "elab_assign_impure env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1
            = Inr (coreStmt, env', next_mv')" by (auto split: if_splits)
    thus ?thesis
      using elab_assign_impure_correct[OF _ True lhs_typed lhs_wl lhs_below mono_lhs "5.prems"(2,3,4)] by simp
  next
    case False
    with "5.prems"(1) lhs_elab lhs_wl lhs_no_meta
    have "elab_assign_pure env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1
            = Inr (coreStmt, env', next_mv')" by (auto split: if_splits)
    thus ?thesis
      using elab_assign_pure_correct[OF _ lhs_typed lhs_wl lhs_below mono_lhs "5.prems"(2,3,4)] by simp
  qed
next
  case (6 env elabEnv ghost loc lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Swap\<close>
next
  case (7 env elabEnv ghost loc tmOpt next_mv) thus ?case sorry  \<comment> \<open>Return\<close>
next
  \<comment> \<open>Assert: emits CoreStmt_Assert with env' = env. The asserted condition (if any)
      is elaborated and coerced to Bool exactly as in Assume, so it typechecks in env
      under Ghost mode (giving condOk). The proof body is elaborated in Ghost mode under
      goalEnv = env with TE_ProofGoal set to the (cleared) condition / kept as-is, and
      TE_ProofTopLevel := True — definitionally the Core rule's goalEnv. The list IH,
      whose two ambient invariants are trivial/vacuous in Ghost mode, certifies the body.\<close>
  case (8 env elabEnv ghost loc condOpt proofBody next_mv)
  show ?case
  proof (cases condOpt)
    case None
    \<comment> \<open>"assert *": the asserted goal is the (existing) current goal; goalEnv keeps it.\<close>
    let ?goalEnv = "env \<lparr> TE_ProofTopLevel := True \<rparr>"
    from "8.prems"(1) None obtain coreBody benv where
      goal: "TE_ProofGoal env \<noteq> None" and
      cs_eq: "coreStmt = CoreStmt_Assert None coreBody" and
      env'_eq: "env' = env" and
      body: "elab_statement_list ?goalEnv elabEnv Ghost proofBody next_mv
               = Inr (coreBody, benv, next_mv')"
      by (auto simp: Let_def split: if_splits sum.splits prod.splits)
    \<comment> \<open>goalEnv premises for the list IH (it differs from env only in the two proof fields).\<close>
    have wf_goal: "tyenv_well_formed ?goalEnv"
      using "8.prems"(2) tyenv_well_formed_TE_ProofTopLevel_irrelevant by blast
    have ee_goal: "elabenv_well_formed ?goalEnv elabEnv"
      using "8.prems"(3) elabenv_well_formed_cong_env[where env' = ?goalEnv and env = env] by simp
    have bound_goal: "\<forall>n. n |\<in>| TE_TypeVars ?goalEnv \<longrightarrow> n < next_mv"
      using "8.prems"(4) by simp
    have body_typed: "core_statement_list_type ?goalEnv Ghost coreBody = Some benv"
      using "8.IH"(1)[OF None] goal wf_goal ee_goal bound_goal body by simp
    \<comment> \<open>Assemble the Core Assert rule: condOk = (goal exists); body typechecks under goalEnv.\<close>
    show ?thesis using goal body_typed by (simp add: cs_eq env'_eq None Let_def)
  next
    case (Some cond)
    \<comment> \<open>"assert cond": elaborate cond to Bool (Assume reasoning), install it as the goal.\<close>
    let ?is_flex = "\<lambda>n. n |\<notin>| TE_TypeVars env"
    \<comment> \<open>Peel the elaborator's nested cases one at a time (avoiding Let_def, which loops
        on the nested let goalEnv = \<dots> wrapping a further case-split).\<close>
    from "8.prems"(1) Some obtain coreCond condTy next_mv1 where
      etm: "elab_term env elabEnv Ghost cond next_mv = Inr (coreCond, condTy, next_mv1)"
      by (cases "elab_term env elabEnv Ghost cond next_mv")
         (auto split: prod.splits)
    from "8.prems"(1) Some etm obtain subst where
      unif: "unify ?is_flex condTy CoreTy_Bool = Some subst"
      by (cases "unify ?is_flex condTy CoreTy_Bool") auto
    let ?clearedCond0 = "clear_metavars next_mv next_mv1 (apply_subst_to_term subst coreCond)"
    let ?goalEnv0 = "env \<lparr> TE_ProofGoal := Some ?clearedCond0, TE_ProofTopLevel := True \<rparr>"
    from "8.prems"(1) Some etm unif obtain coreBody benv where
      cs_eq: "coreStmt = CoreStmt_Assert (Some ?clearedCond0) coreBody" and
      env'_eq: "env' = env" and
      body: "elab_statement_list ?goalEnv0 elabEnv Ghost proofBody next_mv1
               = Inr (coreBody, benv, next_mv')"
      by (cases "elab_statement_list ?goalEnv0 elabEnv Ghost proofBody next_mv1")
         (auto simp: Let_def split: prod.splits)
    \<comment> \<open>The cleared condition typechecks to Bool in env under Ghost mode (Assume reasoning).\<close>
    let ?envD = "extend_env_with_tyvars env Ghost next_mv next_mv1"
    have typed_ghost: "core_term_type ?envD Ghost coreCond = Some condTy"
      using elab_term_correct(1)[OF etm "8.prems"(2,3)] "8.prems"(4) by simp
    have wfD: "tyenv_well_formed ?envD"
      using "8.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast
    have condTy_wk: "is_well_kinded ?envD condTy"
      using core_term_type_well_kinded[OF typed_ghost wfD] .
    have subst_wk: "\<forall>ty' \<in> fmran' subst. is_well_kinded ?envD ty'"
      using unify_preserves_well_kinded[OF unif condTy_wk] by simp
    have dom_flex: "\<forall>n. n |\<in>| fmdom subst \<longrightarrow> ?is_flex n"
      using unify_unify_list_dom_flex(1)[OF unif] .
    have envD_locals: "TE_LocalVars ?envD = TE_LocalVars env"
      unfolding extend_env_with_tyvars_def by simp
    have envD_ret: "TE_ReturnType ?envD = TE_ReturnType env"
      unfolding extend_env_with_tyvars_def by simp
    from flex_subst_identity_on_env[OF dom_flex "8.prems"(2) envD_locals envD_ret]
    have locals_unaffected: "\<And>name ty'. fmlookup (TE_LocalVars ?envD) name = Some ty'
                                          \<Longrightarrow> apply_subst subst ty' = ty'"
      and ret_unaffected: "apply_subst subst (TE_ReturnType ?envD) = TE_ReturnType ?envD"
      by blast+
    have subst_typed: "core_term_type ?envD Ghost (apply_subst_to_term subst coreCond)
                         = Some (apply_subst subst condTy)"
      using apply_subst_to_term_preserves_typing
              [OF typed_ghost wfD subst_wk _ locals_unaffected ret_unaffected] by simp
    have "apply_subst subst condTy = apply_subst subst CoreTy_Bool"
      using unify_sound[OF unif] .
    hence subst_typed_bool:
      "core_term_type ?envD Ghost (apply_subst_to_term subst coreCond) = Some CoreTy_Bool"
      using subst_typed by simp
    have cond_typed: "core_term_type env Ghost ?clearedCond0 = Some CoreTy_Bool"
      using clear_metavars_typed_in_env[OF subst_typed_bool "8.prems"(2,4)] by simp
    \<comment> \<open>goalEnv0 = env with the cleared condition installed; premises for the list IH.\<close>
    have wf_goal: "tyenv_well_formed ?goalEnv0"
      using tyenv_well_formed_TE_ProofTopLevel_irrelevant[OF
              tyenv_well_formed_TE_ProofGoal_irrelevant[OF "8.prems"(2)]] by simp
    have ee_goal: "elabenv_well_formed ?goalEnv0 elabEnv"
      using "8.prems"(3) elabenv_well_formed_cong_env[where env' = ?goalEnv0 and env = env] by simp
    have bound_goal: "\<forall>n. n |\<in>| TE_TypeVars ?goalEnv0 \<longrightarrow> n < next_mv1"
      using "8.prems"(4) elab_term_next_mv_monotone[OF etm] by auto
    have body_typed: "core_statement_list_type ?goalEnv0 Ghost coreBody = Some benv"
      using "8.IH"(2) Some etm unif wf_goal ee_goal bound_goal body by simp
    \<comment> \<open>Assemble the Core Assert rule: condOk = cond typechecks to Bool; body under goalEnv.\<close>
    show ?thesis using cond_typed body_typed by (simp add: cs_eq env'_eq Some Let_def)
  qed
next
  \<comment> \<open>Assume: elaborate the predicate in Ghost mode; its type unifies with Bool.
      Apply the unifier to the term and clear its interval metavariables, so it
      typechecks as Bool in env directly (Bool is ground, so the unifier leaves
      it fixed). The Core Assume rule re-checks in Ghost mode and leaves the env
      unchanged.\<close>
  case (9 env elabEnv ghost loc tm next_mv)
  let ?envD = "extend_env_with_tyvars env Ghost next_mv next_mv'"
  let ?is_flex = "\<lambda>n. n |\<notin>| TE_TypeVars env"
  from "9.prems"(1) obtain coreTm condTy subst where
    etm: "elab_term env elabEnv Ghost tm next_mv = Inr (coreTm, condTy, next_mv')" and
    unif: "unify ?is_flex condTy CoreTy_Bool = Some subst" and
    cs_eq: "coreStmt = CoreStmt_Assume
                         (clear_metavars next_mv next_mv' (apply_subst_to_term subst coreTm))" and
    env'_eq: "env' = env"
    by (auto split: sum.splits prod.splits option.splits if_splits)
  have typed_ghost: "core_term_type ?envD Ghost coreTm = Some condTy"
    using elab_term_correct(1)[OF etm "9.prems"(2,3)] "9.prems"(4) by simp
  have wfD: "tyenv_well_formed ?envD"
    using "9.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast
  have condTy_wk: "is_well_kinded ?envD condTy"
    using core_term_type_well_kinded[OF typed_ghost wfD] .
  \<comment> \<open>The unifying substitution preserves typing and fixes the ground target Bool.\<close>
  have subst_wk: "\<forall>ty' \<in> fmran' subst. is_well_kinded ?envD ty'"
    using unify_preserves_well_kinded[OF unif condTy_wk] by simp
  have dom_flex: "\<forall>n. n |\<in>| fmdom subst \<longrightarrow> ?is_flex n"
    using unify_unify_list_dom_flex(1)[OF unif] .
  have envD_locals: "TE_LocalVars ?envD = TE_LocalVars env"
    unfolding extend_env_with_tyvars_def by simp
  have envD_ret: "TE_ReturnType ?envD = TE_ReturnType env"
    unfolding extend_env_with_tyvars_def by simp
  from flex_subst_identity_on_env[OF dom_flex "9.prems"(2) envD_locals envD_ret]
  have locals_unaffected: "\<And>name ty'. fmlookup (TE_LocalVars ?envD) name = Some ty'
                                        \<Longrightarrow> apply_subst subst ty' = ty'"
    and ret_unaffected: "apply_subst subst (TE_ReturnType ?envD) = TE_ReturnType ?envD"
    by blast+
  have subst_typed: "core_term_type ?envD Ghost (apply_subst_to_term subst coreTm)
                       = Some (apply_subst subst condTy)"
    using apply_subst_to_term_preserves_typing
            [OF typed_ghost wfD subst_wk _ locals_unaffected ret_unaffected] by simp
  \<comment> \<open>apply_subst subst condTy = apply_subst subst Bool = Bool (Bool is ground).\<close>
  have "apply_subst subst condTy = apply_subst subst CoreTy_Bool"
    using unify_sound[OF unif] .
  hence subst_typed_bool:
    "core_term_type ?envD Ghost (apply_subst_to_term subst coreTm) = Some CoreTy_Bool"
    using subst_typed by simp
  have init_typed: "core_term_type env Ghost
                      (clear_metavars next_mv next_mv' (apply_subst_to_term subst coreTm))
                        = Some CoreTy_Bool"
    using clear_metavars_typed_in_env[OF subst_typed_bool "9.prems"(2,4)] by simp
  show ?case using init_typed by (simp add: cs_eq env'_eq)
next
  case (10 env elabEnv ghost loc cond thenB elseB next_mv) thus ?case sorry  \<comment> \<open>If\<close>
next
  case (11 env elabEnv ghost loc cond attrs body next_mv) thus ?case sorry  \<comment> \<open>While\<close>
next
  case (12 env elabEnv ghost loc tm next_mv) thus ?case sorry  \<comment> \<open>Call\<close>
next
  case (13 env elabEnv ghost loc scrut arms next_mv) thus ?case sorry  \<comment> \<open>Match\<close>
next
  \<comment> \<open>ShowHide: env unchanged.\<close>
  case (14 env elabEnv ghost loc sh name next_mv)
  from "14.prems"(1) have cs_eq: "coreStmt = CoreStmt_ShowHide sh name"
    and env'_eq: "env' = env"
    by auto
  show ?case by (simp add: cs_eq env'_eq)
next
  \<comment> \<open>Ghost wrapper: the inner statement is elaborated in Ghost mode, so the IH
      gives a Ghost-mode typing. If the ambient is already Ghost we are done; if
      NotGhost, weaken via core_statement_type_ghost_to_notghost. The invariants
      give TE_FunctionGhost env = NotGhost and TE_ProofGoal env = None in that
      case (so Return/Fix/Use, which read the ambient, stay vacuous).\<close>
  case (15 env elabEnv ghost loc inner next_mv)
  \<comment> \<open>The wrapper elaborates inner in Ghost mode (same env, counter, result).\<close>
  have inner_elab: "elab_statement env elabEnv Ghost inner next_mv = Inr (coreStmt, env', next_mv')"
    using "15.prems"(1) by simp
  \<comment> \<open>Inner IH at ambient Ghost: its invariants are trivially / vacuously satisfied.\<close>
  have inv1: "TE_FunctionGhost env = Ghost \<longrightarrow> Ghost = Ghost" by simp
  have inv2: "Ghost = NotGhost \<longrightarrow> TE_ProofGoal env = None" by simp
  have typed_ghost: "core_statement_type env Ghost coreStmt = Some env'"
    using "15.IH"[OF inner_elab "15.prems"(2,3,4) inv1 inv2] .
  show ?case
  proof (cases ghost)
    case Ghost
    thus ?thesis using typed_ghost by simp
  next
    case NotGhost
    \<comment> \<open>ambient NotGhost: the invariants force TE_FunctionGhost env = NotGhost and
        TE_ProofGoal env = None, so the weakening lemma applies.\<close>
    have fg: "TE_FunctionGhost env = NotGhost"
      using "15.prems"(5) GhostOrNot.exhaust NotGhost by auto
    have pg: "TE_ProofGoal env = None" using "15.prems"(6) NotGhost by simp
    show ?thesis
      using core_statement_type_ghost_to_notghost[OF typed_ghost fg pg] NotGhost by simp
  qed
next
  \<comment> \<open>Empty statement list: env unchanged.\<close>
  case (16 env elabEnv ghost next_mv)
  from "16.prems"(1) have "coreStmts = []" and "env' = env"
    by auto
  thus ?case by simp
next
  \<comment> \<open>Cons: the head typechecks in env producing env1; the tail in env1 producing
      env'. Thread the env (and well-formedness / bound) through.\<close>
  case (17 env elabEnv ghost stmt stmts next_mv)
  from "17.prems"(1) obtain coreStmt1 env1 next_mv1 coreStmts1 where
    head: "elab_statement env elabEnv ghost stmt next_mv = Inr (coreStmt1, env1, next_mv1)" and
    tail: "elab_statement_list env1 elabEnv ghost stmts next_mv1
             = Inr (coreStmts1, env', next_mv')" and
    cs_eq: "coreStmts = coreStmt1 # coreStmts1"
    by (auto split: sum.splits prod.splits)
  \<comment> \<open>Bounds / preservation facts needed for the tail IH. The head preserves
      TE_FunctionGhost / TE_ProofGoal, so the two entry invariants carry to env1.\<close>
  have nmv1: "next_mv \<le> next_mv1" using elab_statement_next_mv_monotone(1)[OF head] .
  have pres: "TE_TypeVars env1 = TE_TypeVars env
                \<and> TE_FunctionGhost env1 = TE_FunctionGhost env \<and> TE_ProofGoal env1 = TE_ProofGoal env"
    using elab_statement_preserves_TE_TypeVars(1)[OF head] by simp
  have wf1: "tyenv_well_formed env1"
    using elab_statement_preserves_well_formed(1)[OF head "17.prems"(2,3,4)] .
  have ee1: "elabenv_well_formed env1 elabEnv"
    using elab_statement_preserves_elabenv_well_formed(1)[OF head "17.prems"(3)] .
  have bound1: "\<forall>n. n |\<in>| TE_TypeVars env1 \<longrightarrow> n < next_mv1"
    using "17.prems"(4) pres nmv1 by auto
  have fg1: "TE_FunctionGhost env1 = Ghost \<longrightarrow> ghost = Ghost"
    using "17.prems"(5) pres by simp
  have pg1: "ghost = NotGhost \<longrightarrow> TE_ProofGoal env1 = None"
    using "17.prems"(6) pres by simp
  have head_typed: "core_statement_type env ghost coreStmt1 = Some env1"
    using "17.IH"(1)[OF head "17.prems"(2,3,4,5,6)] .
  have tail_typed: "core_statement_list_type env1 ghost coreStmts1 = Some env'"
    using "17.IH"(2) head tail wf1 ee1 bound1 fg1 pg1 by simp
  show ?case using head_typed tail_typed by (simp add: cs_eq)
qed

end
