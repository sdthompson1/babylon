theory TypeSubstPreservation
  imports TypeSubstHelpers CoreStmtTypecheck
begin

(* ========================================================================== *)
(* Type preservation theorems for apply_subst_to_term. *)
(* ========================================================================== *)

(* If a term has type ty, then apply_subst_to_term subst tm has type
   (apply_subst subst ty), under the following conditions:

   - The environment is well-formed.
   - The substitution range is well-kinded in env (and runtime in NotGhost mode), so
     that types introduced by the substitution remain well-kinded.
   - The substitution does not affect any local variable's type and does not
     affect the return type. Without this, the lemma is false: for
     `CoreTm_Var name` whose env type is `T`, the result type is the env's `T`
     unchanged, not `apply_subst subst T`. Globals are closed (by the well-kinded
     clause of tyenv_well_formed) so are unaffected by any substitution and need
     no precondition.

     Elaborator clients can typically discharge this from their freshness
     invariant: fresh type variables in the substitution's domain don't appear in any
     pre-existing local-var type or return type.

   This lemma is a corollary of core_term_type_subst_callee_env: under these
   conditions, apply_subst_to_callee_env subst env env equals env up to
   TE_ProofGoal, which core_term_type ignores. *)
lemma apply_subst_to_term_preserves_typing:
  assumes typed: "core_term_type env mode tm = Some ty"
      and wf: "tyenv_well_formed env"
      and subst_wk: "\<forall>ty' \<in> fmran' subst. is_well_kinded env ty'"
      and subst_rt: "mode = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type env ty')"
      and locals_unaffected:
        "\<And>name ty'. fmlookup (TE_LocalVars env) name = Some ty'
                      \<Longrightarrow> apply_subst subst ty' = ty'"
      and ret_unaffected: "apply_subst subst (TE_ReturnType env) = TE_ReturnType env"
  shows "core_term_type env mode (apply_subst_to_term subst tm) = Some (apply_subst subst ty)"
proof -
  \<comment> \<open>fmmap is the identity on TE_LocalVars (each entry's type is unchanged
      under the substitution). \<close>
  have locals_id: "fmmap (apply_subst subst) (TE_LocalVars env) = TE_LocalVars env"
    by (meson fmap.map_ident_strong fmran'E locals_unaffected)

  \<comment> \<open>(i) The substituted callee env equals env up to TE_ProofGoal (the only
      field substitution can still touch under these assumptions). Since
      core_term_type ignores TE_ProofGoal, this is enough. \<close>
  have env_subst_id:
    "apply_subst_to_callee_env subst env env
       = env \<lparr> TE_ProofGoal := map_option (apply_subst_to_term subst) (TE_ProofGoal env) \<rparr>"
    unfolding apply_subst_to_callee_env_def
    by (simp add: locals_id ret_unaffected)

  \<comment> \<open>(ii) callee_env_subst_ok holds. The global field equalities are reflexive.
      For the TE_TypeVars condition: any tyvar in scope, if it's mapped by the
      substitution, the result is well-kinded in env (from subst_wk). If it's
      not mapped, it remains in scope. \<close>
  have ok: "callee_env_subst_ok subst env env"
    unfolding callee_env_subst_ok_def
  proof (intro conjI)
    show "TE_GlobalVars env = TE_GlobalVars env"
      "TE_GhostGlobals env = TE_GhostGlobals env"
      "TE_Functions env = TE_Functions env"
      "TE_Datatypes env = TE_Datatypes env"
      "TE_DataCtors env = TE_DataCtors env"
      "TE_DataCtorsByType env = TE_DataCtorsByType env"
      "TE_GhostDatatypes env = TE_GhostDatatypes env"
      by simp_all
  next
    show "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow>
              (case fmlookup subst n of
                 Some ty' \<Rightarrow> is_well_kinded env ty'
               | None \<Rightarrow> n |\<in>| TE_TypeVars env)"
      using subst_wk by (auto split: option.splits intro: fmran'I)
  qed

  \<comment> \<open>(iii) callee_env_subst_runtime_ok holds in NotGhost mode. \<close>
  have ok_rt: "mode = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst env env"
  proof
    assume ng: "mode = NotGhost"
    with subst_rt have rt: "\<forall>ty' \<in> fmran' subst. is_runtime_type env ty'" by simp
    show "callee_env_subst_runtime_ok subst env env"
      unfolding callee_env_subst_runtime_ok_def
      using rt by (auto split: option.splits intro: fmran'I)
  qed

  from core_term_type_subst_callee_env[OF typed wf ok subst_wk subst_rt ok_rt]
  show ?thesis
    unfolding env_subst_id
    by (simp add: core_term_type_TE_ProofGoal_irrelevant)
qed


(* If an impure call term has type retTy, then applying a subst to tyArgs and tmArgs
   applies the same subst to retTy, under similar conditions to 
   apply_subst_to_term_preserves_typing. *)
lemma apply_subst_core_impure_call_type:
  assumes ct: "core_impure_call_type env ghost fnName tyArgs tmArgs = Some retTy"
    and wf: "tyenv_well_formed env"
    and subst_wk: "\<forall>ty' \<in> fmran' subst. is_well_kinded env ty'"
    and subst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type env ty')"
    and locals_unaffected: "\<And>name ty'. fmlookup (TE_LocalVars env) name = Some ty'
                                         \<Longrightarrow> apply_subst subst ty' = ty'"
    and ret_unaffected: "apply_subst subst (TE_ReturnType env) = TE_ReturnType env"
  shows "core_impure_call_type env ghost fnName
           (map (apply_subst subst) tyArgs) (map (apply_subst_to_term subst) tmArgs)
           = Some (apply_subst subst retTy)"
proof -
  from core_impure_call_type_fn_facts[OF ct] obtain funInfo where
    fi: "fmlookup (TE_Functions env) fnName = Some funInfo" and
    len_ty: "length tyArgs = length (FI_TyArgs funInfo)" and
    wk: "list_all (is_well_kinded env) tyArgs" and
    rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) tyArgs" and
    fn_ng: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost" and
    len_tm: "length tmArgs = length (FI_TmArgs funInfo)" and
    ty_eq: "retTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo)" and
    l2_pure: "list_all2 (\<lambda>tm expectedTy.
                  case core_term_type env ghost tm of None \<Rightarrow> False
                  | Some actualTy \<Rightarrow> actualTy = expectedTy)
                tmArgs
                (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo))" and
    ref_lv: "\<forall>i < length tmArgs.
                snd (FI_TmArgs funInfo ! i) = Ref
                  \<longrightarrow> is_writable_lvalue env (tmArgs ! i)
                      \<and> ghost_lvalue_ok env ghost (tmArgs ! i)"
    by blast

  \<comment> \<open>Signature facts (distinctness + tyvar containment) for substitution composition.\<close>
  have distinct_tyargs: "distinct (FI_TyArgs funInfo)"
    using wf fi unfolding tyenv_well_formed_def tyenv_fun_tyvars_distinct_def by blast
  have fi_args_wk: "\<forall>t \<in> fst ` set (FI_TmArgs funInfo).
            is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) t"
    using wf fi unfolding tyenv_well_formed_def tyenv_fun_types_well_kinded_def by blast
  have fi_ret_wk: "is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) (FI_ReturnType funInfo)"
    using wf fi unfolding tyenv_well_formed_def tyenv_fun_types_well_kinded_def by blast
  have fi_args_tyvars: "\<forall>t \<in> fst ` set (FI_TmArgs funInfo). type_tyvars t \<subseteq> set (FI_TyArgs funInfo)"
  proof
    fix t assume "t \<in> fst ` set (FI_TmArgs funInfo)"
    with fi_args_wk have "is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) t" by blast
    from is_well_kinded_type_tyvars_subset[OF this]
    show "type_tyvars t \<subseteq> set (FI_TyArgs funInfo)" by (simp add: fset_of_list.rep_eq)
  qed
  have fi_ret_tyvars: "type_tyvars (FI_ReturnType funInfo) \<subseteq> set (FI_TyArgs funInfo)"
    using is_well_kinded_type_tyvars_subset[OF fi_ret_wk] by (simp add: fset_of_list.rep_eq)

  \<comment> \<open>Substituted ty-args stay well-kinded / runtime.\<close>
  have len_sty: "length (map (apply_subst subst) tyArgs) = length (FI_TyArgs funInfo)" using len_ty by simp
  have sty_wk: "list_all (is_well_kinded env) (map (apply_subst subst) tyArgs)"
    using wk subst_wk
    by (auto simp: list_all_iff intro!: apply_subst_preserves_well_kinded[where src=env and tgt=env]
             simp: fmran'I split: option.splits)
  have sty_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) (map (apply_subst subst) tyArgs)"
  proof
    assume ng: "ghost = NotGhost"
    show "list_all (is_runtime_type env) (map (apply_subst subst) tyArgs)"
      using rt[rule_format, OF ng] subst_rt[rule_format, OF ng]
      by (auto simp: list_all_iff intro!: apply_subst_preserves_runtime[where src=env and tgt=env]
               simp: fmran'I split: option.splits)
  qed

  \<comment> \<open>The substituted return type is the recomputation from the substituted ty-args.\<close>
  let ?subZip = "fmap_of_list (zip (FI_TyArgs funInfo) (map (apply_subst subst) tyArgs))"
  have ret_recompute: "apply_subst ?subZip (FI_ReturnType funInfo) = apply_subst subst retTy"
    using ty_eq apply_subst_compose_zip[OF len_ty[symmetric] fi_ret_tyvars distinct_tyargs] by simp

  \<comment> \<open>The substituted expected types are the recomputation from the substituted ty-args.\<close>
  let ?exps0 = "map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty) (FI_TmArgs funInfo)"
  let ?expsS = "map (\<lambda>(ty, _). apply_subst ?subZip ty) (FI_TmArgs funInfo)"
  have exps_recompute: "?expsS = map (apply_subst subst) ?exps0"
  proof -
    have "?expsS = map (\<lambda>(ty, _). apply_subst subst (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)) (FI_TmArgs funInfo)"
    proof (rule map_cong[OF refl])
      fix x assume "x \<in> set (FI_TmArgs funInfo)"
      obtain t v where x_eq: "x = (t, v)" by (cases x)
      with \<open>x \<in> set (FI_TmArgs funInfo)\<close> have "t \<in> fst ` set (FI_TmArgs funInfo)"
        by (force simp: rev_image_eqI)
      with fi_args_tyvars have "type_tyvars t \<subseteq> set (FI_TyArgs funInfo)" by blast
      thus "(case x of (ty, _) \<Rightarrow> apply_subst ?subZip ty)
            = (case x of (ty, _) \<Rightarrow> apply_subst subst (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty))"
        using x_eq apply_subst_compose_zip[OF len_ty[symmetric] _ distinct_tyargs] by simp
    qed
    also have "\<dots> = map (apply_subst subst) ?exps0" by (simp add: case_prod_unfold comp_def)
    finally show ?thesis .
  qed

  \<comment> \<open>Each substituted arg term typechecks to the substituted expected type.\<close>
  have len_pure: "length tmArgs = length ?exps0" using l2_pure by (simp add: list_all2_lengthD)
  have l2_subst: "list_all2 (\<lambda>tm expectedTy.
                    case core_term_type env ghost tm of None \<Rightarrow> False
                    | Some actualTy \<Rightarrow> actualTy = expectedTy)
                  (map (apply_subst_to_term subst) tmArgs) ?expsS"
    unfolding list_all2_conv_all_nth
  proof (intro conjI allI impI)
    show "length (map (apply_subst_to_term subst) tmArgs) = length ?expsS" using len_tm by simp
  next
    fix i assume i_lt: "i < length (map (apply_subst_to_term subst) tmArgs)"
    hence i_tm: "i < length tmArgs" by simp
    have "case core_term_type env ghost (tmArgs ! i) of None \<Rightarrow> False
          | Some actualTy \<Rightarrow> actualTy = ?exps0 ! i"
      using list_all2_nthD[OF l2_pure] i_tm len_pure by simp
    then obtain actualTy where
      tm_typed: "core_term_type env ghost (tmArgs ! i) = Some actualTy" and aeq: "actualTy = ?exps0 ! i"
      by (auto split: option.splits)
    have "core_term_type env ghost (apply_subst_to_term subst (tmArgs ! i)) = Some (apply_subst subst actualTy)"
      using apply_subst_to_term_preserves_typing[OF tm_typed wf subst_wk subst_rt locals_unaffected ret_unaffected] .
    moreover have "apply_subst subst (?exps0 ! i) = ?expsS ! i"
      using exps_recompute i_tm len_pure len_tm by simp
    ultimately show "case core_term_type env ghost (map (apply_subst_to_term subst) tmArgs ! i) of
                       None \<Rightarrow> False | Some actualTy' \<Rightarrow> actualTy' = ?expsS ! i"
      using i_tm aeq by simp
  qed

  \<comment> \<open>Ref positions stay writable lvalues (with the ghost discipline intact) under
      the term substitution.\<close>
  have ref_lv_subst: "\<forall>i < length (map (apply_subst_to_term subst) tmArgs).
                        snd (FI_TmArgs funInfo ! i) = Ref
                          \<longrightarrow> is_writable_lvalue env ((map (apply_subst_to_term subst) tmArgs) ! i)
                              \<and> ghost_lvalue_ok env ghost ((map (apply_subst_to_term subst) tmArgs) ! i)"
  proof (intro allI impI)
    fix i assume i_lt: "i < length (map (apply_subst_to_term subst) tmArgs)"
      and ref: "snd (FI_TmArgs funInfo ! i) = Ref"
    hence i_tm: "i < length tmArgs" by simp
    have "is_writable_lvalue env (tmArgs ! i)" and "ghost_lvalue_ok env ghost (tmArgs ! i)"
      using ref_lv i_tm ref by simp_all
    thus "is_writable_lvalue env ((map (apply_subst_to_term subst) tmArgs) ! i)
            \<and> ghost_lvalue_ok env ghost ((map (apply_subst_to_term subst) tmArgs) ! i)"
      using i_tm by simp
  qed

  \<comment> \<open>Reassemble the per-argument (Var/Ref) check for the substituted call.\<close>
  let ?P = "\<lambda>(tm, vor) expectedTy.
                 case vor of
                   Var \<Rightarrow> (case core_term_type env ghost tm of None \<Rightarrow> False
                            | Some actualTy \<Rightarrow> actualTy = expectedTy)
                 | Ref \<Rightarrow> is_writable_lvalue env tm
                          \<and> ghost_lvalue_ok env ghost tm
                          \<and> core_term_type env ghost tm = Some expectedTy"
  let ?zts = "zip (map (apply_subst_to_term subst) tmArgs) (map (\<lambda>(_, vor). vor) (FI_TmArgs funInfo))"
  have len_zts: "length ?zts = length ?expsS" using len_tm by simp
  have nth_pred: "\<And>i. i < length ?zts \<Longrightarrow> ?P (?zts ! i) (?expsS ! i)"
  proof -
    fix i assume i_lt: "i < length ?zts"
    hence i_tm: "i < length tmArgs" using len_tm by simp
    with len_tm have i_lt_fi: "i < length (FI_TmArgs funInfo)" by simp
    obtain ti vor where fi_arg: "FI_TmArgs funInfo ! i = (ti, vor)"
      by (cases "FI_TmArgs funInfo ! i") auto
    have zip_nth: "?zts ! i = ((map (apply_subst_to_term subst) tmArgs) ! i, vor)"
      using i_tm i_lt_fi fi_arg by simp
    have pure_i: "case core_term_type env ghost ((map (apply_subst_to_term subst) tmArgs) ! i) of
                    None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = ?expsS ! i"
      using list_all2_nthD[OF l2_subst] i_tm by simp
    show "?P (?zts ! i) (?expsS ! i)"
    proof (cases vor)
      case Var with zip_nth pure_i show ?thesis by simp
    next
      case Ref
      have "is_writable_lvalue env ((map (apply_subst_to_term subst) tmArgs) ! i)"
        and "ghost_lvalue_ok env ghost ((map (apply_subst_to_term subst) tmArgs) ! i)"
        using ref_lv_subst i_tm fi_arg Ref by simp_all
      moreover from pure_i have
        "core_term_type env ghost ((map (apply_subst_to_term subst) tmArgs) ! i) = Some (?expsS ! i)"
        by (auto split: option.splits)
      ultimately show ?thesis using Ref zip_nth by simp
    qed
  qed
  have l2_full: "list_all2 ?P ?zts ?expsS"
    using len_zts nth_pred by (simp add: list_all2_conv_all_nth)

  show ?thesis
    unfolding core_impure_call_type_def
    using fi sty_wk sty_rt fn_ng len_sty len_tm l2_full ret_recompute
    by (auto simp: Let_def)
qed


end
