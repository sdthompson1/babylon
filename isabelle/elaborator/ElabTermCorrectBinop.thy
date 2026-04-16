theory ElabTermCorrectBinop
  imports ElabTermCorrectHelpers
begin

(* ========================================================================== *)
(* Correctness of binary operator helpers *)
(* ========================================================================== *)

(* Correctness of check_and_coerce_binop: if the helper succeeds, the result is a
   CoreTm_Binop where both operands typecheck to a common type satisfying type_pred,
   and the common type is FiniteInt (when coercion was needed) or equal to the input types.
   The assumption that type_pred holds for all FiniteInt types is needed because
   coercion produces FiniteInt output. *)
lemma check_and_coerce_binop_correct:
  assumes "check_and_coerce_binop type_pred resultTyOverride errMsg cop
             lhsTm lhsTy rhsTm rhsTy loc babOp = Inr (resultTm, resultTy)"
    and "core_term_type env ghost lhsTm = Some lhsTy"
    and "core_term_type env ghost rhsTm = Some rhsTy"
    and "tyenv_well_formed env"
    and "\<And>s b. type_pred (CoreTy_FiniteInt s b)"
  shows "\<exists>opL opR commonTy.
    resultTm = CoreTm_Binop cop opL opR
    \<and> core_term_type env ghost opL = Some commonTy
    \<and> core_term_type env ghost opR = Some commonTy
    \<and> type_pred commonTy
    \<and> resultTy = (case resultTyOverride of None \<Rightarrow> commonTy | Some ty \<Rightarrow> ty)"
proof (cases "lhsTy = rhsTy")
  case True
  from assms(1) True have pred: "type_pred lhsTy"
    by (auto simp: check_and_coerce_binop_def Let_def split: if_splits)
  from assms(1) True pred have
    tm_eq: "resultTm = CoreTm_Binop cop lhsTm rhsTm" and
    ty_eq: "resultTy = (case resultTyOverride of None \<Rightarrow> lhsTy | Some ty \<Rightarrow> ty)"
    by (auto simp: check_and_coerce_binop_def Let_def)
  from pred tm_eq ty_eq assms(2,3) True show ?thesis
    by (intro exI[of _ lhsTm] exI[of _ rhsTm] exI[of _ lhsTy]) auto
next
  case False
  from assms(1) False have preds: "type_pred lhsTy" "type_pred rhsTy"
    by (auto simp: check_and_coerce_binop_def Let_def split: if_splits)
  from assms(1) False preds obtain newLhs newRhs commonTy where
    coerce: "coerce_to_common_int_type lhsTm lhsTy rhsTm rhsTy = Some (newLhs, newRhs, commonTy)" and
    tm_eq: "resultTm = CoreTm_Binop cop newLhs newRhs" and
    ty_eq: "resultTy = (case resultTyOverride of None \<Rightarrow> commonTy | Some ty \<Rightarrow> ty)"
    by (auto simp: check_and_coerce_binop_def Let_def split: option.splits)
  from coerce_to_common_int_type_correct[OF coerce assms(2,3,4)]
  have typed: "core_term_type env ghost newLhs = Some commonTy"
              "core_term_type env ghost newRhs = Some commonTy" by auto
  from coerce obtain s b where "commonTy = CoreTy_FiniteInt s b"
    by (cases lhsTy; cases rhsTy) (auto split: option.splits simp: Let_def)
  hence "type_pred commonTy" using assms(5) by simp
  with typed tm_eq ty_eq show ?thesis
    by (intro exI[of _ newLhs] exI[of _ newRhs] exI[of _ commonTy]) auto
qed

(* Helper: extract components from a successful build_comparison_chain in the let-binding case *)
lemma build_comparison_chain_let_elim:
  assumes "(case elab_binop_with_special is_flex loc ghost op lhsTm lhsTy varTm rhsTy of
              Inl errs \<Rightarrow> Inl errs
            | Inr (cmpTm, _) \<Rightarrow>
                (case build_comparison_chain is_flex loc ghost ctr' varTm rhsTy rest of
                  Inl errs \<Rightarrow> Inl errs
                | Inr restTm \<Rightarrow>
                    Inr (CoreTm_Let varName rhs
                          (CoreTm_Binop CoreBinop_And cmpTm restTm)))) = Inr resultTm"
  obtains cmpTm cmpTy restTm where
    "elab_binop_with_special is_flex loc ghost op lhsTm lhsTy varTm rhsTy = Inr (cmpTm, cmpTy)"
    "build_comparison_chain is_flex loc ghost ctr' varTm rhsTy rest = Inr restTm"
    "resultTm = CoreTm_Let varName rhs (CoreTm_Binop CoreBinop_And cmpTm restTm)"
  using assms by (auto split: sum.splits prod.splits)

(* Helper: range of fmap_of_list where all values are the same *)
lemma fmran'_fmap_of_list_const:
  "\<forall>ty' \<in> fmran' (fmap_of_list (map (\<lambda>n. (n, v)) ns)). ty' = v"
proof (induct ns)
  case Nil thus ?case by (simp add: fmran'_def fmlookup_of_list)
next
  case (Cons n ns)
  thus ?case by (auto simp: fmran'_def fmlookup_of_list)
qed

(* The range of const_subst_for contains only the default type *)
lemma const_subst_for_range:
  "\<forall>ty' \<in> fmran' (const_subst_for is_flex ty defaultTy). ty' = defaultTy"
  unfolding const_subst_for_def by (rule fmran'_fmap_of_list_const)

(* Helper: lookup in a constant-valued fmap_of_list *)
lemma fmlookup_fmap_of_list_const:
  "n \<in> set ns \<Longrightarrow> fmlookup (fmap_of_list (map (\<lambda>n. (n, v)) ns)) n = Some v"
  by (induct ns) (auto simp: fmlookup_of_list)

(* const_subst_for maps every flexible metavariable in the type *)
lemma const_subst_for_domain:
  "n \<in> type_tyvars ty \<Longrightarrow> is_flex n \<Longrightarrow>
   fmlookup (const_subst_for is_flex ty defaultTy) n = Some defaultTy"
  unfolding const_subst_for_def
  using fmlookup_fmap_of_list_const[of n "filter is_flex (type_tyvars_list ty)" defaultTy]
  by (simp add: set_type_tyvars_list)

(* Correctness of resolve_binop_metas: if the input terms typecheck at their types,
   the resolved terms typecheck at the resolved types. *)
lemma resolve_binop_metas_correct:
  assumes resolved: "resolve_binop_metas is_flex babOp lhsTm lhsTy rhsTm rhsTy = (lhsTm', lhsTy', rhsTm', rhsTy')"
    and lhs_typed: "core_term_type env ghost lhsTm = Some lhsTy"
    and rhs_typed: "core_term_type env ghost rhsTm = Some rhsTy"
    and wf: "tyenv_well_formed env"
    and locals_rigid: "\<forall>name ty' n. fmlookup (TE_LocalVars env) name = Some ty'
                         \<longrightarrow> n \<in> type_tyvars ty' \<longrightarrow> \<not> is_flex n"
    and ret_rigid: "\<forall>n. n \<in> type_tyvars (TE_ReturnType env) \<longrightarrow> \<not> is_flex n"
  shows "core_term_type env ghost lhsTm' = Some lhsTy'
       \<and> core_term_type env ghost rhsTm' = Some rhsTy'"
proof (cases "unify is_flex lhsTy rhsTy")
  case None
  \<comment> \<open>Unification failed: pass through unchanged\<close>
  from resolved None have "lhsTm' = lhsTm" "lhsTy' = lhsTy" "rhsTm' = rhsTm" "rhsTy' = rhsTy"
    by simp_all
  thus ?thesis using lhs_typed rhs_typed by simp
next
  case (Some unifSubst)
  let ?unifiedTy = "apply_subst unifSubst lhsTy"
  have sound: "apply_subst unifSubst lhsTy = apply_subst unifSubst rhsTy"
    using unify_sound[OF Some] .

  \<comment> \<open>Substitution range is well-kinded and runtime\<close>
  have lhs_wk: "is_well_kinded env lhsTy"
    using core_term_type_well_kinded[OF lhs_typed wf] .
  have rhs_wk: "is_well_kinded env rhsTy"
    using core_term_type_well_kinded[OF rhs_typed wf] .
  have unif_range_wk: "\<forall>ty' \<in> fmran' unifSubst. is_well_kinded env ty'"
    using unify_preserves_well_kinded[OF Some lhs_wk rhs_wk] .
  have unif_range_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' unifSubst. is_runtime_type env ty')"
  proof
    assume ng: "ghost = NotGhost"
    have "is_runtime_type env lhsTy"
      using core_term_type_notghost_runtime lhs_typed wf ng by auto
    moreover have "is_runtime_type env rhsTy"
      using core_term_type_notghost_runtime wf ng rhs_typed by auto
    ultimately show "\<forall>ty' \<in> fmran' unifSubst. is_runtime_type env ty'"
      using unify_preserves_runtime[OF Some] by auto
  qed

  \<comment> \<open>Helper: applying unifSubst preserves well-kindedness / runtime (src = tgt = env)\<close>
  have unif_apply_wk: "\<And>t. is_well_kinded env t \<Longrightarrow> is_well_kinded env (apply_subst unifSubst t)"
  proof -
    fix t assume t_wk: "is_well_kinded env t"
    show "is_well_kinded env (apply_subst unifSubst t)"
    proof (rule apply_subst_preserves_well_kinded[OF t_wk])
      show "TE_Datatypes env = TE_Datatypes env" by simp
    next
      fix n assume n_in: "n |\<in>| TE_TypeVars env"
      show "case fmlookup unifSubst n of
              Some ty' \<Rightarrow> is_well_kinded env ty'
            | None \<Rightarrow> n |\<in>| TE_TypeVars env"
        using n_in unif_range_wk by (auto simp: fmran'I split: option.splits)
    qed
  qed
  have unif_apply_rt: "\<And>t. ghost = NotGhost \<Longrightarrow> is_runtime_type env t \<Longrightarrow>
                           is_runtime_type env (apply_subst unifSubst t)"
  proof -
    fix t assume ng: "ghost = NotGhost" and t_rt: "is_runtime_type env t"
    show "is_runtime_type env (apply_subst unifSubst t)"
    proof (rule apply_subst_preserves_runtime[OF t_rt])
      show "TE_GhostDatatypes env = TE_GhostDatatypes env" by simp
    next
      fix n assume n_in: "n |\<in>| TE_RuntimeTypeVars env"
      show "case fmlookup unifSubst n of
              Some ty' \<Rightarrow> is_runtime_type env ty'
            | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars env"
        using n_in unif_range_rt ng by (auto simp: fmran'I split: option.splits)
    qed
  qed

  \<comment> \<open>The unifier only binds flex metavars. Combined with the caller's
      rigidity assumptions on locals and the return type, the substitution
      leaves them unchanged. \<close>
  have unif_dom_flex: "\<forall>n. n |\<in>| fmdom unifSubst \<longrightarrow> is_flex n"
    using unify_unify_list_dom_flex(1)[OF Some] .

  have locals_unaffected:
    "\<And>name ty'. fmlookup (TE_LocalVars env) name = Some ty' \<Longrightarrow> apply_subst unifSubst ty' = ty'"
  proof -
    fix name ty' assume lk: "fmlookup (TE_LocalVars env) name = Some ty'"
    have "type_tyvars ty' \<inter> fset (fmdom unifSubst) = {}"
    proof -
      { fix n assume n_mv: "n \<in> type_tyvars ty'" and n_dom: "n \<in> fset (fmdom unifSubst)"
        from n_dom have "n |\<in>| fmdom unifSubst" by simp
        with unif_dom_flex have "is_flex n" by blast
        moreover from locals_rigid lk n_mv have "\<not> is_flex n" by blast
        ultimately have False by simp
      }
      thus ?thesis by auto
    qed
    thus "apply_subst unifSubst ty' = ty'"
      by (rule apply_subst_disjoint_id)
  qed
  have ret_unaffected: "apply_subst unifSubst (TE_ReturnType env) = TE_ReturnType env"
  proof -
    have "type_tyvars (TE_ReturnType env) \<inter> fset (fmdom unifSubst) = {}"
    proof -
      { fix n assume n_mv: "n \<in> type_tyvars (TE_ReturnType env)"
                 and n_dom: "n \<in> fset (fmdom unifSubst)"
        from n_dom have "n |\<in>| fmdom unifSubst" by simp
        with unif_dom_flex have "is_flex n" by blast
        moreover from ret_rigid n_mv have "\<not> is_flex n" by blast
        ultimately have False by simp
      }
      thus ?thesis by auto
    qed
    thus ?thesis by (rule apply_subst_disjoint_id)
  qed

  \<comment> \<open>Both terms typecheck after applying unifSubst\<close>
  have lhs_unif: "core_term_type env ghost (apply_subst_to_term unifSubst lhsTm) = Some ?unifiedTy"
    using apply_subst_to_term_preserves_typing
            [OF lhs_typed wf unif_range_wk unif_range_rt locals_unaffected ret_unaffected]
    by simp
  have rhs_unif: "core_term_type env ghost (apply_subst_to_term unifSubst rhsTm) = Some ?unifiedTy"
    using apply_subst_to_term_preserves_typing
            [OF rhs_typed wf unif_range_wk unif_range_rt locals_unaffected ret_unaffected]
          sound
    by simp

  show ?thesis
  proof (cases "list_all (\<lambda>n. \<not> is_flex n) (type_tyvars_list ?unifiedTy)")
    case True
    \<comment> \<open>Resolved: directly use unified type\<close>
    from resolved Some True have
      eqs: "lhsTm' = apply_subst_to_term unifSubst lhsTm"
           "lhsTy' = ?unifiedTy"
           "rhsTm' = apply_subst_to_term unifSubst rhsTm"
           "rhsTy' = ?unifiedTy"
      by (auto simp: Let_def)
    show ?thesis using lhs_unif rhs_unif eqs by simp
  next
    case not_resolved: False
    \<comment> \<open>Not resolved: fill remaining flexible metas with default type\<close>
    let ?defaultTy = "default_type_for_binop babOp"
    let ?fillSubst = "const_subst_for is_flex ?unifiedTy ?defaultTy"
    let ?fullSubst = "compose_subst ?fillSubst unifSubst"
    from resolved Some not_resolved have
      eqs: "lhsTm' = apply_subst_to_term ?fullSubst lhsTm"
           "lhsTy' = apply_subst ?fillSubst ?unifiedTy"
           "rhsTm' = apply_subst_to_term ?fullSubst rhsTm"
           "rhsTy' = apply_subst ?fillSubst ?unifiedTy"
      by (auto simp: Let_def)

    \<comment> \<open>The default type is well-kinded and runtime\<close>
    have default_wk: "is_well_kinded env ?defaultTy"
      by (auto simp: default_type_for_binop_def split: option.splits)
    have default_rt: "is_runtime_type env ?defaultTy"
      by (auto simp: default_type_for_binop_def split: option.splits)

    \<comment> \<open>The fill substitution range is well-kinded and runtime\<close>
    have fill_range_wk: "\<forall>ty' \<in> fmran' ?fillSubst. is_well_kinded env ty'"
      using const_subst_for_range[of is_flex ?unifiedTy ?defaultTy] default_wk by metis
    have fill_range_rt: "\<forall>ty' \<in> fmran' ?fillSubst. is_runtime_type env ty'"
      using const_subst_for_range[of is_flex ?unifiedTy ?defaultTy] default_rt by metis

    \<comment> \<open>Full substitution range is well-kinded and runtime\<close>
    have full_range_wk: "\<forall>ty' \<in> fmran' ?fullSubst. is_well_kinded env ty'"
      using compose_subst_preserves_well_kinded fill_range_wk unif_range_wk by blast
    have full_range_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' ?fullSubst. is_runtime_type env ty')"
    proof
      assume ng: "ghost = NotGhost"
      from unif_range_rt ng have "\<forall>ty' \<in> fmran' unifSubst. is_runtime_type env ty'" by simp
      from compose_subst_preserves_runtime[OF fill_range_rt this]
      show "\<forall>ty' \<in> fmran' ?fullSubst. is_runtime_type env ty'"
        using Some compose_subst_preserves_runtime core_term_type_well_kinded_and_runtime fill_range_rt
          lhs_typed local.wf ng rhs_typed unify_preserves_runtime by presburger
    qed

    \<comment> \<open>?fullSubst's domain is contained in flex metavars: it's the union of
        unifSubst's domain (from unify_dom_flex) and ?fillSubst's domain
        (filtered to flex by const_subst_for's definition). \<close>
    have fill_dom_flex: "\<forall>n. n |\<in>| fmdom ?fillSubst \<longrightarrow> is_flex n"
      unfolding const_subst_for_def
      by auto
    have full_dom_flex: "\<forall>n. n |\<in>| fmdom ?fullSubst \<longrightarrow> is_flex n"
      using unif_dom_flex fill_dom_flex
      by (auto simp: compose_subst_def)

    have locals_unaffected_full:
      "\<And>name ty'. fmlookup (TE_LocalVars env) name = Some ty' \<Longrightarrow> apply_subst ?fullSubst ty' = ty'"
    proof -
      fix name ty' assume lk: "fmlookup (TE_LocalVars env) name = Some ty'"
      have "type_tyvars ty' \<inter> fset (fmdom ?fullSubst) = {}"
      proof -
        { fix n assume n_mv: "n \<in> type_tyvars ty'"
                    and n_dom: "n \<in> fset (fmdom ?fullSubst)"
          from n_dom have "n |\<in>| fmdom ?fullSubst" by simp
          with full_dom_flex have "is_flex n" by blast
          moreover from locals_rigid lk n_mv have "\<not> is_flex n" by blast
          ultimately have False by simp
        }
        thus ?thesis by auto
      qed
      thus "apply_subst ?fullSubst ty' = ty'"
        by (rule apply_subst_disjoint_id)
    qed
    have ret_unaffected_full: "apply_subst ?fullSubst (TE_ReturnType env) = TE_ReturnType env"
    proof -
      have "type_tyvars (TE_ReturnType env) \<inter> fset (fmdom ?fullSubst) = {}"
      proof -
        { fix n assume n_mv: "n \<in> type_tyvars (TE_ReturnType env)"
                    and n_dom: "n \<in> fset (fmdom ?fullSubst)"
          from n_dom have "n |\<in>| fmdom ?fullSubst" by simp
          with full_dom_flex have "is_flex n" by blast
          moreover from ret_rigid n_mv have "\<not> is_flex n" by blast
          ultimately have False by simp
        }
        thus ?thesis by auto
      qed
      thus ?thesis by (rule apply_subst_disjoint_id)
    qed

    \<comment> \<open>Applying fullSubst preserves typing\<close>
    have lhs_full: "core_term_type env ghost (apply_subst_to_term ?fullSubst lhsTm) =
                    Some (apply_subst ?fullSubst lhsTy)"
      using apply_subst_to_term_preserves_typing
              [OF lhs_typed wf full_range_wk full_range_rt
                  locals_unaffected_full ret_unaffected_full]
      by simp
    have rhs_full: "core_term_type env ghost (apply_subst_to_term ?fullSubst rhsTm) =
                    Some (apply_subst ?fullSubst rhsTy)"
      using apply_subst_to_term_preserves_typing
              [OF rhs_typed wf full_range_wk full_range_rt
                  locals_unaffected_full ret_unaffected_full]
      by simp

    \<comment> \<open>apply_subst ?fullSubst lhsTy = apply_subst ?fillSubst ?unifiedTy via compose_subst_correct\<close>
    have lhs_eq: "apply_subst ?fullSubst lhsTy = apply_subst ?fillSubst ?unifiedTy"
      by (simp add: compose_subst_correct)
    have rhs_eq: "apply_subst ?fullSubst rhsTy = apply_subst ?fillSubst ?unifiedTy"
      using sound by (simp add: compose_subst_correct)

    show ?thesis using lhs_full rhs_full lhs_eq rhs_eq eqs by simp
  qed
qed

(* Correctness of elab_single_binop: if elaboration succeeds, the result typechecks. *)
lemma elab_single_binop_correct:
  assumes "elab_single_binop is_flex loc ghost babOp lhsTm lhsTy rhsTm rhsTy = Inr (resultTm, resultTy)"
    and "core_term_type env ghost lhsTm = Some lhsTy"
    and "core_term_type env ghost rhsTm = Some rhsTy"
    and "tyenv_well_formed env"
    and "binop_to_core babOp = Some cop"
    and locals_rigid: "\<forall>name ty' n. fmlookup (TE_LocalVars env) name = Some ty'
                         \<longrightarrow> n \<in> type_tyvars ty' \<longrightarrow> \<not> is_flex n"
    and ret_rigid: "\<forall>n. n \<in> type_tyvars (TE_ReturnType env) \<longrightarrow> \<not> is_flex n"
  shows "core_term_type env ghost resultTm = Some resultTy"
proof -
  obtain lhsTm' lhsTy' rhsTm' rhsTy' where
    resolved: "resolve_binop_metas is_flex babOp lhsTm lhsTy rhsTm rhsTy = (lhsTm', lhsTy', rhsTm', rhsTy')"
    by (cases "resolve_binop_metas is_flex babOp lhsTm lhsTy rhsTm rhsTy") auto
  have lhs': "core_term_type env ghost lhsTm' = Some lhsTy'"
    and rhs': "core_term_type env ghost rhsTm' = Some rhsTy'"
    using resolve_binop_metas_correct[OF resolved assms(2,3,4) locals_rigid ret_rigid] by auto

  have cop: "binop_to_core babOp = Some cop" using assms(5) .

  \<comment> \<open>Case-split on the binop category using exhaustiveness\<close>
  consider (arith) "is_arithmetic_binop cop"
    | (modulo) "\<not> is_arithmetic_binop cop" "is_modulo_binop cop"
    | (bitwise) "\<not> is_arithmetic_binop cop" "\<not> is_modulo_binop cop" "is_bitwise_binop cop"
    | (shift) "\<not> is_arithmetic_binop cop" "\<not> is_modulo_binop cop" "\<not> is_bitwise_binop cop"
              "is_shift_binop cop"
    | (ordering) "\<not> is_arithmetic_binop cop" "\<not> is_modulo_binop cop" "\<not> is_bitwise_binop cop"
                 "\<not> is_shift_binop cop" "is_ordering_binop cop"
    | (eq_neq) "\<not> is_arithmetic_binop cop" "\<not> is_modulo_binop cop" "\<not> is_bitwise_binop cop"
               "\<not> is_shift_binop cop" "\<not> is_ordering_binop cop" "is_eq_neq_binop cop"
    | (logical) "\<not> is_arithmetic_binop cop" "\<not> is_modulo_binop cop" "\<not> is_bitwise_binop cop"
                "\<not> is_shift_binop cop" "\<not> is_ordering_binop cop" "\<not> is_eq_neq_binop cop"
                "is_logical_binop cop"
    using binop_category_exhaustive[of cop] by blast
  then show ?thesis
  proof cases
    \<comment> \<open>Arithmetic: both numeric, same type or coerced to common type\<close>
    case arith
    from assms(1) resolved cop arith have
      "check_and_coerce_binop is_numeric_type None TyErr_BinopRequiresNumeric cop
         lhsTm' lhsTy' rhsTm' rhsTy' loc babOp = Inr (resultTm, resultTy)"
      by (simp add: Let_def)
    from check_and_coerce_binop_correct[OF this lhs' rhs' assms(4)]
    obtain opL opR commonTy where
      tm_eq: "resultTm = CoreTm_Binop cop opL opR" and
      opL_ty: "core_term_type env ghost opL = Some commonTy" and
      opR_ty: "core_term_type env ghost opR = Some commonTy" and
      pred: "is_numeric_type commonTy" and ty_eq: "resultTy = commonTy"
      by auto
    with arith show ?thesis by auto
  next
    \<comment> \<open>Modulo: both integer, same type or coerced\<close>
    case modulo
    from assms(1) resolved cop modulo have
      "check_and_coerce_binop is_integer_type None TyErr_BinopRequiresInteger cop
         lhsTm' lhsTy' rhsTm' rhsTy' loc babOp = Inr (resultTm, resultTy)"
      by (simp add: Let_def)
    from check_and_coerce_binop_correct[OF this lhs' rhs' assms(4)]
    obtain opL opR commonTy where
      tm_eq: "resultTm = CoreTm_Binop cop opL opR" and
      opL_ty: "core_term_type env ghost opL = Some commonTy" and
      opR_ty: "core_term_type env ghost opR = Some commonTy" and
      pred: "is_integer_type commonTy" and ty_eq: "resultTy = commonTy"
      by auto
    with modulo show ?thesis by auto
  next
    \<comment> \<open>Bitwise: both finite integer, same type or coerced\<close>
    case bitwise
    from assms(1) resolved cop bitwise have
      "check_and_coerce_binop is_finite_integer_type None TyErr_BinopRequiresFiniteInteger cop
         lhsTm' lhsTy' rhsTm' rhsTy' loc babOp = Inr (resultTm, resultTy)"
      by (simp add: Let_def)
    from check_and_coerce_binop_correct[OF this lhs' rhs' assms(4)]
    obtain opL opR commonTy where
      tm_eq: "resultTm = CoreTm_Binop cop opL opR" and
      opL_ty: "core_term_type env ghost opL = Some commonTy" and
      opR_ty: "core_term_type env ghost opR = Some commonTy" and
      pred: "is_finite_integer_type commonTy" and ty_eq: "resultTy = commonTy"
      by auto
    with bitwise show ?thesis by auto
  next
    \<comment> \<open>Shift: both finite integer, cast RHS to LHS type\<close>
    case shift
    from assms(1) resolved cop shift have
      fin_lhs: "is_finite_integer_type lhsTy'" and fin_rhs: "is_finite_integer_type rhsTy'" and
      tm_eq: "resultTm = CoreTm_Binop cop lhsTm' (if lhsTy' = rhsTy' then rhsTm' else CoreTm_Cast lhsTy' rhsTm')" and
      ty_eq: "resultTy = lhsTy'"
      by (auto simp: Let_def split: if_splits)
    have cast_typed: "core_term_type env ghost (if lhsTy' = rhsTy' then rhsTm' else CoreTm_Cast lhsTy' rhsTm') = Some lhsTy'"
    proof (cases "lhsTy' = rhsTy'")
      case True
      then show ?thesis using rhs' by simp
    next
      case False
      have "is_integer_type rhsTy'" using fin_rhs finite_integer_type_is_integer_type by simp
      moreover have "is_integer_type lhsTy'" using fin_lhs finite_integer_type_is_integer_type by simp
      moreover have "is_runtime_type env lhsTy'" using fin_lhs by (cases lhsTy') auto
      ultimately show ?thesis using rhs' False by auto
    qed
    with lhs' fin_lhs shift tm_eq ty_eq show ?thesis by auto
  next
    \<comment> \<open>Ordering: both numeric, result is Bool\<close>
    case ordering
    from assms(1) resolved cop ordering have
      "check_and_coerce_binop is_numeric_type (Some CoreTy_Bool) TyErr_BinopRequiresNumeric cop
         lhsTm' lhsTy' rhsTm' rhsTy' loc babOp = Inr (resultTm, resultTy)"
      by (simp add: Let_def)
    from check_and_coerce_binop_correct[OF this lhs' rhs' assms(4)]
    obtain opL opR commonTy where
      tm_eq: "resultTm = CoreTm_Binop cop opL opR" and
      opL_ty: "core_term_type env ghost opL = Some commonTy" and
      opR_ty: "core_term_type env ghost opR = Some commonTy" and
      pred: "is_numeric_type commonTy" and ty_eq: "resultTy = CoreTy_Bool"
      by auto
    with ordering show ?thesis by auto
  next
    \<comment> \<open>Equality/inequality\<close>
    case eq_neq
    show ?thesis
    proof (cases "lhsTy' = rhsTy'")
      case True
      with assms(1) resolved cop eq_neq have
        cond: "ghost = Ghost \<or> lhsTy' = CoreTy_Bool \<or> is_numeric_type lhsTy'" and
        tm_eq: "resultTm = CoreTm_Binop cop lhsTm' rhsTm'" and ty_eq: "resultTy = CoreTy_Bool"
        by (auto simp: Let_def split: if_splits)
      with lhs' rhs' eq_neq True show ?thesis by auto
    next
      case False
      with assms(1) resolved cop eq_neq obtain newLhs newRhs commonTy where
        coerce: "coerce_to_common_int_type lhsTm' lhsTy' rhsTm' rhsTy' = Some (newLhs, newRhs, commonTy)"
        and tm_eq: "resultTm = CoreTm_Binop cop newLhs newRhs" and ty_eq: "resultTy = CoreTy_Bool"
        by (auto simp: Let_def split: option.splits if_splits)
      from coerce_to_common_int_type_correct[OF coerce lhs' rhs' assms(4)]
      have typed: "core_term_type env ghost newLhs = Some commonTy"
                  "core_term_type env ghost newRhs = Some commonTy" by auto
      from coerce have "is_finite_integer_type commonTy"
        by (cases lhsTy'; cases rhsTy') (auto split: option.splits simp: Let_def)
      hence "is_numeric_type commonTy" by (cases commonTy) auto
      with typed eq_neq tm_eq ty_eq show ?thesis by auto
    qed
  next
    \<comment> \<open>Logical: both Bool\<close>
    case logical
    from assms(1) resolved cop logical have
      "lhsTy' = CoreTy_Bool" "rhsTy' = CoreTy_Bool"
      "resultTm = CoreTm_Binop cop lhsTm' rhsTm'" "resultTy = CoreTy_Bool"
      by (auto simp: Let_def split: if_splits)
    with lhs' rhs' logical show ?thesis by auto
  qed
qed

(* Correctness of elab_binop_with_special *)
lemma elab_binop_with_special_correct:
  assumes "elab_binop_with_special is_flex loc ghost babOp lhsTm lhsTy rhsTm rhsTy = Inr (resultTm, resultTy)"
    and "core_term_type env ghost lhsTm = Some lhsTy"
    and "core_term_type env ghost rhsTm = Some rhsTy"
    and "tyenv_well_formed env"
    and locals_rigid: "\<forall>name ty' n. fmlookup (TE_LocalVars env) name = Some ty'
                         \<longrightarrow> n \<in> type_tyvars ty' \<longrightarrow> \<not> is_flex n"
    and ret_rigid: "\<forall>n. n \<in> type_tyvars (TE_ReturnType env) \<longrightarrow> \<not> is_flex n"
  shows "core_term_type env ghost resultTm = Some resultTy"
proof (cases "babOp = BabBinop_ImpliedBy \<or> babOp = BabBinop_Iff")
  case True
  then show ?thesis
  proof
    assume "babOp = BabBinop_ImpliedBy"
    \<comment> \<open>ImpliedBy: swaps operands and calls elab_single_binop with Implies\<close>
    with assms(1) have
      "elab_single_binop is_flex loc ghost BabBinop_Implies rhsTm rhsTy lhsTm lhsTy = Inr (resultTm, resultTy)"
      by simp
    thus ?thesis using elab_single_binop_correct[OF _ assms(3,2,4) _ locals_rigid ret_rigid]
      using binop_to_core.simps(19) by blast
  next
    assume iff: "babOp = BabBinop_Iff"
    \<comment> \<open>Iff: resolves metas then checks both Bool\<close>
    obtain lhsTm' lhsTy' rhsTm' rhsTy' where
      resolved: "resolve_binop_metas is_flex BabBinop_Iff lhsTm lhsTy rhsTm rhsTy = (lhsTm', lhsTy', rhsTm', rhsTy')"
      by (cases "resolve_binop_metas is_flex BabBinop_Iff lhsTm lhsTy rhsTm rhsTy") auto
    have lhs': "core_term_type env ghost lhsTm' = Some lhsTy'"
      and rhs': "core_term_type env ghost rhsTm' = Some rhsTy'"
      using resolve_binop_metas_correct[OF resolved assms(2,3,4) locals_rigid ret_rigid] by auto
    from assms(1) iff resolved have
      "lhsTy' = CoreTy_Bool" "rhsTy' = CoreTy_Bool"
      "resultTm = CoreTm_Binop CoreBinop_Equal lhsTm' rhsTm'" "resultTy = CoreTy_Bool"
      by (auto simp: Let_def split: if_splits)
    with lhs' rhs' show ?thesis by auto
  qed
next
  case False
  \<comment> \<open>All other cases: elab_binop_with_special delegates to elab_single_binop\<close>
  hence eq: "elab_binop_with_special is_flex loc ghost babOp lhsTm lhsTy rhsTm rhsTy
       = elab_single_binop is_flex loc ghost babOp lhsTm lhsTy rhsTm rhsTy"
    by (cases babOp) simp_all
  from False obtain cop where "binop_to_core babOp = Some cop"
    by (cases babOp) auto
  with assms(1) eq show ?thesis
    using elab_single_binop_correct assms(2,3,4) locals_rigid ret_rigid by auto
qed

(* For comparison operators (those with a comparison_direction), elab_binop_with_special
   always returns CoreTy_Bool as the result type when it succeeds. *)
lemma elab_binop_with_special_comparison_bool:
  assumes "elab_binop_with_special is_flex loc ghost babOp lhsTm lhsTy rhsTm rhsTy = Inr (resultTm, resultTy)"
    and "comparison_direction babOp \<noteq> None"
  shows "resultTy = CoreTy_Bool"
proof -
  \<comment> \<open>comparison_direction is only Some for <, <=, >, >=, ==, !=\<close>
  from assms(2) have "babOp \<in> {BabBinop_Less, BabBinop_LessEqual, BabBinop_Greater,
    BabBinop_GreaterEqual, BabBinop_Equal, BabBinop_NotEqual}"
    by (cases babOp) auto
  \<comment> \<open>None of these are ImpliedBy or Iff, so elab_binop_with_special calls elab_single_binop\<close>
  hence eq: "elab_single_binop is_flex loc ghost babOp lhsTm lhsTy rhsTm rhsTy = Inr (resultTm, resultTy)"
    using assms(1) by auto
  \<comment> \<open>For each of these 6 ops, elab_single_binop returns CoreTy_Bool on success\<close>
  from \<open>babOp \<in> _\<close> eq show "resultTy = CoreTy_Bool"
    by (cases babOp; simp add: check_and_coerce_binop_def Let_def
                      split: prod.splits option.splits if_splits)
qed

(* If check_comparison_chain_directions succeeds, all ops are comparisons *)
lemma check_comparison_chain_directions_all_comparison:
  assumes "check_comparison_chain_directions ops dir"
    and "(op, tm, ty) \<in> set ops"
  shows "comparison_direction op \<noteq> None"
  using assms by (induction ops arbitrary: dir) (auto split: option.splits if_splits)

(* Correctness of fold_binop_left *)
lemma fold_binop_left_correct:
  assumes "fold_binop_left is_flex loc ghost accTm accTy ops = Inr (resultTm, resultTy)"
    and "core_term_type env ghost accTm = Some accTy"
    and "list_all (\<lambda>(op, tm, ty). core_term_type env ghost tm = Some ty) ops"
    and "tyenv_well_formed env"
    and locals_rigid: "\<forall>name ty' n. fmlookup (TE_LocalVars env) name = Some ty'
                         \<longrightarrow> n \<in> type_tyvars ty' \<longrightarrow> \<not> is_flex n"
    and ret_rigid: "\<forall>n. n \<in> type_tyvars (TE_ReturnType env) \<longrightarrow> \<not> is_flex n"
  shows "core_term_type env ghost resultTm = Some resultTy"
using assms proof (induction ops arbitrary: accTm accTy)
  case Nil
  then show ?case by simp
next
  case (Cons triple rest)
  obtain op rhsTm rhsTy where triple_eq: "triple = (op, rhsTm, rhsTy)"
    by (cases triple) auto
  from Cons.prems(1) triple_eq obtain midTm midTy where
    step: "elab_binop_with_special is_flex loc ghost op accTm accTy rhsTm rhsTy = Inr (midTm, midTy)" and
    rest: "fold_binop_left is_flex loc ghost midTm midTy rest = Inr (resultTm, resultTy)"
    by (auto split: sum.splits)
  have mid_typed: "core_term_type env ghost midTm = Some midTy"
    using elab_binop_with_special_correct[OF step Cons.prems(2) _ Cons.prems(4)
                                               Cons.prems(5) Cons.prems(6)]
      Cons.prems(3) triple_eq by simp
  show ?case using Cons.IH[OF rest mid_typed] Cons.prems(3,4,5,6) triple_eq by simp
qed

(* Correctness of fold_implies_right *)
lemma fold_implies_right_correct:
  assumes "fold_implies_right is_flex loc ghost lhsTm lhsTy ops = Inr (resultTm, resultTy)"
    and "core_term_type env ghost lhsTm = Some lhsTy"
    and "list_all (\<lambda>(op, tm, ty). core_term_type env ghost tm = Some ty) ops"
    and "tyenv_well_formed env"
    and locals_rigid: "\<forall>name ty' n. fmlookup (TE_LocalVars env) name = Some ty'
                         \<longrightarrow> n \<in> type_tyvars ty' \<longrightarrow> \<not> is_flex n"
    and ret_rigid: "\<forall>n. n \<in> type_tyvars (TE_ReturnType env) \<longrightarrow> \<not> is_flex n"
  shows "core_term_type env ghost resultTm = Some resultTy"
using assms proof (induction ops arbitrary: lhsTm lhsTy resultTm resultTy)
  case Nil
  then show ?case by simp
next
  case (Cons triple rest)
  obtain op rhsTm rhsTy where triple_eq: "triple = (op, rhsTm, rhsTy)"
    by (cases triple) auto
  have rhs_typed: "core_term_type env ghost rhsTm = Some rhsTy"
    using Cons.prems(3) triple_eq by simp
  show ?case
  proof (cases rest)
    case Nil
    \<comment> \<open>Single element: just call elab_binop_with_special\<close>
    from Cons.prems(1) triple_eq Nil have
      "elab_binop_with_special is_flex loc ghost op lhsTm lhsTy rhsTm rhsTy = Inr (resultTm, resultTy)"
      by simp
    thus ?thesis
      using elab_binop_with_special_correct Cons.prems(2) rhs_typed Cons.prems(4)
            Cons.prems(5) Cons.prems(6) by blast
  next
    case (Cons triple2 rest2)
    \<comment> \<open>Multiple elements: recurse on right side, then combine\<close>
    from Cons.prems(1) triple_eq \<open>rest = triple2 # rest2\<close> obtain rightTm rightTy where
      recurse: "fold_implies_right is_flex loc ghost rhsTm rhsTy rest = Inr (rightTm, rightTy)" and
      combine: "elab_binop_with_special is_flex loc ghost op lhsTm lhsTy rightTm rightTy = Inr (resultTm, resultTy)"
      by (auto split: sum.splits)
    have rest_all: "list_all (\<lambda>(op, tm, ty). core_term_type env ghost tm = Some ty) rest"
      using Cons.prems(3) triple_eq by simp
    have right_typed: "core_term_type env ghost rightTm = Some rightTy"
      using Cons.IH[OF recurse rhs_typed rest_all Cons.prems(4) Cons.prems(5) Cons.prems(6)] .
    show ?thesis
      using elab_binop_with_special_correct[OF combine Cons.prems(2) right_typed
                          Cons.prems(4) Cons.prems(5) Cons.prems(6)] .
  qed
qed

(* Helper: ''chain@@'' @ nat_to_string n starts with ''chain@@'' *)
lemma chain_var_prefix: "take 7 (''chain@@'' @ nat_to_string n) = ''chain@@''"
  by simp

(* Helper: the empty string does not start with ''chain@@'' *)
lemma empty_not_chain_prefix: "take 7 '''' \<noteq> ''chain@@''"
  by simp

(* Helper: if has_unexpected_chain_var returns False, then the only chain@@-prefixed
   free variable (if any) is the allowed one. *)
lemma not_has_unexpected_chain_var:
  assumes "\<not> has_unexpected_chain_var tm allowed"
    and "v \<in> core_term_free_vars tm"
    and "take 7 v = ''chain@@''"
  shows "v = allowed"
  using assms by (auto simp: has_unexpected_chain_var_def)

(* If build_comparison_chain returns Inr, then chain@@ variables (with index >= chainCtr)
   are not free in lhsTm, and chain@@ variables are not free in the op terms.
   This follows from the has_unexpected_chain_var runtime checks.
   We prove a combined statement to avoid issues with multi-conclusion induction. *)
lemma build_comparison_chain_inputs_fresh_combined:
  assumes "build_comparison_chain is_flex loc ghost chainCtr lhsTm lhsTy ops = Inr resultTm"
  shows "(\<forall>n \<ge> chainCtr. ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars lhsTm)
       \<and> (\<forall>opx \<in> set ops. \<forall>n. ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars (fst (snd opx)))"
  using assms
proof (induction ops arbitrary: chainCtr lhsTm lhsTy resultTm)
  case Nil
  \<comment> \<open>build_comparison_chain returns Inl [] for empty ops, contradicting Inr\<close>
  thus ?case by simp
next
  case (Cons triple rest)
  obtain op rhsTm rhsTy where triple_eq: "triple = (op, rhsTm, rhsTy)"
    by (cases triple) auto

  \<comment> \<open>Extract the check results from the Inr return\<close>
  let ?lhsAllowed = "if chainCtr = 0 then '''' else ''chain@@'' @ nat_to_string (chainCtr - 1)"

  \<comment> \<open>The Cons equation starts with a check; if it fails we get Inl, contradicting Inr.\<close>
  have checks_passed: "\<not> (has_unexpected_chain_var lhsTm ?lhsAllowed
                          \<or> has_unexpected_chain_var rhsTm '''')"
  proof (rule notI)
    assume "has_unexpected_chain_var lhsTm ?lhsAllowed
            \<or> has_unexpected_chain_var rhsTm ''''"
    hence "build_comparison_chain is_flex loc ghost chainCtr lhsTm lhsTy (triple # rest)
           = Inl [TyErr_InternalError_UnexpectedChainVar loc]"
      using triple_eq by (simp add: Let_def)
    with Cons.prems show False by simp
  qed
  hence check_lhs: "\<not> has_unexpected_chain_var lhsTm ?lhsAllowed"
    and check_rhs: "\<not> has_unexpected_chain_var rhsTm ''''"
    by auto

  \<comment> \<open>Part 1: chain@@n not free in lhsTm for n \<ge> chainCtr\<close>
  have lhs_result: "\<forall>n \<ge> chainCtr. ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars lhsTm"
  proof (intro allI impI notI)
    fix n assume n_ge: "n \<ge> chainCtr"
    assume in_fv: "''chain@@'' @ nat_to_string n \<in> core_term_free_vars lhsTm"
    have eq_allowed: "''chain@@'' @ nat_to_string n = ?lhsAllowed"
      using not_has_unexpected_chain_var[OF check_lhs in_fv chain_var_prefix] .
    show False
    proof (cases "chainCtr = 0")
      case True
      from True eq_allowed have "''chain@@'' @ nat_to_string n = ''''" by simp
      thus False by simp
    next
      case False
      from False eq_allowed
      have "''chain@@'' @ nat_to_string n = ''chain@@'' @ nat_to_string (chainCtr - 1)" by simp
      hence "nat_to_string n = nat_to_string (chainCtr - 1)" by simp
      hence "n = chainCtr - 1" using nat_to_string_injective by blast
      with n_ge False show False by arith
    qed
  qed

  \<comment> \<open>Part 2a: chain@@n not free in rhsTm (the first op term)\<close>
  have rhs_result: "\<forall>n. ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars rhsTm"
  proof (intro allI notI)
    fix n assume in_fv: "''chain@@'' @ nat_to_string n \<in> core_term_free_vars rhsTm"
    have "''chain@@'' @ nat_to_string n = ''''"
      using not_has_unexpected_chain_var[OF check_rhs in_fv chain_var_prefix] .
    thus False by simp
  qed

  \<comment> \<open>Part 2b: chain@@n not free in ops in rest (from IH via recursive call)\<close>
  have rest_result: "\<forall>opx \<in> set rest. \<forall>n. ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars (fst (snd opx))"
  proof (cases rest)
    case Nil thus ?thesis by simp
  next
    case (Cons triple2 rest2)
    \<comment> \<open>rest is non-empty, so there is a recursive call that returns Inr\<close>
    obtain resolvedLhs resolvedLhsTy resolvedRhs resolvedRhsTy where
      resolved: "resolve_binop_metas is_flex op lhsTm lhsTy rhsTm rhsTy =
                 (resolvedLhs, resolvedLhsTy, resolvedRhs, resolvedRhsTy)"
      by (cases "resolve_binop_metas is_flex op lhsTm lhsTy rhsTm rhsTy") auto
    \<comment> \<open>Simplify the function with checks eliminated\<close>
    from checks_passed triple_eq
    have bcc_simplified:
      "build_comparison_chain is_flex loc ghost chainCtr lhsTm lhsTy (triple # rest) =
       (case rest of
         [] \<Rightarrow> (case elab_binop_with_special is_flex loc ghost op lhsTm lhsTy rhsTm rhsTy of
                  Inl errs \<Rightarrow> Inl errs | Inr (cmpTm, _) \<Rightarrow> Inr cmpTm)
       | _ \<Rightarrow>
         let (_, _, resolvedRhs', resolvedRhsTy') = resolve_binop_metas is_flex op lhsTm lhsTy rhsTm rhsTy
         in if is_simple_term resolvedRhs' then
              (case elab_binop_with_special is_flex loc ghost op lhsTm lhsTy resolvedRhs' resolvedRhsTy' of
                Inl errs \<Rightarrow> Inl errs
              | Inr (cmpTm, _) \<Rightarrow>
                  (case build_comparison_chain is_flex loc ghost chainCtr resolvedRhs' resolvedRhsTy' rest of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr restTm \<Rightarrow> Inr (CoreTm_Binop CoreBinop_And cmpTm restTm)))
            else if \<not> list_all (\<lambda>n. \<not> is_flex n) (type_tyvars_list resolvedRhsTy')
                 then Inl [TyErr_CannotInferType loc]
            else let varName = ''chain@@'' @ nat_to_string chainCtr;
                     varTm = CoreTm_Var varName
                 in (case elab_binop_with_special is_flex loc ghost op lhsTm lhsTy varTm resolvedRhsTy' of
                      Inl errs \<Rightarrow> Inl errs
                    | Inr (cmpTm, _) \<Rightarrow>
                        (case build_comparison_chain is_flex loc ghost (chainCtr + 1) varTm resolvedRhsTy' rest of
                          Inl errs \<Rightarrow> Inl errs
                        | Inr restTm \<Rightarrow>
                            Inr (CoreTm_Let varName resolvedRhs'
                                  (CoreTm_Binop CoreBinop_And cmpTm restTm)))))"
      by (simp add: Let_def)

    show ?thesis
    proof (cases "is_simple_term resolvedRhs")
      case True
      \<comment> \<open>Simple term: recursive call with same chainCtr\<close>
      from Cons.prems bcc_simplified Cons resolved True
      obtain restTm where
        recurse: "build_comparison_chain is_flex loc ghost chainCtr resolvedRhs resolvedRhsTy rest = Inr restTm"
        by (auto simp: Let_def split: sum.splits prod.splits list.splits)
      from Cons.IH[OF recurse] show ?thesis by (simp add: prod.case_eq_if)
    next
      case not_simple: False
      \<comment> \<open>Hide nat_to_string chainCtr behind a definition to prevent linarith looping\<close>
      define varName where "varName = ''chain@@'' @ nat_to_string chainCtr"
      let ?varTm = "CoreTm_Var varName"

      \<comment> \<open>Derive a simplified equation for the complex case\<close>
      from bcc_simplified Cons resolved not_simple
      have bcc_complex:
        "build_comparison_chain is_flex loc ghost chainCtr lhsTm lhsTy (triple # rest) =
         (if \<not> list_all (\<lambda>n. \<not> is_flex n) (type_tyvars_list resolvedRhsTy)
          then Inl [TyErr_CannotInferType loc]
          else (case elab_binop_with_special is_flex loc ghost op lhsTm lhsTy ?varTm resolvedRhsTy of
                  Inl errs \<Rightarrow> Inl errs
                | Inr (cmpTm, _) \<Rightarrow>
                    (case build_comparison_chain is_flex loc ghost (chainCtr + 1) ?varTm resolvedRhsTy rest of
                      Inl errs \<Rightarrow> Inl errs
                    | Inr restTm \<Rightarrow>
                        Inr (CoreTm_Let varName resolvedRhs
                              (CoreTm_Binop CoreBinop_And cmpTm restTm)))))"
        unfolding varName_def[symmetric]
        by (simp add: Let_def split: list.splits prod.splits)

      show ?thesis
      proof (cases "list_all (\<lambda>n. \<not> is_flex n) (type_tyvars_list resolvedRhsTy)")
        case False
        \<comment> \<open>Not resolved: returns Inl, contradicting Inr\<close>
        from Cons.prems bcc_complex False
        have False by simp
        thus ?thesis ..
      next
        case True
        \<comment> \<open>Complex term: recursive call with chainCtr + 1\<close>
        from Cons.prems bcc_complex True
        obtain restTm where
          recurse: "build_comparison_chain is_flex loc ghost (chainCtr + 1) ?varTm resolvedRhsTy rest = Inr restTm"
          by (auto split: sum.splits prod.splits)
        from Cons.IH[OF recurse] show ?thesis by (simp add: prod.case_eq_if)
      qed
    qed
  qed

  \<comment> \<open>Combine parts\<close>
  from lhs_result rhs_result rest_result
  show ?case using triple_eq by (auto simp: prod.case_eq_if)
qed

(* Split the combined lemma into the two conclusions used elsewhere *)
lemma build_comparison_chain_inputs_fresh:
  assumes "build_comparison_chain is_flex loc ghost chainCtr lhsTm lhsTy ops = Inr resultTm"
  shows "\<And>n. n \<ge> chainCtr \<Longrightarrow> ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars lhsTm"
    and "\<And>op tm ty n. (op, tm, ty) \<in> set ops \<Longrightarrow>
           ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars tm"
proof -
  note combined = build_comparison_chain_inputs_fresh_combined[OF assms]
  { fix n assume "n \<ge> chainCtr"
    with combined show "''chain@@'' @ nat_to_string n \<notin> core_term_free_vars lhsTm" by blast }
  { fix op tm ty n assume "(op, tm, ty) \<in> set ops"
    hence "(op, tm, ty) \<in> set ops" .
    with combined have "''chain@@'' @ nat_to_string n \<notin> core_term_free_vars (fst (snd (op, tm, ty)))"
      by blast
    thus "''chain@@'' @ nat_to_string n \<notin> core_term_free_vars tm" by simp }
qed

(* Correctness of build_comparison_chain. *)
lemma build_comparison_chain_correct:
  assumes "build_comparison_chain is_flex loc ghost chainCtr lhsTm lhsTy ops = Inr resultTm"
    and "core_term_type env ghost lhsTm = Some lhsTy"
    and "list_all (\<lambda>(op, tm, ty). core_term_type env ghost tm = Some ty) ops"
    and "tyenv_well_formed env"
    and "check_comparison_chain_directions ops dir"
    and locals_rigid: "\<forall>name ty' n. fmlookup (TE_LocalVars env) name = Some ty'
                         \<longrightarrow> n \<in> type_tyvars ty' \<longrightarrow> \<not> is_flex n"
    and ret_rigid: "\<forall>n. n \<in> type_tyvars (TE_ReturnType env) \<longrightarrow> \<not> is_flex n"
  shows "core_term_type env ghost resultTm = Some CoreTy_Bool"
  using assms
proof (induction ops arbitrary: chainCtr lhsTm lhsTy resultTm env dir)
  case Nil
  then show ?case by simp
next
  case (Cons triple rest)
  obtain op rhsTm rhsTy where triple_eq: "triple = (op, rhsTm, rhsTy)"
    by (cases triple) auto
  have rhs_typed: "core_term_type env ghost rhsTm = Some rhsTy"
    using Cons.prems(3) triple_eq by simp

  \<comment> \<open>Get the chain direction info for op\<close>
  have op_cmp: "comparison_direction op \<noteq> None"
    using check_comparison_chain_directions_all_comparison[OF Cons.prems(5)]
          triple_eq by (meson list.set_intros(1) prod_cases3)

  \<comment> \<open>Get resolved operands\<close>
  obtain resolvedLhs resolvedLhsTy resolvedRhs resolvedRhsTy where
    resolved: "resolve_binop_metas is_flex op lhsTm lhsTy rhsTm rhsTy =
               (resolvedLhs, resolvedLhsTy, resolvedRhs, resolvedRhsTy)"
    by (cases "resolve_binop_metas is_flex op lhsTm lhsTy rhsTm rhsTy") auto

  have resolvedRhs_typed: "core_term_type env ghost resolvedRhs = Some resolvedRhsTy"
    using Cons.prems(2,4,6,7) resolve_binop_metas_correct resolved rhs_typed by blast

  \<comment> \<open>Propagate chain direction check to rest\<close>
  have rest_dirs: "check_comparison_chain_directions rest
      (if comparison_direction op = Some ChainNeutral then dir else the (comparison_direction op))"
    using Cons.prems(5) triple_eq by (auto split: option.splits if_splits)

  \<comment> \<open>The has_unexpected_chain_var checks must have passed (otherwise we'd get Inl)\<close>
  let ?lhsAllowed = "if chainCtr = 0 then '''' else ''chain@@'' @ nat_to_string (chainCtr - 1)"
  have checks_passed: "\<not> (has_unexpected_chain_var lhsTm ?lhsAllowed
                          \<or> has_unexpected_chain_var rhsTm '''')"
  proof (rule notI)
    assume "has_unexpected_chain_var lhsTm ?lhsAllowed
            \<or> has_unexpected_chain_var rhsTm ''''"
    hence "build_comparison_chain is_flex loc ghost chainCtr lhsTm lhsTy (triple # rest)
           = Inl [TyErr_InternalError_UnexpectedChainVar loc]"
      using triple_eq by (simp add: Let_def)
    with Cons.prems(1) show False by simp
  qed

  show ?case
  proof (cases rest)
    case Nil
    \<comment> \<open>Last comparison: just elaborate normally\<close>
    from Cons.prems(1) triple_eq Nil checks_passed
    obtain cmpTm cmpTy where
      elab: "elab_binop_with_special is_flex loc ghost op lhsTm lhsTy rhsTm rhsTy = Inr (cmpTm, cmpTy)"
      and result: "resultTm = cmpTm"
      by (auto simp: Let_def split: sum.splits prod.splits)
    have "core_term_type env ghost cmpTm = Some cmpTy"
      using Cons.prems(2,4,6,7) elab elab_binop_with_special_correct rhs_typed by auto
    moreover have "cmpTy = CoreTy_Bool"
      using elab_binop_with_special_comparison_bool[OF elab op_cmp] .
    ultimately show ?thesis using result by simp
  next
    case rest_cons: (Cons triple2 rest2)
    \<comment> \<open>More comparisons follow\<close>

    \<comment> \<open>Common facts for both subcases\<close>
    have rest_all: "list_all (\<lambda>(op, tm, ty). core_term_type env ghost tm = Some ty) rest"
      using Cons.prems(3) triple_eq by simp

    show ?thesis
    proof (cases "is_simple_term resolvedRhs")
      case True
      \<comment> \<open>Simple term: duplicate directly\<close>
      from Cons.prems(1) triple_eq rest_cons resolved True checks_passed
      obtain cmpTm cmpTy restTm where
        elab: "elab_binop_with_special is_flex loc ghost op lhsTm lhsTy resolvedRhs resolvedRhsTy
               = Inr (cmpTm, cmpTy)" and
        recurse: "build_comparison_chain is_flex loc ghost chainCtr resolvedRhs resolvedRhsTy rest
                  = Inr restTm" and
        result: "resultTm = CoreTm_Binop CoreBinop_And cmpTm restTm"
        by (auto simp: Let_def split: sum.splits prod.splits)
      have cmpTy_bool: "cmpTy = CoreTy_Bool"
        using elab_binop_with_special_comparison_bool[OF elab op_cmp] .
      have cmp_typed: "core_term_type env ghost cmpTm = Some CoreTy_Bool"
        using Cons.prems(2,4,6,7) cmpTy_bool elab elab_binop_with_special_correct resolvedRhs_typed
        by blast
      have rest_typed: "core_term_type env ghost restTm = Some CoreTy_Bool"
        using Cons.IH[OF recurse resolvedRhs_typed rest_all Cons.prems(4) rest_dirs
                         Cons.prems(6) Cons.prems(7)] .
      show ?thesis using cmp_typed rest_typed result by simp
    next
      case not_simple: False
      \<comment> \<open>Complex term: let-binding case\<close>
      let ?varName = "''chain@@'' @ nat_to_string chainCtr"
      let ?varTm = "CoreTm_Var ?varName"

      \<comment> \<open>The resolved check must pass (otherwise we'd get Inl).\<close>
      from Cons.prems(1) triple_eq rest_cons resolved not_simple checks_passed
      have ground: "list_all (\<lambda>n. \<not> is_flex n) (type_tyvars_list resolvedRhsTy)"
        by (auto simp: Let_def split: if_splits sum.splits prod.splits)

      \<comment> \<open>Extract the elab and recursive call results via the helper lemma.\<close>
      from Cons.prems(1) triple_eq rest_cons resolved not_simple ground
      obtain cmpTm cmpTy restTm where
        elab: "elab_binop_with_special is_flex loc ghost op lhsTm lhsTy ?varTm resolvedRhsTy
               = Inr (cmpTm, cmpTy)" and
        recurse: "build_comparison_chain is_flex loc ghost (chainCtr + 1) ?varTm resolvedRhsTy rest
                  = Inr restTm" and
        result: "resultTm = CoreTm_Let ?varName resolvedRhs
                              (CoreTm_Binop CoreBinop_And cmpTm restTm)"
      proof -
        have "build_comparison_chain is_flex loc ghost chainCtr lhsTm lhsTy (Cons triple rest)
          = (let varName = ''chain@@'' @ nat_to_string chainCtr;
              varTm = CoreTm_Var varName
          in (case elab_binop_with_special is_flex loc ghost op lhsTm lhsTy varTm resolvedRhsTy of
            Inl errs \<Rightarrow> Inl errs
          | Inr (cmpTm, _) \<Rightarrow>
              (case build_comparison_chain is_flex loc ghost (chainCtr + 1) varTm resolvedRhsTy rest of
                Inl errs \<Rightarrow> Inl errs
              | Inr restTm \<Rightarrow>
                  Inr (CoreTm_Let varName resolvedRhs
                        (CoreTm_Binop CoreBinop_And cmpTm restTm)))))"
          using rest_cons triple_eq resolved not_simple ground checks_passed
          by (simp only: build_comparison_chain.simps prod.case Let_def list.case
                         if_False if_True if_not_P[OF not_simple]
                         not_True_eq_False not_False_eq_True ground)

        hence "(case elab_binop_with_special is_flex loc ghost op lhsTm lhsTy ?varTm resolvedRhsTy of
                Inl errs \<Rightarrow> Inl errs
              | Inr (cmpTm, _) \<Rightarrow>
                  (case build_comparison_chain is_flex loc ghost (chainCtr + 1) ?varTm resolvedRhsTy rest of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr restTm \<Rightarrow>
                      Inr (CoreTm_Let ?varName resolvedRhs
                            (CoreTm_Binop CoreBinop_And cmpTm restTm)))) = Inr resultTm"
          by (metis Cons.prems(1))

        thus ?thesis using build_comparison_chain_let_elim that by blast
      qed

      \<comment> \<open>Hide nat_to_string chainCtr behind a definition to prevent linarith looping\<close>
      define vn where "vn = ''chain@@'' @ nat_to_string chainCtr"
      have vn_eq: "?varName = vn" by (simp add: vn_def)

      \<comment> \<open>Rewrite elab, recurse, result to use vn\<close>
      note elab' = elab[unfolded vn_eq[symmetric]]
      note recurse' = recurse[unfolded vn_eq[symmetric]]
      note result' = result[unfolded vn_eq[symmetric]]

      \<comment> \<open>Derive chain@@ freshness from build_comparison_chain_inputs_fresh\<close>
      have lhs_fresh: "vn \<notin> core_term_free_vars lhsTm"
        using build_comparison_chain_inputs_fresh(1)[OF Cons.prems(1)] vn_def by blast
      have rest_fresh: "\<And>op tm ty n. (op, tm, ty) \<in> set rest \<Longrightarrow>
             ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars tm"
        using build_comparison_chain_inputs_fresh(2)[OF Cons.prems(1)]
              triple_eq by (meson list.set_intros(2))

      \<comment> \<open>Build the extended environment\<close>
      define gv' where "gv' = (if ghost = Ghost then finsert vn (TE_GhostLocals env)
                               else fminus (TE_GhostLocals env) {|vn|})"
      define env' where "env' = env \<lparr> TE_LocalVars := fmupd vn resolvedRhsTy (TE_LocalVars env),
                                       TE_GhostLocals := gv',
                                       TE_ConstLocals := finsert vn (TE_ConstLocals env) \<rparr>"

      \<comment> \<open>env' is well-formed\<close>
      have wk: "is_well_kinded env resolvedRhsTy"
        using core_term_type_well_kinded[OF resolvedRhs_typed Cons.prems(4)] .
      define env_no_cn where "env_no_cn = env \<lparr> TE_LocalVars := fmupd vn resolvedRhsTy (TE_LocalVars env),
                                                  TE_GhostLocals := gv' \<rparr>"
      have wf_no_cn: "tyenv_well_formed env_no_cn"
      proof (cases ghost)
        case Ghost
        show ?thesis using tyenv_well_formed_add_ghost_var[OF Cons.prems(4) wk] Ghost
          by (simp add: env_no_cn_def gv'_def)
      next
        case NotGhost
        have rt: "is_runtime_type env resolvedRhsTy"
          using core_term_type_notghost_runtime[OF _ Cons.prems(4)] resolvedRhs_typed NotGhost by simp
        thus ?thesis using tyenv_well_formed_add_var[OF Cons.prems(4) wk rt] NotGhost
          by (simp add: env_no_cn_def gv'_def)
      qed
      have env'_eq_cn: "env' = env_no_cn \<lparr> TE_ConstLocals := finsert vn (TE_ConstLocals env) \<rparr>"
        by (simp add: env'_def env_no_cn_def)
      have env'_wf: "tyenv_well_formed env'"
        using wf_no_cn tyenv_well_formed_TE_ConstLocals_irrelevant env'_eq_cn by simp

      \<comment> \<open>The variable typechecks in env'\<close>
      have var_typed: "core_term_type env' ghost (CoreTm_Var vn) = Some resolvedRhsTy"
        by (cases ghost)
           (simp_all add: env'_def gv'_def tyenv_lookup_var_def tyenv_var_ghost_def)

      \<comment> \<open>lhsTm typechecks in env' by weakening (vn not free in lhsTm)\<close>
      have gv'_agree: "\<forall>y. y \<noteq> vn \<longrightarrow> (y |\<in>| gv' \<longleftrightarrow> y |\<in>| TE_GhostLocals env)"
        by (auto simp: gv'_def)
      have lhs_typed': "core_term_type env' ghost lhsTm = Some lhsTy"
        using core_term_type_irrelevant_var[OF lhs_fresh Cons.prems(2) gv'_agree]
              core_term_type_TE_ConstLocals_irrelevant
        by (simp add: env'_def env_no_cn_def)

      \<comment> \<open>env' has the same TE_TypeVars / TE_ReturnType as env (only locals,
          ghost-locals, and const-names changed). The rigidity conditions lift:
          old locals are still rigid (from Cons.prems(6)), and the newly added
          local resolvedRhsTy has no flex metavars (from ground). \<close>
      have env'_locals_rigid:
        "\<forall>name ty' n. fmlookup (TE_LocalVars env') name = Some ty'
                        \<longrightarrow> n \<in> type_tyvars ty' \<longrightarrow> \<not> is_flex n"
      proof (intro allI impI)
        fix name ty' n
        assume lk: "fmlookup (TE_LocalVars env') name = Some ty'"
        assume n_mv: "n \<in> type_tyvars ty'"
        show "\<not> is_flex n"
        proof (cases "name = vn")
          case True
          with lk have "ty' = resolvedRhsTy"
            by (simp add: env'_def)
          with n_mv ground show ?thesis
            by (auto simp: set_type_tyvars_list[symmetric] list_all_iff)
        next
          case False
          with lk have "fmlookup (TE_LocalVars env) name = Some ty'"
            by (simp add: env'_def)
          with Cons.prems(6) n_mv show ?thesis by blast
        qed
      qed
      have env'_ret_rigid: "\<forall>n. n \<in> type_tyvars (TE_ReturnType env') \<longrightarrow> \<not> is_flex n"
        using Cons.prems(7) by (simp add: env'_def)

      \<comment> \<open>cmpTm typechecks in env'\<close>
      have cmpTy_bool: "cmpTy = CoreTy_Bool"
        using elab_binop_with_special_comparison_bool[OF elab op_cmp] .
      have elab_vn: "elab_binop_with_special is_flex loc ghost op lhsTm lhsTy (CoreTm_Var vn) resolvedRhsTy
                     = Inr (cmpTm, cmpTy)"
        using elab using vn_eq by auto
      have cmp_typed: "core_term_type env' ghost cmpTm = Some CoreTy_Bool"
        using elab_binop_with_special_correct[OF elab_vn lhs_typed' var_typed env'_wf
                                                  env'_locals_rigid env'_ret_rigid]
              cmpTy_bool by simp

      \<comment> \<open>The ops in rest typecheck in env' by weakening\<close>
      have rest_all': "list_all (\<lambda>(op, tm, ty). core_term_type env' ghost tm = Some ty) rest"
        unfolding list_all_iff
      proof (intro ballI, clarify)
        fix xop xtm xty assume in_rest: "(xop, xtm, xty) \<in> set rest"
        have xtm_typed: "core_term_type env ghost xtm = Some xty"
          using rest_all in_rest by (auto simp: list_all_iff)
        have xtm_fresh: "vn \<notin> core_term_free_vars xtm"
          using rest_fresh in_rest vn_def by blast
        show "core_term_type env' ghost xtm = Some xty"
          using core_term_type_irrelevant_var[OF xtm_fresh xtm_typed gv'_agree]
                core_term_type_TE_ConstLocals_irrelevant
          by (simp add: env'_def env_no_cn_def)
      qed

      \<comment> \<open>restTm typechecks in env' by the inductive hypothesis\<close>
      have recurse_vn: "build_comparison_chain is_flex loc ghost (chainCtr + 1)
                          (CoreTm_Var vn) resolvedRhsTy rest = Inr restTm"
        using recurse using vn_eq by auto
      have rest_typed: "core_term_type env' ghost restTm = Some CoreTy_Bool"
        using Cons.IH[OF recurse_vn var_typed rest_all' env'_wf rest_dirs
                         env'_locals_rigid env'_ret_rigid] .

      \<comment> \<open>The body (And cmpTm restTm) typechecks in env'\<close>
      have body_typed: "core_term_type env' ghost (CoreTm_Binop CoreBinop_And cmpTm restTm)
                        = Some CoreTy_Bool"
        using cmp_typed rest_typed by simp

      \<comment> \<open>The whole let-expression typechecks\<close>
      have result_vn: "resultTm = CoreTm_Let vn resolvedRhs
                                    (CoreTm_Binop CoreBinop_And cmpTm restTm)"
        using result vn_def by simp
      have "core_term_type env ghost (CoreTm_Let vn resolvedRhs
              (CoreTm_Binop CoreBinop_And cmpTm restTm)) = Some CoreTy_Bool"
        using resolvedRhs_typed ground body_typed
        by (simp add: env'_def gv'_def Let_def)
      thus ?thesis using result_vn by simp
    qed
  qed
qed

(* Correctness of process_binop_chain *)
lemma process_binop_chain_correct:
  assumes "process_binop_chain is_flex loc ghost lhsTm lhsTy ops = Inr (resultTm, resultTy)"
    and "core_term_type env ghost lhsTm = Some lhsTy"
    and "list_all (\<lambda>(op, tm, ty). core_term_type env ghost tm = Some ty) ops"
    and "tyenv_well_formed env"
    and locals_rigid: "\<forall>name ty' n. fmlookup (TE_LocalVars env) name = Some ty'
                         \<longrightarrow> n \<in> type_tyvars ty' \<longrightarrow> \<not> is_flex n"
    and ret_rigid: "\<forall>n. n \<in> type_tyvars (TE_ReturnType env) \<longrightarrow> \<not> is_flex n"
  shows "core_term_type env ghost resultTm = Some resultTy"
proof (cases ops)
  case Nil
  with assms(1) show ?thesis using assms(2) by simp
next
  case (Cons triple rest)
  let ?firstOp = "fst (hd ops)"
  show ?thesis
  proof (cases "?firstOp = BabBinop_Implies \<or> ?firstOp = BabBinop_ImpliedBy")
    case True
    \<comment> \<open>Implies chain: right-associates (check_implies_chain must pass, else we'd get Inl)\<close>
    with assms(1) Cons have "fold_implies_right is_flex loc ghost lhsTm lhsTy ops = Inr (resultTm, resultTy)"
      by (auto simp: Let_def split: if_splits)
    thus ?thesis using fold_implies_right_correct assms(2,3,4) locals_rigid ret_rigid by blast
  next
    case not_implies: False
    show ?thesis
    proof (cases "is_comparison_bab_binop ?firstOp \<and> length ops > 1")
      case True
      \<comment> \<open>Comparison chain\<close>
      from assms(1) Cons not_implies True
      have dirs: "check_comparison_chain_directions ops ChainNeutral"
        by (auto simp: Let_def split: sum.splits if_splits)
      from assms(1) Cons not_implies True
      obtain chainTm where
        chain_ok: "build_comparison_chain is_flex loc ghost 0 lhsTm lhsTy ops = Inr chainTm"
        and result: "resultTm = chainTm" and rty: "resultTy = CoreTy_Bool"
        by (auto simp: Let_def split: sum.splits if_splits)
      have "core_term_type env ghost chainTm = Some CoreTy_Bool"
        using build_comparison_chain_correct[OF chain_ok assms(2,3,4) dirs locals_rigid ret_rigid] .
      thus ?thesis using result rty by simp
    next
      case False
      \<comment> \<open>Left-associate\<close>
      with assms(1) Cons not_implies have
        "fold_binop_left is_flex loc ghost lhsTm lhsTy ops = Inr (resultTm, resultTy)"
        by (auto simp: Let_def split: if_splits)
      thus ?thesis using fold_binop_left_correct assms(2,3,4) locals_rigid ret_rigid by blast
    qed
  qed
qed

end
