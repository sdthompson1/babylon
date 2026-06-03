theory ElabStmtCorrect
  imports ElabStmt ElabTermCorrect ElabTypeCorrect ElabPatternCorrect
    "../core/CoreStmtTypecheck"
begin

(* ========================================================================== *)
(* Correctness of the statement elaborator                                    *)
(*                                                                            *)
(* The main theorem (elab_statement_correct, below) says: if elaboration       *)
(* succeeds, the elaborated Core statement typechecks under the input env      *)
(* extended with the freshly-allocated type-variable interval, and produces    *)
(* the elaborator's output env (also so extended). This mirrors                *)
(* elab_term_correct.                                                         *)
(* ========================================================================== *)


(* Clearing interval metavariables *)
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

(* Main bridge: an initializer term that typechecks (in a given ghost mode) under env
   extended with the fresh interval, once its interval metavariables are cleared,
   typechecks to the SAME type under the original env. The result type is
   metavariable-free (its tyvars are < next_mv, hence outside the interval), so
   substitution leaves it unchanged; clearing removes the interval tyvars from
   the term, so the interval can be dropped via core_term_type_remove_unused_tyvars. *)
lemma clear_metavars_typed_in_env:
  assumes typed: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost coreTm
                    = Some ty"
    and wf: "tyenv_well_formed env"
    and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv"
    and ty_below: "type_tyvars ty \<subseteq> {n. n < next_mv}"
  shows "core_term_type env ghost (clear_metavars next_mv next_mv' coreTm) = Some ty"
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
  \<comment> \<open>Cleared term typechecks (to apply_subst ?subst ty = ty) under the extended env.\<close>
  have ty_unaffected: "apply_subst ?subst ty = ty"
    using clear_metavars_subst_id_below[OF ty_below] .
  have cleared_typedE: "core_term_type ?envE ghost (clear_metavars next_mv next_mv' coreTm) = Some ty"
    using apply_subst_to_term_preserves_typing
            [OF typed wfE subst_wk subst_rt locals_unaffected ret_unaffected]
    unfolding clear_metavars_def by (simp add: ty_unaffected)
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
  \<comment> \<open>VarDecl: each successful branch either keeps next_mv or advances it via elab_term.\<close>
  case (1 env elabEnv ghost loc varName vorf tyOpt tmOpt next_mv)
  show ?case
    using "1.prems"
    by (auto simp: Let_def
             dest!: elab_term_next_mv_monotone
             split: VarOrRef.splits option.splits sum.splits prod.splits if_splits)
next
  case (2 env elabEnv ghost loc varName ty next_mv) thus ?case sorry  \<comment> \<open>Fix (unimplemented)\<close>
next
  case (3 env elabEnv ghost loc varName ty tm next_mv) thus ?case sorry  \<comment> \<open>Obtain\<close>
next
  case (4 env elabEnv ghost loc tm next_mv) thus ?case sorry  \<comment> \<open>Use\<close>
next
  case (5 env elabEnv ghost loc lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Assign\<close>
next
  case (6 env elabEnv ghost loc lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Swap\<close>
next
  case (7 env elabEnv ghost loc tmOpt next_mv) thus ?case sorry  \<comment> \<open>Return\<close>
next
  case (8 env elabEnv ghost loc condOpt proofBody next_mv) thus ?case sorry  \<comment> \<open>Assert\<close>
next
  \<comment> \<open>Assume: next_mv advances via elab_term.\<close>
  case (9 env elabEnv ghost loc tm next_mv)
  show ?case
    using "9.prems"
    by (auto dest!: elab_term_next_mv_monotone split: sum.splits prod.splits if_splits)
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
  \<comment> \<open>VarDecl: every successful branch returns env with only local-var fields changed.\<close>
  case (1 env elabEnv ghost loc varName vorf tyOpt tmOpt next_mv)
  show ?case
    using "1.prems"
    by (auto simp: Let_def
             split: VarOrRef.splits option.splits sum.splits prod.splits if_splits)
next
  case (2 env elabEnv ghost loc varName ty next_mv) thus ?case sorry  \<comment> \<open>Fix\<close>
next
  case (3 env elabEnv ghost loc varName ty tm next_mv) thus ?case sorry  \<comment> \<open>Obtain\<close>
next
  case (4 env elabEnv ghost loc tm next_mv) thus ?case sorry  \<comment> \<open>Use\<close>
next
  case (5 env elabEnv ghost loc lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Assign\<close>
next
  case (6 env elabEnv ghost loc lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Swap\<close>
next
  case (7 env elabEnv ghost loc tmOpt next_mv) thus ?case sorry  \<comment> \<open>Return\<close>
next
  case (8 env elabEnv ghost loc condOpt proofBody next_mv) thus ?case sorry  \<comment> \<open>Assert\<close>
next
  \<comment> \<open>Assume: env unchanged.\<close>
  case (9 env elabEnv ghost loc tm next_mv)
  show ?case using "9.prems" by (auto split: sum.splits prod.splits if_splits)
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
  from "14.prems" show ?case by simp
next
  \<comment> \<open>Ghost wrapper: re-elaborates inner in Ghost mode (same env).\<close>
  case (15 env elabEnv ghost loc inner next_mv)
  have inner_elab: "elab_statement env elabEnv Ghost inner next_mv = Inr (coreStmt, env', next_mv')"
    using "15.prems" by simp
  show ?case using "15.IH"[OF inner_elab] .
next
  \<comment> \<open>Empty statement list.\<close>
  case (16 env elabEnv ghost next_mv)
  from "16.prems" show ?case by simp
next
  \<comment> \<open>Cons: each preserved field is preserved through head then tail.\<close>
  case (17 env elabEnv ghost stmt stmts next_mv)
  from "17.prems" obtain coreStmt1 env1 next_mv1 coreStmts1 where
    head: "elab_statement env elabEnv ghost stmt next_mv = Inr (coreStmt1, env1, next_mv1)" and
    tail: "elab_statement_list env1 elabEnv ghost stmts next_mv1
             = Inr (coreStmts1, env', next_mv')"
    by (auto split: sum.splits prod.splits)
  have e1: "TE_TypeVars env1 = TE_TypeVars env \<and> TE_RuntimeTypeVars env1 = TE_RuntimeTypeVars env
              \<and> TE_FunctionGhost env1 = TE_FunctionGhost env \<and> TE_ProofGoal env1 = TE_ProofGoal env"
    using "17.IH"(1) head by simp
  moreover have "TE_TypeVars env' = TE_TypeVars env1 \<and> TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env1
                  \<and> TE_FunctionGhost env' = TE_FunctionGhost env1 \<and> TE_ProofGoal env' = TE_ProofGoal env1"
    using "17.IH"(2) head tail by blast
  ultimately show ?case by simp
qed

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
      unchanged, so elabenv_well_formed is preserved by congruence.\<close>
  case (1 env elabEnv ghost loc varName vorf tyOpt tmOpt next_mv)
  from "1.prems"(1) have flds:
    "TE_TypeVars env' = TE_TypeVars env \<and> TE_Datatypes env' = TE_Datatypes env
       \<and> TE_DataCtors env' = TE_DataCtors env"
    by (auto simp: Let_def
             split: VarOrRef.splits option.splits sum.splits prod.splits if_splits)
  show ?case
    using "1.prems"(2) elabenv_well_formed_cong_env[OF conjunct1[OF flds]
            conjunct1[OF conjunct2[OF flds]] conjunct2[OF conjunct2[OF flds]]]
    by simp
next
  case (2 env elabEnv ghost loc varName ty next_mv) thus ?case sorry  \<comment> \<open>Fix\<close>
next
  case (3 env elabEnv ghost loc varName ty tm next_mv) thus ?case sorry  \<comment> \<open>Obtain\<close>
next
  case (4 env elabEnv ghost loc tm next_mv) thus ?case sorry  \<comment> \<open>Use\<close>
next
  case (5 env elabEnv ghost loc lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Assign\<close>
next
  case (6 env elabEnv ghost loc lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Swap\<close>
next
  case (7 env elabEnv ghost loc tmOpt next_mv) thus ?case sorry  \<comment> \<open>Return\<close>
next
  case (8 env elabEnv ghost loc condOpt proofBody next_mv) thus ?case sorry  \<comment> \<open>Assert\<close>
next
  \<comment> \<open>Assume: env unchanged.\<close>
  case (9 env elabEnv ghost loc tm next_mv)
  from "9.prems"(1) have "env' = env" by (auto split: sum.splits prod.splits if_splits)
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
      mode), so the resulting env is well-formed by tyenv_well_formed_vardecl_result.\<close>
  case (1 env elabEnv ghost loc varName vorf tyOpt tmOpt next_mv)
  have td_wf: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using "1.prems"(3) unfolding elabenv_well_formed_def by simp
  show ?case
  proof (cases vorf)
    case Var
    show ?thesis
    proof (cases tyOpt)
      case (Some ty)
      \<comment> \<open>Annotated (with or without an initializer): varTy = elaborated annotation.\<close>
      from "1.prems"(1) Var Some obtain coreTy where
        ety: "elab_type env elabEnv ghost ty = Inr coreTy" and
        env'_eq: "env' = (env \<lparr> TE_LocalVars := fmupd varName coreTy (TE_LocalVars env),
                                TE_GhostLocals := (if ghost = Ghost
                                                 then finsert varName (TE_GhostLocals env)
                                                 else fminus (TE_GhostLocals env) {|varName|}) \<rparr>)
                          \<lparr> TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
        by (cases tmOpt) (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
      have wk: "is_well_kinded env coreTy"
        using elab_type_is_well_kinded(1)[OF td_wf "1.prems"(2) ety] .
      have rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env coreTy"
        using elab_type_notghost_is_runtime(1)[OF td_wf "1.prems"(2)] ety by auto
      show ?thesis
        unfolding env'_eq
        using tyenv_well_formed_vardecl_result[OF "1.prems"(2) wk rt] by simp
    next
      case None
      \<comment> \<open>Inferred from the initializer (no annotation): varTy = rhsTy from elab_term,
          which the no-metavar check guarantees is metavariable-free.\<close>
      from "1.prems"(1) Var None obtain tm coreTm rhsTy nmv where
        tm_eq: "tmOpt = Some tm" and
        etm: "elab_term env elabEnv ghost tm next_mv = Inr (coreTm, rhsTy, nmv)" and
        no_meta: "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)" and
        env'_eq: "env' = (env \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars env),
                                TE_GhostLocals := (if ghost = Ghost
                                                 then finsert varName (TE_GhostLocals env)
                                                 else fminus (TE_GhostLocals env) {|varName|}) \<rparr>)
                          \<lparr> TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
        by (cases tmOpt) (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
      have wkrt: "is_well_kinded env rhsTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env rhsTy)"
        using elab_term_inferred_type_well_kinded_runtime[OF etm "1.prems"(2,3) "1.prems"(4) no_meta] .
      show ?thesis
        unfolding env'_eq
        using tyenv_well_formed_vardecl_result[OF "1.prems"(2) conjunct1[OF wkrt] conjunct2[OF wkrt]] by simp
    qed
  next
    case Ref
    \<comment> \<open>Ref: varTy = rhsTy from elab_term (the rhs must be a metavariable-free lvalue).\<close>
    from "1.prems"(1) Ref obtain tm coreTm rhsTy nmv where
      tm_eq: "tmOpt = Some tm" and
      etm: "elab_term env elabEnv ghost tm next_mv = Inr (coreTm, rhsTy, nmv)" and
      no_meta: "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)" and
      env'_eq: "env' = (env \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars env),
                              TE_GhostLocals := (if ghost = Ghost
                                               then finsert varName (TE_GhostLocals env)
                                               else fminus (TE_GhostLocals env) {|varName|}) \<rparr>)
                        \<lparr> TE_ConstLocals := (if is_writable_lvalue env coreTm
                                            then fminus (TE_ConstLocals env) {|varName|}
                                            else finsert varName (TE_ConstLocals env)) \<rparr>"
      by (cases tmOpt) (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
    have wkrt: "is_well_kinded env rhsTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env rhsTy)"
      using elab_term_inferred_type_well_kinded_runtime[OF etm "1.prems"(2,3) "1.prems"(4) no_meta] .
    show ?thesis
      unfolding env'_eq
      using tyenv_well_formed_vardecl_result[OF "1.prems"(2) conjunct1[OF wkrt] conjunct2[OF wkrt]] by simp
  qed
next
  case (2 env elabEnv ghost loc varName ty next_mv) thus ?case sorry  \<comment> \<open>Fix\<close>
next
  case (3 env elabEnv ghost loc varName ty tm next_mv) thus ?case sorry  \<comment> \<open>Obtain\<close>
next
  case (4 env elabEnv ghost loc tm next_mv) thus ?case sorry  \<comment> \<open>Use\<close>
next
  case (5 env elabEnv ghost loc lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Assign\<close>
next
  case (6 env elabEnv ghost loc lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Swap\<close>
next
  case (7 env elabEnv ghost loc tmOpt next_mv) thus ?case sorry  \<comment> \<open>Return\<close>
next
  case (8 env elabEnv ghost loc condOpt proofBody next_mv) thus ?case sorry  \<comment> \<open>Assert\<close>
next
  \<comment> \<open>Assume: env unchanged.\<close>
  case (9 env elabEnv ghost loc tm next_mv)
  from "9.prems"(1) have "env' = env" by (auto split: sum.splits prod.splits if_splits)
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
    - TE_FunctionGhost = Ghost implies ghost = Ghost (this says that ghost function bodies
      are only ever typechecked/elaborated in Ghost mode);
    - ghost = NotGhost implies TE_ProofGoal env = None (this says that executable / non-ghost
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
  \<comment> \<open>VarDecl: the chosen type is well-kinded (runtime in NotGhost mode) in env, and
      the cleared initializer typechecks to it in env directly
      (clear_metavars_typed_in_env). The result env is exactly the elaborator's env'.\<close>
  case (1 env elabEnv ghost loc varName vorf tyOpt tmOpt next_mv)
  have td_wf: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using "1.prems"(3) unfolding elabenv_well_formed_def by simp
  show ?case
  proof (cases vorf)
    case Var
    show ?thesis
    proof (cases tyOpt)
      case (Some ty)
      \<comment> \<open>Annotated: coreTy = elaborated annotation; rhs (Default or coerced term) types to coreTy.\<close>
      from "1.prems"(1) Var Some obtain coreTy where
        ety: "elab_type env elabEnv ghost ty = Inr coreTy"
        by (cases tmOpt) (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
      have ety': "elab_type env elabEnv ghost ty = Inr coreTy"
        using ety by simp
      have wk: "is_well_kinded env coreTy"
        using elab_type_is_well_kinded(1)[OF td_wf "1.prems"(2) ety'] .
      have rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env coreTy"
        using elab_type_notghost_is_runtime(1)[OF td_wf "1.prems"(2)] ety' by auto
      \<comment> \<open>coreTy's tyvars are < next_mv (well-kinded \<Rightarrow> in TE_TypeVars env \<Rightarrow> bounded).\<close>
      have coreTy_below: "type_tyvars coreTy \<subseteq> {n. n < next_mv}"
        using is_well_kinded_type_tyvars_subset[OF wk] "1.prems"(4) by auto
      show ?thesis
      proof (cases tmOpt)
        case None
        \<comment> \<open>Default-initialized: initTm = CoreTm_Default coreTy, which types to coreTy.\<close>
        from "1.prems"(1) Var Some None ety have
          cs_eq: "coreStmt = CoreStmt_VarDecl ghost varName Var coreTy (CoreTm_Default coreTy)" and
          env'_eq: "env' = (env \<lparr> TE_LocalVars := fmupd varName coreTy (TE_LocalVars env),
                                  TE_GhostLocals := (if ghost = Ghost
                                                   then finsert varName (TE_GhostLocals env)
                                                   else fminus (TE_GhostLocals env) {|varName|}) \<rparr>)
                            \<lparr> TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
          by (auto simp: Let_def split: sum.splits if_splits)
        have init_typed: "core_term_type env ghost (CoreTm_Default coreTy) = Some coreTy"
          using wk rt by simp
        show ?thesis using wk rt init_typed by (simp add: cs_eq env'_eq)
      next
        case (Some tm)
        \<comment> \<open>Annotated initializer: elaborate the term, then unify or insert an int cast.
            Either way the emitted term is cleared of interval metavariables.\<close>
        from "1.prems"(1) Var \<open>tyOpt = Some ty\<close> Some ety obtain coreTm rhsTy where
          etm: "elab_term env elabEnv ghost tm next_mv = Inr (coreTm, rhsTy, next_mv')"
          by (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
        have coreTm_typed_decl:
          "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost coreTm = Some rhsTy"
          using elab_term_correct(1)[OF etm "1.prems"(2,3)] "1.prems"(4) by simp
        show ?thesis
        proof (cases "unify (\<lambda>n. n |\<notin>| TE_TypeVars env) rhsTy coreTy")
          case (Some subst)
          \<comment> \<open>unify succeeded: initTm = clear_metavars (apply_subst_to_term subst coreTm),
              which types to coreTy in env.\<close>
          from "1.prems"(1) Var \<open>tyOpt = Some ty\<close> \<open>tmOpt = Some tm\<close> ety etm Some have
            cs_eq: "coreStmt = CoreStmt_VarDecl ghost varName Var coreTy
                                  (clear_metavars next_mv next_mv' (apply_subst_to_term subst coreTm))" and
            env'_eq: "env' = (env \<lparr> TE_LocalVars := fmupd varName coreTy (TE_LocalVars env),
                                    TE_GhostLocals := (if ghost = Ghost
                                                     then finsert varName (TE_GhostLocals env)
                                                     else fminus (TE_GhostLocals env) {|varName|}) \<rparr>)
                              \<lparr> TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
            by (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
          \<comment> \<open>apply_subst_to_term subst coreTm types to apply_subst subst rhsTy = coreTy
              (coreTy metavariable-free, subst flex-only).\<close>
          let ?envD = "extend_env_with_tyvars env ghost next_mv next_mv'"
          let ?is_flex = "\<lambda>n. n |\<notin>| TE_TypeVars env"
          have wfD: "tyenv_well_formed ?envD"
            using "1.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast
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
              using elab_type_notghost_is_runtime(1)[OF td_wf "1.prems"(2) ety'[unfolded dng]] .
            thus "is_runtime_type ?envD coreTy"
              using is_runtime_type_extend_runtime_tyvars dng
              unfolding extend_env_with_tyvars_def by fastforce
          qed
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
          from flex_subst_identity_on_env[OF dom_flex "1.prems"(2) envD_locals envD_ret]
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
          \<comment> \<open>Clear interval metavars and drop to env.\<close>
          have init_typed:
            "core_term_type env ghost
               (clear_metavars next_mv next_mv' (apply_subst_to_term subst coreTm)) = Some coreTy"
            using clear_metavars_typed_in_env[OF subst_typed_coreTy "1.prems"(2,4) coreTy_below] .
          show ?thesis using wk rt init_typed by (simp add: cs_eq env'_eq)
        next
          case None
          \<comment> \<open>unify failed; both integer types, so initTm = clear_metavars (CoreTm_Cast coreTy coreTm).\<close>
          from "1.prems"(1) Var \<open>tyOpt = Some ty\<close> \<open>tmOpt = Some tm\<close> ety etm None have
            ints: "is_integer_type rhsTy \<and> is_integer_type coreTy" and
            cs_eq: "coreStmt = CoreStmt_VarDecl ghost varName Var coreTy
                                  (clear_metavars next_mv next_mv' (CoreTm_Cast coreTy coreTm))" and
            env'_eq: "env' = (env \<lparr> TE_LocalVars := fmupd varName coreTy (TE_LocalVars env),
                                    TE_GhostLocals := (if ghost = Ghost
                                                     then finsert varName (TE_GhostLocals env)
                                                     else fminus (TE_GhostLocals env) {|varName|}) \<rparr>)
                              \<lparr> TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
            by (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
          \<comment> \<open>Cast typechecks under the extended env: operand rhsTy, both integers, coreTy
              runtime if needed. Then clear+drop to env.\<close>
          let ?envD = "extend_env_with_tyvars env ghost next_mv next_mv'"
          have wfD: "tyenv_well_formed ?envD"
            using "1.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast
          have wkD: "is_well_kinded ?envD coreTy"
          proof -
            have "type_tyvars coreTy \<subseteq> fset (TE_TypeVars ?envD)"
              using is_well_kinded_type_tyvars_subset[OF wk]
              unfolding extend_env_with_tyvars_def by auto
            moreover have "TE_Datatypes ?envD = TE_Datatypes env"
              unfolding extend_env_with_tyvars_def by simp
            ultimately show ?thesis using is_well_kinded_transfer[OF wk] by blast
          qed
          have rtD: "ghost = NotGhost \<longrightarrow> is_runtime_type ?envD coreTy"
          proof
            assume dng: "ghost = NotGhost"
            have "is_runtime_type env coreTy"
              using elab_type_notghost_is_runtime(1)[OF td_wf "1.prems"(2) ety'[unfolded dng]] .
            thus "is_runtime_type ?envD coreTy"
              using is_runtime_type_extend_runtime_tyvars dng
              unfolding extend_env_with_tyvars_def by fastforce
          qed
          have cast_typed: "core_term_type ?envD ghost (CoreTm_Cast coreTy coreTm) = Some coreTy"
            using coreTm_typed_decl ints wkD rtD by auto
          have init_typed:
            "core_term_type env ghost (clear_metavars next_mv next_mv' (CoreTm_Cast coreTy coreTm)) = Some coreTy"
            using clear_metavars_typed_in_env[OF cast_typed "1.prems"(2,4) coreTy_below] .
          show ?thesis using wk rt init_typed by (simp add: cs_eq env'_eq)
        qed
      qed
    next
      case None
      \<comment> \<open>Inferred type (no annotation): coreTy = rhsTy, initTm = clear_metavars coreTm.\<close>
      from "1.prems"(1) Var None obtain tm coreTm rhsTy where
        tm_eq: "tmOpt = Some tm" and
        etm: "elab_term env elabEnv ghost tm next_mv = Inr (coreTm, rhsTy, next_mv')" and
        no_meta: "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)" and
        cs_eq: "coreStmt = CoreStmt_VarDecl ghost varName Var rhsTy
                              (clear_metavars next_mv next_mv' coreTm)" and
        env'_eq: "env' = (env \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars env),
                                TE_GhostLocals := (if ghost = Ghost
                                                 then finsert varName (TE_GhostLocals env)
                                                 else fminus (TE_GhostLocals env) {|varName|}) \<rparr>)
                          \<lparr> TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
        by (cases tmOpt) (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
      have wkrt: "is_well_kinded env rhsTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env rhsTy)"
        using elab_term_inferred_type_well_kinded_runtime[OF etm "1.prems"(2,3) "1.prems"(4) no_meta] .
      have wk: "is_well_kinded env rhsTy" using wkrt by simp
      have rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env rhsTy"
        using wkrt by auto
      have rhsTy_below: "type_tyvars rhsTy \<subseteq> {n. n < next_mv}"
        using is_well_kinded_type_tyvars_subset[OF wk] "1.prems"(4) by auto
      have coreTm_typed_decl:
        "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost coreTm = Some rhsTy"
        using elab_term_correct(1)[OF etm "1.prems"(2,3)] "1.prems"(4) by simp
      have init_typed: "core_term_type env ghost (clear_metavars next_mv next_mv' coreTm) = Some rhsTy"
        using clear_metavars_typed_in_env[OF coreTm_typed_decl "1.prems"(2,4) rhsTy_below] .
      show ?thesis using wk rt init_typed by (simp add: cs_eq env'_eq)
    qed
  next
    case Ref
    \<comment> \<open>Ref: varTy = rhsTy, initTm = clear_metavars coreTm (a metavariable-free lvalue).
        clear_metavars preserves lvalue-ness and writability.\<close>
    from "1.prems"(1) Ref obtain tm coreTm rhsTy where
      tm_eq: "tmOpt = Some tm" and
      etm: "elab_term env elabEnv ghost tm next_mv = Inr (coreTm, rhsTy, next_mv')" and
      lv: "is_lvalue coreTm" and
      no_meta: "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)" and
      cs_eq: "coreStmt = CoreStmt_VarDecl ghost varName Ref rhsTy
                            (clear_metavars next_mv next_mv' coreTm)" and
      env'_eq: "env' = (env \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars env),
                              TE_GhostLocals := (if ghost = Ghost
                                               then finsert varName (TE_GhostLocals env)
                                               else fminus (TE_GhostLocals env) {|varName|}) \<rparr>)
                        \<lparr> TE_ConstLocals := (if is_writable_lvalue env coreTm
                                            then fminus (TE_ConstLocals env) {|varName|}
                                            else finsert varName (TE_ConstLocals env)) \<rparr>"
      by (cases tmOpt) (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
    have wkrt: "is_well_kinded env rhsTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env rhsTy)"
      using elab_term_inferred_type_well_kinded_runtime[OF etm "1.prems"(2,3) "1.prems"(4) no_meta] .
    have wk: "is_well_kinded env rhsTy" using wkrt by simp
    have rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env rhsTy"
      using wkrt by auto
    have rhsTy_below: "type_tyvars rhsTy \<subseteq> {n. n < next_mv}"
      using is_well_kinded_type_tyvars_subset[OF wk] "1.prems"(4) by auto
    have coreTm_typed_decl:
      "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost coreTm = Some rhsTy"
      using elab_term_correct(1)[OF etm "1.prems"(2,3)] "1.prems"(4) by simp
    have init_typed: "core_term_type env ghost (clear_metavars next_mv next_mv' coreTm) = Some rhsTy"
      using clear_metavars_typed_in_env[OF coreTm_typed_decl "1.prems"(2,4) rhsTy_below] .
    \<comment> \<open>clear_metavars preserves is_lvalue / is_writable_lvalue (substitution lemmas).\<close>
    have lv': "is_lvalue (clear_metavars next_mv next_mv' coreTm)"
      using lv unfolding clear_metavars_def by simp
    have wl_eq: "is_writable_lvalue env (clear_metavars next_mv next_mv' coreTm)
                   = is_writable_lvalue env coreTm"
      unfolding clear_metavars_def by simp
    show ?thesis using wk rt lv' init_typed wl_eq by (simp add: cs_eq env'_eq)
  qed
next
  case (2 env elabEnv ghost loc varName ty next_mv) thus ?case sorry  \<comment> \<open>Fix\<close>
next
  case (3 env elabEnv ghost loc varName ty tm next_mv) thus ?case sorry  \<comment> \<open>Obtain\<close>
next
  case (4 env elabEnv ghost loc tm next_mv) thus ?case sorry  \<comment> \<open>Use\<close>
next
  case (5 env elabEnv ghost loc lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Assign\<close>
next
  case (6 env elabEnv ghost loc lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Swap\<close>
next
  case (7 env elabEnv ghost loc tmOpt next_mv) thus ?case sorry  \<comment> \<open>Return\<close>
next
  case (8 env elabEnv ghost loc condOpt proofBody next_mv) thus ?case sorry  \<comment> \<open>Assert\<close>
next
  \<comment> \<open>Assume: elaborate the predicate in Ghost mode and clear its interval
      metavariables, so it typechecks as Bool in env directly. The Core Assume
      rule re-checks in Ghost mode and leaves the env unchanged.\<close>
  case (9 env elabEnv ghost loc tm next_mv)
  from "9.prems"(1) obtain coreTm where
    etm: "elab_term env elabEnv Ghost tm next_mv = Inr (coreTm, CoreTy_Bool, next_mv')" and
    cs_eq: "coreStmt = CoreStmt_Assume (clear_metavars next_mv next_mv' coreTm)" and
    env'_eq: "env' = env"
    by (auto split: sum.splits prod.splits if_splits)
  have typed_ghost: "core_term_type (extend_env_with_tyvars env Ghost next_mv next_mv') Ghost coreTm
                       = Some CoreTy_Bool"
    using elab_term_correct(1)[OF etm "9.prems"(2,3)] "9.prems"(4) by simp
  have init_typed: "core_term_type env Ghost (clear_metavars next_mv next_mv' coreTm) = Some CoreTy_Bool"
    using clear_metavars_typed_in_env[OF typed_ghost "9.prems"(2,4)] by simp
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
