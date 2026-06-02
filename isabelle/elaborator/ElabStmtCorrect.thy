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


(* Bridging lemmas: from the elaboration mode (declGhost) to the ambient mode  *)
(* (ghost) used by core_statement_type.                                        *)
(*                                                                            *)
(* Under the VarDecl guard ghost = Ghost \<longrightarrow> declGhost = Ghost, the env extended *)
(* in ambient mode has the same TE_TypeVars as the one extended in declGhost   *)
(* mode and a (possibly larger) TE_RuntimeTypeVars, so embedded checks lift.   *)

lemma ext_ambient_as_decl_irrelevant:
  assumes guard: "ghost = Ghost \<longrightarrow> declGhost = Ghost"
  shows "\<exists>extraRT. extend_env_with_tyvars env ghost lo hi
                    = (extend_env_with_tyvars env declGhost lo hi)
                        \<lparr> TE_TypeVars := TE_TypeVars (extend_env_with_tyvars env declGhost lo hi)
                                          |\<union>| {||},
                          TE_RuntimeTypeVars := TE_RuntimeTypeVars (extend_env_with_tyvars env declGhost lo hi)
                                          |\<union>| extraRT \<rparr>"
proof (rule exI[where x = "if ghost = NotGhost \<and> declGhost = Ghost
                             then fset_of_list [lo..<hi] else {||}"])
  show "extend_env_with_tyvars env ghost lo hi
          = (extend_env_with_tyvars env declGhost lo hi)
              \<lparr> TE_TypeVars := TE_TypeVars (extend_env_with_tyvars env declGhost lo hi) |\<union>| {||},
                TE_RuntimeTypeVars := TE_RuntimeTypeVars (extend_env_with_tyvars env declGhost lo hi)
                  |\<union>| (if ghost = NotGhost \<and> declGhost = Ghost then fset_of_list [lo..<hi] else {||}) \<rparr>"
    using guard unfolding extend_env_with_tyvars_def
    by (cases ghost; cases declGhost) (auto simp: funion_assoc)
qed

lemma core_term_type_decl_to_ambient:
  assumes "core_term_type (extend_env_with_tyvars env declGhost lo hi) declGhost tm = Some ty"
    and "ghost = Ghost \<longrightarrow> declGhost = Ghost"
  shows "core_term_type (extend_env_with_tyvars env ghost lo hi) declGhost tm = Some ty"
proof -
  obtain extraRT where eq:
    "extend_env_with_tyvars env ghost lo hi
       = (extend_env_with_tyvars env declGhost lo hi)
           \<lparr> TE_TypeVars := TE_TypeVars (extend_env_with_tyvars env declGhost lo hi) |\<union>| {||},
             TE_RuntimeTypeVars := TE_RuntimeTypeVars (extend_env_with_tyvars env declGhost lo hi) |\<union>| extraRT \<rparr>"
    using ext_ambient_as_decl_irrelevant[OF assms(2)] by blast
  show ?thesis
    unfolding eq
    using core_term_type_irrelevant_tyvar[OF assms(1), where extraTV = "{||}" and extraRT = extraRT] .
qed

lemma core_impure_call_type_decl_to_ambient:
  assumes "core_impure_call_type (extend_env_with_tyvars env declGhost lo hi) declGhost tm = Some ty"
    and "ghost = Ghost \<longrightarrow> declGhost = Ghost"
  shows "core_impure_call_type (extend_env_with_tyvars env ghost lo hi) declGhost tm = Some ty"
proof -
  obtain extraRT where eq:
    "extend_env_with_tyvars env ghost lo hi
       = (extend_env_with_tyvars env declGhost lo hi)
           \<lparr> TE_TypeVars := TE_TypeVars (extend_env_with_tyvars env declGhost lo hi) |\<union>| {||},
             TE_RuntimeTypeVars := TE_RuntimeTypeVars (extend_env_with_tyvars env declGhost lo hi) |\<union>| extraRT \<rparr>"
    using ext_ambient_as_decl_irrelevant[OF assms(2)] by blast
  show ?thesis
    unfolding eq
    using core_impure_call_type_irrelevant_tyvar[OF assms(1), where extraTV = "{||}" and extraRT = extraRT] .
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
  case (1 env elabEnv ghost loc declGhost varName vorf tyOpt tmOpt next_mv)
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
  case (5 env elabEnv ghost loc assignGhost lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Assign\<close>
next
  case (6 env elabEnv ghost loc swapGhost lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Swap\<close>
next
  case (7 env elabEnv ghost loc returnGhost tmOpt next_mv) thus ?case sorry  \<comment> \<open>Return\<close>
next
  case (8 env elabEnv ghost loc condOpt proofBody next_mv) thus ?case sorry  \<comment> \<open>Assert\<close>
next
  \<comment> \<open>Assume: next_mv advances via elab_term.\<close>
  case (9 env elabEnv ghost loc tm next_mv)
  show ?case
    using "9.prems"
    by (auto dest!: elab_term_next_mv_monotone split: sum.splits prod.splits if_splits)
next
  case (10 env elabEnv ghost loc ifGhost cond thenB elseB next_mv) thus ?case sorry  \<comment> \<open>If\<close>
next
  case (11 env elabEnv ghost loc whileGhost cond attrs body next_mv) thus ?case sorry  \<comment> \<open>While\<close>
next
  case (12 env elabEnv ghost loc callGhost tm next_mv) thus ?case sorry  \<comment> \<open>Call\<close>
next
  case (13 env elabEnv ghost loc matchGhost scrut arms next_mv) thus ?case sorry  \<comment> \<open>Match\<close>
next
  \<comment> \<open>ShowHide: next_mv unchanged.\<close>
  case (14 env elabEnv ghost loc sh name next_mv)
  from "14.prems" show ?case by simp
next
  \<comment> \<open>Empty statement list.\<close>
  case (15 env elabEnv ghost next_mv)
  from "15.prems" show ?case by simp
next
  \<comment> \<open>Cons: chain head and tail.\<close>
  case (16 env elabEnv ghost stmt stmts next_mv)
  show ?case
    using "16.prems" "16.IH"(1) "16.IH"(2)
    by (fastforce split: sum.splits prod.splits dest: order_trans)
qed

(* Elaboration never changes the in-scope type variables: a statement only
   touches the local-variable fields, never TE_TypeVars / TE_RuntimeTypeVars.
   (Used to propagate the tyvar-bound precondition and the interval-widening
   premises through threaded calls.) *)
lemma elab_statement_preserves_TE_TypeVars:
  "elab_statement env elabEnv ghost stmt next_mv = Inr (coreStmt, env', next_mv')
     \<Longrightarrow> TE_TypeVars env' = TE_TypeVars env
       \<and> TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env"
and elab_statement_list_preserves_TE_TypeVars:
  "elab_statement_list env elabEnv ghost stmts next_mv = Inr (coreStmts, env', next_mv')
     \<Longrightarrow> TE_TypeVars env' = TE_TypeVars env
       \<and> TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env"
proof (induction env elabEnv ghost stmt next_mv and env elabEnv ghost stmts next_mv
       arbitrary: coreStmt env' next_mv' and coreStmts env' next_mv'
       rule: elab_statement_elab_statement_list.induct)
  \<comment> \<open>VarDecl: every successful branch returns env with only local-var fields changed.\<close>
  case (1 env elabEnv ghost loc declGhost varName vorf tyOpt tmOpt next_mv)
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
  case (5 env elabEnv ghost loc assignGhost lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Assign\<close>
next
  case (6 env elabEnv ghost loc swapGhost lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Swap\<close>
next
  case (7 env elabEnv ghost loc returnGhost tmOpt next_mv) thus ?case sorry  \<comment> \<open>Return\<close>
next
  case (8 env elabEnv ghost loc condOpt proofBody next_mv) thus ?case sorry  \<comment> \<open>Assert\<close>
next
  \<comment> \<open>Assume: env unchanged.\<close>
  case (9 env elabEnv ghost loc tm next_mv)
  show ?case using "9.prems" by (auto split: sum.splits prod.splits if_splits)
next
  case (10 env elabEnv ghost loc ifGhost cond thenB elseB next_mv) thus ?case sorry  \<comment> \<open>If\<close>
next
  case (11 env elabEnv ghost loc whileGhost cond attrs body next_mv) thus ?case sorry  \<comment> \<open>While\<close>
next
  case (12 env elabEnv ghost loc callGhost tm next_mv) thus ?case sorry  \<comment> \<open>Call\<close>
next
  case (13 env elabEnv ghost loc matchGhost scrut arms next_mv) thus ?case sorry  \<comment> \<open>Match\<close>
next
  \<comment> \<open>ShowHide: env unchanged.\<close>
  case (14 env elabEnv ghost loc sh name next_mv)
  from "14.prems" show ?case by simp
next
  \<comment> \<open>Empty statement list.\<close>
  case (15 env elabEnv ghost next_mv)
  from "15.prems" show ?case by simp
next
  \<comment> \<open>Cons: TE_TypeVars is preserved through head then tail.\<close>
  case (16 env elabEnv ghost stmt stmts next_mv)
  from "16.prems" obtain coreStmt1 env1 next_mv1 coreStmts1 where
    head: "elab_statement env elabEnv ghost stmt next_mv = Inr (coreStmt1, env1, next_mv1)" and
    tail: "elab_statement_list env1 elabEnv ghost stmts next_mv1
             = Inr (coreStmts1, env', next_mv')"
    by (auto split: sum.splits prod.splits)
  have e1: "TE_TypeVars env1 = TE_TypeVars env \<and> TE_RuntimeTypeVars env1 = TE_RuntimeTypeVars env"
    using "16.IH"(1) head by simp
  moreover have "TE_TypeVars env' = TE_TypeVars env1
                  \<and> TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env1"
    using "16.IH"(2) head tail by blast
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
    and rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy"
  shows "tyenv_well_formed
           (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                  TE_GhostLocals := (if declGhost = Ghost
                                     then finsert varName (TE_GhostLocals env)
                                     else fminus (TE_GhostLocals env) {|varName|}) \<rparr>
              \<lparr> TE_ConstLocals := c \<rparr>)"
proof (cases declGhost)
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
  case (1 env elabEnv ghost loc declGhost varName vorf tyOpt tmOpt next_mv)
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
  case (5 env elabEnv ghost loc assignGhost lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Assign\<close>
next
  case (6 env elabEnv ghost loc swapGhost lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Swap\<close>
next
  case (7 env elabEnv ghost loc returnGhost tmOpt next_mv) thus ?case sorry  \<comment> \<open>Return\<close>
next
  case (8 env elabEnv ghost loc condOpt proofBody next_mv) thus ?case sorry  \<comment> \<open>Assert\<close>
next
  \<comment> \<open>Assume: env unchanged.\<close>
  case (9 env elabEnv ghost loc tm next_mv)
  from "9.prems"(1) have "env' = env" by (auto split: sum.splits prod.splits if_splits)
  thus ?case using "9.prems"(2) by simp
next
  case (10 env elabEnv ghost loc ifGhost cond thenB elseB next_mv) thus ?case sorry  \<comment> \<open>If\<close>
next
  case (11 env elabEnv ghost loc whileGhost cond attrs body next_mv) thus ?case sorry  \<comment> \<open>While\<close>
next
  case (12 env elabEnv ghost loc callGhost tm next_mv) thus ?case sorry  \<comment> \<open>Call\<close>
next
  case (13 env elabEnv ghost loc matchGhost scrut arms next_mv) thus ?case sorry  \<comment> \<open>Match\<close>
next
  \<comment> \<open>ShowHide: env unchanged.\<close>
  case (14 env elabEnv ghost loc sh name next_mv)
  from "14.prems"(1) have "env' = env" by simp
  thus ?case using "14.prems"(2) by simp
next
  \<comment> \<open>Empty statement list.\<close>
  case (15 env elabEnv ghost next_mv)
  from "15.prems"(1) have "env' = env" by simp
  thus ?case using "15.prems"(2) by simp
next
  \<comment> \<open>Cons: thread elabenv_well_formed through head then tail.\<close>
  case (16 env elabEnv ghost stmt stmts next_mv)
  from "16.prems"(1) obtain coreStmt1 env1 next_mv1 coreStmts1 where
    head: "elab_statement env elabEnv ghost stmt next_mv = Inr (coreStmt1, env1, next_mv1)" and
    tail: "elab_statement_list env1 elabEnv ghost stmts next_mv1
             = Inr (coreStmts1, env', next_mv')"
    by (auto split: sum.splits prod.splits)
  have ee1: "elabenv_well_formed env1 elabEnv" using "16.IH"(1)[OF head "16.prems"(2)] .
  show ?case using "16.IH"(2) head tail ee1 by simp
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
  case (1 env elabEnv ghost loc declGhost varName vorf tyOpt tmOpt next_mv)
  have td_wf: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using "1.prems"(3) unfolding elabenv_well_formed_def by simp
  \<comment> \<open>The guard forces declMode to match: a non-ghost decl is rejected in a ghost
      context, so when declGhost = NotGhost the elaboration mode is NotGhost.\<close>
  let ?declMode = "if declGhost = Ghost then Ghost else ghost"
  from "1.prems"(1) have not_rejected: "\<not> (ghost = Ghost \<and> declGhost = NotGhost)"
    by (auto split: if_splits)
  hence mode_ng: "declGhost = NotGhost \<Longrightarrow> ?declMode = NotGhost"
    using GhostOrNot.exhaust by auto
  show ?case
  proof (cases vorf)
    case Var
    show ?thesis
    proof (cases tyOpt)
      case (Some ty)
      \<comment> \<open>Annotated (with or without an initializer): varTy = elaborated annotation.\<close>
      from "1.prems"(1) Var Some obtain coreTy where
        ety: "elab_type env elabEnv ?declMode ty = Inr coreTy" and
        env'_eq: "env' = (env \<lparr> TE_LocalVars := fmupd varName coreTy (TE_LocalVars env),
                                TE_GhostLocals := (if declGhost = Ghost
                                                 then finsert varName (TE_GhostLocals env)
                                                 else fminus (TE_GhostLocals env) {|varName|}) \<rparr>)
                          \<lparr> TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
        by (cases tmOpt) (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
      have wk: "is_well_kinded env coreTy"
        using elab_type_is_well_kinded(1)[OF td_wf "1.prems"(2) ety] .
      have rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type env coreTy"
        using mode_ng elab_type_notghost_is_runtime(1)[OF td_wf "1.prems"(2)] ety by auto
      show ?thesis
        unfolding env'_eq
        using tyenv_well_formed_vardecl_result[OF "1.prems"(2) wk rt] by simp
    next
      case None
      \<comment> \<open>Inferred from the initializer (no annotation): varTy = rhsTy from elab_term,
          which the no-metavar check guarantees is metavariable-free.\<close>
      from "1.prems"(1) Var None obtain tm coreTm rhsTy nmv where
        tm_eq: "tmOpt = Some tm" and
        etm: "elab_term env elabEnv ?declMode tm next_mv = Inr (coreTm, rhsTy, nmv)" and
        no_meta: "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)" and
        env'_eq: "env' = (env \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars env),
                                TE_GhostLocals := (if declGhost = Ghost
                                                 then finsert varName (TE_GhostLocals env)
                                                 else fminus (TE_GhostLocals env) {|varName|}) \<rparr>)
                          \<lparr> TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
        by (cases tmOpt) (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
      have wkrt: "is_well_kinded env rhsTy \<and> (?declMode = NotGhost \<longrightarrow> is_runtime_type env rhsTy)"
        using elab_term_inferred_type_well_kinded_runtime[OF etm "1.prems"(2,3) "1.prems"(4) no_meta] .
      have rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type env rhsTy"
        using wkrt mode_ng by auto
      show ?thesis
        unfolding env'_eq
        using tyenv_well_formed_vardecl_result[OF "1.prems"(2) conjunct1[OF wkrt] rt] by simp
    qed
  next
    case Ref
    \<comment> \<open>Ref: varTy = rhsTy from elab_term (the rhs must be a metavariable-free lvalue).\<close>
    from "1.prems"(1) Ref obtain tm coreTm rhsTy nmv where
      tm_eq: "tmOpt = Some tm" and
      etm: "elab_term env elabEnv ?declMode tm next_mv = Inr (coreTm, rhsTy, nmv)" and
      no_meta: "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)" and
      env'_eq: "env' = (env \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars env),
                              TE_GhostLocals := (if declGhost = Ghost
                                               then finsert varName (TE_GhostLocals env)
                                               else fminus (TE_GhostLocals env) {|varName|}) \<rparr>)
                        \<lparr> TE_ConstLocals := (if is_writable_lvalue env coreTm
                                            then fminus (TE_ConstLocals env) {|varName|}
                                            else finsert varName (TE_ConstLocals env)) \<rparr>"
      by (cases tmOpt) (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
    have wkrt: "is_well_kinded env rhsTy \<and> (?declMode = NotGhost \<longrightarrow> is_runtime_type env rhsTy)"
      using elab_term_inferred_type_well_kinded_runtime[OF etm "1.prems"(2,3) "1.prems"(4) no_meta] .
    have rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type env rhsTy"
      using wkrt mode_ng by auto
    show ?thesis
      unfolding env'_eq
      using tyenv_well_formed_vardecl_result[OF "1.prems"(2) conjunct1[OF wkrt] rt] by simp
  qed
next
  case (2 env elabEnv ghost loc varName ty next_mv) thus ?case sorry  \<comment> \<open>Fix\<close>
next
  case (3 env elabEnv ghost loc varName ty tm next_mv) thus ?case sorry  \<comment> \<open>Obtain\<close>
next
  case (4 env elabEnv ghost loc tm next_mv) thus ?case sorry  \<comment> \<open>Use\<close>
next
  case (5 env elabEnv ghost loc assignGhost lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Assign\<close>
next
  case (6 env elabEnv ghost loc swapGhost lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Swap\<close>
next
  case (7 env elabEnv ghost loc returnGhost tmOpt next_mv) thus ?case sorry  \<comment> \<open>Return\<close>
next
  case (8 env elabEnv ghost loc condOpt proofBody next_mv) thus ?case sorry  \<comment> \<open>Assert\<close>
next
  \<comment> \<open>Assume: env unchanged.\<close>
  case (9 env elabEnv ghost loc tm next_mv)
  from "9.prems"(1) have "env' = env" by (auto split: sum.splits prod.splits if_splits)
  thus ?case using "9.prems"(2) by simp
next
  case (10 env elabEnv ghost loc ifGhost cond thenB elseB next_mv) thus ?case sorry  \<comment> \<open>If\<close>
next
  case (11 env elabEnv ghost loc whileGhost cond attrs body next_mv) thus ?case sorry  \<comment> \<open>While\<close>
next
  case (12 env elabEnv ghost loc callGhost tm next_mv) thus ?case sorry  \<comment> \<open>Call\<close>
next
  case (13 env elabEnv ghost loc matchGhost scrut arms next_mv) thus ?case sorry  \<comment> \<open>Match\<close>
next
  \<comment> \<open>ShowHide: env unchanged.\<close>
  case (14 env elabEnv ghost loc sh name next_mv)
  from "14.prems"(1) have "env' = env" by simp
  thus ?case using "14.prems"(2) by simp
next
  \<comment> \<open>Empty statement list.\<close>
  case (15 env elabEnv ghost next_mv)
  from "15.prems"(1) have "env' = env" by simp
  thus ?case using "15.prems"(2) by simp
next
  \<comment> \<open>Cons: thread well-formedness (and the tyvar bound) through head then tail.\<close>
  case (16 env elabEnv ghost stmt stmts next_mv)
  from "16.prems"(1) obtain coreStmt1 env1 next_mv1 coreStmts1 where
    head: "elab_statement env elabEnv ghost stmt next_mv = Inr (coreStmt1, env1, next_mv1)" and
    tail: "elab_statement_list env1 elabEnv ghost stmts next_mv1
             = Inr (coreStmts1, env', next_mv')"
    by (auto split: sum.splits prod.splits)
  have wf1: "tyenv_well_formed env1"
    using "16.IH"(1)[OF head "16.prems"(2,3,4)] .
  have ee1: "elabenv_well_formed env1 elabEnv"
    using elab_statement_preserves_elabenv_well_formed(1)[OF head "16.prems"(3)] .
  \<comment> \<open>The tyvar bound transfers: TE_TypeVars is unchanged and next_mv only grows.\<close>
  have tv1: "TE_TypeVars env1 = TE_TypeVars env"
    using elab_statement_preserves_TE_TypeVars(1)[OF head] by simp
  have nmv1: "next_mv \<le> next_mv1" using elab_statement_next_mv_monotone(1)[OF head] .
  have bound1: "\<forall>n. n |\<in>| TE_TypeVars env1 \<longrightarrow> n < next_mv1"
    using "16.prems"(4) tv1 nmv1 by auto
  show ?case
    using "16.IH"(2) head tail wf1 ee1 bound1 by simp
qed


(* ========================================================================== *)
(* Main correctness theorem                                                   *)
(* ========================================================================== *)

theorem elab_statement_correct:
  "elab_statement env elabEnv ghost stmt next_mv = Inr (coreStmt, env', next_mv') \<Longrightarrow>
   tyenv_well_formed env \<Longrightarrow> elabenv_well_formed env elabEnv \<Longrightarrow>
   (\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv) \<Longrightarrow>
   core_statement_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost coreStmt
     = Some (extend_env_with_tyvars env' ghost next_mv next_mv')"
and elab_statement_list_correct:
  "elab_statement_list env elabEnv ghost stmts next_mv = Inr (coreStmts, env', next_mv') \<Longrightarrow>
   tyenv_well_formed env \<Longrightarrow> elabenv_well_formed env elabEnv \<Longrightarrow>
   (\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv) \<Longrightarrow>
   core_statement_list_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost coreStmts
     = Some (extend_env_with_tyvars env' ghost next_mv next_mv')"
proof (induction env elabEnv ghost stmt next_mv and env elabEnv ghost stmts next_mv
       arbitrary: coreStmt env' next_mv' and coreStmts env' next_mv'
       rule: elab_statement_elab_statement_list.induct)
  \<comment> \<open>VarDecl: the chosen type is well-kinded (runtime in NotGhost mode) and the
      initializer typechecks to it, all under the extended/ambient env. The result
      env's local-var updates commute with the tyvar extension.\<close>
  case (1 env elabEnv ghost loc declGhost varName vorf tyOpt tmOpt next_mv)
  let ?envA = "extend_env_with_tyvars env ghost next_mv next_mv'"
  have td_wf: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using "1.prems"(3) unfolding elabenv_well_formed_def by simp
  \<comment> \<open>The guard: a non-ghost decl is rejected in a ghost context, so declMode = declGhost.\<close>
  from "1.prems"(1) have gd: "ghost = Ghost \<longrightarrow> declGhost = Ghost"
    using GhostOrNot.exhaust by (auto split: if_splits)
  let ?declMode = "if declGhost = Ghost then Ghost else ghost"
  have declMode_eq: "?declMode = declGhost" using gd by (metis GhostOrNot.exhaust)
  \<comment> \<open>Helper facts: lift well-kindedness / runtime to the extended ambient env, and
      build the well-kinded + runtime obligation the Core rule requires.\<close>
  have wk_lift: "\<And>t. is_well_kinded env t \<Longrightarrow> is_well_kinded ?envA t"
  proof -
    fix t assume "is_well_kinded env t"
    moreover have "type_tyvars t \<subseteq> fset (TE_TypeVars ?envA)"
      using is_well_kinded_type_tyvars_subset[OF \<open>is_well_kinded env t\<close>]
      unfolding extend_env_with_tyvars_def by auto
    moreover have "TE_Datatypes ?envA = TE_Datatypes env"
      unfolding extend_env_with_tyvars_def by simp
    ultimately show "is_well_kinded ?envA t"
      using is_well_kinded_transfer by blast
  qed
  have rt_lift: "\<And>t. ghost = NotGhost \<Longrightarrow> is_runtime_type env t \<Longrightarrow> is_runtime_type ?envA t"
    using is_runtime_type_extend_runtime_tyvars unfolding extend_env_with_tyvars_def by fastforce
  \<comment> \<open>The result env (Core rule output) is env' extended, by commutation.\<close>
  have commute: "\<And>lv gl cl.
      (?envA) \<lparr> TE_LocalVars := lv, TE_GhostLocals := gl, TE_ConstLocals := cl \<rparr>
        = extend_env_with_tyvars
            (env \<lparr> TE_LocalVars := lv, TE_GhostLocals := gl, TE_ConstLocals := cl \<rparr>)
            ghost next_mv next_mv'"
    using extend_env_with_tyvars_TE_LocalVars_commute by metis
  show ?case
  proof (cases vorf)
    case Var
    show ?thesis
    proof (cases tyOpt)
      case (Some ty)
      \<comment> \<open>Annotated: coreTy = elaborated annotation; rhs (Default or coerced term) types to coreTy.\<close>
      from "1.prems"(1) Var Some obtain coreTy where
        ety: "elab_type env elabEnv ?declMode ty = Inr coreTy"
        by (cases tmOpt) (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
      have ety': "elab_type env elabEnv declGhost ty = Inr coreTy"
        using ety declMode_eq by simp
      have wk_env: "is_well_kinded env coreTy"
        using elab_type_is_well_kinded(1)[OF td_wf "1.prems"(2) ety'] .
      have wk: "is_well_kinded ?envA coreTy" using wk_lift[OF wk_env] .
      have rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type ?envA coreTy"
      proof
        assume dng: "declGhost = NotGhost"
        with gd have gng: "ghost = NotGhost" by (cases ghost) auto
        have "is_runtime_type env coreTy"
          using elab_type_notghost_is_runtime(1)[OF td_wf "1.prems"(2) ety'[unfolded dng]] .
        thus "is_runtime_type ?envA coreTy" using rt_lift gng by simp
      qed
      \<comment> \<open>Establish that the elaborated initializer typechecks (under ?envA, declGhost
          mode) to coreTy — by cases on whether an initializer is present.\<close>
      show ?thesis
      proof (cases tmOpt)
        case None
        \<comment> \<open>Default-initialized: initTm = CoreTm_Default coreTy, which types to coreTy.\<close>
        from "1.prems"(1) Var Some None ety gd have
          cs_eq: "coreStmt = CoreStmt_VarDecl declGhost varName Var coreTy (CoreTm_Default coreTy)" and
          env'_eq: "env' = (env \<lparr> TE_LocalVars := fmupd varName coreTy (TE_LocalVars env),
                                  TE_GhostLocals := (if declGhost = Ghost
                                                   then finsert varName (TE_GhostLocals env)
                                                   else fminus (TE_GhostLocals env) {|varName|}) \<rparr>)
                            \<lparr> TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>" and
          mv_eq: "next_mv' = next_mv"
          by (auto simp: Let_def split: sum.splits if_splits)
        have init_typed: "core_term_type ?envA declGhost (CoreTm_Default coreTy) = Some coreTy"
          using wk rt by simp
        show ?thesis
          using gd wk rt init_typed
          by (simp add: cs_eq env'_eq extend_env_with_tyvars_def)
      next
        case (Some tm)
        \<comment> \<open>Annotated initializer: elaborate the term, then unify or insert an int cast.\<close>
        from "1.prems"(1) Var \<open>tyOpt = Some ty\<close> Some ety declMode_eq obtain coreTm rhsTy nmv where
          etm: "elab_term env elabEnv declGhost tm next_mv = Inr (coreTm, rhsTy, nmv)"
          by (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
        \<comment> \<open>Typing of coreTm under the decl-mode extended env.\<close>
        have coreTm_typed_decl:
          "core_term_type (extend_env_with_tyvars env declGhost next_mv nmv) declGhost coreTm = Some rhsTy"
          using elab_term_correct(1)[OF etm "1.prems"(2,3)] "1.prems"(4) by simp
        show ?thesis
        proof (cases "unify (\<lambda>n. n |\<notin>| TE_TypeVars env) rhsTy coreTy")
          case (Some subst)
          \<comment> \<open>unify succeeded: initTm = apply_subst_to_term subst coreTm, typing to coreTy.\<close>
          from "1.prems"(1) Var \<open>tyOpt = Some ty\<close> \<open>tmOpt = Some tm\<close> ety etm Some declMode_eq have
            cs_eq: "coreStmt = CoreStmt_VarDecl declGhost varName Var coreTy
                                  (apply_subst_to_term subst coreTm)" and
            env'_eq: "env' = (env \<lparr> TE_LocalVars := fmupd varName coreTy (TE_LocalVars env),
                                    TE_GhostLocals := (if declGhost = Ghost
                                                     then finsert varName (TE_GhostLocals env)
                                                     else fminus (TE_GhostLocals env) {|varName|}) \<rparr>)
                              \<lparr> TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>" and
            mv_eq: "next_mv' = nmv"
            by (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
          \<comment> \<open>The substituted term has type apply_subst subst rhsTy = apply_subst subst coreTy = coreTy
              (coreTy is metavariable-free, being elaborated, so subst leaves it unchanged).\<close>
          let ?envD = "extend_env_with_tyvars env declGhost next_mv nmv"
          let ?is_flex = "\<lambda>n. n |\<notin>| TE_TypeVars env"
          have wfD: "tyenv_well_formed ?envD"
            using "1.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast
          \<comment> \<open>rhsTy and coreTy are well-kinded (and runtime in NotGhost mode) in ?envD.\<close>
          have rhsTy_wk: "is_well_kinded ?envD rhsTy"
            using core_term_type_well_kinded[OF coreTm_typed_decl wfD] .
          have rhsTy_rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type ?envD rhsTy"
            using core_term_type_notghost_runtime coreTm_typed_decl wfD by auto
          have coreTy_wkD: "is_well_kinded ?envD coreTy"
          proof -
            have "type_tyvars coreTy \<subseteq> fset (TE_TypeVars ?envD)"
              using is_well_kinded_type_tyvars_subset[OF wk_env]
              unfolding extend_env_with_tyvars_def by auto
            moreover have "TE_Datatypes ?envD = TE_Datatypes env"
              unfolding extend_env_with_tyvars_def by simp
            ultimately show ?thesis using is_well_kinded_transfer[OF wk_env] by blast
          qed
          have coreTy_rtD: "declGhost = NotGhost \<longrightarrow> is_runtime_type ?envD coreTy"
          proof
            assume dng: "declGhost = NotGhost"
            have "is_runtime_type env coreTy"
              using elab_type_notghost_is_runtime(1)[OF td_wf "1.prems"(2) ety'[unfolded dng]] .
            thus "is_runtime_type ?envD coreTy"
              using is_runtime_type_extend_runtime_tyvars dng
              unfolding extend_env_with_tyvars_def by fastforce
          qed
          \<comment> \<open>The unifier's range is well-kinded / runtime in ?envD.\<close>
          have subst_wk: "\<forall>ty' \<in> fmran' subst. is_well_kinded ?envD ty'"
            using unify_preserves_well_kinded[OF Some rhsTy_wk coreTy_wkD] .
          have subst_rt: "declGhost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type ?envD ty')"
            using unify_preserves_runtime[OF Some] rhsTy_rt coreTy_rtD by blast
          \<comment> \<open>The unifier binds only flex metas, so locals / return type are unaffected.\<close>
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
          \<comment> \<open>Lift coreTm's typing through the substitution.\<close>
          have subst_typed: "core_term_type ?envD declGhost (apply_subst_to_term subst coreTm)
                               = Some (apply_subst subst rhsTy)"
            using apply_subst_to_term_preserves_typing
                    [OF coreTm_typed_decl wfD subst_wk subst_rt locals_unaffected ret_unaffected] .
          \<comment> \<open>apply_subst subst rhsTy = apply_subst subst coreTy (unify) = coreTy (subst is flex-only,
              coreTy is metavariable-free, so its tyvars are disjoint from subst's domain).\<close>
          have coreTy_tvs: "type_tyvars coreTy \<subseteq> fset (TE_TypeVars env)"
            using is_well_kinded_type_tyvars_subset[OF wk_env] .
          have dom_disj: "type_tyvars coreTy \<inter> fset (fmdom subst) = {}"
            using dom_flex coreTy_tvs by auto
          have "apply_subst subst rhsTy = apply_subst subst coreTy"
            using unify_sound[OF Some] .
          also have "apply_subst subst coreTy = coreTy"
            using apply_subst_disjoint_id[OF dom_disj] .
          finally have subst_typed_coreTy:
            "core_term_type ?envD declGhost (apply_subst_to_term subst coreTm) = Some coreTy"
            using subst_typed by simp
          \<comment> \<open>Bridge to the ambient env; the interval already matches (next_mv' = nmv).\<close>
          have init_typed: "core_term_type ?envA declGhost (apply_subst_to_term subst coreTm) = Some coreTy"
            using core_term_type_decl_to_ambient[OF subst_typed_coreTy[unfolded mv_eq[symmetric]] gd] .
          show ?thesis
            using gd wk rt init_typed
            by (simp add: cs_eq env'_eq extend_env_with_tyvars_def)
        next
          case None
          \<comment> \<open>unify failed; both integer types, so initTm = CoreTm_Cast coreTy coreTm.\<close>
          from "1.prems"(1) Var \<open>tyOpt = Some ty\<close> \<open>tmOpt = Some tm\<close> ety etm None declMode_eq have
            ints: "is_integer_type rhsTy \<and> is_integer_type coreTy" and
            cs_eq: "coreStmt = CoreStmt_VarDecl declGhost varName Var coreTy (CoreTm_Cast coreTy coreTm)" and
            env'_eq: "env' = (env \<lparr> TE_LocalVars := fmupd varName coreTy (TE_LocalVars env),
                                    TE_GhostLocals := (if declGhost = Ghost
                                                     then finsert varName (TE_GhostLocals env)
                                                     else fminus (TE_GhostLocals env) {|varName|}) \<rparr>)
                              \<lparr> TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>" and
            mv_eq: "next_mv' = nmv"
            by (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
          \<comment> \<open>coreTm typechecks under ?envA in declGhost mode (interval coincides since next_mv' = nmv).\<close>
          have coreTm_typed: "core_term_type ?envA declGhost coreTm = Some rhsTy"
            using core_term_type_decl_to_ambient[OF coreTm_typed_decl[unfolded mv_eq[symmetric]] gd] .
          \<comment> \<open>Cast to coreTy typechecks: operand is rhsTy, both integers, coreTy runtime if needed.\<close>
          have init_typed: "core_term_type ?envA declGhost (CoreTm_Cast coreTy coreTm) = Some coreTy"
            using coreTm_typed ints wk rt by auto
          show ?thesis
            using gd wk rt init_typed
            by (simp add: cs_eq env'_eq extend_env_with_tyvars_def)
        qed
      qed
    next
      case None
      \<comment> \<open>Inferred type (no annotation): coreTy = rhsTy, initTm = coreTm directly.\<close>
      from "1.prems"(1) Var None obtain tm coreTm rhsTy where
        tm_eq: "tmOpt = Some tm" and
        etm: "elab_term env elabEnv ?declMode tm next_mv = Inr (coreTm, rhsTy, next_mv')" and
        no_meta: "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)" and
        cs_eq: "coreStmt = CoreStmt_VarDecl declGhost varName Var rhsTy coreTm" and
        env'_eq: "env' = (env \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars env),
                                TE_GhostLocals := (if declGhost = Ghost
                                                 then finsert varName (TE_GhostLocals env)
                                                 else fminus (TE_GhostLocals env) {|varName|}) \<rparr>)
                          \<lparr> TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
        by (cases tmOpt) (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
      have wkrt: "is_well_kinded env rhsTy \<and> (?declMode = NotGhost \<longrightarrow> is_runtime_type env rhsTy)"
        using elab_term_inferred_type_well_kinded_runtime[OF etm "1.prems"(2,3) "1.prems"(4) no_meta] .
      have wk: "is_well_kinded ?envA rhsTy" using wk_lift[OF conjunct1[OF wkrt]] .
      have rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type ?envA rhsTy"
      proof
        assume dng: "declGhost = NotGhost"
        with gd have gng: "ghost = NotGhost" by (cases ghost) auto
        have "is_runtime_type env rhsTy" using wkrt declMode_eq dng by auto
        thus "is_runtime_type ?envA rhsTy" using rt_lift gng by simp
      qed
      have coreTm_typed_decl:
        "core_term_type (extend_env_with_tyvars env declGhost next_mv next_mv') declGhost coreTm = Some rhsTy"
        using elab_term_correct(1)[OF etm[unfolded declMode_eq] "1.prems"(2,3)] "1.prems"(4) by simp
      have init_typed: "core_term_type ?envA declGhost coreTm = Some rhsTy"
        using core_term_type_decl_to_ambient[OF coreTm_typed_decl gd] .
      show ?thesis
        using gd wk rt init_typed
        by (simp add: cs_eq env'_eq extend_env_with_tyvars_def)
    qed
  next
    case Ref
    \<comment> \<open>Ref: varTy = rhsTy, initTm = coreTm (a metavariable-free lvalue).\<close>
    from "1.prems"(1) Ref obtain tm coreTm rhsTy where
      tm_eq: "tmOpt = Some tm" and
      etm: "elab_term env elabEnv ?declMode tm next_mv = Inr (coreTm, rhsTy, next_mv')" and
      lv: "is_lvalue coreTm" and
      no_meta: "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)" and
      cs_eq: "coreStmt = CoreStmt_VarDecl declGhost varName Ref rhsTy coreTm" and
      env'_eq: "env' = (env \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars env),
                              TE_GhostLocals := (if declGhost = Ghost
                                               then finsert varName (TE_GhostLocals env)
                                               else fminus (TE_GhostLocals env) {|varName|}) \<rparr>)
                        \<lparr> TE_ConstLocals := (if is_writable_lvalue env coreTm
                                            then fminus (TE_ConstLocals env) {|varName|}
                                            else finsert varName (TE_ConstLocals env)) \<rparr>"
      by (cases tmOpt) (auto simp: Let_def split: sum.splits prod.splits option.splits if_splits)
    have wkrt: "is_well_kinded env rhsTy \<and> (?declMode = NotGhost \<longrightarrow> is_runtime_type env rhsTy)"
      using elab_term_inferred_type_well_kinded_runtime[OF etm "1.prems"(2,3) "1.prems"(4) no_meta] .
    have wk: "is_well_kinded ?envA rhsTy" using wk_lift[OF conjunct1[OF wkrt]] .
    have rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type ?envA rhsTy"
    proof
      assume dng: "declGhost = NotGhost"
      with gd have gng: "ghost = NotGhost" by (cases ghost) auto
      have "is_runtime_type env rhsTy" using wkrt declMode_eq dng by auto
      thus "is_runtime_type ?envA rhsTy" using rt_lift gng by simp
    qed
    have coreTm_typed_decl:
      "core_term_type (extend_env_with_tyvars env declGhost next_mv next_mv') declGhost coreTm = Some rhsTy"
      using elab_term_correct(1)[OF etm[unfolded declMode_eq] "1.prems"(2,3)] "1.prems"(4) by simp
    have init_typed: "core_term_type ?envA declGhost coreTm = Some rhsTy"
      using core_term_type_decl_to_ambient[OF coreTm_typed_decl gd] .
    \<comment> \<open>is_writable_lvalue is unaffected by the tyvar extension (it reads only
        TE_LocalVars / TE_ConstLocals).\<close>
    have wl_eq: "is_writable_lvalue ?envA coreTm = is_writable_lvalue env coreTm"
      by (induction coreTm rule: is_writable_lvalue.induct)
         (auto simp: tyenv_var_writable_def extend_env_with_tyvars_def)
    show ?thesis
      using gd wk rt lv init_typed wl_eq
      by (simp add: cs_eq env'_eq extend_env_with_tyvars_def)
  qed
next
  case (2 env elabEnv ghost loc varName ty next_mv) thus ?case sorry  \<comment> \<open>Fix\<close>
next
  case (3 env elabEnv ghost loc varName ty tm next_mv) thus ?case sorry  \<comment> \<open>Obtain\<close>
next
  case (4 env elabEnv ghost loc tm next_mv) thus ?case sorry  \<comment> \<open>Use\<close>
next
  case (5 env elabEnv ghost loc assignGhost lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Assign\<close>
next
  case (6 env elabEnv ghost loc swapGhost lhs rhs next_mv) thus ?case sorry  \<comment> \<open>Swap\<close>
next
  case (7 env elabEnv ghost loc returnGhost tmOpt next_mv) thus ?case sorry  \<comment> \<open>Return\<close>
next
  case (8 env elabEnv ghost loc condOpt proofBody next_mv) thus ?case sorry  \<comment> \<open>Assert\<close>
next
  \<comment> \<open>Assume: elaborate the predicate in Ghost mode; the Core Assume rule re-checks
      it in Ghost mode, so we bridge the ambient-vs-Ghost runtime-tyvar mismatch
      with core_term_type_irrelevant_tyvar.\<close>
  case (9 env elabEnv ghost loc tm next_mv)
  from "9.prems"(1) obtain coreTm where
    etm: "elab_term env elabEnv Ghost tm next_mv = Inr (coreTm, CoreTy_Bool, next_mv')" and
    cs_eq: "coreStmt = CoreStmt_Assume coreTm" and env'_eq: "env' = env"
    by (auto split: sum.splits prod.splits if_splits)
  \<comment> \<open>Typed as Bool under env extended in Ghost mode.\<close>
  have typed_ghost: "core_term_type (extend_env_with_tyvars env Ghost next_mv next_mv') Ghost coreTm
                       = Some CoreTy_Bool"
    using elab_term_correct(1)[OF etm "9.prems"(2,3)] "9.prems"(4) by simp
  \<comment> \<open>The ambient-mode extended env has the same TE_TypeVars and a (possibly larger)
      TE_RuntimeTypeVars, so the typing transfers by irrelevant_tyvar.\<close>
  let ?envG = "extend_env_with_tyvars env Ghost next_mv next_mv'"
  let ?envA = "extend_env_with_tyvars env ghost next_mv next_mv'"
  have shape: "?envA = ?envG \<lparr> TE_TypeVars := TE_TypeVars ?envG |\<union>| {||},
                              TE_RuntimeTypeVars := TE_RuntimeTypeVars ?envG
                                |\<union>| (if ghost = NotGhost then fset_of_list [next_mv..<next_mv'] else {||}) \<rparr>"
    unfolding extend_env_with_tyvars_def by (cases "ghost = NotGhost") auto
  have typed_ambient: "core_term_type ?envA Ghost coreTm = Some CoreTy_Bool"
    using core_term_type_irrelevant_tyvar[OF typed_ghost] shape by metis
  show ?case using typed_ambient by (simp add: cs_eq env'_eq)
next
  case (10 env elabEnv ghost loc ifGhost cond thenB elseB next_mv) thus ?case sorry  \<comment> \<open>If\<close>
next
  case (11 env elabEnv ghost loc whileGhost cond attrs body next_mv) thus ?case sorry  \<comment> \<open>While\<close>
next
  case (12 env elabEnv ghost loc callGhost tm next_mv) thus ?case sorry  \<comment> \<open>Call\<close>
next
  case (13 env elabEnv ghost loc matchGhost scrut arms next_mv) thus ?case sorry  \<comment> \<open>Match\<close>
next
  \<comment> \<open>ShowHide: empty interval, env unchanged.\<close>
  case (14 env elabEnv ghost loc sh name next_mv)
  from "14.prems"(1) have cs_eq: "coreStmt = CoreStmt_ShowHide sh name"
    and env'_eq: "env' = env" and mv_eq: "next_mv' = next_mv"
    by auto
  show ?case by (simp add: cs_eq env'_eq mv_eq)
next
  \<comment> \<open>Empty statement list: empty interval, env unchanged.\<close>
  case (15 env elabEnv ghost next_mv)
  from "15.prems"(1) have "coreStmts = []" and "env' = env" and "next_mv' = next_mv"
    by auto
  thus ?case by simp
next
  \<comment> \<open>Cons: the head typechecks under [next_mv, next_mv1); the tail under
      [next_mv1, next_mv'). Widen both to the full interval [next_mv, next_mv')
      and thread the env through.\<close>
  case (16 env elabEnv ghost stmt stmts next_mv)
  from "16.prems"(1) obtain coreStmt1 env1 next_mv1 coreStmts1 where
    head: "elab_statement env elabEnv ghost stmt next_mv = Inr (coreStmt1, env1, next_mv1)" and
    tail: "elab_statement_list env1 elabEnv ghost stmts next_mv1
             = Inr (coreStmts1, env', next_mv')" and
    cs_eq: "coreStmts = coreStmt1 # coreStmts1"
    by (auto split: sum.splits prod.splits)
  \<comment> \<open>Bounds / preservation facts needed for the tail IH.\<close>
  have nmv1: "next_mv \<le> next_mv1" using elab_statement_next_mv_monotone(1)[OF head] .
  have nmv': "next_mv1 \<le> next_mv'" using elab_statement_list_next_mv_monotone[OF tail] .
  have tv1: "TE_TypeVars env1 = TE_TypeVars env"
    using elab_statement_preserves_TE_TypeVars(1)[OF head] by simp
  have rtv1: "TE_RuntimeTypeVars env1 = TE_RuntimeTypeVars env"
    using elab_statement_preserves_TE_TypeVars(1)[OF head] by simp
  have wf1: "tyenv_well_formed env1"
    using elab_statement_preserves_well_formed(1)[OF head "16.prems"(2,3,4)] .
  have ee1: "elabenv_well_formed env1 elabEnv"
    using elab_statement_preserves_elabenv_well_formed(1)[OF head "16.prems"(3)] .
  have bound1: "\<forall>n. n |\<in>| TE_TypeVars env1 \<longrightarrow> n < next_mv1"
    using "16.prems"(4) tv1 nmv1 by auto
  \<comment> \<open>Head: typechecks over [next_mv, next_mv1), widened to [next_mv, next_mv').\<close>
  have head_typed: "core_statement_type (extend_env_with_tyvars env ghost next_mv next_mv1) ghost coreStmt1
                      = Some (extend_env_with_tyvars env1 ghost next_mv next_mv1)"
    using "16.IH"(1)[OF head "16.prems"(2,3,4)] .
  have head_wide: "core_statement_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost coreStmt1
                     = Some (extend_env_with_tyvars env1 ghost next_mv next_mv')"
    using core_statement_type_extend_env_with_tyvars_mono[OF head_typed tv1 rtv1 le_refl nmv'] .
  \<comment> \<open>Tail: typechecks over [next_mv1, next_mv'), widened to [next_mv, next_mv').\<close>
  have tail_typed: "core_statement_list_type (extend_env_with_tyvars env1 ghost next_mv1 next_mv') ghost coreStmts1
                      = Some (extend_env_with_tyvars env' ghost next_mv1 next_mv')"
    using "16.IH"(2) head tail wf1 ee1 bound1 by simp
  have tail_wide: "core_statement_list_type (extend_env_with_tyvars env1 ghost next_mv next_mv') ghost coreStmts1
                     = Some (extend_env_with_tyvars env' ghost next_mv next_mv')"
    using core_statement_list_type_extend_env_with_tyvars_mono[OF tail_typed nmv1 le_refl] .
  show ?case
    using head_wide tail_wide by (simp add: cs_eq)
qed

end
