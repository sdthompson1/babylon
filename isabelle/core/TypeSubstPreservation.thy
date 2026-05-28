theory TypeSubstPreservation
  imports TypeSubstHelpers
begin

(* ========================================================================== *)
(* A type preservation theorem for apply_subst_to_term. *)
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


end
