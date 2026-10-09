theory CoreContractTypecheck
  imports CoreTypecheck ModuleBodyEnv TypeSubstEnv
begin

(* Typechecking of function contracts (FI_Requires, FI_Ensures).

   A contract term is a Ghost-mode term of type bool. A precondition is typed
   in the body env of the function itself, with the parameters named
   contract_arg_names; a postcondition is typed in the body env of
   post_funinfo, with the parameters named contract_post_names (see
   ModuleBodyEnv.thy).

   The body env is a parameter (mkEnv), so that the same definition serves
   the module typechecker (mkEnv = module_body_env_for env) and the
   interpreter (mkEnv = body_env_for env, in StateMatchesEnv.thy); the two
   coincide on a closed module. *)

definition contracts_typed_in ::
  "(string list \<Rightarrow> FunInfo \<Rightarrow> CoreTyEnv) \<Rightarrow> FunInfo \<Rightarrow> bool" where
  "contracts_typed_in mkEnv info =
    ((\<forall>tm \<in> set (FI_Requires info).
        core_term_type (mkEnv (contract_arg_names (length (FI_TmArgs info))) info)
                       Ghost tm = Some CoreTy_Bool)
     \<and> (\<forall>tm \<in> set (FI_Ensures info).
          core_term_type (mkEnv (contract_post_names (length (FI_TmArgs info)))
                                (post_funinfo info))
                         Ghost tm = Some CoreTy_Bool))"

(* The contracts of a function, declared with FunInfo info in the module-level
   env, are well-typed. *)
definition fun_contracts_well_typed :: "CoreTyEnv \<Rightarrow> FunInfo \<Rightarrow> bool" where
  "fun_contracts_well_typed env info = contracts_typed_in (module_body_env_for env) info"


(* An empty contract is well-typed in any env. *)
lemma contracts_typed_in_empty:
  assumes "FI_Requires info = []" and "FI_Ensures info = []"
  shows "contracts_typed_in mkEnv info"
  using assms unfolding contracts_typed_in_def by simp

lemma fun_contracts_well_typed_empty:
  assumes "FI_Requires info = []" and "FI_Ensures info = []"
  shows "fun_contracts_well_typed env info"
  unfolding fun_contracts_well_typed_def using contracts_typed_in_empty[OF assms] .

(* Transport to another enclosing env (with the same FunInfo): if every term
   typed bool in a body env over env is typed bool in the corresponding body
   env over env', the contracts carry over. *)
lemma fun_contracts_well_typed_mono:
  assumes ok: "fun_contracts_well_typed env info"
      and step: "\<And>names info' tm.
                   core_term_type (module_body_env_for env names info') Ghost tm
                     = Some CoreTy_Bool
                   \<Longrightarrow> core_term_type (module_body_env_for env' names info') Ghost tm
                     = Some CoreTy_Bool"
  shows "fun_contracts_well_typed env' info"
  using ok step unfolding fun_contracts_well_typed_def contracts_typed_in_def by blast


(* ========================================================================== *)
(* Contracts under type substitution                                          *)
(* ========================================================================== *)

(* Substitution commutes with forming the postcondition signature. *)
lemma apply_subst_to_funinfo_post_funinfo:
  "apply_subst_to_funinfo s (post_funinfo info) = post_funinfo (apply_subst_to_funinfo s info)"
  by (rule FunInfo.equality)
     (simp_all add: apply_subst_to_funinfo_def post_funinfo_def comp_def split_def)

(* Transport of contract typing along a type substitution: if each contract
   term that is typed in a body env over srcEnv (for the function's own
   signature or its postcondition signature) is, after substitution, typed in
   the corresponding body env over tgtEnv, then the substituted contracts are
   well-typed in tgtEnv. *)
lemma fun_contracts_well_typed_subst:
  assumes ctr: "fun_contracts_well_typed srcEnv info"
      and step: "\<And>names info' tm.
                   info' = info \<or> info' = post_funinfo info \<Longrightarrow>
                   length names = length (FI_TmArgs info') \<Longrightarrow>
                   core_term_type (module_body_env_for srcEnv names info') Ghost tm
                     = Some CoreTy_Bool \<Longrightarrow>
                   core_term_type (module_body_env_for tgtEnv names
                                     (apply_subst_to_funinfo s info'))
                                  Ghost (apply_subst_to_term s tm) = Some CoreTy_Bool"
  shows "fun_contracts_well_typed tgtEnv (apply_subst_to_funinfo s info)"
proof -
  let ?n = "length (FI_TmArgs info)"
  let ?info' = "apply_subst_to_funinfo s info"
  have len_s: "length (FI_TmArgs ?info') = ?n" by simp
  have pre: "core_term_type (module_body_env_for tgtEnv (contract_arg_names ?n) ?info')
               Ghost tm' = Some CoreTy_Bool"
    if mem: "tm' \<in> set (FI_Requires ?info')" for tm'
  proof -
    obtain tm where tm_in: "tm \<in> set (FI_Requires info)"
                and tm'_eq: "tm' = apply_subst_to_term s tm"
      using mem by auto
    have typed: "core_term_type (module_body_env_for srcEnv (contract_arg_names ?n) info)
                   Ghost tm = Some CoreTy_Bool"
      using ctr tm_in unfolding fun_contracts_well_typed_def contracts_typed_in_def by blast
    show ?thesis
      unfolding tm'_eq by (rule step) (simp_all add: typed)
  qed
  have post: "core_term_type (module_body_env_for tgtEnv (contract_post_names ?n)
                                (post_funinfo ?info'))
                Ghost tm' = Some CoreTy_Bool"
    if mem: "tm' \<in> set (FI_Ensures ?info')" for tm'
  proof -
    obtain tm where tm_in: "tm \<in> set (FI_Ensures info)"
                and tm'_eq: "tm' = apply_subst_to_term s tm"
      using mem by auto
    have typed: "core_term_type (module_body_env_for srcEnv (contract_post_names ?n)
                                   (post_funinfo info))
                   Ghost tm = Some CoreTy_Bool"
      using ctr tm_in unfolding fun_contracts_well_typed_def contracts_typed_in_def by blast
    have "core_term_type (module_body_env_for tgtEnv (contract_post_names ?n)
                            (apply_subst_to_funinfo s (post_funinfo info)))
            Ghost (apply_subst_to_term s tm) = Some CoreTy_Bool"
      by (rule step) (simp_all add: typed)
    then show ?thesis
      unfolding tm'_eq apply_subst_to_funinfo_post_funinfo .
  qed
  show ?thesis
    unfolding fun_contracts_well_typed_def contracts_typed_in_def len_s
    using pre post by blast
qed

end
