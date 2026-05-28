theory CoreTypeSubstInternal
  imports CoreTypeSubstTerm
begin

(* Internal proof-engine for apply_subst_to_term_preserves_typing.

   This file's only purpose is to help prove apply_subst_to_term_preserves_typing 
   (in CoreTypeSubst.thy). The heavyweight lemma here is core_term_type_subst_callee_env; 
   the corollary in CoreTypeSubst.thy is the degenerate (caller = callee) case.

   The caller/callee asymmetry of apply_subst_to_callee_env dates from a
   previous design where statement-level type soundness substituted the
   caller's type arguments into the callee's body before re-typechecking it.
   That approach was replaced by runtime tyvar bindings on the interpreter
   state (IS_TyArgs). The machinery survives here because the term-level
   corollary is still needed by the elaborator. *)


(* ========================================================================== *)
(* Substitution on callee environments                                         *)
(* ========================================================================== *)

(* At a function call site, the callee body was originally typechecked in an
   environment with the callee's own type variables (FI_TyArgs) in scope. To
   re-typecheck the body in the caller's context we must:
   - Replace the callee's type variables with the caller's (which act as the
     binders for any unresolved type variables in the substitution's range).
   - Substitute through TE_LocalVars (parameter types), so the formal
     parameters get caller-instantiated types.
   - Substitute through TE_ReturnType, so the return-type check inside Return
     statements sees the caller-instantiated return type.
   The other env fields (globals, datatypes, ctors, functions, ghost-locals,
   const-names, function-ghost flag) are unchanged: they were inherited from
   the caller's env in the first place.
*)
definition apply_subst_to_callee_env ::
    "TypeSubst \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv" where
  "apply_subst_to_callee_env subst callerEnv calleeEnv =
    calleeEnv \<lparr>
      TE_LocalVars := fmmap (apply_subst subst) (TE_LocalVars calleeEnv),
      TE_TypeVars := TE_TypeVars callerEnv,
      TE_RuntimeTypeVars := TE_RuntimeTypeVars callerEnv,
      TE_ReturnType := apply_subst subst (TE_ReturnType calleeEnv),
      TE_ProofGoal := map_option (apply_subst_to_term subst) (TE_ProofGoal calleeEnv)
    \<rparr>"

(* Field projections - these come up everywhere downstream. *)
lemma apply_subst_to_callee_env_TE_LocalVars [simp]:
  "TE_LocalVars (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = fmmap (apply_subst subst) (TE_LocalVars calleeEnv)"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_GlobalVars [simp]:
  "TE_GlobalVars (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_GlobalVars calleeEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_GhostLocals [simp]:
  "TE_GhostLocals (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_GhostLocals calleeEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_GhostGlobals [simp]:
  "TE_GhostGlobals (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_GhostGlobals calleeEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_ConstLocals [simp]:
  "TE_ConstLocals (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_ConstLocals calleeEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_TypeVars [simp]:
  "TE_TypeVars (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_TypeVars callerEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_RuntimeTypeVars [simp]:
  "TE_RuntimeTypeVars (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_RuntimeTypeVars callerEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_ReturnType [simp]:
  "TE_ReturnType (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = apply_subst subst (TE_ReturnType calleeEnv)"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_FunctionGhost [simp]:
  "TE_FunctionGhost (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_FunctionGhost calleeEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_Functions [simp]:
  "TE_Functions (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_Functions calleeEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_Datatypes [simp]:
  "TE_Datatypes (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_Datatypes calleeEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_DataCtors [simp]:
  "TE_DataCtors (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_DataCtors calleeEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_DataCtorsByType [simp]:
  "TE_DataCtorsByType (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_DataCtorsByType calleeEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_GhostDatatypes [simp]:
  "TE_GhostDatatypes (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_GhostDatatypes calleeEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_ProofGoal [simp]:
  "TE_ProofGoal (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = map_option (apply_subst_to_term subst) (TE_ProofGoal calleeEnv)"
  by (simp add: apply_subst_to_callee_env_def)

(* If a pattern is compatible with a type in calleeEnv, it is compatible with
   the substituted type in the substituted env. TE_DataCtors is inherited from
   calleeEnv, so pattern_compatible (which only depends on the env via
   TE_DataCtors) reduces to the no-env-substitution case. *)
lemma pattern_compatible_apply_subst_callee_env:
  assumes "tyenv_well_formed calleeEnv"
      and "pattern_compatible calleeEnv p ty"
  shows "pattern_compatible (apply_subst_to_callee_env subst callerEnv calleeEnv) p
                            (apply_subst subst ty)"
proof -
  have dc_eq: "TE_DataCtors (apply_subst_to_callee_env subst callerEnv calleeEnv)
                 = TE_DataCtors calleeEnv"
    by simp
  have "pattern_compatible calleeEnv p (apply_subst subst ty)"
    using pattern_compatible_apply_subst[OF assms] .
  thus ?thesis
    using pattern_compatible_cong_env[OF dc_eq] by simp
qed

(* Substituting types in TE_LocalVars preserves the *keys*, so writability is
   preserved (it only looks at TE_LocalVars's domain and TE_ConstLocals). *)
lemma tyenv_var_writable_apply_subst_to_callee_env [simp]:
  "tyenv_var_writable (apply_subst_to_callee_env subst callerEnv calleeEnv) name
     = tyenv_var_writable calleeEnv name"
  by (simp add: tyenv_var_writable_def apply_subst_to_callee_env_def)

(* Ghost-ness of a variable is determined by TE_LocalVars's domain (not types),
   TE_GhostLocals, and TE_GhostGlobals. All preserved under substitution. *)
lemma tyenv_var_ghost_apply_subst_to_callee_env [simp]:
  "tyenv_var_ghost (apply_subst_to_callee_env subst callerEnv calleeEnv) name
     = tyenv_var_ghost calleeEnv name"
  unfolding tyenv_var_ghost_def
  by (cases "fmlookup (TE_LocalVars calleeEnv) name") simp_all

(* Variable lookup: for locals, the type gets substituted; for globals, the type
   is unchanged (and globally closed in a well-formed env, see the Var case). *)
lemma tyenv_lookup_var_apply_subst_to_callee_env:
  "tyenv_lookup_var (apply_subst_to_callee_env subst callerEnv calleeEnv) name
     = (case fmlookup (TE_LocalVars calleeEnv) name of
          Some ty \<Rightarrow> Some (apply_subst subst ty)
        | None \<Rightarrow> fmlookup (TE_GlobalVars calleeEnv) name)"
  unfolding tyenv_lookup_var_def apply_subst_to_callee_env_def
  by (cases "fmlookup (TE_LocalVars calleeEnv) name") simp_all

lemma is_writable_lvalue_apply_subst_to_callee_env [simp]:
  "is_writable_lvalue (apply_subst_to_callee_env subst callerEnv calleeEnv) tm
     = is_writable_lvalue calleeEnv tm"
  by (induction tm) auto


(* Conditions on a substitution and the caller/callee env relationship that are
   *always* needed for the typing-preservation lemmas: caller and callee agree on
   the global-ish fields, and the substitution maps every callee type variable
   either to a well-kinded type in callerEnv or back to a callerEnv type variable.
   Used by core_term_type_subst_callee_env. *)
definition callee_env_subst_ok ::
    "TypeSubst \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "callee_env_subst_ok subst callerEnv calleeEnv \<equiv>
    \<comment> \<open>Caller and callee agree on the global-ish fields. \<close>
    TE_GlobalVars callerEnv = TE_GlobalVars calleeEnv \<and>
    TE_GhostGlobals callerEnv = TE_GhostGlobals calleeEnv \<and>
    TE_Functions callerEnv = TE_Functions calleeEnv \<and>
    TE_Datatypes callerEnv = TE_Datatypes calleeEnv \<and>
    TE_DataCtors callerEnv = TE_DataCtors calleeEnv \<and>
    TE_DataCtorsByType callerEnv = TE_DataCtorsByType calleeEnv \<and>
    TE_GhostDatatypes callerEnv = TE_GhostDatatypes calleeEnv \<and>
    \<comment> \<open>Every callee type variable is either mapped to a well-kinded type in callerEnv
        or remains in callerEnv's TE_TypeVars. \<close>
    (\<forall>n. n |\<in>| TE_TypeVars calleeEnv \<longrightarrow>
         (case fmlookup subst n of
            Some ty' \<Rightarrow> is_well_kinded callerEnv ty'
          | None \<Rightarrow> n |\<in>| TE_TypeVars callerEnv))"

(* The runtime-tyvar condition is split out separately because it is only needed
   in NotGhost mode. Most consumers will pass it conditionally:
   `mode = NotGhost \<Longrightarrow> callee_env_subst_runtime_ok subst callerEnv calleeEnv`. *)
definition callee_env_subst_runtime_ok ::
    "TypeSubst \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "callee_env_subst_runtime_ok subst callerEnv calleeEnv \<equiv>
    \<forall>n. n |\<in>| TE_RuntimeTypeVars calleeEnv \<longrightarrow>
         (case fmlookup subst n of
            Some ty' \<Rightarrow> is_runtime_type callerEnv ty'
          | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars callerEnv)"


(* Lifting facts: under callee_env_subst_ok, apply_subst preserves well-kindedness
   from calleeEnv to ?be, and runtime-ness similarly. These are direct corollaries
   of apply_subst_preserves_well_kinded / apply_subst_preserves_runtime, but stated
   in terms of ?be so they fit into the well-formedness proof below. *)
lemma apply_subst_preserves_well_kinded_callee:
  assumes "is_well_kinded calleeEnv ty"
      and "callee_env_subst_ok subst callerEnv calleeEnv"
  shows "is_well_kinded (apply_subst_to_callee_env subst callerEnv calleeEnv)
                        (apply_subst subst ty)"
proof (rule apply_subst_preserves_well_kinded[OF assms(1)])
  show "TE_Datatypes (apply_subst_to_callee_env subst callerEnv calleeEnv)
          = TE_Datatypes calleeEnv"
    by simp
next
  fix n assume "n |\<in>| TE_TypeVars calleeEnv"
  with assms(2) show
    "case fmlookup subst n of
        Some ty' \<Rightarrow> is_well_kinded (apply_subst_to_callee_env subst callerEnv calleeEnv) ty'
      | None \<Rightarrow> n |\<in>| TE_TypeVars (apply_subst_to_callee_env subst callerEnv calleeEnv)"
    unfolding callee_env_subst_ok_def
    by (auto split: option.splits intro: is_well_kinded_cong_env[THEN iffD1])
qed

lemma apply_subst_preserves_runtime_callee:
  assumes "is_runtime_type calleeEnv ty"
      and "callee_env_subst_ok subst callerEnv calleeEnv"
      and "callee_env_subst_runtime_ok subst callerEnv calleeEnv"
  shows "is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv)
                         (apply_subst subst ty)"
proof (rule apply_subst_preserves_runtime[OF assms(1)])
  show "TE_GhostDatatypes (apply_subst_to_callee_env subst callerEnv calleeEnv)
          = TE_GhostDatatypes calleeEnv"
    by simp
next
  \<comment> \<open>is_runtime_type only depends on TE_GhostDatatypes and TE_RuntimeTypeVars; on
      ?be both agree with callerEnv (the former by callee_env_subst_ok, the
      latter by definition), so runtime-ness in callerEnv transfers to ?be. \<close>
  have rt_cong: "\<And>ty'. is_runtime_type callerEnv ty'
                       = is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ty'"
    using assms(2)
    by (intro is_runtime_type_cong_env)
       (simp_all add: callee_env_subst_ok_def)
  fix n assume n_in: "n |\<in>| TE_RuntimeTypeVars calleeEnv"
  show
    "case fmlookup subst n of
        Some ty' \<Rightarrow> is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ty'
      | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars (apply_subst_to_callee_env subst callerEnv calleeEnv)"
  proof (cases "fmlookup subst n")
    case None
    with assms(3) n_in have "n |\<in>| TE_RuntimeTypeVars callerEnv"
      unfolding callee_env_subst_runtime_ok_def by auto
    thus ?thesis using None by simp
  next
    case (Some ty')
    with assms(3) n_in have "is_runtime_type callerEnv ty'"
      unfolding callee_env_subst_runtime_ok_def by auto
    with rt_cong have "is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ty'"
      by simp
    thus ?thesis using Some by simp
  qed
qed


(* Well-formedness of the callee env after substitution. This is the lemma case 6
   of the type soundness theorem uses to discharge wf_bodyEnv: given that the
   pre-substitution body env is well-formed and the substitution conditions hold,
   the substituted env is also well-formed. *)
lemma apply_subst_to_callee_env_well_formed:
  assumes wf_callee: "tyenv_well_formed calleeEnv"
      and wf_caller: "tyenv_well_formed callerEnv"
      and ok: "callee_env_subst_ok subst callerEnv calleeEnv"
      and ok_rt: "callee_env_subst_runtime_ok subst callerEnv calleeEnv"
      and ret_wk: "is_well_kinded callerEnv (apply_subst subst (TE_ReturnType calleeEnv))"
      and ret_rt: "TE_FunctionGhost calleeEnv = NotGhost \<Longrightarrow>
                   is_runtime_type callerEnv (apply_subst subst (TE_ReturnType calleeEnv))"
  shows "tyenv_well_formed (apply_subst_to_callee_env subst callerEnv calleeEnv)"
proof -
  let ?be = "apply_subst_to_callee_env subst callerEnv calleeEnv"

  \<comment> \<open>Field-agreement facts pulled out for repeated use. \<close>
  from ok have
    gv_eq: "TE_GlobalVars callerEnv = TE_GlobalVars calleeEnv" and
    gg_eq: "TE_GhostGlobals callerEnv = TE_GhostGlobals calleeEnv" and
    fns_eq: "TE_Functions callerEnv = TE_Functions calleeEnv" and
    dt_eq: "TE_Datatypes callerEnv = TE_Datatypes calleeEnv" and
    dc_eq: "TE_DataCtors callerEnv = TE_DataCtors calleeEnv" and
    dcbt_eq: "TE_DataCtorsByType callerEnv = TE_DataCtorsByType calleeEnv" and
    gd_eq: "TE_GhostDatatypes callerEnv = TE_GhostDatatypes calleeEnv"
    unfolding callee_env_subst_ok_def by auto

  \<comment> \<open>Congruences relating ?be to callerEnv on cleared envs (for the global
      conjuncts of vars_well_kinded and vars_runtime). \<close>
  have wk_cleared_caller_eq:
    "\<And>ty. is_well_kinded (?be \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty
        = is_well_kinded (callerEnv \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
    by (rule is_well_kinded_cong_env) (simp_all add: dt_eq)
  have rt_cleared_caller_eq:
    "\<And>ty. is_runtime_type (?be \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty
        = is_runtime_type (callerEnv \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
    by (rule is_runtime_type_cong_env) (simp_all add: gd_eq)

  \<comment> \<open>Congruences for the inner-override conjuncts (payloads, fun types, etc.). \<close>
  have wk_scope_eq:
    "\<And>tvs t. is_well_kinded (?be \<lparr> TE_TypeVars := tvs \<rparr>) t
            = is_well_kinded (calleeEnv \<lparr> TE_TypeVars := tvs \<rparr>) t"
    by (rule is_well_kinded_cong_env) (simp_all add: apply_subst_to_callee_env_def)
  have rt_scope_eq:
    "\<And>tvs rtvs t.
       is_runtime_type (?be \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t
       = is_runtime_type (calleeEnv \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t"
    by (rule is_runtime_type_cong_env) (simp_all add: apply_subst_to_callee_env_def)

  \<comment> \<open>Extract conjuncts of well-formedness from both envs. \<close>
  from wf_callee have
    callee_vars_wk: "tyenv_vars_well_kinded calleeEnv" and
    callee_vars_rt: "tyenv_vars_runtime calleeEnv" and
    callee_ghost_subset: "tyenv_ghost_vars_subset calleeEnv" and
    callee_ctors_cons: "tyenv_ctors_consistent calleeEnv" and
    callee_payloads_wk: "tyenv_payloads_well_kinded calleeEnv" and
    callee_ctor_tyvars_distinct: "tyenv_ctor_tyvars_distinct calleeEnv" and
    callee_ctors_by_type: "tyenv_ctors_by_type_consistent calleeEnv" and
    callee_fun_types_wk: "tyenv_fun_types_well_kinded calleeEnv" and
    callee_fun_tyvars_distinct: "tyenv_fun_tyvars_distinct calleeEnv" and
    callee_fun_param_names_distinct: "tyenv_fun_param_names_distinct calleeEnv" and
    callee_fun_ghost: "tyenv_fun_ghost_constraint calleeEnv" and
    callee_nonghost_payloads: "tyenv_nonghost_payloads_runtime calleeEnv" and
    callee_ghost_dt_subset: "tyenv_ghost_datatypes_subset calleeEnv" and
    callee_rt_subset: "tyenv_runtime_tyvars_subset calleeEnv"
    unfolding tyenv_well_formed_def by auto

  from wf_caller have
    caller_vars_wk: "tyenv_vars_well_kinded callerEnv" and
    caller_rt_subset: "tyenv_runtime_tyvars_subset callerEnv"
    unfolding tyenv_well_formed_def by auto

  \<comment> \<open>(1) tyenv_vars_well_kinded ?be \<close>
  have c1: "tyenv_vars_well_kinded ?be"
    unfolding tyenv_vars_well_kinded_def
  proof (intro conjI allI impI)
    fix name ty
    assume "fmlookup (TE_LocalVars ?be) name = Some ty"
    then obtain origTy where
      orig_lk: "fmlookup (TE_LocalVars calleeEnv) name = Some origTy" and
      ty_eq: "ty = apply_subst subst origTy"
      by (auto split: option.splits)
    from callee_vars_wk orig_lk have "is_well_kinded calleeEnv origTy"
      unfolding tyenv_vars_well_kinded_def by blast
    from apply_subst_preserves_well_kinded_callee[OF this ok]
    show "is_well_kinded ?be ty" using ty_eq by simp
  next
    fix name ty
    assume gv: "fmlookup (TE_GlobalVars ?be) name = Some ty"
    \<comment> \<open>?be inherits TE_GlobalVars from calleeEnv, which agrees with callerEnv. \<close>
    hence "fmlookup (TE_GlobalVars callerEnv) name = Some ty"
      using gv_eq by simp
    with caller_vars_wk
    have "is_well_kinded (callerEnv \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
      unfolding tyenv_vars_well_kinded_def by blast
    thus "is_well_kinded (?be \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
      using wk_cleared_caller_eq by simp
  qed

  \<comment> \<open>(2) tyenv_vars_runtime ?be \<close>
  from wf_caller have caller_vars_rt: "tyenv_vars_runtime callerEnv"
    unfolding tyenv_well_formed_def by auto
  have c2: "tyenv_vars_runtime ?be"
    unfolding tyenv_vars_runtime_def
  proof (intro conjI allI impI)
    fix name ty
    assume A: "fmlookup (TE_LocalVars ?be) name = Some ty
               \<and> name |\<notin>| TE_GhostLocals ?be"
    from A have lv: "fmlookup (TE_LocalVars ?be) name = Some ty"
      and ng: "name |\<notin>| TE_GhostLocals ?be" by simp_all
    from lv obtain origTy where
      orig_lk: "fmlookup (TE_LocalVars calleeEnv) name = Some origTy" and
      ty_eq: "ty = apply_subst subst origTy"
      by (auto split: option.splits)
    from ng have ng_callee: "name |\<notin>| TE_GhostLocals calleeEnv" by simp
    from callee_vars_rt orig_lk ng_callee
    have "is_runtime_type calleeEnv origTy"
      unfolding tyenv_vars_runtime_def by blast
    from apply_subst_preserves_runtime_callee[OF this ok ok_rt]
    show "is_runtime_type ?be ty" using ty_eq by simp
  next
    fix name ty
    assume A: "fmlookup (TE_GlobalVars ?be) name = Some ty
               \<and> name |\<notin>| TE_GhostGlobals ?be"
    from A have gv: "fmlookup (TE_GlobalVars ?be) name = Some ty"
      and ng: "name |\<notin>| TE_GhostGlobals ?be" by simp_all
    from gv have gv_caller: "fmlookup (TE_GlobalVars callerEnv) name = Some ty"
      using gv_eq by simp
    from ng have ng_caller: "name |\<notin>| TE_GhostGlobals callerEnv"
      using gg_eq by simp
    from caller_vars_rt gv_caller ng_caller
    have "is_runtime_type (callerEnv \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
      unfolding tyenv_vars_runtime_def by blast
    thus "is_runtime_type (?be \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
      using rt_cleared_caller_eq by simp
  qed

  \<comment> \<open>(3) tyenv_ghost_vars_subset ?be: TE_GhostLocals subset of TE_LocalVars dom (preserved
       under fmmap), TE_GhostGlobals subset of TE_GlobalVars (inherited). \<close>
  have c3: "tyenv_ghost_vars_subset ?be"
    using callee_ghost_subset
    unfolding tyenv_ghost_vars_subset_def
    by (simp add: apply_subst_to_callee_env_def)

  \<comment> \<open>(4) tyenv_return_type_well_kinded ?be: TE_ReturnType ?be = apply_subst subst (TE_ReturnType calleeEnv);
       given as a premise. But the predicate checks well-kindedness in ?be, not callerEnv.
       Use congruence to bridge. \<close>
  have wk_be_caller_eq:
    "\<And>ty. is_well_kinded ?be ty = is_well_kinded callerEnv ty"
    by (rule is_well_kinded_cong_env) (simp_all add: dt_eq[symmetric])
  have c4: "tyenv_return_type_well_kinded ?be"
    unfolding tyenv_return_type_well_kinded_def
    using ret_wk wk_be_caller_eq by simp

  \<comment> \<open>(5) tyenv_ctors_consistent ?be: TE_DataCtors and TE_Datatypes inherited from calleeEnv. \<close>
  have c5: "tyenv_ctors_consistent ?be"
    using callee_ctors_cons unfolding tyenv_ctors_consistent_def
    by (simp add: apply_subst_to_callee_env_def)

  \<comment> \<open>(6) tyenv_payloads_well_kinded ?be: inner override on TE_TypeVars; TE_DataCtors,
       TE_Datatypes inherited. \<close>
  have c6: "tyenv_payloads_well_kinded ?be"
    unfolding tyenv_payloads_well_kinded_def
  proof (intro allI impI)
    fix ctorName dtName tyVars payload
    assume "fmlookup (TE_DataCtors ?be) ctorName = Some (dtName, tyVars, payload)"
    hence ctor_lk: "fmlookup (TE_DataCtors calleeEnv) ctorName = Some (dtName, tyVars, payload)"
      by (simp add: apply_subst_to_callee_env_def)
    with callee_payloads_wk
    have "is_well_kinded (calleeEnv \<lparr> TE_TypeVars := fset_of_list tyVars \<rparr>) payload"
      unfolding tyenv_payloads_well_kinded_def by blast
    thus "is_well_kinded (?be \<lparr> TE_TypeVars := fset_of_list tyVars \<rparr>) payload"
      using wk_scope_eq by simp
  qed

  \<comment> \<open>(7) tyenv_ctor_tyvars_distinct ?be: TE_DataCtors inherited. \<close>
  have c7: "tyenv_ctor_tyvars_distinct ?be"
    using callee_ctor_tyvars_distinct unfolding tyenv_ctor_tyvars_distinct_def
    by (simp add: apply_subst_to_callee_env_def)

  \<comment> \<open>(8) tyenv_ctors_by_type_consistent ?be: TE_DataCtorsByType, TE_DataCtors inherited. \<close>
  have c8: "tyenv_ctors_by_type_consistent ?be"
    using callee_ctors_by_type unfolding tyenv_ctors_by_type_consistent_def
    by (simp add: apply_subst_to_callee_env_def)

  \<comment> \<open>(9) tyenv_fun_types_well_kinded ?be: inner override; TE_Functions, TE_Datatypes inherited. \<close>
  have c9: "tyenv_fun_types_well_kinded ?be"
    unfolding tyenv_fun_types_well_kinded_def
  proof (intro allI impI)
    fix funName info
    assume "fmlookup (TE_Functions ?be) funName = Some info"
    hence info_lk: "fmlookup (TE_Functions calleeEnv) funName = Some info"
      by (simp add: apply_subst_to_callee_env_def)
    with callee_fun_types_wk have
      args_wk: "\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs info).
                  is_well_kinded (calleeEnv \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info) \<rparr>) ty"
      and ret_wk_inner: "is_well_kinded (calleeEnv \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info) \<rparr>)
                                  (FI_ReturnType info)"
      unfolding tyenv_fun_types_well_kinded_def by auto
    show "(\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs info).
              is_well_kinded (?be \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info) \<rparr>) ty) \<and>
          is_well_kinded (?be \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info) \<rparr>) (FI_ReturnType info)"
      using args_wk ret_wk_inner wk_scope_eq by simp
  qed

  \<comment> \<open>(10) tyenv_fun_tyvars_distinct ?be: TE_Functions inherited. \<close>
  have c10: "tyenv_fun_tyvars_distinct ?be"
    using callee_fun_tyvars_distinct unfolding tyenv_fun_tyvars_distinct_def
    by (simp add: apply_subst_to_callee_env_def)

  \<comment> \<open>(11) tyenv_fun_param_names_distinct ?be: TE_Functions inherited. \<close>
  have c11: "tyenv_fun_param_names_distinct ?be"
    using callee_fun_param_names_distinct unfolding tyenv_fun_param_names_distinct_def
    by (simp add: apply_subst_to_callee_env_def)

  \<comment> \<open>(12) tyenv_fun_ghost_constraint ?be: inner override; TE_Functions inherited. \<close>
  have c12: "tyenv_fun_ghost_constraint ?be"
    unfolding tyenv_fun_ghost_constraint_def Let_def
  proof (intro allI impI, elim conjE)
    fix funName info
    assume info_lk_be: "fmlookup (TE_Functions ?be) funName = Some info"
       and ng_info: "FI_Ghost info = NotGhost"
    from info_lk_be have info_lk: "fmlookup (TE_Functions calleeEnv) funName = Some info"
      by (simp add: apply_subst_to_callee_env_def)
    from callee_fun_ghost info_lk ng_info have
      "(\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs info).
            is_runtime_type (calleeEnv \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info),
                                          TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info) \<rparr>) ty) \<and>
       is_runtime_type (calleeEnv \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info),
                                     TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info) \<rparr>)
                       (FI_ReturnType info)"
      unfolding tyenv_fun_ghost_constraint_def Let_def by auto
    thus "(\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs info).
              is_runtime_type (?be \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info),
                                      TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info) \<rparr>) ty) \<and>
           is_runtime_type (?be \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info),
                                   TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info) \<rparr>)
                           (FI_ReturnType info)"
      using rt_scope_eq by simp
  qed

  \<comment> \<open>(13) tyenv_nonghost_payloads_runtime ?be: inner override; TE_DataCtors,
        TE_GhostDatatypes inherited. \<close>
  have c13: "tyenv_nonghost_payloads_runtime ?be"
    unfolding tyenv_nonghost_payloads_runtime_def
  proof (intro allI impI)
    fix ctorName dtName tyVars payload
    assume ctor_lk_be: "fmlookup (TE_DataCtors ?be) ctorName = Some (dtName, tyVars, payload)"
       and ng_dt: "dtName |\<notin>| TE_GhostDatatypes ?be"
    from ctor_lk_be have ctor_lk: "fmlookup (TE_DataCtors calleeEnv) ctorName = Some (dtName, tyVars, payload)"
      by (simp add: apply_subst_to_callee_env_def)
    from ng_dt have ng_dt_callee: "dtName |\<notin>| TE_GhostDatatypes calleeEnv"
      by (simp add: apply_subst_to_callee_env_def)
    from callee_nonghost_payloads ctor_lk ng_dt_callee
    have "is_runtime_type (calleeEnv \<lparr> TE_TypeVars := fset_of_list tyVars,
                                        TE_RuntimeTypeVars := fset_of_list tyVars \<rparr>) payload"
      unfolding tyenv_nonghost_payloads_runtime_def by blast
    thus "is_runtime_type (?be \<lparr> TE_TypeVars := fset_of_list tyVars,
                                  TE_RuntimeTypeVars := fset_of_list tyVars \<rparr>) payload"
      using rt_scope_eq by simp
  qed

  \<comment> \<open>(14) tyenv_ghost_datatypes_subset ?be: TE_GhostDatatypes, TE_Datatypes inherited. \<close>
  have c14: "tyenv_ghost_datatypes_subset ?be"
    using callee_ghost_dt_subset unfolding tyenv_ghost_datatypes_subset_def
    by (simp add: apply_subst_to_callee_env_def)

  \<comment> \<open>(15) tyenv_runtime_tyvars_subset ?be: TE_RuntimeTypeVars and TE_TypeVars
       both come from callerEnv, so this reduces to the caller's subset clause. \<close>
  have c15: "tyenv_runtime_tyvars_subset ?be"
    using caller_rt_subset unfolding tyenv_runtime_tyvars_subset_def by simp

  from c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
  show ?thesis unfolding tyenv_well_formed_def by simp
qed


(* ========================================================================== *)
(* Shared setup for FunctionCall substitution proofs                           *)
(* ========================================================================== *)

(* The "preamble" facts that both pure-call and impure-call substitution proofs
   need once they've looked up a function. Given a successful lookup plus the
   ambient subst-ok hypotheses, this bundles the facts about the substituted
   type arguments (well-kindedness, runtime-ness in NotGhost mode, length), the
   distinctness of the function's type parameters, the containment of FI_TmArgs
   / FI_ReturnType type variables in FI_TyArgs, and the substitution-composition
   equation for the return type. Both callers destructure this with obtain. *)
lemma function_call_subst_setup:
  assumes fn_lookup: "fmlookup (TE_Functions calleeEnv) fnName = Some funInfo"
      and len_tyArgs: "length tyArgs = length (FI_TyArgs funInfo)"
      and tyArgs_wk: "list_all (is_well_kinded calleeEnv) tyArgs"
      and ng_tyArgs: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type calleeEnv) tyArgs"
      and wf: "tyenv_well_formed calleeEnv"
      and ok: "callee_env_subst_ok subst callerEnv calleeEnv"
      and subst_wk: "\<forall>ty' \<in> fmran' subst. is_well_kinded callerEnv ty'"
      and ok_rt: "ghost = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst callerEnv calleeEnv"
  shows "fmlookup (TE_Functions (apply_subst_to_callee_env subst callerEnv calleeEnv)) fnName
           = Some funInfo"
    and "list_all (is_well_kinded (apply_subst_to_callee_env subst callerEnv calleeEnv))
                  (map (apply_subst subst) tyArgs)"
    and "ghost = NotGhost \<longrightarrow>
         list_all (is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv))
                  (map (apply_subst subst) tyArgs)"
    and "length (map (apply_subst subst) tyArgs) = length (FI_TyArgs funInfo)"
    and "distinct (FI_TyArgs funInfo)"
    and "\<forall>t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo).
           type_tyvars t \<subseteq> set (FI_TyArgs funInfo)"
    and "type_tyvars (FI_ReturnType funInfo) \<subseteq> set (FI_TyArgs funInfo)"
    and "apply_subst subst (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                                         (FI_ReturnType funInfo))
           = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) (map (apply_subst subst) tyArgs)))
                         (FI_ReturnType funInfo)"
proof -
  show "fmlookup (TE_Functions (apply_subst_to_callee_env subst callerEnv calleeEnv)) fnName
          = Some funInfo"
    using fn_lookup by simp

  show "list_all (is_well_kinded (apply_subst_to_callee_env subst callerEnv calleeEnv))
                 (map (apply_subst subst) tyArgs)"
    using tyArgs_wk
    by (induction tyArgs)
       (auto intro: apply_subst_preserves_well_kinded_callee[OF _ ok])

  show "ghost = NotGhost \<longrightarrow>
        list_all (is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv))
                 (map (apply_subst subst) tyArgs)"
  proof
    assume ng: "ghost = NotGhost"
    with ng_tyArgs have rt: "list_all (is_runtime_type calleeEnv) tyArgs" by simp
    from ng ok_rt have ok_rt': "callee_env_subst_runtime_ok subst callerEnv calleeEnv" by simp
    show "list_all (is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv))
                   (map (apply_subst subst) tyArgs)"
      using rt
      by (induction tyArgs)
         (auto intro: apply_subst_preserves_runtime_callee[OF _ ok ok_rt'])
  qed

  show "length (map (apply_subst subst) tyArgs) = length (FI_TyArgs funInfo)"
    using len_tyArgs by simp

  show tyArgs_distinct: "distinct (FI_TyArgs funInfo)"
    using wf fn_lookup
    unfolding tyenv_well_formed_def tyenv_fun_tyvars_distinct_def by blast

  have fi_args_wk:
    "\<forall>t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo).
       is_well_kinded (calleeEnv \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) t"
    using wf fn_lookup
    unfolding tyenv_well_formed_def tyenv_fun_types_well_kinded_def by blast
  have fi_ret_wk:
    "is_well_kinded (calleeEnv \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) (FI_ReturnType funInfo)"
    using wf fn_lookup
    unfolding tyenv_well_formed_def tyenv_fun_types_well_kinded_def by blast

  show fi_args_tyvars:
    "\<forall>t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo). type_tyvars t \<subseteq> set (FI_TyArgs funInfo)"
  proof
    fix t assume "t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)"
    with fi_args_wk
    have "is_well_kinded (calleeEnv \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) t"
      by blast
    from is_well_kinded_type_tyvars_subset[OF this]
    show "type_tyvars t \<subseteq> set (FI_TyArgs funInfo)"
      by (simp add: fset_of_list.rep_eq)
  qed

  show fi_ret_tyvars: "type_tyvars (FI_ReturnType funInfo) \<subseteq> set (FI_TyArgs funInfo)"
    using is_well_kinded_type_tyvars_subset[OF fi_ret_wk]
    by (simp add: fset_of_list.rep_eq)

  show "apply_subst subst (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                                        (FI_ReturnType funInfo))
          = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) (map (apply_subst subst) tyArgs)))
                        (FI_ReturnType funInfo)"
    using apply_subst_compose_zip[OF len_tyArgs[symmetric] fi_ret_tyvars tyArgs_distinct, of subst]
    by simp
qed


(* ========================================================================== *)
(* Term typing under callee-env substitution                                   *)
(* ========================================================================== *)

(* If a term typechecks in calleeEnv, then it typechecks (with substituted result
   type) in the substituted callee env. The term itself is not substituted; only
   the env changes.

   Conditions:
   - calleeEnv is well-formed (so variable lookups land on well-kinded types, etc.)
   - callee_env_subst_ok: caller and callee envs agree on the global-ish fields,
     and the substitution covers callee type variables with caller-typed values
   - The substitution's range is well-kinded in callerEnv (needed for any embedded
     types like Cast targets, Quantifier binders, function tyArgs, etc., to remain
     well-kinded after substitution)
   - In NotGhost mode, the substitution's range is also runtime in callerEnv
     (needed for the runtime-type checks at non-ghost positions). *)
lemma core_term_type_subst_callee_env:
  assumes "core_term_type calleeEnv ghost tm = Some ty"
      and "tyenv_well_formed calleeEnv"
      and "callee_env_subst_ok subst callerEnv calleeEnv"
      and "\<forall>ty' \<in> fmran' subst. is_well_kinded callerEnv ty'"
      and "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type callerEnv ty')"
      and "ghost = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst callerEnv calleeEnv"
  shows "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                        (apply_subst_to_term subst tm)
           = Some (apply_subst subst ty)"
using assms proof (induction tm arbitrary: ty ghost calleeEnv)
  case (CoreTm_LitBool b)
  \<comment> \<open>LitBool always has type Bool, which is closed under substitution. \<close>
  then show ?case by simp
next
  case (CoreTm_LitInt i)
  \<comment> \<open>LitInt has a finite-int type, which is closed under substitution. \<close>
  then show ?case by (auto split: option.splits)
next
  case (CoreTm_LitArray elemTy tms)
  \<comment> \<open>LitArray: each element must typecheck to elemTy. After substitution, each
      element typechecks to (apply_subst subst elemTy), and the result type is
      Array (apply_subst subst elemTy) [Fixed (length tms)]. \<close>
  from CoreTm_LitArray.prems(1) have
    elemTy_wk: "is_well_kinded calleeEnv elemTy" and
    elemTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type calleeEnv elemTy" and
    tms_typed: "list_all (\<lambda>tm. core_term_type calleeEnv ghost tm = Some elemTy) tms" and
    len_ok: "int_in_range (int_range Unsigned IntBits_64) (int (length tms))" and
    ty_eq: "ty = CoreTy_Array elemTy [CoreDim_Fixed (int (length tms))]"
    by (auto split: if_splits)

  have elemTy_wk_subst: "is_well_kinded (apply_subst_to_callee_env subst callerEnv calleeEnv)
                                        (apply_subst subst elemTy)"
    using apply_subst_preserves_well_kinded_callee[OF elemTy_wk CoreTm_LitArray.prems(3)] .
  have elemTy_rt_subst:
    "ghost = NotGhost \<longrightarrow>
       is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv)
                       (apply_subst subst elemTy)"
  proof
    assume ng: "ghost = NotGhost"
    with elemTy_rt have rt: "is_runtime_type calleeEnv elemTy" by simp
    from ng CoreTm_LitArray.prems(6) have ok_rt: "callee_env_subst_runtime_ok subst callerEnv calleeEnv"
      by simp
    from apply_subst_preserves_runtime_callee[OF rt CoreTm_LitArray.prems(3) ok_rt]
    show "is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv)
                          (apply_subst subst elemTy)" .
  qed

  \<comment> \<open>Each element typechecks to (apply_subst subst elemTy) after substitution. \<close>
  have tms_subst:
    "list_all (\<lambda>tm. core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost tm
                      = Some (apply_subst subst elemTy))
              (map (apply_subst_to_term subst) tms)"
  proof (unfold list_all_iff, intro ballI)
    fix tm' assume "tm' \<in> set (map (apply_subst_to_term subst) tms)"
    then obtain tm where tm_in: "tm \<in> set tms" and tm'_eq: "tm' = apply_subst_to_term subst tm"
      by auto
    from tms_typed tm_in have tm_typed: "core_term_type calleeEnv ghost tm = Some elemTy"
      by (simp add: list_all_iff)
    from CoreTm_LitArray.IH[OF tm_in tm_typed CoreTm_LitArray.prems(2,3,4,5,6)]
    show "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost tm'
            = Some (apply_subst subst elemTy)"
      using tm'_eq by simp
  qed

  have len_eq: "length (map (apply_subst_to_term subst) tms) = length tms" by simp

  show ?case
    using elemTy_wk_subst elemTy_rt_subst tms_subst len_eq len_ok ty_eq by simp
next
  case (CoreTm_Var name)
  \<comment> \<open>Var: looks up the variable in locals (substituted types) or globals (closed
      types). apply_subst_to_term is the identity on Var (no type substitution).
      For local vars, the substituted type is apply_subst subst (original type);
      for global vars, globals are closed so apply_subst subst ty = ty. \<close>
  from CoreTm_Var.prems(1) obtain lookupTy where
    lookup: "tyenv_lookup_var calleeEnv name = Some lookupTy" and
    not_ghost_ok: "ghost = NotGhost \<longrightarrow> \<not> tyenv_var_ghost calleeEnv name" and
    ty_eq: "ty = lookupTy"
    by (auto split: option.splits if_splits)
  show ?case
  proof (cases "fmlookup (TE_LocalVars calleeEnv) name")
    case (Some localTy)
    with lookup have ty_local: "lookupTy = localTy"
      by (simp add: tyenv_lookup_var_def)
    from Some ty_local have
      lookup_subst: "tyenv_lookup_var (apply_subst_to_callee_env subst callerEnv calleeEnv) name
                       = Some (apply_subst subst localTy)"
      by (simp add: tyenv_lookup_var_apply_subst_to_callee_env)
    show ?thesis
      using lookup_subst ty_eq ty_local not_ghost_ok by simp
  next
    case None
    with lookup have gv: "fmlookup (TE_GlobalVars calleeEnv) name = Some lookupTy"
      by (simp add: tyenv_lookup_var_def)
    \<comment> \<open>Global's type is closed (well-formed env), so apply_subst is identity. \<close>
    from gv CoreTm_Var.prems(2) have wk_cleared:
      "is_well_kinded (calleeEnv \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) lookupTy"
      unfolding tyenv_well_formed_def tyenv_vars_well_kinded_def by blast
    have tyvars_empty: "type_tyvars lookupTy = {}"
      using is_well_kinded_type_tyvars_subset[OF wk_cleared] by simp
    have ty_closed: "apply_subst subst lookupTy = lookupTy"
      using tyvars_empty by (simp add: apply_subst_disjoint_id)
    from None have
      lookup_subst: "tyenv_lookup_var (apply_subst_to_callee_env subst callerEnv calleeEnv) name
                       = fmlookup (TE_GlobalVars calleeEnv) name"
      by (simp add: tyenv_lookup_var_apply_subst_to_callee_env)
    show ?thesis
      using lookup_subst gv ty_eq ty_closed not_ghost_ok by simp
  qed
next
  case (CoreTm_Cast targetTy operand)
  \<comment> \<open>Cast: operand has some integer type; result is targetTy (also integer).
      Substitution leaves integer types unchanged, so after substitution the
      operand's type is still an integer (the same one), the target is still
      an integer (and unchanged). \<close>
  from CoreTm_Cast.prems(1) obtain operandTy where
    op_typed: "core_term_type calleeEnv ghost operand = Some operandTy" and
    op_int: "is_integer_type operandTy" and
    tgt_int: "is_integer_type targetTy" and
    tgt_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type calleeEnv targetTy" and
    ty_eq: "ty = targetTy"
    by (auto split: option.splits if_splits)
  from CoreTm_Cast.IH[OF op_typed CoreTm_Cast.prems(2,3,4,5,6)]
  have op_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                    (apply_subst_to_term subst operand)
       = Some (apply_subst subst operandTy)" .
  have op_ty_eq: "apply_subst subst operandTy = operandTy"
    using op_int is_integer_type_apply_subst by simp
  have tgt_ty_eq: "apply_subst subst targetTy = targetTy"
    using tgt_int is_integer_type_apply_subst by simp
  \<comment> \<open>The substituted targetTy, for the runtime check, stays runtime since it's
      closed (integer types have no type variables). \<close>
  have tgt_rt_subst:
    "ghost = NotGhost \<longrightarrow>
       is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv)
                       (apply_subst subst targetTy)"
  proof
    assume ng: "ghost = NotGhost"
    with tgt_rt have rt: "is_runtime_type calleeEnv targetTy" by simp
    from ng CoreTm_Cast.prems(6) have ok_rt: "callee_env_subst_runtime_ok subst callerEnv calleeEnv"
      by simp
    from apply_subst_preserves_runtime_callee[OF rt CoreTm_Cast.prems(3) ok_rt]
    show "is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv)
                          (apply_subst subst targetTy)" .
  qed
  show ?case
    using op_subst op_int op_ty_eq tgt_int tgt_ty_eq tgt_rt_subst ty_eq
    by auto
next
  case (CoreTm_Unop op operand)
  \<comment> \<open>Unop: operand has some type, result depends on the operator. For Negate the
      operand is signed numeric, for Complement finite integer, for Not boolean.
      All of these are closed types; substitution leaves them unchanged. \<close>
  from CoreTm_Unop.prems(1) obtain operandTy where
    op_typed: "core_term_type calleeEnv ghost operand = Some operandTy"
    by (auto split: option.splits)
  from CoreTm_Unop.IH[OF op_typed CoreTm_Unop.prems(2,3,4,5,6)]
  have op_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                    (apply_subst_to_term subst operand)
       = Some (apply_subst subst operandTy)" .
  show ?case
  proof (cases op)
    case CoreUnop_Negate
    with CoreTm_Unop.prems(1) op_typed have
      op_sn: "is_signed_numeric_type operandTy" and
      ty_eq: "ty = operandTy"
      by (auto split: if_splits)
    have "apply_subst subst operandTy = operandTy"
      using op_sn is_signed_numeric_type_apply_subst by simp
    with op_subst op_sn ty_eq CoreUnop_Negate show ?thesis by simp
  next
    case CoreUnop_Complement
    with CoreTm_Unop.prems(1) op_typed have
      op_fi: "is_finite_integer_type operandTy" and
      ty_eq: "ty = operandTy"
      by (auto split: if_splits)
    have "apply_subst subst operandTy = operandTy"
      using op_fi is_finite_integer_type_apply_subst by simp
    with op_subst op_fi ty_eq CoreUnop_Complement show ?thesis by simp
  next
    case CoreUnop_Not
    with CoreTm_Unop.prems(1) op_typed have
      op_bool: "operandTy = CoreTy_Bool" and
      ty_eq: "ty = CoreTy_Bool"
      by (auto split: if_splits)
    with op_subst CoreUnop_Not show ?thesis by simp
  qed
next
  case (CoreTm_Binop op lhs rhs)
  \<comment> \<open>Binop: lhs and rhs have the same type. Split by operator category. For
      arithmetic/modulo/bitwise/shift/ordering/logical, the type is a closed
      concrete type so substitution is the identity. For eq/neq the result type
      is always Bool; the operand type may be arbitrary in Ghost mode, but both
      operands still have the same (substituted) type after substitution. \<close>
  from CoreTm_Binop.prems(1) obtain lhsTy rhsTy where
    lhs_typed: "core_term_type calleeEnv ghost lhs = Some lhsTy" and
    rhs_typed: "core_term_type calleeEnv ghost rhs = Some rhsTy"
    by (auto split: option.splits)
  from CoreTm_Binop.IH(1)[OF lhs_typed CoreTm_Binop.prems(2,3,4,5,6)]
  have lhs_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                    (apply_subst_to_term subst lhs)
       = Some (apply_subst subst lhsTy)" .
  from CoreTm_Binop.IH(2)[OF rhs_typed CoreTm_Binop.prems(2,3,4,5,6)]
  have rhs_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                    (apply_subst_to_term subst rhs)
       = Some (apply_subst subst rhsTy)" .
  from CoreTm_Binop.prems(1) lhs_typed rhs_typed have tys_eq: "lhsTy = rhsTy"
    by (auto split: if_splits)

  from binop_category_exhaustive[of op] consider
    "is_arithmetic_binop op" | "is_modulo_binop op" | "is_bitwise_binop op"
    | "is_shift_binop op" | "is_ordering_binop op" | "is_eq_neq_binop op"
    | "is_logical_binop op"
    by blast
  thus ?case
  proof cases
    case 1  \<comment> \<open>arithmetic: requires numeric, result is operand type\<close>
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      num: "is_numeric_type lhsTy" and ty_eq: "ty = lhsTy"
      by (auto dest: binop_categories_disjoint split: if_splits)
    have ty_closed: "apply_subst subst lhsTy = lhsTy"
      using num is_numeric_type_apply_subst by simp
    show ?thesis
      using 1 lhs_subst rhs_subst tys_eq ty_eq ty_closed num
      by (auto dest: binop_categories_disjoint)
  next
    case 2  \<comment> \<open>modulo: requires integer\<close>
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      int: "is_integer_type lhsTy" and ty_eq: "ty = lhsTy"
      by (auto dest: binop_categories_disjoint split: if_splits)
    have ty_closed: "apply_subst subst lhsTy = lhsTy"
      using int is_integer_type_apply_subst by simp
    show ?thesis
      using 2 lhs_subst rhs_subst tys_eq ty_eq ty_closed int
      by (auto dest: binop_categories_disjoint)
  next
    case 3  \<comment> \<open>bitwise: requires finite integer\<close>
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      fi: "is_finite_integer_type lhsTy" and ty_eq: "ty = lhsTy"
      by (auto dest: binop_categories_disjoint split: if_splits)
    have ty_closed: "apply_subst subst lhsTy = lhsTy"
      using fi is_finite_integer_type_apply_subst by simp
    show ?thesis
      using 3 lhs_subst rhs_subst tys_eq ty_eq ty_closed fi
      by (auto dest: binop_categories_disjoint)
  next
    case 4  \<comment> \<open>shift: requires finite integer\<close>
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      fi: "is_finite_integer_type lhsTy" and ty_eq: "ty = lhsTy"
      by (auto dest: binop_categories_disjoint split: if_splits)
    have ty_closed: "apply_subst subst lhsTy = lhsTy"
      using fi is_finite_integer_type_apply_subst by simp
    show ?thesis
      using 4 lhs_subst rhs_subst tys_eq ty_eq ty_closed fi
      by (auto dest: binop_categories_disjoint)
  next
    case 5  \<comment> \<open>ordering: requires numeric, result is Bool\<close>
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      num: "is_numeric_type lhsTy" and ty_eq: "ty = CoreTy_Bool"
      by (auto dest: binop_categories_disjoint split: if_splits)
    have ty_closed: "apply_subst subst lhsTy = lhsTy"
      using num is_numeric_type_apply_subst by simp
    show ?thesis
      using 5 lhs_subst rhs_subst tys_eq ty_eq ty_closed num
      by (auto dest: binop_categories_disjoint)
  next
    case 6  \<comment> \<open>eq/neq: any same-type operands (in Ghost) or bool/numeric, result Bool\<close>
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      ty_eq: "ty = CoreTy_Bool" and
      typing_ok: "ghost = Ghost \<or> lhsTy = CoreTy_Bool \<or> is_numeric_type lhsTy"
      by (auto dest: binop_categories_disjoint split: if_splits)
    show ?thesis
      using 6 lhs_subst rhs_subst tys_eq ty_eq typing_ok
            is_numeric_type_apply_subst
      by (auto dest: binop_categories_disjoint split: if_splits)
  next
    case 7  \<comment> \<open>logical: requires Bool\<close>
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      bool_eq: "lhsTy = CoreTy_Bool" and ty_eq: "ty = CoreTy_Bool"
      by (auto dest: binop_categories_disjoint split: if_splits)
    show ?thesis
      using 7 lhs_subst rhs_subst tys_eq ty_eq bool_eq
      by (auto dest: binop_categories_disjoint)
  qed
next
  case (CoreTm_Let var rhs body)
  \<comment> \<open>Let: rhs gets typechecked in calleeEnv; body in the env extended with
      (var, rhsTy). We apply the rhs IH against calleeEnv, then the body IH
      against the extended env. The substituted extended env equals the env
      extension of the substituted env. \<close>
  from CoreTm_Let.prems(1) obtain rhsTy where
    rhs_typed: "core_term_type calleeEnv ghost rhs = Some rhsTy" and
    body_typed: "core_term_type
                   (calleeEnv \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars calleeEnv),
                                TE_GhostLocals := (if ghost = Ghost
                                                  then finsert var (TE_GhostLocals calleeEnv)
                                                  else fminus (TE_GhostLocals calleeEnv) {|var|}),
                                TE_ConstLocals := finsert var (TE_ConstLocals calleeEnv) \<rparr>)
                   ghost body = Some ty"
    by (auto split: option.splits simp: Let_def)

  let ?env_ext = "calleeEnv \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars calleeEnv),
                              TE_GhostLocals := (if ghost = Ghost
                                                then finsert var (TE_GhostLocals calleeEnv)
                                                else fminus (TE_GhostLocals calleeEnv) {|var|}),
                              TE_ConstLocals := finsert var (TE_ConstLocals calleeEnv) \<rparr>"

  \<comment> \<open>RHS IH gives the substituted rhs has the substituted rhsTy. \<close>
  from CoreTm_Let.IH(1)[OF rhs_typed CoreTm_Let.prems(2,3,4,5,6)]
  have rhs_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                    (apply_subst_to_term subst rhs)
       = Some (apply_subst subst rhsTy)" .

  \<comment> \<open>The new local's type is well-kinded (and runtime if ghost = NotGhost) by
      core_term_type's wellformedness preservation. \<close>
  have rhsTy_wk: "is_well_kinded calleeEnv rhsTy"
    using core_term_type_well_kinded[OF rhs_typed CoreTm_Let.prems(2)] .
  have rhsTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type calleeEnv rhsTy"
  proof
    assume ng: "ghost = NotGhost"
    with rhs_typed have "core_term_type calleeEnv NotGhost rhs = Some rhsTy" by simp
    from core_term_type_notghost_runtime[OF this CoreTm_Let.prems(2)]
    show "is_runtime_type calleeEnv rhsTy" .
  qed

  have wf_ext: "tyenv_well_formed ?env_ext"
  proof (cases ghost)
    case NotGhost
    from rhsTy_rt NotGhost have rt: "is_runtime_type calleeEnv rhsTy" by simp
    from tyenv_well_formed_add_var[OF CoreTm_Let.prems(2) rhsTy_wk rt]
    have wf':
      "tyenv_well_formed
         (calleeEnv \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars calleeEnv),
                      TE_GhostLocals := fminus (TE_GhostLocals calleeEnv) {|var|} \<rparr>)" .
    from tyenv_well_formed_TE_ConstLocals_irrelevant[OF wf',
            of "finsert var (TE_ConstLocals calleeEnv)"]
    have "tyenv_well_formed
            (calleeEnv \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars calleeEnv),
                         TE_GhostLocals := fminus (TE_GhostLocals calleeEnv) {|var|} \<rparr>
                       \<lparr> TE_ConstLocals := finsert var (TE_ConstLocals calleeEnv) \<rparr>)" .
    with NotGhost show ?thesis by simp
  next
    case Ghost
    from tyenv_well_formed_add_ghost_var[OF CoreTm_Let.prems(2) rhsTy_wk]
    have wf':
      "tyenv_well_formed
         (calleeEnv \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars calleeEnv),
                      TE_GhostLocals := finsert var (TE_GhostLocals calleeEnv) \<rparr>)" .
    from tyenv_well_formed_TE_ConstLocals_irrelevant[OF wf',
            of "finsert var (TE_ConstLocals calleeEnv)"]
    have "tyenv_well_formed
            (calleeEnv \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars calleeEnv),
                         TE_GhostLocals := finsert var (TE_GhostLocals calleeEnv) \<rparr>
                       \<lparr> TE_ConstLocals := finsert var (TE_ConstLocals calleeEnv) \<rparr>)" .
    with Ghost show ?thesis by simp
  qed

  \<comment> \<open>callee_env_subst_ok ?env_ext: same as for calleeEnv since we only changed
      TE_LocalVars / TE_GhostLocals / TE_ConstLocals, none of which appear in
      callee_env_subst_ok. \<close>
  have ok_ext: "callee_env_subst_ok subst callerEnv ?env_ext"
    using CoreTm_Let.prems(3)
    unfolding callee_env_subst_ok_def by simp

  have ok_rt_ext: "ghost = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst callerEnv ?env_ext"
    using CoreTm_Let.prems(6)
    unfolding callee_env_subst_runtime_ok_def by simp

  from CoreTm_Let.IH(2)[OF body_typed wf_ext ok_ext CoreTm_Let.prems(4) CoreTm_Let.prems(5) ok_rt_ext]
  have body_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv ?env_ext) ghost
                    (apply_subst_to_term subst body)
       = Some (apply_subst subst ty)" .

  \<comment> \<open>The substituted extended env equals the extended substituted env. \<close>
  have ext_subst_eq:
    "apply_subst_to_callee_env subst callerEnv ?env_ext
       = (apply_subst_to_callee_env subst callerEnv calleeEnv) \<lparr>
            TE_LocalVars := fmupd var (apply_subst subst rhsTy)
                              (TE_LocalVars (apply_subst_to_callee_env subst callerEnv calleeEnv)),
            TE_GhostLocals := (if ghost = Ghost
                              then finsert var (TE_GhostLocals (apply_subst_to_callee_env subst callerEnv calleeEnv))
                              else fminus (TE_GhostLocals (apply_subst_to_callee_env subst callerEnv calleeEnv))
                                          {|var|}),
            TE_ConstLocals := finsert var (TE_ConstLocals (apply_subst_to_callee_env subst callerEnv calleeEnv)) \<rparr>"
    unfolding apply_subst_to_callee_env_def by (simp add: fmmap_fmupd)

  show ?case
    using rhs_subst body_subst ext_subst_eq by (simp add: Let_def)
next
  case (CoreTm_Quantifier quant var varTy body)
  \<comment> \<open>Quantifier: ghost-only. Body typechecks in env extended with (var, varTy)
      where varTy is well-kinded. Result is Bool. \<close>
  show ?case
  proof (cases ghost)
    case NotGhost
    with CoreTm_Quantifier.prems(1) show ?thesis by simp
  next
    case Ghost
    with CoreTm_Quantifier.prems(1) have
      varTy_wk: "is_well_kinded calleeEnv varTy" and
      body_typed: "core_term_type
                     (calleeEnv \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars calleeEnv),
                                  TE_GhostLocals := finsert var (TE_GhostLocals calleeEnv) \<rparr>)
                     Ghost body = Some CoreTy_Bool" and
      ty_eq: "ty = CoreTy_Bool"
      by (auto split: option.splits CoreType.splits if_splits)

    let ?env_ext = "calleeEnv \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars calleeEnv),
                                TE_GhostLocals := finsert var (TE_GhostLocals calleeEnv) \<rparr>"

    \<comment> \<open>well-formedness of ?env_ext via tyenv_well_formed_add_ghost_var \<close>
    from tyenv_well_formed_add_ghost_var[OF CoreTm_Quantifier.prems(2) varTy_wk]
    have wf_ext: "tyenv_well_formed ?env_ext" .

    \<comment> \<open>callee_env_subst_ok ?env_ext: only TE_LocalVars / TE_GhostLocals changed,
        which callee_env_subst_ok doesn't reference. \<close>
    have ok_ext: "callee_env_subst_ok subst callerEnv ?env_ext"
      using CoreTm_Quantifier.prems(3)
      unfolding callee_env_subst_ok_def by simp

    \<comment> \<open>Substituted varTy is well-kinded in the substituted env. \<close>
    have varTy_wk_subst:
      "is_well_kinded (apply_subst_to_callee_env subst callerEnv calleeEnv)
                      (apply_subst subst varTy)"
      using apply_subst_preserves_well_kinded_callee[OF varTy_wk CoreTm_Quantifier.prems(3)] .

    \<comment> \<open>Body IH (in Ghost mode, so both runtime preconditions are vacuous). \<close>
    have body_rt_premise:
      "Ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type callerEnv ty')"
      by simp
    have body_rt_ok_premise:
      "Ghost = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst callerEnv ?env_ext"
      by simp
    from CoreTm_Quantifier.IH[OF body_typed wf_ext ok_ext CoreTm_Quantifier.prems(4)
                                  body_rt_premise body_rt_ok_premise]
    have body_subst:
      "core_term_type (apply_subst_to_callee_env subst callerEnv ?env_ext) Ghost
                      (apply_subst_to_term subst body)
         = Some (apply_subst subst CoreTy_Bool)" .

    \<comment> \<open>The substituted ?env_ext equals the substituted env extended with
        (var, apply_subst subst varTy). \<close>
    have ext_subst_eq:
      "apply_subst_to_callee_env subst callerEnv ?env_ext
         = (apply_subst_to_callee_env subst callerEnv calleeEnv) \<lparr>
              TE_LocalVars := fmupd var (apply_subst subst varTy)
                                (TE_LocalVars (apply_subst_to_callee_env subst callerEnv calleeEnv)),
              TE_GhostLocals := finsert var (TE_GhostLocals (apply_subst_to_callee_env subst callerEnv calleeEnv)) \<rparr>"
      unfolding apply_subst_to_callee_env_def by (simp add: fmmap_fmupd)

    show ?thesis
      using body_subst varTy_wk_subst ext_subst_eq Ghost ty_eq by simp
  qed
next
  case (CoreTm_FunctionCall fnName tyArgs tmArgs)
  \<comment> \<open>FunctionCall: the typechecker builds an inner substitution mapping the
      callee's type parameters (FI_TyArgs) to the call-site type arguments (tyArgs),
      and applies it to the callee's argument and return types. After our outer
      substitution, the tyArgs become substituted; the inner substitution then
      uses the substituted tyArgs. Substitution composition (apply_subst_compose_zip)
      lets us conclude that the result type matches. \<close>
  from CoreTm_FunctionCall.prems(1) obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions calleeEnv) fnName = Some funInfo" and
    len_tyArgs: "length tyArgs = length (FI_TyArgs funInfo)" and
    tyArgs_wk: "list_all (is_well_kinded calleeEnv) tyArgs" and
    not_ghost_cond: "\<not> (ghost = NotGhost
                       \<and> (\<not> list_all (is_runtime_type calleeEnv) tyArgs
                          \<or> FI_Ghost funInfo = Ghost))" and
    all_var: "list_all (\<lambda>(_, _, vor). vor = Var) (FI_TmArgs funInfo)" and
    not_impure: "\<not> FI_Impure funInfo" and
    len_tmArgs: "length tmArgs = length (FI_TmArgs funInfo)" and
    args_check: "list_all2 (\<lambda>tm expectedTy.
                    case core_term_type calleeEnv ghost tm of
                      None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
                  tmArgs (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                              (FI_TmArgs funInfo))" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo)"
    by (auto simp: Let_def split: option.splits if_splits)
  have ng_tyArgs: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type calleeEnv) tyArgs"
    using not_ghost_cond by blast
  have ng_fn: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost"
    using not_ghost_cond by blast

  let ?be = "apply_subst_to_callee_env subst callerEnv calleeEnv"
  let ?subst_tyArgs = "map (apply_subst subst) tyArgs"
  let ?innerSubst = "fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)"
  let ?subst_innerSubst = "fmap_of_list (zip (FI_TyArgs funInfo) ?subst_tyArgs)"

  \<comment> \<open>Bundled setup facts from the shared helper. \<close>
  note call_setup = function_call_subst_setup[OF fn_lookup len_tyArgs tyArgs_wk ng_tyArgs
                                                 CoreTm_FunctionCall.prems(2,3,4,6)]
  note fn_lookup_subst   = call_setup(1)
  note tyArgs_wk_subst   = call_setup(2)
  note tyArgs_rt_subst   = call_setup(3)
  note len_tyArgs_subst  = call_setup(4)
  note tyArgs_distinct   = call_setup(5)
  note fi_args_tyvars    = call_setup(6)
  note fi_ret_tyvars     = call_setup(7)
  note ret_compose       = call_setup(8)

  have len_tmArgs_eq: "length tmArgs = length (FI_TmArgs funInfo)" using len_tmArgs .

  \<comment> \<open>Each tmArg's IH lifts to the substituted version. The expected type after
      substitution is apply_subst subst (apply_subst ?innerSubst (FI_TmArgs[i].type)),
      which by composition equals apply_subst ?subst_innerSubst (FI_TmArgs[i].type). \<close>
  have args_check_subst:
    "list_all2 (\<lambda>tm expectedTy.
                  case core_term_type ?be ghost tm of
                    None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
              (map (apply_subst_to_term subst) tmArgs)
              (map (\<lambda>(_, ty, _). apply_subst ?subst_innerSubst ty) (FI_TmArgs funInfo))"
  proof -
    \<comment> \<open>The original list_all2 says, for each tmArg, the term typechecks to the
        expected substituted-arg-type. The IH on each tmArg gives us the substituted
        version, which has the substituted-substituted type. Composition equates
        that to the substituted-with-composed-tyArgs type. \<close>
    have len_eq:
      "length tmArgs = length (map (\<lambda>(_, ty, _). apply_subst ?innerSubst ty) (FI_TmArgs funInfo))"
      using len_tmArgs by simp
    show ?thesis
    proof (rule list_all2_all_nthI)
      show "length (map (apply_subst_to_term subst) tmArgs)
              = length (map (\<lambda>(_, ty, _). apply_subst ?subst_innerSubst ty) (FI_TmArgs funInfo))"
        using len_tmArgs by simp
    next
      fix i assume i_bound: "i < length (map (apply_subst_to_term subst) tmArgs)"
      hence i_bound': "i < length tmArgs" by simp
      hence i_bound_args: "i < length (FI_TmArgs funInfo)" using len_tmArgs by simp
      \<comment> \<open>From args_check, the i-th tmArg typechecks to the i-th expected (inner-sub'd) type. \<close>
      from args_check have args_nth_raw:
        "case core_term_type calleeEnv ghost (tmArgs ! i) of
           None \<Rightarrow> False
         | Some actualTy \<Rightarrow>
             actualTy = map (\<lambda>(_, ty, _). apply_subst ?innerSubst ty) (FI_TmArgs funInfo) ! i"
        using i_bound' len_tmArgs
        by (simp add: list_all2_conv_all_nth)
      have args_nth:
        "case core_term_type calleeEnv ghost (tmArgs ! i) of
           None \<Rightarrow> False
         | Some actualTy \<Rightarrow> actualTy = (case FI_TmArgs funInfo ! i of
              (_, ty, _) \<Rightarrow> apply_subst ?innerSubst ty)"
        using args_nth_raw i_bound_args
        by (metis nth_map)
      then obtain actualTy where
        actual_typed: "core_term_type calleeEnv ghost (tmArgs ! i) = Some actualTy" and
        actual_eq: "actualTy = (case FI_TmArgs funInfo ! i of
                                (_, ty, _) \<Rightarrow> apply_subst ?innerSubst ty)"
        by (auto split: option.splits)
      \<comment> \<open>Apply the IH to this tmArg. \<close>
      have tmArg_in: "tmArgs ! i \<in> set tmArgs" using i_bound' by simp
      from CoreTm_FunctionCall.IH[OF tmArg_in actual_typed
                                     CoreTm_FunctionCall.prems(2,3,4,5,6)]
      have ih_result:
        "core_term_type ?be ghost (apply_subst_to_term subst (tmArgs ! i))
           = Some (apply_subst subst actualTy)" .
      \<comment> \<open>The substituted actual type equals the substituted-with-composed
          version of the i-th FI_TmArgs type. \<close>
      obtain n ti vor where fi_arg_eq: "FI_TmArgs funInfo ! i = (n, ti, vor)"
        by (cases "FI_TmArgs funInfo ! i") auto
      from actual_eq fi_arg_eq have actual_eq2: "actualTy = apply_subst ?innerSubst ti" by simp
      \<comment> \<open>ti's type variables are in FI_TyArgs (from fi_args_tyvars). \<close>
      have ti_in: "ti \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)"
        using i_bound_args fi_arg_eq
        by (force simp: image_iff in_set_conv_nth)
      with fi_args_tyvars have ti_tyvars: "type_tyvars ti \<subseteq> set (FI_TyArgs funInfo)" by blast
      have actual_compose:
        "apply_subst subst actualTy = apply_subst ?subst_innerSubst ti"
        unfolding actual_eq2
        using apply_subst_compose_zip[OF len_tyArgs[symmetric] ti_tyvars tyArgs_distinct, of subst]
        by simp
      from ih_result actual_compose have ih_result':
        "core_term_type ?be ghost (apply_subst_to_term subst (tmArgs ! i))
           = Some (apply_subst ?subst_innerSubst ti)" by simp
      show "case core_term_type ?be ghost (map (apply_subst_to_term subst) tmArgs ! i) of
              None \<Rightarrow> False
            | Some actualTy \<Rightarrow> actualTy = map (\<lambda>(_, ty, _). apply_subst ?subst_innerSubst ty)
                                              (FI_TmArgs funInfo) ! i"
        using ih_result' i_bound' i_bound_args fi_arg_eq
        by simp
    qed
  qed

  show ?case
    using fn_lookup_subst len_tyArgs_subst tyArgs_wk_subst tyArgs_rt_subst ng_fn
          all_var not_impure len_tmArgs_eq args_check_subst ty_eq ret_compose
    by (auto simp: Let_def)
next
  case (CoreTm_VariantCtor ctorName tyArgs payload)
  \<comment> \<open>VariantCtor: looks up the constructor; tyArgs are well-kinded; in NotGhost
      tyArgs are runtime and the datatype is non-ghost; payload typechecks to
      apply_subst (zip tyvars tyArgs) payloadTy; result is Datatype dtName tyArgs.

      After substitution: tyArgs become substituted tyArgs (well-kinded/runtime
      via apply_subst_preserves_*_callee), payload's IH lifts, the inner
      substitution composes via apply_subst_compose_zip. \<close>
  from CoreTm_VariantCtor.prems(1) obtain dtName tyvars payloadTy where
    ctor_lookup: "fmlookup (TE_DataCtors calleeEnv) ctorName = Some (dtName, tyvars, payloadTy)" and
    len_eq: "length tyArgs = length tyvars" and
    tyArgs_wk: "list_all (is_well_kinded calleeEnv) tyArgs" and
    ng_constraint: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type calleeEnv) tyArgs
                                          \<and> dtName |\<notin>| TE_GhostDatatypes calleeEnv" and
    payload_typed: "core_term_type calleeEnv ghost payload
                      = Some (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)" and
    ty_eq: "ty = CoreTy_Datatype dtName tyArgs"
    by (auto split: option.splits if_splits prod.splits)

  let ?be = "apply_subst_to_callee_env subst callerEnv calleeEnv"
  let ?subst_tyArgs = "map (apply_subst subst) tyArgs"

  \<comment> \<open>Constructor lookup unchanged in substituted env. \<close>
  have ctor_lookup_subst:
    "fmlookup (TE_DataCtors ?be) ctorName = Some (dtName, tyvars, payloadTy)"
    using ctor_lookup by simp

  \<comment> \<open>Substituted tyArgs are well-kinded in ?be. \<close>
  have tyArgs_wk_subst: "list_all (is_well_kinded ?be) ?subst_tyArgs"
    using tyArgs_wk
    by (induction tyArgs)
       (auto intro: apply_subst_preserves_well_kinded_callee[OF _ CoreTm_VariantCtor.prems(3)])

  \<comment> \<open>Substituted tyArgs are runtime in ?be (when ghost = NotGhost). \<close>
  have tyArgs_rt_subst:
    "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?be) ?subst_tyArgs"
  proof
    assume ng: "ghost = NotGhost"
    with ng_constraint have rt: "list_all (is_runtime_type calleeEnv) tyArgs" by simp
    from ng CoreTm_VariantCtor.prems(6) have ok_rt:
      "callee_env_subst_runtime_ok subst callerEnv calleeEnv" by simp
    show "list_all (is_runtime_type ?be) ?subst_tyArgs"
      using rt
      by (induction tyArgs)
         (auto intro: apply_subst_preserves_runtime_callee[OF _ CoreTm_VariantCtor.prems(3) ok_rt])
  qed

  \<comment> \<open>The datatype is non-ghost (when ghost = NotGhost); ?be inherits TE_GhostDatatypes
      from calleeEnv so the same. \<close>
  have ng_dt_subst:
    "ghost = NotGhost \<longrightarrow> dtName |\<notin>| TE_GhostDatatypes ?be"
    using ng_constraint by simp

  \<comment> \<open>Payload IH gives the substituted payload typechecks to substituted result. \<close>
  from CoreTm_VariantCtor.IH[OF payload_typed CoreTm_VariantCtor.prems(2,3,4,5,6)]
  have payload_subst:
    "core_term_type ?be ghost (apply_subst_to_term subst payload)
       = Some (apply_subst subst (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy))" .

  \<comment> \<open>tyvars are distinct (from tyenv_ctor_tyvars_distinct). \<close>
  have tyvars_distinct: "distinct tyvars"
    using CoreTm_VariantCtor.prems(2) ctor_lookup
    unfolding tyenv_well_formed_def tyenv_ctor_tyvars_distinct_def by blast

  \<comment> \<open>payloadTy's type variables are within set tyvars. \<close>
  have payload_wk: "is_well_kinded (calleeEnv \<lparr> TE_TypeVars := fset_of_list tyvars \<rparr>) payloadTy"
    using CoreTm_VariantCtor.prems(2) ctor_lookup
    unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def by blast
  have payload_tyvars: "type_tyvars payloadTy \<subseteq> set tyvars"
    using is_well_kinded_type_tyvars_subset[OF payload_wk]
    by (simp add: fset_of_list.rep_eq)

  \<comment> \<open>Substitution composition for the payload. \<close>
  have payload_compose:
    "apply_subst subst (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)
       = apply_subst (fmap_of_list (zip tyvars ?subst_tyArgs)) payloadTy"
    using apply_subst_compose_zip[OF len_eq[symmetric] payload_tyvars tyvars_distinct, of subst]
    by simp

  have payload_subst_compose:
    "core_term_type ?be ghost (apply_subst_to_term subst payload)
       = Some (apply_subst (fmap_of_list (zip tyvars ?subst_tyArgs)) payloadTy)"
    using payload_subst payload_compose by simp

  have len_eq_subst: "length ?subst_tyArgs = length tyvars" using len_eq by simp

  show ?case
    using ctor_lookup_subst tyArgs_wk_subst tyArgs_rt_subst ng_dt_subst
          payload_subst_compose len_eq_subst ty_eq by simp
next
  case (CoreTm_Record flds)
  \<comment> \<open>Record: each field typechecks; result is a Record type of the field types.
      After substitution, each field's result type is substituted. \<close>
  from CoreTm_Record.prems(1) obtain fieldTys where
    distinct_names: "distinct (map fst flds)" and
    flds_typed: "those (map (\<lambda>(name, tm). core_term_type calleeEnv ghost tm) flds)
                   = Some fieldTys" and
    ty_eq: "ty = CoreTy_Record (zip (map fst flds) fieldTys)"
    by (auto split: option.splits if_splits)

  \<comment> \<open>The IH for CoreTm_Record is per-field: for any pair (n, t) in flds and any
      type ty', if t typechecks to ty', then the substituted t typechecks to the
      substituted ty'. We extract a uniform IH and then induct on flds. \<close>
  have field_IH:
    "\<And>fld ty'. fld \<in> set flds \<Longrightarrow>
       core_term_type calleeEnv ghost (snd fld) = Some ty' \<Longrightarrow>
       core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                      (apply_subst_to_term subst (snd fld))
         = Some (apply_subst subst ty')"
    using CoreTm_Record.IH CoreTm_Record.prems(2,3,4,5,6)
    by (auto simp: snds.simps)

  have len_tys: "length fieldTys = length flds"
    using flds_typed by (induction flds arbitrary: fieldTys) (auto split: option.splits)

  have fields_subst:
    "those (map (\<lambda>(name, tm). core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv)
                                              ghost tm)
                (map (\<lambda>(name, tm). (name, apply_subst_to_term subst tm)) flds))
       = Some (map (apply_subst subst) fieldTys)"
  using flds_typed field_IH
  proof (induction flds arbitrary: fieldTys)
    case Nil
    then show ?case by simp
  next
    case (Cons fld flds')
    obtain name tm where fld_eq: "fld = (name, tm)" by (cases fld)
    from Cons.prems(1) fld_eq obtain hty rest where
      hd_typed: "core_term_type calleeEnv ghost tm = Some hty" and
      rest_typed: "those (map (\<lambda>(n, t). core_term_type calleeEnv ghost t) flds') = Some rest" and
      fieldTys_eq: "fieldTys = hty # rest"
      by (auto split: option.splits)
    from Cons.prems(2)[of fld hty] fld_eq hd_typed
    have hd_subst:
      "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                      (apply_subst_to_term subst tm)
         = Some (apply_subst subst hty)"
      by simp
    have rest_IH:
      "\<And>fld' ty''. fld' \<in> set flds' \<Longrightarrow>
         core_term_type calleeEnv ghost (snd fld') = Some ty'' \<Longrightarrow>
         core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                        (apply_subst_to_term subst (snd fld'))
           = Some (apply_subst subst ty'')"
      using Cons.prems(2) by auto
    from Cons.IH[OF rest_typed rest_IH]
    have rest_subst:
      "those (map (\<lambda>(name, tm). core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv)
                                                ghost tm)
                  (map (\<lambda>(name, tm). (name, apply_subst_to_term subst tm)) flds'))
         = Some (map (apply_subst subst) rest)" .
    show ?case
      using hd_subst rest_subst fld_eq fieldTys_eq by simp
  qed

  have zip_eq:
    "zip (map fst (map (\<lambda>(name, tm). (name, apply_subst_to_term subst tm)) flds))
         (map (apply_subst subst) fieldTys)
     = map (\<lambda>(n, t). (n, apply_subst subst t)) (zip (map fst flds) fieldTys)"
    using len_tys by (induction flds fieldTys rule: list_induct2') auto

  have distinct_names_subst:
    "distinct (map fst (map (\<lambda>(name, tm). (name, apply_subst_to_term subst tm)) flds))"
    using distinct_names by (simp add: comp_def case_prod_beta)
  show ?case
    using fields_subst ty_eq zip_eq distinct_names_subst by simp
next
  case (CoreTm_RecordProj tm fldName)
  \<comment> \<open>RecordProj: inner term has type CoreTy_Record fieldTypes; result is
      the field's type. After substitution, the inner is a Record of substituted
      fields; looking up the field in the substituted list gives the substituted
      type. \<close>
  from CoreTm_RecordProj.prems(1) obtain fieldTypes where
    inner_typed: "core_term_type calleeEnv ghost tm = Some (CoreTy_Record fieldTypes)" and
    fld_lookup: "map_of fieldTypes fldName = Some ty"
    by (auto split: option.splits CoreType.splits)
  from CoreTm_RecordProj.IH[OF inner_typed CoreTm_RecordProj.prems(2,3,4,5,6)]
  have inner_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                    (apply_subst_to_term subst tm)
       = Some (CoreTy_Record (map (\<lambda>(n, t). (n, apply_subst subst t)) fieldTypes))"
    by simp
  have fld_lookup_subst:
    "map_of (map (\<lambda>(n, t). (n, apply_subst subst t)) fieldTypes) fldName
       = Some (apply_subst subst ty)"
    using fld_lookup by (induction fieldTypes) auto
  show ?case
    using inner_subst fld_lookup_subst by simp
next
  case (CoreTm_ArrayProj arr idxTms)
  \<comment> \<open>ArrayProj: inner is Array elemTy dims; idxTms are u64; result is elemTy.
      After substitution, inner is Array (substituted elemTy) dims; result is
      substituted elemTy. \<close>
  from CoreTm_ArrayProj.prems(1) obtain elemTy dims where
    inner_typed: "core_term_type calleeEnv ghost arr = Some (CoreTy_Array elemTy dims)" and
    len_ok: "length idxTms = length dims" and
    idxs_typed: "list_all (\<lambda>tm. core_term_type calleeEnv ghost tm
                          = Some (CoreTy_FiniteInt Unsigned IntBits_64)) idxTms" and
    ty_eq: "ty = elemTy"
    by (auto split: option.splits CoreType.splits if_splits)
  from CoreTm_ArrayProj.IH(1)[OF inner_typed CoreTm_ArrayProj.prems(2,3,4,5,6)]
  have inner_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                    (apply_subst_to_term subst arr)
       = Some (CoreTy_Array (apply_subst subst elemTy) dims)"
    by simp
  \<comment> \<open>Each index term still typechecks to u64 after substitution (u64 is closed). \<close>
  have idxs_subst:
    "list_all (\<lambda>tm. core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost tm
                      = Some (CoreTy_FiniteInt Unsigned IntBits_64))
              (map (apply_subst_to_term subst) idxTms)"
  proof (unfold list_all_iff, intro ballI)
    fix tm' assume "tm' \<in> set (map (apply_subst_to_term subst) idxTms)"
    then obtain tm where tm_in: "tm \<in> set idxTms" and tm'_eq: "tm' = apply_subst_to_term subst tm"
      by auto
    from idxs_typed tm_in have
      tm_typed: "core_term_type calleeEnv ghost tm = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
      by (simp add: list_all_iff)
    from CoreTm_ArrayProj.IH(2)[OF tm_in tm_typed CoreTm_ArrayProj.prems(2,3,4,5,6)]
    show "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost tm'
            = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
      using tm'_eq by simp
  qed
  show ?case
    using inner_subst idxs_subst len_ok ty_eq by simp
next
  case (CoreTm_VariantProj tm ctorName)
  \<comment> \<open>VariantProj: inner term has type Datatype dtName tyArgs; looks up the
      constructor in TE_DataCtors (inherited from calleeEnv); result is the
      substituted payload type (substituting tyvars := tyArgs).

      After outer substitution: inner becomes Datatype dtName (map substitution
      tyArgs). The DataCtors lookup is unchanged (env field inherited). The
      result of the *outer* substitution on the original result type equals the
      inner substitution on the *substituted* tyArgs: this is substitution
      composition / commutativity. \<close>
  from CoreTm_VariantProj.prems(1) obtain dtName tyArgs tyvars payloadTy where
    inner_typed: "core_term_type calleeEnv ghost tm = Some (CoreTy_Datatype dtName tyArgs)" and
    ctor_lookup: "fmlookup (TE_DataCtors calleeEnv) ctorName = Some (dtName, tyvars, payloadTy)" and
    len_eq: "length tyArgs = length tyvars" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy"
    by (auto split: option.splits CoreType.splits if_splits prod.splits)
  from CoreTm_VariantProj.IH[OF inner_typed CoreTm_VariantProj.prems(2,3,4,5,6)]
  have inner_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                    (apply_subst_to_term subst tm)
       = Some (CoreTy_Datatype dtName (map (apply_subst subst) tyArgs))"
    by simp
  have ctor_lookup_subst:
    "fmlookup (TE_DataCtors (apply_subst_to_callee_env subst callerEnv calleeEnv)) ctorName
       = Some (dtName, tyvars, payloadTy)"
    using ctor_lookup by simp
  have len_eq_subst: "length (map (apply_subst subst) tyArgs) = length tyvars"
    using len_eq by simp

  \<comment> \<open>tyvars are distinct (from tyenv_ctor_tyvars_distinct, a wf clause). \<close>
  have tyvars_distinct: "distinct tyvars"
    using CoreTm_VariantProj.prems(2) ctor_lookup
    unfolding tyenv_well_formed_def tyenv_ctor_tyvars_distinct_def by blast

  \<comment> \<open>payloadTy's type variables are within set tyvars (from tyenv_payloads_well_kinded
      via is_well_kinded_type_tyvars_subset). \<close>
  have payload_wk: "is_well_kinded (calleeEnv \<lparr> TE_TypeVars := fset_of_list tyvars \<rparr>) payloadTy"
    using CoreTm_VariantProj.prems(2) ctor_lookup
    unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def by blast
  have payload_tyvars: "type_tyvars payloadTy \<subseteq> set tyvars"
    using is_well_kinded_type_tyvars_subset[OF payload_wk]
    by (simp add: fset_of_list.rep_eq)

  \<comment> \<open>Substitution composition: pushing the outer subst through the inner zip
      substitution gives the same result as composing them. \<close>
  have ty_subst_eq:
    "apply_subst subst ty
       = apply_subst (fmap_of_list (zip tyvars (map (apply_subst subst) tyArgs))) payloadTy"
    unfolding ty_eq
    using apply_subst_compose_zip[OF len_eq[symmetric] payload_tyvars tyvars_distinct, of subst]
    by simp

  show ?case
    using inner_subst ctor_lookup_subst len_eq_subst ty_subst_eq by simp
next
  case (CoreTm_Match scrut arms)
  \<comment> \<open>Match: scrutinee typechecks; pattern compatibility holds;
      all arm bodies have the same type. After substitution, the scrutinee's
      type is substituted, the patterns are unchanged (substitution doesn't touch
      them), and each arm body's IH gives the substituted body type. \<close>
  from CoreTm_Match.prems(1) obtain scrutTy where
    scrut_typed: "core_term_type calleeEnv ghost scrut = Some scrutTy" and
    arms_nonempty: "arms \<noteq> []" and
    pats_compat: "list_all (\<lambda>p. pattern_compatible calleeEnv p scrutTy) (map fst arms)" and
    hd_typed: "core_term_type calleeEnv ghost (snd (hd arms)) = Some ty" and
    rest_typed: "list_all (\<lambda>body. core_term_type calleeEnv ghost body = Some ty)
                          (tl (map snd arms))"
    by (auto simp: Let_def split: option.splits if_splits)

  let ?be = "apply_subst_to_callee_env subst callerEnv calleeEnv"
  let ?subst_arms = "map (\<lambda>(pat, body). (pat, apply_subst_to_term subst body)) arms"

  \<comment> \<open>Scrutinee IH. \<close>
  from CoreTm_Match.IH(1)[OF scrut_typed CoreTm_Match.prems(2,3,4,5,6)]
  have scrut_subst:
    "core_term_type ?be ghost (apply_subst_to_term subst scrut)
       = Some (apply_subst subst scrutTy)" .

  \<comment> \<open>Per-arm IH from the structural induction. The IH gives, for each (pat, body)
      pair in arms, the body's typing-substitution result. \<close>
  have arm_IH:
    "\<And>arm ty'. arm \<in> set arms \<Longrightarrow>
       core_term_type calleeEnv ghost (snd arm) = Some ty' \<Longrightarrow>
       core_term_type ?be ghost (apply_subst_to_term subst (snd arm))
         = Some (apply_subst subst ty')"
    using CoreTm_Match.IH(2) CoreTm_Match.prems(2,3,4,5,6)
    by (auto simp: snds.simps)

  \<comment> \<open>The patterns of arms are unchanged after substitution; we only substitute the bodies. \<close>
  have pats_eq: "map fst ?subst_arms = map fst arms"
    by (induction arms) auto

  \<comment> \<open>Pattern compatibility transfers to the substituted env / type. \<close>
  have pats_compat_subst:
    "list_all (\<lambda>p. pattern_compatible ?be p (apply_subst subst scrutTy)) (map fst ?subst_arms)"
    using pats_compat pats_eq CoreTm_Match.prems(2)
    by (induction arms)
       (auto intro: pattern_compatible_apply_subst_callee_env)

  \<comment> \<open>Head body IH. \<close>
  have hd_in: "hd arms \<in> set arms" using arms_nonempty by auto
  from arm_IH[OF hd_in hd_typed]
  have hd_subst:
    "core_term_type ?be ghost (apply_subst_to_term subst (snd (hd arms)))
       = Some (apply_subst subst ty)" .

  \<comment> \<open>Head of the substituted arms equals the substituted head of arms. \<close>
  have hd_subst_arms_eq:
    "snd (hd ?subst_arms) = apply_subst_to_term subst (snd (hd arms))"
    using arms_nonempty by (cases arms) auto

  \<comment> \<open>Tail bodies: each typechecks to apply_subst subst ty after substitution. \<close>
  have tl_subst:
    "list_all (\<lambda>body. core_term_type ?be ghost body = Some (apply_subst subst ty))
              (tl (map snd ?subst_arms))"
  proof -
    \<comment> \<open>tl (map snd ?subst_arms) = map (apply_subst_to_term subst) (tl (map snd arms)) \<close>
    have tl_eq: "tl (map snd ?subst_arms)
                   = map (apply_subst_to_term subst) (tl (map snd arms))"
      using arms_nonempty by (cases arms) auto
    show ?thesis
      unfolding tl_eq
    proof (unfold list_all_iff, intro ballI)
      fix b' assume "b' \<in> set (map (apply_subst_to_term subst) (tl (map snd arms)))"
      then obtain b where
        b_in: "b \<in> set (tl (map snd arms))" and
        b'_eq: "b' = apply_subst_to_term subst b"
        by auto
      from b_in have b_typed: "core_term_type calleeEnv ghost b = Some ty"
        using rest_typed by (simp add: list_all_iff)
      \<comment> \<open>b is the body of some arm in arms. \<close>
      from b_in arms_nonempty obtain arm where
        arm_in: "arm \<in> set arms" and arm_body: "snd arm = b"
        by (cases arms) auto
      from arm_IH[OF arm_in] b_typed arm_body
      have "core_term_type ?be ghost (apply_subst_to_term subst b)
              = Some (apply_subst subst ty)"
        by simp
      thus "core_term_type ?be ghost b' = Some (apply_subst subst ty)"
        using b'_eq by simp
    qed
  qed

  have arms_nonempty_subst: "?subst_arms \<noteq> []"
    using arms_nonempty by (cases arms) auto

  show ?case
    using scrut_subst arms_nonempty_subst pats_compat_subst
          hd_subst hd_subst_arms_eq tl_subst
    by (auto simp: Let_def)
next
  case (CoreTm_Sizeof tm)
  \<comment> \<open>Sizeof requires the inner term to have an Array type and returns sizeof_type
      of its dims. apply_subst preserves the dims of an Array, and sizeof_type
      produces a closed type. is_lvalue is a syntactic property preserved by
      apply_subst_to_term. \<close>
  from CoreTm_Sizeof.prems(1) obtain elemTy dims where
    inner: "core_term_type calleeEnv ghost tm = Some (CoreTy_Array elemTy dims)" and
    cond_ok: "\<not> (list_ex (\<lambda>d. d = CoreDim_Allocatable) dims \<and> \<not> is_lvalue tm \<and> ghost = NotGhost)" and
    ty_eq: "ty = sizeof_type dims"
    by (auto split: CoreType.splits option.splits if_splits)
  from CoreTm_Sizeof.IH[OF inner CoreTm_Sizeof.prems(2,3,4,5,6)]
  have inner_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                    (apply_subst_to_term subst tm)
       = Some (CoreTy_Array (apply_subst subst elemTy) dims)" by simp
  have lvalue_eq: "is_lvalue (apply_subst_to_term subst tm) = is_lvalue tm" by simp
  show ?case using inner_subst cond_ok ty_eq lvalue_eq by simp
next
  case (CoreTm_Allocated tm)
  \<comment> \<open>Allocated is ghost-only and always returns Bool. The NotGhost equation reduces
      to None, so we must be in Ghost. The inner term must typecheck to something. \<close>
  show ?case
  proof (cases ghost)
    case NotGhost
    with CoreTm_Allocated.prems(1) show ?thesis by simp
  next
    case Ghost
    with CoreTm_Allocated.prems(1) obtain innerTy where
      inner: "core_term_type calleeEnv Ghost tm = Some innerTy" and
      ty_eq: "ty = CoreTy_Bool"
      by (auto split: option.splits)
    from CoreTm_Allocated.IH[OF inner CoreTm_Allocated.prems(2,3,4)]
         CoreTm_Allocated.prems(5) CoreTm_Allocated.prems(6)
    have "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) Ghost
                          (apply_subst_to_term subst tm)
            = Some (apply_subst subst innerTy)" by simp
    with Ghost ty_eq show ?thesis by simp
  qed
next
  case (CoreTm_Old tm)
  \<comment> \<open>Old is a ghost-only pass-through. The NotGhost equation reduces to None,
      so the precondition forces ghost = Ghost. The IH on tm closes the case. \<close>
  show ?case
  proof (cases ghost)
    case NotGhost
    with CoreTm_Old.prems(1) show ?thesis by simp
  next
    case Ghost
    with CoreTm_Old.prems(1) have inner: "core_term_type calleeEnv Ghost tm = Some ty" by simp
    from CoreTm_Old.IH[OF inner CoreTm_Old.prems(2,3,4)]
         CoreTm_Old.prems(5) CoreTm_Old.prems(6)
    have "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) Ghost
                          (apply_subst_to_term subst tm)
            = Some (apply_subst subst ty)" by simp
    with Ghost show ?thesis by simp
  qed
qed


end
