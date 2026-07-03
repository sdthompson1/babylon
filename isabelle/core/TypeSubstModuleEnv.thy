theory TypeSubstModuleEnv
  imports TypeSubstEnv TypeSubstStmt CoreStmtTypecheck
begin

(* The module-level substitution engine.

   Linking resolves a module's abstract types by applying the merged
   substitution to EVERYTHING in the module: the declaration tables
   (TE_GlobalVars / TE_Functions / TE_DataCtors, via apply_subst_to_tyenv),
   the terms and statements, and any scope fields. The existing callee-env
   engine (core_term_type_subst_callee_env, TypeSubstHelpers.thy) does not
   cover this: it keeps the declaration tables EQUAL between caller and
   callee env, and its callee_env_subst_ok forbids substituting the abstract
   types. This file provides the table-substituting analogue:

     if tm typechecks at ty in env, then apply_subst_to_term subst tm
     typechecks at apply_subst subst ty in
     apply_subst_to_module_env subst targetEnv env

   under conditions bundled in module_env_subst_ok: the target env agrees
   with env on the datatype tables, the substitution covers env's type
   variables with types well-kinded in targetEnv (with a split-out runtime
   analogue for NotGhost mode), and - the capture-avoidance condition - the
   bound type parameters of every function signature and data constructor
   avoid the substitution's whole name set (subst_names: domain AND range
   type variables). The latter is exactly what capture_avoiding
   (CoreModule.thy) provides, discharged by a successful link
   (link_modules_capture_avoiding, LinkModules.thy).

   The key algebraic step at call/ctor sites is subst_names_avoid_compose
   (TypeSubst.thy): because the tables are substituted, the typechecker at
   the substituted site computes
     apply_subst (zip vars (map (apply_subst subst) tyArgs))
                 (apply_subst subst sigTy)
   which must equal
     apply_subst subst (apply_subst (zip vars tyArgs) sigTy);
   binder-avoidance of subst_names makes the two substitutions commute with
   no condition on sigTy at all. *)


(* ========================================================================== *)
(* Substitution on module-level environments                                   *)
(* ========================================================================== *)

(* Substitute through every CoreType in the environment (declaration tables,
   locals, return type, proof goal), taking the type-variable fields from
   targetEnv. In the linking application, env is a module-level env whose
   TE_TypeVars are (a superset of) the abstract types being resolved, and
   targetEnv supplies the linked program's remaining type variables.

   TE_LocalVars is substituted (rather than assumed empty) so that the same
   engine serves both global-initializer terms (empty locals) and function
   bodies (parameter locals). *)
definition apply_subst_to_module_env ::
    "TypeSubst \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv" where
  "apply_subst_to_module_env subst targetEnv env =
    env \<lparr>
      TE_LocalVars := fmmap (apply_subst subst) (TE_LocalVars env),
      TE_GlobalVars := fmmap (apply_subst subst) (TE_GlobalVars env),
      TE_TypeVars := TE_TypeVars targetEnv,
      TE_RuntimeTypeVars := TE_RuntimeTypeVars targetEnv,
      TE_AbstractTypes := TE_AbstractTypes targetEnv,
      TE_ReturnType := apply_subst subst (TE_ReturnType env),
      TE_ProofGoal := map_option (apply_subst_to_term subst) (TE_ProofGoal env),
      TE_Functions := fmmap (apply_subst_to_funinfo subst) (TE_Functions env),
      TE_DataCtors := fmmap (apply_subst_to_datactor subst) (TE_DataCtors env)
    \<rparr>"

(* Field projections - these come up everywhere downstream. *)
lemma apply_subst_to_module_env_TE_LocalVars [simp]:
  "TE_LocalVars (apply_subst_to_module_env subst targetEnv env)
     = fmmap (apply_subst subst) (TE_LocalVars env)"
  by (simp add: apply_subst_to_module_env_def)

lemma apply_subst_to_module_env_TE_GlobalVars [simp]:
  "TE_GlobalVars (apply_subst_to_module_env subst targetEnv env)
     = fmmap (apply_subst subst) (TE_GlobalVars env)"
  by (simp add: apply_subst_to_module_env_def)

lemma apply_subst_to_module_env_TE_GhostLocals [simp]:
  "TE_GhostLocals (apply_subst_to_module_env subst targetEnv env)
     = TE_GhostLocals env"
  by (simp add: apply_subst_to_module_env_def)

lemma apply_subst_to_module_env_TE_GhostGlobals [simp]:
  "TE_GhostGlobals (apply_subst_to_module_env subst targetEnv env)
     = TE_GhostGlobals env"
  by (simp add: apply_subst_to_module_env_def)

lemma apply_subst_to_module_env_TE_ConstLocals [simp]:
  "TE_ConstLocals (apply_subst_to_module_env subst targetEnv env)
     = TE_ConstLocals env"
  by (simp add: apply_subst_to_module_env_def)

lemma apply_subst_to_module_env_TE_TypeVars [simp]:
  "TE_TypeVars (apply_subst_to_module_env subst targetEnv env)
     = TE_TypeVars targetEnv"
  by (simp add: apply_subst_to_module_env_def)

lemma apply_subst_to_module_env_TE_RuntimeTypeVars [simp]:
  "TE_RuntimeTypeVars (apply_subst_to_module_env subst targetEnv env)
     = TE_RuntimeTypeVars targetEnv"
  by (simp add: apply_subst_to_module_env_def)

lemma apply_subst_to_module_env_TE_AbstractTypes [simp]:
  "TE_AbstractTypes (apply_subst_to_module_env subst targetEnv env)
     = TE_AbstractTypes targetEnv"
  by (simp add: apply_subst_to_module_env_def)

lemma apply_subst_to_module_env_TE_ReturnType [simp]:
  "TE_ReturnType (apply_subst_to_module_env subst targetEnv env)
     = apply_subst subst (TE_ReturnType env)"
  by (simp add: apply_subst_to_module_env_def)

lemma apply_subst_to_module_env_TE_FunctionGhost [simp]:
  "TE_FunctionGhost (apply_subst_to_module_env subst targetEnv env)
     = TE_FunctionGhost env"
  by (simp add: apply_subst_to_module_env_def)

lemma apply_subst_to_module_env_TE_ProofGoal [simp]:
  "TE_ProofGoal (apply_subst_to_module_env subst targetEnv env)
     = map_option (apply_subst_to_term subst) (TE_ProofGoal env)"
  by (simp add: apply_subst_to_module_env_def)

lemma apply_subst_to_module_env_TE_ProofTopLevel [simp]:
  "TE_ProofTopLevel (apply_subst_to_module_env subst targetEnv env)
     = TE_ProofTopLevel env"
  by (simp add: apply_subst_to_module_env_def)

lemma apply_subst_to_module_env_TE_Functions [simp]:
  "TE_Functions (apply_subst_to_module_env subst targetEnv env)
     = fmmap (apply_subst_to_funinfo subst) (TE_Functions env)"
  by (simp add: apply_subst_to_module_env_def)

lemma apply_subst_to_module_env_TE_Datatypes [simp]:
  "TE_Datatypes (apply_subst_to_module_env subst targetEnv env)
     = TE_Datatypes env"
  by (simp add: apply_subst_to_module_env_def)

lemma apply_subst_to_module_env_TE_DataCtors [simp]:
  "TE_DataCtors (apply_subst_to_module_env subst targetEnv env)
     = fmmap (apply_subst_to_datactor subst) (TE_DataCtors env)"
  by (simp add: apply_subst_to_module_env_def)

lemma apply_subst_to_module_env_TE_DataCtorsByType [simp]:
  "TE_DataCtorsByType (apply_subst_to_module_env subst targetEnv env)
     = TE_DataCtorsByType env"
  by (simp add: apply_subst_to_module_env_def)

lemma apply_subst_to_module_env_TE_GhostDatatypes [simp]:
  "TE_GhostDatatypes (apply_subst_to_module_env subst targetEnv env)
     = TE_GhostDatatypes env"
  by (simp add: apply_subst_to_module_env_def)


(* ========================================================================== *)
(* Variable lookup / writability / ghost-ness under the substituted env       *)
(* ========================================================================== *)

(* Both locals and globals are substituted, so lookup commutes with the
   substitution uniformly (contrast the callee engine, where globals were
   unchanged and had to be shown closed). *)
lemma tyenv_lookup_var_apply_subst_to_module_env:
  "tyenv_lookup_var (apply_subst_to_module_env subst targetEnv env) name
     = map_option (apply_subst subst) (tyenv_lookup_var env name)"
  unfolding tyenv_lookup_var_def
  by (cases "fmlookup (TE_LocalVars env) name") simp_all

(* Substitution preserves the keys of all variable maps, so ghost-ness and
   writability are unchanged. *)
lemma tyenv_var_ghost_apply_subst_to_module_env [simp]:
  "tyenv_var_ghost (apply_subst_to_module_env subst targetEnv env) name
     = tyenv_var_ghost env name"
  unfolding tyenv_var_ghost_def
  by (cases "fmlookup (TE_LocalVars env) name") simp_all

lemma tyenv_var_writable_apply_subst_to_module_env [simp]:
  "tyenv_var_writable (apply_subst_to_module_env subst targetEnv env) name
     = tyenv_var_writable env name"
  by (simp add: tyenv_var_writable_def apply_subst_to_module_env_def)

lemma is_writable_lvalue_apply_subst_to_module_env [simp]:
  "is_writable_lvalue (apply_subst_to_module_env subst targetEnv env) tm
     = is_writable_lvalue env tm"
  by (induction tm) auto


(* ========================================================================== *)
(* Side conditions on the substitution                                        *)
(* ========================================================================== *)

(* Conditions relating the substitution, the target env (which supplies the
   result's type-variable fields), and the env being substituted:
   - targetEnv agrees with env on the datatype tables (which the substitution
     does not change);
   - every type variable of env is either mapped to a type well-kinded in
     targetEnv, or survives as a type variable of targetEnv;
   - capture-avoidance: the bound type parameters of every function signature
     and data constructor avoid the substitution's whole name set (domain and
     range type variables - see subst_names, TypeSubst.thy). *)
definition module_env_subst_ok ::
    "TypeSubst \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "module_env_subst_ok subst targetEnv env \<equiv>
    TE_Datatypes targetEnv = TE_Datatypes env \<and>
    TE_GhostDatatypes targetEnv = TE_GhostDatatypes env \<and>
    (\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow>
         (case fmlookup subst n of
            Some ty' \<Rightarrow> is_well_kinded targetEnv ty'
          | None \<Rightarrow> n |\<in>| TE_TypeVars targetEnv)) \<and>
    (\<forall>funName info.
        fmlookup (TE_Functions env) funName = Some info \<longrightarrow>
        subst_names subst |\<inter>| fset_of_list (FI_TyArgs info) = {||}) \<and>
    (\<forall>ctorName dtName tyVars payload.
        fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload) \<longrightarrow>
        subst_names subst |\<inter>| fset_of_list tyVars = {||})"

(* The runtime-tyvar condition is split out separately because it is only
   needed in NotGhost mode. Consumers pass it conditionally:
   `ghost = NotGhost \<Longrightarrow> module_env_subst_runtime_ok subst targetEnv env`. *)
definition module_env_subst_runtime_ok ::
    "TypeSubst \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "module_env_subst_runtime_ok subst targetEnv env \<equiv>
    \<forall>n. n |\<in>| TE_RuntimeTypeVars env \<longrightarrow>
         (case fmlookup subst n of
            Some ty' \<Rightarrow> is_runtime_type targetEnv ty'
          | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars targetEnv)"


(* Lifting facts: under module_env_subst_ok, apply_subst preserves
   well-kindedness from env to the substituted env, and runtime-ness
   similarly. *)
lemma apply_subst_preserves_well_kinded_module:
  assumes "is_well_kinded env ty"
      and "module_env_subst_ok subst targetEnv env"
  shows "is_well_kinded (apply_subst_to_module_env subst targetEnv env)
                        (apply_subst subst ty)"
proof (rule apply_subst_preserves_well_kinded[OF assms(1)])
  show "TE_Datatypes (apply_subst_to_module_env subst targetEnv env)
          = TE_Datatypes env"
    by simp
next
  fix n assume "n |\<in>| TE_TypeVars env"
  with assms(2) show
    "case fmlookup subst n of
        Some ty' \<Rightarrow> is_well_kinded (apply_subst_to_module_env subst targetEnv env) ty'
      | None \<Rightarrow> n |\<in>| TE_TypeVars (apply_subst_to_module_env subst targetEnv env)"
    unfolding module_env_subst_ok_def
    by (auto split: option.splits intro: is_well_kinded_cong_env[THEN iffD1])
qed

lemma apply_subst_preserves_runtime_module:
  assumes "is_runtime_type env ty"
      and "module_env_subst_ok subst targetEnv env"
      and "module_env_subst_runtime_ok subst targetEnv env"
  shows "is_runtime_type (apply_subst_to_module_env subst targetEnv env)
                         (apply_subst subst ty)"
proof (rule apply_subst_preserves_runtime[OF assms(1)])
  show "TE_GhostDatatypes (apply_subst_to_module_env subst targetEnv env)
          = TE_GhostDatatypes env"
    by simp
next
  \<comment> \<open>is_runtime_type only depends on TE_GhostDatatypes and TE_RuntimeTypeVars;
      on the substituted env, the former agrees with targetEnv (via
      module_env_subst_ok's datatype-table clause) and the latter is
      targetEnv's by definition, so runtime-ness in targetEnv transfers.\<close>
  have rt_cong: "\<And>ty'. is_runtime_type targetEnv ty'
                       = is_runtime_type (apply_subst_to_module_env subst targetEnv env) ty'"
    using assms(2)
    by (intro is_runtime_type_cong_env)
       (simp_all add: module_env_subst_ok_def)
  fix n assume n_in: "n |\<in>| TE_RuntimeTypeVars env"
  show
    "case fmlookup subst n of
        Some ty' \<Rightarrow> is_runtime_type (apply_subst_to_module_env subst targetEnv env) ty'
      | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars (apply_subst_to_module_env subst targetEnv env)"
  proof (cases "fmlookup subst n")
    case None
    with assms(3) n_in have "n |\<in>| TE_RuntimeTypeVars targetEnv"
      unfolding module_env_subst_runtime_ok_def by auto
    thus ?thesis using None by simp
  next
    case (Some ty')
    with assms(3) n_in have "is_runtime_type targetEnv ty'"
      unfolding module_env_subst_runtime_ok_def by auto
    with rt_cong have "is_runtime_type (apply_subst_to_module_env subst targetEnv env) ty'"
      by simp
    thus ?thesis using Some by simp
  qed
qed


(* ========================================================================== *)
(* Pattern compatibility under the substituted env                            *)
(* ========================================================================== *)

(* If a pattern is compatible with a type in env, it is compatible with the
   substituted type once the ctor table is substituted as well.
   The Variant case is where the work happens: the ctor's payload type is
   substituted in the new table, so the inner tyvar-instantiation must commute
   with the outer substitution - subst_names_avoid_compose, discharged by the
   ctor binder-avoidance hypothesis.

   Stated over a single env (the conclusion updates env's own ctor table)
   so that the induction generalizes just one environment variable; the
   env'-form used by the term-typing proof follows by
   pattern_compatible_cong_env below. *)
lemma pattern_compatible_apply_subst_module_aux:
  assumes "tyenv_well_formed env"
      and "pattern_compatible env p ty"
      and "\<forall>ctorName dtName tyVars payload.
              fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload) \<longrightarrow>
              subst_names subst |\<inter>| fset_of_list tyVars = {||}"
  shows "pattern_compatible
           (env \<lparr> TE_DataCtors := fmmap (apply_subst_to_datactor subst) (TE_DataCtors env) \<rparr>)
           p (apply_subst subst ty)"
  using assms
proof (induction env p ty rule: pattern_compatible.induct[case_names Wildcard Bool Int Variant Record, consumes 0])
  case (Wildcard env uu)
  then show ?case by simp
next
  case (Bool env uv ty)
  then show ?case by (cases ty) auto
next
  case (Int env uw ty)
  then show ?case by (cases ty) auto
next
  case (Variant env ctorName payloadPat ty)
  from Variant.prems show ?case
  proof (cases ty)
    case (CoreTy_Datatype tyName tyArgs)
    with Variant.prems obtain dtName tyvars payloadTy where
      ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payloadTy)" and
      dt_eq: "tyName = dtName" and
      len_eq: "length tyArgs = length tyvars" and
      pc_payload: "pattern_compatible env payloadPat
                     (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
      by (auto split: option.splits prod.splits)
    have tyvars_distinct: "distinct tyvars"
      using Variant.prems(1) ctor_lookup
      unfolding tyenv_well_formed_def tyenv_ctor_tyvars_distinct_def by blast
    have avoid: "subst_names subst |\<inter>| fset_of_list tyvars = {||}"
      using Variant.prems(3) ctor_lookup by blast
    \<comment> \<open>The inner tyvar-instantiation (over substituted tyArgs, on the
        substituted payload) commutes with the outer substitution. \<close>
    have compose:
      "apply_subst (fmap_of_list (zip tyvars (map (apply_subst subst) tyArgs)))
                   (apply_subst subst payloadTy)
         = apply_subst subst (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
      using subst_names_avoid_compose[OF len_eq[symmetric] avoid tyvars_distinct] .
    have ty_eq: "ty = CoreTy_Datatype dtName tyArgs"
      using CoreTy_Datatype dt_eq by simp
    \<comment> \<open>IH on payloadPat. \<close>
    have payload_subst:
      "pattern_compatible
         (env \<lparr> TE_DataCtors := fmmap (apply_subst_to_datactor subst) (TE_DataCtors env) \<rparr>)
         payloadPat
         (apply_subst subst (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy))"
      using Variant.IH[OF ctor_lookup refl refl ty_eq Variant.prems(1) pc_payload
                          Variant.prems(3)] .
    show ?thesis
      using ctor_lookup CoreTy_Datatype dt_eq len_eq payload_subst compose by simp
  qed (use Variant.prems in \<open>auto split: option.splits prod.splits\<close>)
next
  case (Record env pflds ty)
  from Record.prems show ?case
  proof (cases ty)
    case (CoreTy_Record fldTys)
    with Record.prems have
      flds_ok: "list_all2 (\<lambda>(pn, p) (fn, fty). pn = fn \<and> pattern_compatible env p fty)
                          pflds fldTys"
      by auto
    \<comment> \<open>The substituted record type has the same field names, with each field's
        type substituted. \<close>
    let ?subst_fldTys = "map (\<lambda>(name, fty). (name, apply_subst subst fty)) fldTys"
    have subst_ty_eq: "apply_subst subst ty = CoreTy_Record ?subst_fldTys"
      using CoreTy_Record by simp
    have lens_eq: "length pflds = length fldTys"
      using flds_ok by (simp add: list_all2_lengthD)
    let ?env2 = "env \<lparr> TE_DataCtors := fmmap (apply_subst_to_datactor subst) (TE_DataCtors env) \<rparr>"
    have flds_ok':
      "list_all2 (\<lambda>(pn, p) (fn, fty'). pn = fn \<and> pattern_compatible ?env2 p fty')
                 pflds ?subst_fldTys"
      unfolding list_all2_conv_all_nth
    proof (intro conjI allI impI)
      show "length pflds = length ?subst_fldTys" using lens_eq by simp
    next
      fix i assume i_lt: "i < length pflds"
      let ?pf = "pflds ! i"
      let ?ft = "fldTys ! i"
      obtain pn p where pf_eq: "?pf = (pn, p)" by (cases ?pf)
      obtain fn fty where ft_eq: "?ft = (fn, fty)" by (cases ?ft)
      have pf_in: "?pf \<in> set pflds" using i_lt by simp
      have ft_in: "?ft \<in> set fldTys" using i_lt lens_eq by simp
      from flds_ok i_lt have
        names_eq: "pn = fn" and
        pc_p: "pattern_compatible env p fty"
        using pf_eq ft_eq lens_eq by (auto simp: list_all2_conv_all_nth)
      have ih_pc: "pattern_compatible ?env2 p (apply_subst subst fty)"
        using Record.IH[OF CoreTy_Record pf_in ft_in pf_eq[symmetric] Record.prems(1)
                           pc_p Record.prems(3)] .
      have subst_nth: "?subst_fldTys ! i = (fn, apply_subst subst fty)"
        using i_lt lens_eq ft_eq by simp
      show "(case pflds ! i of (pn, p) \<Rightarrow>
              \<lambda>(fn, fty'). pn = fn \<and> pattern_compatible ?env2 p fty')
            (?subst_fldTys ! i)"
        using pf_eq subst_nth names_eq ih_pc by simp
    qed
    show ?thesis
      using subst_ty_eq flds_ok' by simp
  qed (use Record.prems in \<open>auto split: CoreType.splits\<close>)
qed

(* The env'-form: any env whose ctor table is the substituted one works,
   since pattern_compatible only reads the env through TE_DataCtors. *)
lemma pattern_compatible_apply_subst_module:
  assumes "tyenv_well_formed env"
      and "pattern_compatible env p ty"
      and "TE_DataCtors env' = fmmap (apply_subst_to_datactor subst) (TE_DataCtors env)"
      and "\<forall>ctorName dtName tyVars payload.
              fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload) \<longrightarrow>
              subst_names subst |\<inter>| fset_of_list tyVars = {||}"
  shows "pattern_compatible env' p (apply_subst subst ty)"
proof -
  have "pattern_compatible
          (env \<lparr> TE_DataCtors := fmmap (apply_subst_to_datactor subst) (TE_DataCtors env) \<rparr>)
          p (apply_subst subst ty)"
    by (rule pattern_compatible_apply_subst_module_aux[OF assms(1,2,4)])
  moreover have "TE_DataCtors
                   (env \<lparr> TE_DataCtors := fmmap (apply_subst_to_datactor subst) (TE_DataCtors env) \<rparr>)
                 = TE_DataCtors env'"
    using assms(3) by simp
  ultimately show ?thesis
    using pattern_compatible_cong_env by blast
qed


(* ========================================================================== *)
(* Shared setup for FunctionCall substitution proofs                          *)
(* ========================================================================== *)

(* The "preamble" facts a function-call case needs once it has looked up the
   function: the substituted lookup result, well-kindedness / runtime-ness of
   the substituted type arguments, lengths, distinctness of the type
   parameters, and the composition equation. Unlike the callee-env analogue
   (function_call_subst_setup, TypeSubstHelpers.thy) there is no per-type
   tyvar-containment condition: binder-avoidance of subst_names makes the
   composition unconditional in the signature type. *)
lemma module_call_subst_setup:
  assumes fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo"
      and len_tyArgs: "length tyArgs = length (FI_TyArgs funInfo)"
      and tyArgs_wk: "list_all (is_well_kinded env) tyArgs"
      and ng_tyArgs: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) tyArgs"
      and wf: "tyenv_well_formed env"
      and ok: "module_env_subst_ok subst targetEnv env"
      and ok_rt: "ghost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv env"
  shows "fmlookup (TE_Functions (apply_subst_to_module_env subst targetEnv env)) fnName
           = Some (apply_subst_to_funinfo subst funInfo)"
    and "list_all (is_well_kinded (apply_subst_to_module_env subst targetEnv env))
                  (map (apply_subst subst) tyArgs)"
    and "ghost = NotGhost \<longrightarrow>
         list_all (is_runtime_type (apply_subst_to_module_env subst targetEnv env))
                  (map (apply_subst subst) tyArgs)"
    and "length (map (apply_subst subst) tyArgs) = length (FI_TyArgs funInfo)"
    and "distinct (FI_TyArgs funInfo)"
    and "apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) (map (apply_subst subst) tyArgs)))
                     (apply_subst subst ty0)
           = apply_subst subst
               (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty0)"
proof -
  show "fmlookup (TE_Functions (apply_subst_to_module_env subst targetEnv env)) fnName
          = Some (apply_subst_to_funinfo subst funInfo)"
    using fn_lookup by simp

  show "list_all (is_well_kinded (apply_subst_to_module_env subst targetEnv env))
                 (map (apply_subst subst) tyArgs)"
    using tyArgs_wk
    by (induction tyArgs)
       (auto intro: apply_subst_preserves_well_kinded_module[OF _ ok])

  show "ghost = NotGhost \<longrightarrow>
        list_all (is_runtime_type (apply_subst_to_module_env subst targetEnv env))
                 (map (apply_subst subst) tyArgs)"
  proof
    assume ng: "ghost = NotGhost"
    with ng_tyArgs have rt: "list_all (is_runtime_type env) tyArgs" by simp
    from ng ok_rt have ok_rt': "module_env_subst_runtime_ok subst targetEnv env" by simp
    show "list_all (is_runtime_type (apply_subst_to_module_env subst targetEnv env))
                   (map (apply_subst subst) tyArgs)"
      using rt
      by (induction tyArgs)
         (auto intro: apply_subst_preserves_runtime_module[OF _ ok ok_rt'])
  qed

  show "length (map (apply_subst subst) tyArgs) = length (FI_TyArgs funInfo)"
    using len_tyArgs by simp

  show tyArgs_distinct: "distinct (FI_TyArgs funInfo)"
    using wf fn_lookup
    unfolding tyenv_well_formed_def tyenv_fun_tyvars_distinct_def by blast

  have avoid: "subst_names subst |\<inter>| fset_of_list (FI_TyArgs funInfo) = {||}"
    using ok fn_lookup unfolding module_env_subst_ok_def by blast

  show "apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) (map (apply_subst subst) tyArgs)))
                    (apply_subst subst ty0)
          = apply_subst subst
              (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty0)"
    using subst_names_avoid_compose[OF len_tyArgs[symmetric] avoid tyArgs_distinct] .
qed


(* ========================================================================== *)
(* Term typing under module-env substitution                                  *)
(* ========================================================================== *)

(* If a term typechecks in env, then the substituted term typechecks (with
   substituted result type) in the substituted module env.

   Conditions:
   - env is well-formed (variable lookups land on well-kinded types, function
     type parameters are distinct, etc.)
   - module_env_subst_ok: datatype-table agreement with targetEnv, tyvar
     coverage, and binder-avoidance (capture-avoidance) for function / ctor
     type parameters
   - In NotGhost mode, the runtime-tyvar coverage holds
     (module_env_subst_runtime_ok). *)
lemma core_term_type_subst_module_env:
  assumes "core_term_type env ghost tm = Some ty"
      and "tyenv_well_formed env"
      and "module_env_subst_ok subst targetEnv env"
      and "ghost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv env"
  shows "core_term_type (apply_subst_to_module_env subst targetEnv env) ghost
                        (apply_subst_to_term subst tm)
           = Some (apply_subst subst ty)"
using assms proof (induction tm arbitrary: ty ghost env)
  case (CoreTm_LitBool b)
  then show ?case by simp
next
  case (CoreTm_LitInt i)
  then show ?case by (auto split: option.splits)
next
  case (CoreTm_LitArray elemTy tms)
  from CoreTm_LitArray.prems(1) have
    elemTy_wk: "is_well_kinded env elemTy" and
    elemTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env elemTy" and
    tms_typed: "list_all (\<lambda>tm. core_term_type env ghost tm = Some elemTy) tms" and
    len_ok: "int_in_range (int_range Unsigned IntBits_64) (int (length tms))" and
    ty_eq: "ty = CoreTy_Array elemTy [CoreDim_Fixed (int (length tms))]"
    by (auto split: if_splits)

  have elemTy_wk_subst: "is_well_kinded (apply_subst_to_module_env subst targetEnv env)
                                        (apply_subst subst elemTy)"
    using apply_subst_preserves_well_kinded_module[OF elemTy_wk CoreTm_LitArray.prems(3)] .
  have elemTy_rt_subst:
    "ghost = NotGhost \<longrightarrow>
       is_runtime_type (apply_subst_to_module_env subst targetEnv env)
                       (apply_subst subst elemTy)"
  proof
    assume ng: "ghost = NotGhost"
    with elemTy_rt have rt: "is_runtime_type env elemTy" by simp
    from ng CoreTm_LitArray.prems(4) have ok_rt: "module_env_subst_runtime_ok subst targetEnv env"
      by simp
    from apply_subst_preserves_runtime_module[OF rt CoreTm_LitArray.prems(3) ok_rt]
    show "is_runtime_type (apply_subst_to_module_env subst targetEnv env)
                          (apply_subst subst elemTy)" .
  qed

  have tms_subst:
    "list_all (\<lambda>tm. core_term_type (apply_subst_to_module_env subst targetEnv env) ghost tm
                      = Some (apply_subst subst elemTy))
              (map (apply_subst_to_term subst) tms)"
  proof (unfold list_all_iff, intro ballI)
    fix tm' assume "tm' \<in> set (map (apply_subst_to_term subst) tms)"
    then obtain tm where tm_in: "tm \<in> set tms" and tm'_eq: "tm' = apply_subst_to_term subst tm"
      by auto
    from tms_typed tm_in have tm_typed: "core_term_type env ghost tm = Some elemTy"
      by (simp add: list_all_iff)
    from CoreTm_LitArray.IH[OF tm_in tm_typed CoreTm_LitArray.prems(2,3,4)]
    show "core_term_type (apply_subst_to_module_env subst targetEnv env) ghost tm'
            = Some (apply_subst subst elemTy)"
      using tm'_eq by simp
  qed

  have len_eq: "length (map (apply_subst_to_term subst) tms) = length tms" by simp

  show ?case
    using elemTy_wk_subst elemTy_rt_subst tms_subst len_eq len_ok ty_eq by simp
next
  case (CoreTm_Var name)
  \<comment> \<open>Var: both locals and globals are substituted, so lookup commutes with the
      substitution directly. \<close>
  from CoreTm_Var.prems(1) obtain lookupTy where
    lookup: "tyenv_lookup_var env name = Some lookupTy" and
    not_ghost_ok: "ghost = NotGhost \<longrightarrow> \<not> tyenv_var_ghost env name" and
    ty_eq: "ty = lookupTy"
    by (auto split: option.splits if_splits)
  have lookup_subst:
    "tyenv_lookup_var (apply_subst_to_module_env subst targetEnv env) name
       = Some (apply_subst subst lookupTy)"
    using lookup by (simp add: tyenv_lookup_var_apply_subst_to_module_env)
  show ?case
    using lookup_subst ty_eq not_ghost_ok by simp
next
  case (CoreTm_Cast targetTy operand)
  from CoreTm_Cast.prems(1) obtain operandTy where
    op_typed: "core_term_type env ghost operand = Some operandTy" and
    op_int: "is_integer_type operandTy" and
    tgt_int: "is_integer_type targetTy" and
    tgt_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env targetTy" and
    ty_eq: "ty = targetTy"
    by (auto split: option.splits if_splits)
  from CoreTm_Cast.IH[OF op_typed CoreTm_Cast.prems(2,3,4)]
  have op_subst:
    "core_term_type (apply_subst_to_module_env subst targetEnv env) ghost
                    (apply_subst_to_term subst operand)
       = Some (apply_subst subst operandTy)" .
  have op_ty_eq: "apply_subst subst operandTy = operandTy"
    using op_int is_integer_type_apply_subst by simp
  have tgt_ty_eq: "apply_subst subst targetTy = targetTy"
    using tgt_int is_integer_type_apply_subst by simp
  have tgt_rt_subst:
    "ghost = NotGhost \<longrightarrow>
       is_runtime_type (apply_subst_to_module_env subst targetEnv env)
                       (apply_subst subst targetTy)"
  proof
    assume ng: "ghost = NotGhost"
    with tgt_rt have rt: "is_runtime_type env targetTy" by simp
    from ng CoreTm_Cast.prems(4) have ok_rt: "module_env_subst_runtime_ok subst targetEnv env"
      by simp
    from apply_subst_preserves_runtime_module[OF rt CoreTm_Cast.prems(3) ok_rt]
    show "is_runtime_type (apply_subst_to_module_env subst targetEnv env)
                          (apply_subst subst targetTy)" .
  qed
  show ?case
    using op_subst op_int op_ty_eq tgt_int tgt_ty_eq tgt_rt_subst ty_eq
    by auto
next
  case (CoreTm_Unop op operand)
  from CoreTm_Unop.prems(1) obtain operandTy where
    op_typed: "core_term_type env ghost operand = Some operandTy"
    by (auto split: option.splits)
  from CoreTm_Unop.IH[OF op_typed CoreTm_Unop.prems(2,3,4)]
  have op_subst:
    "core_term_type (apply_subst_to_module_env subst targetEnv env) ghost
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
  from CoreTm_Binop.prems(1) obtain lhsTy rhsTy where
    lhs_typed: "core_term_type env ghost lhs = Some lhsTy" and
    rhs_typed: "core_term_type env ghost rhs = Some rhsTy"
    by (auto split: option.splits)
  from CoreTm_Binop.IH(1)[OF lhs_typed CoreTm_Binop.prems(2,3,4)]
  have lhs_subst:
    "core_term_type (apply_subst_to_module_env subst targetEnv env) ghost
                    (apply_subst_to_term subst lhs)
       = Some (apply_subst subst lhsTy)" .
  from CoreTm_Binop.IH(2)[OF rhs_typed CoreTm_Binop.prems(2,3,4)]
  have rhs_subst:
    "core_term_type (apply_subst_to_module_env subst targetEnv env) ghost
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
    case 1
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      num: "is_numeric_type lhsTy" and ty_eq: "ty = lhsTy"
      by (auto dest: binop_categories_disjoint split: if_splits)
    have ty_closed: "apply_subst subst lhsTy = lhsTy"
      using num is_numeric_type_apply_subst by simp
    show ?thesis
      using 1 lhs_subst rhs_subst tys_eq ty_eq ty_closed num
      by (auto dest: binop_categories_disjoint)
  next
    case 2
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      int: "is_integer_type lhsTy" and ty_eq: "ty = lhsTy"
      by (auto dest: binop_categories_disjoint split: if_splits)
    have ty_closed: "apply_subst subst lhsTy = lhsTy"
      using int is_integer_type_apply_subst by simp
    show ?thesis
      using 2 lhs_subst rhs_subst tys_eq ty_eq ty_closed int
      by (auto dest: binop_categories_disjoint)
  next
    case 3
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      fi: "is_finite_integer_type lhsTy" and ty_eq: "ty = lhsTy"
      by (auto dest: binop_categories_disjoint split: if_splits)
    have ty_closed: "apply_subst subst lhsTy = lhsTy"
      using fi is_finite_integer_type_apply_subst by simp
    show ?thesis
      using 3 lhs_subst rhs_subst tys_eq ty_eq ty_closed fi
      by (auto dest: binop_categories_disjoint)
  next
    case 4
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      fi: "is_finite_integer_type lhsTy" and ty_eq: "ty = lhsTy"
      by (auto dest: binop_categories_disjoint split: if_splits)
    have ty_closed: "apply_subst subst lhsTy = lhsTy"
      using fi is_finite_integer_type_apply_subst by simp
    show ?thesis
      using 4 lhs_subst rhs_subst tys_eq ty_eq ty_closed fi
      by (auto dest: binop_categories_disjoint)
  next
    case 5
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      num: "is_numeric_type lhsTy" and ty_eq: "ty = CoreTy_Bool"
      by (auto dest: binop_categories_disjoint split: if_splits)
    have ty_closed: "apply_subst subst lhsTy = lhsTy"
      using num is_numeric_type_apply_subst by simp
    show ?thesis
      using 5 lhs_subst rhs_subst tys_eq ty_eq ty_closed num
      by (auto dest: binop_categories_disjoint)
  next
    case 6
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      ty_eq: "ty = CoreTy_Bool" and
      typing_ok: "ghost = Ghost \<or> lhsTy = CoreTy_Bool \<or> is_numeric_type lhsTy"
      by (auto dest: binop_categories_disjoint split: if_splits)
    \<comment> \<open>Resolve the category if-chain up front, so the final step is plain
        rewriting rather than a search over all 42 disjointness rules
        combined with if-splitting. \<close>
    have not_cats: "\<not> is_arithmetic_binop op \<and> \<not> is_modulo_binop op
                    \<and> \<not> is_bitwise_binop op \<and> \<not> is_shift_binop op
                    \<and> \<not> is_ordering_binop op"
      using 6 by (auto dest: binop_categories_disjoint)
    show ?thesis
      using 6 lhs_subst rhs_subst tys_eq ty_eq typing_ok not_cats
      by (auto simp: is_numeric_type_apply_subst)
  next
    case 7
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      bool_eq: "lhsTy = CoreTy_Bool" and ty_eq: "ty = CoreTy_Bool"
      by (auto dest: binop_categories_disjoint split: if_splits)
    show ?thesis
      using 7 lhs_subst rhs_subst tys_eq ty_eq bool_eq
      by (auto dest: binop_categories_disjoint)
  qed
next
  case (CoreTm_Let var rhs body)
  from CoreTm_Let.prems(1) obtain rhsTy where
    rhs_typed: "core_term_type env ghost rhs = Some rhsTy" and
    body_typed: "core_term_type
                   (env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                          TE_GhostLocals := (if ghost = Ghost
                                            then finsert var (TE_GhostLocals env)
                                            else fminus (TE_GhostLocals env) {|var|}),
                          TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>)
                   ghost body = Some ty"
    by (auto split: option.splits simp: Let_def)

  let ?env_ext = "env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                        TE_GhostLocals := (if ghost = Ghost
                                          then finsert var (TE_GhostLocals env)
                                          else fminus (TE_GhostLocals env) {|var|}),
                        TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"

  from CoreTm_Let.IH(1)[OF rhs_typed CoreTm_Let.prems(2,3,4)]
  have rhs_subst:
    "core_term_type (apply_subst_to_module_env subst targetEnv env) ghost
                    (apply_subst_to_term subst rhs)
       = Some (apply_subst subst rhsTy)" .

  have rhsTy_wk: "is_well_kinded env rhsTy"
    using core_term_type_well_kinded[OF rhs_typed CoreTm_Let.prems(2)] .
  have rhsTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env rhsTy"
  proof
    assume ng: "ghost = NotGhost"
    with rhs_typed have "core_term_type env NotGhost rhs = Some rhsTy" by simp
    from core_term_type_notghost_runtime[OF this CoreTm_Let.prems(2)]
    show "is_runtime_type env rhsTy" .
  qed

  have wf_ext: "tyenv_well_formed ?env_ext"
  proof (cases ghost)
    case NotGhost
    from rhsTy_rt NotGhost have rt: "is_runtime_type env rhsTy" by simp
    from tyenv_well_formed_add_var[OF CoreTm_Let.prems(2) rhsTy_wk rt]
    have wf':
      "tyenv_well_formed
         (env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                TE_GhostLocals := fminus (TE_GhostLocals env) {|var|} \<rparr>)" .
    from tyenv_well_formed_TE_ConstLocals_irrelevant[OF wf',
            of "finsert var (TE_ConstLocals env)"]
    have "tyenv_well_formed
            (env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                   TE_GhostLocals := fminus (TE_GhostLocals env) {|var|} \<rparr>
                 \<lparr> TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>)" .
    with NotGhost show ?thesis by simp
  next
    case Ghost
    from tyenv_well_formed_add_ghost_var[OF CoreTm_Let.prems(2) rhsTy_wk]
    have wf':
      "tyenv_well_formed
         (env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                TE_GhostLocals := finsert var (TE_GhostLocals env) \<rparr>)" .
    from tyenv_well_formed_TE_ConstLocals_irrelevant[OF wf',
            of "finsert var (TE_ConstLocals env)"]
    have "tyenv_well_formed
            (env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                   TE_GhostLocals := finsert var (TE_GhostLocals env) \<rparr>
                 \<lparr> TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>)" .
    with Ghost show ?thesis by simp
  qed

  \<comment> \<open>module_env_subst_ok ?env_ext: only TE_LocalVars / TE_GhostLocals /
      TE_ConstLocals changed, none of which module_env_subst_ok references. \<close>
  have ok_ext: "module_env_subst_ok subst targetEnv ?env_ext"
    using CoreTm_Let.prems(3)
    unfolding module_env_subst_ok_def by simp

  have ok_rt_ext: "ghost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv ?env_ext"
    using CoreTm_Let.prems(4)
    unfolding module_env_subst_runtime_ok_def by simp

  from CoreTm_Let.IH(2)[OF body_typed wf_ext ok_ext ok_rt_ext]
  have body_subst:
    "core_term_type (apply_subst_to_module_env subst targetEnv ?env_ext) ghost
                    (apply_subst_to_term subst body)
       = Some (apply_subst subst ty)" .

  have ext_subst_eq:
    "apply_subst_to_module_env subst targetEnv ?env_ext
       = (apply_subst_to_module_env subst targetEnv env) \<lparr>
            TE_LocalVars := fmupd var (apply_subst subst rhsTy)
                              (TE_LocalVars (apply_subst_to_module_env subst targetEnv env)),
            TE_GhostLocals := (if ghost = Ghost
                              then finsert var (TE_GhostLocals (apply_subst_to_module_env subst targetEnv env))
                              else fminus (TE_GhostLocals (apply_subst_to_module_env subst targetEnv env))
                                          {|var|}),
            TE_ConstLocals := finsert var (TE_ConstLocals (apply_subst_to_module_env subst targetEnv env)) \<rparr>"
    unfolding apply_subst_to_module_env_def by (simp add: fmmap_fmupd)

  show ?case
    using rhs_subst body_subst ext_subst_eq by (simp add: Let_def)
next
  case (CoreTm_Quantifier quant var varTy body)
  show ?case
  proof (cases ghost)
    case NotGhost
    with CoreTm_Quantifier.prems(1) show ?thesis by simp
  next
    case Ghost
    with CoreTm_Quantifier.prems(1) have
      varTy_wk: "is_well_kinded env varTy" and
      body_typed: "core_term_type
                     (env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                            TE_GhostLocals := finsert var (TE_GhostLocals env) \<rparr>)
                     Ghost body = Some CoreTy_Bool" and
      ty_eq: "ty = CoreTy_Bool"
      by (auto split: option.splits CoreType.splits if_splits)

    let ?env_ext = "env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                          TE_GhostLocals := finsert var (TE_GhostLocals env) \<rparr>"

    from tyenv_well_formed_add_ghost_var[OF CoreTm_Quantifier.prems(2) varTy_wk]
    have wf_ext: "tyenv_well_formed ?env_ext" .

    have ok_ext: "module_env_subst_ok subst targetEnv ?env_ext"
      using CoreTm_Quantifier.prems(3)
      unfolding module_env_subst_ok_def by simp

    have varTy_wk_subst:
      "is_well_kinded (apply_subst_to_module_env subst targetEnv env)
                      (apply_subst subst varTy)"
      using apply_subst_preserves_well_kinded_module[OF varTy_wk CoreTm_Quantifier.prems(3)] .

    have body_rt_ok_premise:
      "Ghost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv ?env_ext"
      by simp
    from CoreTm_Quantifier.IH[OF body_typed wf_ext ok_ext body_rt_ok_premise]
    have body_subst:
      "core_term_type (apply_subst_to_module_env subst targetEnv ?env_ext) Ghost
                      (apply_subst_to_term subst body)
         = Some (apply_subst subst CoreTy_Bool)" .

    have ext_subst_eq:
      "apply_subst_to_module_env subst targetEnv ?env_ext
         = (apply_subst_to_module_env subst targetEnv env) \<lparr>
              TE_LocalVars := fmupd var (apply_subst subst varTy)
                                (TE_LocalVars (apply_subst_to_module_env subst targetEnv env)),
              TE_GhostLocals := finsert var (TE_GhostLocals (apply_subst_to_module_env subst targetEnv env)) \<rparr>"
      unfolding apply_subst_to_module_env_def by (simp add: fmmap_fmupd)

    show ?thesis
      using body_subst varTy_wk_subst ext_subst_eq Ghost ty_eq by simp
  qed
next
  case (CoreTm_FunctionCall fnName tyArgs tmArgs)
  \<comment> \<open>FunctionCall: the lookup in the substituted env returns the SUBSTITUTED
      FunInfo (contrast the callee engine, where the tables are equal). The
      typechecker at the substituted site therefore instantiates the
      substituted signature types with the substituted type arguments; the
      composition equation (module_call_subst_setup, last conclusion) turns
      that into the outer substitution applied to the original expected types. \<close>
  from CoreTm_FunctionCall.prems(1) obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
    len_tyArgs: "length tyArgs = length (FI_TyArgs funInfo)" and
    tyArgs_wk: "list_all (is_well_kinded env) tyArgs" and
    not_ghost_cond: "\<not> (ghost = NotGhost
                       \<and> (\<not> list_all (is_runtime_type env) tyArgs
                          \<or> FI_Ghost funInfo = Ghost))" and
    all_var: "list_all (\<lambda>(_, vor). vor = Var) (FI_TmArgs funInfo)" and
    not_impure: "\<not> FI_Impure funInfo" and
    len_tmArgs: "length tmArgs = length (FI_TmArgs funInfo)" and
    args_check: "list_all2 (\<lambda>tm expectedTy.
                    case core_term_type env ghost tm of
                      None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
                  tmArgs (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                              (FI_TmArgs funInfo))" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo)"
    by (auto simp: Let_def split: option.splits if_splits)
  have ng_tyArgs: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) tyArgs"
    using not_ghost_cond by blast
  have ng_fn: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost"
    using not_ghost_cond by blast

  let ?me = "apply_subst_to_module_env subst targetEnv env"
  let ?subst_tyArgs = "map (apply_subst subst) tyArgs"
  let ?innerSubst = "fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)"
  let ?subst_innerSubst = "fmap_of_list (zip (FI_TyArgs funInfo) ?subst_tyArgs)"
  let ?funInfo' = "apply_subst_to_funinfo subst funInfo"

  note call_setup = module_call_subst_setup[OF fn_lookup len_tyArgs tyArgs_wk ng_tyArgs
                                               CoreTm_FunctionCall.prems(2,3,4)]
  note fn_lookup_subst   = call_setup(1)
  note tyArgs_wk_subst   = call_setup(2)
  note tyArgs_rt_subst   = call_setup(3)
  note len_tyArgs_subst  = call_setup(4)
  note tyArgs_distinct   = call_setup(5)
  note compose           = call_setup(6)

  have all_var_subst: "list_all (\<lambda>(_, vor). vor = Var) (FI_TmArgs ?funInfo')"
    using all_var by (fastforce simp: list_all_iff)

  have len_tmArgs_subst:
    "length (map (apply_subst_to_term subst) tmArgs) = length (FI_TmArgs ?funInfo')"
    using len_tmArgs by simp

  \<comment> \<open>The expected argument types at the substituted site are the outer
      substitution applied to the original expected argument types. Stated as
      a function-level equation so that it rewrites the fused
      \<open>map (f \<circ> g)\<close> form the simplifier produces from the two nested maps. \<close>
  have expected_eq:
    "(\<lambda>(ty, _). apply_subst ?subst_innerSubst ty) \<circ> (\<lambda>(ty, vr). (apply_subst subst ty, vr))
       = (\<lambda>(ty, _). apply_subst subst (apply_subst ?innerSubst ty))"
    using compose by (auto simp: fun_eq_iff split: prod.splits)

  have args_check_subst:
    "list_all2 (\<lambda>tm expectedTy.
                  case core_term_type ?me ghost tm of
                    None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
              (map (apply_subst_to_term subst) tmArgs)
              (map (\<lambda>(ty, _). apply_subst subst (apply_subst ?innerSubst ty)) (FI_TmArgs funInfo))"
  proof (rule list_all2_all_nthI)
    show "length (map (apply_subst_to_term subst) tmArgs)
            = length (map (\<lambda>(ty, _). apply_subst subst (apply_subst ?innerSubst ty))
                          (FI_TmArgs funInfo))"
      using len_tmArgs by simp
  next
    fix i assume i_bound: "i < length (map (apply_subst_to_term subst) tmArgs)"
    hence i_bound': "i < length tmArgs" by simp
    hence i_bound_args: "i < length (FI_TmArgs funInfo)" using len_tmArgs by simp
    from args_check have args_nth_raw:
      "case core_term_type env ghost (tmArgs ! i) of
         None \<Rightarrow> False
       | Some actualTy \<Rightarrow>
           actualTy = map (\<lambda>(ty, _). apply_subst ?innerSubst ty) (FI_TmArgs funInfo) ! i"
      using i_bound' len_tmArgs
      by (simp add: list_all2_conv_all_nth)
    have args_nth:
      "case core_term_type env ghost (tmArgs ! i) of
         None \<Rightarrow> False
       | Some actualTy \<Rightarrow> actualTy = (case FI_TmArgs funInfo ! i of
            (ty, _) \<Rightarrow> apply_subst ?innerSubst ty)"
      using args_nth_raw i_bound_args
      by (metis nth_map)
    then obtain actualTy where
      actual_typed: "core_term_type env ghost (tmArgs ! i) = Some actualTy" and
      actual_eq: "actualTy = (case FI_TmArgs funInfo ! i of
                              (ty, _) \<Rightarrow> apply_subst ?innerSubst ty)"
      by (auto split: option.splits)
    have tmArg_in: "tmArgs ! i \<in> set tmArgs" using i_bound' by simp
    from CoreTm_FunctionCall.IH[OF tmArg_in actual_typed
                                   CoreTm_FunctionCall.prems(2,3,4)]
    have ih_result:
      "core_term_type ?me ghost (apply_subst_to_term subst (tmArgs ! i))
         = Some (apply_subst subst actualTy)" .
    obtain ti vor where fi_arg_eq: "FI_TmArgs funInfo ! i = (ti, vor)"
      by (cases "FI_TmArgs funInfo ! i") auto
    from actual_eq fi_arg_eq have actual_eq2: "actualTy = apply_subst ?innerSubst ti" by simp
    show "case core_term_type ?me ghost (map (apply_subst_to_term subst) tmArgs ! i) of
            None \<Rightarrow> False
          | Some actualTy \<Rightarrow> actualTy = map (\<lambda>(ty, _). apply_subst subst (apply_subst ?innerSubst ty))
                                            (FI_TmArgs funInfo) ! i"
      using ih_result actual_eq2 i_bound' i_bound_args fi_arg_eq
      by simp
  qed

  have ret_compose:
    "apply_subst ?subst_innerSubst (apply_subst subst (FI_ReturnType funInfo))
       = apply_subst subst (apply_subst ?innerSubst (FI_ReturnType funInfo))"
    by (rule compose)

  show ?case
    using fn_lookup_subst len_tyArgs_subst tyArgs_wk_subst tyArgs_rt_subst ng_fn
          all_var_subst not_impure len_tmArgs_subst args_check_subst
          ty_eq ret_compose
    by (auto simp: Let_def expected_eq)
next
  case (CoreTm_VariantCtor ctorName tyArgs payload)
  \<comment> \<open>VariantCtor: the ctor lookup in the substituted env returns the
      substituted payload type; the inner tyvar-instantiation over the
      substituted tyArgs commutes with the outer substitution via
      subst_names_avoid_compose (ctor binder-avoidance). \<close>
  from CoreTm_VariantCtor.prems(1) obtain dtName tyvars payloadTy where
    ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payloadTy)" and
    len_eq: "length tyArgs = length tyvars" and
    tyArgs_wk: "list_all (is_well_kinded env) tyArgs" and
    ng_constraint: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) tyArgs
                                          \<and> dtName |\<notin>| TE_GhostDatatypes env" and
    payload_typed: "core_term_type env ghost payload
                      = Some (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)" and
    ty_eq: "ty = CoreTy_Datatype dtName tyArgs"
    by (auto split: option.splits if_splits prod.splits)

  let ?me = "apply_subst_to_module_env subst targetEnv env"
  let ?subst_tyArgs = "map (apply_subst subst) tyArgs"

  have tyArgs_wk_subst: "list_all (is_well_kinded ?me) ?subst_tyArgs"
    using tyArgs_wk
    by (induction tyArgs)
       (auto intro: apply_subst_preserves_well_kinded_module[OF _ CoreTm_VariantCtor.prems(3)])

  have tyArgs_rt_subst:
    "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?me) ?subst_tyArgs"
  proof
    assume ng: "ghost = NotGhost"
    with ng_constraint have rt: "list_all (is_runtime_type env) tyArgs" by simp
    from ng CoreTm_VariantCtor.prems(4) have ok_rt:
      "module_env_subst_runtime_ok subst targetEnv env" by simp
    show "list_all (is_runtime_type ?me) ?subst_tyArgs"
      using rt
      by (induction tyArgs)
         (auto intro: apply_subst_preserves_runtime_module[OF _ CoreTm_VariantCtor.prems(3) ok_rt])
  qed

  have ng_dt_subst:
    "ghost = NotGhost \<longrightarrow> dtName |\<notin>| TE_GhostDatatypes ?me"
    using ng_constraint by simp

  from CoreTm_VariantCtor.IH[OF payload_typed CoreTm_VariantCtor.prems(2,3,4)]
  have payload_subst:
    "core_term_type ?me ghost (apply_subst_to_term subst payload)
       = Some (apply_subst subst (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy))" .

  have tyvars_distinct: "distinct tyvars"
    using CoreTm_VariantCtor.prems(2) ctor_lookup
    unfolding tyenv_well_formed_def tyenv_ctor_tyvars_distinct_def by blast

  have avoid: "subst_names subst |\<inter>| fset_of_list tyvars = {||}"
    using CoreTm_VariantCtor.prems(3) ctor_lookup
    unfolding module_env_subst_ok_def by blast

  have payload_compose:
    "apply_subst (fmap_of_list (zip tyvars ?subst_tyArgs)) (apply_subst subst payloadTy)
       = apply_subst subst (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
    using subst_names_avoid_compose[OF len_eq[symmetric] avoid tyvars_distinct] .

  have payload_subst_compose:
    "core_term_type ?me ghost (apply_subst_to_term subst payload)
       = Some (apply_subst (fmap_of_list (zip tyvars ?subst_tyArgs)) (apply_subst subst payloadTy))"
    using payload_subst payload_compose by simp

  have len_eq_subst: "length ?subst_tyArgs = length tyvars" using len_eq by simp

  show ?case
    using ctor_lookup tyArgs_wk_subst tyArgs_rt_subst ng_dt_subst
          payload_subst_compose len_eq_subst ty_eq
    by (auto simp: Let_def)
next
  case (CoreTm_Record flds)
  from CoreTm_Record.prems(1) obtain fieldTys where
    distinct_names: "distinct (map fst flds)" and
    flds_typed: "those (map (\<lambda>(name, tm). core_term_type env ghost tm) flds)
                   = Some fieldTys" and
    ty_eq: "ty = CoreTy_Record (zip (map fst flds) fieldTys)"
    by (auto split: option.splits if_splits)

  have field_IH:
    "\<And>fld ty'. fld \<in> set flds \<Longrightarrow>
       core_term_type env ghost (snd fld) = Some ty' \<Longrightarrow>
       core_term_type (apply_subst_to_module_env subst targetEnv env) ghost
                      (apply_subst_to_term subst (snd fld))
         = Some (apply_subst subst ty')"
    using CoreTm_Record.IH CoreTm_Record.prems(2,3,4)
    by (auto simp: snds.simps)

  have len_tys: "length fieldTys = length flds"
    using flds_typed by (induction flds arbitrary: fieldTys) (auto split: option.splits)

  have fields_subst:
    "those (map (\<lambda>(name, tm). core_term_type (apply_subst_to_module_env subst targetEnv env)
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
      hd_typed: "core_term_type env ghost tm = Some hty" and
      rest_typed: "those (map (\<lambda>(n, t). core_term_type env ghost t) flds') = Some rest" and
      fieldTys_eq: "fieldTys = hty # rest"
      by (auto split: option.splits)
    from Cons.prems(2)[of fld hty] fld_eq hd_typed
    have hd_subst:
      "core_term_type (apply_subst_to_module_env subst targetEnv env) ghost
                      (apply_subst_to_term subst tm)
         = Some (apply_subst subst hty)"
      by simp
    have rest_IH:
      "\<And>fld' ty''. fld' \<in> set flds' \<Longrightarrow>
         core_term_type env ghost (snd fld') = Some ty'' \<Longrightarrow>
         core_term_type (apply_subst_to_module_env subst targetEnv env) ghost
                        (apply_subst_to_term subst (snd fld'))
           = Some (apply_subst subst ty'')"
      using Cons.prems(2) by auto
    from Cons.IH[OF rest_typed rest_IH]
    have rest_subst:
      "those (map (\<lambda>(name, tm). core_term_type (apply_subst_to_module_env subst targetEnv env)
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
  from CoreTm_RecordProj.prems(1) obtain fieldTypes where
    inner_typed: "core_term_type env ghost tm = Some (CoreTy_Record fieldTypes)" and
    fld_lookup: "map_of fieldTypes fldName = Some ty"
    by (auto split: option.splits CoreType.splits)
  from CoreTm_RecordProj.IH[OF inner_typed CoreTm_RecordProj.prems(2,3,4)]
  have inner_subst:
    "core_term_type (apply_subst_to_module_env subst targetEnv env) ghost
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
  from CoreTm_ArrayProj.prems(1) obtain elemTy dims where
    inner_typed: "core_term_type env ghost arr = Some (CoreTy_Array elemTy dims)" and
    len_ok: "length idxTms = length dims" and
    idxs_typed: "list_all (\<lambda>tm. core_term_type env ghost tm
                          = Some (CoreTy_FiniteInt Unsigned IntBits_64)) idxTms" and
    ty_eq: "ty = elemTy"
    by (auto split: option.splits CoreType.splits if_splits)
  from CoreTm_ArrayProj.IH(1)[OF inner_typed CoreTm_ArrayProj.prems(2,3,4)]
  have inner_subst:
    "core_term_type (apply_subst_to_module_env subst targetEnv env) ghost
                    (apply_subst_to_term subst arr)
       = Some (CoreTy_Array (apply_subst subst elemTy) dims)"
    by simp
  have idxs_subst:
    "list_all (\<lambda>tm. core_term_type (apply_subst_to_module_env subst targetEnv env) ghost tm
                      = Some (CoreTy_FiniteInt Unsigned IntBits_64))
              (map (apply_subst_to_term subst) idxTms)"
  proof (unfold list_all_iff, intro ballI)
    fix tm' assume "tm' \<in> set (map (apply_subst_to_term subst) idxTms)"
    then obtain tm where tm_in: "tm \<in> set idxTms" and tm'_eq: "tm' = apply_subst_to_term subst tm"
      by auto
    from idxs_typed tm_in have
      tm_typed: "core_term_type env ghost tm = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
      by (simp add: list_all_iff)
    from CoreTm_ArrayProj.IH(2)[OF tm_in tm_typed CoreTm_ArrayProj.prems(2,3,4)]
    show "core_term_type (apply_subst_to_module_env subst targetEnv env) ghost tm'
            = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
      using tm'_eq by simp
  qed
  show ?case
    using inner_subst idxs_subst len_ok ty_eq by simp
next
  case (CoreTm_VariantProj tm ctorName)
  from CoreTm_VariantProj.prems(1) obtain dtName tyArgs tyvars payloadTy where
    inner_typed: "core_term_type env ghost tm = Some (CoreTy_Datatype dtName tyArgs)" and
    ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payloadTy)" and
    len_eq: "length tyArgs = length tyvars" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy"
    by (auto split: option.splits CoreType.splits if_splits prod.splits)

  let ?me = "apply_subst_to_module_env subst targetEnv env"

  from CoreTm_VariantProj.IH[OF inner_typed CoreTm_VariantProj.prems(2,3,4)]
  have inner_subst:
    "core_term_type ?me ghost (apply_subst_to_term subst tm)
       = Some (CoreTy_Datatype dtName (map (apply_subst subst) tyArgs))"
    by simp
  have len_eq_subst: "length (map (apply_subst subst) tyArgs) = length tyvars"
    using len_eq by simp

  have tyvars_distinct: "distinct tyvars"
    using CoreTm_VariantProj.prems(2) ctor_lookup
    unfolding tyenv_well_formed_def tyenv_ctor_tyvars_distinct_def by blast

  have avoid: "subst_names subst |\<inter>| fset_of_list tyvars = {||}"
    using CoreTm_VariantProj.prems(3) ctor_lookup
    unfolding module_env_subst_ok_def by blast

  have ty_subst_eq:
    "apply_subst subst ty
       = apply_subst (fmap_of_list (zip tyvars (map (apply_subst subst) tyArgs)))
                     (apply_subst subst payloadTy)"
    unfolding ty_eq
    using subst_names_avoid_compose[OF len_eq[symmetric] avoid tyvars_distinct]
    by simp

  show ?case
    using inner_subst ctor_lookup len_eq_subst ty_subst_eq by (auto simp: Let_def)
next
  case (CoreTm_Match scrut arms)
  from CoreTm_Match.prems(1) obtain scrutTy where
    scrut_typed: "core_term_type env ghost scrut = Some scrutTy" and
    arms_nonempty: "arms \<noteq> []" and
    pats_compat: "list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst arms)" and
    hd_typed: "core_term_type env ghost (snd (hd arms)) = Some ty" and
    rest_typed: "list_all (\<lambda>body. core_term_type env ghost body = Some ty)
                          (tl (map snd arms))"
    by (auto simp: Let_def split: option.splits if_splits)

  let ?me = "apply_subst_to_module_env subst targetEnv env"
  let ?subst_arms = "map (\<lambda>(pat, body). (pat, apply_subst_to_term subst body)) arms"

  from CoreTm_Match.IH(1)[OF scrut_typed CoreTm_Match.prems(2,3,4)]
  have scrut_subst:
    "core_term_type ?me ghost (apply_subst_to_term subst scrut)
       = Some (apply_subst subst scrutTy)" .

  have arm_IH:
    "\<And>arm ty'. arm \<in> set arms \<Longrightarrow>
       core_term_type env ghost (snd arm) = Some ty' \<Longrightarrow>
       core_term_type ?me ghost (apply_subst_to_term subst (snd arm))
         = Some (apply_subst subst ty')"
    using CoreTm_Match.IH(2) CoreTm_Match.prems(2,3,4)
    by (auto simp: snds.simps)

  have pats_eq: "map fst ?subst_arms = map fst arms"
    by (induction arms) auto

  \<comment> \<open>Pattern compatibility transfers to the substituted env / type, via the
      substituted ctor table and the ctor binder-avoidance clause. \<close>
  have dc_eq: "TE_DataCtors ?me = fmmap (apply_subst_to_datactor subst) (TE_DataCtors env)"
    by simp
  from CoreTm_Match.prems(3) have ctors_avoid:
    "\<forall>ctorName dtName tyVars payload.
        fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload) \<longrightarrow>
        subst_names subst |\<inter>| fset_of_list tyVars = {||}"
    unfolding module_env_subst_ok_def by blast
  have pats_compat_subst:
    "list_all (\<lambda>p. pattern_compatible ?me p (apply_subst subst scrutTy)) (map fst ?subst_arms)"
    using pats_compat pats_eq CoreTm_Match.prems(2)
    by (induction arms)
       (auto intro: pattern_compatible_apply_subst_module[OF _ _ dc_eq ctors_avoid])

  have hd_in: "hd arms \<in> set arms" using arms_nonempty by auto
  from arm_IH[OF hd_in hd_typed]
  have hd_subst:
    "core_term_type ?me ghost (apply_subst_to_term subst (snd (hd arms)))
       = Some (apply_subst subst ty)" .

  have hd_subst_arms_eq:
    "snd (hd ?subst_arms) = apply_subst_to_term subst (snd (hd arms))"
    using arms_nonempty by (cases arms) auto

  have tl_subst:
    "list_all (\<lambda>body. core_term_type ?me ghost body = Some (apply_subst subst ty))
              (tl (map snd ?subst_arms))"
  proof -
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
      from b_in have b_typed: "core_term_type env ghost b = Some ty"
        using rest_typed by (simp add: list_all_iff)
      from b_in arms_nonempty obtain arm where
        arm_in: "arm \<in> set arms" and arm_body: "snd arm = b"
        by (cases arms) auto
      from arm_IH[OF arm_in] b_typed arm_body
      have "core_term_type ?me ghost (apply_subst_to_term subst b)
              = Some (apply_subst subst ty)"
        by simp
      thus "core_term_type ?me ghost b' = Some (apply_subst subst ty)"
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
  from CoreTm_Sizeof.prems(1) obtain elemTy dims where
    inner: "core_term_type env ghost tm = Some (CoreTy_Array elemTy dims)" and
    cond_ok: "\<not> (list_ex (\<lambda>d. d = CoreDim_Allocatable) dims \<and> \<not> is_lvalue tm \<and> ghost = NotGhost)" and
    ty_eq: "ty = sizeof_type dims"
    by (auto split: CoreType.splits option.splits if_splits)
  from CoreTm_Sizeof.IH[OF inner CoreTm_Sizeof.prems(2,3,4)]
  have inner_subst:
    "core_term_type (apply_subst_to_module_env subst targetEnv env) ghost
                    (apply_subst_to_term subst tm)
       = Some (CoreTy_Array (apply_subst subst elemTy) dims)" by simp
  have lvalue_eq: "is_lvalue (apply_subst_to_term subst tm) = is_lvalue tm" by simp
  show ?case using inner_subst cond_ok ty_eq lvalue_eq by simp
next
  case (CoreTm_Allocated tm)
  show ?case
  proof (cases ghost)
    case NotGhost
    with CoreTm_Allocated.prems(1) show ?thesis by simp
  next
    case Ghost
    with CoreTm_Allocated.prems(1) obtain innerTy where
      inner: "core_term_type env Ghost tm = Some innerTy" and
      ty_eq: "ty = CoreTy_Bool"
      by (auto split: option.splits)
    from CoreTm_Allocated.IH[OF inner CoreTm_Allocated.prems(2,3)]
         CoreTm_Allocated.prems(4)
    have "core_term_type (apply_subst_to_module_env subst targetEnv env) Ghost
                          (apply_subst_to_term subst tm)
            = Some (apply_subst subst innerTy)" by simp
    with Ghost ty_eq show ?thesis by simp
  qed
next
  case (CoreTm_Old tm)
  show ?case
  proof (cases ghost)
    case NotGhost
    with CoreTm_Old.prems(1) show ?thesis by simp
  next
    case Ghost
    with CoreTm_Old.prems(1) have inner: "core_term_type env Ghost tm = Some ty" by simp
    from CoreTm_Old.IH[OF inner CoreTm_Old.prems(2,3)]
         CoreTm_Old.prems(4)
    have "core_term_type (apply_subst_to_module_env subst targetEnv env) Ghost
                          (apply_subst_to_term subst tm)
            = Some (apply_subst subst ty)" by simp
    with Ghost show ?thesis by simp
  qed
next
  case (CoreTm_Default tyD)
  from CoreTm_Default.prems(1) have
    wk: "is_well_kinded env tyD" and
    rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env tyD" and
    ty_eq: "ty = tyD"
    by (auto split: if_splits)
  have wk_subst: "is_well_kinded (apply_subst_to_module_env subst targetEnv env)
                                  (apply_subst subst tyD)"
    using apply_subst_preserves_well_kinded_module[OF wk CoreTm_Default.prems(3)] .
  have rt_subst:
    "ghost = NotGhost \<longrightarrow>
       is_runtime_type (apply_subst_to_module_env subst targetEnv env)
                       (apply_subst subst tyD)"
  proof
    assume ng: "ghost = NotGhost"
    with rt have rt': "is_runtime_type env tyD" by simp
    from ng CoreTm_Default.prems(4) have ok_rt: "module_env_subst_runtime_ok subst targetEnv env"
      by simp
    from apply_subst_preserves_runtime_module[OF rt' CoreTm_Default.prems(3) ok_rt]
    show "is_runtime_type (apply_subst_to_module_env subst targetEnv env)
                          (apply_subst subst tyD)" .
  qed
  show ?case using wk_subst rt_subst ty_eq by simp
qed


(* ========================================================================== *)
(* Statement-level helpers                                                    *)
(* ========================================================================== *)

(* ghost_lvalue_ok only reads the env through tyenv_var_ghost, which the
   module-env substitution leaves unchanged. *)
lemma ghost_lvalue_ok_apply_subst_to_module_env [simp]:
  "ghost_lvalue_ok (apply_subst_to_module_env subst targetEnv env) ghost tm
     = ghost_lvalue_ok env ghost tm"
  unfolding ghost_lvalue_ok_def
  by (simp split: option.splits)

(* The module-env substitution commutes with the proof-scope field updates
   that statement typechecking performs. *)
lemma apply_subst_to_module_env_ProofTopLevel [simp]:
  "apply_subst_to_module_env subst targetEnv (env \<lparr> TE_ProofTopLevel := b \<rparr>)
     = apply_subst_to_module_env subst targetEnv env \<lparr> TE_ProofTopLevel := b \<rparr>"
  unfolding apply_subst_to_module_env_def by simp

lemma apply_subst_to_module_env_ProofGoal [simp]:
  "apply_subst_to_module_env subst targetEnv (env \<lparr> TE_ProofGoal := g \<rparr>)
     = apply_subst_to_module_env subst targetEnv env
         \<lparr> TE_ProofGoal := map_option (apply_subst_to_term subst) g \<rparr>"
  unfolding apply_subst_to_module_env_def by simp

(* The substitution side conditions only mention fields that statement
   typechecking leaves fixed, so they transfer along tyenv_fixed_eq
   (core_statement_type_fixed_eq). *)
lemma module_env_subst_ok_fixed_eq:
  assumes "tyenv_fixed_eq env env'"
  shows "module_env_subst_ok subst targetEnv env'
           = module_env_subst_ok subst targetEnv env"
  using assms unfolding module_env_subst_ok_def tyenv_fixed_eq_def by simp

lemma module_env_subst_runtime_ok_fixed_eq:
  assumes "tyenv_fixed_eq env env'"
  shows "module_env_subst_runtime_ok subst targetEnv env'
           = module_env_subst_runtime_ok subst targetEnv env"
  using assms unfolding module_env_subst_runtime_ok_def tyenv_fixed_eq_def by simp

(* Statements typecheck sub-terms in an inner ghost mode that is at least as
   ghostly as the ambient one (ghost = Ghost forces inner = Ghost), so a
   NotGhost-conditional fact at the ambient mode yields the same fact at the
   inner mode. *)
lemma ghost_cond_weaken:
  assumes "ghost = Ghost \<longrightarrow> inner = Ghost"
      and "ghost = NotGhost \<longrightarrow> P"
  shows "inner = NotGhost \<longrightarrow> P"
  using assms by (cases ghost) auto

(* Conditional form of apply_subst_preserves_runtime_module, matching the
   NotGhost-guarded shape the statement cases carry around. *)
lemma apply_subst_preserves_runtime_module_cond:
  assumes "g = NotGhost \<longrightarrow> is_runtime_type env ty"
      and "module_env_subst_ok subst targetEnv env"
      and "g = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv env"
  shows "g = NotGhost \<longrightarrow>
           is_runtime_type (apply_subst_to_module_env subst targetEnv env)
                           (apply_subst subst ty)"
  using assms apply_subst_preserves_runtime_module by blast

(* Valid decreases types contain no type variables, so substitution leaves
   them unchanged. *)
lemma is_valid_decreases_type_apply_subst:
  assumes "is_valid_decreases_type ty"
  shows "apply_subst subst ty = ty"
  using is_valid_decreases_type_no_tyvars[OF assms]
  by (intro apply_subst_disjoint_id) simp

(* The cast on an impure call's return value transfers to the substituted
   env: integer types are closed under substitution, and runtime-ness of the
   cast target transfers via the module conditions. *)
lemma cast_result_type_subst_module_env:
  assumes ct: "cast_result_type env ghost retTy castOpt = Some ty"
      and ok: "module_env_subst_ok subst targetEnv env"
      and ok_rt: "ghost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv env"
  shows "cast_result_type (apply_subst_to_module_env subst targetEnv env) ghost
           (apply_subst subst retTy) (map_option (apply_subst subst) castOpt)
           = Some (apply_subst subst ty)"
proof (cases castOpt)
  case None
  with ct have "ty = retTy" by (simp add: cast_result_type_def)
  with None show ?thesis by (simp add: cast_result_type_def)
next
  case (Some t)
  with ct have
    ret_int: "is_integer_type retTy" and
    t_int: "is_integer_type t" and
    t_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env t" and
    ty_eq: "ty = t"
    by (auto simp: cast_result_type_def split: if_splits)
  have ret_id: "apply_subst subst retTy = retTy"
    using ret_int is_integer_type_apply_subst by simp
  have t_id: "apply_subst subst t = t"
    using t_int is_integer_type_apply_subst by simp
  have t_rt_subst:
    "ghost = NotGhost \<longrightarrow>
       is_runtime_type (apply_subst_to_module_env subst targetEnv env)
                       (apply_subst subst t)"
    using apply_subst_preserves_runtime_module_cond[OF t_rt ok ok_rt] .
  show ?thesis
    using Some ret_int t_int ret_id t_id t_rt_subst ty_eq
    by (simp add: cast_result_type_def)
qed

(* The impure-call typecheck transfers to the substituted module env. Mirrors
   the CoreTm_FunctionCall case of core_term_type_subst_module_env, with the
   extra Var/Ref split: Ref arguments carry lvalue / ghost-discipline checks,
   which substitution leaves unchanged. *)
lemma core_impure_call_type_subst_module_env:
  assumes ct: "core_impure_call_type env ghost fnName tyArgs tmArgs = Some retTy"
      and wf: "tyenv_well_formed env"
      and ok: "module_env_subst_ok subst targetEnv env"
      and ok_rt: "ghost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv env"
  shows "core_impure_call_type (apply_subst_to_module_env subst targetEnv env) ghost
           fnName (map (apply_subst subst) tyArgs) (map (apply_subst_to_term subst) tmArgs)
           = Some (apply_subst subst retTy)"
proof -
  let ?me = "apply_subst_to_module_env subst targetEnv env"
  from core_impure_call_type_fn_facts[OF ct] obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
    len_tyArgs: "length tyArgs = length (FI_TyArgs funInfo)" and
    tyArgs_wk: "list_all (is_well_kinded env) tyArgs" and
    ng_tyArgs: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) tyArgs" and
    ng_fn: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost" and
    len_tmArgs: "length tmArgs = length (FI_TmArgs funInfo)" and
    ty_eq: "retTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                                (FI_ReturnType funInfo)" and
    l2_pure: "list_all2 (\<lambda>tm expectedTy.
                  case core_term_type env ghost tm of
                    None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
                tmArgs
                (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo))" and
    ref_lv: "\<forall>i < length tmArgs.
                snd (FI_TmArgs funInfo ! i) = Ref
                  \<longrightarrow> is_writable_lvalue env (tmArgs ! i)
                      \<and> ghost_lvalue_ok env ghost (tmArgs ! i)"
    by blast

  let ?innerSubst = "fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)"
  let ?subst_tyArgs = "map (apply_subst subst) tyArgs"
  let ?subst_innerSubst = "fmap_of_list (zip (FI_TyArgs funInfo) ?subst_tyArgs)"
  let ?funInfo' = "apply_subst_to_funinfo subst funInfo"

  note call_setup = module_call_subst_setup[OF fn_lookup len_tyArgs tyArgs_wk ng_tyArgs
                                               wf ok ok_rt]
  note fn_lookup_subst   = call_setup(1)
  note tyArgs_wk_subst   = call_setup(2)
  note tyArgs_rt_subst   = call_setup(3)
  note len_tyArgs_subst  = call_setup(4)
  note compose           = call_setup(6)

  have len_tmArgs_subst:
    "length (map (apply_subst_to_term subst) tmArgs) = length (FI_TmArgs ?funInfo')"
    using len_tmArgs by simp

  \<comment> \<open>Function-level bridging equations for the fused map forms the simplifier
      produces from the substituted FunInfo's argument list. \<close>
  have expected_eq:
    "(\<lambda>(ty, _). apply_subst ?subst_innerSubst ty) \<circ> (\<lambda>(ty, vr). (apply_subst subst ty, vr))
       = (\<lambda>(ty, _). apply_subst subst (apply_subst ?innerSubst ty))"
    using compose by (auto simp: fun_eq_iff split: prod.splits)
  have vor_eq:
    "(\<lambda>(_, vor). vor) \<circ> (\<lambda>(ty, vr). (apply_subst subst ty, vr)) = (\<lambda>(_, vor). vor)"
    by (auto simp: fun_eq_iff split: prod.splits)

  have l2_subst:
    "list_all2 (\<lambda>(tm, vor) expectedTy.
                  case vor of
                    Var \<Rightarrow>
                      (case core_term_type ?me ghost tm of
                         None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
                  | Ref \<Rightarrow>
                      is_writable_lvalue ?me tm
                      \<and> ghost_lvalue_ok ?me ghost tm
                      \<and> core_term_type ?me ghost tm = Some expectedTy)
               (zip (map (apply_subst_to_term subst) tmArgs)
                    (map (\<lambda>(_, vor). vor) (FI_TmArgs funInfo)))
               (map (\<lambda>(ty, _). apply_subst subst (apply_subst ?innerSubst ty))
                    (FI_TmArgs funInfo))"
    unfolding list_all2_conv_all_nth
  proof (intro conjI allI impI)
    show "length (zip (map (apply_subst_to_term subst) tmArgs)
                      (map (\<lambda>(_, vor). vor) (FI_TmArgs funInfo)))
            = length (map (\<lambda>(ty, _). apply_subst subst (apply_subst ?innerSubst ty))
                          (FI_TmArgs funInfo))"
      using len_tmArgs by simp
  next
    fix i assume i_lt: "i < length (zip (map (apply_subst_to_term subst) tmArgs)
                                        (map (\<lambda>(_, vor). vor) (FI_TmArgs funInfo)))"
    hence i_lt_tm: "i < length tmArgs" by simp
    with len_tmArgs have i_lt_fi: "i < length (FI_TmArgs funInfo)" by simp
    obtain ti vor where fi_arg_eq: "FI_TmArgs funInfo ! i = (ti, vor)"
      by (cases "FI_TmArgs funInfo ! i") auto
    have zip_nth:
      "zip (map (apply_subst_to_term subst) tmArgs)
           (map (\<lambda>(_, vor). vor) (FI_TmArgs funInfo)) ! i
         = (apply_subst_to_term subst (tmArgs ! i), vor)"
      using i_lt_tm i_lt_fi fi_arg_eq by simp
    have exp_nth:
      "map (\<lambda>(ty, _). apply_subst subst (apply_subst ?innerSubst ty)) (FI_TmArgs funInfo) ! i
         = apply_subst subst (apply_subst ?innerSubst ti)"
      using i_lt_fi fi_arg_eq by simp
    from l2_pure have pure_nth_raw:
      "case core_term_type env ghost (tmArgs ! i) of
         None \<Rightarrow> False
       | Some actualTy \<Rightarrow>
           actualTy = map (\<lambda>(ty, _). apply_subst ?innerSubst ty) (FI_TmArgs funInfo) ! i"
      using i_lt_tm len_tmArgs by (simp add: list_all2_conv_all_nth)
    have pure_nth:
      "case core_term_type env ghost (tmArgs ! i) of
         None \<Rightarrow> False
       | Some actualTy \<Rightarrow> actualTy = apply_subst ?innerSubst ti"
      using pure_nth_raw i_lt_fi fi_arg_eq by (metis case_prod_conv nth_map)
    then obtain actualTy where
      actual_typed: "core_term_type env ghost (tmArgs ! i) = Some actualTy" and
      actual_eq: "actualTy = apply_subst ?innerSubst ti"
      by (auto split: option.splits)
    from core_term_type_subst_module_env[OF actual_typed wf ok ok_rt]
    have ih_typed:
      "core_term_type ?me ghost (apply_subst_to_term subst (tmArgs ! i))
         = Some (apply_subst subst (apply_subst ?innerSubst ti))"
      using actual_eq by simp
    show "(case zip (map (apply_subst_to_term subst) tmArgs)
                    (map (\<lambda>(_, vor). vor) (FI_TmArgs funInfo)) ! i of
             (tm, vor) \<Rightarrow>
               \<lambda>expectedTy.
                 (case vor of
                   Var \<Rightarrow>
                     (case core_term_type ?me ghost tm of
                        None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
                 | Ref \<Rightarrow>
                     is_writable_lvalue ?me tm
                     \<and> ghost_lvalue_ok ?me ghost tm
                     \<and> core_term_type ?me ghost tm = Some expectedTy))
          (map (\<lambda>(ty, _). apply_subst subst (apply_subst ?innerSubst ty))
               (FI_TmArgs funInfo) ! i)"
    proof (cases vor)
      case Var
      with zip_nth exp_nth ih_typed show ?thesis by simp
    next
      case Ref
      have wl: "is_writable_lvalue env (tmArgs ! i)" and
           glv: "ghost_lvalue_ok env ghost (tmArgs ! i)"
        using ref_lv i_lt_tm fi_arg_eq Ref by auto
      have wl': "is_writable_lvalue ?me (apply_subst_to_term subst (tmArgs ! i))"
        using wl by simp
      have glv': "ghost_lvalue_ok ?me ghost (apply_subst_to_term subst (tmArgs ! i))"
        using glv by simp
      with Ref zip_nth exp_nth ih_typed wl' show ?thesis by simp
    qed
  qed

  have ret_compose:
    "apply_subst ?subst_innerSubst (apply_subst subst (FI_ReturnType funInfo))
       = apply_subst subst (apply_subst ?innerSubst (FI_ReturnType funInfo))"
    by (rule compose)

  show ?thesis
    unfolding core_impure_call_type_def
    using fn_lookup_subst len_tyArgs_subst tyArgs_wk_subst tyArgs_rt_subst ng_fn
          len_tmArgs_subst l2_subst ty_eq ret_compose
    by (auto simp: Let_def expected_eq vor_eq)
qed


(* ========================================================================== *)
(* Statement typing under module-env substitution                             *)
(* ========================================================================== *)

(* The statement-level analogue of core_term_type_subst_module_env: if a
   statement typechecks producing envOut, the substituted statement
   typechecks in the substituted env, producing the substituted envOut.
   Same six side conditions as the term lemma. The induction follows the
   mutual structure of core_statement_type / core_statement_list_type
   (mirroring core_statement_type_tyenv_extends, TyEnvExtension.thy). *)
lemma core_statement_type_subst_module_env:
  "core_statement_type env ghost stmt = Some envOut \<Longrightarrow>
   tyenv_well_formed env \<Longrightarrow>
   module_env_subst_ok subst targetEnv env \<Longrightarrow>
   ghost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv env \<Longrightarrow>
   core_statement_type (apply_subst_to_module_env subst targetEnv env) ghost
                       (apply_subst_to_statement subst stmt)
     = Some (apply_subst_to_module_env subst targetEnv envOut)"
and core_statement_list_type_subst_module_env:
  "core_statement_list_type env ghost stmts = Some envOut \<Longrightarrow>
   tyenv_well_formed env \<Longrightarrow>
   module_env_subst_ok subst targetEnv env \<Longrightarrow>
   ghost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv env \<Longrightarrow>
   core_statement_list_type (apply_subst_to_module_env subst targetEnv env) ghost
                            (apply_subst_to_statement_list subst stmts)
     = Some (apply_subst_to_module_env subst targetEnv envOut)"
proof (induction env ghost stmt and env ghost stmts
       arbitrary: envOut and envOut
       rule: core_statement_type_core_statement_list_type.induct)
  \<comment> \<open>VarDecl (Var): adds a local of the substituted declared type.\<close>
  case (1 env ghost declGhost varName varTy initTm)
  note wf = "1.prems"(2) and ok = "1.prems"(3)
  from "1.prems"(1) have
    gh: "ghost = Ghost \<longrightarrow> declGhost = Ghost" and
    wk: "is_well_kinded env varTy" and
    rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy" and
    init: "core_term_type env declGhost initTm = Some varTy" and
    out_eq: "envOut = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                  TE_GhostLocals := (if declGhost = Ghost
                                   then finsert varName (TE_GhostLocals env)
                                   else fminus (TE_GhostLocals env) {|varName|}),
                  TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
    by (auto split: if_splits)
  let ?me = "apply_subst_to_module_env subst targetEnv env"
  have ok_rt_d: "declGhost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv env"
    using ghost_cond_weaken[OF gh "1.prems"(4)] .
  have wk_subst: "is_well_kinded ?me (apply_subst subst varTy)"
    using apply_subst_preserves_well_kinded_module[OF wk ok] .
  have rt_subst: "declGhost = NotGhost \<longrightarrow> is_runtime_type ?me (apply_subst subst varTy)"
    using apply_subst_preserves_runtime_module_cond[OF rt ok ok_rt_d] .
  have init_subst:
    "core_term_type ?me declGhost (apply_subst_to_term subst initTm)
       = Some (apply_subst subst varTy)"
    using core_term_type_subst_module_env[OF init wf ok ok_rt_d] .
  have out_subst_eq:
    "apply_subst_to_module_env subst targetEnv envOut
       = ?me \<lparr> TE_LocalVars := fmupd varName (apply_subst subst varTy) (TE_LocalVars ?me),
               TE_GhostLocals := (if declGhost = Ghost
                                then finsert varName (TE_GhostLocals ?me)
                                else fminus (TE_GhostLocals ?me) {|varName|}),
               TE_ConstLocals := fminus (TE_ConstLocals ?me) {|varName|} \<rparr>"
    unfolding out_eq apply_subst_to_module_env_def by (simp add: fmmap_fmupd)
  show ?case
    using gh wk_subst rt_subst init_subst out_subst_eq by simp
next
  \<comment> \<open>VarDeclCall: impure-call initializer, via the call and cast helpers.\<close>
  case (2 env ghost declGhost varName varTy castOpt fnName tyArgs argTms)
  note wf = "2.prems"(2) and ok = "2.prems"(3)
  from "2.prems"(1) obtain retTy where
    gh: "ghost = Ghost \<longrightarrow> declGhost = Ghost" and
    wk: "is_well_kinded env varTy" and
    rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy" and
    ct: "core_impure_call_type env declGhost fnName tyArgs argTms = Some retTy" and
    cast: "cast_result_type env declGhost retTy castOpt = Some varTy" and
    out_eq: "envOut = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                  TE_GhostLocals := (if declGhost = Ghost
                                   then finsert varName (TE_GhostLocals env)
                                   else fminus (TE_GhostLocals env) {|varName|}),
                  TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
    by (auto split: if_splits option.splits)
  let ?me = "apply_subst_to_module_env subst targetEnv env"
  have ok_rt_d: "declGhost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv env"
    using ghost_cond_weaken[OF gh "2.prems"(4)] .
  have wk_subst: "is_well_kinded ?me (apply_subst subst varTy)"
    using apply_subst_preserves_well_kinded_module[OF wk ok] .
  have rt_subst: "declGhost = NotGhost \<longrightarrow> is_runtime_type ?me (apply_subst subst varTy)"
    using apply_subst_preserves_runtime_module_cond[OF rt ok ok_rt_d] .
  have ct_subst:
    "core_impure_call_type ?me declGhost fnName
       (map (apply_subst subst) tyArgs) (map (apply_subst_to_term subst) argTms)
       = Some (apply_subst subst retTy)"
    using core_impure_call_type_subst_module_env[OF ct wf ok ok_rt_d] .
  have cast_subst:
    "cast_result_type ?me declGhost (apply_subst subst retTy)
       (map_option (apply_subst subst) castOpt)
       = Some (apply_subst subst varTy)"
    using cast_result_type_subst_module_env[OF cast ok ok_rt_d] .
  have out_subst_eq:
    "apply_subst_to_module_env subst targetEnv envOut
       = ?me \<lparr> TE_LocalVars := fmupd varName (apply_subst subst varTy) (TE_LocalVars ?me),
               TE_GhostLocals := (if declGhost = Ghost
                                then finsert varName (TE_GhostLocals ?me)
                                else fminus (TE_GhostLocals ?me) {|varName|}),
               TE_ConstLocals := fminus (TE_ConstLocals ?me) {|varName|} \<rparr>"
    unfolding out_eq apply_subst_to_module_env_def by (simp add: fmmap_fmupd)
  show ?case
    using gh wk_subst rt_subst ct_subst cast_subst out_subst_eq by simp
next
  \<comment> \<open>VarDecl (Ref): the initializer's lvalue-ness / writability / ghost
      discipline are unchanged by substitution.\<close>
  case (3 env ghost declGhost varName varTy initTm)
  note wf = "3.prems"(2) and ok = "3.prems"(3)
  from "3.prems"(1) have
    gh: "ghost = Ghost \<longrightarrow> declGhost = Ghost" and
    wk: "is_well_kinded env varTy" and
    rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy" and
    lv: "is_lvalue initTm" and
    glv: "ghost_lvalue_ok env declGhost initTm" and
    init: "core_term_type env declGhost initTm = Some varTy" and
    out_eq: "envOut = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                  TE_GhostLocals := (if declGhost = Ghost
                                   then finsert varName (TE_GhostLocals env)
                                   else fminus (TE_GhostLocals env) {|varName|}),
                  TE_ConstLocals := (if is_writable_lvalue env initTm
                                    then fminus (TE_ConstLocals env) {|varName|}
                                    else finsert varName (TE_ConstLocals env)) \<rparr>"
    by (auto split: if_splits)
  let ?me = "apply_subst_to_module_env subst targetEnv env"
  have ok_rt_d: "declGhost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv env"
    using ghost_cond_weaken[OF gh "3.prems"(4)] .
  have wk_subst: "is_well_kinded ?me (apply_subst subst varTy)"
    using apply_subst_preserves_well_kinded_module[OF wk ok] .
  have rt_subst: "declGhost = NotGhost \<longrightarrow> is_runtime_type ?me (apply_subst subst varTy)"
    using apply_subst_preserves_runtime_module_cond[OF rt ok ok_rt_d] .
  have init_subst:
    "core_term_type ?me declGhost (apply_subst_to_term subst initTm)
       = Some (apply_subst subst varTy)"
    using core_term_type_subst_module_env[OF init wf ok ok_rt_d] .
  have out_subst_eq:
    "apply_subst_to_module_env subst targetEnv envOut
       = ?me \<lparr> TE_LocalVars := fmupd varName (apply_subst subst varTy) (TE_LocalVars ?me),
               TE_GhostLocals := (if declGhost = Ghost
                                then finsert varName (TE_GhostLocals ?me)
                                else fminus (TE_GhostLocals ?me) {|varName|}),
               TE_ConstLocals := (if is_writable_lvalue env initTm
                                 then fminus (TE_ConstLocals ?me) {|varName|}
                                 else finsert varName (TE_ConstLocals ?me)) \<rparr>"
    unfolding out_eq apply_subst_to_module_env_def by (simp add: fmmap_fmupd)
  show ?case
    using gh wk_subst rt_subst lv glv init_subst out_subst_eq by simp
next
  \<comment> \<open>Assign: env unchanged.\<close>
  case (4 env ghost assignGhost lhsTm rhsTm)
  note wf = "4.prems"(2) and ok = "4.prems"(3)
  from "4.prems"(1) obtain lhsTy where
    gh: "ghost = Ghost \<longrightarrow> assignGhost = Ghost" and
    wl: "is_writable_lvalue env lhsTm" and
    glv: "ghost_lvalue_ok env assignGhost lhsTm" and
    lhs: "core_term_type env assignGhost lhsTm = Some lhsTy" and
    rhs: "core_term_type env assignGhost rhsTm = Some lhsTy" and
    out_eq: "envOut = env"
    by (auto split: if_splits option.splits)
  let ?me = "apply_subst_to_module_env subst targetEnv env"
  have ok_rt_a: "assignGhost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv env"
    using ghost_cond_weaken[OF gh "4.prems"(4)] .
  have lhs_subst:
    "core_term_type ?me assignGhost (apply_subst_to_term subst lhsTm)
       = Some (apply_subst subst lhsTy)"
    using core_term_type_subst_module_env[OF lhs wf ok ok_rt_a] .
  have rhs_subst:
    "core_term_type ?me assignGhost (apply_subst_to_term subst rhsTm)
       = Some (apply_subst subst lhsTy)"
    using core_term_type_subst_module_env[OF rhs wf ok ok_rt_a] .
  show ?case
    using gh wl glv lhs_subst rhs_subst out_eq by simp
next
  \<comment> \<open>AssignCall: env unchanged; lhs term plus the call and cast helpers.\<close>
  case (5 env ghost assignGhost lhsTm castOpt fnName tyArgs argTms)
  note wf = "5.prems"(2) and ok = "5.prems"(3)
  \<comment> \<open>Staged extraction (one case-split per step): a single auto over the
      nested if/option splits blows up here, as in
      core_statement_type_tyenv_extends. \<close>
  from "5.prems"(1) have
    pre: "(ghost = Ghost \<longrightarrow> assignGhost = Ghost) \<and> is_writable_lvalue env lhsTm
            \<and> ghost_lvalue_ok env assignGhost lhsTm"
    by (simp split: if_splits)
  hence gh: "ghost = Ghost \<longrightarrow> assignGhost = Ghost" and wl: "is_writable_lvalue env lhsTm"
    and glv: "ghost_lvalue_ok env assignGhost lhsTm"
    by simp_all
  from "5.prems"(1) pre obtain lhsTy where
    lhs: "core_term_type env assignGhost lhsTm = Some lhsTy"
    by (simp split: option.splits)
  from "5.prems"(1) pre lhs obtain retTy where
    ct: "core_impure_call_type env assignGhost fnName tyArgs argTms = Some retTy"
    by (simp split: option.splits)
  from "5.prems"(1) pre lhs ct have
    cast: "cast_result_type env assignGhost retTy castOpt = Some lhsTy" and
    out_eq: "envOut = env"
    by (simp split: if_splits)+
  let ?me = "apply_subst_to_module_env subst targetEnv env"
  have ok_rt_a: "assignGhost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv env"
    using ghost_cond_weaken[OF gh "5.prems"(4)] .
  have lhs_subst:
    "core_term_type ?me assignGhost (apply_subst_to_term subst lhsTm)
       = Some (apply_subst subst lhsTy)"
    using core_term_type_subst_module_env[OF lhs wf ok ok_rt_a] .
  have ct_subst:
    "core_impure_call_type ?me assignGhost fnName
       (map (apply_subst subst) tyArgs) (map (apply_subst_to_term subst) argTms)
       = Some (apply_subst subst retTy)"
    using core_impure_call_type_subst_module_env[OF ct wf ok ok_rt_a] .
  have cast_subst:
    "cast_result_type ?me assignGhost (apply_subst subst retTy)
       (map_option (apply_subst subst) castOpt)
       = Some (apply_subst subst lhsTy)"
    using cast_result_type_subst_module_env[OF cast ok ok_rt_a] .
  show ?case
    using gh wl glv lhs_subst ct_subst cast_subst out_eq by simp
next
  \<comment> \<open>Return: the substituted env's return type is the substituted return type.\<close>
  case (6 env ghost tm)
  note wf = "6.prems"(2) and ok = "6.prems"(3)
  from "6.prems"(1) have
    gh: "ghost = TE_FunctionGhost env" and
    tm_typed: "core_term_type env ghost tm = Some (TE_ReturnType env)" and
    out_eq: "envOut = env"
    by (auto split: if_splits)
  let ?me = "apply_subst_to_module_env subst targetEnv env"
  have tm_subst:
    "core_term_type ?me ghost (apply_subst_to_term subst tm)
       = Some (apply_subst subst (TE_ReturnType env))"
    using core_term_type_subst_module_env[OF tm_typed wf ok "6.prems"(4)] .
  show ?case
    using gh tm_subst out_eq by simp
next
  \<comment> \<open>Swap: env unchanged; both sides writable lvalues of the same type.\<close>
  case (7 env ghost swapGhost lhsTm rhsTm)
  note wf = "7.prems"(2) and ok = "7.prems"(3)
  from "7.prems"(1) obtain lhsTy where
    gh: "ghost = Ghost \<longrightarrow> swapGhost = Ghost" and
    wl_l: "is_writable_lvalue env lhsTm" and
    wl_r: "is_writable_lvalue env rhsTm" and
    glv_l: "ghost_lvalue_ok env swapGhost lhsTm" and
    glv_r: "ghost_lvalue_ok env swapGhost rhsTm" and
    lhs: "core_term_type env swapGhost lhsTm = Some lhsTy" and
    rhs: "core_term_type env swapGhost rhsTm = Some lhsTy" and
    out_eq: "envOut = env"
    by (auto split: if_splits option.splits)
  let ?me = "apply_subst_to_module_env subst targetEnv env"
  have ok_rt_s: "swapGhost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv env"
    using ghost_cond_weaken[OF gh "7.prems"(4)] .
  have lhs_subst:
    "core_term_type ?me swapGhost (apply_subst_to_term subst lhsTm)
       = Some (apply_subst subst lhsTy)"
    using core_term_type_subst_module_env[OF lhs wf ok ok_rt_s] .
  have rhs_subst:
    "core_term_type ?me swapGhost (apply_subst_to_term subst rhsTm)
       = Some (apply_subst subst lhsTy)"
    using core_term_type_subst_module_env[OF rhs wf ok ok_rt_s] .
  show ?case
    using gh wl_l wl_r glv_l glv_r lhs_subst rhs_subst out_eq by simp
next
  \<comment> \<open>Assert: the proof body runs in Ghost mode under the goal env; the
      substituted goal env is the module-env substitution of the goal env.\<close>
  case (8 env ghost condOpt proofBody)
  note wf = "8.prems"(2) and ok = "8.prems"(3)
  let ?me = "apply_subst_to_module_env subst targetEnv env"
  let ?goalEnv = "env \<lparr> TE_ProofGoal := (case condOpt of Some condTm \<Rightarrow> Some condTm
                                        | None \<Rightarrow> TE_ProofGoal env),
                       TE_ProofTopLevel := True \<rparr>"
  from "8.prems"(1) obtain bodyEnv where
    condOk: "(case condOpt of
                Some condTm \<Rightarrow> core_term_type env Ghost condTm = Some CoreTy_Bool
              | None \<Rightarrow> TE_ProofGoal env \<noteq> None)" and
    body: "core_statement_list_type ?goalEnv Ghost proofBody = Some bodyEnv" and
    out_eq: "envOut = env"
    by (auto simp: Let_def split: if_splits option.splits)
  have wf_goal: "tyenv_well_formed ?goalEnv"
    using tyenv_well_formed_TE_ProofTopLevel_irrelevant[OF
            tyenv_well_formed_TE_ProofGoal_irrelevant[OF wf]]
    by simp
  have ok_goal: "module_env_subst_ok subst targetEnv ?goalEnv"
    using ok unfolding module_env_subst_ok_def by simp
  have triv_ok_rt: "Ghost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv ?goalEnv"
    by simp
  from "8.IH"[OF refl refl refl condOk body wf_goal ok_goal triv_ok_rt]
  have body_subst:
    "core_statement_list_type (apply_subst_to_module_env subst targetEnv ?goalEnv) Ghost
                              (apply_subst_to_statement_list subst proofBody)
       = Some (apply_subst_to_module_env subst targetEnv bodyEnv)" .
  have goal_env_subst:
    "apply_subst_to_module_env subst targetEnv ?goalEnv
       = ?me \<lparr> TE_ProofGoal := (case map_option (apply_subst_to_term subst) condOpt of
                                  Some condTm' \<Rightarrow> Some condTm'
                                | None \<Rightarrow> TE_ProofGoal ?me),
               TE_ProofTopLevel := True \<rparr>"
    unfolding apply_subst_to_module_env_def by (cases condOpt) auto
  have condOk_subst:
    "(case map_option (apply_subst_to_term subst) condOpt of
        Some condTm' \<Rightarrow> core_term_type ?me Ghost condTm' = Some CoreTy_Bool
      | None \<Rightarrow> TE_ProofGoal ?me \<noteq> None)"
  proof (cases condOpt)
    case None
    with condOk show ?thesis by simp
  next
    case (Some condTm)
    with condOk have c: "core_term_type env Ghost condTm = Some CoreTy_Bool" by simp
    have triv_ok_rt': "Ghost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv env"
      by simp
    from core_term_type_subst_module_env[OF c wf ok triv_ok_rt']
    show ?thesis using Some by simp
  qed
  show ?case
    using condOk_subst body_subst goal_env_subst out_eq
    by (simp add: Let_def split: option.splits)
next
  \<comment> \<open>Assume: env unchanged; the condition is Ghost-checked.\<close>
  case (9 env ghost tm)
  note wf = "9.prems"(2) and ok = "9.prems"(3)
  from "9.prems"(1) have
    tm_typed: "core_term_type env Ghost tm = Some CoreTy_Bool" and
    out_eq: "envOut = env"
    by (auto split: if_splits)
  have triv_ok_rt: "Ghost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv env"
    by simp
  from core_term_type_subst_module_env[OF tm_typed wf ok triv_ok_rt]
  have tm_subst:
    "core_term_type (apply_subst_to_module_env subst targetEnv env) Ghost
                    (apply_subst_to_term subst tm)
       = Some CoreTy_Bool"
    by simp
  show ?case
    using tm_subst out_eq by simp
next
  \<comment> \<open>ShowHide: no checks, statement unchanged by substitution.\<close>
  case (10 env ghost sh name)
  from "10.prems"(1) have "envOut = env" by simp
  then show ?case by simp
next
  \<comment> \<open>Match: patterns are untouched by substitution; their compatibility
      transfers via the substituted ctor table. Arm bodies are checked under
      TE_ProofTopLevel := False, which commutes with the substitution.\<close>
  case (11 env ghost matchGhost scrut arms)
  note wf = "11.prems"(2) and ok = "11.prems"(3)
  let ?me = "apply_subst_to_module_env subst targetEnv env"
  let ?envF = "env \<lparr> TE_ProofTopLevel := False \<rparr>"
  let ?subst_arms = "map (\<lambda>(pat, body). (pat, apply_subst_to_statement_list subst body)) arms"
  from "11.prems"(1) obtain scrutTy where
    gh: "ghost = Ghost \<longrightarrow> matchGhost = Ghost" and
    scrut: "core_term_type env matchGhost scrut = Some scrutTy" and
    pats: "list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst arms)" and
    bodies: "list_all (\<lambda>body. core_statement_list_type ?envF matchGhost body \<noteq> None)
                      (map snd arms)" and
    out_eq: "envOut = env"
    by (auto simp: Let_def split: if_splits option.splits)
  have pats_nn: "\<not> \<not> list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst arms)"
    using pats by simp
  have ok_rt_m: "matchGhost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv env"
    using ghost_cond_weaken[OF gh "11.prems"(4)] .
  have scrut_subst:
    "core_term_type ?me matchGhost (apply_subst_to_term subst scrut)
       = Some (apply_subst subst scrutTy)"
    using core_term_type_subst_module_env[OF scrut wf ok ok_rt_m] .
  \<comment> \<open>Function-level bridging equations: the simplifier fuses the arm
      projections to \<open>map (fst \<circ> \<dots>)\<close> / \<open>map (snd \<circ> \<dots>)\<close> forms, so the
      equations must be stated at the composition level to rewrite them. \<close>
  have fst_comp_eq:
    "fst \<circ> (\<lambda>(pat, body). (pat, apply_subst_to_statement_list subst body)) = fst"
    by (auto simp: fun_eq_iff split: prod.splits)
  have snd_comp_eq:
    "snd \<circ> (\<lambda>(pat, body). (pat, apply_subst_to_statement_list subst body))
       = apply_subst_to_statement_list subst \<circ> snd"
    by (auto simp: fun_eq_iff split: prod.splits)
  have dc_eq: "TE_DataCtors ?me = fmmap (apply_subst_to_datactor subst) (TE_DataCtors env)"
    by simp
  from ok have ctors_avoid:
    "\<forall>ctorName dtName tyVars payload.
        fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload) \<longrightarrow>
        subst_names subst |\<inter>| fset_of_list tyVars = {||}"
    unfolding module_env_subst_ok_def by blast
  have pats_compat_subst:
    "list_all (\<lambda>p. pattern_compatible ?me p (apply_subst subst scrutTy)) (map fst arms)"
    using pats wf
    by (induction arms)
       (auto intro: pattern_compatible_apply_subst_module[OF _ _ dc_eq ctors_avoid])
  have wf_F: "tyenv_well_formed ?envF"
    using tyenv_well_formed_TE_ProofTopLevel_irrelevant[OF wf] .
  have ok_F: "module_env_subst_ok subst targetEnv ?envF"
    using ok unfolding module_env_subst_ok_def by simp
  have ok_rt_F: "matchGhost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv ?envF"
    using ok_rt_m unfolding module_env_subst_runtime_ok_def by simp
  have bodies_subst:
    "list_all (\<lambda>body. core_statement_list_type (?me \<lparr> TE_ProofTopLevel := False \<rparr>)
                        matchGhost body \<noteq> None)
              (map (apply_subst_to_statement_list subst) (map snd arms))"
    unfolding list_all_iff
  proof (rule ballI)
    fix body' assume "body' \<in> set (map (apply_subst_to_statement_list subst) (map snd arms))"
    then obtain body where
      body_in: "body \<in> set (map snd arms)" and
      body'_eq: "body' = apply_subst_to_statement_list subst body"
      by auto
    from bodies[unfolded list_all_iff] body_in
    have "core_statement_list_type ?envF matchGhost body \<noteq> None" by blast
    then obtain bEnv where
      bsome: "core_statement_list_type ?envF matchGhost body = Some bEnv"
      by blast
    from "11.IH"[OF gh scrut refl refl pats_nn body_in bsome
                    wf_F ok_F ok_rt_F]
    have "core_statement_list_type (apply_subst_to_module_env subst targetEnv ?envF)
            matchGhost (apply_subst_to_statement_list subst body)
            = Some (apply_subst_to_module_env subst targetEnv bEnv)" .
    thus "core_statement_list_type (?me \<lparr> TE_ProofTopLevel := False \<rparr>) matchGhost body'
            \<noteq> None"
      using body'_eq by simp
  qed
  show ?case
    using gh scrut_subst pats_compat_subst bodies_subst out_eq
    by (simp add: Let_def fst_comp_eq snd_comp_eq)
next
  \<comment> \<open>While: the decreases type contains no tyvars, so it is unchanged; the
      body is checked under TE_ProofTopLevel := False.\<close>
  case (12 env ghost whileGhost condTm invars decrTm body)
  note wf = "12.prems"(2) and ok = "12.prems"(3)
  let ?me = "apply_subst_to_module_env subst targetEnv env"
  let ?envF = "env \<lparr> TE_ProofTopLevel := False \<rparr>"
  from "12.prems"(1) obtain decrTy bodyEnv where
    gh: "ghost = Ghost \<longrightarrow> whileGhost = Ghost" and
    cond: "core_term_type env whileGhost condTm = Some CoreTy_Bool" and
    invs: "list_all (\<lambda>inv. core_term_type env Ghost inv = Some CoreTy_Bool) invars" and
    decr: "core_term_type env Ghost decrTm = Some decrTy" and
    decr_valid: "is_valid_decreases_type decrTy" and
    body_typed: "core_statement_list_type ?envF whileGhost body = Some bodyEnv" and
    out_eq: "envOut = env"
    by (auto split: if_splits option.splits CoreType.splits)
  have ok_rt_w: "whileGhost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv env"
    using ghost_cond_weaken[OF gh "12.prems"(4)] .
  have cond_subst:
    "core_term_type ?me whileGhost (apply_subst_to_term subst condTm) = Some CoreTy_Bool"
    using core_term_type_subst_module_env[OF cond wf ok ok_rt_w]
    by simp
  have triv_ok_rt: "Ghost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv env"
    by simp
  have invs_subst:
    "list_all (\<lambda>inv. core_term_type ?me Ghost inv = Some CoreTy_Bool)
              (map (apply_subst_to_term subst) invars)"
    unfolding list_all_iff
  proof (rule ballI)
    fix inv' assume "inv' \<in> set (map (apply_subst_to_term subst) invars)"
    then obtain inv where
      inv_in: "inv \<in> set invars" and inv'_eq: "inv' = apply_subst_to_term subst inv"
      by auto
    from invs inv_in have "core_term_type env Ghost inv = Some CoreTy_Bool"
      by (simp add: list_all_iff)
    from core_term_type_subst_module_env[OF this wf ok triv_ok_rt]
    show "core_term_type ?me Ghost inv' = Some CoreTy_Bool"
      using inv'_eq by simp
  qed
  have decr_subst:
    "core_term_type ?me Ghost (apply_subst_to_term subst decrTm) = Some decrTy"
    using core_term_type_subst_module_env[OF decr wf ok triv_ok_rt]
          is_valid_decreases_type_apply_subst[OF decr_valid]
    by simp
  have wf_F: "tyenv_well_formed ?envF"
    using tyenv_well_formed_TE_ProofTopLevel_irrelevant[OF wf] .
  have ok_F: "module_env_subst_ok subst targetEnv ?envF"
    using ok unfolding module_env_subst_ok_def by simp
  have ok_rt_F: "whileGhost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv ?envF"
    using ok_rt_w unfolding module_env_subst_runtime_ok_def by simp
  from "12.IH"[OF gh cond refl invs decr decr_valid body_typed
                  wf_F ok_F ok_rt_F]
  have body_subst:
    "core_statement_list_type (?me \<lparr> TE_ProofTopLevel := False \<rparr>) whileGhost
                              (apply_subst_to_statement_list subst body)
       = Some (apply_subst_to_module_env subst targetEnv bodyEnv)"
    by simp
  show ?case
    using gh cond_subst invs_subst decr_subst decr_valid body_subst out_eq by simp
next
  \<comment> \<open>Obtain: adds a ghost local; the condition is checked in the extended env.\<close>
  case (13 env ghost varName varTy condTm)
  note wf = "13.prems"(2) and ok = "13.prems"(3)
  let ?me = "apply_subst_to_module_env subst targetEnv env"
  let ?envX = "env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                     TE_GhostLocals := finsert varName (TE_GhostLocals env),
                     TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
  from "13.prems"(1) have
    wk: "is_well_kinded env varTy" and
    cond: "core_term_type ?envX Ghost condTm = Some CoreTy_Bool" and
    out_eq: "envOut = ?envX"
    by (auto simp: Let_def split: if_splits)
  have wk_subst: "is_well_kinded ?me (apply_subst subst varTy)"
    using apply_subst_preserves_well_kinded_module[OF wk ok] .
  have wf_X: "tyenv_well_formed ?envX"
  proof -
    from tyenv_well_formed_add_ghost_var[OF wf wk]
    have wf': "tyenv_well_formed
                 (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                        TE_GhostLocals := finsert varName (TE_GhostLocals env) \<rparr>)" .
    from tyenv_well_formed_TE_ConstLocals_irrelevant[OF wf',
            of "fminus (TE_ConstLocals env) {|varName|}"]
    show ?thesis by simp
  qed
  have ok_X: "module_env_subst_ok subst targetEnv ?envX"
    using ok unfolding module_env_subst_ok_def by simp
  have triv_ok_rt: "Ghost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv ?envX"
    by simp
  from core_term_type_subst_module_env[OF cond wf_X ok_X triv_ok_rt]
  have cond_subst:
    "core_term_type (apply_subst_to_module_env subst targetEnv ?envX) Ghost
                    (apply_subst_to_term subst condTm)
       = Some CoreTy_Bool"
    by simp
  have X_subst_eq:
    "apply_subst_to_module_env subst targetEnv ?envX
       = ?me \<lparr> TE_LocalVars := fmupd varName (apply_subst subst varTy) (TE_LocalVars ?me),
               TE_GhostLocals := finsert varName (TE_GhostLocals ?me),
               TE_ConstLocals := fminus (TE_ConstLocals ?me) {|varName|} \<rparr>"
    unfolding apply_subst_to_module_env_def by (simp add: fmmap_fmupd)
  show ?case
    using wk_subst cond_subst X_subst_eq out_eq by (simp add: Let_def)
next
  \<comment> \<open>Fix: needs a Quant_Forall goal; the substituted goal's bound type is the
      substituted declared type, so the equality check transfers.\<close>
  case (14 env ghost varName varTy)
  note wf = "14.prems"(2) and ok = "14.prems"(3)
  let ?me = "apply_subst_to_module_env subst targetEnv env"
  from "14.prems"(1) obtain qName bodyTm where
    goal: "TE_ProofGoal env = Some (CoreTm_Quantifier Quant_Forall qName varTy bodyTm)" and
    gh: "ghost = Ghost" and
    wk: "is_well_kinded env varTy" and
    topLevel: "TE_ProofTopLevel env" and
    out_eq: "envOut = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                            TE_GhostLocals := finsert varName (TE_GhostLocals env),
                            TE_ConstLocals := finsert varName (TE_ConstLocals env),
                            TE_ProofGoal := Some bodyTm \<rparr>"
    by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
  have wk_subst: "is_well_kinded ?me (apply_subst subst varTy)"
    using apply_subst_preserves_well_kinded_module[OF wk ok] .
  have out_subst_eq:
    "apply_subst_to_module_env subst targetEnv envOut
       = ?me \<lparr> TE_LocalVars := fmupd varName (apply_subst subst varTy) (TE_LocalVars ?me),
               TE_GhostLocals := finsert varName (TE_GhostLocals ?me),
               TE_ConstLocals := finsert varName (TE_ConstLocals ?me),
               TE_ProofGoal := Some (apply_subst_to_term subst bodyTm) \<rparr>"
    unfolding out_eq apply_subst_to_module_env_def by (simp add: fmmap_fmupd)
  \<comment> \<open>Pass the PLAIN goal lookup (over TE_ProofGoal env), not the substituted
      one: the substituted-site case expression normalizes to
      \<open>case TE_ProofGoal env of \<dots>\<close>, which the plain fact reduces directly. \<close>
  show ?case
    using goal gh wk_subst topLevel out_subst_eq by simp
next
  \<comment> \<open>Use: needs a Quant_Exists goal; the witness's substituted type matches
      the substituted bound type.\<close>
  case (15 env ghost witnessTm)
  note wf = "15.prems"(2) and ok = "15.prems"(3)
  let ?me = "apply_subst_to_module_env subst targetEnv env"
  from "15.prems"(1) obtain qName qVarTy bodyTm where
    goal: "TE_ProofGoal env = Some (CoreTm_Quantifier Quant_Exists qName qVarTy bodyTm)" and
    gh: "ghost = Ghost" and
    wit: "core_term_type env ghost witnessTm = Some qVarTy" and
    topLevel: "TE_ProofTopLevel env" and
    out_eq: "envOut = env \<lparr> TE_ProofGoal := Some bodyTm \<rparr>"
    by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
  have wit_subst:
    "core_term_type ?me ghost (apply_subst_to_term subst witnessTm)
       = Some (apply_subst subst qVarTy)"
    using core_term_type_subst_module_env[OF wit wf ok "15.prems"(4)] .
  have out_subst_eq:
    "apply_subst_to_module_env subst targetEnv envOut
       = ?me \<lparr> TE_ProofGoal := Some (apply_subst_to_term subst bodyTm) \<rparr>"
    unfolding out_eq by simp
  \<comment> \<open>As in the Fix case, pass the PLAIN goal lookup rather than the
      substituted one. \<close>
  show ?case
    using goal gh wit_subst topLevel out_subst_eq by simp
next
  \<comment> \<open>Block: body checked under TE_ProofTopLevel := False at the ambient mode.\<close>
  case (16 env ghost body)
  note wf = "16.prems"(2) and ok = "16.prems"(3)
  let ?me = "apply_subst_to_module_env subst targetEnv env"
  let ?envF = "env \<lparr> TE_ProofTopLevel := False \<rparr>"
  from "16.prems"(1) obtain bodyEnv where
    body_typed: "core_statement_list_type ?envF ghost body = Some bodyEnv" and
    out_eq: "envOut = env"
    by (auto split: option.splits)
  have wf_F: "tyenv_well_formed ?envF"
    using tyenv_well_formed_TE_ProofTopLevel_irrelevant[OF wf] .
  have ok_F: "module_env_subst_ok subst targetEnv ?envF"
    using ok unfolding module_env_subst_ok_def by simp
  have ok_rt_F: "ghost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv ?envF"
    using "16.prems"(4) unfolding module_env_subst_runtime_ok_def by simp
  from "16.IH"[OF body_typed wf_F ok_F ok_rt_F]
  have body_subst:
    "core_statement_list_type (?me \<lparr> TE_ProofTopLevel := False \<rparr>) ghost
                              (apply_subst_to_statement_list subst body)
       = Some (apply_subst_to_module_env subst targetEnv bodyEnv)"
    by simp
  show ?case
    using body_subst out_eq by simp
next
  \<comment> \<open>Empty statement list.\<close>
  case (17 env ghost)
  from "17.prems"(1) have "envOut = env" by simp
  then show ?case by simp
next
  \<comment> \<open>Cons: the side conditions transfer to the intermediate env because
      statement typechecking preserves well-formedness and the fixed fields.\<close>
  case (18 env ghost stmt stmts)
  from "18.prems"(1) obtain envMid where
    head: "core_statement_type env ghost stmt = Some envMid" and
    tail: "core_statement_list_type envMid ghost stmts = Some envOut"
    by (auto split: option.splits)
  from "18.IH"(1)[OF head "18.prems"(2,3,4)]
  have head_subst:
    "core_statement_type (apply_subst_to_module_env subst targetEnv env) ghost
                         (apply_subst_to_statement subst stmt)
       = Some (apply_subst_to_module_env subst targetEnv envMid)" .
  have wf_mid: "tyenv_well_formed envMid"
    using core_statement_type_preserves_well_formed[OF head "18.prems"(2)] .
  note fixed_mid = core_statement_type_fixed_eq[OF head]
  have ok_mid: "module_env_subst_ok subst targetEnv envMid"
    using "18.prems"(3) module_env_subst_ok_fixed_eq[OF fixed_mid] by simp
  have ok_rt_mid: "ghost = NotGhost \<longrightarrow> module_env_subst_runtime_ok subst targetEnv envMid"
    using "18.prems"(4) module_env_subst_runtime_ok_fixed_eq[OF fixed_mid] by simp
  from "18.IH"(2)[OF head tail wf_mid ok_mid ok_rt_mid]
  have tail_subst:
    "core_statement_list_type (apply_subst_to_module_env subst targetEnv envMid) ghost
                              (apply_subst_to_statement_list subst stmts)
       = Some (apply_subst_to_module_env subst targetEnv envOut)" .
  show ?case
    using head_subst tail_subst by simp
qed


(* ========================================================================== *)
(* Preservation of tyenv_well_formed                                          *)
(*                                                                            *)
(* The companion to the typing engines above: under the same side conditions, *)
(* apply_subst_to_module_env carries a well-formed environment to a           *)
(* well-formed environment. Three extra hypotheses pin down the module-level  *)
(* setting in which the lemma is used:                                        *)
(*   - TE_AbstractTypes env = TE_TypeVars env: at module level every in-scope *)
(*     type variable is an abstract type (normalized_module_well_typed's      *)
(*     first clause), which collapses the "TE_TypeVars := TE_AbstractTypes"   *)
(*     overrides inside the tyenv_well_formed clauses to congruences;         *)
(*   - the same equation for targetEnv (link_result installs it); and         *)
(*   - TE_RuntimeTypeVars targetEnv |\<subseteq>| TE_TypeVars targetEnv (the target's   *)
(*     own tyenv_runtime_tyvars_subset clause), needed to collapse the        *)
(*     "TE_AbstractTypes |\<inter>| TE_RuntimeTypeVars" intersections on the target  *)
(*     side.                                                                  *)
(* module_env_subst_runtime_ok is required unconditionally here (not gated on *)
(* a ghost mode) because tyenv_well_formed's runtime clauses are themselves   *)
(* unconditional.                                                             *)
(* ========================================================================== *)

(* Binder-extended form of apply_subst_preserves_well_kinded_module: lifts
   well-kindedness of a type under extra bound type parameters (a function's
   FI_TyArgs or a data constructor's tyvars), provided the substitution's
   name set avoids the binders - which module_env_subst_ok guarantees at
   every function/ctor entry. *)
lemma apply_subst_preserves_well_kinded_module_binders:
  assumes wk: "is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list binders \<rparr>) ty"
      and ok: "module_env_subst_ok subst targetEnv env"
      and avoid: "subst_names subst |\<inter>| fset_of_list binders = {||}"
  shows "is_well_kinded
           (targetEnv \<lparr> TE_TypeVars := TE_TypeVars targetEnv |\<union>| fset_of_list binders \<rparr>)
           (apply_subst subst ty)"
proof (rule apply_subst_preserves_well_kinded[OF wk])
  show "TE_Datatypes (targetEnv \<lparr> TE_TypeVars := TE_TypeVars targetEnv |\<union>| fset_of_list binders \<rparr>)
          = TE_Datatypes (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list binders \<rparr>)"
    using ok unfolding module_env_subst_ok_def by simp
next
  fix n assume "n |\<in>| TE_TypeVars (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list binders \<rparr>)"
  hence n_in: "n |\<in>| TE_TypeVars env \<or> n \<in> set binders"
    by (auto simp: fset_of_list_elem)
  show "case fmlookup subst n of
          Some ty' \<Rightarrow> is_well_kinded
                        (targetEnv \<lparr> TE_TypeVars := TE_TypeVars targetEnv |\<union>| fset_of_list binders \<rparr>) ty'
        | None \<Rightarrow> n |\<in>| TE_TypeVars
                        (targetEnv \<lparr> TE_TypeVars := TE_TypeVars targetEnv |\<union>| fset_of_list binders \<rparr>)"
  proof (cases "n \<in> set binders")
    case True
    \<comment> \<open>A binder is untouched by the substitution (its domain is part of
        subst_names) and survives into the extended target scope.\<close>
    have n_none: "fmlookup subst n = None"
    proof (cases "fmlookup subst n")
      case None thus ?thesis .
    next
      case (Some ty')
      hence "n |\<in>| fmdom subst" by (rule fmdomI)
      hence "n |\<in>| subst_names subst" unfolding subst_names_def by simp
      with True avoid show ?thesis
        by (metis fempty_iff finterI fset_of_list_elem)
    qed
    show ?thesis using True by (simp add: n_none fset_of_list_elem)
  next
    case False
    with n_in have n_env: "n |\<in>| TE_TypeVars env" by (simp add: fset_of_list_elem)
    hence cov: "case fmlookup subst n of
                  Some ty' \<Rightarrow> is_well_kinded targetEnv ty'
                | None \<Rightarrow> n |\<in>| TE_TypeVars targetEnv"
      using ok unfolding module_env_subst_ok_def by blast
    show ?thesis
    proof (cases "fmlookup subst n")
      case None
      with cov show ?thesis by simp
    next
      case (Some ty')
      with cov have wk_t: "is_well_kinded targetEnv ty'" by simp
      have "is_well_kinded (targetEnv \<lparr> TE_TypeVars := TE_TypeVars targetEnv |\<union>| fset_of_list binders \<rparr>) ty'"
      proof (rule is_well_kinded_transfer[OF wk_t])
        show "type_tyvars ty' \<subseteq> fset (TE_TypeVars
                (targetEnv \<lparr> TE_TypeVars := TE_TypeVars targetEnv |\<union>| fset_of_list binders \<rparr>))"
          using is_well_kinded_type_tyvars_subset[OF wk_t] by auto
        show "TE_Datatypes (targetEnv \<lparr> TE_TypeVars := TE_TypeVars targetEnv |\<union>| fset_of_list binders \<rparr>)
                = TE_Datatypes targetEnv"
          by simp
      qed
      with Some show ?thesis by simp
    qed
  qed
qed

(* Runtime analogue of the previous lemma. The target env extends both
   TE_TypeVars and TE_RuntimeTypeVars by the binders, matching the shape used
   by tyenv_fun_ghost_constraint and tyenv_nonghost_payloads_runtime (after
   the Abs-intersection collapse performed by the caller). *)
lemma apply_subst_preserves_runtime_module_binders:
  assumes rt: "is_runtime_type
                 (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list binders,
                        TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| fset_of_list binders \<rparr>) ty"
      and ok: "module_env_subst_ok subst targetEnv env"
      and ok_rt: "module_env_subst_runtime_ok subst targetEnv env"
      and avoid: "subst_names subst |\<inter>| fset_of_list binders = {||}"
  shows "is_runtime_type
           (targetEnv \<lparr> TE_TypeVars := TE_TypeVars targetEnv |\<union>| fset_of_list binders,
                        TE_RuntimeTypeVars := TE_RuntimeTypeVars targetEnv |\<union>| fset_of_list binders \<rparr>)
           (apply_subst subst ty)"
proof (rule apply_subst_preserves_runtime[OF rt])
  show "TE_GhostDatatypes
          (targetEnv \<lparr> TE_TypeVars := TE_TypeVars targetEnv |\<union>| fset_of_list binders,
                       TE_RuntimeTypeVars := TE_RuntimeTypeVars targetEnv |\<union>| fset_of_list binders \<rparr>)
          = TE_GhostDatatypes
              (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list binders,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| fset_of_list binders \<rparr>)"
    using ok unfolding module_env_subst_ok_def by simp
next
  fix n assume "n |\<in>| TE_RuntimeTypeVars
                        (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list binders,
                               TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| fset_of_list binders \<rparr>)"
  hence n_in: "n |\<in>| TE_RuntimeTypeVars env \<or> n \<in> set binders"
    by (auto simp: fset_of_list_elem)
  show "case fmlookup subst n of
          Some ty' \<Rightarrow> is_runtime_type
                        (targetEnv \<lparr> TE_TypeVars := TE_TypeVars targetEnv |\<union>| fset_of_list binders,
                                     TE_RuntimeTypeVars := TE_RuntimeTypeVars targetEnv |\<union>| fset_of_list binders \<rparr>) ty'
        | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars
                        (targetEnv \<lparr> TE_TypeVars := TE_TypeVars targetEnv |\<union>| fset_of_list binders,
                                     TE_RuntimeTypeVars := TE_RuntimeTypeVars targetEnv |\<union>| fset_of_list binders \<rparr>)"
  proof (cases "n \<in> set binders")
    case True
    have n_none: "fmlookup subst n = None"
    proof (cases "fmlookup subst n")
      case None thus ?thesis .
    next
      case (Some ty')
      hence "n |\<in>| fmdom subst" by (rule fmdomI)
      hence "n |\<in>| subst_names subst" unfolding subst_names_def by simp
      with True avoid show ?thesis
        by (metis fempty_iff finterI fset_of_list_elem)
    qed
    show ?thesis using True by (simp add: n_none fset_of_list_elem)
  next
    case False
    with n_in have n_env: "n |\<in>| TE_RuntimeTypeVars env" by (simp add: fset_of_list_elem)
    hence cov: "case fmlookup subst n of
                  Some ty' \<Rightarrow> is_runtime_type targetEnv ty'
                | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars targetEnv"
      using ok_rt unfolding module_env_subst_runtime_ok_def by blast
    show ?thesis
    proof (cases "fmlookup subst n")
      case None
      with cov show ?thesis by simp
    next
      case (Some ty')
      with cov have rt_t: "is_runtime_type targetEnv ty'" by simp
      have "is_runtime_type
              (targetEnv \<lparr> TE_TypeVars := TE_TypeVars targetEnv |\<union>| fset_of_list binders,
                           TE_RuntimeTypeVars := TE_RuntimeTypeVars targetEnv |\<union>| fset_of_list binders \<rparr>) ty'"
        by (rule is_runtime_type_extend_runtime_tyvars[OF rt_t])
      with Some show ?thesis by simp
    qed
  qed
qed


(* The main preservation lemma: the substituted module env is well-formed. *)
lemma tyenv_well_formed_apply_subst_to_module_env:
  assumes wf: "tyenv_well_formed env"
      and ok: "module_env_subst_ok subst targetEnv env"
      and ok_rt: "module_env_subst_runtime_ok subst targetEnv env"
      and abs_env: "TE_AbstractTypes env = TE_TypeVars env"
      and abs_target: "TE_AbstractTypes targetEnv = TE_TypeVars targetEnv"
      and rtv_target: "TE_RuntimeTypeVars targetEnv |\<subseteq>| TE_TypeVars targetEnv"
  shows "tyenv_well_formed (apply_subst_to_module_env subst targetEnv env)"
proof -
  let ?me = "apply_subst_to_module_env subst targetEnv env"

  \<comment> \<open>Unpack the hypotheses.\<close>
  have wf_vars_wk: "tyenv_vars_well_kinded env"
   and wf_vars_rt: "tyenv_vars_runtime env"
   and wf_ghost_sub: "tyenv_ghost_vars_subset env"
   and wf_ret_wk: "tyenv_return_type_well_kinded env"
   and wf_ret_rt: "tyenv_return_type_runtime env"
   and wf_ctors_cons: "tyenv_ctors_consistent env"
   and wf_payloads: "tyenv_payloads_well_kinded env"
   and wf_ctor_dist: "tyenv_ctor_tyvars_distinct env"
   and wf_ctors_bt: "tyenv_ctors_by_type_consistent env"
   and wf_fun_wk: "tyenv_fun_types_well_kinded env"
   and wf_fun_dist: "tyenv_fun_tyvars_distinct env"
   and wf_fun_ghost: "tyenv_fun_ghost_constraint env"
   and wf_ng_payloads: "tyenv_nonghost_payloads_runtime env"
   and wf_gdt_sub: "tyenv_ghost_datatypes_subset env"
   and wf_dt_nonempty: "tyenv_datatypes_nonempty env"
    using wf[unfolded tyenv_well_formed_def] by simp_all
  have rtv_env: "TE_RuntimeTypeVars env |\<subseteq>| TE_TypeVars env"
    using wf[unfolded tyenv_well_formed_def]
    unfolding tyenv_runtime_tyvars_subset_def by simp
  have dt_eq: "TE_Datatypes targetEnv = TE_Datatypes env"
   and gdt_eq: "TE_GhostDatatypes targetEnv = TE_GhostDatatypes env"
    using ok unfolding module_env_subst_ok_def by simp_all
  have fun_avoid: "\<And>funName info. fmlookup (TE_Functions env) funName = Some info \<Longrightarrow>
                     subst_names subst |\<inter>| fset_of_list (FI_TyArgs info) = {||}"
    using ok unfolding module_env_subst_ok_def by blast
  have ctor_avoid: "\<And>ctorName dtName tyVars payload.
                      fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload) \<Longrightarrow>
                      subst_names subst |\<inter>| fset_of_list tyVars = {||}"
    using ok unfolding module_env_subst_ok_def by blast

  \<comment> \<open>With RTV below TV, the Abs-intersection forms collapse (after rewriting
      Abs to TV via the module-level equations).\<close>
  have tv_inter_env: "TE_TypeVars env |\<inter>| TE_RuntimeTypeVars env = TE_RuntimeTypeVars env"
    using rtv_env by (simp add: inf_absorb2)
  have tv_inter_target: "TE_TypeVars targetEnv |\<inter>| TE_RuntimeTypeVars targetEnv
                           = TE_RuntimeTypeVars targetEnv"
    using rtv_target by (simp add: inf_absorb2)

  \<comment> \<open>Clause 1: variable types are well-kinded.\<close>
  have c1: "tyenv_vars_well_kinded ?me"
    unfolding tyenv_vars_well_kinded_def
  proof (intro conjI allI impI)
    fix name ty
    assume "fmlookup (TE_LocalVars ?me) name = Some ty"
    then obtain ty0 where l0: "fmlookup (TE_LocalVars env) name = Some ty0"
                      and ty_eq: "ty = apply_subst subst ty0"
      by (cases "fmlookup (TE_LocalVars env) name") auto
    have "is_well_kinded env ty0"
      using wf_vars_wk l0 unfolding tyenv_vars_well_kinded_def by blast
    thus "is_well_kinded ?me ty"
      unfolding ty_eq by (rule apply_subst_preserves_well_kinded_module[OF _ ok])
  next
    fix name ty
    assume "fmlookup (TE_GlobalVars ?me) name = Some ty"
    then obtain ty0 where g0: "fmlookup (TE_GlobalVars env) name = Some ty0"
                      and ty_eq: "ty = apply_subst subst ty0"
      by (cases "fmlookup (TE_GlobalVars env) name") auto
    have wk_abs: "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env \<rparr>) ty0"
      using wf_vars_wk g0 unfolding tyenv_vars_well_kinded_def by blast
    have "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env \<rparr>) ty0
            = is_well_kinded env ty0"
      by (intro is_well_kinded_cong_env) (simp_all add: abs_env)
    with wk_abs have "is_well_kinded env ty0" by simp
    hence me_wk: "is_well_kinded ?me (apply_subst subst ty0)"
      by (rule apply_subst_preserves_well_kinded_module[OF _ ok])
    have "is_well_kinded (?me \<lparr> TE_TypeVars := TE_AbstractTypes ?me \<rparr>) (apply_subst subst ty0)
            = is_well_kinded ?me (apply_subst subst ty0)"
      by (intro is_well_kinded_cong_env) (simp_all add: abs_target)
    with me_wk show "is_well_kinded (?me \<lparr> TE_TypeVars := TE_AbstractTypes ?me \<rparr>) ty"
      unfolding ty_eq by simp
  qed

  \<comment> \<open>Clause 2: non-ghost variable types are runtime.\<close>
  have c2: "tyenv_vars_runtime ?me"
    unfolding tyenv_vars_runtime_def
  proof (intro conjI allI impI)
    fix name ty
    assume a: "fmlookup (TE_LocalVars ?me) name = Some ty \<and> name |\<notin>| TE_GhostLocals ?me"
    then obtain ty0 where l0: "fmlookup (TE_LocalVars env) name = Some ty0"
                      and ty_eq: "ty = apply_subst subst ty0"
      by (cases "fmlookup (TE_LocalVars env) name") auto
    from a have ng: "name |\<notin>| TE_GhostLocals env" by simp
    have "is_runtime_type env ty0"
      using wf_vars_rt l0 ng unfolding tyenv_vars_runtime_def by blast
    thus "is_runtime_type ?me ty"
      unfolding ty_eq by (rule apply_subst_preserves_runtime_module[OF _ ok ok_rt])
  next
    fix name ty
    assume a: "fmlookup (TE_GlobalVars ?me) name = Some ty \<and> name |\<notin>| TE_GhostGlobals ?me"
    then obtain ty0 where g0: "fmlookup (TE_GlobalVars env) name = Some ty0"
                      and ty_eq: "ty = apply_subst subst ty0"
      by (cases "fmlookup (TE_GlobalVars env) name") auto
    from a have ng: "name |\<notin>| TE_GhostGlobals env" by simp
    have rt_abs: "is_runtime_type
                    (env \<lparr> TE_TypeVars := TE_AbstractTypes env,
                           TE_RuntimeTypeVars := TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env \<rparr>) ty0"
      using wf_vars_rt g0 ng unfolding tyenv_vars_runtime_def by blast
    have "is_runtime_type
            (env \<lparr> TE_TypeVars := TE_AbstractTypes env,
                   TE_RuntimeTypeVars := TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env \<rparr>) ty0
            = is_runtime_type env ty0"
      by (intro is_runtime_type_cong_env) (simp_all add: abs_env tv_inter_env)
    with rt_abs have "is_runtime_type env ty0" by simp
    hence me_rt: "is_runtime_type ?me (apply_subst subst ty0)"
      by (rule apply_subst_preserves_runtime_module[OF _ ok ok_rt])
    have "is_runtime_type
            (?me \<lparr> TE_TypeVars := TE_AbstractTypes ?me,
                   TE_RuntimeTypeVars := TE_AbstractTypes ?me |\<inter>| TE_RuntimeTypeVars ?me \<rparr>)
            (apply_subst subst ty0)
            = is_runtime_type ?me (apply_subst subst ty0)"
      by (intro is_runtime_type_cong_env) (simp_all add: abs_target tv_inter_target)
    with me_rt show "is_runtime_type
                       (?me \<lparr> TE_TypeVars := TE_AbstractTypes ?me,
                              TE_RuntimeTypeVars := TE_AbstractTypes ?me |\<inter>| TE_RuntimeTypeVars ?me \<rparr>) ty"
      unfolding ty_eq by simp
  qed

  \<comment> \<open>Clause 3: ghost variable names are declared (fmmap preserves domains).\<close>
  have c3: "tyenv_ghost_vars_subset ?me"
    using wf_ghost_sub unfolding tyenv_ghost_vars_subset_def by simp

  \<comment> \<open>Clauses 4 and 5: the return type.\<close>
  have c4: "tyenv_return_type_well_kinded ?me"
    unfolding tyenv_return_type_well_kinded_def
    using apply_subst_preserves_well_kinded_module[OF
            wf_ret_wk[unfolded tyenv_return_type_well_kinded_def] ok]
    by simp
  have c5: "tyenv_return_type_runtime ?me"
    unfolding tyenv_return_type_runtime_def
  proof (intro impI)
    assume "TE_FunctionGhost ?me = NotGhost"
    hence "TE_FunctionGhost env = NotGhost" by simp
    hence rt0: "is_runtime_type env (TE_ReturnType env)"
      using wf_ret_rt unfolding tyenv_return_type_runtime_def by simp
    show "is_runtime_type ?me (TE_ReturnType ?me)"
      using apply_subst_preserves_runtime_module[OF rt0 ok ok_rt] by simp
  qed

  \<comment> \<open>Clause 6: ctors consistent with datatypes (substitution keeps the
      datatype name and tyvar list of every ctor entry).\<close>
  have c6: "tyenv_ctors_consistent ?me"
    unfolding tyenv_ctors_consistent_def
  proof (intro allI impI)
    fix ctorName dtName tyVars payload
    assume "fmlookup (TE_DataCtors ?me) ctorName = Some (dtName, tyVars, payload)"
    then obtain payload0 where
      dc0: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload0)"
      by (cases "fmlookup (TE_DataCtors env) ctorName")
         (auto simp: apply_subst_to_datactor_def split: prod.splits)
    have "fmlookup (TE_Datatypes env) dtName = Some (length tyVars)"
      using wf_ctors_cons dc0 unfolding tyenv_ctors_consistent_def by blast
    thus "fmlookup (TE_Datatypes ?me) dtName = Some (length tyVars)" by simp
  qed

  \<comment> \<open>Clause 7: ctor payload types are well-kinded (binder-extended lifting).\<close>
  have c7: "tyenv_payloads_well_kinded ?me"
    unfolding tyenv_payloads_well_kinded_def
  proof (intro allI impI)
    fix ctorName dtName tyVars payload
    assume "fmlookup (TE_DataCtors ?me) ctorName = Some (dtName, tyVars, payload)"
    then obtain payload0 where
      dc0: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload0)" and
      p_eq: "payload = apply_subst subst payload0"
      by (cases "fmlookup (TE_DataCtors env) ctorName")
         (auto simp: apply_subst_to_datactor_def split: prod.splits)
    have wk0: "is_well_kinded
                 (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyVars \<rparr>) payload0"
      using wf_payloads dc0 unfolding tyenv_payloads_well_kinded_def by blast
    have src_eq: "is_well_kinded
                    (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyVars \<rparr>) payload0
                    = is_well_kinded
                        (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list tyVars \<rparr>) payload0"
      by (intro is_well_kinded_cong_env) (simp_all add: abs_env)
    have wk_t: "is_well_kinded
                  (targetEnv \<lparr> TE_TypeVars := TE_TypeVars targetEnv |\<union>| fset_of_list tyVars \<rparr>)
                  (apply_subst subst payload0)"
    proof (rule apply_subst_preserves_well_kinded_module_binders[OF _ ok ctor_avoid[OF dc0]])
      show "is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list tyVars \<rparr>) payload0"
        using wk0 src_eq by simp
    qed
    have tgt_eq: "is_well_kinded
                    (targetEnv \<lparr> TE_TypeVars := TE_TypeVars targetEnv |\<union>| fset_of_list tyVars \<rparr>)
                    (apply_subst subst payload0)
                    = is_well_kinded
                        (?me \<lparr> TE_TypeVars := TE_AbstractTypes ?me |\<union>| fset_of_list tyVars \<rparr>)
                        (apply_subst subst payload0)"
      by (intro is_well_kinded_cong_env) (simp_all add: abs_target dt_eq)
    show "is_well_kinded (?me \<lparr> TE_TypeVars := TE_AbstractTypes ?me |\<union>| fset_of_list tyVars \<rparr>) payload"
      using wk_t tgt_eq unfolding p_eq by simp
  qed

  \<comment> \<open>Clause 8: ctor tyvars are distinct (unchanged by substitution).\<close>
  have c8: "tyenv_ctor_tyvars_distinct ?me"
    unfolding tyenv_ctor_tyvars_distinct_def
  proof (intro allI impI)
    fix ctorName dtName tyVars payload
    assume "fmlookup (TE_DataCtors ?me) ctorName = Some (dtName, tyVars, payload)"
    then obtain payload0 where
      dc0: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload0)"
      by (cases "fmlookup (TE_DataCtors env) ctorName")
         (auto simp: apply_subst_to_datactor_def split: prod.splits)
    thus "distinct tyVars"
      using wf_ctor_dist unfolding tyenv_ctor_tyvars_distinct_def by blast
  qed

  \<comment> \<open>Clause 9: TE_DataCtorsByType consistency - substitution preserves the
      existence and datatype name of every ctor entry, so the iff carries over.\<close>
  have c9: "tyenv_ctors_by_type_consistent ?me"
    unfolding tyenv_ctors_by_type_consistent_def
  proof (intro allI impI)
    fix dtName ctors ctorName
    assume "fmlookup (TE_DataCtorsByType ?me) dtName = Some ctors"
    hence bt0: "fmlookup (TE_DataCtorsByType env) dtName = Some ctors" by simp
    have iff0: "(\<exists>tyVars payload.
                   fmlookup (TE_DataCtors ?me) ctorName = Some (dtName, tyVars, payload))
                  \<longleftrightarrow> (\<exists>tyVars payload.
                        fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload))"
      by (cases "fmlookup (TE_DataCtors env) ctorName")
         (auto simp: apply_subst_to_datactor_def split: prod.splits)
    have "ctorName \<in> set ctors \<longleftrightarrow>
            (\<exists>tyVars payload.
               fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload))"
      using wf_ctors_bt bt0 unfolding tyenv_ctors_by_type_consistent_def by blast
    thus "ctorName \<in> set ctors \<longleftrightarrow>
            (\<exists>tyVars payload.
               fmlookup (TE_DataCtors ?me) ctorName = Some (dtName, tyVars, payload))"
      using iff0 by blast
  qed

  \<comment> \<open>Clause 10: function arg/return types are well-kinded (binder-extended
      lifting at the function's FI_TyArgs).\<close>
  have c10: "tyenv_fun_types_well_kinded ?me"
    unfolding tyenv_fun_types_well_kinded_def
  proof (intro allI impI)
    fix funName info
    assume "fmlookup (TE_Functions ?me) funName = Some info"
    then obtain info0 where
      f0: "fmlookup (TE_Functions env) funName = Some info0" and
      i_eq: "info = apply_subst_to_funinfo subst info0"
      by (cases "fmlookup (TE_Functions env) funName") auto
    have tyargs: "FI_TyArgs info = FI_TyArgs info0" by (simp add: i_eq)
    have wk_lift: "\<And>ty0.
        is_well_kinded
          (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty0 \<Longrightarrow>
        is_well_kinded
          (?me \<lparr> TE_TypeVars := TE_AbstractTypes ?me |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>)
          (apply_subst subst ty0)"
    proof -
      fix ty0
      assume w0: "is_well_kinded
                    (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty0"
      have src_eq: "is_well_kinded
                      (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty0
                      = is_well_kinded
                          (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty0"
        by (intro is_well_kinded_cong_env) (simp_all add: abs_env)
      have wk_t: "is_well_kinded
                    (targetEnv \<lparr> TE_TypeVars := TE_TypeVars targetEnv |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>)
                    (apply_subst subst ty0)"
      proof (rule apply_subst_preserves_well_kinded_module_binders[OF _ ok fun_avoid[OF f0]])
        show "is_well_kinded
                (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty0"
          using w0 src_eq by simp
      qed
      have tgt_eq: "is_well_kinded
                      (targetEnv \<lparr> TE_TypeVars := TE_TypeVars targetEnv |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>)
                      (apply_subst subst ty0)
                      = is_well_kinded
                          (?me \<lparr> TE_TypeVars := TE_AbstractTypes ?me |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>)
                          (apply_subst subst ty0)"
        by (intro is_well_kinded_cong_env) (simp_all add: abs_target dt_eq)
      show "is_well_kinded
              (?me \<lparr> TE_TypeVars := TE_AbstractTypes ?me |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>)
              (apply_subst subst ty0)"
        using wk_t tgt_eq by simp
    qed
    have args': "\<forall>ty \<in> fst ` set (FI_TmArgs info).
                   is_well_kinded
                     (?me \<lparr> TE_TypeVars := TE_AbstractTypes ?me |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty"
    proof
      fix ty assume "ty \<in> fst ` set (FI_TmArgs info)"
      then obtain ty0 where ty0_in: "ty0 \<in> fst ` set (FI_TmArgs info0)"
                        and ty_eq: "ty = apply_subst subst ty0"
        by (force simp: i_eq apply_subst_to_funinfo_def)
      have "is_well_kinded
              (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty0"
        using wf_fun_wk f0 ty0_in unfolding tyenv_fun_types_well_kinded_def by blast
      from wk_lift[OF this]
      show "is_well_kinded
              (?me \<lparr> TE_TypeVars := TE_AbstractTypes ?me |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty"
        unfolding ty_eq .
    qed
    have ret': "is_well_kinded
                  (?me \<lparr> TE_TypeVars := TE_AbstractTypes ?me |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>)
                  (FI_ReturnType info)"
    proof -
      have "is_well_kinded
              (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>)
              (FI_ReturnType info0)"
        using wf_fun_wk f0 unfolding tyenv_fun_types_well_kinded_def by blast
      from wk_lift[OF this] show ?thesis by (simp add: i_eq)
    qed
    show "(\<forall>ty \<in> fst ` set (FI_TmArgs info).
             is_well_kinded
               (?me \<lparr> TE_TypeVars := TE_AbstractTypes ?me |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
          \<and> is_well_kinded
              (?me \<lparr> TE_TypeVars := TE_AbstractTypes ?me |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
              (FI_ReturnType info)"
      using args' ret' unfolding tyargs by blast
  qed

  \<comment> \<open>Clause 11: function tyvars are distinct (unchanged by substitution).\<close>
  have c11: "tyenv_fun_tyvars_distinct ?me"
    unfolding tyenv_fun_tyvars_distinct_def
  proof (intro allI impI)
    fix funName info
    assume "fmlookup (TE_Functions ?me) funName = Some info"
    then obtain info0 where
      f0: "fmlookup (TE_Functions env) funName = Some info0" and
      i_eq: "info = apply_subst_to_funinfo subst info0"
      by (cases "fmlookup (TE_Functions env) funName") auto
    have "distinct (FI_TyArgs info0)"
      using wf_fun_dist f0 unfolding tyenv_fun_tyvars_distinct_def by blast
    thus "distinct (FI_TyArgs info)" by (simp add: i_eq)
  qed

  \<comment> \<open>Clause 12: non-ghost function signatures are runtime (binder-extended
      runtime lifting at the function's FI_TyArgs).\<close>
  have c12: "tyenv_fun_ghost_constraint ?me"
    unfolding tyenv_fun_ghost_constraint_def Let_def
  proof (intro allI impI)
    fix funName info
    assume a: "fmlookup (TE_Functions ?me) funName = Some info \<and> FI_Ghost info = NotGhost"
    then obtain info0 where
      f0: "fmlookup (TE_Functions env) funName = Some info0" and
      i_eq: "info = apply_subst_to_funinfo subst info0"
      by (cases "fmlookup (TE_Functions env) funName") auto
    from a have ng: "FI_Ghost info0 = NotGhost" by (simp add: i_eq)
    have tyargs: "FI_TyArgs info = FI_TyArgs info0" by (simp add: i_eq)
    let ?srcAbs = "env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list (FI_TyArgs info0),
                         TE_RuntimeTypeVars := (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                                |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>"
    let ?srcTv = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list (FI_TyArgs info0),
                        TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>"
    let ?tgtTv = "targetEnv \<lparr> TE_TypeVars := TE_TypeVars targetEnv |\<union>| fset_of_list (FI_TyArgs info0),
                              TE_RuntimeTypeVars := TE_RuntimeTypeVars targetEnv
                                                     |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>"
    let ?tgtAbs = "?me \<lparr> TE_TypeVars := TE_AbstractTypes ?me |\<union>| fset_of_list (FI_TyArgs info0),
                         TE_RuntimeTypeVars := (TE_AbstractTypes ?me |\<inter>| TE_RuntimeTypeVars ?me)
                                                |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>"
    have rt0_all: "(\<forall>ty0 \<in> fst ` set (FI_TmArgs info0). is_runtime_type ?srcAbs ty0)
                   \<and> is_runtime_type ?srcAbs (FI_ReturnType info0)"
      using wf_fun_ghost f0 ng unfolding tyenv_fun_ghost_constraint_def Let_def by blast
    have rt_lift: "\<And>ty0. is_runtime_type ?srcAbs ty0 \<Longrightarrow>
                          is_runtime_type ?tgtAbs (apply_subst subst ty0)"
    proof -
      fix ty0 assume r0: "is_runtime_type ?srcAbs ty0"
      have src_eq: "is_runtime_type ?srcAbs ty0 = is_runtime_type ?srcTv ty0"
        by (intro is_runtime_type_cong_env) (simp_all add: abs_env tv_inter_env)
      have rt_t: "is_runtime_type ?tgtTv (apply_subst subst ty0)"
      proof (rule apply_subst_preserves_runtime_module_binders[OF _ ok ok_rt fun_avoid[OF f0]])
        show "is_runtime_type ?srcTv ty0" using r0 src_eq by simp
      qed
      have tgt_eq: "is_runtime_type ?tgtTv (apply_subst subst ty0)
                      = is_runtime_type ?tgtAbs (apply_subst subst ty0)"
        by (intro is_runtime_type_cong_env) (simp_all add: abs_target tv_inter_target gdt_eq)
      show "is_runtime_type ?tgtAbs (apply_subst subst ty0)" using rt_t tgt_eq by simp
    qed
    have args': "\<forall>ty \<in> fst ` set (FI_TmArgs info). is_runtime_type ?tgtAbs ty"
    proof
      fix ty assume "ty \<in> fst ` set (FI_TmArgs info)"
      then obtain ty0 where ty0_in: "ty0 \<in> fst ` set (FI_TmArgs info0)"
                        and ty_eq: "ty = apply_subst subst ty0"
        by (force simp: i_eq apply_subst_to_funinfo_def)
      have "is_runtime_type ?srcAbs ty0" using rt0_all ty0_in by blast
      from rt_lift[OF this] show "is_runtime_type ?tgtAbs ty" unfolding ty_eq .
    qed
    have ret': "is_runtime_type ?tgtAbs (FI_ReturnType info)"
    proof -
      have "is_runtime_type ?srcAbs (FI_ReturnType info0)" using rt0_all by blast
      from rt_lift[OF this] show ?thesis by (simp add: i_eq)
    qed
    show "(\<forall>ty \<in> fst ` set (FI_TmArgs info).
             is_runtime_type
               (?me \<lparr> TE_TypeVars := TE_AbstractTypes ?me |\<union>| fset_of_list (FI_TyArgs info),
                      TE_RuntimeTypeVars := (TE_AbstractTypes ?me |\<inter>| TE_RuntimeTypeVars ?me)
                                             |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
          \<and> is_runtime_type
              (?me \<lparr> TE_TypeVars := TE_AbstractTypes ?me |\<union>| fset_of_list (FI_TyArgs info),
                     TE_RuntimeTypeVars := (TE_AbstractTypes ?me |\<inter>| TE_RuntimeTypeVars ?me)
                                            |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
              (FI_ReturnType info)"
      using args' ret' unfolding tyargs by blast
  qed

  \<comment> \<open>Clause 13: non-ghost ctor payloads are runtime (binder-extended runtime
      lifting at the ctor's tyvars).\<close>
  have c13: "tyenv_nonghost_payloads_runtime ?me"
    unfolding tyenv_nonghost_payloads_runtime_def
  proof (intro allI impI)
    fix ctorName dtName tyVars payload
    assume l: "fmlookup (TE_DataCtors ?me) ctorName = Some (dtName, tyVars, payload)"
       and ng: "dtName |\<notin>| TE_GhostDatatypes ?me"
    from l obtain payload0 where
      dc0: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload0)" and
      p_eq: "payload = apply_subst subst payload0"
      by (cases "fmlookup (TE_DataCtors env) ctorName")
         (auto simp: apply_subst_to_datactor_def split: prod.splits)
    from ng have ng0: "dtName |\<notin>| TE_GhostDatatypes env" by simp
    let ?srcAbs = "env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyVars,
                         TE_RuntimeTypeVars := (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                                |\<union>| fset_of_list tyVars \<rparr>"
    let ?srcTv = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list tyVars,
                        TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| fset_of_list tyVars \<rparr>"
    let ?tgtTv = "targetEnv \<lparr> TE_TypeVars := TE_TypeVars targetEnv |\<union>| fset_of_list tyVars,
                              TE_RuntimeTypeVars := TE_RuntimeTypeVars targetEnv
                                                     |\<union>| fset_of_list tyVars \<rparr>"
    let ?tgtAbs = "?me \<lparr> TE_TypeVars := TE_AbstractTypes ?me |\<union>| fset_of_list tyVars,
                         TE_RuntimeTypeVars := (TE_AbstractTypes ?me |\<inter>| TE_RuntimeTypeVars ?me)
                                                |\<union>| fset_of_list tyVars \<rparr>"
    have r0: "is_runtime_type ?srcAbs payload0"
      using wf_ng_payloads dc0 ng0 unfolding tyenv_nonghost_payloads_runtime_def by blast
    have src_eq: "is_runtime_type ?srcAbs payload0 = is_runtime_type ?srcTv payload0"
      by (intro is_runtime_type_cong_env) (simp_all add: abs_env tv_inter_env)
    have rt_t: "is_runtime_type ?tgtTv (apply_subst subst payload0)"
    proof (rule apply_subst_preserves_runtime_module_binders[OF _ ok ok_rt ctor_avoid[OF dc0]])
      show "is_runtime_type ?srcTv payload0" using r0 src_eq by simp
    qed
    have tgt_eq: "is_runtime_type ?tgtTv (apply_subst subst payload0)
                    = is_runtime_type ?tgtAbs (apply_subst subst payload0)"
      by (intro is_runtime_type_cong_env) (simp_all add: abs_target tv_inter_target gdt_eq)
    show "is_runtime_type ?tgtAbs payload"
      using rt_t tgt_eq unfolding p_eq by simp
  qed

  \<comment> \<open>Clauses 14-17: pure bookkeeping on fields that either come from
      targetEnv (with the hypotheses supplying the subset facts) or are
      untouched by the substitution.\<close>
  have c14: "tyenv_ghost_datatypes_subset ?me"
    using wf_gdt_sub unfolding tyenv_ghost_datatypes_subset_def by simp
  have c15: "tyenv_runtime_tyvars_subset ?me"
    using rtv_target unfolding tyenv_runtime_tyvars_subset_def by simp
  have c16: "tyenv_abstract_types_subset ?me"
    using abs_target unfolding tyenv_abstract_types_subset_def by simp
  have c17: "tyenv_datatypes_nonempty ?me"
    using wf_dt_nonempty unfolding tyenv_datatypes_nonempty_def by simp

  show ?thesis
    unfolding tyenv_well_formed_def
    using c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17
    by blast
qed


end
