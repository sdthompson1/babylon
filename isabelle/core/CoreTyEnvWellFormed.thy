theory CoreTyEnvWellFormed
  imports CoreKindcheck
begin

(* All term variables' types (both local and global) are well-kinded *)
definition tyenv_vars_well_kinded :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_vars_well_kinded env =
    ((\<forall>name ty. fmlookup (TE_LocalVars env) name = Some ty \<longrightarrow> is_well_kinded env ty) \<and>
     (\<forall>name ty. fmlookup (TE_GlobalVars env) name = Some ty \<longrightarrow> is_well_kinded env ty))"

(* All nonghost term variables' types are runtime types *)
definition tyenv_vars_runtime :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_vars_runtime env =
    ((\<forall>name ty. fmlookup (TE_LocalVars env) name = Some ty
               \<and> name |\<notin>| TE_GhostLocals env
               \<longrightarrow> is_runtime_type env ty) \<and>
     (\<forall>name ty. fmlookup (TE_GlobalVars env) name = Some ty
               \<and> name |\<notin>| TE_GhostGlobals env
               \<longrightarrow> is_runtime_type env ty))"

(* Ghost locals are a subset of local variable names;
   ghost globals are a subset of global variable names *)
definition tyenv_ghost_vars_subset :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_ghost_vars_subset env =
    (TE_GhostLocals env |\<subseteq>| fmdom (TE_LocalVars env) \<and>
     TE_GhostGlobals env |\<subseteq>| fmdom (TE_GlobalVars env))"

(* The return type is well-kinded *)
definition tyenv_return_type_well_kinded :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_return_type_well_kinded env =
    is_well_kinded env (TE_ReturnType env)"

(* Data constructors are consistent with datatypes:
   For each ctor in TE_DataCtors mapping to (dtName, tyArgMetavars, payload),
   dtName must be in TE_Datatypes with matching numTyArgs *)
definition tyenv_ctors_consistent :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_ctors_consistent env =
    (\<forall>ctorName dtName tyArgMetavars payload.
      fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyArgMetavars, payload) \<longrightarrow>
      fmlookup (TE_Datatypes env) dtName = Some (length tyArgMetavars))"

(* Data constructor payload types are well-kinded, in an appropriate env. *)
(* (Note that well-kindedness depends only on TE_Datatypes and TE_TypeVars, so overriding
   only TE_TypeVars is appropriate here.) *)
definition tyenv_payloads_well_kinded :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_payloads_well_kinded env =
    (\<forall>ctorName dtName tyArgMetavars payload.
      fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyArgMetavars, payload) \<longrightarrow>
      is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list tyArgMetavars \<rparr>) payload)"

(* Data constructor type arguments (type variables) are distinct *)
definition tyenv_ctor_tyvars_distinct :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_ctor_tyvars_distinct env =
    (\<forall>ctorName dtName tyVars payload.
      fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload) \<longrightarrow>
      distinct tyVars)"

(* TE_DataCtorsByType is consistent with TE_DataCtors:
   A constructor is in TE_DataCtorsByType[dtName] iff it maps to dtName in TE_DataCtors *)
definition tyenv_ctors_by_type_consistent :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_ctors_by_type_consistent env =
    (\<forall>dtName ctors. fmlookup (TE_DataCtorsByType env) dtName = Some ctors \<longrightarrow>
      (\<forall>ctorName. ctorName \<in> set ctors \<longleftrightarrow>
        (\<exists>tyArgMetavars payload.
          fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyArgMetavars, payload))))"

(* Function arg and return types are well-kinded in an appropriate env. *)
definition tyenv_fun_types_well_kinded :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_fun_types_well_kinded env =
    (\<forall>funName info. fmlookup (TE_Functions env) funName = Some info \<longrightarrow>
      (\<forall>ty \<in> fst ` set (FI_TmArgs info).
          is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info) \<rparr>) ty) \<and>
      is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info) \<rparr>) (FI_ReturnType info))"

(* Function type arguments (tyvars) are distinct *)
definition tyenv_fun_tyvars_distinct :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_fun_tyvars_distinct env =
    (\<forall>funName info. fmlookup (TE_Functions env) funName = Some info \<longrightarrow>
      distinct (FI_TyArgs info))"

(* For non-ghost functions, types must be runtime types (for polymorphic functions,
   this only needs to hold when the type arguments themselves are runtime types). *)
definition tyenv_fun_ghost_constraint :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_fun_ghost_constraint env =
    (\<forall>funName info. fmlookup (TE_Functions env) funName = Some info \<and>
    (FI_Ghost info) = NotGhost \<longrightarrow>
      (let fenv = env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info),
                         TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info) \<rparr>
       in (\<forall>ty \<in> fst ` set (FI_TmArgs info). is_runtime_type fenv ty) \<and>
          is_runtime_type fenv (FI_ReturnType info)))"

(* For non-ghost datatypes, all constructor payload types must be runtime.
   This ensures variant types can be represented in memory (e.g. as tagged unions). *)
definition tyenv_nonghost_payloads_runtime :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_nonghost_payloads_runtime env =
    (\<forall>ctorName dtName tyVars payload.
      fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload) \<longrightarrow>
      dtName |\<notin>| TE_GhostDatatypes env \<longrightarrow>
      is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list tyVars,
                              TE_RuntimeTypeVars := fset_of_list tyVars \<rparr>) payload)"

(* Ghost datatypes must be a subset of all datatypes *)
definition tyenv_ghost_datatypes_subset :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_ghost_datatypes_subset env =
    (TE_GhostDatatypes env |\<subseteq>| fmdom (TE_Datatypes env))"

(* A type environment is well-formed if all the above conditions hold *)
definition tyenv_well_formed :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_well_formed env =
    (tyenv_vars_well_kinded env \<and>
     tyenv_vars_runtime env \<and>
     tyenv_ghost_vars_subset env \<and>
     tyenv_return_type_well_kinded env \<and>
     tyenv_ctors_consistent env \<and>
     tyenv_payloads_well_kinded env \<and>
     tyenv_ctor_tyvars_distinct env \<and>
     tyenv_ctors_by_type_consistent env \<and>
     tyenv_fun_types_well_kinded env \<and>
     tyenv_fun_tyvars_distinct env \<and>
     tyenv_fun_ghost_constraint env \<and>
     tyenv_nonghost_payloads_runtime env \<and>
     tyenv_ghost_datatypes_subset env)"

(* Adding a well-kinded, runtime, non-ghost local variable preserves tyenv_well_formed. *)
lemma tyenv_well_formed_add_var:
  assumes wf: "tyenv_well_formed env"
    and ty_wk: "is_well_kinded env ty"
    and ty_runtime: "is_runtime_type env ty"
  shows "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd var ty (TE_LocalVars env),
                                 TE_GhostLocals := fminus (TE_GhostLocals env) {|var|} \<rparr>)"
proof -
  let ?env' = "env \<lparr> TE_LocalVars := fmupd var ty (TE_LocalVars env),
                     TE_GhostLocals := fminus (TE_GhostLocals env) {|var|} \<rparr>"
  from wf have wk: "tyenv_vars_well_kinded env"
    and rt: "tyenv_vars_runtime env"
    and gvs: "tyenv_ghost_vars_subset env"
    and rest: "tyenv_ctors_consistent env"
              "tyenv_payloads_well_kinded env"
              "tyenv_ctor_tyvars_distinct env"
              "tyenv_ctors_by_type_consistent env"
              "tyenv_fun_types_well_kinded env"
              "tyenv_fun_tyvars_distinct env"
              "tyenv_fun_ghost_constraint env"
              "tyenv_nonghost_payloads_runtime env"
              "tyenv_ghost_datatypes_subset env"
    unfolding tyenv_well_formed_def by auto

  \<comment> \<open>is_well_kinded only depends on TE_Datatypes and TE_TypeVars, not TE_LocalVars\<close>
  have env'_fields: "TE_TypeVars ?env' = TE_TypeVars env"
                     "TE_Datatypes ?env' = TE_Datatypes env"
    by simp_all
  have wk_preserved: "\<And>ty'. is_well_kinded env ty' = is_well_kinded ?env' ty'"
    using is_well_kinded_cong_env[OF env'_fields] by simp

  \<comment> \<open>is_runtime_type only depends on TE_GhostDatatypes and TE_RuntimeTypeVars\<close>
  have gds_eq: "TE_GhostDatatypes ?env' = TE_GhostDatatypes env" by simp
  have rtv_eq: "TE_RuntimeTypeVars ?env' = TE_RuntimeTypeVars env" by simp
  have rt_preserved: "\<And>ty'. is_runtime_type ?env' ty' = is_runtime_type env ty'"
    using is_runtime_type_cong_env[OF gds_eq rtv_eq] by simp

  have "tyenv_vars_well_kinded ?env'"
    using wk ty_wk unfolding tyenv_vars_well_kinded_def
    by (auto simp: wk_preserved split: if_splits)
  moreover have "tyenv_vars_runtime ?env'"
    using rt ty_runtime unfolding tyenv_vars_runtime_def
    by (auto simp: rt_preserved split: if_splits)
  moreover have "tyenv_ghost_vars_subset ?env'"
    using gvs unfolding tyenv_ghost_vars_subset_def by auto
  moreover have "tyenv_return_type_well_kinded ?env'"
    using local.wf tyenv_return_type_well_kinded_def tyenv_well_formed_def wk_preserved
    by auto
  moreover have "tyenv_ctors_consistent ?env'" using rest(1)
    unfolding tyenv_ctors_consistent_def by simp
  moreover have "tyenv_payloads_well_kinded ?env'"
  proof -
    have "\<And>mvs t. is_well_kinded (?env' \<lparr> TE_TypeVars := fset_of_list mvs \<rparr>) t =
                    is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list mvs \<rparr>) t"
      by (rule is_well_kinded_cong_env) simp_all
    thus ?thesis using rest(2) unfolding tyenv_payloads_well_kinded_def by simp
  qed
  moreover have "tyenv_ctor_tyvars_distinct ?env'" using rest(3)
    unfolding tyenv_ctor_tyvars_distinct_def by simp
  moreover have "tyenv_ctors_by_type_consistent ?env'" using rest(4)
    unfolding tyenv_ctors_by_type_consistent_def by simp
  moreover have "tyenv_fun_types_well_kinded ?env'"
  proof -
    have "\<And>tvs t. is_well_kinded (?env' \<lparr> TE_TypeVars := tvs \<rparr>) t =
                    is_well_kinded (env \<lparr> TE_TypeVars := tvs \<rparr>) t"
      by (rule is_well_kinded_cong_env) simp_all
    thus ?thesis using rest(5) unfolding tyenv_fun_types_well_kinded_def by simp
  qed
  moreover have "tyenv_fun_tyvars_distinct ?env'" using rest(6)
    unfolding tyenv_fun_tyvars_distinct_def by simp
  moreover have "tyenv_fun_ghost_constraint ?env'"
  proof -
    have "\<And>rtvs tvs t. is_runtime_type (?env' \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t =
                        is_runtime_type (env \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t"
      by (rule is_runtime_type_cong_env) simp_all
    thus ?thesis using rest(7) unfolding tyenv_fun_ghost_constraint_def Let_def by simp
  qed
  moreover have "tyenv_nonghost_payloads_runtime ?env'"
  proof -
    have "\<And>tvs rtvs t. is_runtime_type (?env' \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t =
                        is_runtime_type (env \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t"
      by (rule is_runtime_type_cong_env) simp_all
    thus ?thesis using rest(8) unfolding tyenv_nonghost_payloads_runtime_def by simp
  qed
  moreover have "tyenv_ghost_datatypes_subset ?env'" using rest(9)
    unfolding tyenv_ghost_datatypes_subset_def by simp
  ultimately show ?thesis unfolding tyenv_well_formed_def by auto
qed

(* Adding a well-kinded ghost local variable preserves tyenv_well_formed.
   Ghost variables do not need to be runtime types. *)
lemma tyenv_well_formed_add_ghost_var:
  assumes wf: "tyenv_well_formed env"
    and ty_wk: "is_well_kinded env ty"
  shows "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd var ty (TE_LocalVars env),
                                 TE_GhostLocals := finsert var (TE_GhostLocals env) \<rparr>)"
proof -
  let ?env' = "env \<lparr> TE_LocalVars := fmupd var ty (TE_LocalVars env),
                     TE_GhostLocals := finsert var (TE_GhostLocals env) \<rparr>"
  from wf have wk: "tyenv_vars_well_kinded env"
    and rt: "tyenv_vars_runtime env"
    and gvs: "tyenv_ghost_vars_subset env"
    and rest: "tyenv_ctors_consistent env"
              "tyenv_payloads_well_kinded env"
              "tyenv_ctor_tyvars_distinct env"
              "tyenv_ctors_by_type_consistent env"
              "tyenv_fun_types_well_kinded env"
              "tyenv_fun_tyvars_distinct env"
              "tyenv_fun_ghost_constraint env"
              "tyenv_nonghost_payloads_runtime env"
              "tyenv_ghost_datatypes_subset env"
    unfolding tyenv_well_formed_def by auto

  have env'_fields: "TE_TypeVars ?env' = TE_TypeVars env"
                     "TE_Datatypes ?env' = TE_Datatypes env"
    by simp_all
  have wk_preserved: "\<And>ty'. is_well_kinded env ty' = is_well_kinded ?env' ty'"
    using is_well_kinded_cong_env[OF env'_fields] by simp

  \<comment> \<open>is_runtime_type only depends on TE_GhostDatatypes and TE_RuntimeTypeVars\<close>
  have gds_eq: "TE_GhostDatatypes ?env' = TE_GhostDatatypes env" by simp
  have rtv_eq: "TE_RuntimeTypeVars ?env' = TE_RuntimeTypeVars env" by simp
  have rt_preserved: "\<And>ty'. is_runtime_type ?env' ty' = is_runtime_type env ty'"
    using is_runtime_type_cong_env[OF gds_eq rtv_eq] by simp

  have "tyenv_vars_well_kinded ?env'"
    using wk ty_wk unfolding tyenv_vars_well_kinded_def
    by (auto simp: wk_preserved split: if_splits)
  moreover have "tyenv_vars_runtime ?env'"
    using rt unfolding tyenv_vars_runtime_def
    by (auto simp: rt_preserved split: if_splits)
  moreover have "tyenv_ghost_vars_subset ?env'"
    using gvs unfolding tyenv_ghost_vars_subset_def by auto
  moreover have "tyenv_return_type_well_kinded ?env'"
    using local.wf tyenv_return_type_well_kinded_def tyenv_well_formed_def wk_preserved
    by auto
  moreover have "tyenv_ctors_consistent ?env'" using rest(1)
    unfolding tyenv_ctors_consistent_def by simp
  moreover have "tyenv_payloads_well_kinded ?env'"
  proof -
    have "\<And>mvs t. is_well_kinded (?env' \<lparr> TE_TypeVars := fset_of_list mvs \<rparr>) t =
                    is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list mvs \<rparr>) t"
      by (rule is_well_kinded_cong_env) simp_all
    thus ?thesis using rest(2) unfolding tyenv_payloads_well_kinded_def by simp
  qed
  moreover have "tyenv_ctor_tyvars_distinct ?env'" using rest(3)
    unfolding tyenv_ctor_tyvars_distinct_def by simp
  moreover have "tyenv_ctors_by_type_consistent ?env'" using rest(4)
    unfolding tyenv_ctors_by_type_consistent_def by simp
  moreover have "tyenv_fun_types_well_kinded ?env'"
  proof -
    have "\<And>tvs t. is_well_kinded (?env' \<lparr> TE_TypeVars := tvs \<rparr>) t =
                    is_well_kinded (env \<lparr> TE_TypeVars := tvs \<rparr>) t"
      by (rule is_well_kinded_cong_env) simp_all
    thus ?thesis using rest(5) unfolding tyenv_fun_types_well_kinded_def by simp
  qed
  moreover have "tyenv_fun_tyvars_distinct ?env'" using rest(6)
    unfolding tyenv_fun_tyvars_distinct_def by simp
  moreover have "tyenv_fun_ghost_constraint ?env'"
  proof -
    have "\<And>rtvs tvs t. is_runtime_type (?env' \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t =
                        is_runtime_type (env \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t"
      by (rule is_runtime_type_cong_env) simp_all
    thus ?thesis using rest(7) unfolding tyenv_fun_ghost_constraint_def Let_def by simp
  qed
  moreover have "tyenv_nonghost_payloads_runtime ?env'"
  proof -
    have "\<And>tvs rtvs t. is_runtime_type (?env' \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t =
                        is_runtime_type (env \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t"
      by (rule is_runtime_type_cong_env) simp_all
    thus ?thesis using rest(8) unfolding tyenv_nonghost_payloads_runtime_def by simp
  qed
  moreover have "tyenv_ghost_datatypes_subset ?env'" using rest(9)
    unfolding tyenv_ghost_datatypes_subset_def by simp
  ultimately show ?thesis unfolding tyenv_well_formed_def by auto
qed

(* tyenv_well_formed does not depend on TE_ConstNames *)
lemma tyenv_well_formed_TE_ConstNames_irrelevant:
  assumes "tyenv_well_formed env"
  shows "tyenv_well_formed (env \<lparr> TE_ConstNames := c \<rparr>)"
proof -
  let ?env' = "env \<lparr> TE_ConstNames := c \<rparr>"
  have wk: "\<And>ty. is_well_kinded ?env' ty = is_well_kinded env ty"
    using is_well_kinded_cong_env[of ?env' env] by simp
  have rt: "\<And>ty. is_runtime_type ?env' ty = is_runtime_type env ty"
    using is_runtime_type_cong_env[of ?env' env] by simp
  have scope_wk: "\<And>tvs t. is_well_kinded (?env' \<lparr> TE_TypeVars := tvs \<rparr>) t =
                            is_well_kinded (env \<lparr> TE_TypeVars := tvs \<rparr>) t"
    by (rule is_well_kinded_cong_env) simp_all
  have scope_rt: "\<And>tvs rtvs t. is_runtime_type (?env' \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t =
                                 is_runtime_type (env \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t"
    by (rule is_runtime_type_cong_env) simp_all
  from assms show ?thesis unfolding tyenv_well_formed_def
    tyenv_vars_well_kinded_def tyenv_vars_runtime_def
    tyenv_ghost_vars_subset_def tyenv_return_type_well_kinded_def tyenv_ctors_consistent_def
    tyenv_payloads_well_kinded_def
    tyenv_ctor_tyvars_distinct_def tyenv_ctors_by_type_consistent_def
    tyenv_fun_types_well_kinded_def
    tyenv_fun_tyvars_distinct_def tyenv_fun_ghost_constraint_def Let_def
    tyenv_nonghost_payloads_runtime_def tyenv_ghost_datatypes_subset_def
    by (force simp: wk rt scope_wk scope_rt)
qed

end
