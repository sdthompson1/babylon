theory CoreTyEnvWellFormed
  imports CoreKindcheck
begin

(* All term variables' types are well-kinded.
   - Local variables typecheck in the current env (with both the TE_AbstractTypes, and
     the enclosing function's type variables, in scope).
   - Global variables typecheck in an env with only the TE_AbstractTypes in scope
     ("local" type variables can't be used for global variables).
   - Note that since is_well_kinded doesn't look at TE_RuntimeTypeVars, we only
     need to override TE_TypeVars here, not TE_RuntimeTypeVars. *)
definition tyenv_vars_well_kinded :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_vars_well_kinded env =
    ((\<forall>name ty. fmlookup (TE_LocalVars env) name = Some ty \<longrightarrow> is_well_kinded env ty) \<and>
     (\<forall>name ty. fmlookup (TE_GlobalVars env) name = Some ty \<longrightarrow>
        is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env \<rparr>) ty))"

(* All nonghost term variables' types are runtime types. Globals are checked
   in an env with "local" TE_TypeVars removed (similarly to tyenv_vars_well_kinded, except
   that this time we do need to modify TE_RuntimeTypeVars, because is_runtime_type depends
   on it). *)
definition tyenv_vars_runtime :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_vars_runtime env =
    ((\<forall>name ty. fmlookup (TE_LocalVars env) name = Some ty
               \<and> name |\<notin>| TE_GhostLocals env
               \<longrightarrow> is_runtime_type env ty) \<and>
     (\<forall>name ty. fmlookup (TE_GlobalVars env) name = Some ty
               \<longrightarrow> is_runtime_type (env \<lparr> TE_TypeVars := TE_AbstractTypes env,
                                          TE_RuntimeTypeVars := TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env \<rparr>) ty))"

(* Ghost locals are a subset of local variable names *)
definition tyenv_ghost_vars_subset :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_ghost_vars_subset env =
    (TE_GhostLocals env |\<subseteq>| fmdom (TE_LocalVars env))"

(* The return type is well-kinded *)
definition tyenv_return_type_well_kinded :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_return_type_well_kinded env =
    is_well_kinded env (TE_ReturnType env)"

(* For a non-ghost (executable) function, the return type must be a runtime type. *)
definition tyenv_return_type_runtime :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_return_type_runtime env =
    (TE_FunctionGhost env = NotGhost \<longrightarrow> is_runtime_type env (TE_ReturnType env))"

(* Data constructors are consistent with datatypes:
   For each ctor in TE_DataCtors mapping to (dtName, tyVars, payload),
   dtName must be in TE_Datatypes with matching numTyArgs *)
definition tyenv_ctors_consistent :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_ctors_consistent env =
    (\<forall>ctorName dtName tyVars payload.
      fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload) \<longrightarrow>
      fmlookup (TE_Datatypes env) dtName = Some (length tyVars))"

(* Data constructor payload types are well-kinded, in an appropriate env. *)
(* Note that well-kindedness depends only on TE_Datatypes and TE_TypeVars, so overriding
   only TE_TypeVars is appropriate here. *)
definition tyenv_payloads_well_kinded :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_payloads_well_kinded env =
    (\<forall>ctorName dtName tyVars payload.
      fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload) \<longrightarrow>
      is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyVars \<rparr>) payload)"

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
        (\<exists>tyVars payload.
          fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload))))"

(* Function arg and return types are well-kinded in an appropriate env. *)
definition tyenv_fun_types_well_kinded :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_fun_types_well_kinded env =
    (\<forall>funName info. fmlookup (TE_Functions env) funName = Some info \<longrightarrow>
      (\<forall>ty \<in> fst ` set (FI_TmArgs info).
          is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty) \<and>
      is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) (FI_ReturnType info))"

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
      (let fenv = env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list (FI_TyArgs info),
                        TE_RuntimeTypeVars := (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                               |\<union>| fset_of_list (FI_TyArgs info) \<rparr>
       in (\<forall>ty \<in> fst ` set (FI_TmArgs info). is_runtime_type fenv ty) \<and>
          is_runtime_type fenv (FI_ReturnType info)))"

(* For non-ghost datatypes, all constructor payload types must be runtime.
   This ensures variant types can be represented in memory (e.g. as tagged unions). *)
definition tyenv_nonghost_payloads_runtime :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_nonghost_payloads_runtime env =
    (\<forall>ctorName dtName tyVars payload.
      fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload) \<longrightarrow>
      dtName |\<notin>| TE_GhostDatatypes env \<longrightarrow>
      is_runtime_type (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyVars,
                             TE_RuntimeTypeVars := (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                                    |\<union>| fset_of_list tyVars \<rparr>) payload)"

(* Ghost datatypes must be a subset of all datatypes *)
definition tyenv_ghost_datatypes_subset :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_ghost_datatypes_subset env =
    (TE_GhostDatatypes env |\<subseteq>| fmdom (TE_Datatypes env))"

(* All datatypes are inhabited (have at least one data constructor). This
   comes in two parts:
    (1) Every datatype listed in TE_Datatypes also has a constructor-list
        in TE_DataCtorsByType.
    (2) All of the constructor-lists in TE_DataCtorsByType are non-empty.
   Note that the reverse inclusion, fmdom (TE_DataCtorsByType env) |\<subseteq>|
   fmdom (TE_Datatypes env), is proved in tyenv_bytype_dom_subset below. *)
definition tyenv_datatypes_nonempty :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_datatypes_nonempty env =
    (fmdom (TE_Datatypes env) |\<subseteq>| fmdom (TE_DataCtorsByType env)
     \<and> (\<forall>dtName ctors.
          fmlookup (TE_DataCtorsByType env) dtName = Some ctors \<longrightarrow> ctors \<noteq> []))"

(* TE_RuntimeTypeVars is a subset of TE_TypeVars: a type variable can only be a
   runtime type variable if it is in scope at all. *)
definition tyenv_runtime_tyvars_subset :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_runtime_tyvars_subset env =
    (TE_RuntimeTypeVars env |\<subseteq>| TE_TypeVars env)"

(* The module-level abstract types are a subset of the in-scope type variables:
   an abstract type behaves like a globally scoped (opaque) type variable. *)
definition tyenv_abstract_types_subset :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_abstract_types_subset env =
    (TE_AbstractTypes env |\<subseteq>| TE_TypeVars env)"

(* A type environment is well-formed if all the above conditions hold *)
definition tyenv_well_formed :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_well_formed env =
    (tyenv_vars_well_kinded env \<and>
     tyenv_vars_runtime env \<and>
     tyenv_ghost_vars_subset env \<and>
     tyenv_return_type_well_kinded env \<and>
     tyenv_return_type_runtime env \<and>
     tyenv_ctors_consistent env \<and>
     tyenv_payloads_well_kinded env \<and>
     tyenv_ctor_tyvars_distinct env \<and>
     tyenv_ctors_by_type_consistent env \<and>
     tyenv_fun_types_well_kinded env \<and>
     tyenv_fun_tyvars_distinct env \<and>
     tyenv_fun_ghost_constraint env \<and>
     tyenv_nonghost_payloads_runtime env \<and>
     tyenv_ghost_datatypes_subset env \<and>
     tyenv_runtime_tyvars_subset env \<and>
     tyenv_abstract_types_subset env \<and>
     tyenv_datatypes_nonempty env)"

(* The domain of TE_DataCtorsByType is contained in the domain of TE_Datatypes:
   an entry's constructor list is nonempty, its first constructor maps back to
   the entry's name in TE_DataCtors, and that constructor's datatype is
   registered in TE_Datatypes. *)
lemma tyenv_bytype_dom_subset:
  assumes cons: "tyenv_ctors_consistent env"
      and btc: "tyenv_ctors_by_type_consistent env"
      and dne: "tyenv_datatypes_nonempty env"
  shows "fmdom (TE_DataCtorsByType env) |\<subseteq>| fmdom (TE_Datatypes env)"
proof
  fix dtName assume "dtName |\<in>| fmdom (TE_DataCtorsByType env)"
  then obtain ctors where lk: "fmlookup (TE_DataCtorsByType env) dtName = Some ctors"
    by (metis fmdomE)
  have "ctors \<noteq> []"
    using dne lk unfolding tyenv_datatypes_nonempty_def by blast
  then obtain c cs where "ctors = c # cs" by (cases ctors) auto
  then have "c \<in> set ctors" by simp
  then obtain tyVars payload where
    "fmlookup (TE_DataCtors env) c = Some (dtName, tyVars, payload)"
    using btc lk unfolding tyenv_ctors_by_type_consistent_def by blast
  then have "fmlookup (TE_Datatypes env) dtName = Some (length tyVars)"
    using cons unfolding tyenv_ctors_consistent_def by blast
  then show "dtName |\<in>| fmdom (TE_Datatypes env)" by (rule fmdomI)
qed

(* Every registered datatype has a "first" constructor. *)
lemma tyenv_datatypes_nonempty_first_ctor:
  assumes dne: "tyenv_datatypes_nonempty env"
      and dt: "dtName |\<in>| fmdom (TE_Datatypes env)"
  shows "\<exists>ctorName ctors.
           fmlookup (TE_DataCtorsByType env) dtName = Some (ctorName # ctors)"
proof -
  from dne dt have "dtName |\<in>| fmdom (TE_DataCtorsByType env)"
    unfolding tyenv_datatypes_nonempty_def by blast
  then obtain ctors where lk: "fmlookup (TE_DataCtorsByType env) dtName = Some ctors"
    by (metis fmdomE)
  have "ctors \<noteq> []"
    using dne lk unfolding tyenv_datatypes_nonempty_def by blast
  then show ?thesis using lk by (cases ctors) auto
qed

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
    and ret_rt: "tyenv_return_type_runtime env"
    and rest: "tyenv_ctors_consistent env"
              "tyenv_payloads_well_kinded env"
              "tyenv_ctor_tyvars_distinct env"
              "tyenv_ctors_by_type_consistent env"
              "tyenv_fun_types_well_kinded env"
              "tyenv_fun_tyvars_distinct env"
              "tyenv_fun_ghost_constraint env"
              "tyenv_nonghost_payloads_runtime env"
              "tyenv_ghost_datatypes_subset env"
              "tyenv_runtime_tyvars_subset env"
              "tyenv_abstract_types_subset env"
              "tyenv_datatypes_nonempty env"
    unfolding tyenv_well_formed_def by auto

  \<comment> \<open>?env' agrees with env on the kind- and runtime-relevant fields, and on TE_AbstractTypes. \<close>
  have abs_eq: "TE_AbstractTypes ?env' = TE_AbstractTypes env" by simp

  \<comment> \<open>is_well_kinded only depends on TE_Datatypes and TE_TypeVars, not TE_LocalVars\<close>
  have env'_fields: "TE_TypeVars ?env' = TE_TypeVars env"
                     "TE_Datatypes ?env' = TE_Datatypes env"
    by simp_all
  have wk_preserved: "\<And>ty'. is_well_kinded env ty' = is_well_kinded ?env' ty'"
    using is_well_kinded_cong_env[OF env'_fields] by simp

  \<comment> \<open>Generic scope congruences: any override of the tyvar fields agrees between env and ?env'. \<close>
  have wk_scope_eq: "\<And>tvs t. is_well_kinded (?env' \<lparr> TE_TypeVars := tvs \<rparr>) t =
                               is_well_kinded (env \<lparr> TE_TypeVars := tvs \<rparr>) t"
    by (rule is_well_kinded_cong_env) simp_all
  \<comment> \<open>is_runtime_type only depends on TE_GhostDatatypes and TE_RuntimeTypeVars\<close>
  have gds_eq: "TE_GhostDatatypes ?env' = TE_GhostDatatypes env" by simp
  have rtv_eq: "TE_RuntimeTypeVars ?env' = TE_RuntimeTypeVars env" by simp
  have rt_preserved: "\<And>ty'. is_runtime_type ?env' ty' = is_runtime_type env ty'"
    using is_runtime_type_cong_env[OF gds_eq rtv_eq] by simp

  have rt_scope_eq:
    "\<And>tvs rtvs t. is_runtime_type (?env' \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t =
                    is_runtime_type (env \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t"
    by (rule is_runtime_type_cong_env) simp_all

  have "tyenv_vars_well_kinded ?env'"
    using wk ty_wk unfolding tyenv_vars_well_kinded_def
    by (auto simp: wk_preserved wk_scope_eq abs_eq split: if_splits)
  moreover have "tyenv_vars_runtime ?env'"
    using rt ty_runtime unfolding tyenv_vars_runtime_def
    by (auto simp: rt_preserved rt_scope_eq abs_eq rtv_eq split: if_splits)
  moreover have "tyenv_ghost_vars_subset ?env'"
    using gvs unfolding tyenv_ghost_vars_subset_def by auto
  moreover have "tyenv_return_type_well_kinded ?env'"
    using local.wf tyenv_return_type_well_kinded_def tyenv_well_formed_def wk_preserved
    by auto
  moreover have "tyenv_return_type_runtime ?env'"
    using ret_rt rt_preserved unfolding tyenv_return_type_runtime_def by simp
  moreover have "tyenv_ctors_consistent ?env'" using rest(1)
    unfolding tyenv_ctors_consistent_def by simp
  moreover have "tyenv_payloads_well_kinded ?env'"
    using rest(2) unfolding tyenv_payloads_well_kinded_def
    by (simp add: wk_scope_eq abs_eq)
  moreover have "tyenv_ctor_tyvars_distinct ?env'" using rest(3)
    unfolding tyenv_ctor_tyvars_distinct_def by simp
  moreover have "tyenv_ctors_by_type_consistent ?env'" using rest(4)
    unfolding tyenv_ctors_by_type_consistent_def by simp
  moreover have "tyenv_fun_types_well_kinded ?env'"
    using rest(5) unfolding tyenv_fun_types_well_kinded_def
    by (simp add: wk_scope_eq abs_eq)
  moreover have "tyenv_fun_tyvars_distinct ?env'" using rest(6)
    unfolding tyenv_fun_tyvars_distinct_def by simp
  moreover have "tyenv_fun_ghost_constraint ?env'"
    using rest(7) unfolding tyenv_fun_ghost_constraint_def Let_def
    by (simp add: rt_scope_eq abs_eq rtv_eq)
  moreover have "tyenv_nonghost_payloads_runtime ?env'"
    using rest(8) unfolding tyenv_nonghost_payloads_runtime_def
    by (simp add: rt_scope_eq abs_eq rtv_eq)
  moreover have "tyenv_ghost_datatypes_subset ?env'" using rest(9)
    unfolding tyenv_ghost_datatypes_subset_def by simp
  moreover have "tyenv_runtime_tyvars_subset ?env'" using rest(10)
    unfolding tyenv_runtime_tyvars_subset_def by simp
  moreover have "tyenv_abstract_types_subset ?env'" using rest(11)
    unfolding tyenv_abstract_types_subset_def by simp
  moreover have "tyenv_datatypes_nonempty ?env'" using rest(12)
    unfolding tyenv_datatypes_nonempty_def by simp
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
    and ret_rt: "tyenv_return_type_runtime env"
    and rest: "tyenv_ctors_consistent env"
              "tyenv_payloads_well_kinded env"
              "tyenv_ctor_tyvars_distinct env"
              "tyenv_ctors_by_type_consistent env"
              "tyenv_fun_types_well_kinded env"
              "tyenv_fun_tyvars_distinct env"
              "tyenv_fun_ghost_constraint env"
              "tyenv_nonghost_payloads_runtime env"
              "tyenv_ghost_datatypes_subset env"
              "tyenv_runtime_tyvars_subset env"
              "tyenv_abstract_types_subset env"
              "tyenv_datatypes_nonempty env"
    unfolding tyenv_well_formed_def by auto

  have abs_eq: "TE_AbstractTypes ?env' = TE_AbstractTypes env" by simp

  have env'_fields: "TE_TypeVars ?env' = TE_TypeVars env"
                     "TE_Datatypes ?env' = TE_Datatypes env"
    by simp_all
  have wk_preserved: "\<And>ty'. is_well_kinded env ty' = is_well_kinded ?env' ty'"
    using is_well_kinded_cong_env[OF env'_fields] by simp

  have wk_scope_eq: "\<And>tvs t. is_well_kinded (?env' \<lparr> TE_TypeVars := tvs \<rparr>) t =
                               is_well_kinded (env \<lparr> TE_TypeVars := tvs \<rparr>) t"
    by (rule is_well_kinded_cong_env) simp_all
  \<comment> \<open>is_runtime_type only depends on TE_GhostDatatypes and TE_RuntimeTypeVars\<close>
  have gds_eq: "TE_GhostDatatypes ?env' = TE_GhostDatatypes env" by simp
  have rtv_eq: "TE_RuntimeTypeVars ?env' = TE_RuntimeTypeVars env" by simp
  have rt_preserved: "\<And>ty'. is_runtime_type ?env' ty' = is_runtime_type env ty'"
    using is_runtime_type_cong_env[OF gds_eq rtv_eq] by simp

  have rt_scope_eq:
    "\<And>tvs rtvs t. is_runtime_type (?env' \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t =
                    is_runtime_type (env \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t"
    by (rule is_runtime_type_cong_env) simp_all

  have "tyenv_vars_well_kinded ?env'"
    using wk ty_wk unfolding tyenv_vars_well_kinded_def
    by (auto simp: wk_preserved wk_scope_eq abs_eq split: if_splits)
  moreover have "tyenv_vars_runtime ?env'"
    using rt unfolding tyenv_vars_runtime_def
    by (auto simp: rt_preserved rt_scope_eq abs_eq rtv_eq split: if_splits)
  moreover have "tyenv_ghost_vars_subset ?env'"
    using gvs unfolding tyenv_ghost_vars_subset_def by auto
  moreover have "tyenv_return_type_well_kinded ?env'"
    using local.wf tyenv_return_type_well_kinded_def tyenv_well_formed_def wk_preserved
    by auto
  moreover have "tyenv_return_type_runtime ?env'"
    using ret_rt rt_preserved unfolding tyenv_return_type_runtime_def by simp
  moreover have "tyenv_ctors_consistent ?env'" using rest(1)
    unfolding tyenv_ctors_consistent_def by simp
  moreover have "tyenv_payloads_well_kinded ?env'"
    using rest(2) unfolding tyenv_payloads_well_kinded_def
    by (simp add: wk_scope_eq abs_eq)
  moreover have "tyenv_ctor_tyvars_distinct ?env'" using rest(3)
    unfolding tyenv_ctor_tyvars_distinct_def by simp
  moreover have "tyenv_ctors_by_type_consistent ?env'" using rest(4)
    unfolding tyenv_ctors_by_type_consistent_def by simp
  moreover have "tyenv_fun_types_well_kinded ?env'"
    using rest(5) unfolding tyenv_fun_types_well_kinded_def
    by (simp add: wk_scope_eq abs_eq)
  moreover have "tyenv_fun_tyvars_distinct ?env'" using rest(6)
    unfolding tyenv_fun_tyvars_distinct_def by simp
  moreover have "tyenv_fun_ghost_constraint ?env'"
    using rest(7) unfolding tyenv_fun_ghost_constraint_def Let_def
    by (simp add: rt_scope_eq abs_eq rtv_eq)
  moreover have "tyenv_nonghost_payloads_runtime ?env'"
    using rest(8) unfolding tyenv_nonghost_payloads_runtime_def
    by (simp add: rt_scope_eq abs_eq rtv_eq)
  moreover have "tyenv_ghost_datatypes_subset ?env'" using rest(9)
    unfolding tyenv_ghost_datatypes_subset_def by simp
  moreover have "tyenv_runtime_tyvars_subset ?env'" using rest(10)
    unfolding tyenv_runtime_tyvars_subset_def by simp
  moreover have "tyenv_abstract_types_subset ?env'" using rest(11)
    unfolding tyenv_abstract_types_subset_def by simp
  moreover have "tyenv_datatypes_nonempty ?env'" using rest(12)
    unfolding tyenv_datatypes_nonempty_def by simp
  ultimately show ?thesis unfolding tyenv_well_formed_def by auto
qed

(* tyenv_well_formed does not depend on TE_ConstLocals *)
lemma tyenv_well_formed_TE_ConstLocals_irrelevant:
  assumes "tyenv_well_formed env"
  shows "tyenv_well_formed (env \<lparr> TE_ConstLocals := c \<rparr>)"
proof -
  let ?env' = "env \<lparr> TE_ConstLocals := c \<rparr>"
  have wk: "\<And>ty. is_well_kinded ?env' ty = is_well_kinded env ty"
    using is_well_kinded_cong_env[of ?env' env] by simp
  have rt: "\<And>ty. is_runtime_type ?env' ty = is_runtime_type env ty"
    using is_runtime_type_cong_env[of ?env' env] by simp
  have scope_wk_one: "\<And>tvs t. is_well_kinded (?env' \<lparr> TE_TypeVars := tvs \<rparr>) t =
                                is_well_kinded (env \<lparr> TE_TypeVars := tvs \<rparr>) t"
    by (rule is_well_kinded_cong_env) simp_all
  have scope_rt: "\<And>tvs rtvs t. is_runtime_type (?env' \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t =
                                 is_runtime_type (env \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t"
    by (rule is_runtime_type_cong_env) simp_all
  from assms show ?thesis unfolding tyenv_well_formed_def
    tyenv_vars_well_kinded_def tyenv_vars_runtime_def
    tyenv_ghost_vars_subset_def tyenv_return_type_well_kinded_def
    tyenv_return_type_runtime_def tyenv_ctors_consistent_def
    tyenv_payloads_well_kinded_def
    tyenv_ctor_tyvars_distinct_def tyenv_ctors_by_type_consistent_def
    tyenv_fun_types_well_kinded_def
    tyenv_fun_tyvars_distinct_def
    tyenv_fun_ghost_constraint_def Let_def
    tyenv_nonghost_payloads_runtime_def tyenv_ghost_datatypes_subset_def
    tyenv_runtime_tyvars_subset_def
    tyenv_abstract_types_subset_def
    tyenv_datatypes_nonempty_def
    by (force simp: wk rt scope_wk_one scope_rt)
qed

(* tyenv_well_formed does not depend on TE_ProofGoal *)
lemma tyenv_well_formed_TE_ProofGoal_irrelevant:
  assumes "tyenv_well_formed env"
  shows "tyenv_well_formed (env \<lparr> TE_ProofGoal := g \<rparr>)"
proof -
  let ?env' = "env \<lparr> TE_ProofGoal := g \<rparr>"
  have wk: "\<And>ty. is_well_kinded ?env' ty = is_well_kinded env ty"
    using is_well_kinded_cong_env[of ?env' env] by simp
  have rt: "\<And>ty. is_runtime_type ?env' ty = is_runtime_type env ty"
    using is_runtime_type_cong_env[of ?env' env] by simp
  have scope_wk_one: "\<And>tvs t. is_well_kinded (?env' \<lparr> TE_TypeVars := tvs \<rparr>) t =
                                is_well_kinded (env \<lparr> TE_TypeVars := tvs \<rparr>) t"
    by (rule is_well_kinded_cong_env) simp_all
  have scope_rt: "\<And>tvs rtvs t. is_runtime_type (?env' \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t =
                                 is_runtime_type (env \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t"
    by (rule is_runtime_type_cong_env) simp_all
  from assms show ?thesis unfolding tyenv_well_formed_def
    tyenv_vars_well_kinded_def tyenv_vars_runtime_def
    tyenv_ghost_vars_subset_def tyenv_return_type_well_kinded_def
    tyenv_return_type_runtime_def tyenv_ctors_consistent_def
    tyenv_payloads_well_kinded_def
    tyenv_ctor_tyvars_distinct_def tyenv_ctors_by_type_consistent_def
    tyenv_fun_types_well_kinded_def
    tyenv_fun_tyvars_distinct_def
    tyenv_fun_ghost_constraint_def Let_def
    tyenv_nonghost_payloads_runtime_def tyenv_ghost_datatypes_subset_def
    tyenv_runtime_tyvars_subset_def
    tyenv_abstract_types_subset_def
    tyenv_datatypes_nonempty_def
    by (force simp: wk rt scope_wk_one scope_rt)
qed

(* tyenv_well_formed does not depend on TE_ProofTopLevel *)
lemma tyenv_well_formed_TE_ProofTopLevel_irrelevant:
  assumes "tyenv_well_formed env"
  shows "tyenv_well_formed (env \<lparr> TE_ProofTopLevel := b \<rparr>)"
proof -
  let ?env' = "env \<lparr> TE_ProofTopLevel := b \<rparr>"
  have wk: "\<And>ty. is_well_kinded ?env' ty = is_well_kinded env ty"
    using is_well_kinded_cong_env[of ?env' env] by simp
  have rt: "\<And>ty. is_runtime_type ?env' ty = is_runtime_type env ty"
    using is_runtime_type_cong_env[of ?env' env] by simp
  have scope_wk_one: "\<And>tvs t. is_well_kinded (?env' \<lparr> TE_TypeVars := tvs \<rparr>) t =
                                is_well_kinded (env \<lparr> TE_TypeVars := tvs \<rparr>) t"
    by (rule is_well_kinded_cong_env) simp_all
  have scope_rt: "\<And>tvs rtvs t. is_runtime_type (?env' \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t =
                                 is_runtime_type (env \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t"
    by (rule is_runtime_type_cong_env) simp_all
  from assms show ?thesis unfolding tyenv_well_formed_def
    tyenv_vars_well_kinded_def tyenv_vars_runtime_def
    tyenv_ghost_vars_subset_def tyenv_return_type_well_kinded_def
    tyenv_return_type_runtime_def tyenv_ctors_consistent_def
    tyenv_payloads_well_kinded_def
    tyenv_ctor_tyvars_distinct_def tyenv_ctors_by_type_consistent_def
    tyenv_fun_types_well_kinded_def
    tyenv_fun_tyvars_distinct_def
    tyenv_fun_ghost_constraint_def Let_def
    tyenv_nonghost_payloads_runtime_def tyenv_ghost_datatypes_subset_def
    tyenv_runtime_tyvars_subset_def
    tyenv_abstract_types_subset_def
    tyenv_datatypes_nonempty_def
    by (force simp: wk rt scope_wk_one scope_rt)
qed

(* Growing TE_TypeVars and TE_RuntimeTypeVars preserves tyenv_well_formed.
   The predicates using inner envs that override TE_TypeVars / TE_RuntimeTypeVars
   (payloads, fun types, ghost-constraints, non-ghost payloads) are unaffected
   because the override drops the extension. The remaining kind/runtime
   conjuncts follow from monotonicity of is_well_kinded and is_runtime_type. *)
lemma tyenv_well_formed_extend_tyvars:
  assumes "tyenv_well_formed env"
      and "extraRT |\<subseteq>| extraTV"
  shows "tyenv_well_formed
           (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                  TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>)"
proof -
  let ?env' = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>"
  let ?A = "TE_AbstractTypes env"
  have abs_eq: "TE_AbstractTypes ?env' = ?A" by simp

  \<comment> \<open>is_well_kinded ignores TE_RuntimeTypeVars, so a leftover TE_RuntimeTypeVars
     update (which appears after simp normalizes ?env' with a TE_TypeVars override)
     can be dropped. \<close>
  have wk_drop_rtv: "\<And>r tvs t. is_well_kinded (env \<lparr> TE_RuntimeTypeVars := r, TE_TypeVars := tvs \<rparr>) t =
                                 is_well_kinded (env \<lparr> TE_TypeVars := tvs \<rparr>) t"
    by (rule is_well_kinded_cong_env) simp_all

  from assms have vars_wk: "tyenv_vars_well_kinded env"
    and vars_rt: "tyenv_vars_runtime env"
    and ghost_subset: "tyenv_ghost_vars_subset env"
    and ret_wk: "tyenv_return_type_well_kinded env"
    and ret_rt: "tyenv_return_type_runtime env"
    and ctors_cons: "tyenv_ctors_consistent env"
    and payloads_wk: "tyenv_payloads_well_kinded env"
    and ctor_tyvars_distinct: "tyenv_ctor_tyvars_distinct env"
    and ctors_by_type: "tyenv_ctors_by_type_consistent env"
    and fun_types_wk: "tyenv_fun_types_well_kinded env"
    and fun_tyvars_distinct: "tyenv_fun_tyvars_distinct env"
    and fun_ghost: "tyenv_fun_ghost_constraint env"
    and nonghost_payloads: "tyenv_nonghost_payloads_runtime env"
    and ghost_dt_subset: "tyenv_ghost_datatypes_subset env"
    and rt_subset: "tyenv_runtime_tyvars_subset env"
    and abs_subset: "tyenv_abstract_types_subset env"
    and dt_nonempty: "tyenv_datatypes_nonempty env"
    unfolding tyenv_well_formed_def by auto

  \<comment> \<open>Global (cleared) branch helper for tyenv_vars_runtime. The cleared env on the
     ?env' side pins TE_TypeVars to ?A (= TE_AbstractTypes on both sides) and
     TE_RuntimeTypeVars to ?A |\<inter>| TE_RuntimeTypeVars ?env'. We compare against the
     env-side cleared env: the ?env' runtime set is a superset, so the transfer
     lemma applies.\<close>
  have rtv_env'_eq: "TE_RuntimeTypeVars ?env' = TE_RuntimeTypeVars env |\<union>| extraRT" by simp
  let ?e1 = "env \<lparr> TE_TypeVars := ?A, TE_RuntimeTypeVars := ?A |\<inter>| TE_RuntimeTypeVars env \<rparr>"
  let ?e2 = "env \<lparr> TE_TypeVars := ?A,
                   TE_RuntimeTypeVars := ?A |\<inter>| (TE_RuntimeTypeVars env |\<union>| extraRT) \<rparr>"
  have rt_cleared: "\<And>ty'. is_runtime_type ?e1 ty' \<Longrightarrow> is_runtime_type ?e2 ty'"
  proof -
    fix ty'
    assume rt1: "is_runtime_type ?e1 ty'"
    have gd: "TE_GhostDatatypes ?e2 = TE_GhostDatatypes ?e1" by simp
    have tv_sub: "type_tyvars ty' \<subseteq> fset (TE_RuntimeTypeVars ?e1)"
      using is_runtime_type_tyvars_subset[OF rt1] .
    have "TE_RuntimeTypeVars ?e1 |\<subseteq>| TE_RuntimeTypeVars ?e2" by auto
    hence "fset (TE_RuntimeTypeVars ?e1) \<subseteq> fset (TE_RuntimeTypeVars ?e2)"
      by (simp add: less_eq_fset.rep_eq)
    with tv_sub have tv_sub2: "type_tyvars ty' \<subseteq> fset (TE_RuntimeTypeVars ?e2)" by blast
    show "is_runtime_type ?e2 ty'"
      using is_runtime_type_transfer[OF rt1 tv_sub2 gd] .
  qed

  \<comment> \<open>General monotone transfer for the function/ctor scopes. The ?env'-side runtime
     set differs from the env-side only by including (?A |\<inter>| extraRT), which is a
     superset, so is_runtime_type transfers (same TE_TypeVars, same TE_GhostDatatypes).\<close>
  have rt_scope_mono:
    "\<And>extraTV' base t.
       is_runtime_type (env \<lparr> TE_TypeVars := ?A |\<union>| extraTV',
                              TE_RuntimeTypeVars := (?A |\<inter>| TE_RuntimeTypeVars env) |\<union>| base \<rparr>) t \<Longrightarrow>
       is_runtime_type (?env' \<lparr> TE_TypeVars := ?A |\<union>| extraTV',
                                TE_RuntimeTypeVars := (?A |\<inter>| TE_RuntimeTypeVars ?env') |\<union>| base \<rparr>) t"
  proof -
    fix extraTV' base t
    let ?f1 = "env \<lparr> TE_TypeVars := ?A |\<union>| extraTV',
                     TE_RuntimeTypeVars := (?A |\<inter>| TE_RuntimeTypeVars env) |\<union>| base \<rparr>"
    let ?f2 = "?env' \<lparr> TE_TypeVars := ?A |\<union>| extraTV',
                       TE_RuntimeTypeVars := (?A |\<inter>| TE_RuntimeTypeVars ?env') |\<union>| base \<rparr>"
    assume rt1: "is_runtime_type ?f1 t"
    have gd: "TE_GhostDatatypes ?f2 = TE_GhostDatatypes ?f1" by simp
    have tv_sub: "type_tyvars t \<subseteq> fset (TE_RuntimeTypeVars ?f1)"
      using is_runtime_type_tyvars_subset[OF rt1] .
    have "TE_RuntimeTypeVars ?f1 |\<subseteq>| TE_RuntimeTypeVars ?f2"
      by (simp add: rtv_env'_eq) blast
    hence "fset (TE_RuntimeTypeVars ?f1) \<subseteq> fset (TE_RuntimeTypeVars ?f2)"
      by (simp add: less_eq_fset.rep_eq)
    with tv_sub have tv_sub2: "type_tyvars t \<subseteq> fset (TE_RuntimeTypeVars ?f2)" by blast
    show "is_runtime_type ?f2 t"
      using is_runtime_type_transfer[OF rt1 tv_sub2 gd] .
  qed

  have "tyenv_vars_well_kinded ?env'"
    unfolding tyenv_vars_well_kinded_def
  proof (intro conjI allI impI)
    fix name ty'
    assume "fmlookup (TE_LocalVars ?env') name = Some ty'"
    hence "fmlookup (TE_LocalVars env) name = Some ty'" by simp
    with vars_wk have "is_well_kinded env ty'"
      unfolding tyenv_vars_well_kinded_def by blast
    thus "is_well_kinded ?env' ty'" using is_well_kinded_extend_tyvars by simp
  next
    fix name ty'
    assume "fmlookup (TE_GlobalVars ?env') name = Some ty'"
    hence "fmlookup (TE_GlobalVars env) name = Some ty'" by simp
    with vars_wk have "is_well_kinded (env \<lparr> TE_TypeVars := ?A \<rparr>) ty'"
      unfolding tyenv_vars_well_kinded_def by blast
    thus "is_well_kinded (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env' \<rparr>) ty'"
      using is_well_kinded_cong_env[where env = "env \<lparr> TE_TypeVars := ?A \<rparr>"
                                      and env' = "?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env' \<rparr>"]
      by (simp add: abs_eq)
  qed
  moreover have "tyenv_vars_runtime ?env'"
    unfolding tyenv_vars_runtime_def
  proof (intro conjI allI impI)
    fix name ty'
    assume "fmlookup (TE_LocalVars ?env') name = Some ty' \<and> name |\<notin>| TE_GhostLocals ?env'"
    hence "fmlookup (TE_LocalVars env) name = Some ty' \<and> name |\<notin>| TE_GhostLocals env" by simp
    with vars_rt have "is_runtime_type env ty'"
      unfolding tyenv_vars_runtime_def by blast
    thus "is_runtime_type ?env' ty'" using is_runtime_type_extend_runtime_tyvars by simp
  next
    fix name ty'
    assume "fmlookup (TE_GlobalVars ?env') name = Some ty'"
    hence "fmlookup (TE_GlobalVars env) name = Some ty'" by simp
    with vars_rt have "is_runtime_type ?e1 ty'"
      unfolding tyenv_vars_runtime_def by blast
    hence "is_runtime_type ?e2 ty'" using rt_cleared by simp
    thus "is_runtime_type (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env',
            TE_RuntimeTypeVars := TE_AbstractTypes ?env' |\<inter>| TE_RuntimeTypeVars ?env' \<rparr>) ty'"
      by (simp add: abs_eq rtv_env'_eq)
  qed
  moreover have "tyenv_ghost_vars_subset ?env'"
    using ghost_subset unfolding tyenv_ghost_vars_subset_def by simp
  moreover have "tyenv_return_type_well_kinded ?env'"
    using ret_wk is_well_kinded_extend_tyvars
    unfolding tyenv_return_type_well_kinded_def by simp
  moreover have "tyenv_return_type_runtime ?env'"
    using ret_rt is_runtime_type_extend_runtime_tyvars
    unfolding tyenv_return_type_runtime_def by simp
  moreover have "tyenv_ctors_consistent ?env'"
    using ctors_cons unfolding tyenv_ctors_consistent_def by simp
  moreover have "tyenv_payloads_well_kinded ?env'"
    using payloads_wk unfolding tyenv_payloads_well_kinded_def
    by (simp add: wk_drop_rtv abs_eq)
  moreover have "tyenv_ctor_tyvars_distinct ?env'"
    using ctor_tyvars_distinct unfolding tyenv_ctor_tyvars_distinct_def by simp
  moreover have "tyenv_ctors_by_type_consistent ?env'"
    using ctors_by_type unfolding tyenv_ctors_by_type_consistent_def by simp
  moreover have "tyenv_fun_types_well_kinded ?env'"
    using fun_types_wk unfolding tyenv_fun_types_well_kinded_def
    by (simp add: wk_drop_rtv abs_eq)
  moreover have "tyenv_fun_tyvars_distinct ?env'"
    using fun_tyvars_distinct unfolding tyenv_fun_tyvars_distinct_def by simp
  moreover have "tyenv_fun_ghost_constraint ?env'"
    unfolding tyenv_fun_ghost_constraint_def Let_def
  proof (intro allI impI, elim conjE)
    fix funName info
    assume info_lk': "fmlookup (TE_Functions ?env') funName = Some info"
       and ng: "FI_Ghost info = NotGhost"
    from info_lk' have info_lk: "fmlookup (TE_Functions env) funName = Some info" by simp
    from fun_ghost info_lk ng have
      args_rt: "\<forall>ty \<in> fst ` set (FI_TmArgs info).
            is_runtime_type (env \<lparr> TE_TypeVars := ?A |\<union>| fset_of_list (FI_TyArgs info),
                  TE_RuntimeTypeVars := (?A |\<inter>| TE_RuntimeTypeVars env) |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
      and ret_rt': "is_runtime_type (env \<lparr> TE_TypeVars := ?A |\<union>| fset_of_list (FI_TyArgs info),
                  TE_RuntimeTypeVars := (?A |\<inter>| TE_RuntimeTypeVars env) |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                  (FI_ReturnType info)"
      unfolding tyenv_fun_ghost_constraint_def Let_def by auto
    show "(\<forall>ty \<in> fst ` set (FI_TmArgs info).
              is_runtime_type (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env' |\<union>| fset_of_list (FI_TyArgs info),
                  TE_RuntimeTypeVars := (TE_AbstractTypes ?env' |\<inter>| TE_RuntimeTypeVars ?env')
                                         |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty) \<and>
           is_runtime_type (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env' |\<union>| fset_of_list (FI_TyArgs info),
                  TE_RuntimeTypeVars := (TE_AbstractTypes ?env' |\<inter>| TE_RuntimeTypeVars ?env')
                                         |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                  (FI_ReturnType info)"
      using args_rt ret_rt' rt_scope_mono by (simp add: abs_eq)
  qed
  moreover have "tyenv_nonghost_payloads_runtime ?env'"
    unfolding tyenv_nonghost_payloads_runtime_def
  proof (intro allI impI)
    fix ctorName dtName tyVars payload
    assume ctor_lk': "fmlookup (TE_DataCtors ?env') ctorName = Some (dtName, tyVars, payload)"
       and ng_dt: "dtName |\<notin>| TE_GhostDatatypes ?env'"
    from ctor_lk' have ctor_lk: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload)"
      by simp
    from ng_dt have ng_dt_env: "dtName |\<notin>| TE_GhostDatatypes env" by simp
    from nonghost_payloads ctor_lk ng_dt_env
    have "is_runtime_type (env \<lparr> TE_TypeVars := ?A |\<union>| fset_of_list tyVars,
              TE_RuntimeTypeVars := (?A |\<inter>| TE_RuntimeTypeVars env) |\<union>| fset_of_list tyVars \<rparr>) payload"
      unfolding tyenv_nonghost_payloads_runtime_def by blast
    thus "is_runtime_type (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env' |\<union>| fset_of_list tyVars,
              TE_RuntimeTypeVars := (TE_AbstractTypes ?env' |\<inter>| TE_RuntimeTypeVars ?env')
                                     |\<union>| fset_of_list tyVars \<rparr>) payload"
      using rt_scope_mono by (simp add: abs_eq)
  qed
  moreover have "tyenv_ghost_datatypes_subset ?env'"
    using ghost_dt_subset unfolding tyenv_ghost_datatypes_subset_def by simp
  moreover have "tyenv_runtime_tyvars_subset ?env'"
    using rt_subset assms(2) unfolding tyenv_runtime_tyvars_subset_def
    by simp blast
  moreover have "tyenv_abstract_types_subset ?env'"
    using abs_subset unfolding tyenv_abstract_types_subset_def
    by (simp add: abs_eq) blast
  moreover have "tyenv_datatypes_nonempty ?env'"
    using dt_nonempty unfolding tyenv_datatypes_nonempty_def by simp
  ultimately show ?thesis unfolding tyenv_well_formed_def by auto
qed

(* If a datatype's ctor list in TE_DataCtorsByType begins with ctorName, then
   TE_DataCtors records ctorName as belonging to this datatype, with some
   tyvars and payload. (Derived from tyenv_ctors_by_type_consistent; this is
   the form callers — notably default_value_sound — actually need.) *)
lemma tyenv_first_ctor_consistent:
  assumes wf: "tyenv_well_formed env"
      and lookup: "fmlookup (TE_DataCtorsByType env) dtName = Some (ctorName # ctors)"
  shows "\<exists>tyvars payload.
            fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payload)"
proof -
  from wf have cons: "tyenv_ctors_by_type_consistent env"
    unfolding tyenv_well_formed_def by simp
  have "ctorName \<in> set (ctorName # ctors)" by simp
  with cons lookup show ?thesis
    unfolding tyenv_ctors_by_type_consistent_def by blast
qed

end
