theory CoreTyEnvWellFormed
  imports CoreKindcheck
begin

(* All term variables' types are well-kinded *)
definition tyenv_vars_well_kinded :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_vars_well_kinded env =
    (\<forall>name ty. fmlookup (TE_TermVars env) name = Some ty \<longrightarrow> is_well_kinded env ty)"

(* All term variables' types are ground (no metavariables) *)
definition tyenv_vars_ground :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_vars_ground env =
    (\<forall>name ty. fmlookup (TE_TermVars env) name = Some ty \<longrightarrow> is_ground ty)"

(* All nonghost term variables' types are runtime types *)
definition tyenv_vars_runtime :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_vars_runtime env =
    (\<forall>name ty. fmlookup (TE_TermVars env) name = Some ty
               \<and> name |\<notin>| TE_GhostVars env
               \<longrightarrow> is_runtime_type ty)"

(* Type variable names and datatype names are disjoint *)
definition tyenv_tyvars_datatypes_disjoint :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_tyvars_datatypes_disjoint env =
    (TE_TypeVars env |\<inter>| fmdom (TE_Datatypes env) = {||})"

(* Data constructors are consistent with datatypes:
   For each ctor in TE_DataCtors mapping to (dtName, tyArgMetavars, payload),
   dtName must be in TE_Datatypes with matching numTyArgs *)
definition tyenv_ctors_consistent :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_ctors_consistent env =
    (\<forall>ctorName dtName tyArgMetavars payload.
      fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyArgMetavars, payload) \<longrightarrow>
      fmlookup (TE_Datatypes env) dtName = Some (length tyArgMetavars))"

(* Data constructor payload types are well-kinded *)
definition tyenv_payloads_well_kinded :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_payloads_well_kinded env =
    (\<forall>ctorName dtName tyArgMetavars payload.
      fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyArgMetavars, payload) \<longrightarrow>
      is_well_kinded env payload)"

(* Metavars in data constructor payload types are a subset of the stated metavars *)
(* (This means that after substituting in the actual type arguments, the payload will
   have a ground type) *)
definition tyenv_payloads_have_expected_metavars :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_payloads_have_expected_metavars env =
    (\<forall>ctorName dtName tyArgMetavars payload.
      fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyArgMetavars, payload) \<longrightarrow>
      type_metavars payload \<subseteq> set tyArgMetavars)"

(* Data constructor type arguments (metavars) are distinct *)
definition tyenv_ctor_metavars_distinct :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_ctor_metavars_distinct env =
    (\<forall>ctorName dtName tyArgMetavars payload.
      fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyArgMetavars, payload) \<longrightarrow>
      distinct tyArgMetavars)"

(* TE_DataCtorsByType is consistent with TE_DataCtors:
   A constructor is in TE_DataCtorsByType[dtName] iff it maps to dtName in TE_DataCtors *)
definition tyenv_ctors_by_type_consistent :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_ctors_by_type_consistent env =
    (\<forall>dtName ctors. fmlookup (TE_DataCtorsByType env) dtName = Some ctors \<longrightarrow>
      (\<forall>ctorName. ctorName \<in> set ctors \<longleftrightarrow>
        (\<exists>tyArgMetavars payload.
          fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyArgMetavars, payload))))"

(* Function arg and return types are well-kinded *)
definition tyenv_fun_types_well_kinded :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_fun_types_well_kinded env =
    (\<forall>funName info. fmlookup (TE_Functions env) funName = Some info \<longrightarrow>
      (\<forall>ty \<in> set (FI_TmArgs info). is_well_kinded env ty) \<and>
      is_well_kinded env (FI_ReturnType info))"

(* Function arg and return types have the expected metavars *)
definition tyenv_funs_have_expected_metavars :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_funs_have_expected_metavars env =
    (\<forall>funName info. fmlookup (TE_Functions env) funName = Some info \<longrightarrow>
      (\<forall>ty \<in> set (FI_TmArgs info). type_metavars ty \<subseteq> set (FI_TyArgs info)) \<and>
      type_metavars (FI_ReturnType info) \<subseteq> set (FI_TyArgs info))"

(* Function type arguments (metavars) are distinct *)
definition tyenv_fun_metavars_distinct :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_fun_metavars_distinct env =
    (\<forall>funName info. fmlookup (TE_Functions env) funName = Some info \<longrightarrow>
      distinct (FI_TyArgs info))"

(* For non-ghost functions, types must be runtime types *)
definition tyenv_fun_ghost_constraint :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_fun_ghost_constraint env =
    (\<forall>funName info. fmlookup (TE_Functions env) funName = Some info \<and>
    (FI_Ghost info) = NotGhost \<longrightarrow>
      (\<forall>ty \<in> set (FI_TmArgs info). is_runtime_type ty) \<and>
      is_runtime_type (FI_ReturnType info))"

(* A type environment is well-formed if all the above conditions hold *)
definition tyenv_well_formed :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_well_formed env =
    (tyenv_vars_well_kinded env \<and>
     tyenv_vars_ground env \<and>
     tyenv_vars_runtime env \<and>
     tyenv_tyvars_datatypes_disjoint env \<and>
     tyenv_ctors_consistent env \<and>
     tyenv_payloads_well_kinded env \<and>
     tyenv_payloads_have_expected_metavars env \<and>
     tyenv_ctor_metavars_distinct env \<and>
     tyenv_ctors_by_type_consistent env \<and>
     tyenv_fun_types_well_kinded env \<and>
     tyenv_funs_have_expected_metavars env \<and>
     tyenv_fun_metavars_distinct env \<and>
     tyenv_fun_ghost_constraint env)"

(* Adding a well-kinded, ground, runtime variable preserves tyenv_well_formed.
   This is the NotGhost case; the variable is removed from TE_GhostVars. *)
lemma tyenv_well_formed_add_var:
  assumes wf: "tyenv_well_formed env"
    and ty_wk: "is_well_kinded env ty"
    and ty_ground: "is_ground ty"
    and ty_runtime: "is_runtime_type ty"
  shows "tyenv_well_formed (env \<lparr> TE_TermVars := fmupd var ty (TE_TermVars env),
                                 TE_GhostVars := fminus (TE_GhostVars env) {|var|} \<rparr>)"
proof -
  let ?env' = "env \<lparr> TE_TermVars := fmupd var ty (TE_TermVars env),
                     TE_GhostVars := fminus (TE_GhostVars env) {|var|} \<rparr>"
  from wf have wk: "tyenv_vars_well_kinded env"
    and gr: "tyenv_vars_ground env"
    and rt: "tyenv_vars_runtime env"
    and rest: "tyenv_tyvars_datatypes_disjoint env"
              "tyenv_ctors_consistent env"
              "tyenv_payloads_well_kinded env"
              "tyenv_payloads_have_expected_metavars env"
              "tyenv_ctor_metavars_distinct env"
              "tyenv_ctors_by_type_consistent env"
              "tyenv_fun_types_well_kinded env"
              "tyenv_funs_have_expected_metavars env"
              "tyenv_fun_metavars_distinct env"
              "tyenv_fun_ghost_constraint env"
    unfolding tyenv_well_formed_def by auto

  \<comment> \<open>is_well_kinded only depends on TE_Datatypes and TE_TypeVars, not TE_TermVars\<close>
  have env'_fields: "TE_TypeVars ?env' = TE_TypeVars env"
                     "TE_Datatypes ?env' = TE_Datatypes env"
    by simp_all
  have wk_preserved: "\<And>ty'. is_well_kinded env ty' = is_well_kinded ?env' ty'"
    using is_well_kinded_cong_env[OF env'_fields] by simp

  have "tyenv_vars_well_kinded ?env'"
    using wk ty_wk unfolding tyenv_vars_well_kinded_def
    by (auto simp: wk_preserved split: if_splits)
  moreover have "tyenv_vars_ground ?env'"
    using gr ty_ground unfolding tyenv_vars_ground_def
    by (auto split: if_splits)
  moreover have "tyenv_vars_runtime ?env'"
    using rt ty_runtime unfolding tyenv_vars_runtime_def
    by (auto split: if_splits)
  moreover have "tyenv_tyvars_datatypes_disjoint ?env'" using rest(1)
    unfolding tyenv_tyvars_datatypes_disjoint_def by simp
  moreover have "tyenv_ctors_consistent ?env'" using rest(2)
    unfolding tyenv_ctors_consistent_def by simp
  moreover have "tyenv_payloads_well_kinded ?env'" using rest(3)
    unfolding tyenv_payloads_well_kinded_def by (simp add: wk_preserved)
  moreover have "tyenv_payloads_have_expected_metavars ?env'" using rest(4)
    unfolding tyenv_payloads_have_expected_metavars_def by simp
  moreover have "tyenv_ctor_metavars_distinct ?env'" using rest(5)
    unfolding tyenv_ctor_metavars_distinct_def by simp
  moreover have "tyenv_ctors_by_type_consistent ?env'" using rest(6)
    unfolding tyenv_ctors_by_type_consistent_def by simp
  moreover have "tyenv_fun_types_well_kinded ?env'" using rest(7)
    unfolding tyenv_fun_types_well_kinded_def by (simp add: wk_preserved)
  moreover have "tyenv_funs_have_expected_metavars ?env'" using rest(8)
    unfolding tyenv_funs_have_expected_metavars_def by simp
  moreover have "tyenv_fun_metavars_distinct ?env'" using rest(9)
    unfolding tyenv_fun_metavars_distinct_def by simp
  moreover have "tyenv_fun_ghost_constraint ?env'" using rest(10)
    unfolding tyenv_fun_ghost_constraint_def by auto
  ultimately show ?thesis unfolding tyenv_well_formed_def by auto
qed

(* Adding a well-kinded, ground ghost variable preserves tyenv_well_formed.
   Ghost variables do not need to be runtime types. *)
lemma tyenv_well_formed_add_ghost_var:
  assumes wf: "tyenv_well_formed env"
    and ty_wk: "is_well_kinded env ty"
    and ty_ground: "is_ground ty"
  shows "tyenv_well_formed (env \<lparr> TE_TermVars := fmupd var ty (TE_TermVars env),
                                 TE_GhostVars := finsert var (TE_GhostVars env) \<rparr>)"
proof -
  let ?env' = "env \<lparr> TE_TermVars := fmupd var ty (TE_TermVars env),
                     TE_GhostVars := finsert var (TE_GhostVars env) \<rparr>"
  from wf have wk: "tyenv_vars_well_kinded env"
    and gr: "tyenv_vars_ground env"
    and rt: "tyenv_vars_runtime env"
    and rest: "tyenv_tyvars_datatypes_disjoint env"
              "tyenv_ctors_consistent env"
              "tyenv_payloads_well_kinded env"
              "tyenv_payloads_have_expected_metavars env"
              "tyenv_ctor_metavars_distinct env"
              "tyenv_ctors_by_type_consistent env"
              "tyenv_fun_types_well_kinded env"
              "tyenv_funs_have_expected_metavars env"
              "tyenv_fun_metavars_distinct env"
              "tyenv_fun_ghost_constraint env"
    unfolding tyenv_well_formed_def by auto

  have env'_fields: "TE_TypeVars ?env' = TE_TypeVars env"
                     "TE_Datatypes ?env' = TE_Datatypes env"
    by simp_all
  have wk_preserved: "\<And>ty'. is_well_kinded env ty' = is_well_kinded ?env' ty'"
    using is_well_kinded_cong_env[OF env'_fields] by simp

  have "tyenv_vars_well_kinded ?env'"
    using wk ty_wk unfolding tyenv_vars_well_kinded_def
    by (auto simp: wk_preserved split: if_splits)
  moreover have "tyenv_vars_ground ?env'"
    using gr ty_ground unfolding tyenv_vars_ground_def
    by (auto split: if_splits)
  moreover have "tyenv_vars_runtime ?env'"
    using rt unfolding tyenv_vars_runtime_def
    by (auto split: if_splits)
  moreover have "tyenv_tyvars_datatypes_disjoint ?env'" using rest(1)
    unfolding tyenv_tyvars_datatypes_disjoint_def by simp
  moreover have "tyenv_ctors_consistent ?env'" using rest(2)
    unfolding tyenv_ctors_consistent_def by simp
  moreover have "tyenv_payloads_well_kinded ?env'" using rest(3)
    unfolding tyenv_payloads_well_kinded_def by (simp add: wk_preserved)
  moreover have "tyenv_payloads_have_expected_metavars ?env'" using rest(4)
    unfolding tyenv_payloads_have_expected_metavars_def by simp
  moreover have "tyenv_ctor_metavars_distinct ?env'" using rest(5)
    unfolding tyenv_ctor_metavars_distinct_def by simp
  moreover have "tyenv_ctors_by_type_consistent ?env'" using rest(6)
    unfolding tyenv_ctors_by_type_consistent_def by simp
  moreover have "tyenv_fun_types_well_kinded ?env'" using rest(7)
    unfolding tyenv_fun_types_well_kinded_def by (simp add: wk_preserved)
  moreover have "tyenv_funs_have_expected_metavars ?env'" using rest(8)
    unfolding tyenv_funs_have_expected_metavars_def by simp
  moreover have "tyenv_fun_metavars_distinct ?env'" using rest(9)
    unfolding tyenv_fun_metavars_distinct_def by simp
  moreover have "tyenv_fun_ghost_constraint ?env'" using rest(10)
    unfolding tyenv_fun_ghost_constraint_def by auto
  ultimately show ?thesis unfolding tyenv_well_formed_def by auto
qed

end
