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

end
