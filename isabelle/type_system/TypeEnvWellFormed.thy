theory TypeEnvWellFormed
  imports BabKindcheck
begin

(* All term variable types are well-kinded *)
definition tyenv_vars_well_kinded :: "BabTyEnv \<Rightarrow> bool" where
  "tyenv_vars_well_kinded env \<equiv>
    \<forall>name ty. fmlookup (TE_TermVars env) name = Some ty \<longrightarrow> is_well_kinded env ty"

(* All term variable types are ground (no metavariables) *)
definition tyenv_vars_ground :: "BabTyEnv \<Rightarrow> bool" where
  "tyenv_vars_ground env \<equiv>
    \<forall>name ty. fmlookup (TE_TermVars env) name = Some ty \<longrightarrow> is_ground ty"

(* All non-ghost term variable types are runtime types *)
definition tyenv_vars_runtime :: "BabTyEnv \<Rightarrow> bool" where
  "tyenv_vars_runtime env \<equiv>
    \<forall>name ty. fmlookup (TE_TermVars env) name = Some ty
              \<and> name |\<notin>| TE_GhostVars env
              \<longrightarrow> is_runtime_type ty"

(* Data constructors are consistent with datatypes:
   for each ctor in TE_DataCtors mapping to (dtName, numTyArgs, payload),
   dtName must be in TE_Datatypes with a type variable list of matching length,
   and dtName must not be a type variable *)
definition tyenv_ctors_consistent :: "BabTyEnv \<Rightarrow> bool" where
  "tyenv_ctors_consistent env \<equiv>
    \<forall>ctorName dtName numTyArgs payload.
      fmlookup (TE_DataCtors env) ctorName = Some (dtName, numTyArgs, payload) \<longrightarrow>
      (\<exists>tyVars. fmlookup (TE_Datatypes env) dtName = Some tyVars \<and>
                length tyVars = numTyArgs \<and>
                dtName |\<notin>| TE_TypeVars env)"

(* All data constructor payload types are well-kinded *)
definition tyenv_payloads_well_kinded :: "BabTyEnv \<Rightarrow> bool" where
  "tyenv_payloads_well_kinded env \<equiv>
    \<forall>ctorName dtName numTyArgs payloadTy.
      fmlookup (TE_DataCtors env) ctorName = Some (dtName, numTyArgs, Some payloadTy) \<longrightarrow>
      is_well_kinded env payloadTy"

(* All datatype type variable lists are distinct *)
definition tyenv_datatypes_distinct :: "BabTyEnv \<Rightarrow> bool" where
  "tyenv_datatypes_distinct env \<equiv>
    \<forall>dtName tyVars.
      fmlookup (TE_Datatypes env) dtName = Some tyVars \<longrightarrow>
      distinct tyVars"

(* Helper: environment extended with type variables from a function declaration *)
definition env_with_tyvars :: "BabTyEnv \<Rightarrow> string list \<Rightarrow> BabTyEnv" where
  "env_with_tyvars env tyVars \<equiv>
    env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list tyVars \<rparr>"

(* Function declarations are well-formed:
   - Function type variables don't shadow datatype names
   - All argument types are ground and well-kinded (in env extended with function's type variables)
   - Return type (if present) is ground and well-kinded (in env extended with function's type variables)
   - For non-ghost functions, argument types and return type must be runtime types *)
definition tyenv_functions_well_formed :: "BabTyEnv \<Rightarrow> bool" where
  "tyenv_functions_well_formed env \<equiv>
    \<forall>fnName funDecl.
      fmlookup (TE_Functions env) fnName = Some funDecl \<longrightarrow>
      (let extEnv = env_with_tyvars env (DF_TyArgs funDecl) in
        \<comment> \<open>Function type variables don't shadow datatype names\<close>
        fset_of_list (DF_TyArgs funDecl) |\<inter>| fmdom (TE_Datatypes env) = {||} \<and>
        \<comment> \<open>All argument types are ground and well-kinded\<close>
        list_all (\<lambda>(_, _, ty). is_ground ty \<and> is_well_kinded extEnv ty) (DF_TmArgs funDecl) \<and>
        \<comment> \<open>Return type (if present) is ground and well-kinded\<close>
        (case DF_ReturnType funDecl of
          None \<Rightarrow> True
        | Some retTy \<Rightarrow> is_ground retTy \<and> is_well_kinded extEnv retTy) \<and>
        \<comment> \<open>For non-ghost functions, types must be runtime types\<close>
        (DF_Ghost funDecl = NotGhost \<longrightarrow>
          list_all (\<lambda>(_, _, ty). is_runtime_type ty) (DF_TmArgs funDecl) \<and>
          (case DF_ReturnType funDecl of
            None \<Rightarrow> True
          | Some retTy \<Rightarrow> is_runtime_type retTy)))"

(* A type environment is well-formed if all the above conditions hold *)
definition tyenv_well_formed :: "BabTyEnv \<Rightarrow> bool" where
  "tyenv_well_formed env \<equiv>
    tyenv_vars_ground env \<and>
    tyenv_vars_runtime env \<and>
    tyenv_vars_well_kinded env \<and>
    tyenv_ctors_consistent env \<and>
    tyenv_payloads_well_kinded env \<and>
    tyenv_datatypes_distinct env \<and>
    tyenv_functions_well_formed env"

end
