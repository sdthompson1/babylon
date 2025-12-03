theory TypeEnvWellFormed
  imports BabKindcheck
begin

(* All term variable types are ground (no metavariables) *)
definition tyenv_vars_ground :: "BabTyEnv \<Rightarrow> bool" where
  "tyenv_vars_ground env \<equiv>
    \<forall>name ty. fmlookup (TE_TermVars env) name = Some ty \<longrightarrow> is_ground ty"

(* All non-ghost variables have runtime types *)
definition tyenv_vars_runtime :: "BabTyEnv \<Rightarrow> bool" where
  "tyenv_vars_runtime env \<equiv>
    \<forall>name ty. fmlookup (TE_TermVars env) name = Some ty
              \<and> name |\<notin>| TE_GhostVars env
              \<longrightarrow> is_runtime_type ty"

(* All term variable types are well-kinded *)
definition tyenv_vars_well_kinded :: "BabTyEnv \<Rightarrow> bool" where
  "tyenv_vars_well_kinded env \<equiv>
    \<forall>name ty. fmlookup (TE_TermVars env) name = Some ty \<longrightarrow> is_well_kinded env ty"

(* Data constructors are consistent with datatypes:
   for each ctor in TE_DataCtors mapping to (dtName, numTyArgs, payload),
   dtName must be in TE_Datatypes with matching type argument count,
   and dtName must not be a type variable *)
definition tyenv_ctors_consistent :: "BabTyEnv \<Rightarrow> bool" where
  "tyenv_ctors_consistent env \<equiv>
    \<forall>ctorName dtName numTyArgs payload.
      fmlookup (TE_DataCtors env) ctorName = Some (dtName, numTyArgs, payload) \<longrightarrow>
      (\<exists>dt. fmlookup (TE_Datatypes env) dtName = Some dt \<and>
            length (DD_TyArgs dt) = numTyArgs \<and>
            dtName |\<notin>| TE_TypeVars env)"

(* A type environment is well-formed if all the above conditions hold *)
definition tyenv_well_formed :: "BabTyEnv \<Rightarrow> bool" where
  "tyenv_well_formed env \<equiv>
    tyenv_vars_ground env \<and>
    tyenv_vars_runtime env \<and>
    tyenv_vars_well_kinded env \<and>
    tyenv_ctors_consistent env"

end
