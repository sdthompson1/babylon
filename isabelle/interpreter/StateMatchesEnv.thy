theory StateMatchesEnv
  imports CoreInterp
begin

(* This predicate asserts that "name" is defined as a term variable (local, ref or
   constant) in the state, and its value has the given type (in the given environment) *)
definition term_var_in_state_with_type :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> string \<Rightarrow> CoreType \<Rightarrow> bool" where
  "term_var_in_state_with_type state env name ty =
    (case fmlookup (IS_Locals state) name of
      Some addr \<Rightarrow> addr < length (IS_Store state) \<and>
                   value_has_type env (IS_Store state ! addr) ty
    | None \<Rightarrow>
      (case fmlookup (IS_Refs state) name of
        Some (addr, path) \<Rightarrow> addr < length (IS_Store state) \<and>
                             (case get_value_at_path (IS_Store state ! addr) path of
                               Inr v \<Rightarrow> value_has_type env v ty
                             | Inl err \<Rightarrow> False)
      | None \<Rightarrow>
        (case fmlookup (IS_Constants state) name of
          Some val \<Rightarrow> value_has_type env val ty
        | None \<Rightarrow> False)))"

(* This says that a given FunInfo and an InterpFun match *)
(* TODO: This needs to be extended, as explained below *)
definition fun_info_matches_interp_fun :: "FunInfo \<Rightarrow> 'w InterpFun \<Rightarrow> bool" where
  "fun_info_matches_interp_fun funInfo interpFun =
    \<comment> \<open>Same number of arguments\<close>
    (length (FI_TmArgs funInfo) = length (IF_Args interpFun))
    \<comment> \<open>TODO: Var/Ref status of each argument matches\<close>
    \<comment> \<open>TODO: Impure flag matches\<close>
    \<comment> \<open>TODO: for Babylon functions: the IF_Body statement list must have
        an appropriate type (corresponding to the function's return type) in an
        appropriate environment (corresponding to the function's arguments)\<close>
    \<comment> \<open>TODO: for external functions, the ExternFunc, when called with appropriate
        CoreValues for the arguments, returns CoreValue(s) of the expected type and
        quantity\<close>"


(* This asserts that all variables in the type env (TE_TermVars, but not ghost)
   also exist in the state (either IS_Locals, IS_Refs or IS_Constants) 
   with the correct type. *)
definition vars_exist_in_state :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "vars_exist_in_state state env \<equiv>
    \<forall>name ty. fmlookup (TE_TermVars env) name = Some ty \<and> name |\<notin>| TE_GhostVars env \<longrightarrow>
      term_var_in_state_with_type state env name ty"

(* This asserts the converse: if a variable is not in TE_TermVars (or is in TE_GhostVars)
   then it is not in the state. *)
definition no_extra_vars :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "no_extra_vars state env \<equiv>
    \<forall>name. fmlookup (TE_TermVars env) name = None \<or> name |\<in>| TE_GhostVars env \<longrightarrow>
      fmlookup (IS_Locals state) name = None \<and>
      fmlookup (IS_Refs state) name = None \<and>
      fmlookup (IS_Constants state) name = None"

(* All NotGhost functions in the type environment also exist in the state
   with corresponding numbers of arguments and other properties *)
definition funs_exist_in_state :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "funs_exist_in_state state env \<equiv>
    \<forall>name info. fmlookup (TE_Functions env) name = Some info \<and> FI_Ghost info = NotGhost \<longrightarrow>
      (case fmlookup (IS_Functions state) name of
        Some interpFun \<Rightarrow> fun_info_matches_interp_fun info interpFun
      | None \<Rightarrow> False)"

(* There are no extra functions in the interp state *)
definition no_extra_funs :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "no_extra_funs state env \<equiv>
    \<forall>name. (case fmlookup (TE_Functions env) name of
              None \<Rightarrow> True
            | Some info \<Rightarrow> FI_Ghost info = Ghost) \<longrightarrow>
      fmlookup (IS_Functions state) name = None"

(* Overall definition: state matches environment *)
definition state_matches_env :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "state_matches_env state env \<equiv>
    vars_exist_in_state state env \<and>
    no_extra_vars state env \<and>
    funs_exist_in_state state env \<and>
    no_extra_funs state env"

end
