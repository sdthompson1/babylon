theory StateMatchesEnv
  imports CoreInterp "../core/CoreStmtTypecheck"
begin

(* Build the type environment in which a function body should typecheck.
   Inherits TE_GlobalVars, TE_GhostGlobals, TE_Functions, TE_Datatypes, TE_DataCtors,
   TE_DataCtorsByType, TE_GhostDatatypes from the surrounding env. The locals,
   ghost-locals, const-names, type-vars, return type, and function-ghost flag are
   all replaced by ones derived from the FunInfo:
   - TE_LocalVars: formal parameter names mapped to their declared types
   - TE_GhostLocals: empty (ghost functions are not handled here; this helper is
     only used for non-ghost functions)
   - TE_ConstNames: the names of Var (by-value) parameters; Ref parameters are
     non-const because they may be assigned to via the reference
   - TE_TypeVars / TE_RuntimeTypeVars: the function's own type variables (both
     equal because we are only interested in non-ghost calls)
   - TE_ReturnType: the function's declared return type
   - TE_FunctionGhost: NotGhost *)
definition body_env_for :: "CoreTyEnv \<Rightarrow> FunInfo \<Rightarrow> CoreTyEnv" where
  "body_env_for env funInfo =
    env \<lparr>
      TE_LocalVars := fmap_of_list (map (\<lambda>(name, ty, _). (name, ty)) (FI_TmArgs funInfo)),
      TE_GhostLocals := {||},
      TE_ConstNames := fset_of_list
        (map (\<lambda>(name, _, _). name)
             (filter (\<lambda>(_, _, vor). vor = Var) (FI_TmArgs funInfo))),
      TE_TypeVars := fset_of_list (FI_TyArgs funInfo),
      TE_RuntimeTypeVars := fset_of_list (FI_TyArgs funInfo),
      TE_ReturnType := FI_ReturnType funInfo,
      TE_FunctionGhost := NotGhost
    \<rparr>"

(* Store typing: a list of types, one per store slot, giving each slot's designated
   type. Length-matched with IS_Store state. Pins down the type of each slot so that
   we avoid the type-uniqueness problem (e.g. an empty array value has many possible
   array types; the store typing says which one the slot was allocated with). *)

(* For a local variable, the slot's designated type must be exactly the variable's
   declared type (no drift to a different valid type).
   For a ref, the path through the slot type must arrive at the variable's declared type.
     - If the ref is "live" (get_value_at_path succeeds), the obtained value has type ty
       (by get_value_at_path_type with slotTy = storeTyping ! addr).
     - If the ref is "dangling" (get_value_at_path fails), the error is RuntimeError
       (by get_value_at_path_error_is_runtime). RuntimeError is a sound error result.
   This models Babylon's semantics where e.g. binding a ref into a variant ctor
   (match x { case Just(ref r) => ... }) and then reassigning x = Nothing leaves r
   dangling. In real Babylon programs, such accesses are prevented statically by
   SMT-discharged proof obligations; the Core language typechecker does not (and
   need not) enforce this. *)

(* A local variable (in IS_Locals or IS_Refs) has the expected type via the store typing *)
definition local_var_in_state_with_type :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> CoreType list
    \<Rightarrow> string \<Rightarrow> CoreType \<Rightarrow> bool" where
  "local_var_in_state_with_type state env storeTyping name ty =
    (case fmlookup (IS_Locals state) name of
      Some addr \<Rightarrow> addr < length (IS_Store state) \<and> storeTyping ! addr = ty
    | None \<Rightarrow>
      (case fmlookup (IS_Refs state) name of
        Some (addr, path) \<Rightarrow> addr < length (IS_Store state) \<and>
                             type_at_path env (storeTyping ! addr) path = Some ty
      | None \<Rightarrow> False))"

(* A global variable (in IS_Globals) has the expected type directly *)
definition global_var_in_state_with_type :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow>
    string \<Rightarrow> CoreType \<Rightarrow> bool" where
  "global_var_in_state_with_type state env name ty =
    (case fmlookup (IS_Globals state) name of
      Some val \<Rightarrow> value_has_type env val ty
    | None \<Rightarrow> False)"

(* Contract for an external function: when called with arguments of the expected
   types, it returns values of the expected types. Currently a stub: discharging
   this contract is the responsibility of whoever provides the ExternFunc, and
   the soundness proof for extern calls is deferred. *)
definition extern_fun_contract :: "CoreTyEnv \<Rightarrow> FunInfo \<Rightarrow> 'w ExternFunc \<Rightarrow> bool" where
  "extern_fun_contract env funInfo externFun = True"

(* This says that a given FunInfo and an InterpFun match, in a given type environment.
   The env is needed because the body-typechecks clause (for Babylon functions)
   references the surrounding env's globals, datatypes, and other functions.
   Hard-wires NotGhost: this predicate is only meaningful for non-ghost functions
   (see funs_exist_in_state), since the interpreter skips ghost calls. *)
definition fun_info_matches_interp_fun :: "CoreTyEnv \<Rightarrow> FunInfo \<Rightarrow> 'w InterpFun \<Rightarrow> bool" where
  "fun_info_matches_interp_fun env funInfo interpFun =
    \<comment> \<open>Same number of arguments\<close>
    (length (FI_TmArgs funInfo) = length (IF_Args interpFun) \<and>
    \<comment> \<open>Parameter name and Var/Ref status of each argument matches\<close>
    list_all2 (\<lambda>(name1, _, vor1) (name2, vor2). name1 = name2 \<and> vor1 = vor2)
              (FI_TmArgs funInfo) (IF_Args interpFun) \<and>
    \<comment> \<open>Impure flag matches\<close>
    FI_Impure funInfo = IF_Impure interpFun \<and>
    \<comment> \<open>Body certification: for Babylon functions, the body statement list
        typechecks in body_env_for env funInfo; for external functions, the
        extern contract holds.\<close>
    (case IF_Body interpFun of
       Inl bodyStmts \<Rightarrow>
         (\<exists>env'. core_statement_list_type (body_env_for env funInfo) NotGhost bodyStmts = Some env')
     | Inr externFun \<Rightarrow> extern_fun_contract env funInfo externFun))"


(* All local variables in the type env (TE_LocalVars, but not ghost)
   also exist in the state (either IS_Locals or IS_Refs) with the correct type. *)
definition local_vars_exist_in_state :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> CoreType list \<Rightarrow> bool" where
  "local_vars_exist_in_state state env storeTyping \<equiv>
    \<forall>name ty. fmlookup (TE_LocalVars env) name = Some ty \<and> name |\<notin>| TE_GhostLocals env \<longrightarrow>
      local_var_in_state_with_type state env storeTyping name ty"

(* All global variables in the type env (TE_GlobalVars, but not ghost)
   also exist in the state (IS_Globals) with the correct type. *)
definition global_vars_exist_in_state :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "global_vars_exist_in_state state env \<equiv>
    \<forall>name ty. fmlookup (TE_GlobalVars env) name = Some ty \<and> name |\<notin>| TE_GhostGlobals env \<longrightarrow>
      global_var_in_state_with_type state env name ty"

(* Converse for locals: if a variable is not in TE_LocalVars (or is ghost local)
   then it is not in IS_Locals or IS_Refs. *)
definition no_extra_local_vars :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "no_extra_local_vars state env \<equiv>
    \<forall>name. fmlookup (TE_LocalVars env) name = None \<or> name |\<in>| TE_GhostLocals env \<longrightarrow>
      fmlookup (IS_Locals state) name = None \<and>
      fmlookup (IS_Refs state) name = None"

(* Converse for globals: if a variable is not in TE_GlobalVars (or is ghost global)
   then it is not in IS_Globals. *)
definition no_extra_global_vars :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "no_extra_global_vars state env \<equiv>
    \<forall>name. fmlookup (TE_GlobalVars env) name = None \<or> name |\<in>| TE_GhostGlobals env \<longrightarrow>
      fmlookup (IS_Globals state) name = None"

(* All NotGhost functions in the type environment also exist in the state
   with corresponding numbers of arguments and other properties *)
definition funs_exist_in_state :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "funs_exist_in_state state env \<equiv>
    \<forall>name info. fmlookup (TE_Functions env) name = Some info \<and> FI_Ghost info = NotGhost \<longrightarrow>
      (case fmlookup (IS_Functions state) name of
        Some interpFun \<Rightarrow> fun_info_matches_interp_fun env info interpFun
      | None \<Rightarrow> False)"

(* There are no extra functions in the interp state *)
definition no_extra_funs :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "no_extra_funs state env \<equiv>
    \<forall>name. (case fmlookup (TE_Functions env) name of
              None \<Rightarrow> True
            | Some info \<Rightarrow> FI_Ghost info = Ghost) \<longrightarrow>
      fmlookup (IS_Functions state) name = None"

(* Non-constant, non-ghost local variables are in IS_Locals or IS_Refs.
   (Globals are implicitly constant and are always in IS_Globals, not here.) *)
definition non_consts_in_locals_or_refs :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "non_consts_in_locals_or_refs state env \<equiv>
    \<forall>name. fmlookup (TE_LocalVars env) name \<noteq> None \<and>
           name |\<notin>| TE_GhostLocals env \<and> name |\<notin>| TE_ConstNames env \<longrightarrow>
      (fmlookup (IS_Locals state) name \<noteq> None \<or> fmlookup (IS_Refs state) name \<noteq> None)"

(* The interpreter's IS_ConstNames matches the type environment's TE_ConstNames *)
definition const_names_match :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "const_names_match state env \<equiv>
    IS_ConstNames state = TE_ConstNames env"

(* The store typing has the same length as the store, and every slot value has the
   designated type for its address. *)
definition store_well_typed :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> CoreType list \<Rightarrow> bool" where
  "store_well_typed state env storeTyping \<equiv>
    length storeTyping = length (IS_Store state) \<and>
    (\<forall>addr. addr < length (IS_Store state) \<longrightarrow>
        value_has_type env (IS_Store state ! addr) (storeTyping ! addr))"

(* Overall definition: state matches environment under a given store typing *)
definition state_matches_env :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> CoreType list \<Rightarrow> bool" where
  "state_matches_env state env storeTyping \<equiv>
    local_vars_exist_in_state state env storeTyping \<and>
    global_vars_exist_in_state state env \<and>
    no_extra_local_vars state env \<and>
    no_extra_global_vars state env \<and>
    funs_exist_in_state state env \<and>
    no_extra_funs state env \<and>
    non_consts_in_locals_or_refs state env \<and>
    const_names_match state env \<and>
    store_well_typed state env storeTyping"

(* body_env_for only depends on the "global" fields of env (TE_GlobalVars,
   TE_GhostGlobals, TE_Functions, TE_Datatypes, TE_DataCtors, TE_DataCtorsByType,
   TE_GhostDatatypes); the "local" fields it sets are all overwritten from
   funInfo. So if two envs agree on the global fields, body_env_for produces
   the same env. *)
lemma body_env_for_cong:
  assumes "TE_GlobalVars env1 = TE_GlobalVars env2"
      and "TE_GhostGlobals env1 = TE_GhostGlobals env2"
      and "TE_Functions env1 = TE_Functions env2"
      and "TE_Datatypes env1 = TE_Datatypes env2"
      and "TE_DataCtors env1 = TE_DataCtors env2"
      and "TE_DataCtorsByType env1 = TE_DataCtorsByType env2"
      and "TE_GhostDatatypes env1 = TE_GhostDatatypes env2"
  shows "body_env_for env1 funInfo = body_env_for env2 funInfo"
  using assms unfolding body_env_for_def by simp

(* fun_info_matches_interp_fun congruence: same global fields imply same result. *)
lemma fun_info_matches_interp_fun_cong_env:
  assumes "TE_GlobalVars env1 = TE_GlobalVars env2"
      and "TE_GhostGlobals env1 = TE_GhostGlobals env2"
      and "TE_Functions env1 = TE_Functions env2"
      and "TE_Datatypes env1 = TE_Datatypes env2"
      and "TE_DataCtors env1 = TE_DataCtors env2"
      and "TE_DataCtorsByType env1 = TE_DataCtorsByType env2"
      and "TE_GhostDatatypes env1 = TE_GhostDatatypes env2"
  shows "fun_info_matches_interp_fun env1 funInfo interpFun =
         fun_info_matches_interp_fun env2 funInfo interpFun"
  unfolding fun_info_matches_interp_fun_def
  using body_env_for_cong[OF assms, of funInfo]
  by (simp add: extern_fun_contract_def split: sum.splits)

end
