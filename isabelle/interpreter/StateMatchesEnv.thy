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
   - TE_ConstLocals: the names of Var (by-value) parameters; Ref parameters are
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
      TE_ConstLocals := fset_of_list
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
           name |\<notin>| TE_GhostLocals env \<and> name |\<notin>| TE_ConstLocals env \<longrightarrow>
      (fmlookup (IS_Locals state) name \<noteq> None \<or> fmlookup (IS_Refs state) name \<noteq> None)"

(* The interpreter's IS_ConstLocals matches the type environment's TE_ConstLocals,
   minus ghost names (which don't exist at runtime). *)
definition const_locals_match :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "const_locals_match state env \<equiv>
    IS_ConstLocals state = fminus (TE_ConstLocals env) (TE_GhostLocals env)"

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
    const_locals_match state env \<and>
    store_well_typed state env storeTyping"

(* body_env_for preserves tyenv_well_formed, given that funInfo is one of env's
   non-ghost functions. The interesting parts are:
   - Locals get FI_TmArgs types, which are well-kinded and runtime in env-with-
     FI_TyArgs-as-TE_TypeVars (from tyenv_fun_types_well_kinded /
     tyenv_fun_ghost_constraint). Since body_env_for uses exactly that override,
     they remain well-kinded and runtime in body_env_for env funInfo.
   - The return type's well-kindedness comes from the same source.
   - All other conjuncts depend only on fields inherited from env or use inner
     overrides that agree across both envs. *)
lemma body_env_for_well_formed:
  assumes wf: "tyenv_well_formed env"
      and fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo"
      and not_ghost: "FI_Ghost funInfo = NotGhost"
  shows "tyenv_well_formed (body_env_for env funInfo)"
proof -
  let ?be = "body_env_for env funInfo"
  let ?inner = "env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>"
  let ?inner_rt = "env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo),
                          TE_RuntimeTypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>"

  \<comment> \<open>Field congruence facts: ?be agrees with env on TE_Datatypes etc., and with
      ?inner / ?inner_rt on the relevant fields for is_well_kinded / is_runtime_type. \<close>
  have wk_inner_eq: "\<And>ty. is_well_kinded ?be ty = is_well_kinded ?inner ty"
    by (rule is_well_kinded_cong_env) (simp_all add: body_env_for_def)
  have rt_inner_eq: "\<And>ty. is_runtime_type ?be ty = is_runtime_type ?inner_rt ty"
    by (rule is_runtime_type_cong_env) (simp_all add: body_env_for_def)
  have wk_cleared_eq:
    "\<And>ty. is_well_kinded (?be \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty
        = is_well_kinded (env \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
    by (rule is_well_kinded_cong_env) (simp_all add: body_env_for_def)
  have rt_cleared_eq:
    "\<And>ty. is_runtime_type (?be \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty
        = is_runtime_type (env \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
    by (rule is_runtime_type_cong_env) (simp_all add: body_env_for_def)

  \<comment> \<open>Inner-override congruences for the various nested-env conjuncts. These all
      override TE_TypeVars (and possibly TE_RuntimeTypeVars), so the outer
      differences between env and ?be are dropped. \<close>
  have wk_scope_eq:
    "\<And>tvs t. is_well_kinded (?be \<lparr> TE_TypeVars := tvs \<rparr>) t
            = is_well_kinded (env \<lparr> TE_TypeVars := tvs \<rparr>) t"
    by (rule is_well_kinded_cong_env) (simp_all add: body_env_for_def)
  have rt_scope_eq:
    "\<And>tvs rtvs t. is_runtime_type (?be \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t
                = is_runtime_type (env \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t"
    by (rule is_runtime_type_cong_env) (simp_all add: body_env_for_def)

  \<comment> \<open>Extract relevant well-formedness facts from env. \<close>
  from wf have
    vars_wk: "tyenv_vars_well_kinded env" and
    vars_rt: "tyenv_vars_runtime env" and
    ghost_subset: "tyenv_ghost_vars_subset env" and
    ctors_cons: "tyenv_ctors_consistent env" and
    payloads_wk: "tyenv_payloads_well_kinded env" and
    ctor_tyvars_distinct: "tyenv_ctor_tyvars_distinct env" and
    ctors_by_type: "tyenv_ctors_by_type_consistent env" and
    fun_types_wk: "tyenv_fun_types_well_kinded env" and
    fun_tyvars_distinct: "tyenv_fun_tyvars_distinct env" and
    fun_param_names_distinct: "tyenv_fun_param_names_distinct env" and
    fun_ghost: "tyenv_fun_ghost_constraint env" and
    nonghost_payloads: "tyenv_nonghost_payloads_runtime env" and
    ghost_dt_subset: "tyenv_ghost_datatypes_subset env" and
    rt_subset: "tyenv_runtime_tyvars_subset env"
    unfolding tyenv_well_formed_def by auto

  \<comment> \<open>FI_TmArgs types are well-kinded in ?inner. \<close>
  from fun_types_wk fn_lookup have args_wk_inner:
    "\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo). is_well_kinded ?inner ty"
    unfolding tyenv_fun_types_well_kinded_def by auto
  \<comment> \<open>FI_ReturnType is well-kinded in ?inner. \<close>
  from fun_types_wk fn_lookup have ret_wk_inner:
    "is_well_kinded ?inner (FI_ReturnType funInfo)"
    unfolding tyenv_fun_types_well_kinded_def by auto
  \<comment> \<open>FI_TmArgs types are runtime in ?inner_rt (using non-ghost). \<close>
  from fun_ghost fn_lookup not_ghost have args_rt_inner:
    "\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo). is_runtime_type ?inner_rt ty"
    unfolding tyenv_fun_ghost_constraint_def Let_def by auto

  \<comment> \<open>(1) tyenv_vars_well_kinded ?be \<close>
  have c1: "tyenv_vars_well_kinded ?be"
    unfolding tyenv_vars_well_kinded_def
  proof (intro conjI allI impI)
    fix name ty
    assume "fmlookup (TE_LocalVars ?be) name = Some ty"
    hence "(name, ty) \<in> set (map (\<lambda>(n, t, _). (n, t)) (FI_TmArgs funInfo))"
      by (auto simp: body_env_for_def fmlookup_of_list weak_map_of_SomeI dest: map_of_SomeD)
    then obtain b where in_args: "(name, ty, b) \<in> set (FI_TmArgs funInfo)" by auto
    have "is_well_kinded ?inner ty"
      using args_wk_inner in_args by force
    thus "is_well_kinded ?be ty" using wk_inner_eq by simp
  next
    fix name ty
    assume gv: "fmlookup (TE_GlobalVars ?be) name = Some ty"
    hence "fmlookup (TE_GlobalVars env) name = Some ty"
      by (simp add: body_env_for_def)
    with vars_wk have "is_well_kinded (env \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
      unfolding tyenv_vars_well_kinded_def by blast
    thus "is_well_kinded (?be \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
      using wk_cleared_eq by simp
  qed

  \<comment> \<open>(2) tyenv_vars_runtime ?be (TE_GhostLocals is empty in ?be) \<close>
  have c2: "tyenv_vars_runtime ?be"
    unfolding tyenv_vars_runtime_def
  proof (intro conjI allI impI)
    fix name ty
    assume "fmlookup (TE_LocalVars ?be) name = Some ty
            \<and> name |\<notin>| TE_GhostLocals ?be"
    hence lv: "fmlookup (TE_LocalVars ?be) name = Some ty" by simp
    from lv have "(name, ty) \<in> set (map (\<lambda>(n, t, _). (n, t)) (FI_TmArgs funInfo))"
      by (auto simp: body_env_for_def fmlookup_of_list weak_map_of_SomeI dest: map_of_SomeD)
    then obtain b where in_args: "(name, ty, b) \<in> set (FI_TmArgs funInfo)" by auto
    have "is_runtime_type ?inner_rt ty"
      using args_rt_inner in_args by force
    thus "is_runtime_type ?be ty" using rt_inner_eq by simp
  next
    fix name ty
    assume A: "fmlookup (TE_GlobalVars ?be) name = Some ty
               \<and> name |\<notin>| TE_GhostGlobals ?be"
    from A have gv: "fmlookup (TE_GlobalVars ?be) name = Some ty"
      and ng: "name |\<notin>| TE_GhostGlobals ?be" by simp_all
    from gv have lk: "fmlookup (TE_GlobalVars env) name = Some ty"
      by (simp add: body_env_for_def)
    from ng have "name |\<notin>| TE_GhostGlobals env"
      by (simp add: body_env_for_def)
    with lk have "is_runtime_type (env \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
      using vars_rt unfolding tyenv_vars_runtime_def by blast
    thus "is_runtime_type (?be \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
      using rt_cleared_eq by simp
  qed

  \<comment> \<open>(3) tyenv_ghost_vars_subset ?be: TE_GhostLocals = {||} is empty subset; globals
       inherited. \<close>
  have c3: "tyenv_ghost_vars_subset ?be"
    using ghost_subset unfolding tyenv_ghost_vars_subset_def
    by (simp add: body_env_for_def)

  \<comment> \<open>(4) tyenv_return_type_well_kinded ?be: TE_ReturnType ?be = FI_ReturnType. \<close>
  have c4: "tyenv_return_type_well_kinded ?be"
    unfolding tyenv_return_type_well_kinded_def
    using ret_wk_inner wk_inner_eq by (simp add: body_env_for_def)

  \<comment> \<open>(5) tyenv_ctors_consistent ?be: TE_DataCtors and TE_Datatypes inherited. \<close>
  have c5: "tyenv_ctors_consistent ?be"
    using ctors_cons unfolding tyenv_ctors_consistent_def
    by (simp add: body_env_for_def)

  \<comment> \<open>(6) tyenv_payloads_well_kinded ?be: inner override on TE_TypeVars, TE_Datatypes inherited. \<close>
  have c6: "tyenv_payloads_well_kinded ?be"
    unfolding tyenv_payloads_well_kinded_def
  proof (intro allI impI)
    fix ctorName dtName tyVars payload
    assume "fmlookup (TE_DataCtors ?be) ctorName = Some (dtName, tyVars, payload)"
    hence ctor_lk: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload)"
      by (simp add: body_env_for_def)
    with payloads_wk
    have "is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list tyVars \<rparr>) payload"
      unfolding tyenv_payloads_well_kinded_def by blast
    thus "is_well_kinded (?be \<lparr> TE_TypeVars := fset_of_list tyVars \<rparr>) payload"
      using wk_scope_eq by simp
  qed

  \<comment> \<open>(7) tyenv_ctor_tyvars_distinct ?be: TE_DataCtors inherited. \<close>
  have c7: "tyenv_ctor_tyvars_distinct ?be"
    using ctor_tyvars_distinct unfolding tyenv_ctor_tyvars_distinct_def
    by (simp add: body_env_for_def)

  \<comment> \<open>(8) tyenv_ctors_by_type_consistent ?be: TE_DataCtorsByType, TE_DataCtors inherited. \<close>
  have c8: "tyenv_ctors_by_type_consistent ?be"
    using ctors_by_type unfolding tyenv_ctors_by_type_consistent_def
    by (simp add: body_env_for_def)

  \<comment> \<open>(9) tyenv_fun_types_well_kinded ?be: inner override, TE_Functions, TE_Datatypes inherited. \<close>
  have c9: "tyenv_fun_types_well_kinded ?be"
    unfolding tyenv_fun_types_well_kinded_def
  proof (intro allI impI)
    fix funName info
    assume "fmlookup (TE_Functions ?be) funName = Some info"
    hence info_lk: "fmlookup (TE_Functions env) funName = Some info"
      by (simp add: body_env_for_def)
    with fun_types_wk have
      args_wk: "\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs info).
                  is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info) \<rparr>) ty"
      and ret_wk: "is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info) \<rparr>)
                                  (FI_ReturnType info)"
      unfolding tyenv_fun_types_well_kinded_def by auto
    show "(\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs info).
              is_well_kinded (?be \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info) \<rparr>) ty) \<and>
          is_well_kinded (?be \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info) \<rparr>) (FI_ReturnType info)"
      using args_wk ret_wk wk_scope_eq by simp
  qed

  \<comment> \<open>(10) tyenv_fun_tyvars_distinct ?be: TE_Functions inherited. \<close>
  have c10: "tyenv_fun_tyvars_distinct ?be"
    using fun_tyvars_distinct unfolding tyenv_fun_tyvars_distinct_def
    by (simp add: body_env_for_def)

  \<comment> \<open>(11) tyenv_fun_param_names_distinct ?be: TE_Functions inherited. \<close>
  have c11: "tyenv_fun_param_names_distinct ?be"
    using fun_param_names_distinct unfolding tyenv_fun_param_names_distinct_def
    by (simp add: body_env_for_def)

  \<comment> \<open>(12) tyenv_fun_ghost_constraint ?be: inner override, TE_Functions inherited. \<close>
  have c12: "tyenv_fun_ghost_constraint ?be"
    unfolding tyenv_fun_ghost_constraint_def Let_def
  proof (intro allI impI, elim conjE)
    fix funName info
    assume info_lk_be: "fmlookup (TE_Functions ?be) funName = Some info"
       and ng_info: "FI_Ghost info = NotGhost"
    from info_lk_be have info_lk: "fmlookup (TE_Functions env) funName = Some info"
      by (simp add: body_env_for_def)
    from fun_ghost info_lk ng_info have
      "(\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs info).
            is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info),
                                    TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info) \<rparr>) ty) \<and>
       is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info),
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

  \<comment> \<open>(13) tyenv_nonghost_payloads_runtime ?be: inner override, TE_DataCtors,
        TE_GhostDatatypes inherited. \<close>
  have c13: "tyenv_nonghost_payloads_runtime ?be"
    unfolding tyenv_nonghost_payloads_runtime_def
  proof (intro allI impI)
    fix ctorName dtName tyVars payload
    assume ctor_lk_be: "fmlookup (TE_DataCtors ?be) ctorName = Some (dtName, tyVars, payload)"
       and ng_dt: "dtName |\<notin>| TE_GhostDatatypes ?be"
    from ctor_lk_be have ctor_lk: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload)"
      by (simp add: body_env_for_def)
    from ng_dt have ng_dt_env: "dtName |\<notin>| TE_GhostDatatypes env"
      by (simp add: body_env_for_def)
    from nonghost_payloads ctor_lk ng_dt_env
    have "is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list tyVars,
                                  TE_RuntimeTypeVars := fset_of_list tyVars \<rparr>) payload"
      unfolding tyenv_nonghost_payloads_runtime_def by blast
    thus "is_runtime_type (?be \<lparr> TE_TypeVars := fset_of_list tyVars,
                                  TE_RuntimeTypeVars := fset_of_list tyVars \<rparr>) payload"
      using rt_scope_eq by simp
  qed

  \<comment> \<open>(15) tyenv_runtime_tyvars_subset ?be: ?be sets TE_TypeVars and TE_RuntimeTypeVars
       to the same fset, so the subset relation is trivial. \<close>
  have c15: "tyenv_runtime_tyvars_subset ?be"
    unfolding tyenv_runtime_tyvars_subset_def by (simp add: body_env_for_def)

  \<comment> \<open>(14) tyenv_ghost_datatypes_subset ?be: TE_GhostDatatypes, TE_Datatypes inherited. \<close>
  have c14: "tyenv_ghost_datatypes_subset ?be"
    using ghost_dt_subset unfolding tyenv_ghost_datatypes_subset_def
    by (simp add: body_env_for_def)

  from c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
  show ?thesis unfolding tyenv_well_formed_def by simp
qed

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
