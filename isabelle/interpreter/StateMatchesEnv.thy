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
      TE_FunctionGhost := NotGhost,
      TE_ProofGoal := None
    \<rparr>"

(* body_env_for overrides TE_ProofGoal (to None) and depends on no other field
   that a TE_ProofGoal update touches, so the input env's proof goal is
   irrelevant. *)
lemma body_env_for_input_TE_ProofGoal_irrelevant [simp]:
  "body_env_for (env \<lparr> TE_ProofGoal := g \<rparr>) funInfo = body_env_for env funInfo"
  by (simp add: body_env_for_def)

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

(* Contract for an external function: for every well-formed instantiation of the
   callee's type arguments and every well-typed value list, the extern function
   returns a return value of the (substituted) return type and a list of ref
   updates (one per Ref parameter, in IF_Args / FI_TmArgs order) at the
   (substituted) Ref-parameter types.
   The world is opaque to soundness so it is left unconstrained.
   Discharging this contract is the responsibility of whoever provides the
   ExternFunc; the soundness proof for extern calls consumes it. *)
definition extern_fun_contract :: "CoreTyEnv \<Rightarrow> FunInfo \<Rightarrow> 'w ExternFunc \<Rightarrow> bool" where
  "extern_fun_contract env funInfo externFun =
    (\<forall>tySubst world vals.
       \<comment> \<open>tySubst maps exactly the callee's type arguments to runtime, well-kinded
           types in the caller's env\<close>
       fmdom tySubst = fset_of_list (FI_TyArgs funInfo) \<and>
       (\<forall>ty' \<in> fmran' tySubst. is_well_kinded env ty' \<and> is_runtime_type env ty') \<and>
       \<comment> \<open>arguments have the substituted parameter types\<close>
       list_all2 (value_has_type env)
                 vals
                 (map (\<lambda>(_, ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo))
       \<longrightarrow>
       (case externFun world vals of (newWorld, refUpdates, retVal) \<Rightarrow>
          \<comment> \<open>return value has the substituted return type\<close>
          value_has_type env retVal (apply_subst tySubst (FI_ReturnType funInfo)) \<and>
          \<comment> \<open>one ref update per Ref parameter, in IF_Args order, at the substituted type\<close>
          list_all2 (value_has_type env)
                    refUpdates
                    (map (\<lambda>(_, ty, _). apply_subst tySubst ty)
                         (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs funInfo)))))"

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

(* extern_fun_contract reads env only through is_well_kinded, is_runtime_type
   and value_has_type, all of which ignore TE_ProofGoal. *)
lemma extern_fun_contract_TE_ProofGoal_irrelevant [simp]:
  "extern_fun_contract (env \<lparr> TE_ProofGoal := g \<rparr>) funInfo externFun
     = extern_fun_contract env funInfo externFun"
proof -
  have vht_eq: "value_has_type (env \<lparr> TE_ProofGoal := g \<rparr>) = value_has_type env"
    by (rule ext)+ simp
  show ?thesis
    unfolding extern_fun_contract_def
    using is_well_kinded_cong_env[where env' = "env \<lparr> TE_ProofGoal := g \<rparr>" and env = env]
          is_runtime_type_cong_env[where env' = "env \<lparr> TE_ProofGoal := g \<rparr>" and env = env]
          vht_eq
    by simp
qed

(* fun_info_matches_interp_fun depends on env only through body_env_for env
   funInfo and extern_fun_contract, both of which ignore TE_ProofGoal. *)
lemma fun_info_matches_interp_fun_TE_ProofGoal_irrelevant [simp]:
  "fun_info_matches_interp_fun (env \<lparr> TE_ProofGoal := g \<rparr>) funInfo interpFun
     = fun_info_matches_interp_fun env funInfo interpFun"
  by (simp add: fun_info_matches_interp_fun_def split: sum.splits)


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

(* type_at_path reads env only through TE_DataCtors, so a TE_ProofGoal update
   is irrelevant. *)
lemma type_at_path_TE_ProofGoal_irrelevant [simp]:
  "type_at_path (env \<lparr> TE_ProofGoal := g \<rparr>) ty p = type_at_path env ty p"
proof (induction p arbitrary: ty)
  case Nil then show ?case by simp
next
  case (Cons step rest)
  show ?case
    by (cases ty; cases step) (simp_all add: Cons.IH split: option.splits)
qed

(* state_matches_env does not depend on TE_ProofGoal: every conjunct projects
   only the variable/function/store fields, never the proof goal. *)
lemma state_matches_env_TE_ProofGoal_irrelevant [simp]:
  "state_matches_env state (env \<lparr> TE_ProofGoal := g \<rparr>) storeTyping
     = state_matches_env state env storeTyping"
  by (simp add: state_matches_env_def
        local_vars_exist_in_state_def global_vars_exist_in_state_def
        no_extra_local_vars_def no_extra_global_vars_def
        funs_exist_in_state_def no_extra_funs_def
        non_consts_in_locals_or_refs_def const_locals_match_def
        store_well_typed_def
        local_var_in_state_with_type_def global_var_in_state_with_type_def
        split: option.splits)

(* state_matches_env does not depend on IS_World: every conjunct projects
   only IS_Locals, IS_Refs, IS_Globals, IS_Functions, IS_Store, or IS_ConstLocals. *)
lemma state_matches_env_IS_World_irrelevant [simp]:
  "state_matches_env (state \<lparr> IS_World := w \<rparr>) env storeTyping
     = state_matches_env state env storeTyping"
  by (simp add: state_matches_env_def
        local_vars_exist_in_state_def global_vars_exist_in_state_def
        no_extra_local_vars_def no_extra_global_vars_def
        funs_exist_in_state_def no_extra_funs_def
        non_consts_in_locals_or_refs_def const_locals_match_def
        store_well_typed_def
        local_var_in_state_with_type_def global_var_in_state_with_type_def
        split: option.splits)

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

(* fun_info_matches_interp_fun congruence: agreement on the global fields plus
   TE_TypeVars and TE_RuntimeTypeVars implies the same result. The Inl
   (Babylon-body) case needs only the global fields (because body_env_for
   overwrites TE_TypeVars / TE_RuntimeTypeVars from FunInfo), but the Inr
   (extern) case reads them directly via extern_fun_contract. *)
lemma fun_info_matches_interp_fun_cong_env:
  assumes gv: "TE_GlobalVars env1 = TE_GlobalVars env2"
      and gg: "TE_GhostGlobals env1 = TE_GhostGlobals env2"
      and fn: "TE_Functions env1 = TE_Functions env2"
      and dt: "TE_Datatypes env1 = TE_Datatypes env2"
      and dc: "TE_DataCtors env1 = TE_DataCtors env2"
      and dcbt: "TE_DataCtorsByType env1 = TE_DataCtorsByType env2"
      and gd: "TE_GhostDatatypes env1 = TE_GhostDatatypes env2"
      and tv: "TE_TypeVars env1 = TE_TypeVars env2"
      and rtv: "TE_RuntimeTypeVars env1 = TE_RuntimeTypeVars env2"
  shows "fun_info_matches_interp_fun env1 funInfo interpFun =
         fun_info_matches_interp_fun env2 funInfo interpFun"
proof -
  have body_eq: "body_env_for env1 funInfo = body_env_for env2 funInfo"
    by (rule body_env_for_cong[OF gv gg fn dt dc dcbt gd])
  have wk_eq: "\<And>ty. is_well_kinded env1 ty = is_well_kinded env2 ty"
    by (rule is_well_kinded_cong_env[OF tv dt])
  have rt_eq: "\<And>ty. is_runtime_type env1 ty = is_runtime_type env2 ty"
    by (rule is_runtime_type_cong_env[OF gd rtv])
  have vht_eq: "value_has_type env1 = value_has_type env2"
    by (rule ext)+ (rule value_has_type_cong_env[OF dc dt tv gd rtv])
  have ext_eq: "\<And>externFun. extern_fun_contract env1 funInfo externFun
                              = extern_fun_contract env2 funInfo externFun"
    by (simp add: extern_fun_contract_def wk_eq rt_eq vht_eq)
  show ?thesis
    unfolding fun_info_matches_interp_fun_def
    by (simp add: body_eq ext_eq split: sum.splits)
qed

end
