theory StateMatchesEnv
  imports CoreInterp "../core/CoreStmtTypecheck" "../core/CoreTermTypeMode"
          "../core/ModuleBodyEnv"
begin

(* This helper builds the type environment in which a function body should typecheck.
   Used in fun_info_matches_interp_fun to check that the function body (given in
   the InterpState) matches the function's type (given in the TypeEnv).

   The parameter names are NOT part of FunInfo (they belong with the definition, not
   the type), so they are supplied explicitly via `names`. In practice these come from
   the matching InterpFun's IF_Args (see fun_info_matches_interp_fun).

   Since this is used ONLY for the interpreter (specifically, state_matches_env), it
   is assumed that TE_AbstractTypes env = {||}.

   Most fields are inherited from the surrounding env. The changes are:
   - TE_LocalVars: replaced with the function's formal args (names from `names`,
     types from FI_TmArgs).
   - TE_GhostLocals: for a Ghost function, all function parameters; for a NotGhost
     function, the ghost parameters.
   - TE_ConstLocals: Var args are const initially; Ref args are not.
   - TE_TypeVars: replaced with the function's type variables.
   - TE_RuntimeTypeVars: for a NotGhost function, equal to TE_TypeVars; for a Ghost
     function, empty.
   - TE_ReturnType: set to the function's declared return type.
   - TE_FunctionGhost: set to the function's FI_Ghost.
   - TE_FunctionImpure: set to the function's FI_Impure.

   (With no abstract types, this is the same environment as module_body_env_for
   in core/ModuleBodyEnv.thy; see module_body_env_for_eq_body_env_for below.)
*)
definition body_env_for :: "CoreTyEnv \<Rightarrow> string list \<Rightarrow> FunInfo \<Rightarrow> CoreTyEnv" where
  "body_env_for env names funInfo =
    env \<lparr>
      TE_LocalVars := fmap_of_list (zip names (map fst (FI_TmArgs funInfo))),
      TE_GhostLocals := (if FI_Ghost funInfo = Ghost then fset_of_list names
                         else fset_of_list
                                (map fst
                                     (filter (\<lambda>(_, _, gh). gh = Ghost)
                                             (zip names (map snd (FI_TmArgs funInfo)))))),
      TE_ConstLocals := fset_of_list
        (map fst
             (filter (\<lambda>(_, vor, _). vor = Var) (zip names (map snd (FI_TmArgs funInfo))))),
      TE_TypeVars := fset_of_list (FI_TyArgs funInfo),
      TE_RuntimeTypeVars := (if FI_Ghost funInfo = NotGhost
                             then fset_of_list (FI_TyArgs funInfo) else {||}),
      TE_ReturnType := FI_ReturnType funInfo,
      TE_FunctionGhost := FI_Ghost funInfo,
      TE_FunctionImpure := FI_Impure funInfo,
      TE_ProofGoal := None,
      TE_ProofTopLevel := False
    \<rparr>"

(* In an env with no abstract types, the module typechecker's body
   environment coincides with the interpreter's, for any function. *)
lemma module_body_env_for_eq_body_env_for:
  assumes abs_empty: "TE_AbstractTypes env = {||}"
  shows "module_body_env_for env names info = body_env_for env names info"
  using assms unfolding module_body_env_for_def body_env_for_def by simp

(* Lemma: body_env_for does not depend on TE_ProofGoal. *)
lemma body_env_for_input_TE_ProofGoal_irrelevant [simp]:
  "body_env_for (env \<lparr> TE_ProofGoal := g \<rparr>) names funInfo = body_env_for env names funInfo"
  by (simp add: body_env_for_def)

(* Lemma: body_env_for does not depend on TE_ProofTopLevel. *)
lemma body_env_for_input_TE_ProofTopLevel_irrelevant [simp]:
  "body_env_for (env \<lparr> TE_ProofTopLevel := b \<rparr>) names funInfo = body_env_for env names funInfo"
  by (simp add: body_env_for_def)


(* state_matches_env requires a "store typing" which is a list of types, same length
   as `IS_Store state`, and giving the actual runtime type of each store slot.

   For Var variables, the store typing will always agree with the variable's declared
   type.

   For Ref variables, the type may sometimes drift ("dangling ref" problem) - e.g.
   consider
     var x: Either<i32,bool> = Left(1);
     ref r: i32 = <<project payload of x>>;
     x = Right(true);  // r now points to wrong type.
   This is not in itself an error, but any future usage of r would cause a RuntimeError
   (not a TypeError). 
*)

(* This says that a given local (Var) variable has a valid address in the store, 
   and the store typing at that address matches the variable's declared type (`ty`).
   The latter may contain type variables, so these are substituted out (using
   IS_TyArgs state) before checking. *)
definition local_var_in_state_with_type :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> CoreType list
    \<Rightarrow> string \<Rightarrow> CoreType \<Rightarrow> bool" where
  "local_var_in_state_with_type state env storeTyping name ty =
    (let groundTy = apply_subst (IS_TyArgs state) ty in
     case fmlookup (IS_Locals state) name of
      Some addr \<Rightarrow> addr < length (IS_Store state) \<and> storeTyping ! addr = groundTy
    | None \<Rightarrow>
      (case fmlookup (IS_Refs state) name of
        Some (addr, path) \<Rightarrow> addr < length (IS_Store state) \<and>
                             type_at_path env (storeTyping ! addr) path = Some groundTy
      | None \<Rightarrow> False))"

(* A global variable (in IS_Globals) has the expected type directly *)
definition global_var_in_state_with_type :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow>
    string \<Rightarrow> CoreType \<Rightarrow> bool" where
  "global_var_in_state_with_type state env name ty =
    (case fmlookup (IS_Globals state) name of
      Some val \<Rightarrow> value_has_type env val ty
    | None \<Rightarrow> False)"

(* Contract for an external function: for every valid input (type args, term args,
   world), the extern function returns a valid return value of the (substituted)
   return type, and a valid list of ref updates (one per Ref parameter) at the
   (substituted) Ref-parameter types.
   The type arguments are not required to be runtime types: ghost code may call
   the function at any ground, well-kinded type arguments.
   The world is opaque to soundness, so the contract says only one thing about
   it: a pure function (one that is not marked impure) returns the world it
   was given. This holds for every input, not only for well-typed arguments.
   Discharging this contract is the responsibility of whoever provides the
   ExternFunc; the soundness proof for extern calls consumes it. *)
definition extern_fun_contract :: "CoreTyEnv \<Rightarrow> FunInfo \<Rightarrow> 'w ExternFunc \<Rightarrow> bool" where
  "extern_fun_contract env funInfo externFun =
   ((\<forall>tySubst world vals.
       \<comment> \<open>tySubst maps exactly the callee's type arguments to ground,
           well-kinded types in the caller's env.\<close>
       fmdom tySubst = fset_of_list (FI_TyArgs funInfo) \<and>
       (\<forall>ty' \<in> fmran' tySubst. type_tyvars ty' = {}
                              \<and> is_well_kinded env ty') \<and>
       \<comment> \<open>Term arguments (vals) have the substituted parameter types.\<close>
       list_all2 (value_has_type env)
                 vals
                 (map (\<lambda>(ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo))
       \<longrightarrow>
       (case externFun world vals of (newWorld, refUpdates, retVal) \<Rightarrow>
          \<comment> \<open>Return value has the substituted return type.\<close>
          value_has_type env retVal (apply_subst tySubst (FI_ReturnType funInfo)) \<and>
          \<comment> \<open>One ref update per Ref parameter, in IF_Args order, at the substituted type.\<close>
          list_all2 (value_has_type env)
                    refUpdates
                    (map (\<lambda>(ty, _). apply_subst tySubst ty)
                         (filter (\<lambda>(_, vor, _). vor = Ref) (FI_TmArgs funInfo)))))
    \<comment> \<open>A pure function leaves the world unchanged.\<close>
    \<and> (\<not> FI_Impure funInfo \<longrightarrow> (\<forall>world vals. fst (externFun world vals) = world)))"

(* A pure extern function returns the world it was given. *)
lemma extern_fun_contract_pure_world:
  assumes "extern_fun_contract env funInfo externFun" and "\<not> FI_Impure funInfo"
  shows "fst (externFun world vals) = world"
  using assms unfolding extern_fun_contract_def by simp

(* This says that a given FunInfo and an InterpFun match, in a given type environment.
   The env is needed for typechecking the function body, if there is one. *)
definition fun_info_matches_interp_fun :: "CoreTyEnv \<Rightarrow> FunInfo \<Rightarrow> 'w InterpFun \<Rightarrow> bool" where
  "fun_info_matches_interp_fun env funInfo interpFun =
    \<comment> \<open>Type arguments match\<close>
    (FI_TyArgs funInfo = IF_TyArgs interpFun \<and>
    \<comment> \<open>Term arguments match: same length, and the Var/Ref and ghost markers agree.\<close>
    list_all2 (\<lambda>(_, vor1, gh1) (_, vor2, gh2). vor1 = vor2 \<and> gh1 = gh2)
              (FI_TmArgs funInfo) (IF_Args interpFun) \<and>
    \<comment> \<open>Parameter names are distinct.\<close>
    distinct (map fst (IF_Args interpFun)) \<and>
    \<comment> \<open>Impure flag matches\<close>
    FI_Impure funInfo = IF_Impure interpFun \<and>
    \<comment> \<open>Body certification: for Babylon functions, the body statement list
        typechecks in an appropriate env and ghost-mode; for external functions,
        the extern contract holds.\<close>
    (case IF_Body interpFun of
       Inl bodyStmts \<Rightarrow>
         core_statement_list_type
           (body_env_for env (map fst (IF_Args interpFun)) funInfo)
           (FI_Ghost funInfo) bodyStmts \<noteq> None
     | Inr externFun \<Rightarrow>
         extern_fun_contract env funInfo externFun) \<and>
    \<comment> \<open>An external function has no ghost parameter. (It is given the whole
        argument list, so ghost erasure could not drop a ghost argument.)\<close>
    (case IF_Body interpFun of
       Inl _ \<Rightarrow> True
     | Inr _ \<Rightarrow> no_ghost_params funInfo))"

(* Lemma: extern_fun_contract does not depend on TE_ProofGoal. *)
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

(* Lemma: extern_fun_contract does not depend on TE_ProofTopLevel. *)
lemma extern_fun_contract_TE_ProofTopLevel_irrelevant [simp]:
  "extern_fun_contract (env \<lparr> TE_ProofTopLevel := b \<rparr>) funInfo externFun
     = extern_fun_contract env funInfo externFun"
proof -
  have vht_eq: "value_has_type (env \<lparr> TE_ProofTopLevel := b \<rparr>) = value_has_type env"
    by (rule ext)+ simp
  show ?thesis
    unfolding extern_fun_contract_def
    using is_well_kinded_cong_env[where env' = "env \<lparr> TE_ProofTopLevel := b \<rparr>" and env = env]
          is_runtime_type_cong_env[where env' = "env \<lparr> TE_ProofTopLevel := b \<rparr>" and env = env]
          vht_eq
    by simp
qed

(* Lemma: fun_info_matches_interp_fun does not depend on TE_ProofGoal. *)
lemma fun_info_matches_interp_fun_TE_ProofGoal_irrelevant [simp]:
  "fun_info_matches_interp_fun (env \<lparr> TE_ProofGoal := g \<rparr>) funInfo interpFun
     = fun_info_matches_interp_fun env funInfo interpFun"
  by (simp add: fun_info_matches_interp_fun_def split: sum.splits)

(* Lemma: fun_info_matches_interp_fun does not depend on TE_ProofTopLevel. *)
lemma fun_info_matches_interp_fun_TE_ProofTopLevel_irrelevant [simp]:
  "fun_info_matches_interp_fun (env \<lparr> TE_ProofTopLevel := b \<rparr>) funInfo interpFun
     = fun_info_matches_interp_fun env funInfo interpFun"
  by (simp add: fun_info_matches_interp_fun_def split: sum.splits)


(* All local variables in the type env also exist in the state
   with the correct type. *)
definition local_vars_exist_in_state :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> CoreType list \<Rightarrow> bool" where
  "local_vars_exist_in_state state env storeTyping \<equiv>
    \<forall>name ty. fmlookup (TE_LocalVars env) name = Some ty \<longrightarrow>
      local_var_in_state_with_type state env storeTyping name ty"

(* All global variables in the type env
   also exist in the state with the correct type. *)
definition global_vars_exist_in_state :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "global_vars_exist_in_state state env \<equiv>
    \<forall>name ty. fmlookup (TE_GlobalVars env) name = Some ty \<longrightarrow>
      global_var_in_state_with_type state env name ty"

(* Converse for locals: if a variable is not in TE_LocalVars,
   then it is not in IS_Locals or IS_Refs. *)
definition no_extra_local_vars :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "no_extra_local_vars state env \<equiv>
    \<forall>name. fmlookup (TE_LocalVars env) name = None \<longrightarrow>
      fmlookup (IS_Locals state) name = None \<and>
      fmlookup (IS_Refs state) name = None"

(* Converse for globals: if a variable is not in TE_GlobalVars,
   then it is not in IS_Globals. *)
definition no_extra_global_vars :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "no_extra_global_vars state env \<equiv>
    \<forall>name. fmlookup (TE_GlobalVars env) name = None \<longrightarrow>
      fmlookup (IS_Globals state) name = None"

(* All functions in the type environment also exist in the state with
   corresponding numbers of arguments and other properties *)
definition funs_exist_in_state :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "funs_exist_in_state state env \<equiv>
    \<forall>name info. fmlookup (TE_Functions env) name = Some info \<longrightarrow>
      (case fmlookup (IS_Functions state) name of
        Some interpFun \<Rightarrow> fun_info_matches_interp_fun env info interpFun
      | None \<Rightarrow> False)"

(* There are no extra functions in the interp state *)
definition no_extra_funs :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "no_extra_funs state env \<equiv>
    \<forall>name. fmlookup (TE_Functions env) name = None \<longrightarrow>
      fmlookup (IS_Functions state) name = None"

(* Non-constant local variables are in IS_Locals or IS_Refs.
   (This is a consequence of local_vars_exist_in_state.) *)
definition non_consts_in_locals_or_refs :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "non_consts_in_locals_or_refs state env \<equiv>
    \<forall>name. fmlookup (TE_LocalVars env) name \<noteq> None \<and> name |\<notin>| TE_ConstLocals env \<longrightarrow>
      (fmlookup (IS_Locals state) name \<noteq> None \<or> fmlookup (IS_Refs state) name \<noteq> None)"

(* Proof that local_vars_exist_in_state implies non_consts_in_locals_or_refs. *)
lemma local_vars_exist_in_state_implies_non_consts_in_locals_or_refs:
  assumes "local_vars_exist_in_state state env storeTyping"
  shows "non_consts_in_locals_or_refs state env"
  using assms
  unfolding local_vars_exist_in_state_def non_consts_in_locals_or_refs_def
            local_var_in_state_with_type_def
  by (metis (lifting) option.exhaust option.simps(4))

(* The interpreter's IS_ConstLocals matches the type environment's TE_ConstLocals. *)
definition const_locals_match :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "const_locals_match state env \<equiv>
    IS_ConstLocals state = TE_ConstLocals env"

(* The store typing has the same length as the store, and every slot value has the
   designated type for its address.
   Note: the storeTyping only contains ground types, so no substitution is required here. *)
definition store_well_typed :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> CoreType list \<Rightarrow> bool" where
  "store_well_typed state env storeTyping \<equiv>
    length storeTyping = length (IS_Store state) \<and>
    (\<forall>addr. addr < length (IS_Store state) \<longrightarrow>
        value_has_type env (IS_Store state ! addr) (storeTyping ! addr))"

(* IS_TyArgs has domain exactly the env's type variables, and its range
   contains only ground, well-kinded types. *)
definition ty_args_well_formed :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "ty_args_well_formed state env \<equiv>
     fmdom (IS_TyArgs state) = TE_TypeVars env \<and>
     subst_range_tyvars (IS_TyArgs state) = {} \<and>
     (\<forall>ty \<in> fmran' (IS_TyArgs state). is_well_kinded env ty)"

(* For each datatype, if env says defCtorName heads the ctor list and
   TE_DataCtors records (dtName', tyvars, payload) for defCtorName, then
   IS_DefaultCtors carries the matching triple at dtName. Used to evaluate
   CoreTm_Default at a datatype type. *)
definition default_ctors_match :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "default_ctors_match state env \<equiv>
     \<forall>dtName defCtorName otherCtors dtName' tyvars payload.
       fmlookup (TE_DataCtorsByType env) dtName = Some (defCtorName # otherCtors) \<longrightarrow>
       fmlookup (TE_DataCtors env) defCtorName = Some (dtName', tyvars, payload) \<longrightarrow>
       fmlookup (IS_DefaultCtors state) dtName = Some (defCtorName, tyvars, payload)"

(* The state's datatype tables are those of the env. *)
definition tables_match :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "tables_match state env \<equiv>
     IS_Datatypes state = TE_Datatypes env \<and>
     IS_DataCtors state = TE_DataCtors env"

(* Overall definition: state matches environment under a given store typing. *)
(* The final conjunct (TE_AbstractTypes env = {||}) reflects that the interpreter can
   only run fully-linked programs (with no unresolved abstract types). *)
definition state_matches_env :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> CoreType list \<Rightarrow> bool" where
  "state_matches_env state env storeTyping \<equiv>
    local_vars_exist_in_state state env storeTyping \<and>
    global_vars_exist_in_state state env \<and>
    no_extra_local_vars state env \<and>
    no_extra_global_vars state env \<and>
    funs_exist_in_state state env \<and>
    no_extra_funs state env \<and>
    const_locals_match state env \<and>
    store_well_typed state env storeTyping \<and>
    ty_args_well_formed state env \<and>
    default_ctors_match state env \<and>
    tables_match state env \<and>
    TE_AbstractTypes env = {||}"


(* Lemma: state_matches_env does not depend on TE_ProofGoal. *)
lemma state_matches_env_TE_ProofGoal_irrelevant [simp]:
  "state_matches_env state (env \<lparr> TE_ProofGoal := g \<rparr>) storeTyping
     = state_matches_env state env storeTyping"
proof -
  have rt_eq: "\<And>ty. is_runtime_type (env \<lparr> TE_ProofGoal := g \<rparr>) ty = is_runtime_type env ty"
    by (rule is_runtime_type_cong_env) simp_all
  have wk_eq: "\<And>ty. is_well_kinded (env \<lparr> TE_ProofGoal := g \<rparr>) ty = is_well_kinded env ty"
    by (rule is_well_kinded_cong_env) simp_all
  show ?thesis
    by (simp add: state_matches_env_def
          local_vars_exist_in_state_def global_vars_exist_in_state_def
          no_extra_local_vars_def no_extra_global_vars_def
          funs_exist_in_state_def no_extra_funs_def
          const_locals_match_def
          store_well_typed_def ty_args_well_formed_def
          default_ctors_match_def tables_match_def
          local_var_in_state_with_type_def global_var_in_state_with_type_def
          rt_eq wk_eq
          split: option.splits)
qed

(* Lemma: state_matches_env does not depend on TE_ProofTopLevel. *)
lemma state_matches_env_TE_ProofTopLevel_irrelevant [simp]:
  "state_matches_env state (env \<lparr> TE_ProofTopLevel := b \<rparr>) storeTyping
     = state_matches_env state env storeTyping"
proof -
  have rt_eq: "\<And>ty. is_runtime_type (env \<lparr> TE_ProofTopLevel := b \<rparr>) ty = is_runtime_type env ty"
    by (rule is_runtime_type_cong_env) simp_all
  have wk_eq: "\<And>ty. is_well_kinded (env \<lparr> TE_ProofTopLevel := b \<rparr>) ty = is_well_kinded env ty"
    by (rule is_well_kinded_cong_env) simp_all
  show ?thesis
    by (simp add: state_matches_env_def
          local_vars_exist_in_state_def global_vars_exist_in_state_def
          no_extra_local_vars_def no_extra_global_vars_def
          funs_exist_in_state_def no_extra_funs_def
          const_locals_match_def
          store_well_typed_def ty_args_well_formed_def
          default_ctors_match_def tables_match_def
          local_var_in_state_with_type_def global_var_in_state_with_type_def
          rt_eq wk_eq
          split: option.splits)
qed

(* Lemma: state_matches_env does not depend on IS_World. *)
lemma state_matches_env_IS_World_irrelevant [simp]:
  "state_matches_env (state \<lparr> IS_World := w \<rparr>) env storeTyping
     = state_matches_env state env storeTyping"
  by (simp add: state_matches_env_def
        local_vars_exist_in_state_def global_vars_exist_in_state_def
        no_extra_local_vars_def no_extra_global_vars_def
        funs_exist_in_state_def no_extra_funs_def
        const_locals_match_def
        store_well_typed_def ty_args_well_formed_def
        default_ctors_match_def tables_match_def
        local_var_in_state_with_type_def global_var_in_state_with_type_def
        split: option.splits)

(* body_env_for preserves tyenv_well_formed, given that funInfo is one of env's
   functions, and that there is one name for each parameter.
   The assumption "abs_empty" is justified because body_env_for is only used by the
   interpreter, which only works with fully-linked programs (with no abstract types).
   Under that assumption body_env_for is module_body_env_for, so this is a
   corollary of module_body_env_for_well_formed (core/ModuleBodyEnv.thy). *)
lemma body_env_for_well_formed:
  assumes wf: "tyenv_well_formed env"
      and fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo"
      and abs_empty: "TE_AbstractTypes env = {||}"
      and len_names: "length names = length (FI_TmArgs funInfo)"
  shows "tyenv_well_formed (body_env_for env names funInfo)"
  using module_body_env_for_well_formed[OF wf fn_lookup len_names]
  by (simp add: module_body_env_for_eq_body_env_for[OF abs_empty])

(* body_env_for only depends on the "global" fields of env (TE_GlobalVars,
   TE_Functions, TE_Datatypes, TE_DataCtors, TE_DataCtorsByType,
   TE_GhostDatatypes); the "local" fields it sets are all overwritten from
   funInfo. So if two envs agree on the global fields, body_env_for produces
   the same env. *)
lemma body_env_for_cong:
  assumes "TE_GlobalVars env1 = TE_GlobalVars env2"
      and "TE_Functions env1 = TE_Functions env2"
      and "TE_Datatypes env1 = TE_Datatypes env2"
      and "TE_DataCtors env1 = TE_DataCtors env2"
      and "TE_DataCtorsByType env1 = TE_DataCtorsByType env2"
      and "TE_GhostDatatypes env1 = TE_GhostDatatypes env2"
      and "TE_AbstractTypes env1 = TE_AbstractTypes env2"
  shows "body_env_for env1 names funInfo = body_env_for env2 names funInfo"
  using assms unfolding body_env_for_def by simp

(* fun_info_matches_interp_fun congruence: agreement on the global fields plus
   TE_TypeVars and TE_RuntimeTypeVars implies the same result. The Inl
   (Babylon-body) case needs only the global fields (because body_env_for
   overwrites TE_TypeVars / TE_RuntimeTypeVars from FunInfo), but the Inr
   (extern) case reads them directly via extern_fun_contract. *)
lemma fun_info_matches_interp_fun_cong_env:
  assumes gv: "TE_GlobalVars env1 = TE_GlobalVars env2"
      and fn: "TE_Functions env1 = TE_Functions env2"
      and dt: "TE_Datatypes env1 = TE_Datatypes env2"
      and dc: "TE_DataCtors env1 = TE_DataCtors env2"
      and dcbt: "TE_DataCtorsByType env1 = TE_DataCtorsByType env2"
      and gd: "TE_GhostDatatypes env1 = TE_GhostDatatypes env2"
      and tv: "TE_TypeVars env1 = TE_TypeVars env2"
      and rtv: "TE_RuntimeTypeVars env1 = TE_RuntimeTypeVars env2"
      and abs: "TE_AbstractTypes env1 = TE_AbstractTypes env2"
  shows "fun_info_matches_interp_fun env1 funInfo interpFun =
         fun_info_matches_interp_fun env2 funInfo interpFun"
proof -
  have body_eq: "\<And>names. body_env_for env1 names funInfo = body_env_for env2 names funInfo"
    by (rule body_env_for_cong[OF gv fn dt dc dcbt gd abs])
  have wk_eq: "\<And>ty. is_well_kinded env1 ty = is_well_kinded env2 ty"
    by (rule is_well_kinded_cong_env[OF tv dt])
  have rt_eq: "\<And>ty. is_runtime_type env1 ty = is_runtime_type env2 ty"
    by (rule is_runtime_type_cong_env[OF gd rtv])
  have vht_eq: "value_has_type env1 = value_has_type env2"
    by (rule ext)+ (rule value_has_type_cong_env[OF dc dt tv])
  have ext_eq: "\<And>externFun. extern_fun_contract env1 funInfo externFun
                              = extern_fun_contract env2 funInfo externFun"
    by (simp add: extern_fun_contract_def wk_eq rt_eq vht_eq)
  show ?thesis
    unfolding fun_info_matches_interp_fun_def
    by (simp add: body_eq ext_eq split: sum.splits)
qed

end
