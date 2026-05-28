theory TypeSoundnessHelpers
  imports StateMatchesEnv CoreInterpPreservation
          "../core/CoreStmtTypecheck" "../core/CoreTypeSubst"
begin

(*-----------------------------------------------------------------------------*)
(* Definitions for type-soundness of interpreter results *)
(*-----------------------------------------------------------------------------*)

(* Type soundness for terms means that evaluating a well-typed term will either:
    - Succeed with a value of the correct type
    - Fail with RuntimeError
    - Fail with InsufficientFuel
   It will not:
    - Succeed with a value of the wrong type
    - Fail with TypeError *)

fun sound_error_result :: "InterpError \<Rightarrow> bool" where
  "sound_error_result TypeError = False"
| "sound_error_result RuntimeError = True"
| "sound_error_result InsufficientFuel = True"

(* ty is in the env in which the term was typechecked. If that env is a generic
   function body, ty may mention the function's type variables; we resolve them
   via apply_subst (IS_TyArgs state). The state is the one passed to the
   interpreter when producing the result. *)
fun sound_term_result :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> CoreType
    \<Rightarrow> InterpError + CoreValue \<Rightarrow> bool" where
  "sound_term_result state env ty (Inl err) = sound_error_result err"
| "sound_term_result state env ty (Inr val) =
    value_has_type env val (apply_subst (IS_TyArgs state) ty)"

fun sound_term_results :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> CoreType list
    \<Rightarrow> InterpError + CoreValue list \<Rightarrow> bool" where
  "sound_term_results state env types (Inl err) = sound_error_result err"
| "sound_term_results state env types (Inr vals) =
    list_all2 (value_has_type env) vals (map (apply_subst (IS_TyArgs state)) types)"

(* A writable lvalue is sound if its address is in the store and its path
   statically descends to the expected type (resolved through IS_TyArgs state)
   in the store typing. If get_value_at_path succeeds, the obtained value has
   that resolved type (by get_value_at_path_type); if it fails, the error is
   RuntimeError. *)
fun sound_lvalue_result :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> CoreType list \<Rightarrow> CoreType
    \<Rightarrow> InterpError + (nat \<times> LValuePath list) \<Rightarrow> bool" where
  "sound_lvalue_result state env storeTyping ty (Inl err) = sound_error_result err"
| "sound_lvalue_result state env storeTyping ty (Inr (addr, path)) =
    (addr < length (IS_Store state) \<and>
     type_at_path env (storeTyping ! addr) path = Some (apply_subst (IS_TyArgs state) ty))"

(* The second store typing extends the first: every address present in the
   first typing retains the same type in the second, and the second may have
   additional entries appended. This captures the fact that executing a single
   statement only ever grows the store (or leaves it the same length) — while
   a While/Match body may internally call restore_scope, that only truncates
   slots the statement itself allocated, so the net effect still extends the
   old store typing rather than removing any pre-existing entries. *)
definition storeTyping_extends :: "CoreType list \<Rightarrow> CoreType list \<Rightarrow> bool" where
  "storeTyping_extends st1 st2 \<equiv> \<exists>suffix. st2 = st1 @ suffix"

lemma storeTyping_extends_refl: "storeTyping_extends st st"
  unfolding storeTyping_extends_def by (rule exI[of _ "[]"]) simp

lemma storeTyping_extends_trans:
  "storeTyping_extends st1 st2 \<Longrightarrow> storeTyping_extends st2 st3 \<Longrightarrow> storeTyping_extends st1 st3"
  unfolding storeTyping_extends_def by auto

lemma storeTyping_extends_append: "storeTyping_extends st (st @ suffix)"
  unfolding storeTyping_extends_def by blast

(* retTy is in the caller's env; if the caller is itself a generic function its
   tyvars may appear in retTy. apply_subst (IS_TyArgs newState) resolves them:
   IS_TyArgs is restored to the caller's bindings at function return (see
   restore_scope), so newState's IS_TyArgs is the caller's. *)
fun sound_function_call_result :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> CoreType list
    \<Rightarrow> CoreType \<Rightarrow> InterpError + ('w InterpState \<times> CoreValue) \<Rightarrow> bool" where
  "sound_function_call_result state env storeTyping retTy (Inl err) = sound_error_result err"
| "sound_function_call_result state env storeTyping retTy (Inr (newState, retVal)) =
    ((\<exists>storeTyping'. state_matches_env newState env storeTyping'
                   \<and> storeTyping_extends storeTyping storeTyping')
     \<and> IS_TyArgs newState = IS_TyArgs state
     \<and> value_has_type env retVal (apply_subst (IS_TyArgs state) retTy))"

(* env is the env the statement was typechecked in. For a Return inside a
   generic function body, TE_ReturnType env mentions that function's tyvars,
   which we resolve via IS_TyArgs state'. *)
fun sound_statement_result :: "CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> CoreType list
    \<Rightarrow> InterpError + 'w ExecResult \<Rightarrow> bool" where
  "sound_statement_result env env' storeTyping (Inl err) = sound_error_result err"
| "sound_statement_result env env' storeTyping (Inr (Continue state')) =
    (\<exists>storeTyping'. state_matches_env state' env' storeTyping'
                  \<and> storeTyping_extends storeTyping storeTyping')"
| "sound_statement_result env env' storeTyping (Inr (Return state' retVal)) =
    (value_has_type env retVal (apply_subst (IS_TyArgs state') (TE_ReturnType env)) \<and>
     (\<exists>env_mid storeTyping'. tyenv_fixed_eq env env_mid \<and> tyenv_fixed_eq env_mid env' \<and>
                tyenv_well_formed env_mid \<and>
                state_matches_env state' env_mid storeTyping'
              \<and> storeTyping_extends storeTyping storeTyping'))"

(* sound_statement_result does not depend on TE_ProofGoal of either env: each
   conjunct that mentions env/env' does so through value_has_type,
   state_matches_env, tyenv_fixed_eq, or TE_ReturnType, all of which ignore
   TE_ProofGoal. *)
lemma sound_statement_result_TE_ProofGoal_irrelevant_left [simp]:
  "sound_statement_result (env \<lparr> TE_ProofGoal := g \<rparr>) env' storeTyping res
     = sound_statement_result env env' storeTyping res"
proof (cases res)
  case (Inl err) then show ?thesis by simp
next
  case (Inr execRes) then show ?thesis
    by (cases execRes) simp_all
qed

lemma sound_statement_result_TE_ProofGoal_irrelevant_right [simp]:
  "sound_statement_result env (env' \<lparr> TE_ProofGoal := g \<rparr>) storeTyping res
     = sound_statement_result env env' storeTyping res"
proof (cases res)
  case (Inl err) then show ?thesis by simp
next
  case (Inr execRes) then show ?thesis
    by (cases execRes) simp_all
qed


(*-----------------------------------------------------------------------------*)
(* Helpers for interpreter soundness lemmas *)
(*-----------------------------------------------------------------------------*)

(* Property of int_complement *)
lemma int_complement_fits:
  assumes "int_fits sign bits i"
  shows "int_fits sign bits (int_complement sign bits i)"
  using assms by (cases sign; cases bits; auto)

(* type_at_path of a concatenated path: first walk to the intermediate type,
   then continue with the suffix from there. *)
lemma type_at_path_append:
  assumes "type_at_path env t p1 = Some t1"
  shows "type_at_path env t (p1 @ p2) = type_at_path env t1 p2"
using assms proof (induction p1 arbitrary: t)
  case Nil then show ?case by simp
next
  case (Cons step rest)
  show ?case
  proof (cases t)
    case (CoreTy_Record fieldTypes)
    with Cons.prems show ?thesis
      by (cases step) (auto split: option.splits intro: Cons.IH)
  next
    case (CoreTy_Datatype dtName argTypes)
    with Cons.prems show ?thesis
      by (cases step) (auto split: option.splits if_splits intro: Cons.IH)
  next
    case (CoreTy_Array elemTy dims)
    with Cons.prems show ?thesis
      by (cases step) (auto intro: Cons.IH)
  next
    case CoreTy_Bool with Cons.prems show ?thesis by (cases step) simp_all
  next
    case (CoreTy_FiniteInt x y) with Cons.prems show ?thesis by (cases step) simp_all
  next
    case CoreTy_MathInt with Cons.prems show ?thesis by (cases step) simp_all
  next
    case CoreTy_MathReal with Cons.prems show ?thesis by (cases step) simp_all
  next
    case (CoreTy_Var x) with Cons.prems show ?thesis by (cases step) simp_all
  qed
qed

(* type_at_path depends on the environment only through TE_DataCtors (used in the
   variant case). If two environments agree on TE_DataCtors, they give the same
   type_at_path result. *)
lemma type_at_path_cong_env:
  assumes "TE_DataCtors env' = TE_DataCtors env"
  shows "type_at_path env t p = type_at_path env' t p"
proof (induction p arbitrary: t)
  case Nil then show ?case by simp
next
  case (Cons step rest)
  show ?case
  proof (cases t)
    case (CoreTy_Record fieldTypes)
    then show ?thesis
      by (cases step) (simp_all add: Cons.IH split: option.splits)
  next
    case (CoreTy_Datatype dtName argTypes)
    then show ?thesis
      by (cases step) (simp_all add: assms Cons.IH split: option.splits if_splits)
  next
    case (CoreTy_Array elemTy dims)
    then show ?thesis
      by (cases step) (simp_all add: Cons.IH)
  next
    case CoreTy_Bool then show ?thesis by (cases step) simp_all
  next
    case (CoreTy_FiniteInt x y) then show ?thesis by (cases step) simp_all
  next
    case CoreTy_MathInt then show ?thesis by (cases step) simp_all
  next
    case CoreTy_MathReal then show ?thesis by (cases step) simp_all
  next
    case (CoreTy_Var x) then show ?thesis by (cases step) simp_all
  qed
qed

(* After alloc_store + fmupd of locals, the new state matches the extended env
   under an extended storeTyping (with rhsTy appended).
   General version that works for both const (let) and non-const (var decl) cases.
   The variable is removed from TE_GhostLocals (since the new binding is non-ghost). *)
lemma state_matches_env_add_local:
  assumes state_env: "state_matches_env state env storeTyping"
    and val_typed: "value_has_type env val (apply_subst (IS_TyArgs state) rhsTy)"
    and state'_eq: "(state', addr) = alloc_store state val"
    and state''_eq: "state'' = state' \<lparr> IS_Locals := fmupd var addr (IS_Locals state'),
                                        IS_Refs := fmdrop var (IS_Refs state'),
                                        IS_ConstLocals := new_state_cn \<rparr>"
    and env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                               TE_GhostLocals := fminus (TE_GhostLocals env) {|var|},
                               TE_ConstLocals := new_env_cn \<rparr>"
    and cn_match: "const_locals_match state'' env'"
    and cn_other: "\<And>name. name \<noteq> var \<Longrightarrow>
                     (name |\<in>| TE_ConstLocals env' \<longleftrightarrow> name |\<in>| TE_ConstLocals env)"
  shows "state_matches_env state'' env' (storeTyping @ [apply_subst (IS_TyArgs state) rhsTy])"
proof -
  (* Facts about alloc_store *)
  from state'_eq have addr_eq: "addr = length (IS_Store state)"
    and store'_eq: "IS_Store state' = IS_Store state @ [val]"
    and locals'_eq: "IS_Locals state' = IS_Locals state"
    and refs'_eq: "IS_Refs state' = IS_Refs state"
    and consts'_eq: "IS_Globals state' = IS_Globals state"
    and funs'_eq: "IS_Functions state' = IS_Functions state"
    by auto

  (* Facts about state'' *)
  have store''_eq: "IS_Store state'' = IS_Store state @ [val]"
    using state''_eq store'_eq by simp
  have locals''_eq: "IS_Locals state'' = fmupd var addr (IS_Locals state)"
    using state''_eq locals'_eq by simp
  have refs''_eq: "IS_Refs state'' = fmdrop var (IS_Refs state)"
    using state''_eq refs'_eq by simp
  have consts''_eq: "IS_Globals state'' = IS_Globals state"
    using state''_eq consts'_eq by simp
  have funs''_eq: "IS_Functions state'' = IS_Functions state"
    using state''_eq funs'_eq by simp
  have tyargs''_eq [simp]: "IS_TyArgs state'' = IS_TyArgs state"
    using state''_eq state'_eq by auto

  (* The new address points to val *)
  have addr_valid: "addr < length (IS_Store state'')"
    using addr_eq store''_eq by simp
  have val_at_addr: "IS_Store state'' ! addr = val"
    using addr_eq store''_eq by (simp add: nth_append)

  (* Old addresses are still valid and point to the same values *)
  have old_addrs: "\<And>a. a < length (IS_Store state) \<Longrightarrow>
      a < length (IS_Store state'') \<and> IS_Store state'' ! a = IS_Store state ! a"
    using store''_eq by (simp add: nth_append)

  (* Old storeTyping has the right length *)
  from state_env have old_st_len: "length storeTyping = length (IS_Store state)"
    unfolding state_matches_env_def store_well_typed_def by simp

  (* Facts about the new storeTyping. Stored entry is the substituted (ground)
     type — env binds var to rhsTy, but storeTyping holds the substituted form so
     local_var_in_state_with_type's apply_subst matches. *)
  let ?rhsTy' = "apply_subst (IS_TyArgs state) rhsTy"
  let ?st' = "storeTyping @ [?rhsTy']"
  have st'_len: "length ?st' = length (IS_Store state'')"
    using old_st_len store''_eq by simp
  have st'_at_addr: "?st' ! addr = ?rhsTy'"
    using addr_eq old_st_len by (simp add: nth_append)
  have st'_at_old: "\<And>a. a < length (IS_Store state) \<Longrightarrow> ?st' ! a = storeTyping ! a"
    using old_st_len by (simp add: nth_append)

  (* value_has_type is the same in env and env' *)
  have env'_fields: "TE_DataCtors env' = TE_DataCtors env"
                    "TE_Datatypes env' = TE_Datatypes env"
                    "TE_TypeVars env' = TE_TypeVars env"
                    "TE_GhostDatatypes env' = TE_GhostDatatypes env"
                    "TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env"
    using env'_eq by simp_all
  have vht_eq: "\<And>v t. value_has_type env' v t = value_has_type env v t"
    using value_has_type_cong_env[OF env'_fields] .
  have tap_eq: "\<And>t p. type_at_path env t p = type_at_path env' t p"
    using type_at_path_cong_env[OF env'_fields(1)] .

  (* 1. local_vars_exist_in_state *)
  have "local_vars_exist_in_state state'' env' ?st'"
    unfolding local_vars_exist_in_state_def
  proof (intro allI impI, elim conjE)
    fix name ty
    assume lookup: "fmlookup (TE_LocalVars env') name = Some ty"
      and not_ghost: "name |\<notin>| TE_GhostLocals env'"
    show "local_var_in_state_with_type state'' env' ?st' name ty"
    proof (cases "name = var")
      case True
      (* The new variable - points to val at addr, with storeTyping entry = rhsTy *)
      then have "ty = rhsTy" using lookup env'_eq by simp
      then show ?thesis
        using True locals''_eq addr_valid st'_at_addr
        unfolding local_var_in_state_with_type_def by simp
    next
      case False
      (* An existing local variable *)
      then have "fmlookup (TE_LocalVars env) name = Some ty"
        using lookup env'_eq by simp
      moreover have "name |\<notin>| TE_GhostLocals env"
        using not_ghost env'_eq False by auto
      ultimately have old: "local_var_in_state_with_type state env storeTyping name ty"
        using state_env unfolding state_matches_env_def local_vars_exist_in_state_def by blast
      (* Locals lookup is unchanged for name \<noteq> var *)
      have locals_name: "fmlookup (IS_Locals state'') name = fmlookup (IS_Locals state) name"
        using False locals''_eq by simp
      from old show ?thesis
      proof (cases "fmlookup (IS_Locals state) name")
        case (Some a)
        (* name is a local in old state, pointing to address a *)
        from old Some have a_valid: "a < length (IS_Store state)"
          and st_eq: "storeTyping ! a = apply_subst (IS_TyArgs state) ty"
          unfolding local_var_in_state_with_type_def by auto
        from old_addrs[OF a_valid] have a_valid'': "a < length (IS_Store state'')" by simp
        from st'_at_old[OF a_valid] st_eq
        have "?st' ! a = apply_subst (IS_TyArgs state'') ty" by simp
        then show ?thesis
          using Some locals_name a_valid''
          unfolding local_var_in_state_with_type_def by simp
      next
        case None
        have refs_name: "fmlookup (IS_Refs state'') name = fmlookup (IS_Refs state) name"
          using False refs''_eq by simp
        from old None obtain addrPath where
          refs_lookup: "fmlookup (IS_Refs state) name = Some addrPath"
          unfolding local_var_in_state_with_type_def by (auto split: option.splits)
        obtain aa ba where ap_eq: "addrPath = (aa, ba)" by (cases addrPath) auto
        from old None refs_lookup ap_eq have
          aa_valid: "aa < length (IS_Store state)" and
          path_ty: "type_at_path env (storeTyping ! aa) ba = Some (apply_subst (IS_TyArgs state) ty)"
          unfolding local_var_in_state_with_type_def by auto
        from old_addrs[OF aa_valid] have aa_valid'': "aa < length (IS_Store state'')" by simp
        from st'_at_old[OF aa_valid] have st_at_aa: "?st' ! aa = storeTyping ! aa" by simp
        from path_ty tap_eq st_at_aa
        have path_ty': "type_at_path env' (?st' ! aa) ba = Some (apply_subst (IS_TyArgs state'') ty)"
          by simp
        show ?thesis
          unfolding local_var_in_state_with_type_def
          using locals_name refs_name None refs_lookup ap_eq aa_valid'' path_ty'
          by simp
      qed
    qed
  qed

  (* 2. global_vars_exist_in_state: globals unchanged *)
  moreover have "global_vars_exist_in_state state'' env'"
    unfolding global_vars_exist_in_state_def
  proof (intro allI impI, elim conjE)
    fix name ty
    assume lookup: "fmlookup (TE_GlobalVars env') name = Some ty"
      and not_ghost: "name |\<notin>| TE_GhostGlobals env'"
    have "fmlookup (TE_GlobalVars env) name = Some ty"
      using lookup env'_eq by simp
    moreover have "name |\<notin>| TE_GhostGlobals env"
      using not_ghost env'_eq by auto
    ultimately have "global_var_in_state_with_type state env name ty"
      using state_env unfolding state_matches_env_def global_vars_exist_in_state_def by blast
    then show "global_var_in_state_with_type state'' env' name ty"
      using consts''_eq vht_eq unfolding global_var_in_state_with_type_def
      by (auto split: option.splits)
  qed

  (* 3. no_extra_local_vars *)
  moreover have "no_extra_local_vars state'' env'"
    unfolding no_extra_local_vars_def
  proof (intro allI impI)
    fix name
    assume ante: "fmlookup (TE_LocalVars env') name = None \<or> name |\<in>| TE_GhostLocals env'"
    show "fmlookup (IS_Locals state'') name = None \<and>
          fmlookup (IS_Refs state'') name = None"
    proof (cases "name = var")
      case True
      then have "fmlookup (TE_LocalVars env') var = Some rhsTy" using env'_eq by simp
      with ante True have "var |\<in>| TE_GhostLocals env'" by simp
      hence False using env'_eq by simp
      then show ?thesis ..
    next
      case False
      then have tv_eq: "fmlookup (TE_LocalVars env') name = fmlookup (TE_LocalVars env) name"
        using env'_eq by simp
      have gv_iff: "name |\<in>| TE_GhostLocals env' \<longleftrightarrow> name |\<in>| TE_GhostLocals env"
        using False env'_eq by auto
      from ante tv_eq gv_iff
      have "fmlookup (TE_LocalVars env) name = None \<or> name |\<in>| TE_GhostLocals env"
        by simp
      then have "fmlookup (IS_Locals state) name = None \<and>
                 fmlookup (IS_Refs state) name = None"
        using state_env unfolding state_matches_env_def no_extra_local_vars_def by blast
      then show ?thesis using False locals''_eq refs''_eq by simp
    qed
  qed

  (* 4. no_extra_global_vars: globals unchanged *)
  moreover have "no_extra_global_vars state'' env'"
    using state_env consts''_eq env'_eq
    unfolding state_matches_env_def no_extra_global_vars_def by simp

  (* 5. funs_exist_in_state *)
  moreover have "funs_exist_in_state state'' env'"
  proof -
    from state_env have old_fes: "funs_exist_in_state state env"
      unfolding state_matches_env_def by simp
    have fcong: "\<And>info ifn. fun_info_matches_interp_fun env' info ifn =
                              fun_info_matches_interp_fun env info ifn"
      by (rule fun_info_matches_interp_fun_cong_env)
         (use env'_eq in simp_all)
    have funs_eq: "TE_Functions env' = TE_Functions env" using env'_eq by simp
    show ?thesis
      unfolding funs_exist_in_state_def
      using old_fes funs''_eq funs_eq fcong
      by (metis funs_exist_in_state_def option.case_eq_if)
  qed

  (* 6. no_extra_funs *)
  moreover have "no_extra_funs state'' env'"
    using state_env funs''_eq env'_eq
    unfolding state_matches_env_def no_extra_funs_def by simp

  (* 7. non_consts_in_locals_or_refs *)
  moreover have "non_consts_in_locals_or_refs state'' env'"
    unfolding non_consts_in_locals_or_refs_def
  proof (intro allI impI, elim conjE)
    fix name
    assume tv: "fmlookup (TE_LocalVars env') name \<noteq> None"
      and ng: "name |\<notin>| TE_GhostLocals env'"
      and nc: "name |\<notin>| TE_ConstLocals env'"
    show "fmlookup (IS_Locals state'') name \<noteq> None \<or>
          fmlookup (IS_Refs state'') name \<noteq> None"
    proof (cases "name = var")
      case True
      then show ?thesis using locals''_eq by simp
    next
      case False
      then have "fmlookup (TE_LocalVars env) name \<noteq> None"
        using tv env'_eq by simp
      moreover have "name |\<notin>| TE_GhostLocals env"
        using ng env'_eq False by auto
      moreover have "name |\<notin>| TE_ConstLocals env"
        using nc cn_other[OF False] by simp
      ultimately have "fmlookup (IS_Locals state) name \<noteq> None \<or>
                       fmlookup (IS_Refs state) name \<noteq> None"
        using state_env
        unfolding state_matches_env_def non_consts_in_locals_or_refs_def by blast
      then show ?thesis using False locals''_eq refs''_eq by simp
    qed
  qed

  (* 8. const_locals_match *)
  moreover have "const_locals_match state'' env'"
    using cn_match .

  (* 9. store_well_typed for the extended storeTyping *)
  moreover have "store_well_typed state'' env' ?st'"
    unfolding store_well_typed_def
  proof (intro conjI allI impI)
    show "length ?st' = length (IS_Store state'')" using st'_len .
  next
    fix a
    assume a_lt: "a < length (IS_Store state'')"
    show "value_has_type env' (IS_Store state'' ! a) (?st' ! a)"
    proof (cases "a = addr")
      case True
      with val_at_addr st'_at_addr val_typed vht_eq show ?thesis by simp
    next
      case False
      from a_lt store''_eq have a_lt_old: "a < length (IS_Store state)"
        using False addr_eq by (auto simp add: nth_append)
      have store_a: "IS_Store state'' ! a = IS_Store state ! a"
        using old_addrs[OF a_lt_old] by simp
      have st_a: "?st' ! a = storeTyping ! a"
        using st'_at_old[OF a_lt_old] .
      from state_env a_lt_old
      have "value_has_type env (IS_Store state ! a) (storeTyping ! a)"
        unfolding state_matches_env_def store_well_typed_def by simp
      with store_a st_a vht_eq show ?thesis by simp
    qed
  qed

  moreover have tawf'': "ty_args_well_formed state'' env'"
  proof -
    have rt_eq: "\<And>ty. is_runtime_type env' ty = is_runtime_type env ty"
      by (rule is_runtime_type_cong_env) (use env'_eq in simp_all)
    have wk_eq: "\<And>ty. is_well_kinded env' ty = is_well_kinded env ty"
      by (rule is_well_kinded_cong_env) (use env'_eq in simp_all)
    show ?thesis
      using state_env tyargs''_eq env'_eq rt_eq wk_eq
      unfolding state_matches_env_def ty_args_well_formed_def by simp
  qed
  ultimately show ?thesis
    unfolding state_matches_env_def by auto
qed

(* Add a ref binding: state matches env with an additional IS_Refs entry pointing
   to an existing store slot. The store is unchanged, so storeTyping is unchanged
   as well. The new env has the ref's name bound in TE_LocalVars (to the type
   reached by the path) and removed from TE_GhostLocals.

   Unlike Var, a Ref binding does not make the name const — it is writable through
   the reference. TE_ConstLocals is therefore unchanged. *)
lemma state_matches_env_add_ref:
  assumes state_env: "state_matches_env state env storeTyping"
    and addr_valid: "addr < length (IS_Store state)"
    and path_ty: "type_at_path env (storeTyping ! addr) path
                    = Some (apply_subst (IS_TyArgs state) refTy)"
    and state'_eq: "state' = state \<lparr> IS_Locals := fmdrop var (IS_Locals state),
                                       IS_Refs := fmupd var (addr, path) (IS_Refs state),
                                       IS_ConstLocals := fminus (IS_ConstLocals state) {|var|} \<rparr>"
    and env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd var refTy (TE_LocalVars env),
                                TE_GhostLocals := fminus (TE_GhostLocals env) {|var|},
                                TE_ConstLocals := fminus (TE_ConstLocals env) {|var|} \<rparr>"
    and var_fresh: "fmlookup (TE_LocalVars env) var = None"
    and var_not_ghost: "var |\<notin>| TE_GhostLocals env"
  shows "state_matches_env state' env' storeTyping"
proof -
  have store_eq: "IS_Store state' = IS_Store state"
    using state'_eq by simp
  have locals_eq: "IS_Locals state' = fmdrop var (IS_Locals state)"
    using state'_eq by simp
  have refs_eq: "IS_Refs state' = fmupd var (addr, path) (IS_Refs state)"
    using state'_eq by simp
  have globals_eq: "IS_Globals state' = IS_Globals state"
    using state'_eq by simp
  have funs_eq: "IS_Functions state' = IS_Functions state"
    using state'_eq by simp
  have consts_eq: "IS_ConstLocals state' = fminus (IS_ConstLocals state) {|var|}"
    using state'_eq by simp
  have tyargs_eq [simp]: "IS_TyArgs state' = IS_TyArgs state"
    using state'_eq by simp

  have env'_fields: "TE_DataCtors env' = TE_DataCtors env"
                    "TE_Datatypes env' = TE_Datatypes env"
                    "TE_TypeVars env' = TE_TypeVars env"
                    "TE_GhostDatatypes env' = TE_GhostDatatypes env"
                    "TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env"
    using env'_eq by simp_all
  have vht_eq: "\<And>v t. value_has_type env' v t = value_has_type env v t"
    using value_has_type_cong_env[OF env'_fields] .
  have tap_eq: "\<And>t p. type_at_path env t p = type_at_path env' t p"
    using type_at_path_cong_env[OF env'_fields(1)] .

  from state_env have
    lv_src: "local_vars_exist_in_state state env storeTyping" and
    gv_src: "global_vars_exist_in_state state env" and
    no_lv_src: "no_extra_local_vars state env" and
    no_gv_src: "no_extra_global_vars state env" and
    fes_src: "funs_exist_in_state state env" and
    no_fun_src: "no_extra_funs state env" and
    nc_src: "non_consts_in_locals_or_refs state env" and
    cn_src: "const_locals_match state env" and
    swt_src: "store_well_typed state env storeTyping"
    unfolding state_matches_env_def by blast+

  \<comment> \<open>1. local_vars_exist_in_state. \<close>
  have lv_tgt: "local_vars_exist_in_state state' env' storeTyping"
    unfolding local_vars_exist_in_state_def
  proof (intro allI impI, elim conjE)
    fix name ty
    assume lookup: "fmlookup (TE_LocalVars env') name = Some ty"
      and not_ghost: "name |\<notin>| TE_GhostLocals env'"
    show "local_var_in_state_with_type state' env' storeTyping name ty"
    proof (cases "name = var")
      case True
      from lookup env'_eq True have ty_eq: "ty = refTy" by simp
      \<comment> \<open>var was not previously a local, so no_extra_local_vars gives us that
          neither IS_Locals nor IS_Refs had an entry for var. In state', we added
          (addr, path) to IS_Refs, so IS_Locals state' var = None still. \<close>
      from var_fresh var_not_ghost no_lv_src have
        lk_none_locals: "fmlookup (IS_Locals state) var = None" and
        lk_none_refs: "fmlookup (IS_Refs state) var = None"
        unfolding no_extra_local_vars_def by blast+
      have lk_state'_locals: "fmlookup (IS_Locals state') var = None"
        using lk_none_locals locals_eq by simp
      have lk_state'_refs: "fmlookup (IS_Refs state') var = Some (addr, path)"
        using refs_eq by simp
      have addr_valid': "addr < length (IS_Store state')"
        using addr_valid store_eq by simp
      have path_ty': "type_at_path env' (storeTyping ! addr) path
                        = Some (apply_subst (IS_TyArgs state') refTy)"
        using path_ty tap_eq by simp
      show ?thesis
        using True ty_eq lk_state'_locals lk_state'_refs addr_valid' path_ty'
        unfolding local_var_in_state_with_type_def by simp
    next
      case False
      from lookup env'_eq False have "fmlookup (TE_LocalVars env) name = Some ty" by simp
      moreover from not_ghost env'_eq False have "name |\<notin>| TE_GhostLocals env" by auto
      ultimately have old:
        "local_var_in_state_with_type state env storeTyping name ty"
        using lv_src unfolding local_vars_exist_in_state_def by blast
      from False locals_eq refs_eq have
        lk_locals: "fmlookup (IS_Locals state') name = fmlookup (IS_Locals state) name" and
        lk_refs: "fmlookup (IS_Refs state') name = fmlookup (IS_Refs state) name"
        by simp_all
      show ?thesis
        using old lk_locals lk_refs store_eq tap_eq tyargs_eq
        unfolding local_var_in_state_with_type_def Let_def
        by (auto split: option.splits)
    qed
  qed

  \<comment> \<open>2. global_vars_exist_in_state. \<close>
  have gv_tgt: "global_vars_exist_in_state state' env'"
    unfolding global_vars_exist_in_state_def
  proof (intro allI impI, elim conjE)
    fix name ty
    assume "fmlookup (TE_GlobalVars env') name = Some ty"
       and "name |\<notin>| TE_GhostGlobals env'"
    hence "fmlookup (TE_GlobalVars env) name = Some ty"
      and "name |\<notin>| TE_GhostGlobals env"
      by (simp_all add: env'_eq)
    with gv_src have "global_var_in_state_with_type state env name ty"
      unfolding global_vars_exist_in_state_def by blast
    thus "global_var_in_state_with_type state' env' name ty"
      using globals_eq vht_eq
      unfolding global_var_in_state_with_type_def
      by (auto split: option.splits)
  qed

  \<comment> \<open>3. no_extra_local_vars. \<close>
  have no_lv_tgt: "no_extra_local_vars state' env'"
    unfolding no_extra_local_vars_def
  proof (intro allI impI)
    fix name
    assume ante: "fmlookup (TE_LocalVars env') name = None \<or> name |\<in>| TE_GhostLocals env'"
    show "fmlookup (IS_Locals state') name = None \<and>
          fmlookup (IS_Refs state') name = None"
    proof (cases "name = var")
      case True
      with env'_eq have "fmlookup (TE_LocalVars env') name = Some refTy" by simp
      with ante True env'_eq have "var |\<in>| TE_GhostLocals env'" by simp
      hence False using env'_eq by simp
      thus ?thesis ..
    next
      case False
      with env'_eq have tv_eq: "fmlookup (TE_LocalVars env') name = fmlookup (TE_LocalVars env) name"
        by simp
      with env'_eq False have gv_iff: "name |\<in>| TE_GhostLocals env' \<longleftrightarrow> name |\<in>| TE_GhostLocals env"
        by auto
      from ante tv_eq gv_iff
      have "fmlookup (TE_LocalVars env) name = None \<or> name |\<in>| TE_GhostLocals env" by simp
      with no_lv_src have
        "fmlookup (IS_Locals state) name = None \<and> fmlookup (IS_Refs state) name = None"
        unfolding no_extra_local_vars_def by blast
      thus ?thesis using False locals_eq refs_eq by simp
    qed
  qed

  \<comment> \<open>4. no_extra_global_vars. \<close>
  have no_gv_tgt: "no_extra_global_vars state' env'"
    using no_gv_src env'_eq globals_eq
    unfolding no_extra_global_vars_def by simp

  \<comment> \<open>5. funs_exist_in_state. \<close>
  have fes_tgt: "funs_exist_in_state state' env'"
  proof -
    have fi_cong: "\<And>info ifn. fun_info_matches_interp_fun env' info ifn
                             = fun_info_matches_interp_fun env info ifn"
      by (rule fun_info_matches_interp_fun_cong_env) (use env'_eq in simp_all)
    show ?thesis
      unfolding funs_exist_in_state_def
    proof (intro allI impI, elim conjE)
      fix name info
      assume lookup: "fmlookup (TE_Functions env') name = Some info"
         and nghost: "FI_Ghost info = NotGhost"
      from lookup env'_eq have "fmlookup (TE_Functions env) name = Some info" by simp
      with nghost fes_src have
        "case fmlookup (IS_Functions state) name of None \<Rightarrow> False
         | Some interpFun \<Rightarrow> fun_info_matches_interp_fun env info interpFun"
        unfolding funs_exist_in_state_def by blast
      thus "case fmlookup (IS_Functions state') name of None \<Rightarrow> False
            | Some interpFun \<Rightarrow> fun_info_matches_interp_fun env' info interpFun"
        using funs_eq fi_cong by (auto split: option.splits)
    qed
  qed

  \<comment> \<open>6. no_extra_funs. \<close>
  have no_fun_tgt: "no_extra_funs state' env'"
    using no_fun_src env'_eq funs_eq
    unfolding no_extra_funs_def by simp

  \<comment> \<open>7. non_consts_in_locals_or_refs. \<close>
  have nc_tgt: "non_consts_in_locals_or_refs state' env'"
    unfolding non_consts_in_locals_or_refs_def
  proof (intro allI impI, elim conjE)
    fix name
    assume tv: "fmlookup (TE_LocalVars env') name \<noteq> None"
       and ng: "name |\<notin>| TE_GhostLocals env'"
       and nc: "name |\<notin>| TE_ConstLocals env'"
    show "fmlookup (IS_Locals state') name \<noteq> None \<or>
          fmlookup (IS_Refs state') name \<noteq> None"
    proof (cases "name = var")
      case True
      with refs_eq show ?thesis by simp
    next
      case False
      with env'_eq have tv2: "fmlookup (TE_LocalVars env) name \<noteq> None"
        using tv by simp
      from False env'_eq ng have ng2: "name |\<notin>| TE_GhostLocals env" by auto
      from env'_eq nc False have nc2: "name |\<notin>| TE_ConstLocals env" by auto
      from tv2 ng2 nc2 nc_src have
        "fmlookup (IS_Locals state) name \<noteq> None \<or> fmlookup (IS_Refs state) name \<noteq> None"
        unfolding non_consts_in_locals_or_refs_def by blast
      thus ?thesis using False locals_eq refs_eq by simp
    qed
  qed

  \<comment> \<open>8. const_locals_match. \<close>
  have cn_tgt: "const_locals_match state' env'"
    using cn_src env'_eq consts_eq
    unfolding const_locals_match_def by auto

  \<comment> \<open>9. store_well_typed. \<close>
  have swt_tgt: "store_well_typed state' env' storeTyping"
    using swt_src store_eq vht_eq
    unfolding store_well_typed_def by simp

  have ta_tgt: "ty_args_well_formed state' env'"
  proof -
    have rt_eq: "\<And>ty. is_runtime_type env' ty = is_runtime_type env ty"
      by (rule is_runtime_type_cong_env) (use env'_eq in simp_all)
    have wk_eq: "\<And>ty. is_well_kinded env' ty = is_well_kinded env ty"
      by (rule is_well_kinded_cong_env) (use env'_eq in simp_all)
    show ?thesis
      using state_env tyargs_eq env'_eq rt_eq wk_eq
      unfolding state_matches_env_def ty_args_well_formed_def by simp
  qed

  show ?thesis
    unfolding state_matches_env_def
    using lv_tgt gv_tgt no_lv_tgt no_gv_tgt fes_tgt no_fun_tgt nc_tgt cn_tgt swt_tgt ta_tgt
    by blast
qed

(* Const specialization: variable is added to ConstNames (used for let-bindings) *)
corollary state_matches_env_add_const_local:
  assumes state_env: "state_matches_env state env storeTyping"
    and val_typed: "value_has_type env val (apply_subst (IS_TyArgs state) rhsTy)"
    and state'_eq: "(state', addr) = alloc_store state val"
    and state''_eq: "state'' = state' \<lparr> IS_Locals := fmupd var addr (IS_Locals state'),
                                        IS_Refs := fmdrop var (IS_Refs state'),
                                        IS_ConstLocals := finsert var (IS_ConstLocals state') \<rparr>"
    and env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                               TE_GhostLocals := fminus (TE_GhostLocals env) {|var|},
                               TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
  shows "state_matches_env state'' env' (storeTyping @ [apply_subst (IS_TyArgs state) rhsTy])"
proof -
  from state'_eq have ic_eq: "IS_ConstLocals state' = IS_ConstLocals state" by auto
  have icn_eq: "IS_ConstLocals state = fminus (TE_ConstLocals env) (TE_GhostLocals env)"
    using state_env unfolding state_matches_env_def const_locals_match_def by simp
  have "IS_ConstLocals state''
        = finsert var (fminus (TE_ConstLocals env) (TE_GhostLocals env))"
    using state''_eq ic_eq icn_eq by simp
  hence cn: "const_locals_match state'' env'"
    using env'_eq unfolding const_locals_match_def by auto
  have cn_oth: "\<And>name. name \<noteq> var \<Longrightarrow>
      (name |\<in>| TE_ConstLocals env' \<longleftrightarrow> name |\<in>| TE_ConstLocals env)"
    using env'_eq by auto
  show ?thesis
    using state_matches_env_add_local[OF state_env val_typed state'_eq state''_eq env'_eq
                                        cn cn_oth] .
qed

(* Non-const specialization: var is removed from ConstNames (used for VarDecl Var) *)
corollary state_matches_env_add_nonconst_local:
  assumes state_env: "state_matches_env state env storeTyping"
    and val_typed: "value_has_type env val (apply_subst (IS_TyArgs state) rhsTy)"
    and state'_eq: "(state', addr) = alloc_store state val"
    and state''_eq: "state'' = state' \<lparr> IS_Locals := fmupd var addr (IS_Locals state'),
                                         IS_Refs := fmdrop var (IS_Refs state'),
                                         IS_ConstLocals := fminus (IS_ConstLocals state') {|var|} \<rparr>"
    and env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                               TE_GhostLocals := fminus (TE_GhostLocals env) {|var|},
                               TE_ConstLocals := fminus (TE_ConstLocals env) {|var|} \<rparr>"
  shows "state_matches_env state'' env' (storeTyping @ [apply_subst (IS_TyArgs state) rhsTy])"
proof -
  from state'_eq have ic_eq: "IS_ConstLocals state' = IS_ConstLocals state" by auto
  have icn_eq: "IS_ConstLocals state = fminus (TE_ConstLocals env) (TE_GhostLocals env)"
    using state_env unfolding state_matches_env_def const_locals_match_def by simp
  have "IS_ConstLocals state''
        = fminus (fminus (TE_ConstLocals env) (TE_GhostLocals env)) {|var|}"
    using state''_eq ic_eq icn_eq by simp
  hence cn: "const_locals_match state'' env'"
    using env'_eq unfolding const_locals_match_def by auto
  have cn_oth: "\<And>name. name \<noteq> var \<Longrightarrow>
      (name |\<in>| TE_ConstLocals env' \<longleftrightarrow> name |\<in>| TE_ConstLocals env)"
    using env'_eq by auto
  show ?thesis
    using state_matches_env_add_local[OF state_env val_typed state'_eq state''_eq env'_eq
                                        cn cn_oth] .
qed


(* If two association lists are related by list_all2 with matching keys,
   then map_of on the first succeeds whenever map_of on the second does *)
lemma map_of_list_all2:
  assumes "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t) xs ys"
    and "map_of ys name = Some t"
  shows "\<exists>v. map_of xs name = Some v \<and> P v t"
using assms proof (induction xs ys rule: list_all2_induct)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  obtain n1 v where x_eq: "x = (n1, v)" by (cases x) auto
  obtain n2 t' where y_eq: "y = (n2, t')" by (cases y) auto
  from Cons.hyps x_eq y_eq have name_eq: "n1 = n2" and rel: "P v t'" by auto
  show ?case
  proof (cases "name = n2")
    case True
    from Cons.prems y_eq True have "t = t'" by simp
    with name_eq True x_eq rel show ?thesis by auto
  next
    case False
    from Cons.prems y_eq False have "map_of ys name = Some t" by simp
    from Cons.IH[OF this] obtain v' where "map_of xs name = Some v'" "P v' t" by auto
    with name_eq False x_eq show ?thesis by auto
  qed
qed

(* If all values have type u64, interpret_index_vals succeeds *)
lemma interpret_index_vals_u64:
  assumes "list_all2 (value_has_type env) vals (replicate n (CoreTy_FiniteInt Unsigned IntBits_64))"
  shows "\<exists>indices. interpret_index_vals vals = Inr indices"
using assms proof (induction vals arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons v vs)
  from Cons.prems obtain n' where n_eq: "n = Suc n'" and
    v_typed: "value_has_type env v (CoreTy_FiniteInt Unsigned IntBits_64)" and
    vs_typed: "list_all2 (value_has_type env) vs (replicate n' (CoreTy_FiniteInt Unsigned IntBits_64))"
    by (cases n) auto
  from value_has_type_FiniteInt[OF v_typed] obtain i where
    v_eq: "v = CV_FiniteInt Unsigned IntBits_64 i" by auto
  from Cons.IH[OF vs_typed] obtain rest_indices where
    rest_eq: "interpret_index_vals vs = Inr rest_indices" by auto
  show ?case using v_eq rest_eq by simp
qed

(* Path append: following a concatenated path is the same as following the first
   part and then following the second part on the result *)
lemma get_value_at_path_append:
  "get_value_at_path root (path @ rest) =
    (case get_value_at_path root path of
      Inr v \<Rightarrow> get_value_at_path v rest
    | Inl err \<Rightarrow> Inl err)"
proof (induction path arbitrary: root)
  case Nil
  then show ?case by simp
next
  case (Cons step path)
  show ?case
  proof (cases root)
    case (CV_Record flds)
    then show ?thesis
    proof (cases step)
      case (LVPath_RecordProj fldName)
      then show ?thesis using CV_Record Cons.IH
        by (simp split: option.splits)
    next
      case (LVPath_VariantProj x2)
      then show ?thesis using CV_Record by simp
    next
      case (LVPath_ArrayProj x3)
      then show ?thesis using CV_Record by simp
    qed
  next
    case (CV_Variant ctor payload)
    then show ?thesis
    proof (cases step)
      case (LVPath_RecordProj x1)
      then show ?thesis using CV_Variant by simp
    next
      case (LVPath_VariantProj expectedCtor)
      then show ?thesis using CV_Variant Cons.IH by simp
    next
      case (LVPath_ArrayProj x3)
      then show ?thesis using CV_Variant by simp
    qed
  next
    case (CV_Array sizes elementMap)
    then show ?thesis
    proof (cases step)
      case (LVPath_RecordProj x1)
      then show ?thesis using CV_Array by simp
    next
      case (LVPath_VariantProj x2)
      then show ?thesis using CV_Array by simp
    next
      case (LVPath_ArrayProj indices)
      then show ?thesis using CV_Array Cons.IH
        by (simp split: option.splits)
    qed
  next
    case (CV_Bool x)
    then show ?thesis by (cases step) auto
  next
    case (CV_FiniteInt x1 x2 x3)
    then show ?thesis by (cases step) auto
  qed
qed

(* If flds and fieldTypes are related by list_all2 with name equality,
   then map_of lookups agree and predicates transfer. *)
lemma list_all2_map_of_transfer:
  assumes "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t) flds fieldTypes"
    and "map_of flds k = Some v"
  shows "\<exists>t. map_of fieldTypes k = Some t \<and> P v t"
using assms proof (induction flds arbitrary: fieldTypes)
  case Nil
  then show ?case by simp
next
  case (Cons entry flds)
  obtain k1 v1 where entry_eq: "entry = (k1, v1)" by (cases entry) auto
  from Cons.prems(1) obtain ft fieldTypes' where
    ft_eq: "fieldTypes = ft # fieldTypes'" and
    head_rel: "(\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t) entry ft" and
    tail_rel: "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t) flds fieldTypes'"
    by (cases fieldTypes) auto
  obtain k2 t2 where ft_pair: "ft = (k2, t2)" by (cases ft) auto
  from head_rel entry_eq ft_pair have k_eq: "k1 = k2" and pred: "P v1 t2" by auto
  show ?case
  proof (cases "k1 = k")
    case True
    with entry_eq Cons.prems(2) have "v = v1" by simp
    with True k_eq ft_eq ft_pair pred show ?thesis by simp
  next
    case False
    with entry_eq Cons.prems(2) have "map_of flds k = Some v" by simp
    from Cons.IH[OF tail_rel this] obtain t where
      "map_of fieldTypes' k = Some t" and "P v t" by auto
    with False k_eq ft_eq ft_pair show ?thesis by simp
  qed
qed

(* Reverse direction of list_all2_map_of_transfer: given a key present in the
   second list (fieldTypes), conclude it is also present in the first list (flds). *)
lemma list_all2_map_of_transfer_rev:
  assumes "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t) flds fieldTypes"
    and "map_of fieldTypes k = Some t"
  shows "\<exists>v. map_of flds k = Some v \<and> P v t"
using assms proof (induction flds arbitrary: fieldTypes)
  case Nil
  then show ?case by simp
next
  case (Cons entry flds)
  obtain k1 v1 where entry_eq: "entry = (k1, v1)" by (cases entry) auto
  from Cons.prems(1) obtain ft fieldTypes' where
    ft_eq: "fieldTypes = ft # fieldTypes'" and
    head_rel: "(\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t) entry ft" and
    tail_rel: "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t) flds fieldTypes'"
    by (cases fieldTypes) auto
  obtain k2 t2 where ft_pair: "ft = (k2, t2)" by (cases ft) auto
  from head_rel entry_eq ft_pair have k_eq: "k1 = k2" and pred: "P v1 t2" by auto
  show ?case
  proof (cases "k2 = k")
    case True
    with ft_eq ft_pair Cons.prems(2) have "t = t2" by simp
    with True k_eq entry_eq pred show ?thesis by simp
  next
    case False
    with ft_eq ft_pair Cons.prems(2) have "map_of fieldTypes' k = Some t" by simp
    from Cons.IH[OF tail_rel this] obtain v where
      "map_of flds k = Some v" and "P v t" by auto
    with False k_eq entry_eq show ?thesis by simp
  qed
qed

(* AList.update preserves list_all2 when the replacement value satisfies the
   same predicate as the original value at that key. *)
lemma alist_update_preserves_list_all2:
  assumes all2: "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t) flds fieldTypes"
    and lookup: "map_of flds field = Some oldVal"
    and new_pred: "\<And>t. map_of fieldTypes field = Some t \<Longrightarrow> P newVal t"
  shows "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t)
           (AList.update field newVal flds) fieldTypes"
using all2 lookup new_pred proof (induction flds arbitrary: fieldTypes)
  case Nil
  then show ?case by simp
next
  case (Cons entry flds)
  obtain k v where entry_eq: "entry = (k, v)" by (cases entry) auto
  from Cons.prems(1) obtain ft fieldTypes' where
    ft_eq: "fieldTypes = ft # fieldTypes'" and
    head_rel: "(\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t) entry ft" and
    tail_rel: "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t) flds fieldTypes'"
    by (cases fieldTypes) auto
  obtain kft tft where ft_pair: "ft = (kft, tft)" by (cases ft) auto
  from head_rel entry_eq ft_pair have k_eq: "k = kft" and old_P: "P v tft" by auto
  show ?case
  proof (cases "k = field")
    case True
    then have "AList.update field newVal (entry # flds) = (field, newVal) # flds"
      using entry_eq by simp
    moreover from True k_eq ft_pair have "map_of fieldTypes field = Some tft"
      using ft_eq by simp
    hence "P newVal tft" using Cons.prems(3) by simp
    ultimately show ?thesis using ft_eq ft_pair k_eq True tail_rel by force
  next
    case False
    then have "AList.update field newVal (entry # flds) =
               entry # AList.update field newVal flds"
      using entry_eq by simp
    moreover from False have lookup_tail: "map_of flds field = Some oldVal"
      using Cons.prems(2) entry_eq by simp
    have new_pred_tail: "\<And>t. map_of fieldTypes' field = Some t \<Longrightarrow> P newVal t"
      using Cons.prems(3) ft_eq False k_eq entry_eq ft_pair by simp
    from Cons.IH[OF tail_rel lookup_tail new_pred_tail] have
      "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t)
         (AList.update field newVal flds) fieldTypes'" .
    ultimately show ?thesis using ft_eq head_rel by simp
  qed
qed


(* update_value_at_path preserves value_has_type, provided the new value has
   the type that type_at_path computes for the given path.
   This is the key lemma for CoreStmt_Assign soundness. *)
lemma update_value_at_path_preserves_type:
  assumes typed: "value_has_type env oldVal ty"
    and update_ok: "update_value_at_path oldVal path newVal = Inr updatedVal"
    and path_ty: "type_at_path env ty path = Some pathTy"
    and new_typed: "value_has_type env newVal pathTy"
  shows "value_has_type env updatedVal ty"
using assms proof (induction path arbitrary: oldVal ty updatedVal)
  case Nil
  from Nil.prems(3) have "pathTy = ty" by simp
  with Nil.prems(2,4) show ?case by simp
next
  case (Cons step rest)
  then show ?case
  proof (cases oldVal)
    case (CV_Record flds)
    then show ?thesis
    proof (cases step)
      case (LVPath_RecordProj field)
      (* Extract record type *)
      from Cons.prems(1) CV_Record obtain fieldTypes where
        ty_eq: "ty = CoreTy_Record fieldTypes" and
        distinct_names: "distinct (map fst fieldTypes)" and
        all2: "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> value_has_type env v t) flds fieldTypes"
        by (cases ty) auto
      (* Extract field value and updated field value *)
      from Cons.prems(2) CV_Record LVPath_RecordProj obtain fieldVal updatedFieldVal where
        fld_lookup: "map_of flds field = Some fieldVal" and
        update_rest: "update_value_at_path fieldVal rest newVal = Inr updatedFieldVal" and
        updatedVal_eq: "updatedVal = CV_Record (AList.update field updatedFieldVal flds)"
        by (auto split: option.splits sum.splits)
      (* Get the field type *)
      from list_all2_map_of_transfer[OF all2 fld_lookup] obtain fieldTy where
        fld_ty_lookup: "map_of fieldTypes field = Some fieldTy" and
        fld_typed: "value_has_type env fieldVal fieldTy"
        by auto
      (* type_at_path descends into the field *)
      from Cons.prems(3) ty_eq LVPath_RecordProj fld_ty_lookup
      have path_ty_rest: "type_at_path env fieldTy rest = Some pathTy" by simp
      (* Apply IH *)
      have "value_has_type env updatedFieldVal fieldTy"
        using Cons.IH[OF fld_typed update_rest path_ty_rest Cons.prems(4)] .
      (* Use alist_update_preserves_list_all2 *)
      hence "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> value_has_type env v t)
               (AList.update field updatedFieldVal flds) fieldTypes"
        using alist_update_preserves_list_all2[OF all2 fld_lookup] fld_ty_lookup by auto
      then show ?thesis using updatedVal_eq ty_eq distinct_names by simp
    next
      case (LVPath_VariantProj x)
      with CV_Record Cons.prems show ?thesis by simp
    next
      case (LVPath_ArrayProj x)
      with CV_Record Cons.prems show ?thesis by simp
    qed
  next
    case (CV_Variant ctor payload)
    then show ?thesis
    proof (cases step)
      case (LVPath_RecordProj x)
      with CV_Variant Cons.prems show ?thesis by simp
    next
      case (LVPath_VariantProj expectedCtor)
      (* Extract variant type *)
      from Cons.prems(1) CV_Variant obtain dtName argTypes tyvars payloadTy where
        ty_eq: "ty = CoreTy_Datatype dtName argTypes" and
        ctor_lookup: "fmlookup (TE_DataCtors env) ctor = Some (dtName, tyvars, payloadTy)" and
        len_eq: "length tyvars = length argTypes" and
        args_wk: "list_all (is_well_kinded env) argTypes" and
        args_rt: "list_all (is_runtime_type env) argTypes" and
        args_ground: "list_all (\<lambda>a. type_tyvars a = {}) argTypes" and
        dt_nonghost: "dtName |\<notin>| TE_GhostDatatypes env" and
        payload_typed: "value_has_type env payload
            (apply_subst (fmap_of_list (zip tyvars argTypes)) payloadTy)"
        by (cases ty) (auto split: option.splits prod.splits)
      let ?payloadTy = "apply_subst (fmap_of_list (zip tyvars argTypes)) payloadTy"
      (* Extract from update_value_at_path: ctor must match *)
      from Cons.prems(2) CV_Variant LVPath_VariantProj obtain updatedPayload where
        ctor_match: "ctor = expectedCtor" and
        update_rest: "update_value_at_path payload rest newVal = Inr updatedPayload" and
        updatedVal_eq: "updatedVal = CV_Variant ctor updatedPayload"
        by (auto split: if_splits sum.splits)
      (* type_at_path descends into the payload *)
      from Cons.prems(3) ty_eq LVPath_VariantProj ctor_match ctor_lookup
      have path_ty_rest: "type_at_path env ?payloadTy rest = Some pathTy" by simp
      (* Apply IH *)
      have "value_has_type env updatedPayload ?payloadTy"
        using Cons.IH[OF payload_typed update_rest path_ty_rest Cons.prems(4)] .
      then show ?thesis using updatedVal_eq ty_eq ctor_lookup len_eq args_wk args_rt
          args_ground dt_nonghost by simp
    next
      case (LVPath_ArrayProj x)
      with CV_Variant Cons.prems show ?thesis by simp
    qed
  next
    case (CV_Array sizes elementMap)
    then show ?thesis
    proof (cases step)
      case (LVPath_RecordProj x)
      with CV_Array Cons.prems show ?thesis by simp
    next
      case (LVPath_VariantProj x)
      with CV_Array Cons.prems show ?thesis by simp
    next
      case (LVPath_ArrayProj indices)
      (* Extract array type *)
      from Cons.prems(1) CV_Array obtain elemTy dims where
        ty_eq: "ty = CoreTy_Array elemTy dims" and
        elem_wk: "is_well_kinded env elemTy" and
        elem_rt: "is_runtime_type env elemTy" and
        elem_ground: "type_tyvars elemTy = {}" and
        elems_typed: "\<forall>idx val. fmlookup elementMap idx = Some val \<longrightarrow>
                        value_has_type env val elemTy" and
        dims_wk: "array_dims_well_kinded dims" and
        sizes_match: "fmap_matches_sizes sizes elementMap" and
        dims_match: "sizes_match_dims sizes dims"
        by (cases ty) auto
      (* Extract from update_value_at_path: index lookup succeeds *)
      from Cons.prems(2) CV_Array LVPath_ArrayProj obtain elemVal updatedElem where
        elem_lookup: "fmlookup elementMap indices = Some elemVal" and
        update_rest: "update_value_at_path elemVal rest newVal = Inr updatedElem" and
        updatedVal_eq: "updatedVal = CV_Array sizes (fmupd indices updatedElem elementMap)"
        by (auto split: option.splits sum.splits)
      (* The old element has type elemTy *)
      from elems_typed elem_lookup have elem_typed: "value_has_type env elemVal elemTy" by simp
      (* type_at_path descends into the element type *)
      from Cons.prems(3) ty_eq LVPath_ArrayProj
      have path_ty_rest: "type_at_path env elemTy rest = Some pathTy" by simp
      (* Apply IH *)
      have updated_elem_typed: "value_has_type env updatedElem elemTy"
        using Cons.IH[OF elem_typed update_rest path_ty_rest Cons.prems(4)] .
      (* All elements of the updated map have type elemTy *)
      have "\<forall>idx val. fmlookup (fmupd indices updatedElem elementMap) idx = Some val \<longrightarrow>
              value_has_type env val elemTy"
      proof (intro allI impI)
        fix idx val
        assume "fmlookup (fmupd indices updatedElem elementMap) idx = Some val"
        then show "value_has_type env val elemTy"
        proof (cases "idx = indices")
          case True
          then show ?thesis
            using \<open>fmlookup (fmupd indices updatedElem elementMap) idx = Some val\<close>
                  updated_elem_typed by simp
        next
          case False
          then show ?thesis
            using \<open>fmlookup (fmupd indices updatedElem elementMap) idx = Some val\<close>
                  elems_typed by simp
        qed
      qed
      (* fmap_matches_sizes is preserved by fmupd at an existing key *)
      moreover have "fmap_matches_sizes sizes (fmupd indices updatedElem elementMap)"
        using sizes_match elem_lookup
        unfolding fmap_matches_sizes_def by force
      ultimately show ?thesis using updatedVal_eq ty_eq elem_wk elem_rt elem_ground
          dims_wk dims_match
        by simp
    qed
  next
    case (CV_Bool x)
    with Cons.prems show ?thesis by (cases step) auto
  next
    case (CV_FiniteInt x1 x2 x3)
    with Cons.prems show ?thesis by (cases step) auto
  qed
qed

(* Bridging lemma: if get_value_at_path succeeds on a well-typed value, the result is
   well-typed and its type is computable by type_at_path. *)
lemma get_value_at_path_type:
  assumes "value_has_type env root ty"
    and "get_value_at_path root path = Inr v"
  shows "\<exists>pathTy. type_at_path env ty path = Some pathTy \<and> value_has_type env v pathTy"
using assms proof (induction path arbitrary: root ty)
  case Nil
  then show ?case by simp
next
  case (Cons step rest)
  show ?case
  proof (cases root)
    case (CV_Record flds)
    show ?thesis proof (cases step)
      case (LVPath_RecordProj field)
      from Cons.prems(1) CV_Record obtain fieldTypes where
        ty_eq: "ty = CoreTy_Record fieldTypes" and
        distinct_names: "distinct (map fst fieldTypes)" and
        all2: "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> value_has_type env v t) flds fieldTypes"
        by (cases ty) auto
      from Cons.prems(2) CV_Record LVPath_RecordProj obtain fieldVal where
        fld_lookup: "map_of flds field = Some fieldVal" and
        get_rest: "get_value_at_path fieldVal rest = Inr v"
        by (auto split: option.splits)
      from list_all2_map_of_transfer[OF all2 fld_lookup] obtain fieldTy where
        fty_lookup: "map_of fieldTypes field = Some fieldTy" and
        fld_typed: "value_has_type env fieldVal fieldTy"
        by auto
      from Cons.IH[OF fld_typed get_rest] obtain pathTy where
        rest_ty: "type_at_path env fieldTy rest = Some pathTy" and
        v_typed: "value_has_type env v pathTy"
        by auto
      have "type_at_path env ty (step # rest) = Some pathTy"
        using ty_eq LVPath_RecordProj fty_lookup rest_ty by simp
      with v_typed show ?thesis by blast
    next
      case (LVPath_VariantProj x)
      with CV_Record Cons.prems show ?thesis by simp
    next
      case (LVPath_ArrayProj x)
      with CV_Record Cons.prems show ?thesis by simp
    qed
  next
    case (CV_Variant ctor payload)
    show ?thesis proof (cases step)
      case (LVPath_RecordProj x)
      with CV_Variant Cons.prems show ?thesis by simp
    next
      case (LVPath_VariantProj expectedCtor)
      from Cons.prems(1) CV_Variant obtain dtName argTypes tyvars payloadTy where
        ty_eq: "ty = CoreTy_Datatype dtName argTypes" and
        ctor_lookup: "fmlookup (TE_DataCtors env) ctor = Some (dtName, tyvars, payloadTy)" and
        payload_typed: "value_has_type env payload
                          (apply_subst (fmap_of_list (zip tyvars argTypes)) payloadTy)"
        by (cases ty) (auto split: option.splits)
      from Cons.prems(2) CV_Variant LVPath_VariantProj have ctor_match: "ctor = expectedCtor"
        and get_rest: "get_value_at_path payload rest = Inr v"
        by (auto split: if_splits)
      let ?subPayloadTy = "apply_subst (fmap_of_list (zip tyvars argTypes)) payloadTy"
      from Cons.IH[OF payload_typed get_rest] obtain pathTy where
        rest_ty: "type_at_path env ?subPayloadTy rest = Some pathTy" and
        v_typed: "value_has_type env v pathTy"
        by auto
      have "type_at_path env ty (step # rest) = Some pathTy"
        using ty_eq LVPath_VariantProj ctor_match ctor_lookup rest_ty by simp
      with v_typed show ?thesis by blast
    next
      case (LVPath_ArrayProj x)
      with CV_Variant Cons.prems show ?thesis by simp
    qed
  next
    case (CV_Array sizes elementMap)
    show ?thesis proof (cases step)
      case (LVPath_RecordProj x)
      with CV_Array Cons.prems show ?thesis by simp
    next
      case (LVPath_VariantProj x)
      with CV_Array Cons.prems show ?thesis by simp
    next
      case (LVPath_ArrayProj indices)
      from Cons.prems(1) CV_Array obtain elemTy dims where
        ty_eq: "ty = CoreTy_Array elemTy dims" and
        elems_typed: "\<forall>idx val. fmlookup elementMap idx = Some val \<longrightarrow>
                        value_has_type env val elemTy"
        by (cases ty) auto
      from Cons.prems(2) CV_Array LVPath_ArrayProj obtain elemVal where
        elem_lookup: "fmlookup elementMap indices = Some elemVal" and
        get_rest: "get_value_at_path elemVal rest = Inr v"
        by (auto split: option.splits)
      from elems_typed elem_lookup have elem_typed: "value_has_type env elemVal elemTy" by simp
      from Cons.IH[OF elem_typed get_rest] obtain pathTy where
        rest_ty: "type_at_path env elemTy rest = Some pathTy" and
        v_typed: "value_has_type env v pathTy"
        by auto
      have "type_at_path env ty (step # rest) = Some pathTy"
        using ty_eq LVPath_ArrayProj rest_ty by simp
      with v_typed show ?thesis by blast
    qed
  next
    case (CV_Bool x)
    with Cons.prems show ?thesis by (cases step) auto
  next
    case (CV_FiniteInt x1 x2 x3)
    with Cons.prems show ?thesis by (cases step) auto
  qed
qed


(* If a path is structurally compatible with a typed value (type_at_path succeeds),
   then get_value_at_path can only fail with RuntimeError, never TypeError.
   TypeError means the path step doesn't match the value's shape at all (e.g. record
   projection on a non-record), but type_at_path succeeding rules that out. *)
lemma get_value_at_path_error_is_runtime:
  assumes typed: "value_has_type env val slotTy"
    and path_ty: "type_at_path env slotTy path = Some ty"
    and fails: "get_value_at_path val path = Inl err"
  shows "err = RuntimeError"
using assms proof (induction path arbitrary: val slotTy)
  case Nil
  then show ?case by simp
next
  case (Cons step rest)
  show ?case
  proof (cases val)
    case (CV_Record flds)
    from Cons.prems(1) CV_Record obtain fieldTypes where
      slotTy_eq: "slotTy = CoreTy_Record fieldTypes" and
      all2: "list_all2 (\<lambda>(n1,v) (n2,t). n1=n2 \<and> value_has_type env v t) flds fieldTypes"
      by (cases slotTy) auto
    show ?thesis proof (cases step)
      case (LVPath_RecordProj field)
      from Cons.prems(2) slotTy_eq LVPath_RecordProj obtain fieldTy where
        fty_lookup: "map_of fieldTypes field = Some fieldTy" and
        rest_ty: "type_at_path env fieldTy rest = Some ty"
        by (auto split: option.splits)
      \<comment> \<open>map_of fieldTypes succeeds, so map_of flds must also succeed (reverse direction).\<close>
      from list_all2_map_of_transfer_rev[OF all2 fty_lookup]
      obtain fieldVal where fld_lookup: "map_of flds field = Some fieldVal"
        and fv_typed': "value_has_type env fieldVal fieldTy"
        by auto
      from Cons.prems(3) CV_Record LVPath_RecordProj fld_lookup
      have "get_value_at_path fieldVal rest = Inl err" by (auto split: option.splits)
      from Cons.IH[OF fv_typed' rest_ty this] show ?thesis .
    next
      case (LVPath_VariantProj x) with CV_Record Cons.prems slotTy_eq show ?thesis by simp
    next
      case (LVPath_ArrayProj x) with CV_Record Cons.prems slotTy_eq show ?thesis by simp
    qed
  next
    case (CV_Variant ctor payload)
    from Cons.prems(1) CV_Variant obtain dtName argTypes tyvars payloadTy where
      slotTy_eq: "slotTy = CoreTy_Datatype dtName argTypes" and
      ctor_lookup: "fmlookup (TE_DataCtors env) ctor = Some (dtName, tyvars, payloadTy)" and
      payload_typed: "value_has_type env payload
                        (apply_subst (fmap_of_list (zip tyvars argTypes)) payloadTy)"
      by (cases slotTy) (auto split: option.splits)
    show ?thesis proof (cases step)
      case (LVPath_RecordProj x) with CV_Variant Cons.prems slotTy_eq show ?thesis by simp
    next
      case (LVPath_VariantProj expectedCtor)
      show ?thesis
      proof (cases "ctor = expectedCtor")
        case True
        \<comment> \<open>Ctor matches: type_at_path uses ctor_lookup, so we can extract rest_ty.\<close>
        from Cons.prems(2) slotTy_eq LVPath_VariantProj True ctor_lookup obtain
          rest_ty: "type_at_path env
                      (apply_subst (fmap_of_list (zip tyvars argTypes)) payloadTy) rest
                    = Some ty"
          by (auto split: if_splits)
        from Cons.prems(3) CV_Variant LVPath_VariantProj True
        have "get_value_at_path payload rest = Inl err" by simp
        from Cons.IH[OF payload_typed rest_ty this] show ?thesis .
      next
        case False
        \<comment> \<open>Ctor mismatch: get_value_at_path returns RuntimeError directly.\<close>
        from Cons.prems(3) CV_Variant LVPath_VariantProj False
        have "err = RuntimeError" by simp
        then show ?thesis .
      qed
    next
      case (LVPath_ArrayProj x) with CV_Variant Cons.prems slotTy_eq show ?thesis by simp
    qed
  next
    case (CV_Array sizes elementMap)
    from Cons.prems(1) CV_Array obtain elemTy dims where
      slotTy_eq: "slotTy = CoreTy_Array elemTy dims" and
      elems_typed: "\<forall>idx v. fmlookup elementMap idx = Some v \<longrightarrow> value_has_type env v elemTy"
      by (cases slotTy) auto
    show ?thesis proof (cases step)
      case (LVPath_RecordProj x) with CV_Array Cons.prems slotTy_eq show ?thesis by simp
    next
      case (LVPath_VariantProj x) with CV_Array Cons.prems slotTy_eq show ?thesis by simp
    next
      case (LVPath_ArrayProj indices)
      from Cons.prems(2) slotTy_eq LVPath_ArrayProj
      have rest_ty: "type_at_path env elemTy rest = Some ty" by simp
      show ?thesis
      proof (cases "fmlookup elementMap indices")
        case None
        \<comment> \<open>Array index OOB: RuntimeError directly.\<close>
        from Cons.prems(3) CV_Array LVPath_ArrayProj None
        have "err = RuntimeError" by simp
        then show ?thesis .
      next
        case (Some elemVal)
        from elems_typed Some have "value_has_type env elemVal elemTy" by simp
        from Cons.prems(3) CV_Array LVPath_ArrayProj Some
        have "get_value_at_path elemVal rest = Inl err" by (auto split: option.splits)
        from Cons.IH[OF \<open>value_has_type env elemVal elemTy\<close> rest_ty this] show ?thesis .
      qed
    qed
  next
    case (CV_Bool x) with Cons.prems show ?thesis by (cases slotTy) auto
  next
    case (CV_FiniteInt x1 x2 x3) with Cons.prems show ?thesis by (cases slotTy) auto
  qed
qed


(* If the path is structurally compatible with a typed value (type_at_path succeeds),
   then update_value_at_path can only fail with RuntimeError, never TypeError.
   Dual to get_value_at_path_error_is_runtime. *)
lemma update_value_at_path_error_is_runtime:
  assumes typed: "value_has_type env val slotTy"
    and path_ty: "type_at_path env slotTy path = Some ty"
    and fails: "update_value_at_path val path newVal = Inl err"
  shows "err = RuntimeError"
using assms proof (induction path arbitrary: val slotTy)
  case Nil
  then show ?case by simp
next
  case (Cons step rest)
  show ?case
  proof (cases val)
    case (CV_Record flds)
    from Cons.prems(1) CV_Record obtain fieldTypes where
      slotTy_eq: "slotTy = CoreTy_Record fieldTypes" and
      all2: "list_all2 (\<lambda>(n1,v) (n2,t). n1=n2 \<and> value_has_type env v t) flds fieldTypes"
      by (cases slotTy) auto
    show ?thesis proof (cases step)
      case (LVPath_RecordProj field)
      from Cons.prems(2) slotTy_eq LVPath_RecordProj obtain fieldTy where
        fty_lookup: "map_of fieldTypes field = Some fieldTy" and
        rest_ty: "type_at_path env fieldTy rest = Some ty"
        by (auto split: option.splits)
      from list_all2_map_of_transfer_rev[OF all2 fty_lookup]
      obtain fieldVal where fld_lookup: "map_of flds field = Some fieldVal"
        and fv_typed: "value_has_type env fieldVal fieldTy"
        by auto
      show ?thesis
      proof (cases "update_value_at_path fieldVal rest newVal")
        case (Inl err2)
        with Cons.prems(3) CV_Record LVPath_RecordProj fld_lookup
        have err_eq: "err = err2" by simp
        show ?thesis
          using Cons.IH Inl err_eq fv_typed rest_ty by auto
      next
        case (Inr updated_val)
        with Cons.prems(3) CV_Record LVPath_RecordProj fld_lookup show ?thesis by simp
      qed
    next
      case (LVPath_VariantProj x) with CV_Record Cons.prems slotTy_eq show ?thesis by simp
    next
      case (LVPath_ArrayProj x) with CV_Record Cons.prems slotTy_eq show ?thesis by simp
    qed
  next
    case (CV_Variant ctor payload)
    from Cons.prems(1) CV_Variant obtain dtName argTypes tyvars payloadTy where
      slotTy_eq: "slotTy = CoreTy_Datatype dtName argTypes" and
      ctor_lookup: "fmlookup (TE_DataCtors env) ctor = Some (dtName, tyvars, payloadTy)" and
      payload_typed: "value_has_type env payload
                        (apply_subst (fmap_of_list (zip tyvars argTypes)) payloadTy)"
      by (cases slotTy) (auto split: option.splits)
    show ?thesis proof (cases step)
      case (LVPath_RecordProj x) with CV_Variant Cons.prems slotTy_eq show ?thesis by simp
    next
      case (LVPath_VariantProj expectedCtor)
      show ?thesis
      proof (cases "ctor = expectedCtor")
        case True
        from Cons.prems(2) slotTy_eq LVPath_VariantProj True ctor_lookup obtain
          rest_ty: "type_at_path env
                      (apply_subst (fmap_of_list (zip tyvars argTypes)) payloadTy) rest
                    = Some ty"
          by (auto split: if_splits)
        show ?thesis
        proof (cases "update_value_at_path payload rest newVal")
          case (Inl err2)
          with Cons.prems(3) CV_Variant LVPath_VariantProj True
          have err_eq: "err = err2" by simp
          show ?thesis using Cons.IH payload_typed rest_ty Inl err_eq by simp
        next
          case (Inr updated_val)
          with Cons.prems(3) CV_Variant LVPath_VariantProj True show ?thesis by simp
        qed
      next
        case False
        \<comment> \<open>Ctor mismatch: update_value_at_path returns RuntimeError directly.\<close>
        from Cons.prems(3) CV_Variant LVPath_VariantProj False
        have "err = RuntimeError" by simp
        then show ?thesis .
      qed
    next
      case (LVPath_ArrayProj x) with CV_Variant Cons.prems slotTy_eq show ?thesis by simp
    qed
  next
    case (CV_Array sizes elementMap)
    from Cons.prems(1) CV_Array obtain elemTy dims where
      slotTy_eq: "slotTy = CoreTy_Array elemTy dims" and
      elems_typed: "\<forall>idx v. fmlookup elementMap idx = Some v \<longrightarrow> value_has_type env v elemTy"
      by (cases slotTy) auto
    show ?thesis proof (cases step)
      case (LVPath_RecordProj x) with CV_Array Cons.prems slotTy_eq show ?thesis by simp
    next
      case (LVPath_VariantProj x) with CV_Array Cons.prems slotTy_eq show ?thesis by simp
    next
      case (LVPath_ArrayProj indices)
      from Cons.prems(2) slotTy_eq LVPath_ArrayProj
      have rest_ty: "type_at_path env elemTy rest = Some ty" by simp
      show ?thesis
      proof (cases "fmlookup elementMap indices")
        case None
        \<comment> \<open>Array index OOB: RuntimeError directly.\<close>
        from Cons.prems(3) CV_Array LVPath_ArrayProj None
        have "err = RuntimeError" by simp
        then show ?thesis .
      next
        case (Some elemVal)
        from elems_typed Some have elem_typed: "value_has_type env elemVal elemTy" by simp
        show ?thesis
        proof (cases "update_value_at_path elemVal rest newVal")
          case (Inl err2)
          with Cons.prems(3) CV_Array LVPath_ArrayProj Some have err_eq: "err = err2" by simp
          show ?thesis using Cons.IH elem_typed rest_ty Inl err_eq by simp
        next
          case (Inr updated_val)
          with Cons.prems(3) CV_Array LVPath_ArrayProj Some show ?thesis by simp
        qed
      qed
    qed
  next
    case (CV_Bool x) with Cons.prems show ?thesis by (cases slotTy) auto
  next
    case (CV_FiniteInt x1 x2 x3) with Cons.prems show ?thesis by (cases slotTy) auto
  qed
qed


(* state_matches_env is preserved when a single store slot is updated, provided
   the new slot value has the designated type for that slot (storeTyping ! addr).
   This is the key lemma for CoreStmt_Assign and CoreStmt_Swap soundness. *)
lemma state_matches_env_update_store:
  assumes state_env: "state_matches_env state env storeTyping"
    and addr_valid: "addr < length (IS_Store state)"
    and new_slot_typed: "value_has_type env newSlotVal (storeTyping ! addr)"
    and state'_eq: "state' = state \<lparr> IS_Store := (IS_Store state)[addr := newSlotVal] \<rparr>"
  shows "state_matches_env state' env storeTyping"
proof -
  from state'_eq have
    store'_len: "length (IS_Store state') = length (IS_Store state)" and
    locals'_eq: "IS_Locals state' = IS_Locals state" and
    refs'_eq: "IS_Refs state' = IS_Refs state" and
    globals'_eq: "IS_Globals state' = IS_Globals state" and
    funs'_eq: "IS_Functions state' = IS_Functions state" and
    cn'_eq: "IS_ConstLocals state' = IS_ConstLocals state"
    by auto
  have tyargs'_eq [simp]: "IS_TyArgs state' = IS_TyArgs state"
    using state'_eq by simp
  have slot_at_addr: "IS_Store state' ! addr = newSlotVal"
    using state'_eq addr_valid by simp
  have slot_other: "\<And>a. a \<noteq> addr \<Longrightarrow> a < length (IS_Store state)
      \<Longrightarrow> IS_Store state' ! a = IS_Store state ! a"
    using state'_eq by simp

  (* 1. local_vars_exist_in_state: the storeTyping entries haven't changed, and
     type_at_path of storeTyping is independent of the actual store contents. *)
  have "local_vars_exist_in_state state' env storeTyping"
    unfolding local_vars_exist_in_state_def
  proof (intro allI impI, elim conjE)
    fix name ty
    assume lk: "fmlookup (TE_LocalVars env) name = Some ty"
      and ng: "name |\<notin>| TE_GhostLocals env"
    from state_env lk ng have old: "local_var_in_state_with_type state env storeTyping name ty"
      unfolding state_matches_env_def local_vars_exist_in_state_def by blast
    show "local_var_in_state_with_type state' env storeTyping name ty"
      using old locals'_eq refs'_eq store'_len
      unfolding local_var_in_state_with_type_def Let_def
      by (auto split: option.splits)
  qed

  (* 2. global_vars_exist_in_state: unchanged *)
  moreover have "global_vars_exist_in_state state' env"
    using state_env globals'_eq
    unfolding state_matches_env_def global_vars_exist_in_state_def
              global_var_in_state_with_type_def by simp

  (* 3. no_extra_local_vars: unchanged *)
  moreover have "no_extra_local_vars state' env"
    using state_env locals'_eq refs'_eq
    unfolding state_matches_env_def no_extra_local_vars_def by simp

  (* 4. no_extra_global_vars: unchanged *)
  moreover have "no_extra_global_vars state' env"
    using state_env globals'_eq
    unfolding state_matches_env_def no_extra_global_vars_def by simp

  (* 5. funs_exist_in_state: unchanged *)
  moreover have "funs_exist_in_state state' env"
    using state_env funs'_eq
    unfolding state_matches_env_def funs_exist_in_state_def by simp

  (* 6. no_extra_funs: unchanged *)
  moreover have "no_extra_funs state' env"
    using state_env funs'_eq
    unfolding state_matches_env_def no_extra_funs_def by simp

  (* 7. non_consts_in_locals_or_refs: unchanged *)
  moreover have "non_consts_in_locals_or_refs state' env"
    using state_env locals'_eq refs'_eq
    unfolding state_matches_env_def non_consts_in_locals_or_refs_def by simp

  (* 8. const_locals_match: unchanged *)
  moreover have "const_locals_match state' env"
    using state_env cn'_eq
    unfolding state_matches_env_def const_locals_match_def by simp

  (* 9. store_well_typed: slot at addr is newSlotVal with storeTyping ! addr; others unchanged. *)
  moreover have "store_well_typed state' env storeTyping"
    unfolding store_well_typed_def
  proof (intro conjI allI impI)
    from state_env have "length storeTyping = length (IS_Store state)"
      unfolding state_matches_env_def store_well_typed_def by simp
    with store'_len show "length storeTyping = length (IS_Store state')" by simp
  next
    fix a
    assume a_lt: "a < length (IS_Store state')"
    with store'_len have a_lt_old: "a < length (IS_Store state)" by simp
    show "value_has_type env (IS_Store state' ! a) (storeTyping ! a)"
    proof (cases "a = addr")
      case True
      with slot_at_addr new_slot_typed show ?thesis by simp
    next
      case False
      with slot_other[OF False a_lt_old]
      have "IS_Store state' ! a = IS_Store state ! a" by simp
      moreover from state_env a_lt_old
      have "value_has_type env (IS_Store state ! a) (storeTyping ! a)"
        unfolding state_matches_env_def store_well_typed_def by simp
      ultimately show ?thesis by simp
    qed
  qed

  moreover have "ty_args_well_formed state' env"
    using state_env
    unfolding state_matches_env_def ty_args_well_formed_def by simp

  ultimately show ?thesis unfolding state_matches_env_def by auto
qed

(* Soundness of apply_ref_updates: given a list of ref-lvalues each pointing at
   a value of some type ty_i in the existing store, and a parallel list of new
   values each of type ty_i, the fold either errors soundly (RuntimeError, when
   an intermediate update_value_at_path fails on a dangling path) or produces a
   new state matching the same env under the same storeTyping. The storeTyping
   itself does not change because each step only mutates an existing slot
   (no append). *)
lemma apply_ref_updates_sound:
  assumes sme: "state_matches_env state env storeTyping"
      and len: "length refs = length newVals"
      and len_tys: "length tys = length refs"
      and refs_ok: "\<forall>i < length refs.
                       fst (refs ! i) < length (IS_Store state) \<and>
                       type_at_path env (storeTyping ! (fst (refs ! i)))
                                        (snd (refs ! i)) = Some (tys ! i)"
      and vals_typed: "\<forall>i < length newVals. value_has_type env (newVals ! i) (tys ! i)"
  shows "(case apply_ref_updates state refs newVals of
            Inl err \<Rightarrow> sound_error_result err
          | Inr finalState \<Rightarrow> state_matches_env finalState env storeTyping)"
using assms proof (induction state refs newVals arbitrary: tys rule: apply_ref_updates.induct)
  case (1 state)
  from "1.prems"(1) show ?case by simp
next
  case (2 state addr path rest_lvals newVal rest_vals)
  \<comment> \<open>Peel off the head of tys.\<close>
  from "2.prems"(3) obtain ty rest_tys where tys_eq: "tys = ty # rest_tys"
    by (cases tys) auto
  with "2.prems"(3) have len_rest_tys: "length rest_tys = length rest_lvals" by simp
  from "2.prems"(2) have len_rest: "length rest_lvals = length rest_vals" by simp

  \<comment> \<open>The head ref is well-formed in the current state and storeTyping.\<close>
  have len_pos: "0 < length ((addr, path) # rest_lvals)" by simp
  from "2.prems"(4)[rule_format, OF len_pos]
  have head_ok: "addr < length (IS_Store state) \<and>
                 type_at_path env (storeTyping ! addr) path = Some ty"
    using tys_eq by simp
  hence addr_valid: "addr < length (IS_Store state)"
    and path_ty: "type_at_path env (storeTyping ! addr) path = Some ty" by auto

  \<comment> \<open>The head newVal has the path's type.\<close>
  have len_pos_vals: "0 < length (newVal # rest_vals)" by simp
  from "2.prems"(5)[rule_format, OF len_pos_vals]
  have head_typed: "value_has_type env newVal ty"
    using tys_eq by simp

  \<comment> \<open>The old slot has the store-typing type.\<close>
  from sme addr_valid
  have old_slot_typed: "value_has_type env (IS_Store state ! addr) (storeTyping ! addr)"
    unfolding state_matches_env_def store_well_typed_def
    using "2.prems"(1) state_matches_env_def store_well_typed_def by blast

  show ?case
  proof (cases "update_value_at_path (IS_Store state ! addr) path newVal")
    case (Inl err)
    from update_value_at_path_error_is_runtime[OF old_slot_typed path_ty Inl]
    have "err = RuntimeError" .
    with Inl show ?thesis by simp
  next
    case (Inr updated_val)
    \<comment> \<open>The updated slot still has the slot's type.\<close>
    from update_value_at_path_preserves_type[OF old_slot_typed Inr path_ty head_typed]
    have new_slot_typed: "value_has_type env updated_val (storeTyping ! addr)" .

    \<comment> \<open>Lift to state_matches_env on the new state.\<close>
    let ?state1 = "state \<lparr> IS_Store := (IS_Store state)[addr := updated_val] \<rparr>"
    have state1_eq: "?state1 = state \<lparr> IS_Store := (IS_Store state)[addr := updated_val] \<rparr>"
      by simp
    from state_matches_env_update_store[OF "2.prems"(1) addr_valid new_slot_typed state1_eq]
    have sme1: "state_matches_env ?state1 env storeTyping" .

    \<comment> \<open>The store length and storeTyping are unchanged, so the remaining ref-lvalues
        are still well-formed under the new state.\<close>
    have store1_len: "length (IS_Store ?state1) = length (IS_Store state)" by simp
    have rest_refs_ok: "\<forall>i < length rest_lvals.
                          fst (rest_lvals ! i) < length (IS_Store ?state1) \<and>
                          type_at_path env (storeTyping ! (fst (rest_lvals ! i)))
                                           (snd (rest_lvals ! i)) = Some (rest_tys ! i)"
    proof (intro allI impI)
      fix i assume i_lt: "i < length rest_lvals"
      hence "Suc i < length ((addr, path) # rest_lvals)" by simp
      from "2.prems"(4)[rule_format, OF this]
      have "fst (((addr, path) # rest_lvals) ! Suc i) < length (IS_Store state) \<and>
            type_at_path env (storeTyping ! (fst (((addr, path) # rest_lvals) ! Suc i)))
                             (snd (((addr, path) # rest_lvals) ! Suc i))
            = Some (tys ! Suc i)" .
      thus "fst (rest_lvals ! i) < length (IS_Store ?state1) \<and>
            type_at_path env (storeTyping ! (fst (rest_lvals ! i)))
                             (snd (rest_lvals ! i)) = Some (rest_tys ! i)"
        using store1_len tys_eq by simp
    qed

    have rest_vals_typed: "\<forall>i < length rest_vals. value_has_type env (rest_vals ! i) (rest_tys ! i)"
    proof (intro allI impI)
      fix i assume i_lt: "i < length rest_vals"
      hence "Suc i < length (newVal # rest_vals)" by simp
      from "2.prems"(5)[rule_format, OF this]
      have "value_has_type env ((newVal # rest_vals) ! Suc i) (tys ! Suc i)" .
      thus "value_has_type env (rest_vals ! i) (rest_tys ! i)"
        using tys_eq by simp
    qed

    from "2.IH"[OF Inr state1_eq sme1 len_rest len_rest_tys rest_refs_ok rest_vals_typed]
    have IH_result: "case apply_ref_updates ?state1 rest_lvals rest_vals of
                       Inl err \<Rightarrow> sound_error_result err
                     | Inr finalState \<Rightarrow> state_matches_env finalState env storeTyping" .
    have step_eq: "apply_ref_updates state ((addr, path) # rest_lvals) (newVal # rest_vals)
                     = apply_ref_updates ?state1 rest_lvals rest_vals"
      using Inr by (simp add: Let_def)
    from IH_result step_eq show ?thesis by simp
  qed
qed (simp_all)

(* When every element of a sum-typed list is Inr, rights preserves length and
   recovers the wrapped value by index. Used in the extern-call branch of case 6,
   where every val-result is known to be Inr by fold_process_one_arg_inr_inversion. *)
lemma rights_all_inr_length:
  fixes xs :: "('a + 'b) list"
  assumes "\<forall>i < length xs. \<exists>v. xs ! i = Inr v"
  shows "length (rights xs) = length xs"
  using assms
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons x xs')
  from Cons.prems have head: "\<exists>v. x = Inr v"
    by (auto dest: spec[where x=0])
  from head obtain v where x_eq: "x = Inr v" by blast
  from Cons.prems have rest: "\<forall>i < length xs'. \<exists>v. xs' ! i = Inr v"
    by (metis Suc_less_eq length_Cons nth_Cons_Suc)
  show ?case using x_eq Cons.IH[OF rest] by simp
qed

lemma rights_all_inr_nth:
  fixes xs :: "('a + 'b) list"
  assumes "\<forall>j < length xs. \<exists>v. xs ! j = Inr v"
      and "i < length xs"
  shows "Inr (rights xs ! i) = xs ! i"
  using assms
proof (induction xs arbitrary: i)
  case Nil thus ?case by simp
next
  case (Cons x xs')
  from Cons.prems(1) have head: "\<exists>v. x = Inr v"
    by (auto dest: spec[where x=0])
  from head obtain v0 where x_eq: "x = Inr v0" by blast
  from Cons.prems(1) have rest: "\<forall>j < length xs'. \<exists>v. xs' ! j = Inr v"
    by (metis Suc_less_eq length_Cons nth_Cons_Suc)
  show ?case
  proof (cases i)
    case 0 with x_eq show ?thesis by simp
  next
    case (Suc j)
    from Cons.prems(2) Suc have j_lt: "j < length xs'" by simp
    from Cons.IH[OF rest j_lt] x_eq Suc show ?thesis by simp
  qed
qed

(* The interpreter's extern-call branch builds the list of ref-lvalue updates by
   mapping over (IF_Args, refResults), replacing Var-position refResults with
   Inl TypeError (which `rights` then drops), then taking `rights`. This lemma
   characterises the result: its length is the number of Ref positions, and
   its j-th element is the projected refResult at the j-th Ref index.

   Hypothesis: every Ref-position's refResult is actually Inr (which the caller
   establishes from a successful arg-processing fold via
   fold_process_one_arg_inr_inversion). *)
lemma rights_filter_zip_refs_chars_aux:
  fixes ifs :: "(string \<times> VarOrRef) list"
    and rrs :: "(InterpError + (nat \<times> LValuePath list)) list"
  assumes "length ifs = length rrs"
      and "\<forall>i < length ifs. snd (ifs ! i) = Ref \<longrightarrow> (\<exists>a p. rrs ! i = Inr (a, p))"
  shows
    "length (rights (map (\<lambda>((_, vr), r). if vr = Ref then r else Inl TypeError)
                          (zip ifs rrs)))
       = length (filter (\<lambda>i. snd (ifs ! i) = Ref) [0 ..< length ifs])
     \<and> (\<forall>j < length (filter (\<lambda>i. snd (ifs ! i) = Ref) [0 ..< length ifs]).
            rrs ! ((filter (\<lambda>i. snd (ifs ! i) = Ref) [0 ..< length ifs]) ! j)
              = Inr (rights (map (\<lambda>((_, vr), r). if vr = Ref then r else Inl TypeError)
                                 (zip ifs rrs)) ! j))"
using assms proof (induction ifs arbitrary: rrs)
  case Nil
  then show ?case by simp
next
  case (Cons ifa ifrest)
  from Cons.prems(1) obtain rr rrest where rrs_eq: "rrs = rr # rrest"
    by (cases rrs) auto
  obtain name vor where ifa_eq: "ifa = (name, vor)" by (cases ifa)

  have len_rest: "length ifrest = length rrest"
    using Cons.prems(1) rrs_eq by simp
  have rest_inrs:
    "\<forall>i < length ifrest. snd (ifrest ! i) = Ref \<longrightarrow> (\<exists>a p. rrest ! i = Inr (a, p))"
  proof (intro allI impI)
    fix i assume i_lt: "i < length ifrest" and i_ref: "snd (ifrest ! i) = Ref"
    have "Suc i < length (ifa # ifrest)" using i_lt by simp
    moreover have "snd ((ifa # ifrest) ! Suc i) = Ref" using i_ref by simp
    ultimately have "\<exists>a p. rrs ! Suc i = Inr (a, p)"
      using Cons.prems(2) by blast
    thus "\<exists>a p. rrest ! i = Inr (a, p)" using rrs_eq by simp
  qed

  \<comment> \<open>IH on the tail. \<close>
  from Cons.IH[OF len_rest rest_inrs]
  have IH_len:
    "length (rights (map (\<lambda>((_, vr), r). if vr = Ref then r else Inl TypeError)
                          (zip ifrest rrest)))
       = length (filter (\<lambda>i. snd (ifrest ! i) = Ref) [0 ..< length ifrest])"
    and IH_chars:
    "\<And>j. j < length (filter (\<lambda>i. snd (ifrest ! i) = Ref) [0 ..< length ifrest]) \<Longrightarrow>
          rrest ! ((filter (\<lambda>i. snd (ifrest ! i) = Ref) [0 ..< length ifrest]) ! j)
            = Inr (rights (map (\<lambda>((_, vr), r). if vr = Ref then r else Inl TypeError)
                                (zip ifrest rrest)) ! j)"
    by auto

  let ?map_rest = "map (\<lambda>((_, vr), r). if vr = Ref then r else Inl TypeError)
                       (zip ifrest rrest)"
  let ?idxs_rest = "filter (\<lambda>i. snd (ifrest ! i) = Ref) [0 ..< length ifrest]"

  have upt_split: "[0 ..< length (ifa # ifrest)] = 0 # map Suc [0 ..< length ifrest]"
    using map_Suc_upt upt_rec by auto
  have idxs_split:
    "filter (\<lambda>i. snd ((ifa # ifrest) ! i) = Ref) [0 ..< length (ifa # ifrest)]
      = (if vor = Ref then 0 # map Suc ?idxs_rest else map Suc ?idxs_rest)"
    using upt_split ifa_eq by (simp add: filter_map o_def)

  show ?case
  proof (cases vor)
    case Var
    have rights_step:
      "rights (map (\<lambda>((_, vr), r). if vr = Ref then r else Inl TypeError)
                   (zip (ifa # ifrest) (rr # rrest)))
         = rights ?map_rest"
      using ifa_eq Var by simp
    have idxs_step:
      "filter (\<lambda>i. snd ((ifa # ifrest) ! i) = Ref) [0 ..< length (ifa # ifrest)]
         = map Suc ?idxs_rest"
      using idxs_split Var by simp

    have len_part:
      "length (rights (map (\<lambda>((_, vr), r). if vr = Ref then r else Inl TypeError)
                            (zip (ifa # ifrest) (rr # rrest))))
         = length (filter (\<lambda>i. snd ((ifa # ifrest) ! i) = Ref)
                          [0 ..< length (ifa # ifrest)])"
      using rights_step idxs_step IH_len by simp

    have chars_part:
      "\<forall>j < length (filter (\<lambda>i. snd ((ifa # ifrest) ! i) = Ref)
                            [0 ..< length (ifa # ifrest)]).
          (rr # rrest) ! ((filter (\<lambda>i. snd ((ifa # ifrest) ! i) = Ref)
                                   [0 ..< length (ifa # ifrest)]) ! j)
            = Inr (rights (map (\<lambda>((_, vr), r). if vr = Ref then r else Inl TypeError)
                                (zip (ifa # ifrest) (rr # rrest))) ! j)"
    proof (intro allI impI)
      fix j
      assume "j < length (filter (\<lambda>i. snd ((ifa # ifrest) ! i) = Ref)
                                  [0 ..< length (ifa # ifrest)])"
      hence j_lt: "j < length ?idxs_rest" using idxs_step length_map by metis
      have rhs: "(filter (\<lambda>i. snd ((ifa # ifrest) ! i) = Ref)
                          [0 ..< length (ifa # ifrest)]) ! j
                   = Suc (?idxs_rest ! j)"
        using idxs_step j_lt by simp
      show "(rr # rrest) ! ((filter (\<lambda>i. snd ((ifa # ifrest) ! i) = Ref)
                                     [0 ..< length (ifa # ifrest)]) ! j)
              = Inr (rights (map (\<lambda>((_, vr), r). if vr = Ref then r else Inl TypeError)
                                  (zip (ifa # ifrest) (rr # rrest))) ! j)"
        using rhs rights_step IH_chars[OF j_lt] by simp
    qed

    from len_part chars_part rrs_eq show ?thesis by simp
  next
    case Ref
    have head_inr: "\<exists>a p. rr = Inr (a, p)"
    proof -
      have "0 < length (ifa # ifrest)" by simp
      moreover have "snd ((ifa # ifrest) ! 0) = Ref" using ifa_eq Ref by simp
      ultimately have "\<exists>a p. rrs ! 0 = Inr (a, p)"
        using Cons.prems(2) by blast
      thus ?thesis using rrs_eq by simp
    qed
    then obtain a p where rr_eq: "rr = Inr (a, p)" by blast

    have rights_step:
      "rights (map (\<lambda>((_, vr), r). if vr = Ref then r else Inl TypeError)
                   (zip (ifa # ifrest) (rr # rrest)))
         = (a, p) # rights ?map_rest"
      using ifa_eq Ref rr_eq by simp
    have idxs_step:
      "filter (\<lambda>i. snd ((ifa # ifrest) ! i) = Ref) [0 ..< length (ifa # ifrest)]
         = 0 # map Suc ?idxs_rest"
      using idxs_split Ref by simp

    have len_part:
      "length (rights (map (\<lambda>((_, vr), r). if vr = Ref then r else Inl TypeError)
                            (zip (ifa # ifrest) (rr # rrest))))
         = length (filter (\<lambda>i. snd ((ifa # ifrest) ! i) = Ref)
                          [0 ..< length (ifa # ifrest)])"
      using rights_step idxs_step IH_len by simp

    have chars_part:
      "\<forall>j < length (filter (\<lambda>i. snd ((ifa # ifrest) ! i) = Ref)
                            [0 ..< length (ifa # ifrest)]).
          (rr # rrest) ! ((filter (\<lambda>i. snd ((ifa # ifrest) ! i) = Ref)
                                   [0 ..< length (ifa # ifrest)]) ! j)
            = Inr (rights (map (\<lambda>((_, vr), r). if vr = Ref then r else Inl TypeError)
                                (zip (ifa # ifrest) (rr # rrest))) ! j)"
    proof (intro allI impI)
      fix j
      assume j_lt_outer:
        "j < length (filter (\<lambda>i. snd ((ifa # ifrest) ! i) = Ref)
                             [0 ..< length (ifa # ifrest)])"
      show "(rr # rrest) ! ((filter (\<lambda>i. snd ((ifa # ifrest) ! i) = Ref)
                                     [0 ..< length (ifa # ifrest)]) ! j)
              = Inr (rights (map (\<lambda>((_, vr), r). if vr = Ref then r else Inl TypeError)
                                  (zip (ifa # ifrest) (rr # rrest))) ! j)"
      proof (cases j)
        case 0
        have idx0: "(filter (\<lambda>i. snd ((ifa # ifrest) ! i) = Ref)
                             [0 ..< length (ifa # ifrest)]) ! 0 = 0"
          using idxs_step by simp
        from idx0 0 rr_eq rights_step show ?thesis by simp
      next
        case (Suc k)
        from j_lt_outer Suc idxs_step have k_lt: "k < length ?idxs_rest"
          by (metis Suc_less_eq length_Cons length_map)
        have idxk: "(filter (\<lambda>i. snd ((ifa # ifrest) ! i) = Ref)
                             [0 ..< length (ifa # ifrest)]) ! Suc k
                      = Suc (?idxs_rest ! k)"
          using idxs_step k_lt by simp
        from idxk rights_step IH_chars[OF k_lt] Suc show ?thesis by simp
      qed
    qed

    from len_part chars_part rrs_eq show ?thesis by simp
  qed
qed

lemma rights_filter_zip_refs_chars:
  fixes ifArgs :: "(string \<times> VarOrRef) list"
    and refResults :: "(InterpError + (nat \<times> LValuePath list)) list"
  defines "mapped \<equiv> map (\<lambda>((_, vr), r). if vr = Ref then r else Inl TypeError)
                        (zip ifArgs refResults)"
      and "idxs \<equiv> filter (\<lambda>i. snd (ifArgs ! i) = Ref) [0 ..< length ifArgs]"
  assumes len_eq: "length ifArgs = length refResults"
      and ref_inrs: "\<forall>i < length ifArgs.
                       snd (ifArgs ! i) = Ref \<longrightarrow> (\<exists>a p. refResults ! i = Inr (a, p))"
  shows "length (rights mapped) = length idxs \<and>
         (\<forall>j < length idxs.
             refResults ! (idxs ! j) = Inr (rights mapped ! j))"
  using rights_filter_zip_refs_chars_aux[OF len_eq ref_inrs]
  unfolding mapped_def idxs_def by blast

(* If find_matching_arm succeeds, the result is the body of some arm in the list *)
lemma find_matching_arm_in_set:
  assumes "find_matching_arm val arms = Inr rhs"
  shows "\<exists>pat. (pat, rhs) \<in> set arms"
  using assms by (induction arms) (auto split: if_splits)

(* find_matching_arm only ever fails with RuntimeError (no matching arm found).
   This is the key fact that makes non-exhaustive matches sound: a failed match
   at runtime is a runtime error, not a type error. *)
lemma find_matching_arm_error:
  assumes "find_matching_arm val arms = Inl err"
  shows "err = RuntimeError"
  using assms by (induction arms) (auto split: if_splits)

(* Helper: sizes_match_dims implies equal length *)
lemma sizes_match_dims_length:
  "sizes_match_dims sizes dims \<Longrightarrow> length sizes = length dims"
  by (induction sizes dims rule: sizes_match_dims.induct) auto

(* Helper: array_size_to_value has sizeof_type *)
lemma array_size_to_value_has_sizeof_type:
  assumes "sizes_valid sizes"
    and "sizes_match_dims sizes dims"
  shows "value_has_type env (array_size_to_value sizes) (sizeof_type dims)"
proof -
  from assms(2) have len_eq: "length sizes = length dims" by (rule sizes_match_dims_length)
  from assms(1) have fits: "\<forall>s \<in> set sizes. int_fits Unsigned IntBits_64 s"
    by (auto simp: sizes_valid_def list_all_iff)
  show ?thesis
  proof (cases dims rule: sizeof_type.cases)
    case (1 d)
    then obtain n where sizes_eq: "sizes = [n]" using len_eq by (cases sizes) auto
    from fits sizes_eq have "int_fits Unsigned IntBits_64 n" by simp
    then show ?thesis using 1 sizes_eq by (simp add: u64_type_def)
  next
    case "2_1"
    then show ?thesis using len_eq by simp
  next
    case ("2_2" d1 d2 ds)
    then obtain s1 s2 ss where sizes_eq: "sizes = s1 # s2 # ss" and
      len_ss: "length ss = length ds"
      using len_eq by (cases sizes; cases "tl sizes") auto
    have val_eq': "array_size_to_value (s1 # s2 # ss) =
          CV_Record (zip (tuple_field_names (Suc (Suc (length ss))))
                         (map (CV_FiniteInt Unsigned IntBits_64) (s1 # s2 # ss)))"
      by simp
    have ty_eq': "sizeof_type (d1 # d2 # ds) =
          CoreTy_Record (zip (tuple_field_names (Suc (Suc (length ds))))
                             (replicate (Suc (Suc (length ds))) u64_type))"
      by simp
    have la2: "list_all2
        (\<lambda>(name1, fldVal) (name2, fldTy). name1 = name2 \<and> value_has_type env fldVal fldTy)
        (zip (tuple_field_names (Suc (Suc (length ss))))
             (map (CV_FiniteInt Unsigned IntBits_64) (s1 # s2 # ss)))
        (zip (tuple_field_names (Suc (Suc (length ds))))
             (replicate (Suc (Suc (length ds))) u64_type))"
    proof (intro list_all2_all_nthI)
      show "length (zip (tuple_field_names (Suc (Suc (length ss))))
                        (map (CV_FiniteInt Unsigned IntBits_64) (s1 # s2 # ss))) =
            length (zip (tuple_field_names (Suc (Suc (length ds))))
                        (replicate (Suc (Suc (length ds))) u64_type))"
        using len_ss by (simp add: tuple_field_names_def)
    next
      fix i assume i_bound: "i < length (zip (tuple_field_names (Suc (Suc (length ss))))
                                             (map (CV_FiniteInt Unsigned IntBits_64) (s1 # s2 # ss)))"
      hence i_len: "i < Suc (Suc (length ss))"
        by (simp add: tuple_field_names_def)
      have i_len2: "i < Suc (Suc (length ds))" using i_len len_ss by simp
      have nth_val: "(map (CV_FiniteInt Unsigned IntBits_64) (s1 # s2 # ss)) ! i =
                     CV_FiniteInt Unsigned IntBits_64 ((s1 # s2 # ss) ! i)"
        using i_len by (metis length_Cons nth_map)
      have nth_ty: "(replicate (Suc (Suc (length ds))) u64_type) ! i = u64_type"
        using i_len2 by (meson nth_replicate) 
      have nth_name_eq: "(tuple_field_names (Suc (Suc (length ss)))) ! i =
                         (tuple_field_names (Suc (Suc (length ds)))) ! i"
        using len_ss by simp
      have sz_i: "(s1 # s2 # ss) ! i \<in> set sizes" using sizes_eq i_len by (auto simp: set_conv_nth)
      hence "int_fits Unsigned IntBits_64 ((s1 # s2 # ss) ! i)" using fits by auto
      then show "(case zip (tuple_field_names (Suc (Suc (length ss))))
                           (map (CV_FiniteInt Unsigned IntBits_64) (s1 # s2 # ss)) ! i of
                  (name1, fldVal) \<Rightarrow>
                    \<lambda>(name2, fldTy). name1 = name2 \<and> value_has_type env fldVal fldTy)
                 (zip (tuple_field_names (Suc (Suc (length ds))))
                      (replicate (Suc (Suc (length ds))) u64_type) ! i)"
        using i_len i_len2 nth_val nth_ty nth_name_eq len_ss
        by (simp add: tuple_field_names_def u64_type_def)
    qed
    then show ?thesis using "2_2" sizes_eq distinct_tuple_field_names by simp
  qed
qed



(* ========================================================================== *)
(* HELPER 2 (arg processing soundness for function calls)                      *)
(*                                                                             *)
(* Used by case 6 (function call) of type_soundness. The interpreter evaluates  *)
(* each argument's value and (for Ref params) its writable lvalue, then folds   *)
(* process_one_arg over the results starting from a state whose locals/refs    *)
(* have been cleared. Helper 2 says that this fold either errors soundly or    *)
(* produces a state that matches the (substituted) body env under some store   *)
(* typing extending the caller's.                                              *)
(*                                                                             *)
(* The proof is structured as:                                                 *)
(*                                                                             *)
(*   H2a  cleared state matches an "empty-locals" partial body env             *)
(*                                                                             *)
(*   H2b  single-step: given a state matching the partial body env up to the   *)
(*        first k parameters, process_one_arg on the (k+1)-th tuple either     *)
(*        errors soundly or produces a state matching the partial env up to    *)
(*        k+1 parameters, with the store typing possibly extended by one slot  *)
(*        (for Var params).                                                    *)
(*                                                                             *)
(*   H2c  fold: compose the single-step lemma over the full parameter list.    *)
(*                                                                             *)
(* partial_body_env_for env funInfo k is body_env_for env funInfo with        *)
(* TE_LocalVars restricted to the first k FI_TmArgs (types stored             *)
(* unsubstituted; the substitution lives in IS_TyArgs of the matching state), *)
(* and TE_ConstLocals restricted to Var-marked names among them.              *)
(* When k = length (FI_TmArgs funInfo), this equals body_env_for env funInfo. *)
(* ========================================================================== *)

(* partial_body_env_for env funInfo k is body_env_for env funInfo with
   TE_LocalVars restricted to the first k FI_TmArgs (types stored unsubstituted)
   and TE_ConstLocals restricted to Var-marked names among them.

   When k = length (FI_TmArgs funInfo) the partial env equals body_env_for
   env funInfo directly.

   The substitution previously inlined here (apply_subst tySubst) now lives in
   IS_TyArgs of the matching state, and state_matches_env_add_const_local /
   _add_ref pin the slot's storeTyping entry at apply_subst (IS_TyArgs state) ty
   when adding. *)
definition partial_body_env_for ::
    "CoreTyEnv \<Rightarrow> FunInfo \<Rightarrow> nat \<Rightarrow> CoreTyEnv" where
  "partial_body_env_for env funInfo k =
    (body_env_for env funInfo) \<lparr>
      TE_LocalVars := fmap_of_list
        (map (\<lambda>(name, ty, _). (name, ty))
             (take k (FI_TmArgs funInfo))),
      TE_ConstLocals := fset_of_list
        (map (\<lambda>(name, _, _). name)
             (filter (\<lambda>(_, _, vor). vor = Var) (take k (FI_TmArgs funInfo))))
    \<rparr>"

(* When k = 0, the partial env has no locals and no const names: a body env
   whose locals/refs have been cleared. *)
lemma partial_body_env_for_zero:
  "TE_LocalVars (partial_body_env_for env funInfo 0) = fmempty"
  "TE_ConstLocals (partial_body_env_for env funInfo 0) = {||}"
  by (simp_all add: partial_body_env_for_def)

(* When k = length (FI_TmArgs funInfo), the partial env equals body_env_for
   env funInfo. This is the bridge from the induction's end state to the
   bodyEnv used in case 6. *)
lemma partial_body_env_for_full:
  "partial_body_env_for env funInfo (length (FI_TmArgs funInfo))
   = body_env_for env funInfo"
  by (simp add: partial_body_env_for_def body_env_for_def)

(* partial_body_env_for is well-formed whenever env is. Strategy: each clause
   of tyenv_well_formed is established for body_env_for env funInfo by
   body_env_for_well_formed; the local-related overrides in partial_body_env_for
   only weaken/eliminate the local-mentioning clauses (TE_LocalVars is restricted,
   TE_ConstLocals is restricted, and TE_GhostLocals stays {||}), so each clause
   either survives unchanged (most do, since they don't read these fields) or
   becomes easier to satisfy. *)
lemma partial_body_env_for_well_formed:
  assumes wf: "tyenv_well_formed env"
      and fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo"
      and not_ghost: "FI_Ghost funInfo = NotGhost"
  shows "tyenv_well_formed (partial_body_env_for env funInfo k)"
proof -
  let ?pEnv = "partial_body_env_for env funInfo k"
  let ?be = "body_env_for env funInfo"
  have wf_be: "tyenv_well_formed ?be"
    using body_env_for_well_formed[OF wf fn_lookup not_ghost] .

  \<comment> \<open>?pEnv differs from ?be only in TE_LocalVars and TE_ConstLocals. All other
      record fields are identical. \<close>
  have lv_pEnv: "TE_LocalVars ?pEnv =
                   fmap_of_list (map (\<lambda>(n, t, _). (n, t)) (take k (FI_TmArgs funInfo)))"
    by (simp add: partial_body_env_for_def)
  have cl_pEnv: "TE_ConstLocals ?pEnv =
                   fset_of_list (map (\<lambda>(n, _, _). n)
                     (filter (\<lambda>(_, _, vor). vor = Var) (take k (FI_TmArgs funInfo))))"
    by (simp add: partial_body_env_for_def)
  have ghost_pEnv: "TE_GhostLocals ?pEnv = {||}"
    by (simp add: partial_body_env_for_def body_env_for_def)
  have other_eq:
    "TE_GlobalVars ?pEnv = TE_GlobalVars ?be"
    "TE_GhostGlobals ?pEnv = TE_GhostGlobals ?be"
    "TE_Functions ?pEnv = TE_Functions ?be"
    "TE_Datatypes ?pEnv = TE_Datatypes ?be"
    "TE_DataCtors ?pEnv = TE_DataCtors ?be"
    "TE_DataCtorsByType ?pEnv = TE_DataCtorsByType ?be"
    "TE_GhostDatatypes ?pEnv = TE_GhostDatatypes ?be"
    "TE_TypeVars ?pEnv = TE_TypeVars ?be"
    "TE_RuntimeTypeVars ?pEnv = TE_RuntimeTypeVars ?be"
    "TE_ReturnType ?pEnv = TE_ReturnType ?be"
    by (simp_all add: partial_body_env_for_def body_env_for_def)

  \<comment> \<open>Local-var typings in ?pEnv are a subset of those in ?be: if a name maps to
      ty in ?pEnv's locals, it maps to ty in ?be's locals too. This holds because
      ?pEnv's locals = first k of FI_TmArgs, ?be's locals = all of FI_TmArgs,
      and the param names are distinct (so map_of of a sublist agrees with
      map_of of the full list on that sublist's keys). \<close>
  from wf fn_lookup have all_distinct: "distinct (map fst (FI_TmArgs funInfo))"
    using wf unfolding tyenv_well_formed_def tyenv_fun_param_names_distinct_def
    by blast

  have lv_subset:
    "\<And>name ty. fmlookup (TE_LocalVars ?pEnv) name = Some ty
                 \<Longrightarrow> fmlookup (TE_LocalVars ?be) name = Some ty"
  proof -
    fix name ty assume "fmlookup (TE_LocalVars ?pEnv) name = Some ty"
    hence "map_of (map (\<lambda>(n, t, _). (n, t)) (take k (FI_TmArgs funInfo))) name = Some ty"
      using lv_pEnv by (simp add: fmap_of_list.rep_eq)
    hence in_take: "(name, ty) \<in> set (map (\<lambda>(n, t, _). (n, t)) (take k (FI_TmArgs funInfo)))"
      by (rule map_of_SomeD)
    have "set (take k (FI_TmArgs funInfo)) \<subseteq> set (FI_TmArgs funInfo)"
      by (rule set_take_subset)
    hence "set (map (\<lambda>(n, t, _). (n, t)) (take k (FI_TmArgs funInfo)))
            \<subseteq> set (map (\<lambda>(n, t, _). (n, t)) (FI_TmArgs funInfo))"
      by (metis set_take_subset take_map)
    with in_take have in_full:
      "(name, ty) \<in> set (map (\<lambda>(n, t, _). (n, t)) (FI_TmArgs funInfo))"
      by blast
    \<comment> \<open>distinct map fst transferred to the projection \<close>
    have dist_proj:
      "distinct (map fst (map (\<lambda>(n, t, _). (n, t)) (FI_TmArgs funInfo)))"
      using all_distinct by (simp add: case_prod_beta comp_def)
    from in_full dist_proj have
      "map_of (map (\<lambda>(n, t, _). (n, t)) (FI_TmArgs funInfo)) name = Some ty"
      by simp
    thus "fmlookup (TE_LocalVars ?be) name = Some ty"
      by (simp add: body_env_for_def fmap_of_list.rep_eq)
  qed

  \<comment> \<open>Extract well-formedness clauses from ?be. \<close>
  from wf_be have
    be_vars_wk: "tyenv_vars_well_kinded ?be" and
    be_vars_rt: "tyenv_vars_runtime ?be" and
    be_ghost_subset: "tyenv_ghost_vars_subset ?be" and
    be_ret_wk: "tyenv_return_type_well_kinded ?be" and
    be_ctors_cons: "tyenv_ctors_consistent ?be" and
    be_payloads_wk: "tyenv_payloads_well_kinded ?be" and
    be_ctor_tyvars_distinct: "tyenv_ctor_tyvars_distinct ?be" and
    be_ctors_by_type: "tyenv_ctors_by_type_consistent ?be" and
    be_fun_types_wk: "tyenv_fun_types_well_kinded ?be" and
    be_fun_tyvars_distinct: "tyenv_fun_tyvars_distinct ?be" and
    be_fun_param_names_distinct: "tyenv_fun_param_names_distinct ?be" and
    be_fun_ghost: "tyenv_fun_ghost_constraint ?be" and
    be_nonghost_payloads: "tyenv_nonghost_payloads_runtime ?be" and
    be_ghost_dt_subset: "tyenv_ghost_datatypes_subset ?be" and
    be_rt_subset: "tyenv_runtime_tyvars_subset ?be"
    unfolding tyenv_well_formed_def by auto

  \<comment> \<open>Field congruence: is_well_kinded / is_runtime_type only depend on
      TE_TypeVars / TE_RuntimeTypeVars and TE_Datatypes / TE_GhostDatatypes,
      all of which agree between ?pEnv and ?be. So we can substitute freely. \<close>
  have wk_eq: "\<And>e f t. is_well_kinded (?pEnv \<lparr> TE_TypeVars := e, TE_RuntimeTypeVars := f \<rparr>) t
                       = is_well_kinded (?be \<lparr> TE_TypeVars := e, TE_RuntimeTypeVars := f \<rparr>) t"
    by (rule is_well_kinded_cong_env) (simp_all add: other_eq)
  have rt_eq: "\<And>e f t. is_runtime_type (?pEnv \<lparr> TE_TypeVars := e, TE_RuntimeTypeVars := f \<rparr>) t
                       = is_runtime_type (?be \<lparr> TE_TypeVars := e, TE_RuntimeTypeVars := f \<rparr>) t"
    by (rule is_runtime_type_cong_env) (simp_all add: other_eq)
  have wk_self_eq: "\<And>t. is_well_kinded ?pEnv t = is_well_kinded ?be t"
    by (rule is_well_kinded_cong_env) (simp_all add: other_eq)
  have rt_self_eq: "\<And>t. is_runtime_type ?pEnv t = is_runtime_type ?be t"
    by (rule is_runtime_type_cong_env) (simp_all add: other_eq)

  \<comment> \<open>(1) tyenv_vars_well_kinded: locals come from ?be's locals (via lv_subset);
       globals lookup is identical to ?be (other_eq); is_well_kinded transfers. \<close>
  have c1: "tyenv_vars_well_kinded ?pEnv"
    unfolding tyenv_vars_well_kinded_def
  proof (intro conjI allI impI)
    fix name ty assume A: "fmlookup (TE_LocalVars ?pEnv) name = Some ty"
    from lv_subset[OF A] have "is_well_kinded ?be ty"
      using be_vars_wk unfolding tyenv_vars_well_kinded_def by blast
    thus "is_well_kinded ?pEnv ty" using wk_self_eq by simp
  next
    fix name ty assume gv: "fmlookup (TE_GlobalVars ?pEnv) name = Some ty"
    hence "fmlookup (TE_GlobalVars ?be) name = Some ty" using other_eq by simp
    with be_vars_wk
    have "is_well_kinded (?be \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
      unfolding tyenv_vars_well_kinded_def by blast
    thus "is_well_kinded (?pEnv \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
      using wk_eq by simp
  qed

  \<comment> \<open>(2) tyenv_vars_runtime: locals similar; ghost-locals = {||} so the not-ghost
       condition holds for all locals; globals inherited. \<close>
  have c2: "tyenv_vars_runtime ?pEnv"
    unfolding tyenv_vars_runtime_def
  proof (intro conjI allI impI)
    fix name ty
    assume A: "fmlookup (TE_LocalVars ?pEnv) name = Some ty
                \<and> name |\<notin>| TE_GhostLocals ?pEnv"
    from A have lv: "fmlookup (TE_LocalVars ?pEnv) name = Some ty" by simp
    from lv_subset[OF lv] have "fmlookup (TE_LocalVars ?be) name = Some ty" .
    moreover have "name |\<notin>| TE_GhostLocals ?be"
      by (simp add: body_env_for_def)
    ultimately have "is_runtime_type ?be ty"
      using be_vars_rt unfolding tyenv_vars_runtime_def by blast
    thus "is_runtime_type ?pEnv ty" using rt_self_eq by simp
  next
    fix name ty
    assume A: "fmlookup (TE_GlobalVars ?pEnv) name = Some ty
                \<and> name |\<notin>| TE_GhostGlobals ?pEnv"
    hence gv: "fmlookup (TE_GlobalVars ?be) name = Some ty"
      and ng: "name |\<notin>| TE_GhostGlobals ?be"
      using other_eq by simp_all
    from gv ng be_vars_rt
    have "is_runtime_type (?be \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
      unfolding tyenv_vars_runtime_def by blast
    thus "is_runtime_type (?pEnv \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
      using rt_eq by simp
  qed

  \<comment> \<open>(3) tyenv_ghost_vars_subset: TE_GhostLocals = {||} \<subseteq> anything;
       globals inherited from ?be. \<close>
  have c3: "tyenv_ghost_vars_subset ?pEnv"
    unfolding tyenv_ghost_vars_subset_def
    using be_ghost_subset
    unfolding tyenv_ghost_vars_subset_def
    by (simp add: ghost_pEnv other_eq)

  \<comment> \<open>Remaining clauses (4)–(15): all are statements about the env's fields
       that ?pEnv inherits from ?be (TE_DataCtors, TE_Datatypes, TE_GhostDatatypes,
       TE_Functions, TE_TypeVars, TE_RuntimeTypeVars, TE_ReturnType). For each
       clause we can transfer directly via field equalities, possibly wrapping
       wk/rt with the appropriate cong. \<close>

  have c4: "tyenv_return_type_well_kinded ?pEnv"
    using be_ret_wk wk_self_eq other_eq(10)
    unfolding tyenv_return_type_well_kinded_def by simp

  have c5: "tyenv_ctors_consistent ?pEnv"
    using be_ctors_cons unfolding tyenv_ctors_consistent_def
    by (simp add: other_eq)

  have c6: "tyenv_payloads_well_kinded ?pEnv"
    unfolding tyenv_payloads_well_kinded_def
  proof (intro allI impI)
    fix ctorName dtName tyVars payload
    assume "fmlookup (TE_DataCtors ?pEnv) ctorName = Some (dtName, tyVars, payload)"
    hence ctor_lk: "fmlookup (TE_DataCtors ?be) ctorName = Some (dtName, tyVars, payload)"
      using other_eq by simp
    with be_payloads_wk
    have "is_well_kinded (?be \<lparr> TE_TypeVars := fset_of_list tyVars \<rparr>) payload"
      unfolding tyenv_payloads_well_kinded_def by blast
    \<comment> \<open>Drop into wk_eq form: this is wk_eq with the rtvs arg set to whatever
        ?be has. Need a single-field variant. \<close>
    moreover
    have "is_well_kinded (?be \<lparr> TE_TypeVars := fset_of_list tyVars \<rparr>) payload
        = is_well_kinded (?pEnv \<lparr> TE_TypeVars := fset_of_list tyVars \<rparr>) payload"
      by (rule is_well_kinded_cong_env) (simp_all add: other_eq)
    ultimately show "is_well_kinded (?pEnv \<lparr> TE_TypeVars := fset_of_list tyVars \<rparr>) payload"
      by simp
  qed

  have c7: "tyenv_ctor_tyvars_distinct ?pEnv"
    using be_ctor_tyvars_distinct
    unfolding tyenv_ctor_tyvars_distinct_def
    by (simp add: other_eq)

  have c8: "tyenv_ctors_by_type_consistent ?pEnv"
    using be_ctors_by_type unfolding tyenv_ctors_by_type_consistent_def
    by (simp add: other_eq)

  have c9: "tyenv_fun_types_well_kinded ?pEnv"
    unfolding tyenv_fun_types_well_kinded_def
  proof (intro allI impI)
    fix funName info
    assume "fmlookup (TE_Functions ?pEnv) funName = Some info"
    hence info_lk: "fmlookup (TE_Functions ?be) funName = Some info"
      using other_eq by simp
    with be_fun_types_wk
    have args_wk: "\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs info).
                     is_well_kinded (?be \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info) \<rparr>) ty"
      and ret_wk: "is_well_kinded (?be \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info) \<rparr>)
                                  (FI_ReturnType info)"
      unfolding tyenv_fun_types_well_kinded_def by auto
    have wk_scope_eq:
      "\<And>t. is_well_kinded (?be \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info) \<rparr>) t
        = is_well_kinded (?pEnv \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info) \<rparr>) t"
      by (rule is_well_kinded_cong_env) (simp_all add: other_eq)
    show "(\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs info).
             is_well_kinded (?pEnv \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info) \<rparr>) ty) \<and>
          is_well_kinded (?pEnv \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info) \<rparr>) (FI_ReturnType info)"
      using args_wk ret_wk wk_scope_eq by simp
  qed

  have c10: "tyenv_fun_tyvars_distinct ?pEnv"
    using be_fun_tyvars_distinct
    unfolding tyenv_fun_tyvars_distinct_def
    by (simp add: other_eq)

  have c11: "tyenv_fun_param_names_distinct ?pEnv"
    using be_fun_param_names_distinct
    unfolding tyenv_fun_param_names_distinct_def
    by (simp add: other_eq)

  have c12: "tyenv_fun_ghost_constraint ?pEnv"
    unfolding tyenv_fun_ghost_constraint_def Let_def
  proof (intro allI impI, elim conjE)
    fix funName info
    assume info_lk_pEnv: "fmlookup (TE_Functions ?pEnv) funName = Some info"
       and ng_info: "FI_Ghost info = NotGhost"
    have info_lk: "fmlookup (TE_Functions ?be) funName = Some info"
      using info_lk_pEnv other_eq by simp
    from info_lk ng_info be_fun_ghost
    have inner:
      "(\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs info).
             is_runtime_type (?be \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info),
                                     TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info) \<rparr>) ty) \<and>
       is_runtime_type (?be \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info),
                               TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info) \<rparr>)
                       (FI_ReturnType info)"
      unfolding tyenv_fun_ghost_constraint_def Let_def by blast
    have rt_scope_eq:
      "\<And>t. is_runtime_type (?be \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info),
                                    TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info) \<rparr>) t
         = is_runtime_type (?pEnv \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info),
                                     TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info) \<rparr>) t"
      by (rule is_runtime_type_cong_env) (simp_all add: other_eq)
    show "(\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs info).
              is_runtime_type (?pEnv \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info),
                                        TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info) \<rparr>) ty) \<and>
          is_runtime_type (?pEnv \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info),
                                    TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info) \<rparr>)
                          (FI_ReturnType info)"
      using inner rt_scope_eq by simp
  qed

  have c13: "tyenv_nonghost_payloads_runtime ?pEnv"
    unfolding tyenv_nonghost_payloads_runtime_def
  proof (intro allI impI)
    fix ctorName dtName tyVars payload
    assume ctor_lk_pEnv: "fmlookup (TE_DataCtors ?pEnv) ctorName = Some (dtName, tyVars, payload)"
       and ng_dt: "dtName |\<notin>| TE_GhostDatatypes ?pEnv"
    have ctor_lk_be: "fmlookup (TE_DataCtors ?be) ctorName = Some (dtName, tyVars, payload)"
      using ctor_lk_pEnv other_eq by simp
    have ng_dt_be: "dtName |\<notin>| TE_GhostDatatypes ?be"
      using ng_dt other_eq by simp
    from ctor_lk_be ng_dt_be be_nonghost_payloads
    have "is_runtime_type (?be \<lparr> TE_TypeVars := fset_of_list tyVars,
                                  TE_RuntimeTypeVars := fset_of_list tyVars \<rparr>) payload"
      unfolding tyenv_nonghost_payloads_runtime_def by blast
    moreover
    have "is_runtime_type (?be \<lparr> TE_TypeVars := fset_of_list tyVars,
                                  TE_RuntimeTypeVars := fset_of_list tyVars \<rparr>) payload
        = is_runtime_type (?pEnv \<lparr> TE_TypeVars := fset_of_list tyVars,
                                    TE_RuntimeTypeVars := fset_of_list tyVars \<rparr>) payload"
      by (rule is_runtime_type_cong_env) (simp_all add: other_eq)
    ultimately show "is_runtime_type (?pEnv \<lparr> TE_TypeVars := fset_of_list tyVars,
                                                TE_RuntimeTypeVars := fset_of_list tyVars \<rparr>) payload"
      by simp
  qed

  have c14: "tyenv_ghost_datatypes_subset ?pEnv"
    using be_ghost_dt_subset
    unfolding tyenv_ghost_datatypes_subset_def
    by (simp add: other_eq)

  have c15: "tyenv_runtime_tyvars_subset ?pEnv"
    using be_rt_subset
    unfolding tyenv_runtime_tyvars_subset_def
    by (simp add: other_eq)

  from c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
  show ?thesis unfolding tyenv_well_formed_def by blast
qed

(* Shape of the sound arg-processing result: the fold either errors soundly
   or produces a state matching body_env_for env funInfo (the callee's static
   env), with IS_TyArgs set to the call-site type substitution. *)
definition sound_arg_processing_result ::
    "CoreTyEnv \<Rightarrow> FunInfo \<Rightarrow> (nat, CoreType) fmap \<Rightarrow> CoreType list
    \<Rightarrow> InterpError + 'w InterpState \<Rightarrow> bool" where
  "sound_arg_processing_result env funInfo tySubst storeTyping result =
    (case result of
      Inl err \<Rightarrow> sound_error_result err
    | Inr preCallState \<Rightarrow>
        IS_TyArgs preCallState = tySubst
        \<and> (\<exists>bodyStoreTyping.
              state_matches_env preCallState (body_env_for env funInfo) bodyStoreTyping
            \<and> storeTyping_extends storeTyping bodyStoreTyping))"

(* Partial variant: after k steps, the state matches partial_body_env_for at k
   with some store typing extending the original, and IS_TyArgs is the
   call-site type substitution (preserved by process_one_arg). *)
definition sound_partial_arg_processing_result ::
    "CoreTyEnv \<Rightarrow> FunInfo \<Rightarrow> (nat, CoreType) fmap \<Rightarrow> nat \<Rightarrow> CoreType list
    \<Rightarrow> InterpError + 'w InterpState \<Rightarrow> bool" where
  "sound_partial_arg_processing_result env funInfo tySubst k storeTyping result =
    (case result of
      Inl err \<Rightarrow> sound_error_result err
    | Inr state \<Rightarrow>
        IS_TyArgs state = tySubst
        \<and> (\<exists>partialStoreTyping.
              state_matches_env state (partial_body_env_for env funInfo k)
                partialStoreTyping
            \<and> storeTyping_extends storeTyping partialStoreTyping))"

(* -------------------------------------------------------------------------- *)
(* H2a. The cleared state matches the k=0 partial body env under the caller's *)
(* store typing (no new slots needed).                                        *)
(* -------------------------------------------------------------------------- *)
(* New shape: the cleared state's IS_TyArgs is set to the call-site tySubst (not
   fmempty), and the partial body env at k=0 inherits TE_RuntimeTypeVars from
   body_env_for (which sets it to fset_of_list (FI_TyArgs funInfo)). Discharging
   ty_args_well_formed therefore requires the call-site assumptions that
   tyArgs are well-kinded + runtime in env and that tySubst is built as
   fmap_of_list (zip (FI_TyArgs funInfo) (map (apply_subst (IS_TyArgs state)) tyArgs)).

   Body of the proof: TODO in subtask 6. *)
lemma cleared_state_matches_partial_env_zero:
  assumes sme: "state_matches_env state env storeTyping"
      and wf: "tyenv_well_formed env"
      and fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo"
      and not_ghost: "FI_Ghost funInfo = NotGhost"
      and ty_len: "length tyArgs = length (FI_TyArgs funInfo)"
      and ty_wk:  "list_all (is_well_kinded env) tyArgs"
      and ty_rt:  "list_all (is_runtime_type env) tyArgs"
      and tySubst_eq:
            "tySubst = fmap_of_list
                         (zip (FI_TyArgs funInfo)
                              (map (apply_subst (IS_TyArgs state)) tyArgs))"
  shows "state_matches_env
           (state \<lparr> IS_Locals := fmempty,
                    IS_Refs := fmempty,
                    IS_ConstLocals := {||},
                    IS_TyArgs := tySubst \<rparr>)
           (partial_body_env_for env funInfo 0)
           storeTyping"
proof -
  let ?clearedState = "state \<lparr> IS_Locals := fmempty,
                                IS_Refs := fmempty,
                                IS_ConstLocals := {||},
                                IS_TyArgs := tySubst \<rparr>"
  let ?pEnv = "partial_body_env_for env funInfo 0"

  \<comment> \<open>Field equations for ?pEnv at k=0. \<close>
  have pEnv_locals: "TE_LocalVars ?pEnv = fmempty"
    by (simp add: partial_body_env_for_def)
  have pEnv_const: "TE_ConstLocals ?pEnv = {||}"
    by (simp add: partial_body_env_for_def)
  have pEnv_ghost_locals: "TE_GhostLocals ?pEnv = {||}"
    by (simp add: partial_body_env_for_def body_env_for_def)
  have pEnv_globals: "TE_GlobalVars ?pEnv = TE_GlobalVars env"
    by (simp add: partial_body_env_for_def body_env_for_def)
  have pEnv_ghost_globals: "TE_GhostGlobals ?pEnv = TE_GhostGlobals env"
    by (simp add: partial_body_env_for_def body_env_for_def)
  have pEnv_funs: "TE_Functions ?pEnv = TE_Functions env"
    by (simp add: partial_body_env_for_def body_env_for_def)
  have pEnv_datatypes: "TE_Datatypes ?pEnv = TE_Datatypes env"
    by (simp add: partial_body_env_for_def body_env_for_def)
  have pEnv_dactors: "TE_DataCtors ?pEnv = TE_DataCtors env"
    by (simp add: partial_body_env_for_def body_env_for_def)
  have pEnv_dactors_by_ty: "TE_DataCtorsByType ?pEnv = TE_DataCtorsByType env"
    by (simp add: partial_body_env_for_def body_env_for_def)
  have pEnv_ghost_dt: "TE_GhostDatatypes ?pEnv = TE_GhostDatatypes env"
    by (simp add: partial_body_env_for_def body_env_for_def)
  have pEnv_tyvars: "TE_TypeVars ?pEnv = fset_of_list (FI_TyArgs funInfo)"
    by (simp add: partial_body_env_for_def body_env_for_def)
  have pEnv_rt_tyvars: "TE_RuntimeTypeVars ?pEnv = fset_of_list (FI_TyArgs funInfo)"
    by (simp add: partial_body_env_for_def body_env_for_def)

  \<comment> \<open>Well-formedness of ?pEnv. Since partial_body_env_for at k=0 has same field
      structure as body_env_for for everything that well-formedness cares about
      (the local-related fields don't appear in tyenv_well_formed), we get this
      via a separate lemma. Actually easier: derive from body_env_for_well_formed
      after observing pEnv equals body_env_for with empty locals. \<close>
  \<comment> \<open>Strategy: skip wf_pEnv unless we need it. \<close>

  \<comment> \<open>Extract conjuncts from the source state_matches_env. \<close>
  from sme have
    lv_src: "local_vars_exist_in_state state env storeTyping" and
    gv_src: "global_vars_exist_in_state state env" and
    no_lv_src: "no_extra_local_vars state env" and
    no_gv_src: "no_extra_global_vars state env" and
    fes_src: "funs_exist_in_state state env" and
    no_fun_src: "no_extra_funs state env" and
    nc_src: "non_consts_in_locals_or_refs state env" and
    cn_src: "const_locals_match state env" and
    swt_src: "store_well_typed state env storeTyping" and
    ta_src: "ty_args_well_formed state env"
    unfolding state_matches_env_def by blast+

  \<comment> \<open>(a) Discharge value_has_type congruence for ground types. This is the
      replacement for the old value_has_type_cong_env step, which required
      TE_TypeVars / TE_RuntimeTypeVars equality. Here we have those fields
      differing — but we'll only ever transfer value_has_type for values that
      satisfy value_has_type, whose types are ground (by value_has_type_ground),
      so we can use the ground-only cong lemmas.

      Concretely, the wk/rt of a ground type doesn't depend on tyvar fields:
      we use is_well_kinded_ground_cong_env and is_runtime_type_ground_cong_env
      to show wk/rt in ?pEnv given wk/rt in env (which we get from
      value_has_type_well_kinded / value_has_type_runtime). \<close>
  have vht_to_pEnv: "\<And>v t. value_has_type env v t \<Longrightarrow> value_has_type ?pEnv v t"
  proof -
    fix v t assume vht: "value_has_type env v t"
    have ground: "type_tyvars t = {}" using value_has_type_ground[OF vht] .
    have wk_env: "is_well_kinded env t" using value_has_type_well_kinded[OF vht wf] .
    have rt_env: "is_runtime_type env t" using value_has_type_runtime[OF vht] .
    have wk_pEnv: "is_well_kinded ?pEnv t"
      using wk_env is_well_kinded_ground_cong_env[OF ground, of ?pEnv env]
            pEnv_datatypes by simp
    have rt_pEnv: "is_runtime_type ?pEnv t"
      using rt_env is_runtime_type_ground_cong_env[OF ground, of ?pEnv env]
            pEnv_ghost_dt by simp
    have wf_pEnv: "tyenv_well_formed ?pEnv"
      using partial_body_env_for_well_formed[OF wf fn_lookup not_ghost] .
    show "value_has_type ?pEnv v t"
      using value_has_type_cong_env_wk
              [OF pEnv_dactors pEnv_datatypes pEnv_ghost_dt wf wf_pEnv
                  wk_env wk_pEnv rt_env rt_pEnv vht] .
  qed

  \<comment> \<open>Discharge each conjunct of state_matches_env for the cleared state and ?pEnv. \<close>

  have lv_tgt: "local_vars_exist_in_state ?clearedState ?pEnv storeTyping"
    unfolding local_vars_exist_in_state_def pEnv_locals by simp

  have gv_tgt: "global_vars_exist_in_state ?clearedState ?pEnv"
    unfolding global_vars_exist_in_state_def
  proof (intro allI impI, elim conjE)
    fix name ty
    assume lk_pEnv: "fmlookup (TE_GlobalVars ?pEnv) name = Some ty"
       and ng_pEnv: "name |\<notin>| TE_GhostGlobals ?pEnv"
    from lk_pEnv have lk_env: "fmlookup (TE_GlobalVars env) name = Some ty"
      by (simp add: pEnv_globals)
    from ng_pEnv have ng_env: "name |\<notin>| TE_GhostGlobals env"
      by (simp add: pEnv_ghost_globals)
    from gv_src lk_env ng_env have gvst:
      "global_var_in_state_with_type state env name ty"
      unfolding global_vars_exist_in_state_def by blast
    from gvst obtain val where
      lkup_g: "fmlookup (IS_Globals state) name = Some val" and
      vht_env: "value_has_type env val ty"
      unfolding global_var_in_state_with_type_def
      by (cases "fmlookup (IS_Globals state) name") auto
    from vht_to_pEnv[OF vht_env] have vht_pEnv: "value_has_type ?pEnv val ty" .
    show "global_var_in_state_with_type ?clearedState ?pEnv name ty"
      unfolding global_var_in_state_with_type_def using lkup_g vht_pEnv by simp
  qed

  have no_lv_tgt: "no_extra_local_vars ?clearedState ?pEnv"
    unfolding no_extra_local_vars_def by simp

  have no_gv_tgt: "no_extra_global_vars ?clearedState ?pEnv"
    using no_gv_src pEnv_globals pEnv_ghost_globals
    unfolding no_extra_global_vars_def
    by simp

  \<comment> \<open>funs_exist_in_state: TE_Functions is inherited from env. The Inl
      (Babylon-body) case of fun_info_matches_interp_fun transfers because
      body_env_for env info' = body_env_for ?pEnv info' (via body_env_for_cong
      on the global-only fields). The Inr (extern) case transfers because the
      strengthened extern_fun_contract restricts tySubst's range to ground types,
      so is_well_kinded / is_runtime_type / value_has_type are env-tyvar-invariant
      via the ground-cong lemmas. \<close>
  have fes_tgt: "funs_exist_in_state ?clearedState ?pEnv"
    unfolding funs_exist_in_state_def
  proof (intro allI impI)
    fix name info'
    assume A: "fmlookup (TE_Functions ?pEnv) name = Some info' \<and> FI_Ghost info' = NotGhost"
    from A have lookup: "fmlookup (TE_Functions env) name = Some info'"
      and nghost: "FI_Ghost info' = NotGhost"
      by (simp_all add: pEnv_funs)
    from fes_src lookup nghost have outer:
      "case fmlookup (IS_Functions state) name of None \<Rightarrow> False
       | Some interpFun \<Rightarrow> fun_info_matches_interp_fun env info' interpFun"
      unfolding funs_exist_in_state_def by blast
    show "case fmlookup (IS_Functions ?clearedState) name of None \<Rightarrow> False
          | Some interpFun \<Rightarrow> fun_info_matches_interp_fun ?pEnv info' interpFun"
    proof (cases "fmlookup (IS_Functions state) name")
      case None
      with outer show ?thesis by simp
    next
      case (Some interpFun)
      with outer have fim:
        "fun_info_matches_interp_fun env info' interpFun" by simp
      \<comment> \<open>Transfer fun_info_matches_interp_fun from env to ?pEnv. \<close>
      \<comment> \<open>Step 1: the equality on non-body components. \<close>
      from fim have non_body_eqs:
        "FI_TyArgs info' = IF_TyArgs interpFun"
        "length (FI_TmArgs info') = length (IF_Args interpFun)"
        "list_all2 (\<lambda>(name1, _, vor1) (name2, vor2). name1 = name2 \<and> vor1 = vor2)
                   (FI_TmArgs info') (IF_Args interpFun)"
        "FI_Impure info' = IF_Impure interpFun"
        unfolding fun_info_matches_interp_fun_def by simp_all
      \<comment> \<open>Step 2: body match transfers. \<close>
      have body_match:
        "(case IF_Body interpFun of
            Inl bodyStmts \<Rightarrow>
              (\<exists>env''. core_statement_list_type (body_env_for ?pEnv info') NotGhost bodyStmts
                          = Some env'')
          | Inr externFun \<Rightarrow> extern_fun_contract ?pEnv info' externFun)"
      proof (cases "IF_Body interpFun")
        case (Inl bodyStmts)
        with fim have
          "\<exists>env''. core_statement_list_type (body_env_for env info') NotGhost bodyStmts
                    = Some env''"
          unfolding fun_info_matches_interp_fun_def by simp
        moreover have "body_env_for env info' = body_env_for ?pEnv info'"
          by (rule body_env_for_cong[symmetric])
             (simp_all add: pEnv_globals pEnv_ghost_globals pEnv_funs
                            pEnv_datatypes pEnv_dactors pEnv_dactors_by_ty pEnv_ghost_dt)
        ultimately show ?thesis using Inl by simp
      next
        case (Inr externFun)
        with fim have ext_env:
          "extern_fun_contract env info' externFun"
          unfolding fun_info_matches_interp_fun_def by simp
        \<comment> \<open>Transfer to ?pEnv. With the strengthened contract (ground range),
            wk/rt/value_has_type are env-tyvar-invariant via ground-cong. \<close>
        have wf_pEnv: "tyenv_well_formed ?pEnv"
          using partial_body_env_for_well_formed[OF wf fn_lookup not_ghost] .
        have ext_pEnv: "extern_fun_contract ?pEnv info' externFun"
          unfolding extern_fun_contract_def
        proof (intro allI impI, elim conjE)
          fix tySubst' world vals
          assume sub_dom: "fmdom tySubst' = fset_of_list (FI_TyArgs info')"
            and sub_range: "\<forall>ty' \<in> fmran' tySubst'.
                              type_tyvars ty' = {}
                              \<and> is_well_kinded ?pEnv ty'
                              \<and> is_runtime_type ?pEnv ty'"
            and vals_typed_pEnv:
              "list_all2 (value_has_type ?pEnv) vals
                         (map (\<lambda>(_, ty, _). apply_subst tySubst' ty) (FI_TmArgs info'))"
          \<comment> \<open>Transfer the premises to env via ground-cong. \<close>
          have sub_range_env: "\<forall>ty' \<in> fmran' tySubst'.
                              type_tyvars ty' = {}
                              \<and> is_well_kinded env ty'
                              \<and> is_runtime_type env ty'"
          proof
            fix ty' assume mem: "ty' \<in> fmran' tySubst'"
            with sub_range have ground: "type_tyvars ty' = {}"
              and wk_pEnv: "is_well_kinded ?pEnv ty'"
              and rt_pEnv: "is_runtime_type ?pEnv ty'" by auto
            have wk_env: "is_well_kinded env ty'"
              using wk_pEnv
                    is_well_kinded_ground_cong_env[OF ground, of env ?pEnv]
                    pEnv_datatypes
              by simp
            have rt_env: "is_runtime_type env ty'"
              using rt_pEnv
                    is_runtime_type_ground_cong_env[OF ground, of env ?pEnv]
                    pEnv_ghost_dt
              by simp
            show "type_tyvars ty' = {} \<and> is_well_kinded env ty' \<and> is_runtime_type env ty'"
              using ground wk_env rt_env by simp
          qed
          \<comment> \<open>For value_has_type: each argument type is apply_subst tySubst' (paramTy).
              paramTy's tyvars are bounded by FI_TyArgs info' = fmdom tySubst', so the
              substituted type's tyvars come from tySubst's range, which is ground.
              Hence value_has_type ?pEnv = value_has_type env via cong_env_wk. \<close>
          have vals_typed_env:
            "list_all2 (value_has_type env) vals
                       (map (\<lambda>(_, ty, _). apply_subst tySubst' ty) (FI_TmArgs info'))"
          proof -
            \<comment> \<open>Each arg-type (after applying tySubst') is ground (since tySubst's
                range is ground and paramTy's tyvars are in FI_TyArgs info' = fmdom tySubst'). \<close>
            have arg_ground:
              "\<forall>arg_ty \<in> set (map (\<lambda>(_, ty, _). apply_subst tySubst' ty) (FI_TmArgs info')).
                  type_tyvars arg_ty = {}"
            proof
              fix arg_ty
              assume "arg_ty \<in> set (map (\<lambda>(_, ty, _). apply_subst tySubst' ty) (FI_TmArgs info'))"
              then obtain n t v where in_args: "(n, t, v) \<in> set (FI_TmArgs info')"
                and arg_eq: "arg_ty = apply_subst tySubst' t"
                by auto
              \<comment> \<open>t's tyvars are in fset_of_list (FI_TyArgs info') = fmdom tySubst'. \<close>
              from wf fn_lookup have fg: "tyenv_fun_ghost_constraint env"
                unfolding tyenv_well_formed_def by simp
              from fg lookup nghost have args_rt:
                "\<forall>ty'' \<in> (fst \<circ> snd) ` set (FI_TmArgs info').
                    is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info'),
                                           TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info') \<rparr>)
                                    ty''"
                unfolding tyenv_fun_ghost_constraint_def Let_def by blast
              from in_args have "t \<in> (fst \<circ> snd) ` set (FI_TmArgs info')" by force
              with args_rt have
                "is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info'),
                                       TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info') \<rparr>)
                                  t" by blast
              from is_runtime_type_tyvars_subset[OF this]
              have t_tyvars: "type_tyvars t \<subseteq> fset (fset_of_list (FI_TyArgs info'))" by simp
              hence t_in_dom: "type_tyvars t \<subseteq> fset (fmdom tySubst')"
                using sub_dom by simp
              \<comment> \<open>tySubst's range is ground. \<close>
              have sub_range_ground: "subst_range_tyvars tySubst' = {}"
                using sub_range unfolding subst_range_tyvars_def by force
              have "type_tyvars (apply_subst tySubst' t)
                      \<subseteq> (type_tyvars t - fset (fmdom tySubst'))
                        \<union> subst_range_tyvars tySubst'"
                by (rule apply_subst_tyvars_result)
              also have "\<dots> = {}" using t_in_dom sub_range_ground by auto
              finally show "type_tyvars arg_ty = {}" using arg_eq by simp
            qed
            \<comment> \<open>Each value satisfies value_has_type ?pEnv val arg_ty; we want it under env.
                The transfer is via value_has_type_cong_env_wk + ground-cong on wk/rt. \<close>
            from vals_typed_pEnv have len_vals:
              "length vals = length (FI_TmArgs info')"
              by (auto dest: list_all2_lengthD)
            have vals_typed_pointwise:
              "\<forall>i < length vals. value_has_type ?pEnv (vals ! i)
                                   ((map (\<lambda>(_, ty, _). apply_subst tySubst' ty) (FI_TmArgs info')) ! i)"
              using vals_typed_pEnv
              by (auto simp: list_all2_conv_all_nth)
            have vals_typed_env_pointwise:
              "\<forall>i < length vals. value_has_type env (vals ! i)
                                   ((map (\<lambda>(_, ty, _). apply_subst tySubst' ty) (FI_TmArgs info')) ! i)"
            proof (intro allI impI)
              fix i assume i_lt: "i < length vals"
              with len_vals have i_fi: "i < length (FI_TmArgs info')" by simp
              let ?arg_ty = "(map (\<lambda>(_, ty, _). apply_subst tySubst' ty) (FI_TmArgs info')) ! i"
              from vals_typed_pointwise i_lt have vht_pEnv:
                "value_has_type ?pEnv (vals ! i) ?arg_ty" by blast
              \<comment> \<open>?arg_ty is in the list, so ground. \<close>
              have arg_ty_in:
                "?arg_ty \<in> set (map (\<lambda>(_, ty, _). apply_subst tySubst' ty) (FI_TmArgs info'))"
                using i_fi by simp
              with arg_ground have arg_ty_ground: "type_tyvars ?arg_ty = {}" by blast
              \<comment> \<open>Transfer via value_has_type_cong_env_wk. \<close>
              from value_has_type_well_kinded[OF vht_pEnv wf_pEnv]
              have wk_pEnv: "is_well_kinded ?pEnv ?arg_ty" .
              from value_has_type_runtime[OF vht_pEnv]
              have rt_pEnv: "is_runtime_type ?pEnv ?arg_ty" .
              have wk_env: "is_well_kinded env ?arg_ty"
                using wk_pEnv
                      is_well_kinded_ground_cong_env[OF arg_ty_ground, of env ?pEnv]
                      pEnv_datatypes
                by simp
              have rt_env: "is_runtime_type env ?arg_ty"
                using rt_pEnv
                      is_runtime_type_ground_cong_env[OF arg_ty_ground, of env ?pEnv]
                      pEnv_ghost_dt
                by simp
              show "value_has_type env (vals ! i) ?arg_ty"
                using value_has_type_cong_env_wk
                        [OF pEnv_dactors[symmetric] pEnv_datatypes[symmetric]
                            pEnv_ghost_dt[symmetric] wf_pEnv wf
                            wk_pEnv wk_env rt_pEnv rt_env vht_pEnv] .
            qed
            show ?thesis
              unfolding list_all2_conv_all_nth
              using vals_typed_env_pointwise len_vals by auto
          qed
          \<comment> \<open>Apply the env-version of the contract. \<close>
          from ext_env have ext_env_inst:
            "fmdom tySubst' = fset_of_list (FI_TyArgs info') \<and>
             (\<forall>ty' \<in> fmran' tySubst'.
                  type_tyvars ty' = {} \<and> is_well_kinded env ty' \<and> is_runtime_type env ty') \<and>
             list_all2 (value_has_type env) vals
                       (map (\<lambda>(_, ty, _). apply_subst tySubst' ty) (FI_TmArgs info'))
             \<longrightarrow> (case externFun world vals of
                    (newWorld, refUpdates, retVal) \<Rightarrow>
                      value_has_type env retVal (apply_subst tySubst' (FI_ReturnType info')) \<and>
                      list_all2 (value_has_type env) refUpdates
                        (map (\<lambda>(_, ty, _). apply_subst tySubst' ty)
                             (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs info'))))"
            unfolding extern_fun_contract_def by presburger
          from ext_env_inst sub_dom sub_range_env vals_typed_env
          have env_post:
            "case externFun world vals of
               (newWorld, refUpdates, retVal) \<Rightarrow>
                 value_has_type env retVal (apply_subst tySubst' (FI_ReturnType info')) \<and>
                 list_all2 (value_has_type env) refUpdates
                   (map (\<lambda>(_, ty, _). apply_subst tySubst' ty)
                        (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs info')))"
            by simp
          \<comment> \<open>Transfer back to ?pEnv. The return type's tyvars are in FI_TyArgs info'
              = fmdom tySubst', so apply_subst tySubst' (FI_ReturnType info') is ground.
              Similarly for ref-update types. \<close>
          obtain newWorld refUpdates retVal where
            ext_call: "externFun world vals = (newWorld, refUpdates, retVal)"
            by (cases "externFun world vals") auto
          from env_post ext_call have env_post_unfold:
            "value_has_type env retVal (apply_subst tySubst' (FI_ReturnType info')) \<and>
             list_all2 (value_has_type env) refUpdates
               (map (\<lambda>(_, ty, _). apply_subst tySubst' ty)
                    (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs info')))"
            by simp
          \<comment> \<open>Now transfer retVal typing and refUpdates typing to ?pEnv. \<close>
          have ret_ground: "type_tyvars (apply_subst tySubst' (FI_ReturnType info')) = {}"
          proof -
            from wf fn_lookup have fg: "tyenv_fun_ghost_constraint env"
              unfolding tyenv_well_formed_def by simp
            from fg lookup nghost have ret_rt:
              "is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info'),
                                     TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info') \<rparr>)
                                (FI_ReturnType info')"
              unfolding tyenv_fun_ghost_constraint_def Let_def by blast
            from is_runtime_type_tyvars_subset[OF ret_rt]
            have ret_tv: "type_tyvars (FI_ReturnType info') \<subseteq> fset (fset_of_list (FI_TyArgs info'))"
              by simp
            hence ret_in_dom: "type_tyvars (FI_ReturnType info') \<subseteq> fset (fmdom tySubst')"
              using sub_dom by simp
            have sub_range_ground: "subst_range_tyvars tySubst' = {}"
              using sub_range unfolding subst_range_tyvars_def by force
            have "type_tyvars (apply_subst tySubst' (FI_ReturnType info'))
                    \<subseteq> (type_tyvars (FI_ReturnType info') - fset (fmdom tySubst'))
                      \<union> subst_range_tyvars tySubst'"
              by (rule apply_subst_tyvars_result)
            also have "\<dots> = {}" using ret_in_dom sub_range_ground by auto
            finally show ?thesis by simp
          qed
          \<comment> \<open>retVal typing transfers. \<close>
          from env_post_unfold have ret_typed_env:
            "value_has_type env retVal (apply_subst tySubst' (FI_ReturnType info'))" by simp
          from value_has_type_well_kinded[OF ret_typed_env wf]
          have ret_wk_env: "is_well_kinded env (apply_subst tySubst' (FI_ReturnType info'))" .
          from value_has_type_runtime[OF ret_typed_env]
          have ret_rt_env: "is_runtime_type env (apply_subst tySubst' (FI_ReturnType info'))" .
          have ret_wk_pEnv: "is_well_kinded ?pEnv (apply_subst tySubst' (FI_ReturnType info'))"
            using ret_wk_env
                  is_well_kinded_ground_cong_env[OF ret_ground, of ?pEnv env]
                  pEnv_datatypes
            by simp
          have ret_rt_pEnv: "is_runtime_type ?pEnv (apply_subst tySubst' (FI_ReturnType info'))"
            using ret_rt_env
                  is_runtime_type_ground_cong_env[OF ret_ground, of ?pEnv env]
                  pEnv_ghost_dt
            by simp
          have ret_typed_pEnv: "value_has_type ?pEnv retVal (apply_subst tySubst' (FI_ReturnType info'))"
            using value_has_type_cong_env_wk
                    [OF pEnv_dactors pEnv_datatypes pEnv_ghost_dt wf wf_pEnv
                        ret_wk_env ret_wk_pEnv ret_rt_env ret_rt_pEnv ret_typed_env] .
          \<comment> \<open>refUpdates typing transfers. Each ref-update has type apply_subst tySubst' ty
              for a Ref-position FI_TmArg's ty. Same groundness argument as for paramTy. \<close>
          from env_post_unfold have refUpdates_typed_env:
            "list_all2 (value_has_type env) refUpdates
               (map (\<lambda>(_, ty, _). apply_subst tySubst' ty)
                    (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs info')))" by simp
          have refUpdates_typed_pEnv:
            "list_all2 (value_has_type ?pEnv) refUpdates
               (map (\<lambda>(_, ty, _). apply_subst tySubst' ty)
                    (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs info')))"
          proof -
            from refUpdates_typed_env have len_ref:
              "length refUpdates
                = length (map (\<lambda>(_, ty, _). apply_subst tySubst' ty)
                              (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs info')))"
              by (auto dest: list_all2_lengthD)
            \<comment> \<open>Each ref-arg-type (after apply_subst tySubst') is ground (same arg as before). \<close>
            have ref_arg_ground:
              "\<forall>arg_ty \<in> set (map (\<lambda>(_, ty, _). apply_subst tySubst' ty)
                                   (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs info'))).
                  type_tyvars arg_ty = {}"
            proof
              fix arg_ty
              assume "arg_ty \<in> set (map (\<lambda>(_, ty, _). apply_subst tySubst' ty)
                                        (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs info')))"
              then obtain n t v where in_filter:
                "(n, t, v) \<in> set (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs info'))"
                and arg_eq: "arg_ty = apply_subst tySubst' t"
                by auto
              from in_filter have in_args: "(n, t, v) \<in> set (FI_TmArgs info')" by auto
              from wf fn_lookup have fg: "tyenv_fun_ghost_constraint env"
                unfolding tyenv_well_formed_def by simp
              from fg lookup nghost have args_rt:
                "\<forall>ty'' \<in> (fst \<circ> snd) ` set (FI_TmArgs info').
                    is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info'),
                                           TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info') \<rparr>)
                                    ty''"
                unfolding tyenv_fun_ghost_constraint_def Let_def by blast
              from in_args have "t \<in> (fst \<circ> snd) ` set (FI_TmArgs info')" by force
              with args_rt have
                "is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info'),
                                       TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info') \<rparr>)
                                  t" by blast
              from is_runtime_type_tyvars_subset[OF this]
              have t_tyvars: "type_tyvars t \<subseteq> fset (fset_of_list (FI_TyArgs info'))" by simp
              hence t_in_dom: "type_tyvars t \<subseteq> fset (fmdom tySubst')"
                using sub_dom by simp
              have sub_range_ground: "subst_range_tyvars tySubst' = {}"
                using sub_range unfolding subst_range_tyvars_def by force
              have "type_tyvars (apply_subst tySubst' t)
                      \<subseteq> (type_tyvars t - fset (fmdom tySubst'))
                        \<union> subst_range_tyvars tySubst'"
                by (rule apply_subst_tyvars_result)
              also have "\<dots> = {}" using t_in_dom sub_range_ground by auto
              finally show "type_tyvars arg_ty = {}" using arg_eq by simp
            qed
            \<comment> \<open>Pointwise transfer via value_has_type_cong_env_wk. \<close>
            from refUpdates_typed_env have vh_pointwise:
              "\<forall>i < length refUpdates. value_has_type env (refUpdates ! i)
                  ((map (\<lambda>(_, ty, _). apply_subst tySubst' ty)
                        (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs info'))) ! i)"
              by (auto simp: list_all2_conv_all_nth)
            have vh_pEnv_pointwise:
              "\<forall>i < length refUpdates. value_has_type ?pEnv (refUpdates ! i)
                  ((map (\<lambda>(_, ty, _). apply_subst tySubst' ty)
                        (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs info'))) ! i)"
            proof (intro allI impI)
              fix i assume i_lt: "i < length refUpdates"
              with len_ref have i_lt_map:
                "i < length (map (\<lambda>(_, ty, _). apply_subst tySubst' ty)
                                 (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs info')))"
                by simp
              let ?arg_ty = "(map (\<lambda>(_, ty, _). apply_subst tySubst' ty)
                                  (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs info'))) ! i"
              from vh_pointwise i_lt have vht_env:
                "value_has_type env (refUpdates ! i) ?arg_ty" by blast
              have arg_ty_in:
                "?arg_ty \<in> set (map (\<lambda>(_, ty, _). apply_subst tySubst' ty)
                                    (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs info')))"
                using i_lt_map nth_mem by blast
              with ref_arg_ground have arg_ty_ground: "type_tyvars ?arg_ty = {}" by blast
              from value_has_type_well_kinded[OF vht_env wf]
              have wk_env: "is_well_kinded env ?arg_ty" .
              from value_has_type_runtime[OF vht_env]
              have rt_env: "is_runtime_type env ?arg_ty" .
              have wk_pEnv: "is_well_kinded ?pEnv ?arg_ty"
                using wk_env
                      is_well_kinded_ground_cong_env[OF arg_ty_ground, of ?pEnv env]
                      pEnv_datatypes
                by simp
              have rt_pEnv: "is_runtime_type ?pEnv ?arg_ty"
                using rt_env
                      is_runtime_type_ground_cong_env[OF arg_ty_ground, of ?pEnv env]
                      pEnv_ghost_dt
                by simp
              show "value_has_type ?pEnv (refUpdates ! i) ?arg_ty"
                using value_has_type_cong_env_wk
                        [OF pEnv_dactors pEnv_datatypes pEnv_ghost_dt wf wf_pEnv
                            wk_env wk_pEnv rt_env rt_pEnv vht_env] .
            qed
            show ?thesis
              unfolding list_all2_conv_all_nth
              using vh_pEnv_pointwise len_ref by auto
          qed
          show "case externFun world vals of
                  (newWorld, refUpdates, retVal) \<Rightarrow>
                    value_has_type ?pEnv retVal (apply_subst tySubst' (FI_ReturnType info')) \<and>
                    list_all2 (value_has_type ?pEnv) refUpdates
                      (map (\<lambda>(_, ty, _). apply_subst tySubst' ty)
                           (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs info')))"
            using ret_typed_pEnv refUpdates_typed_pEnv ext_call by simp
        qed
        show ?thesis using Inr ext_pEnv by simp
      qed
      \<comment> \<open>Combine. \<close>
      from non_body_eqs body_match have fim_pEnv:
        "fun_info_matches_interp_fun ?pEnv info' interpFun"
        unfolding fun_info_matches_interp_fun_def by simp
      show ?thesis using Some fim_pEnv by simp
    qed
  qed

  have no_fun_tgt: "no_extra_funs ?clearedState ?pEnv"
    using no_fun_src pEnv_funs
    unfolding no_extra_funs_def
    by simp

  have nc_tgt: "non_consts_in_locals_or_refs ?clearedState ?pEnv"
    unfolding non_consts_in_locals_or_refs_def pEnv_locals by simp

  have cn_tgt: "const_locals_match ?clearedState ?pEnv"
    unfolding const_locals_match_def pEnv_const by simp

  \<comment> \<open>store_well_typed: the store is unchanged; values' types are ground (by
      value_has_type_ground), so we can use the ground-cong machinery via
      vht_to_pEnv. \<close>
  have swt_tgt: "store_well_typed ?clearedState ?pEnv storeTyping"
    using swt_src vht_to_pEnv
    unfolding store_well_typed_def by simp

  \<comment> \<open>ty_args_well_formed: domain matches FI_TyArgs (= TE_RuntimeTypeVars ?pEnv).
      Range is ground (composed substitution of ground IS_TyArgs state on tyArgs).
      Range is well-kinded + runtime in ?pEnv (ground, transports via ground-cong). \<close>

  \<comment> \<open>Extract well-formedness invariants on the caller's IS_TyArgs. \<close>
  from ta_src have
    dom_caller: "fmdom (IS_TyArgs state) = TE_RuntimeTypeVars env" and
    range_ground: "subst_range_tyvars (IS_TyArgs state) = {}" and
    range_wk_rt: "\<forall>ty \<in> fmran' (IS_TyArgs state).
                    is_well_kinded env ty \<and> is_runtime_type env ty"
    unfolding ty_args_well_formed_def by auto

  \<comment> \<open>Distinctness of FI_TyArgs from env's well-formedness. \<close>
  from wf fn_lookup have fi_ty_dist: "distinct (FI_TyArgs funInfo)"
    unfolding tyenv_well_formed_def tyenv_fun_tyvars_distinct_def by blast

  \<comment> \<open>(a) fmdom tySubst = fset_of_list (FI_TyArgs funInfo) = TE_RuntimeTypeVars ?pEnv. \<close>
  have fmdom_tySubst: "fmdom tySubst = fset_of_list (FI_TyArgs funInfo)"
  proof -
    have len_map: "length (FI_TyArgs funInfo)
                   = length (map (apply_subst (IS_TyArgs state)) tyArgs)"
      using ty_len by simp
    show ?thesis
      using tySubst_eq
      by (simp add: len_map fset_of_list.rep_eq)
  qed
  have dom_tgt: "fmdom (IS_TyArgs ?clearedState) = TE_RuntimeTypeVars ?pEnv"
    using fmdom_tySubst pEnv_rt_tyvars by simp

  \<comment> \<open>(b) range of tySubst is ground. \<close>
  \<comment> \<open>Each element in the range is apply_subst (IS_TyArgs state) ty_i for some i.
      By is_runtime_type env ty_i (from ty_rt), tyvars(ty_i) \<subseteq> RuntimeTypeVars env =
      fmdom (IS_TyArgs state). By apply_subst_tyvars_result and range_ground, the
      result has empty tyvars. \<close>
  have range_subst_ground:
    "\<forall>ty \<in> fmran' tySubst. type_tyvars ty = {}"
  proof
    fix ty assume "ty \<in> fmran' tySubst"
    then obtain n where lk: "fmlookup tySubst n = Some ty"
      by (auto simp: fmran'_alt_def fmlookup_dom_iff)
    \<comment> \<open>ty is an element of map (apply_subst (IS_TyArgs state)) tyArgs at some index. \<close>
    from lk tySubst_eq have lk':
      "fmlookup (fmap_of_list (zip (FI_TyArgs funInfo)
                  (map (apply_subst (IS_TyArgs state)) tyArgs))) n = Some ty"
      by simp
    hence "map_of (zip (FI_TyArgs funInfo)
              (map (apply_subst (IS_TyArgs state)) tyArgs)) n = Some ty"
      by (simp add: fmap_of_list.rep_eq)
    hence "(n, ty) \<in> set (zip (FI_TyArgs funInfo)
                            (map (apply_subst (IS_TyArgs state)) tyArgs))"
      by (rule map_of_SomeD)
    then obtain i where i_bound: "i < length (FI_TyArgs funInfo)"
      and ty_eq: "ty = apply_subst (IS_TyArgs state) (tyArgs ! i)"
      and i_bound_ty: "i < length tyArgs"
      using ty_len by (auto simp: set_zip)
    \<comment> \<open>tyvars(tyArgs ! i) \<subseteq> TE_RuntimeTypeVars env = fmdom(IS_TyArgs state). \<close>
    from ty_rt i_bound_ty have "is_runtime_type env (tyArgs ! i)"
      by (simp add: list_all_length)
    from is_runtime_type_tyvars_subset[OF this]
    have "type_tyvars (tyArgs ! i) \<subseteq> fset (TE_RuntimeTypeVars env)" .
    hence subset_dom: "type_tyvars (tyArgs ! i) \<subseteq> fset (fmdom (IS_TyArgs state))"
      using dom_caller by simp
    \<comment> \<open>Now apply_subst_tyvars_result. \<close>
    have "type_tyvars (apply_subst (IS_TyArgs state) (tyArgs ! i))
            \<subseteq> (type_tyvars (tyArgs ! i) - fset (fmdom (IS_TyArgs state)))
              \<union> subst_range_tyvars (IS_TyArgs state)"
      by (rule apply_subst_tyvars_result)
    also have "\<dots> = {}"
      using subset_dom range_ground by auto
    finally show "type_tyvars ty = {}" using ty_eq by simp
  qed

  have range_ground_tgt: "subst_range_tyvars (IS_TyArgs ?clearedState) = {}"
    unfolding subst_range_tyvars_def
    using range_subst_ground by auto

  \<comment> \<open>(c) range of tySubst is well-kinded + runtime in ?pEnv.
      Each entry t = apply_subst (IS_TyArgs state) ty_i is well-kinded + runtime
      in env (by apply_subst_preserves_well_kinded / apply_subst_preserves_runtime
      with src = tgt = env). Since t is ground (range_subst_ground), is_well_kinded
      and is_runtime_type don't depend on tyvar fields, so they transfer to ?pEnv
      via the ground-cong lemmas. \<close>
  have range_wk_rt_tgt:
    "\<forall>ty \<in> fmran' (IS_TyArgs ?clearedState).
         is_well_kinded ?pEnv ty \<and> is_runtime_type ?pEnv ty"
  proof
    fix ty assume mem: "ty \<in> fmran' (IS_TyArgs ?clearedState)"
    hence mem_tySubst: "ty \<in> fmran' tySubst" by simp
    \<comment> \<open>ty is ground. \<close>
    from mem_tySubst range_subst_ground have ground: "type_tyvars ty = {}" by simp
    \<comment> \<open>ty = apply_subst (IS_TyArgs state) (tyArgs ! i) for some i. \<close>
    from mem_tySubst obtain n where lk: "fmlookup tySubst n = Some ty"
      by (auto simp: fmran'_alt_def fmlookup_dom_iff)
    from lk tySubst_eq
    have "map_of (zip (FI_TyArgs funInfo)
              (map (apply_subst (IS_TyArgs state)) tyArgs)) n = Some ty"
      by (simp add: fmap_of_list.rep_eq)
    hence "(n, ty) \<in> set (zip (FI_TyArgs funInfo)
                            (map (apply_subst (IS_TyArgs state)) tyArgs))"
      by (rule map_of_SomeD)
    then obtain i where i_ty: "i < length tyArgs"
      and ty_eq: "ty = apply_subst (IS_TyArgs state) (tyArgs ! i)"
      using ty_len by (auto simp: set_zip)
    \<comment> \<open>Get is_well_kinded env (tyArgs ! i) and is_runtime_type env (tyArgs ! i). \<close>
    from ty_wk i_ty have wk_i: "is_well_kinded env (tyArgs ! i)"
      by (simp add: list_all_length)
    from ty_rt i_ty have rt_i: "is_runtime_type env (tyArgs ! i)"
      by (simp add: list_all_length)
    \<comment> \<open>The range elements of IS_TyArgs state are well-kinded + runtime in env. \<close>
    have wk_range:
      "\<And>n. n |\<in>| TE_TypeVars env \<Longrightarrow>
            (case fmlookup (IS_TyArgs state) n of
               Some ty' \<Rightarrow> is_well_kinded env ty'
             | None \<Rightarrow> n |\<in>| TE_TypeVars env)"
    proof -
      fix n assume "n |\<in>| TE_TypeVars env"
      show "case fmlookup (IS_TyArgs state) n of
              Some ty' \<Rightarrow> is_well_kinded env ty'
            | None \<Rightarrow> n |\<in>| TE_TypeVars env"
        using range_wk_rt
        by (cases "fmlookup (IS_TyArgs state) n")
           (auto simp: \<open>n |\<in>| TE_TypeVars env\<close> fmran'I)
    qed
    have wk_apply_env: "is_well_kinded env (apply_subst (IS_TyArgs state) (tyArgs ! i))"
      using apply_subst_preserves_well_kinded[OF wk_i refl wk_range] .
    have rt_range:
      "\<And>n. n |\<in>| TE_RuntimeTypeVars env \<Longrightarrow>
            (case fmlookup (IS_TyArgs state) n of
               Some ty' \<Rightarrow> is_runtime_type env ty'
             | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars env)"
    proof -
      fix n assume "n |\<in>| TE_RuntimeTypeVars env"
      show "case fmlookup (IS_TyArgs state) n of
              Some ty' \<Rightarrow> is_runtime_type env ty'
            | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars env"
        using range_wk_rt
        by (cases "fmlookup (IS_TyArgs state) n")
           (auto simp: \<open>n |\<in>| TE_RuntimeTypeVars env\<close> fmran'I)
    qed
    have rt_apply_env: "is_runtime_type env (apply_subst (IS_TyArgs state) (tyArgs ! i))"
      using apply_subst_preserves_runtime[OF rt_i refl rt_range] .
    \<comment> \<open>Transport to ?pEnv via ground-cong. \<close>
    have wk_pEnv: "is_well_kinded ?pEnv ty"
      using wk_apply_env ty_eq
            is_well_kinded_ground_cong_env[OF ground, of ?pEnv env]
            pEnv_datatypes
      by simp
    have rt_pEnv: "is_runtime_type ?pEnv ty"
      using rt_apply_env ty_eq
            is_runtime_type_ground_cong_env[OF ground, of ?pEnv env]
            pEnv_ghost_dt
      by simp
    show "is_well_kinded ?pEnv ty \<and> is_runtime_type ?pEnv ty"
      using wk_pEnv rt_pEnv by simp
  qed

  have ta_tgt: "ty_args_well_formed ?clearedState ?pEnv"
    unfolding ty_args_well_formed_def
    using dom_tgt range_ground_tgt range_wk_rt_tgt by blast

  show ?thesis
    unfolding state_matches_env_def
    using lv_tgt gv_tgt no_lv_tgt no_gv_tgt fes_tgt no_fun_tgt nc_tgt cn_tgt swt_tgt ta_tgt
    by blast
qed

(* -------------------------------------------------------------------------- *)
(* H2b. One step of process_one_arg extends the partial body env by one local. *)
(*                                                                             *)
(* The interpretation results (lvalue + value) for argument k must be sound    *)
(* w.r.t. the k-th parameter's expected type in the *caller's* env:            *)
(*                                                                             *)
(*   valResult  = interp_term fuel state argTms[k]                             *)
(*   lvalResult = interp_writable_lvalue fuel state argTms[k]                  *)
(*                                                                             *)
(* where "state" is the caller's state. The expected type is                   *)
(* apply_subst tySubst (ty of k-th FI_TmArg). By the IH of the main theorem,   *)
(* both results are sound in the caller's env and store typing — that's the    *)
(* form of the preconditions.                                                  *)
(*                                                                             *)
(* For Var params: process_one_arg allocates a new slot in the store. The      *)
(* resulting store typing is partialStoreTyping @ [apply_subst tySubst ty].    *)
(*                                                                             *)
(* For Ref params: the store is unchanged; the ref entry is added to IS_Refs.  *)
(* -------------------------------------------------------------------------- *)
(* Field equalities for partial_body_env_for: all fields except TE_LocalVars
   and TE_ConstLocals are independent of k. *)
lemma partial_body_env_for_fields:
  "TE_GlobalVars (partial_body_env_for env funInfo k) = TE_GlobalVars env"
  "TE_GhostLocals (partial_body_env_for env funInfo k) = {||}"
  "TE_GhostGlobals (partial_body_env_for env funInfo k) = TE_GhostGlobals env"
  "TE_Functions (partial_body_env_for env funInfo k) = TE_Functions env"
  "TE_Datatypes (partial_body_env_for env funInfo k) = TE_Datatypes env"
  "TE_DataCtors (partial_body_env_for env funInfo k) = TE_DataCtors env"
  "TE_DataCtorsByType (partial_body_env_for env funInfo k) = TE_DataCtorsByType env"
  "TE_GhostDatatypes (partial_body_env_for env funInfo k) = TE_GhostDatatypes env"
  "TE_TypeVars (partial_body_env_for env funInfo k) = fset_of_list (FI_TyArgs funInfo)"
  "TE_RuntimeTypeVars (partial_body_env_for env funInfo k) = fset_of_list (FI_TyArgs funInfo)"
  "TE_ReturnType (partial_body_env_for env funInfo k) = FI_ReturnType funInfo"
  "TE_FunctionGhost (partial_body_env_for env funInfo k) = NotGhost"
  by (simp_all add: partial_body_env_for_def body_env_for_def)

(* How partial_body_env_for evolves between k and Suc k: the (k+1)-th FI_TmArg is
   added, substituting its type. For Var parameters, the name is also added to
   TE_ConstLocals. For Ref parameters, ConstNames is unchanged.

   Both the locals update and the const-names update are phrased in the exact
   form that state_matches_env_add_(const|nonconst)_local expects, so the step
   lemma can be applied directly.

   Requires k < length (FI_TmArgs funInfo). The tyenv_fun_param_names_distinct
   assumption on env (and the function being in TE_Functions) guarantees that
   paramName is not already in the prefix, so fmupd at k corresponds to
   appending the k-th entry to the fmap. *)
lemma partial_body_env_for_step:
  assumes k_bound: "k < length (FI_TmArgs funInfo)"
      and kth: "FI_TmArgs funInfo ! k = (paramName, paramTy, vor)"
      and distinct: "tyenv_fun_param_names_distinct env"
      and fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo"
  shows
    "partial_body_env_for env funInfo (Suc k)
     = (partial_body_env_for env funInfo k) \<lparr>
         TE_LocalVars := fmupd paramName paramTy
           (TE_LocalVars (partial_body_env_for env funInfo k)),
         TE_GhostLocals := fminus
           (TE_GhostLocals (partial_body_env_for env funInfo k)) {|paramName|},
         TE_ConstLocals :=
           (if vor = Var
            then finsert paramName
                   (TE_ConstLocals (partial_body_env_for env funInfo k))
            else fminus
                   (TE_ConstLocals (partial_body_env_for env funInfo k))
                   {|paramName|})
       \<rparr>"
proof -
  let ?args = "FI_TmArgs funInfo"

  \<comment> \<open>Standard: take (Suc k) xs = take k xs @ [xs ! k]. \<close>
  have take_Suc: "take (Suc k) ?args = take k ?args @ [?args ! k]"
    using k_bound by (simp add: take_Suc_conv_app_nth)

  \<comment> \<open>Locals: fmap_of_list of the (Suc k)-prefix pairs equals fmupd of the k-th
      entry onto the k-prefix's fmap. \<close>
  let ?pairs_k = "map (\<lambda>(name, ty, _). (name, ty)) (take k ?args)"
  let ?pairs_Sk = "map (\<lambda>(name, ty, _). (name, ty)) (take (Suc k) ?args)"
  have pairs_Sk_eq:
    "?pairs_Sk = ?pairs_k @ [(paramName, paramTy)]"
    using take_Suc kth by simp
  \<comment> \<open>Need: paramName is not already a key in pairs_k. This follows from
      param name distinctness on FI_TmArgs. \<close>
  from distinct fn_lookup have all_distinct: "distinct (map fst ?args)"
    unfolding tyenv_fun_param_names_distinct_def by blast
  have paramName_fresh: "paramName \<notin> set (map fst ?pairs_k)"
  proof -
    have "distinct (take (Suc k) (map fst ?args))"
      using all_distinct by (rule distinct_take)
    moreover have "take (Suc k) (map fst ?args)
                 = map fst (take k ?args) @ [paramName]"
      using k_bound kth by (simp add: take_Suc_conv_app_nth take_map)
    ultimately have "paramName \<notin> set (map fst (take k ?args))"
      by simp
    thus ?thesis by (auto simp: comp_def case_prod_beta)
  qed

  have fmap_pairs_step:
    "fmap_of_list ?pairs_Sk
       = fmupd paramName paramTy (fmap_of_list ?pairs_k)"
  proof (rule fmap_ext)
    fix name
    show "fmlookup (fmap_of_list ?pairs_Sk) name
        = fmlookup (fmupd paramName paramTy (fmap_of_list ?pairs_k)) name"
    proof (cases "name = paramName")
      case True
      have map_of_pairs_k_none: "map_of ?pairs_k paramName = None"
        using paramName_fresh by (auto simp add: map_of_eq_None_iff image_image)
      have "fmlookup (fmap_of_list ?pairs_Sk) paramName
              = map_of ?pairs_Sk paramName"
        by (simp add: fmap_of_list.rep_eq)
      also have "\<dots> = map_of (?pairs_k @ [(paramName, paramTy)]) paramName"
        using pairs_Sk_eq by simp
      also have "\<dots> = Some paramTy"
        using map_of_pairs_k_none by (simp add: map_add_Some_iff)
      finally have lhs: "fmlookup (fmap_of_list ?pairs_Sk) paramName
                           = Some paramTy" .
      from True show ?thesis by (simp add: lhs)
    next
      case False
      have "fmlookup (fmap_of_list ?pairs_Sk) name
              = map_of ?pairs_Sk name"
        by (simp add: fmap_of_list.rep_eq)
      also have "\<dots> = map_of ?pairs_k name"
        using pairs_Sk_eq False
        by (simp add: map_add_def split: option.split)
      also have "\<dots> = fmlookup (fmap_of_list ?pairs_k) name"
        by (simp add: fmap_of_list.rep_eq)
      finally show ?thesis using False by simp
    qed
  qed

  \<comment> \<open>Const names: the filter of the (Suc k)-prefix for Var parameters extends
      the k-prefix filter by either [paramName] (if vor = Var) or []. \<close>
  let ?const_k = "map (\<lambda>(name, _, _). name)
                   (filter (\<lambda>(_, _, vor'). vor' = Var) (take k ?args))"
  let ?const_Sk = "map (\<lambda>(name, _, _). name)
                    (filter (\<lambda>(_, _, vor'). vor' = Var) (take (Suc k) ?args))"
  have filter_Sk:
    "filter (\<lambda>(_, _, vor'). vor' = Var) (take (Suc k) ?args)
       = filter (\<lambda>(_, _, vor'). vor' = Var) (take k ?args)
         @ (if vor = Var then [?args ! k] else [])"
    using take_Suc kth by simp
  have const_Sk_eq:
    "?const_Sk = (if vor = Var then ?const_k @ [paramName] else ?const_k)"
    using filter_Sk kth by (cases "vor = Var") simp_all
  \<comment> \<open>paramName is not in the k-prefix of params, hence not in ?const_k either.
      This makes the fminus in the Ref branch a no-op. \<close>
  have paramName_not_in_const_k: "paramName \<notin> set ?const_k"
  proof -
    have "distinct (take (Suc k) (map fst ?args))"
      using all_distinct by (rule distinct_take)
    moreover have "take (Suc k) (map fst ?args)
                 = map fst (take k ?args) @ [paramName]"
      using k_bound kth by (simp add: take_Suc_conv_app_nth take_map)
    ultimately have "paramName \<notin> set (map fst (take k ?args))"
      by simp
    thus ?thesis by (auto simp: comp_def case_prod_beta)
  qed
  have paramName_not_in_const_k_fset:
    "paramName |\<notin>| fset_of_list ?const_k"
    using paramName_not_in_const_k by (metis fset_of_list.rep_eq)
  have const_k_fminus:
    "fminus (fset_of_list ?const_k) {|paramName|} = fset_of_list ?const_k"
    using paramName_not_in_const_k_fset by auto
  have fset_const_Sk:
    "fset_of_list ?const_Sk
       = (if vor = Var then finsert paramName (fset_of_list ?const_k)
          else fminus (fset_of_list ?const_k) {|paramName|})"
    using const_Sk_eq const_k_fminus
    by (cases "vor = Var") auto

  \<comment> \<open>TE_GhostLocals is {||} at both k and (Suc k), so fminus is a no-op. \<close>
  have ghost_locals_eq:
    "fminus (TE_GhostLocals (partial_body_env_for env funInfo k)) {|paramName|}
       = TE_GhostLocals (partial_body_env_for env funInfo (Suc k))"
    by (simp add: partial_body_env_for_fields(2))

  show ?thesis
    using fmap_pairs_step fset_const_Sk ghost_locals_eq
    by (simp add: partial_body_env_for_def body_env_for_def)
qed

lemma process_one_arg_step_sound:
  fixes env :: CoreTyEnv
    and funInfo :: FunInfo
    and tySubst :: "(nat, CoreType) fmap"
    and storeTyping :: "CoreType list"
    and k :: nat
  assumes sme_caller: "state_matches_env state env storeTyping"  \<comment> \<open>caller state (for value/lvalue soundness)\<close>
      and wf_env: "tyenv_well_formed env"
      and fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo"
      and not_ghost: "FI_Ghost funInfo = NotGhost"
      and k_bound: "k < length (FI_TmArgs funInfo)"
      and kth_arg: "FI_TmArgs funInfo ! k = (paramName, paramTy, vor)"
      and val_sound: "sound_term_result state env (apply_subst tySubst paramTy) valResult"
      and lval_sound: "vor = Ref \<Longrightarrow>
             sound_lvalue_result state env storeTyping
               (apply_subst tySubst paramTy) lvalResult"
      and partial_sound:
            "sound_partial_arg_processing_result env funInfo tySubst k storeTyping
               (Inr partialState)"
  shows "sound_partial_arg_processing_result env funInfo tySubst (Suc k) storeTyping
           (process_one_arg ((paramName, vor), lvalResult, valResult) (Inr partialState))"
proof -
  \<comment> \<open>Extract the partial state invariants from partial_sound. \<close>
  from partial_sound have tyargs_partial: "IS_TyArgs partialState = tySubst"
    unfolding sound_partial_arg_processing_result_def by auto
  from partial_sound obtain partialStoreTyping where
    sme_partial: "state_matches_env partialState
                    (partial_body_env_for env funInfo k) partialStoreTyping"
    and ext_partial: "storeTyping_extends storeTyping partialStoreTyping"
    unfolding sound_partial_arg_processing_result_def by auto

  let ?pEnv_k = "partial_body_env_for env funInfo k"
  let ?pEnv_Sk = "partial_body_env_for env funInfo (Suc k)"

  \<comment> \<open>partialState has ty_args_well_formed wrt ?pEnv_k. \<close>
  from sme_partial have ta_partial: "ty_args_well_formed partialState ?pEnv_k"
    unfolding state_matches_env_def by blast
  from ta_partial have
    dom_tySubst: "fmdom tySubst = TE_RuntimeTypeVars ?pEnv_k" and
    range_ground: "subst_range_tyvars tySubst = {}"
    unfolding ty_args_well_formed_def using tyargs_partial by auto

  \<comment> \<open>paramTy is the k-th parameter type. By tyenv_fun_ghost_constraint, it is
      runtime in (env with TE_TypeVars/TE_RuntimeTypeVars overridden to FI_TyArgs),
      which equals TE_RuntimeTypeVars ?pEnv_k = fmdom tySubst. \<close>
  from wf_env fn_lookup not_ghost have paramTy_rt_env_fset:
    "is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo),
                              TE_RuntimeTypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>)
                     paramTy"
  proof -
    from wf_env have fg: "tyenv_fun_ghost_constraint env"
      unfolding tyenv_well_formed_def by simp
    from fg fn_lookup not_ghost have
      "(\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo).
            is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo),
                                    TE_RuntimeTypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) ty)"
      unfolding tyenv_fun_ghost_constraint_def Let_def by blast
    moreover have "paramTy \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)"
      using kth_arg k_bound image_iff nth_mem by fastforce
    ultimately show ?thesis by blast
  qed
  hence paramTy_tyvars:
    "type_tyvars paramTy \<subseteq> fset (fset_of_list (FI_TyArgs funInfo))"
    using is_runtime_type_tyvars_subset by fastforce

  \<comment> \<open>fmdom tySubst = fset_of_list (FI_TyArgs funInfo) (via TE_RuntimeTypeVars ?pEnv_k
      which equals fset_of_list (FI_TyArgs funInfo) by partial_body_env_for_fields). \<close>
  have rtv_pEnv_k: "TE_RuntimeTypeVars ?pEnv_k = fset_of_list (FI_TyArgs funInfo)"
    by (simp add: partial_body_env_for_def body_env_for_def)
  have fmdom_tySubst: "fmdom tySubst = fset_of_list (FI_TyArgs funInfo)"
    using dom_tySubst rtv_pEnv_k by simp
  hence paramTy_tyvars_in_dom: "type_tyvars paramTy \<subseteq> fset (fmdom tySubst)"
    using paramTy_tyvars by simp

  \<comment> \<open>Apply_subst on paramTy with tySubst gives a ground type. \<close>
  have apply_ground:
    "type_tyvars (apply_subst tySubst paramTy) = {}"
  proof -
    have "type_tyvars (apply_subst tySubst paramTy)
            \<subseteq> (type_tyvars paramTy - fset (fmdom tySubst))
              \<union> subst_range_tyvars tySubst"
      by (rule apply_subst_tyvars_result)
    also have "\<dots> = {}"
      using paramTy_tyvars_in_dom range_ground by auto
    finally show ?thesis by simp
  qed

  \<comment> \<open>IS_TyArgs state pass on a ground type is identity. \<close>
  have apply_state_id:
    "apply_subst (IS_TyArgs state) (apply_subst tySubst paramTy)
       = apply_subst tySubst paramTy"
    using apply_ground apply_subst_disjoint_id by force

  show ?thesis
  proof (cases vor)
    case Var
    show ?thesis
    proof (cases valResult)
      case (Inl err)
      from val_sound Inl have err_sound: "sound_error_result err" by simp
      from Var Inl have step_eq:
        "process_one_arg ((paramName, vor), lvalResult, valResult) (Inr partialState) = Inl err"
        by simp
      show ?thesis
        using err_sound step_eq
        unfolding sound_partial_arg_processing_result_def by simp
    next
      case (Inr val)
      \<comment> \<open>val_sound on Inr: value_has_type env val (apply_subst (IS_TyArgs state)
          (apply_subst tySubst paramTy)). Simplify to apply_subst tySubst paramTy. \<close>
      from val_sound Inr have val_typed_env:
        "value_has_type env val (apply_subst tySubst paramTy)"
        using apply_state_id by simp

      \<comment> \<open>Transfer val_typed to ?pEnv_k. apply_subst tySubst paramTy is ground (apply_ground),
          so we can use value_has_type_cong_env_wk + ground-cong of wk/rt. \<close>
      have wk_env: "is_well_kinded env (apply_subst tySubst paramTy)"
        using value_has_type_well_kinded[OF val_typed_env wf_env] .
      have rt_env: "is_runtime_type env (apply_subst tySubst paramTy)"
        using value_has_type_runtime[OF val_typed_env] .

      have wf_pEnv_k: "tyenv_well_formed ?pEnv_k"
        using partial_body_env_for_well_formed[OF wf_env fn_lookup not_ghost] .

      have wk_pEnv_k: "is_well_kinded ?pEnv_k (apply_subst tySubst paramTy)"
        using wk_env is_well_kinded_ground_cong_env[OF apply_ground, of ?pEnv_k env]
        by (simp add: partial_body_env_for_def body_env_for_def)
      have rt_pEnv_k: "is_runtime_type ?pEnv_k (apply_subst tySubst paramTy)"
        using rt_env is_runtime_type_ground_cong_env[OF apply_ground, of ?pEnv_k env]
        by (simp add: partial_body_env_for_def body_env_for_def)

      have val_typed_pEnv:
        "value_has_type ?pEnv_k val (apply_subst tySubst paramTy)"
        using value_has_type_cong_env_wk
                [OF _ _ _ wf_env wf_pEnv_k wk_env wk_pEnv_k rt_env rt_pEnv_k val_typed_env]
        by (simp add: partial_body_env_for_def body_env_for_def)

      \<comment> \<open>Rewrite val_typed_pEnv using IS_TyArgs partialState = tySubst, so the
          shape matches what state_matches_env_add_const_local expects. \<close>
      have val_typed_partial:
        "value_has_type ?pEnv_k val (apply_subst (IS_TyArgs partialState) paramTy)"
        using val_typed_pEnv tyargs_partial by simp

      \<comment> \<open>alloc_store on partialState. \<close>
      obtain state' addr where alloc_eq:
        "(state', addr) = alloc_store partialState val"
        by (cases "alloc_store partialState val") auto

      let ?state'' = "state' \<lparr> IS_Locals := fmupd paramName addr (IS_Locals state'),
                                IS_Refs := fmdrop paramName (IS_Refs state'),
                                IS_ConstLocals := finsert paramName (IS_ConstLocals state') \<rparr>"

      have step_eq:
        "process_one_arg ((paramName, vor), lvalResult, valResult) (Inr partialState)
           = Inr ?state''"
        using Var Inr alloc_eq
        by (simp add: case_prod_beta)

      from wf_env have distinct: "tyenv_fun_param_names_distinct env"
        unfolding tyenv_well_formed_def by simp
      have env'_shape:
        "?pEnv_Sk = ?pEnv_k \<lparr>
             TE_LocalVars := fmupd paramName paramTy (TE_LocalVars ?pEnv_k),
             TE_GhostLocals := fminus (TE_GhostLocals ?pEnv_k) {|paramName|},
             TE_ConstLocals := finsert paramName (TE_ConstLocals ?pEnv_k)
           \<rparr>"
        using partial_body_env_for_step[OF k_bound kth_arg distinct fn_lookup] Var
        by simp

      \<comment> \<open>Apply state_matches_env_add_const_local with rhsTy = paramTy. The resulting
          storeTyping is partialStoreTyping @ [apply_subst (IS_TyArgs partialState) paramTy]
          = partialStoreTyping @ [apply_subst tySubst paramTy]. \<close>
      have sme_new:
        "state_matches_env ?state'' ?pEnv_Sk
           (partialStoreTyping @ [apply_subst (IS_TyArgs partialState) paramTy])"
        using state_matches_env_add_const_local
                [OF sme_partial val_typed_partial alloc_eq refl env'_shape] .

      have ext_new: "storeTyping_extends storeTyping
                       (partialStoreTyping @ [apply_subst (IS_TyArgs partialState) paramTy])"
      proof -
        from ext_partial obtain suffix where
          "partialStoreTyping = storeTyping @ suffix"
          unfolding storeTyping_extends_def by blast
        hence "partialStoreTyping @ [apply_subst (IS_TyArgs partialState) paramTy]
                 = storeTyping @ (suffix @ [apply_subst (IS_TyArgs partialState) paramTy])"
          by simp
        thus ?thesis unfolding storeTyping_extends_def by blast
      qed

      \<comment> \<open>IS_TyArgs ?state'' = IS_TyArgs partialState = tySubst (alloc_store and the
          subsequent record updates don't touch IS_TyArgs). \<close>
      have tyargs_state'': "IS_TyArgs ?state'' = tySubst"
        using alloc_eq tyargs_partial by (simp add: Let_def)

      show ?thesis
        using sme_new ext_new step_eq tyargs_state''
        unfolding sound_partial_arg_processing_result_def by auto
    qed
  next
    case Ref
    show ?thesis
    proof (cases lvalResult)
      case (Inl err)
      from lval_sound[OF Ref] Inl have err_sound: "sound_error_result err" by simp
      from Ref Inl have step_eq:
        "process_one_arg ((paramName, vor), lvalResult, valResult) (Inr partialState) = Inl err"
        by simp
      show ?thesis
        using err_sound step_eq
        unfolding sound_partial_arg_processing_result_def by simp
    next
      case (Inr lval)
      obtain addr path where lval_eq: "lval = (addr, path)"
        by (cases lval) auto
      \<comment> \<open>lval_sound on Inr: addr < length (IS_Store state) and type_at_path env
          (storeTyping ! addr) path = Some (apply_subst (IS_TyArgs state) (apply_subst tySubst paramTy))
          = Some (apply_subst tySubst paramTy) (by apply_state_id). \<close>
      from lval_sound[OF Ref] Inr lval_eq apply_state_id
      have lval_good:
        "addr < length (IS_Store state)"
        "type_at_path env (storeTyping ! addr) path = Some (apply_subst tySubst paramTy)"
        by auto
      show ?thesis
      proof (cases valResult)
        case Inl_val: (Inl err)
        from val_sound Inl_val have err_sound: "sound_error_result err" by simp
        from Ref Inr lval_eq Inl_val have step_eq:
          "process_one_arg ((paramName, vor), lvalResult, valResult) (Inr partialState) = Inl err"
          by simp
        show ?thesis
          using err_sound step_eq
          unfolding sound_partial_arg_processing_result_def by simp
      next
        case Inr_val: (Inr val)
        let ?state' = "partialState \<lparr> IS_Locals := fmdrop paramName (IS_Locals partialState),
                                       IS_Refs := fmupd paramName (addr, path) (IS_Refs partialState),
                                       IS_ConstLocals := fminus (IS_ConstLocals partialState) {|paramName|} \<rparr>"

        have step_eq:
          "process_one_arg ((paramName, vor), lvalResult, valResult) (Inr partialState)
             = Inr ?state'"
          using Ref Inr lval_eq Inr_val by simp

        from ext_partial obtain suffix where
          pst_eq: "partialStoreTyping = storeTyping @ suffix"
          unfolding storeTyping_extends_def by blast
        have len_st: "length storeTyping = length (IS_Store state)"
          using sme_caller
          unfolding state_matches_env_def store_well_typed_def by simp
        have len_pst: "length partialStoreTyping = length (IS_Store partialState)"
          using sme_partial
          unfolding state_matches_env_def store_well_typed_def by simp
        have len_ge: "length (IS_Store state) \<le> length (IS_Store partialState)"
          using pst_eq len_st len_pst by simp
        from lval_good(1) len_ge have addr_valid_partial:
          "addr < length (IS_Store partialState)" by linarith

        have pst_at_addr: "partialStoreTyping ! addr = storeTyping ! addr"
          using pst_eq lval_good(1) len_st by (simp add: nth_append)

        \<comment> \<open>Transfer type_at_path from env to ?pEnv_k. type_at_path only depends on
            TE_DataCtors, which ?pEnv_k inherits from env. \<close>
        have path_ty_partial:
          "type_at_path ?pEnv_k (partialStoreTyping ! addr) path
             = Some (apply_subst tySubst paramTy)"
        proof -
          have "type_at_path env (storeTyping ! addr) path
                  = Some (apply_subst tySubst paramTy)"
            using lval_good(2) .
          also have "storeTyping ! addr = partialStoreTyping ! addr"
            using pst_at_addr by simp
          also have "type_at_path env = type_at_path ?pEnv_k"
            using type_at_path_cong_env
                    [where env=env and env'="?pEnv_k"]
            using partial_body_env_for_fields(6) by auto
          finally show ?thesis by simp
        qed

        \<comment> \<open>Rewrite path_ty_partial to use IS_TyArgs partialState shape. \<close>
        have path_ty_partial':
          "type_at_path ?pEnv_k (partialStoreTyping ! addr) path
             = Some (apply_subst (IS_TyArgs partialState) paramTy)"
          using path_ty_partial tyargs_partial by simp

        have var_fresh: "fmlookup (TE_LocalVars ?pEnv_k) paramName = None"
        proof -
          from wf_env have all_distinct: "distinct (map fst (FI_TmArgs funInfo))"
            using fn_lookup
            unfolding tyenv_well_formed_def tyenv_fun_param_names_distinct_def by blast
          have "distinct (take (Suc k) (map fst (FI_TmArgs funInfo)))"
            using all_distinct by (rule distinct_take)
          moreover have "take (Suc k) (map fst (FI_TmArgs funInfo))
                       = map fst (take k (FI_TmArgs funInfo)) @ [paramName]"
            using k_bound kth_arg
            by (simp add: take_Suc_conv_app_nth take_map)
          ultimately have not_in_prefix:
            "paramName \<notin> set (map fst (take k (FI_TmArgs funInfo)))"
            by simp
          let ?pairs_k = "map (\<lambda>(name, ty, _). (name, ty)) (take k (FI_TmArgs funInfo))"
          have "paramName \<notin> set (map fst ?pairs_k)"
            using not_in_prefix by (auto simp: comp_def case_prod_beta)
          hence "map_of ?pairs_k paramName = None"
            by (auto simp: map_of_eq_None_iff image_image)
          hence "fmlookup (fmap_of_list ?pairs_k) paramName = None"
            by (simp add: fmap_of_list.rep_eq)
          thus ?thesis by (simp add: partial_body_env_for_def)
        qed

        have var_not_ghost: "paramName |\<notin>| TE_GhostLocals ?pEnv_k"
          by (simp add: partial_body_env_for_def body_env_for_def)

        from wf_env have distinct: "tyenv_fun_param_names_distinct env"
          unfolding tyenv_well_formed_def by simp
        have env'_shape:
          "?pEnv_Sk = ?pEnv_k \<lparr>
               TE_LocalVars := fmupd paramName paramTy (TE_LocalVars ?pEnv_k),
               TE_GhostLocals := fminus (TE_GhostLocals ?pEnv_k) {|paramName|},
               TE_ConstLocals := fminus (TE_ConstLocals ?pEnv_k) {|paramName|}
             \<rparr>"
          using partial_body_env_for_step[OF k_bound kth_arg distinct fn_lookup] Ref
          by simp

        have sme_new:
          "state_matches_env ?state' ?pEnv_Sk partialStoreTyping"
          using state_matches_env_add_ref
                  [OF sme_partial addr_valid_partial path_ty_partial' refl env'_shape
                      var_fresh var_not_ghost] .

        have tyargs_state': "IS_TyArgs ?state' = tySubst"
          using tyargs_partial by simp

        show ?thesis
          using sme_new ext_partial step_eq tyargs_state'
          unfolding sound_partial_arg_processing_result_def by auto
      qed
    qed
  qed
qed

(* If a single process_one_arg step succeeds, then the val-result was Inr (in
   both Var and Ref clauses) and, for the Ref clause, the ref-result was Inr too. *)
lemma process_one_arg_inr_inversion:
  assumes "process_one_arg ((name, vor), refResult, valResult) (Inr state) = Inr state'"
  shows "(\<exists>v. valResult = Inr v) \<and> (vor = Ref \<longrightarrow> (\<exists>a p. refResult = Inr (a, p)))"
proof (cases vor)
  case Var
  show ?thesis using assms Var by (cases valResult) auto
next
  case Ref
  show ?thesis
  proof (cases refResult)
    case (Inl err) with assms Ref show ?thesis by simp
  next
    case (Inr ap)
    obtain a p where ap_eq: "ap = (a, p)" by (cases ap)
    show ?thesis using assms Ref Inr ap_eq by (cases valResult) auto
  qed
qed

(* Strengthening: if the entire fold succeeds, every val-result in the tuple
   list is Inr, and every Ref-position's ref-result is Inr.

   Stated by index over the formal parameters / refResults / valResults
   (which are length-aligned by construction). The fold is over
   zip ifArgs (zip refResults valResults), so we induct on this list. *)
lemma fold_process_one_arg_inr_inversion:
  assumes "fold process_one_arg (zip ifArgs (zip refResults valResults)) (Inr initState)
             = Inr finalState"
      and "length ifArgs = length refResults"
      and "length ifArgs = length valResults"
  shows "\<forall>i < length ifArgs.
           (\<exists>v. valResults ! i = Inr v) \<and>
           (snd (ifArgs ! i) = Ref \<longrightarrow> (\<exists>a p. refResults ! i = Inr (a, p)))"
using assms proof (induction ifArgs arbitrary: refResults valResults initState)
  case Nil
  then show ?case by simp
next
  case (Cons ifa ifrest)
  from Cons.prems(2) obtain rr rrest where rr_eq: "refResults = rr # rrest"
    by (cases refResults) auto
  from Cons.prems(3) obtain vv vrest where vv_eq: "valResults = vv # vrest"
    by (cases valResults) auto
  obtain name vor where ifa_eq: "ifa = (name, vor)" by (cases ifa)

  let ?step = "process_one_arg ((name, vor), rr, vv) (Inr initState)"
  have fold_unfold:
    "fold process_one_arg (zip (ifa # ifrest) (zip refResults valResults)) (Inr initState)
       = fold process_one_arg (zip ifrest (zip rrest vrest)) ?step"
    using rr_eq vv_eq ifa_eq by simp

  \<comment> \<open>If ?step were Inl, the fold would stay Inl, contradicting Cons.prems(1).\<close>
  have step_inr: "\<exists>s'. ?step = Inr s'"
  proof (cases ?step)
    case (Inl err)
    show ?thesis
      by (metis Cons.prems(1) Inl fold_process_one_arg_error fold_unfold) 
  next
    case (Inr s') then show ?thesis by blast
  qed
  then obtain s' where step_eq: "?step = Inr s'" by blast

  \<comment> \<open>Apply the per-step inversion to the head. \<close>
  from process_one_arg_inr_inversion[OF step_eq[unfolded ifa_eq]]
  have head: "(\<exists>v. vv = Inr v) \<and> (vor = Ref \<longrightarrow> (\<exists>a p. rr = Inr (a, p)))" .

  \<comment> \<open>The IH gives us the rest. \<close>
  from fold_unfold step_eq Cons.prems(1)
  have rest_fold: "fold process_one_arg (zip ifrest (zip rrest vrest)) (Inr s') = Inr finalState"
    by simp
  from Cons.prems(2) rr_eq have len_rrest: "length ifrest = length rrest" by simp
  from Cons.prems(3) vv_eq have len_vrest: "length ifrest = length vrest" by simp
  from Cons.IH[OF rest_fold len_rrest len_vrest]
  have rest: "\<forall>i < length ifrest.
                (\<exists>v. vrest ! i = Inr v) \<and>
                (snd (ifrest ! i) = Ref \<longrightarrow> (\<exists>a p. rrest ! i = Inr (a, p)))" .

  show ?case
  proof (intro allI impI)
    fix i assume i_lt: "i < length (ifa # ifrest)"
    show "(\<exists>v. valResults ! i = Inr v) \<and>
          (snd ((ifa # ifrest) ! i) = Ref \<longrightarrow> (\<exists>a p. refResults ! i = Inr (a, p)))"
    proof (cases i)
      case 0
      from head ifa_eq show ?thesis using 0 rr_eq vv_eq by simp
    next
      case (Suc j)
      from i_lt Suc have j_lt: "j < length ifrest" by simp
      from rest j_lt have
        "(\<exists>v. vrest ! j = Inr v) \<and>
         (snd (ifrest ! j) = Ref \<longrightarrow> (\<exists>a p. rrest ! j = Inr (a, p)))" by simp
      thus ?thesis using Suc rr_eq vv_eq by simp
    qed
  qed
qed

(* Short-circuit: if the running result is already an error, process_one_arg
   preserves it; soundness is preserved too. *)
lemma process_one_arg_preserve_error:
  assumes "sound_partial_arg_processing_result env funInfo tySubst k storeTyping (Inl err)"
  shows "sound_partial_arg_processing_result env funInfo tySubst (Suc k) storeTyping
           (process_one_arg tuple (Inl err))"
proof -
  from assms have "sound_error_result err"
    unfolding sound_partial_arg_processing_result_def by simp
  moreover have "process_one_arg tuple (Inl err) = Inl err" by simp
  ultimately show ?thesis
    unfolding sound_partial_arg_processing_result_def by simp
qed

(* -------------------------------------------------------------------------- *)
(* H2c — step 1: a generalized induction lemma.                                 *)
(*                                                                             *)
(* Parameterized by a starting index k and a suffix of the formal parameter    *)
(* list. Assumes partial soundness at k, plus per-position soundness for each  *)
(* formal parameter in the suffix (aligned pointwise with argTms suffix).      *)
(* Concludes partial soundness after folding through all remaining arguments.  *)
(* -------------------------------------------------------------------------- *)
lemma fold_process_one_arg_sound_gen:
  fixes env :: CoreTyEnv
    and funInfo :: FunInfo
    and tySubst :: "(nat, CoreType) fmap"
    and storeTyping :: "CoreType list"
    and state :: "'w InterpState"
  assumes sme_caller: "state_matches_env state env storeTyping"
      and wf_env: "tyenv_well_formed env"
      and fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo"
      and not_ghost: "FI_Ghost funInfo = NotGhost"
      and suffix_at_k:
            "suffixFnArgs = drop k (FI_TmArgs funInfo)"
      and var_ref_match:
            "list_all2 (\<lambda>(name1, _, vor1) (name2, vor2). name1 = name2 \<and> vor1 = vor2)
                       suffixFnArgs suffixIfArgs"
      and len_vals: "length suffixIfArgs = length suffixValResults"
      and len_refs: "length suffixIfArgs = length suffixRefResults"
      and k_plus_len: "k + length suffixFnArgs = length (FI_TmArgs funInfo)"
      and vals_sound:
            "\<forall>i < length suffixFnArgs.
               sound_term_result state env
                 (apply_subst tySubst (fst (snd (suffixFnArgs ! i))))
                 (suffixValResults ! i)"
      and lvals_sound:
            "\<forall>i < length suffixFnArgs.
               snd (snd (suffixFnArgs ! i)) = Ref \<longrightarrow>
                 sound_lvalue_result state env storeTyping
                   (apply_subst tySubst (fst (snd (suffixFnArgs ! i))))
                   (suffixRefResults ! i)"
      and partial_sound_k:
            "sound_partial_arg_processing_result env funInfo tySubst k storeTyping
               partialResult"
  shows "sound_partial_arg_processing_result env funInfo tySubst
           (k + length suffixFnArgs) storeTyping
           (fold process_one_arg (zip suffixIfArgs (zip suffixRefResults suffixValResults))
                                 partialResult)"
using suffix_at_k var_ref_match len_vals len_refs k_plus_len vals_sound lvals_sound
      partial_sound_k
proof (induction suffixFnArgs arbitrary: k suffixIfArgs suffixValResults
                                          suffixRefResults partialResult)
  case Nil
  from Nil.prems(1) have empty_ifArgs: "suffixIfArgs = []"
    using Nil.prems(2) by (cases suffixIfArgs) auto
  from Nil.prems(3) empty_ifArgs have empty_vals: "suffixValResults = []"
    by (cases suffixValResults) auto
  from Nil.prems(4) empty_ifArgs have empty_refs: "suffixRefResults = []"
    by (cases suffixRefResults) auto
  have fold_eq: "fold process_one_arg
                   (zip suffixIfArgs (zip suffixRefResults suffixValResults)) partialResult
                  = partialResult"
    using empty_ifArgs empty_vals empty_refs by simp
  show ?case using Nil.prems(8) fold_eq by simp
next
  case (Cons arg restArgs)
  from Cons.prems(2) obtain ifHead ifRest where
    ifArgs_eq: "suffixIfArgs = ifHead # ifRest" and
    ifRest_match: "list_all2 (\<lambda>(name1, _, vor1) (name2, vor2). name1 = name2 \<and> vor1 = vor2)
                              restArgs ifRest"
    by (cases suffixIfArgs) auto
  obtain paramName paramTy vor where arg_eq: "arg = (paramName, paramTy, vor)"
    by (cases arg) auto
  obtain ifName ifVor where ifHead_eq: "ifHead = (ifName, ifVor)"
    by (cases ifHead)
  from Cons.prems(2) ifArgs_eq arg_eq ifHead_eq
  have head_match: "paramName = ifName" "vor = ifVor" by simp_all
  from Cons.prems(3) ifArgs_eq obtain valHead valRest where
    vals_eq: "suffixValResults = valHead # valRest" and
    len_vals': "length ifRest = length valRest"
    by (cases suffixValResults) auto
  from Cons.prems(4) ifArgs_eq obtain refHead refRest where
    refs_eq: "suffixRefResults = refHead # refRest" and
    len_refs': "length ifRest = length refRest"
    by (cases suffixRefResults) auto

  from Cons.prems(1) have k_bound: "k < length (FI_TmArgs funInfo)"
    using Cons.prems(5)
    by (metis drop_eq_Nil2 linorder_le_less_linear neq_Nil_conv)
  from Cons.prems(1) have kth: "FI_TmArgs funInfo ! k = arg"
    using k_bound nth_via_drop by metis
  from kth arg_eq
  have kth_arg: "FI_TmArgs funInfo ! k = (paramName, paramTy, vor)" by simp

  from Cons.prems(6) have val_sound_head:
    "sound_term_result state env (apply_subst tySubst paramTy) valHead"
    using arg_eq vals_eq by force
  from Cons.prems(7) have lval_sound_head:
    "vor = Ref \<Longrightarrow> sound_lvalue_result state env storeTyping
                     (apply_subst tySubst paramTy) refHead"
    using arg_eq refs_eq by force

  let ?step = "process_one_arg ((paramName, vor), refHead, valHead) partialResult"
  have step_sound:
    "sound_partial_arg_processing_result env funInfo tySubst (Suc k) storeTyping ?step"
  proof (cases partialResult)
    case (Inl err)
    from process_one_arg_preserve_error[of env funInfo tySubst k storeTyping err
                                           "((paramName, vor), refHead, valHead)"]
         Cons.prems(8) Inl
    show ?thesis by simp
  next
    case (Inr partialState)
    from process_one_arg_step_sound[OF sme_caller wf_env fn_lookup not_ghost k_bound
                                       kth_arg val_sound_head lval_sound_head]
         Cons.prems(8) Inr
    show ?thesis by simp
  qed

  have rest_at_k1: "restArgs = drop (Suc k) (FI_TmArgs funInfo)"
    using Cons.prems(1)
    by (metis Cons_nth_drop_Suc k_bound list.inject)
  have len_rest: "Suc k + length restArgs = length (FI_TmArgs funInfo)"
    using Cons.prems(5) by simp
  have vals_sound_rest: "\<forall>i < length restArgs.
      sound_term_result state env
        (apply_subst tySubst (fst (snd (restArgs ! i))))
        (valRest ! i)"
  proof (intro allI impI)
    fix i assume "i < length restArgs"
    hence "Suc i < length (arg # restArgs)" by simp
    from Cons.prems(6)[rule_format, OF this]
    have "sound_term_result state env
            (apply_subst tySubst (fst (snd ((arg # restArgs) ! Suc i))))
            (suffixValResults ! Suc i)" .
    thus "sound_term_result state env
            (apply_subst tySubst (fst (snd (restArgs ! i))))
            (valRest ! i)"
      by (simp add: vals_eq)
  qed
  have lvals_sound_rest: "\<forall>i < length restArgs.
      snd (snd (restArgs ! i)) = Ref \<longrightarrow>
        sound_lvalue_result state env storeTyping
          (apply_subst tySubst (fst (snd (restArgs ! i))))
          (refRest ! i)"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < length restArgs"
    assume is_ref: "snd (snd (restArgs ! i)) = Ref"
    from i_lt have "Suc i < length (arg # restArgs)" by simp
    moreover from is_ref have "snd (snd ((arg # restArgs) ! Suc i)) = Ref" by simp
    ultimately have "sound_lvalue_result state env storeTyping
                        (apply_subst tySubst (fst (snd ((arg # restArgs) ! Suc i))))
                        (suffixRefResults ! Suc i)"
      using Cons.prems(7)[rule_format] by blast
    thus "sound_lvalue_result state env storeTyping
            (apply_subst tySubst (fst (snd (restArgs ! i)))) (refRest ! i)"
      by (simp add: refs_eq)
  qed

  have fold_unfold: "fold process_one_arg
      (zip suffixIfArgs (zip suffixRefResults suffixValResults)) partialResult
    = fold process_one_arg (zip ifRest (zip refRest valRest)) ?step"
    using ifArgs_eq vals_eq refs_eq head_match ifHead_eq by simp

  from Cons.IH[OF rest_at_k1 ifRest_match len_vals' len_refs' len_rest
                  vals_sound_rest lvals_sound_rest step_sound]
  have "sound_partial_arg_processing_result env funInfo tySubst
          (Suc k + length restArgs) storeTyping
          (fold process_one_arg (zip ifRest (zip refRest valRest)) ?step)" .
  moreover have "k + length (arg # restArgs) = Suc k + length restArgs" by simp
  ultimately show ?case using fold_unfold by simp
qed


(* -------------------------------------------------------------------------- *)
(* H2c. The fold over all parameters is sound: starting from the cleared state *)
(* and the k=0 partial env, folding produces a state matching the full        *)
(* body env.                                                                   *)
(* -------------------------------------------------------------------------- *)
(* The vals/lvals soundness preconditions are stated using the *outer*
   substitution outerSubst = fmap_of_list (zip (FI_TyArgs funInfo) tyArgs),
   which is exactly the shape produced by the IH (via args_typed at the
   call site). The internal proof bridges to tySubst (which has the caller's
   IS_TyArgs pre-applied to the range) via apply_subst_compose_zip. *)
lemma fold_process_one_arg_sound:
  fixes env :: CoreTyEnv
    and funInfo :: FunInfo
    and tyArgs :: "CoreType list"
    and storeTyping :: "CoreType list"
    and state :: "'w InterpState"
    and f :: "'w InterpFun"
  defines "outerSubst \<equiv> fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)"
      and "tySubst \<equiv> fmap_of_list
              (zip (FI_TyArgs funInfo)
                   (map (apply_subst (IS_TyArgs state)) tyArgs))"
  assumes sme_caller: "state_matches_env state env storeTyping"
      and wf_env: "tyenv_well_formed env"
      and fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo"
      and not_ghost: "FI_Ghost funInfo = NotGhost"
      and fi_match: "fun_info_matches_interp_fun env funInfo f"
      and ty_len: "length tyArgs = length (FI_TyArgs funInfo)"
      and ty_wk:  "list_all (is_well_kinded env) tyArgs"
      and ty_rt:  "list_all (is_runtime_type env) tyArgs"
      and vals_sound:
            "\<forall>i < length (FI_TmArgs funInfo).
               sound_term_result state env
                 (apply_subst outerSubst (fst (snd (FI_TmArgs funInfo ! i))))
                 (map (interp_term fuel state) argTms ! i)"
      and lvals_sound:
            "\<forall>i < length (FI_TmArgs funInfo).
               snd (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow>
                 sound_lvalue_result state env storeTyping
                   (apply_subst outerSubst (fst (snd (FI_TmArgs funInfo ! i))))
                   (map (interp_writable_lvalue fuel state) argTms ! i)"
      and len_argTms: "length argTms = length (FI_TmArgs funInfo)"
  shows "sound_arg_processing_result env funInfo tySubst storeTyping
           (fold process_one_arg
              (zip (IF_Args f)
                   (zip (map (interp_writable_lvalue fuel state) argTms)
                        (map (interp_term fuel state) argTms)))
              (Inr (state \<lparr> IS_Locals := fmempty,
                             IS_Refs := fmempty,
                             IS_ConstLocals := {||},
                             IS_TyArgs := tySubst \<rparr>)))"
proof -
  let ?clearedState = "state \<lparr> IS_Locals := fmempty, IS_Refs := fmempty,
                                IS_ConstLocals := {||},
                                IS_TyArgs := tySubst \<rparr>"
  let ?valResults = "map (interp_term fuel state) argTms"
  let ?refResults = "map (interp_writable_lvalue fuel state) argTms"

  \<comment> \<open>H2a: initial state is sound at k=0. \<close>
  have sme_cleared:
    "state_matches_env ?clearedState (partial_body_env_for env funInfo 0) storeTyping"
    using cleared_state_matches_partial_env_zero
            [OF sme_caller wf_env fn_lookup not_ghost ty_len ty_wk ty_rt,
             where tySubst=tySubst]
    by (simp add: tySubst_def)
  have partial_sound_zero:
    "sound_partial_arg_processing_result env funInfo tySubst 0 storeTyping
       (Inr ?clearedState)"
    unfolding sound_partial_arg_processing_result_def
    using sme_cleared storeTyping_extends_refl by auto

  \<comment> \<open>Translate vals_sound / lvals_sound from outerSubst-form to tySubst-form.
      The translation uses apply_subst_compose_zip plus apply_state_id (ground). \<close>

  \<comment> \<open>Distinctness and groundness conditions. \<close>
  from wf_env fn_lookup have ty_dist: "distinct (FI_TyArgs funInfo)"
    unfolding tyenv_well_formed_def tyenv_fun_tyvars_distinct_def by blast
  \<comment> \<open>Caller's ty_args_well_formed. \<close>
  from sme_caller have ta_caller: "ty_args_well_formed state env"
    unfolding state_matches_env_def by blast
  from ta_caller have caller_dom: "fmdom (IS_TyArgs state) = TE_RuntimeTypeVars env"
    and caller_range_ground: "subst_range_tyvars (IS_TyArgs state) = {}"
    unfolding ty_args_well_formed_def by auto

  \<comment> \<open>For each i < length FI_TmArgs funInfo, apply_subst tySubst paramTy_i is ground. \<close>
  have paramTy_apply_ground:
    "\<And>i. i < length (FI_TmArgs funInfo) \<Longrightarrow>
            type_tyvars (apply_subst tySubst (fst (snd (FI_TmArgs funInfo ! i)))) = {}"
  proof -
    fix i assume i_bound: "i < length (FI_TmArgs funInfo)"
    let ?paramTy_i = "fst (snd (FI_TmArgs funInfo ! i))"
    have "?paramTy_i \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)"
      using i_bound by force
    from wf_env fn_lookup not_ghost have
      "is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo),
                                TE_RuntimeTypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>)
                        ?paramTy_i"
      unfolding tyenv_well_formed_def tyenv_fun_ghost_constraint_def Let_def
      using \<open>?paramTy_i \<in> _\<close> by blast
    hence paramTy_tyvars:
      "type_tyvars ?paramTy_i \<subseteq> fset (fset_of_list (FI_TyArgs funInfo))"
      using is_runtime_type_tyvars_subset by fastforce
    \<comment> \<open>fmdom tySubst = fset_of_list (FI_TyArgs funInfo). \<close>
    have fmdom_tySubst: "fmdom tySubst = fset_of_list (FI_TyArgs funInfo)"
      using tySubst_def ty_len
      by (simp add: fset_of_list.rep_eq)
    \<comment> \<open>subst_range_tyvars tySubst = {} (each entry is apply_subst (IS_TyArgs state) of
        a runtime-in-env type; by apply_subst_tyvars_result + caller's well-formedness,
        each entry is ground). \<close>
    have range_ground: "subst_range_tyvars tySubst = {}"
    proof -
      have "\<forall>t \<in> fmran' tySubst. type_tyvars t = {}"
      proof
        fix t assume mem: "t \<in> fmran' tySubst"
        then obtain n where lk: "fmlookup tySubst n = Some t"
          by (auto simp: fmran'_alt_def fmlookup_dom_iff)
        from lk tySubst_def
        have "map_of (zip (FI_TyArgs funInfo)
                  (map (apply_subst (IS_TyArgs state)) tyArgs)) n = Some t"
          by (simp add: fmap_of_list.rep_eq)
        hence "(n, t) \<in> set (zip (FI_TyArgs funInfo)
                              (map (apply_subst (IS_TyArgs state)) tyArgs))"
          by (rule map_of_SomeD)
        then obtain j where j_lt: "j < length tyArgs"
          and t_eq: "t = apply_subst (IS_TyArgs state) (tyArgs ! j)"
          using ty_len by (auto simp: set_zip)
        from ty_rt j_lt have "is_runtime_type env (tyArgs ! j)"
          by (simp add: list_all_length)
        from is_runtime_type_tyvars_subset[OF this]
        have tyArg_tyvars: "type_tyvars (tyArgs ! j) \<subseteq> fset (TE_RuntimeTypeVars env)"
          by simp
        hence tyArg_in_dom: "type_tyvars (tyArgs ! j) \<subseteq> fset (fmdom (IS_TyArgs state))"
          using caller_dom by simp
        have "type_tyvars (apply_subst (IS_TyArgs state) (tyArgs ! j))
                \<subseteq> (type_tyvars (tyArgs ! j) - fset (fmdom (IS_TyArgs state)))
                  \<union> subst_range_tyvars (IS_TyArgs state)"
          by (rule apply_subst_tyvars_result)
        also have "\<dots> = {}" using tyArg_in_dom caller_range_ground by auto
        finally show "type_tyvars t = {}" using t_eq by simp
      qed
      thus ?thesis unfolding subst_range_tyvars_def by auto
    qed
    \<comment> \<open>Now apply_subst tySubst ?paramTy_i has empty tyvars. \<close>
    have "type_tyvars (apply_subst tySubst ?paramTy_i)
            \<subseteq> (type_tyvars ?paramTy_i - fset (fmdom tySubst))
              \<union> subst_range_tyvars tySubst"
      by (rule apply_subst_tyvars_result)
    also have "\<dots> = {}"
      using paramTy_tyvars fmdom_tySubst range_ground by auto
    finally show "type_tyvars (apply_subst tySubst ?paramTy_i) = {}" by simp
  qed

  \<comment> \<open>compose_zip: apply_subst tySubst t = apply_subst (IS_TyArgs state) (apply_subst outerSubst t)
      when t's tyvars are in FI_TyArgs funInfo. \<close>
  have compose_zip:
    "\<And>i. i < length (FI_TmArgs funInfo) \<Longrightarrow>
       apply_subst tySubst (fst (snd (FI_TmArgs funInfo ! i)))
       = apply_subst (IS_TyArgs state)
           (apply_subst outerSubst (fst (snd (FI_TmArgs funInfo ! i))))"
  proof -
    fix i assume i_bound: "i < length (FI_TmArgs funInfo)"
    let ?paramTy_i = "fst (snd (FI_TmArgs funInfo ! i))"
    have "?paramTy_i \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)"
      using i_bound by force
    from wf_env fn_lookup not_ghost have
      "is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo),
                                TE_RuntimeTypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>)
                        ?paramTy_i"
      unfolding tyenv_well_formed_def tyenv_fun_ghost_constraint_def Let_def
      using \<open>?paramTy_i \<in> _\<close> by blast
    from is_runtime_type_tyvars_subset[OF this]
    have paramTy_subset: "type_tyvars ?paramTy_i \<subseteq> set (FI_TyArgs funInfo)"
      by (simp add: fset_of_list.rep_eq)
    show "apply_subst tySubst ?paramTy_i
            = apply_subst (IS_TyArgs state) (apply_subst outerSubst ?paramTy_i)"
      unfolding tySubst_def outerSubst_def
      using apply_subst_compose_zip[OF ty_len[symmetric] paramTy_subset ty_dist] .
  qed

  \<comment> \<open>vals_sound translated to tySubst form. \<close>
  have vals_sound_tySubst:
    "\<forall>i < length (FI_TmArgs funInfo).
       sound_term_result state env
         (apply_subst tySubst (fst (snd (FI_TmArgs funInfo ! i))))
         (?valResults ! i)"
  proof (intro allI impI)
    fix i assume i_bound: "i < length (FI_TmArgs funInfo)"
    let ?paramTy_i = "fst (snd (FI_TmArgs funInfo ! i))"
    from vals_sound i_bound have outer_sound:
      "sound_term_result state env (apply_subst outerSubst ?paramTy_i) (?valResults ! i)"
      by blast
    have ground_i: "type_tyvars (apply_subst tySubst ?paramTy_i) = {}"
      using paramTy_apply_ground[OF i_bound] .
    have id_state:
      "apply_subst (IS_TyArgs state) (apply_subst tySubst ?paramTy_i)
       = apply_subst tySubst ?paramTy_i"
      using apply_subst_disjoint_id ground_i by force
    have type_arg_eq:
      "apply_subst (IS_TyArgs state) (apply_subst outerSubst ?paramTy_i)
       = apply_subst tySubst ?paramTy_i"
      using compose_zip[OF i_bound] by simp
    show "sound_term_result state env (apply_subst tySubst ?paramTy_i) (?valResults ! i)"
    proof (cases "?valResults ! i")
      case (Inl err)
      from outer_sound Inl show ?thesis by simp
    next
      case (Inr val)
      from outer_sound Inr have
        "value_has_type env val (apply_subst (IS_TyArgs state) (apply_subst outerSubst ?paramTy_i))"
        by simp
      with type_arg_eq have "value_has_type env val (apply_subst tySubst ?paramTy_i)"
        by simp
      hence "value_has_type env val (apply_subst (IS_TyArgs state) (apply_subst tySubst ?paramTy_i))"
        using id_state by simp
      thus ?thesis using Inr by simp
    qed
  qed

  \<comment> \<open>lvals_sound translated similarly. sound_lvalue_result also applies (IS_TyArgs state). \<close>
  have lvals_sound_tySubst:
    "\<forall>i < length (FI_TmArgs funInfo).
       snd (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow>
         sound_lvalue_result state env storeTyping
           (apply_subst tySubst (fst (snd (FI_TmArgs funInfo ! i))))
           (?refResults ! i)"
  proof (intro allI impI)
    fix i assume i_bound: "i < length (FI_TmArgs funInfo)"
      and is_ref: "snd (snd (FI_TmArgs funInfo ! i)) = Ref"
    let ?paramTy_i = "fst (snd (FI_TmArgs funInfo ! i))"
    from lvals_sound i_bound is_ref have outer_sound:
      "sound_lvalue_result state env storeTyping (apply_subst outerSubst ?paramTy_i) (?refResults ! i)"
      by blast
    have ground_i: "type_tyvars (apply_subst tySubst ?paramTy_i) = {}"
      using paramTy_apply_ground[OF i_bound] .
    have id_state:
      "apply_subst (IS_TyArgs state) (apply_subst tySubst ?paramTy_i)
       = apply_subst tySubst ?paramTy_i"
      using apply_subst_disjoint_id ground_i by force
    have type_arg_eq:
      "apply_subst (IS_TyArgs state) (apply_subst outerSubst ?paramTy_i)
       = apply_subst tySubst ?paramTy_i"
      using compose_zip[OF i_bound] by simp
    show "sound_lvalue_result state env storeTyping (apply_subst tySubst ?paramTy_i)
            (?refResults ! i)"
    proof (cases "?refResults ! i")
      case (Inl err)
      from outer_sound Inl show ?thesis by simp
    next
      case (Inr lval)
      obtain addr path where lval_eq: "lval = (addr, path)" by (cases lval) auto
      from outer_sound Inr lval_eq have
        "addr < length (IS_Store state) \<and>
         type_at_path env (storeTyping ! addr) path
           = Some (apply_subst (IS_TyArgs state) (apply_subst outerSubst ?paramTy_i))"
        by simp
      with type_arg_eq have
        "addr < length (IS_Store state) \<and>
         type_at_path env (storeTyping ! addr) path = Some (apply_subst tySubst ?paramTy_i)"
        by simp
      hence "addr < length (IS_Store state) \<and>
             type_at_path env (storeTyping ! addr) path
               = Some (apply_subst (IS_TyArgs state) (apply_subst tySubst ?paramTy_i))"
        using id_state by simp
      thus ?thesis using Inr lval_eq by simp
    qed
  qed

  \<comment> \<open>fi_match gives var_ref_match and length agreement on IF_Args. \<close>
  from fi_match have var_ref_match:
    "list_all2 (\<lambda>(name1, _, vor1) (name2, vor2). name1 = name2 \<and> vor1 = vor2)
               (FI_TmArgs funInfo) (IF_Args f)"
    unfolding fun_info_matches_interp_fun_def by simp
  from fi_match have len_ifArgs: "length (FI_TmArgs funInfo) = length (IF_Args f)"
    unfolding fun_info_matches_interp_fun_def by simp

  have len_vals: "length (IF_Args f) = length ?valResults"
    using len_ifArgs len_argTms by simp
  have len_refs: "length (IF_Args f) = length ?refResults"
    using len_ifArgs len_argTms by simp

  \<comment> \<open>Invoke H2c with k=0. \<close>
  have k_plus_len_zero: "(0::nat) + length (FI_TmArgs funInfo) = length (FI_TmArgs funInfo)"
    by simp
  have suffix_at_zero: "FI_TmArgs funInfo = drop 0 (FI_TmArgs funInfo)" by simp
  from fold_process_one_arg_sound_gen[
      OF sme_caller wf_env fn_lookup not_ghost suffix_at_zero var_ref_match
         len_vals len_refs k_plus_len_zero vals_sound_tySubst lvals_sound_tySubst
         partial_sound_zero]
  have gen_result:
    "sound_partial_arg_processing_result env funInfo tySubst
       (0 + length (FI_TmArgs funInfo)) storeTyping
       (fold process_one_arg
         (zip (IF_Args f) (zip ?refResults ?valResults)) (Inr ?clearedState))" .

  \<comment> \<open>Bridge from partial_body_env_for at length FI_TmArgs to body_env_for. \<close>
  have pbe_full:
    "partial_body_env_for env funInfo (length (FI_TmArgs funInfo)) = body_env_for env funInfo"
    using partial_body_env_for_full .

  show ?thesis
    unfolding sound_arg_processing_result_def
    using gen_result pbe_full
    unfolding sound_partial_arg_processing_result_def
    by (auto split: sum.splits)
qed


(* Helper 4: restore_scope soundness.
   After a function call, restore_scope builds a final state by taking the
   caller's locals/refs/const-names back from the original state and truncating
   the store to its original length. This lemma shows that the restored state
   matches the caller's env under the *original* storeTyping: we do not grow
   the store typing at all for the caller. The body's store extensions are
   discarded by the truncation.

   Inputs:
   - state_env: the caller's original state matches env under storeTyping
   - post_env_mid: the body's post-state matches env_mid under postStoreTyping
   - ext_post: postStoreTyping extends storeTyping (transitively, via
     bodyStoreTyping)
   - body_calls: interp_function_call gave us this postCallState via running
     a body. We need this so CoreInterpPreservation can tell us the globals
     and functions of postCallState equal those of state. Equivalently, we
     could take a direct hypothesis "IS_Globals postCallState = IS_Globals state
     \<and> IS_Functions postCallState = IS_Functions state". Phrasing it as a
     hypothesis keeps the lemma usable in both the Babylon and extern cases.
   - fixed_eq: env_mid's pinned fields agree with env (required because
     bodyEnv = body_env_for env funInfo and then env_mid agrees with bodyEnv
     on the pinned fields via tyenv_fixed_eq)
*)
lemma restore_scope_sound:
  fixes state postCallState :: "'w InterpState"
  assumes state_env: "state_matches_env state env storeTyping"
      and post_env_mid: "state_matches_env postCallState env_mid postStoreTyping"
      and ext_post: "storeTyping_extends storeTyping postStoreTyping"
      and globals_eq: "IS_Globals postCallState = IS_Globals state"
      and functions_eq: "IS_Functions postCallState = IS_Functions state"
      and dt_eq: "TE_DataCtors env = TE_DataCtors env_mid"
      and ty_eq: "TE_Datatypes env = TE_Datatypes env_mid"
      and gd_eq: "TE_GhostDatatypes env = TE_GhostDatatypes env_mid"
      and wf: "tyenv_well_formed env"
      and wf_mid: "tyenv_well_formed env_mid"
  shows "state_matches_env (restore_scope state postCallState) env storeTyping"
proof -
  let ?rs = "restore_scope state postCallState"

  \<comment> \<open>Unpack the two inputs into their ten conjuncts. \<close>
  from state_env have
    lv_src: "local_vars_exist_in_state state env storeTyping" and
    gv_src: "global_vars_exist_in_state state env" and
    no_lv_src: "no_extra_local_vars state env" and
    no_gv_src: "no_extra_global_vars state env" and
    fes_src: "funs_exist_in_state state env" and
    no_fun_src: "no_extra_funs state env" and
    nc_src: "non_consts_in_locals_or_refs state env" and
    cn_src: "const_locals_match state env" and
    swt_src: "store_well_typed state env storeTyping" and
    ta_src: "ty_args_well_formed state env"
    unfolding state_matches_env_def by blast+

  from post_env_mid have
    swt_post: "store_well_typed postCallState env_mid postStoreTyping"
    unfolding state_matches_env_def by blast

  \<comment> \<open>Basic facts about the restored state's fields. \<close>
  have rs_locals: "IS_Locals ?rs = IS_Locals state" by simp
  have rs_refs: "IS_Refs ?rs = IS_Refs state" by simp
  have rs_consts: "IS_ConstLocals ?rs = IS_ConstLocals state" by simp
  have rs_globals: "IS_Globals ?rs = IS_Globals state"
    using globals_eq by (simp add: restore_scope_preserves_globals_funs)
  have rs_functions: "IS_Functions ?rs = IS_Functions state"
    using functions_eq by (simp add: restore_scope_preserves_globals_funs)
  have rs_tyargs [simp]: "IS_TyArgs ?rs = IS_TyArgs state"
    by (simp add: restore_scope_preserves_globals_funs)

  \<comment> \<open>Store length: equals the old store length, hence matches storeTyping. \<close>
  from swt_src have st_len: "length storeTyping = length (IS_Store state)"
    unfolding store_well_typed_def by simp
  from swt_post have post_len: "length postStoreTyping = length (IS_Store postCallState)"
    unfolding store_well_typed_def by simp
  from ext_post obtain suffix where
    post_eq_suffix: "postStoreTyping = storeTyping @ suffix"
    unfolding storeTyping_extends_def by blast
  hence len_le: "length storeTyping \<le> length postStoreTyping" by simp
  with post_len have "length storeTyping \<le> length (IS_Store postCallState)" by simp
  hence rs_store_len: "length (IS_Store ?rs) = length storeTyping"
    by (simp add: st_len)

  \<comment> \<open>For each prefix address, the value in the truncated store is the same as in
      postCallState, and postStoreTyping agrees with storeTyping there. \<close>
  have rs_store_at: "\<And>addr. addr < length storeTyping
      \<Longrightarrow> IS_Store ?rs ! addr = IS_Store postCallState ! addr"
    using st_len len_le post_len by simp
  have post_st_agree: "\<And>addr. addr < length storeTyping
      \<Longrightarrow> postStoreTyping ! addr = storeTyping ! addr"
    using post_eq_suffix by (simp add: nth_append)

  \<comment> \<open>Field congruences between env and env_mid. \<close>
  have env_mid_fields:
    "TE_DataCtors env = TE_DataCtors env_mid"
    "TE_Datatypes env = TE_Datatypes env_mid"
    "TE_GhostDatatypes env = TE_GhostDatatypes env_mid"
    using dt_eq ty_eq gd_eq by simp_all

  \<comment> \<open>Conjunct 1: local_vars_exist_in_state. Locals/refs come from the old state,
      so this reduces to the original state's witness. The store is truncated,
      but since local addresses are all < length storeTyping, the prefix relation
      on storeTyping is unchanged. \<close>
  have rs_lv: "local_vars_exist_in_state ?rs env storeTyping"
    unfolding local_vars_exist_in_state_def
  proof (intro allI impI, elim conjE)
    fix name ty
    assume lk: "fmlookup (TE_LocalVars env) name = Some ty"
       and ng: "name |\<notin>| TE_GhostLocals env"
    from lv_src lk ng
    have old: "local_var_in_state_with_type state env storeTyping name ty"
      unfolding local_vars_exist_in_state_def by blast
    show "local_var_in_state_with_type ?rs env storeTyping name ty"
      using old rs_locals rs_refs rs_store_len st_len rs_tyargs
      unfolding local_var_in_state_with_type_def Let_def
      by (auto split: option.splits)
  qed

  \<comment> \<open>Conjunct 2: global_vars_exist_in_state. Globals are unchanged (same map),
      so this is direct from state_env. \<close>
  have rs_gv: "global_vars_exist_in_state ?rs env"
    using gv_src rs_globals
    unfolding global_vars_exist_in_state_def global_var_in_state_with_type_def
    by simp

  \<comment> \<open>Conjunct 3: no_extra_local_vars. Direct from state_env via rs_locals/rs_refs. \<close>
  have rs_no_lv: "no_extra_local_vars ?rs env"
    using no_lv_src rs_locals rs_refs
    unfolding no_extra_local_vars_def by simp

  \<comment> \<open>Conjunct 4: no_extra_global_vars. Direct from state_env via rs_globals. \<close>
  have rs_no_gv: "no_extra_global_vars ?rs env"
    using no_gv_src rs_globals
    unfolding no_extra_global_vars_def by simp

  \<comment> \<open>Conjunct 5: funs_exist_in_state. Functions are unchanged. \<close>
  have rs_fes: "funs_exist_in_state ?rs env"
    using fes_src rs_functions
    unfolding funs_exist_in_state_def by simp

  \<comment> \<open>Conjunct 6: no_extra_funs. \<close>
  have rs_no_fun: "no_extra_funs ?rs env"
    using no_fun_src rs_functions
    unfolding no_extra_funs_def by simp

  \<comment> \<open>Conjunct 7: non_consts_in_locals_or_refs. Direct. \<close>
  have rs_nc: "non_consts_in_locals_or_refs ?rs env"
    using nc_src rs_locals rs_refs
    unfolding non_consts_in_locals_or_refs_def by simp

  \<comment> \<open>Conjunct 8: const_locals_match. Direct. \<close>
  have rs_cn: "const_locals_match ?rs env"
    using cn_src rs_consts
    unfolding const_locals_match_def by simp

  \<comment> \<open>Conjunct 9: store_well_typed. The interesting one.
      For each prefix address, the slot has type (storeTyping ! addr) under env.
      We know (postStoreTyping ! addr) = (storeTyping ! addr) and that the slot
      has type (postStoreTyping ! addr) under env_mid. Transferring from env_mid
      to env requires a congruence on value_has_type that covers the fields we
      agree on. The TE_TypeVars / TE_RuntimeTypeVars mismatch is the open
      question — pushing forward to see what breaks.
  \<close>
  have rs_swt: "store_well_typed ?rs env storeTyping"
    unfolding store_well_typed_def
  proof (intro conjI allI impI)
    show "length storeTyping = length (IS_Store ?rs)" using rs_store_len by simp
  next
    fix addr
    assume a_lt: "addr < length (IS_Store ?rs)"
    with rs_store_len have a_lt_st: "addr < length storeTyping" by simp
    from a_lt_st st_len have a_lt_state: "addr < length (IS_Store state)" by simp
    from a_lt_st len_le post_len
    have a_lt_post: "addr < length (IS_Store postCallState)" by simp
    have val_eq: "IS_Store ?rs ! addr = IS_Store postCallState ! addr"
      using rs_store_at a_lt_st by simp
    from swt_post a_lt_post
    have vht_mid: "value_has_type env_mid (IS_Store postCallState ! addr) (postStoreTyping ! addr)"
      unfolding store_well_typed_def by blast
    have ty_eq: "postStoreTyping ! addr = storeTyping ! addr"
      using post_st_agree a_lt_st by simp
    from vht_mid ty_eq
    have vht_mid': "value_has_type env_mid (IS_Store postCallState ! addr) (storeTyping ! addr)"
      by simp
    \<comment> \<open>Derive well-kindedness / runtime of (storeTyping ! addr) in both envs.
        In env: from the original store_well_typed on state under env, the old slot
        value has type (storeTyping ! addr), and value_has_type_well_kinded /
        value_has_type_runtime give us what we need.
        In env_mid: from vht_mid' directly. \<close>
    from swt_src a_lt_state
    have vht_old_env: "value_has_type env (IS_Store state ! addr) (storeTyping ! addr)"
      unfolding store_well_typed_def by blast
    from value_has_type_well_kinded[OF vht_old_env wf]
    have wk_env: "is_well_kinded env (storeTyping ! addr)" .
    from value_has_type_runtime[OF vht_old_env]
    have rt_env: "is_runtime_type env (storeTyping ! addr)" .
    from value_has_type_well_kinded[OF vht_mid' wf_mid]
    have wk_mid: "is_well_kinded env_mid (storeTyping ! addr)" .
    from value_has_type_runtime[OF vht_mid']
    have rt_mid: "is_runtime_type env_mid (storeTyping ! addr)" .
    \<comment> \<open>Transfer env_mid to env using the new well-kinded-aware congruence. \<close>
    have vht_env: "value_has_type env (IS_Store postCallState ! addr) (storeTyping ! addr)"
    proof (rule value_has_type_cong_env_wk[where env=env_mid and env'=env])
      show "TE_DataCtors env = TE_DataCtors env_mid" using env_mid_fields by simp
      show "TE_Datatypes env = TE_Datatypes env_mid" using env_mid_fields by simp
      show "TE_GhostDatatypes env = TE_GhostDatatypes env_mid" using env_mid_fields by simp
      show "tyenv_well_formed env_mid" using wf_mid .
      show "tyenv_well_formed env" using wf .
      show "is_well_kinded env_mid (storeTyping ! addr)" using wk_mid .
      show "is_well_kinded env (storeTyping ! addr)" using wk_env .
      show "is_runtime_type env_mid (storeTyping ! addr)" using rt_mid .
      show "is_runtime_type env (storeTyping ! addr)" using rt_env .
      show "value_has_type env_mid (IS_Store postCallState ! addr) (storeTyping ! addr)"
        using vht_mid' .
    qed
    show "value_has_type env (IS_Store ?rs ! addr) (storeTyping ! addr)"
      using val_eq vht_env by simp
  qed

  have rs_ta: "ty_args_well_formed ?rs env"
    using ta_src rs_tyargs unfolding ty_args_well_formed_def by simp

  from rs_lv rs_gv rs_no_lv rs_no_gv rs_fes rs_no_fun rs_nc rs_cn rs_swt rs_ta
  show ?thesis
    unfolding state_matches_env_def by blast
qed


(*-----------------------------------------------------------------------------*)
(* Unified function-call facts from either typecheck disjunct                  *)
(*                                                                             *)
(* The Assign and VarDecl(Var) cases of type soundness both need to reach the  *)
(* function-call soundness IH (IH_fc) when the rhs is a CoreTm_FunctionCall,   *)
(* regardless of whether the rhs typechecks via core_impure_call_type (impure  *)
(* call) or via core_term_type (pure call). This helper normalizes both        *)
(* branches into the shape IH_fc needs: either we have the full set of        *)
(* function-call facts (including the Ref-position writable-lvalue witness),  *)
(* or the rhs is not a function call and the pure core_term_type fact holds.  *)
(*-----------------------------------------------------------------------------*)

lemma fn_call_facts_from_disjunct:
  assumes disj: "core_impure_call_type env NotGhost tm = Some ty
                 \<or> core_term_type env NotGhost tm = Some ty"
  shows "(\<exists>fnName tyArgs argTms funInfo.
             tm = CoreTm_FunctionCall fnName tyArgs argTms
             \<and> fmlookup (TE_Functions env) fnName = Some funInfo
             \<and> length tyArgs = length (FI_TyArgs funInfo)
             \<and> list_all (is_well_kinded env) tyArgs
             \<and> list_all (is_runtime_type env) tyArgs
             \<and> FI_Ghost funInfo = NotGhost
             \<and> length argTms = length (FI_TmArgs funInfo)
             \<and> list_all2 (\<lambda>tm expectedTy.
                    case core_term_type env NotGhost tm of
                      None \<Rightarrow> False
                    | Some actualTy \<Rightarrow> actualTy = expectedTy)
                 argTms
                 (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                      (FI_TmArgs funInfo))
             \<and> ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                                 (FI_ReturnType funInfo)
             \<and> (\<forall>i < length argTms.
                  snd (snd (FI_TmArgs funInfo ! i)) = Ref
                    \<longrightarrow> is_writable_lvalue env (argTms ! i)))
         \<or> ((\<nexists>fnName tyArgs argTms. tm = CoreTm_FunctionCall fnName tyArgs argTms)
            \<and> core_term_type env NotGhost tm = Some ty)"
proof -
  from disj show ?thesis
  proof
    assume impure: "core_impure_call_type env NotGhost tm = Some ty"
    from impure obtain fnName tyArgs argTms where tm_eq:
      "tm = CoreTm_FunctionCall fnName tyArgs argTms"
      unfolding core_impure_call_type_def
      by (cases tm) (auto split: option.splits if_splits)
    from core_impure_call_type_fn_facts[OF impure tm_eq]
    obtain funInfo where
      fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
      len_tyargs: "length tyArgs = length (FI_TyArgs funInfo)" and
      tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
      tyargs_rt: "list_all (is_runtime_type env) tyArgs" and
      not_ghost_fn: "FI_Ghost funInfo \<noteq> Ghost" and
      len_tmargs: "length argTms = length (FI_TmArgs funInfo)" and
      fn_ty_eq: "ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                                  (FI_ReturnType funInfo)" and
      args_check: "list_all2 (\<lambda>tm expectedTy.
                   case core_term_type env NotGhost tm of
                     None \<Rightarrow> False
                   | Some actualTy \<Rightarrow> actualTy = expectedTy)
                 argTms
                 (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                      (FI_TmArgs funInfo))" and
      ref_lvalues: "\<forall>i < length argTms.
                      snd (snd (FI_TmArgs funInfo ! i)) = Ref
                        \<longrightarrow> is_writable_lvalue env (argTms ! i)"
      by blast
    have fn_not_ghost: "FI_Ghost funInfo = NotGhost"
      using not_ghost_fn by (cases "FI_Ghost funInfo") auto
    from tm_eq fn_lookup len_tyargs tyargs_wk tyargs_rt fn_not_ghost
         len_tmargs args_check fn_ty_eq ref_lvalues
    show ?thesis by blast
  next
    assume pure: "core_term_type env NotGhost tm = Some ty"
    show ?thesis
    proof (cases "\<exists>fnName tyArgs argTms. tm = CoreTm_FunctionCall fnName tyArgs argTms")
      case True
      then obtain fnName tyArgs argTms where tm_eq:
        "tm = CoreTm_FunctionCall fnName tyArgs argTms" by auto
      from pure tm_eq obtain funInfo where
        fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
        len_tyargs: "length tyArgs = length (FI_TyArgs funInfo)" and
        tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
        tyargs_rt: "list_all (is_runtime_type env) tyArgs" and
        not_ghost_fn: "FI_Ghost funInfo \<noteq> Ghost" and
        all_var: "list_all (\<lambda>(_, _, vor). vor = Var) (FI_TmArgs funInfo)" and
        not_impure: "\<not> FI_Impure funInfo" and
        len_tmargs: "length argTms = length (FI_TmArgs funInfo)"
        by (auto simp: Let_def split: option.splits if_splits)
      let ?tySubst = "fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)"
      let ?expectedArgTypes = "map (\<lambda>(_, ty, _). apply_subst ?tySubst ty) (FI_TmArgs funInfo)"
      from pure tm_eq fn_lookup len_tyargs tyargs_wk all_var not_impure
           len_tmargs tyargs_rt not_ghost_fn have
        args_check: "list_all2 (\<lambda>tm expectedTy.
            case core_term_type env NotGhost tm of None \<Rightarrow> False
            | Some actualTy \<Rightarrow> actualTy = expectedTy)
          argTms ?expectedArgTypes" and
        fn_ty_eq: "ty = apply_subst ?tySubst (FI_ReturnType funInfo)"
        by (auto simp: Let_def split: if_splits)
      have fn_not_ghost: "FI_Ghost funInfo = NotGhost"
        using not_ghost_fn by (cases "FI_Ghost funInfo") auto
      \<comment> \<open>Pure function-call: all args are Var, so Ref obligation is vacuous. \<close>
      have ref_lvalues: "\<forall>i < length argTms.
                           snd (snd (FI_TmArgs funInfo ! i)) = Ref
                             \<longrightarrow> is_writable_lvalue env (argTms ! i)"
      proof (intro allI impI)
        fix i assume i_lt: "i < length argTms"
          and is_ref: "snd (snd (FI_TmArgs funInfo ! i)) = Ref"
        with len_tmargs have i_lt_fi: "i < length (FI_TmArgs funInfo)" by simp
        obtain n ti vor where fi_arg: "FI_TmArgs funInfo ! i = (n, ti, vor)"
          by (cases "FI_TmArgs funInfo ! i") auto
        from is_ref fi_arg have vor_eq: "vor = Ref" by simp
        from all_var i_lt_fi fi_arg
        have "(\<lambda>(_, _, vor). vor = Var) (n, ti, vor)"
          by (metis list_all_length)
        hence "vor = Var" by simp
        with vor_eq have False by simp
        thus "is_writable_lvalue env (argTms ! i)" by simp
      qed
      from tm_eq fn_lookup len_tyargs tyargs_wk tyargs_rt fn_not_ghost
           len_tmargs args_check fn_ty_eq ref_lvalues
      show ?thesis by blast
    next
      case False
      thus ?thesis using pure by blast
    qed
  qed
qed


end
