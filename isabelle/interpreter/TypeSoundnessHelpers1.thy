theory TypeSoundnessHelpers1
  imports StateMatchesEnv CoreInterpPreservation
          "../core/CoreStmtTypecheck" "../core/TypeSubst"
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

(* Likewise, sound_statement_result does not depend on TE_ProofTopLevel of either
   env, for the same reasons. *)
lemma sound_statement_result_TE_ProofTopLevel_irrelevant_left [simp]:
  "sound_statement_result (env \<lparr> TE_ProofTopLevel := b \<rparr>) env' storeTyping res
     = sound_statement_result env env' storeTyping res"
proof (cases res)
  case (Inl err) then show ?thesis by simp
next
  case (Inr execRes) then show ?thesis
    by (cases execRes) simp_all
qed

lemma sound_statement_result_TE_ProofTopLevel_irrelevant_right [simp]:
  "sound_statement_result env (env' \<lparr> TE_ProofTopLevel := b \<rparr>) storeTyping res
     = sound_statement_result env env' storeTyping res"
proof (cases res)
  case (Inl err) then show ?thesis by simp
next
  case (Inr execRes) then show ?thesis
    by (cases execRes) simp_all
qed


(*-----------------------------------------------------------------------------*)
(* Various helper lemmas *)
(*-----------------------------------------------------------------------------*)

(* Property of int_complement *)
lemma int_complement_fits:
  assumes "int_fits sign bits i"
  shows "int_fits sign bits (int_complement sign bits i)"
  using assms by (cases sign; cases bits; auto)

(* Lifting is_well_kinded and is_runtime_type through apply_subst (IS_TyArgs state):
   under state_matches_env, the substitution's domain is exactly TE_RuntimeTypeVars
   env (and TE_RuntimeTypeVars |\<subseteq>| TE_TypeVars), and its range types are all
   well-kinded and runtime in env. So applying it to a well-kinded (resp. runtime)
   type gives a well-kinded (resp. runtime) result, in the same env. *)
lemma is_well_kinded_apply_IS_TyArgs:
  assumes sme: "state_matches_env state env storeTyping"
      and wf: "tyenv_well_formed env"
      and wk: "is_well_kinded env ty"
  shows "is_well_kinded env (apply_subst (IS_TyArgs state) ty)"
proof (rule apply_subst_preserves_well_kinded[OF wk])
  show "TE_Datatypes env = TE_Datatypes env" by simp
next
  fix n assume n_in: "n |\<in>| TE_TypeVars env"
  from sme have tawf: "ty_args_well_formed state env"
    unfolding state_matches_env_def by simp
  show "case fmlookup (IS_TyArgs state) n of
          Some ty' \<Rightarrow> is_well_kinded env ty'
        | None \<Rightarrow> n |\<in>| TE_TypeVars env"
  proof (cases "fmlookup (IS_TyArgs state) n")
    case None
    then show ?thesis using n_in by simp
  next
    case (Some ty')
    hence "ty' \<in> fmran' (IS_TyArgs state)" by (simp add: fmran'I)
    with tawf have "is_well_kinded env ty'"
      unfolding ty_args_well_formed_def by blast
    thus ?thesis using Some by simp
  qed
qed

(* When the type's tyvars are covered by the IS_TyArgs domain (e.g. because ty
   is runtime in env, so its tyvars are a subset of TE_RuntimeTypeVars env),
   applying IS_TyArgs eliminates every type variable: the substitution range is
   ground (subst_range_tyvars = {}) by the well-formedness invariant. *)
lemma is_runtime_type_apply_IS_TyArgs_ground:
  assumes sme: "state_matches_env state env storeTyping"
      and rt: "is_runtime_type env ty"
  shows "type_tyvars (apply_subst (IS_TyArgs state) ty) = {}"
proof -
  from sme have tawf: "ty_args_well_formed state env"
    unfolding state_matches_env_def by simp
  hence dom_eq: "fmdom (IS_TyArgs state) = TE_RuntimeTypeVars env"
    and range_ground: "subst_range_tyvars (IS_TyArgs state) = {}"
    unfolding ty_args_well_formed_def by auto
  have tyvars_sub: "type_tyvars ty \<subseteq> fset (TE_RuntimeTypeVars env)"
    using is_runtime_type_tyvars_subset[OF rt] .
  have "type_tyvars (apply_subst (IS_TyArgs state) ty) \<subseteq>
          (type_tyvars ty - fset (fmdom (IS_TyArgs state))) \<union> subst_range_tyvars (IS_TyArgs state)"
    by (rule apply_subst_tyvars_result)
  also have "... \<subseteq> {}"
    using tyvars_sub range_ground dom_eq by auto
  finally show ?thesis by simp
qed

lemma is_runtime_type_apply_IS_TyArgs:
  assumes sme: "state_matches_env state env storeTyping"
      and rt: "is_runtime_type env ty"
  shows "is_runtime_type env (apply_subst (IS_TyArgs state) ty)"
proof (rule apply_subst_preserves_runtime[OF rt])
  show "TE_GhostDatatypes env = TE_GhostDatatypes env" by simp
next
  fix n assume n_in: "n |\<in>| TE_RuntimeTypeVars env"
  from sme have tawf: "ty_args_well_formed state env"
    unfolding state_matches_env_def by simp
  show "case fmlookup (IS_TyArgs state) n of
          Some ty' \<Rightarrow> is_runtime_type env ty'
        | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars env"
  proof (cases "fmlookup (IS_TyArgs state) n")
    case None
    then show ?thesis using n_in by simp
  next
    case (Some ty')
    hence "ty' \<in> fmran' (IS_TyArgs state)" by (simp add: fmran'I)
    with tawf have "is_runtime_type env ty'"
      unfolding ty_args_well_formed_def by blast
    thus ?thesis using Some by simp
  qed
qed

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
  proof (intro allI impI)
    fix name ty
    assume lookup: "fmlookup (TE_GlobalVars env') name = Some ty"
    have "fmlookup (TE_GlobalVars env) name = Some ty"
      using lookup env'_eq by simp
    then have "global_var_in_state_with_type state env name ty"
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
        using state_env state_matches_env_def non_consts_in_locals_or_refs_def
          local_vars_exist_in_state_implies_non_consts_in_locals_or_refs by blast
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
  moreover have "default_ctors_match state'' env'"
    using state_env state''_eq state'_eq env'_eq
    unfolding state_matches_env_def default_ctors_match_def by simp
  moreover have "TE_AbstractTypes env' = {||}"
    using state_env env'_eq unfolding state_matches_env_def by simp
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
    unfolding state_matches_env_def 
    using local_vars_exist_in_state_implies_non_consts_in_locals_or_refs
    by blast+

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
  proof (intro allI impI)
    fix name ty
    assume "fmlookup (TE_GlobalVars env') name = Some ty"
    hence "fmlookup (TE_GlobalVars env) name = Some ty"
      by (simp add: env'_eq)
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

  have dc_tgt: "default_ctors_match state' env'"
    using state_env state'_eq env'_eq
    unfolding state_matches_env_def default_ctors_match_def by simp

  have abs_tgt: "TE_AbstractTypes env' = {||}"
    using state_env env'_eq unfolding state_matches_env_def by simp

  show ?thesis
    unfolding state_matches_env_def
    using lv_tgt gv_tgt no_lv_tgt no_gv_tgt fes_tgt no_fun_tgt nc_tgt cn_tgt swt_tgt ta_tgt dc_tgt abs_tgt
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


(* Add a ghost local: the variable is ghost in env', so it occupies no store slot.
   The interpreter drops the name from the runtime maps (IS_Locals / IS_Refs /
   IS_ConstLocals). storeTyping is unchanged. Used by the Ghost branches of
   CoreStmt_VarDecl(Var) and CoreStmt_VarDeclCall. *)
lemma state_matches_env_add_ghost_local:
  assumes old_sme: "state_matches_env state env storeTyping"
    and env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                               TE_GhostLocals := finsert var (TE_GhostLocals env),
                               TE_ConstLocals := fminus (TE_ConstLocals env) {|var|} \<rparr>"
    and state'_eq: "state' = state \<lparr> IS_Locals := fmdrop var (IS_Locals state),
                                     IS_Refs := fmdrop var (IS_Refs state),
                                     IS_ConstLocals := fminus (IS_ConstLocals state) {|var|} \<rparr>"
  shows "state_matches_env state' env' storeTyping"
proof -
  have tyargs_eq [simp]: "IS_TyArgs state' = IS_TyArgs state" using state'_eq by simp
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
  show "state_matches_env state' env' storeTyping"
    unfolding state_matches_env_def
  proof (intro conjI)
    show "local_vars_exist_in_state state' env' storeTyping"
      unfolding local_vars_exist_in_state_def
    proof (intro allI impI, elim conjE)
      fix name ty
      assume lk: "fmlookup (TE_LocalVars env') name = Some ty"
        and ng: "name |\<notin>| TE_GhostLocals env'"
      from ng env'_eq have "name \<noteq> var" by auto
      with lk env'_eq have lk_old: "fmlookup (TE_LocalVars env) name = Some ty" by simp
      from ng env'_eq \<open>name \<noteq> var\<close> have ng_old: "name |\<notin>| TE_GhostLocals env" by auto
      from old_sme lk_old ng_old
      have "local_var_in_state_with_type state env storeTyping name ty"
        unfolding state_matches_env_def local_vars_exist_in_state_def by blast
      with \<open>name \<noteq> var\<close> tap_eq state'_eq show "local_var_in_state_with_type state' env' storeTyping name ty"
        unfolding local_var_in_state_with_type_def Let_def
        by (auto split: option.splits)
    qed
  next
    show "global_vars_exist_in_state state' env'"
    proof -
      from old_sme have old_gv: "global_vars_exist_in_state state env"
        unfolding state_matches_env_def by simp
      have gv_eq: "TE_GlobalVars env' = TE_GlobalVars env" using env'_eq by simp
      show ?thesis unfolding global_vars_exist_in_state_def
      proof (intro allI impI)
        fix name ty
        assume lk: "fmlookup (TE_GlobalVars env') name = Some ty"
        from lk gv_eq have "fmlookup (TE_GlobalVars env) name = Some ty" by simp
        then have "global_var_in_state_with_type state env name ty"
          using old_gv unfolding global_vars_exist_in_state_def by blast
        thus "global_var_in_state_with_type state' env' name ty"
          using vht_eq state'_eq unfolding global_var_in_state_with_type_def
          by (auto split: option.splits)
      qed
    qed
  next
    show "no_extra_local_vars state' env'"
      unfolding no_extra_local_vars_def
    proof (intro allI impI)
      fix name
      assume ante: "fmlookup (TE_LocalVars env') name = None \<or> name |\<in>| TE_GhostLocals env'"
      show "fmlookup (IS_Locals state') name = None \<and>
            fmlookup (IS_Refs state') name = None"
      proof (cases "name = var")
        case True
        then show ?thesis using state'_eq by simp
      next
        case False
        from ante False env'_eq
        have "fmlookup (TE_LocalVars env) name = None \<or> name |\<in>| TE_GhostLocals env" by auto
        with old_sme have "fmlookup (IS_Locals state) name = None \<and>
            fmlookup (IS_Refs state) name = None"
          unfolding state_matches_env_def no_extra_local_vars_def by blast
        with False state'_eq show ?thesis by simp
      qed
    qed
  next
    show "no_extra_global_vars state' env'"
      using old_sme env'_eq state'_eq
      unfolding state_matches_env_def no_extra_global_vars_def by simp
  next
    show "funs_exist_in_state state' env'"
      unfolding funs_exist_in_state_def
    proof (intro allI impI, elim conjE)
      fix name info
      assume lk: "fmlookup (TE_Functions env') name = Some info"
        and ng: "FI_Ghost info = NotGhost"
      from old_sme have old_fes: "funs_exist_in_state state env"
        unfolding state_matches_env_def by simp
      have funs_eq: "TE_Functions env' = TE_Functions env" using env'_eq by simp
      from lk funs_eq have lk': "fmlookup (TE_Functions env) name = Some info" by simp
      from old_fes lk' ng obtain interpFun where
        if_lk: "fmlookup (IS_Functions state) name = Some interpFun" and
        matches: "fun_info_matches_interp_fun env info interpFun"
        unfolding funs_exist_in_state_def by (auto split: option.splits)
      have if_lk': "fmlookup (IS_Functions state') name = Some interpFun"
        using if_lk state'_eq by simp
      have fcong: "fun_info_matches_interp_fun env' info interpFun =
                    fun_info_matches_interp_fun env info interpFun"
        by (rule fun_info_matches_interp_fun_cong_env)
           (use env'_eq in simp_all)
      have "fun_info_matches_interp_fun env' info interpFun"
        using matches fcong by simp
      with if_lk' show "case fmlookup (IS_Functions state') name of
                          None \<Rightarrow> False
                        | Some interpFun \<Rightarrow> fun_info_matches_interp_fun env' info interpFun"
        by simp
    qed
  next
    show "no_extra_funs state' env'"
      using old_sme env'_eq state'_eq
      unfolding state_matches_env_def no_extra_funs_def by simp
  next
    show "const_locals_match state' env'"
      using old_sme env'_eq state'_eq
      unfolding state_matches_env_def const_locals_match_def by auto
  next
    show "store_well_typed state' env' storeTyping"
      using old_sme vht_eq state'_eq
      unfolding state_matches_env_def store_well_typed_def by simp
  next
    have rt_eq: "\<And>ty. is_runtime_type env' ty = is_runtime_type env ty"
      by (rule is_runtime_type_cong_env) (use env'_fields in simp_all)
    have wk_eq: "\<And>ty. is_well_kinded env' ty = is_well_kinded env ty"
      by (rule is_well_kinded_cong_env) (use env'_fields in simp_all)
    show "ty_args_well_formed state' env'"
      using old_sme env'_fields rt_eq wk_eq state'_eq
      unfolding state_matches_env_def ty_args_well_formed_def by simp
  next
    show "default_ctors_match state' env'"
      using old_sme env'_eq state'_eq
      unfolding state_matches_env_def default_ctors_match_def by simp
  next
    show "TE_AbstractTypes env' = {||}"
      using old_sme env'_eq unfolding state_matches_env_def by simp
  qed
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
    using calculation(1) local_vars_exist_in_state_implies_non_consts_in_locals_or_refs
    by auto

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

  moreover have "default_ctors_match state' env"
    using state_env state'_eq
    unfolding state_matches_env_def default_ctors_match_def by simp

  moreover have "TE_AbstractTypes env = {||}"
    using state_env unfolding state_matches_env_def by blast

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


end
