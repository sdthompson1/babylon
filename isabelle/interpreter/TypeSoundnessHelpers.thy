theory TypeSoundnessHelpers
  imports StateMatchesEnv CoreInterpPreservation CoreInterpErasure
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

fun sound_term_result :: "CoreTyEnv \<Rightarrow> CoreType \<Rightarrow> InterpError + CoreValue \<Rightarrow> bool" where
  "sound_term_result env ty (Inl err) = sound_error_result err"
| "sound_term_result env ty (Inr val) = value_has_type env val ty"

fun sound_term_results :: "CoreTyEnv \<Rightarrow> CoreType list \<Rightarrow> InterpError + CoreValue list \<Rightarrow> bool" where
  "sound_term_results env types (Inl err) = sound_error_result err"
| "sound_term_results env types (Inr vals) = list_all2 (value_has_type env) vals types"

(* A writable lvalue is sound if its address is in the store and its path
   statically descends to the expected type through the store typing.
   This implies: if get_value_at_path succeeds, the obtained value has type ty
   (by get_value_at_path_type); if it fails, the error is RuntimeError
   (by get_value_at_path_error_is_runtime). Callers that need either fact
   should derive it from store_well_typed. *)
fun sound_lvalue_result :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> CoreType list \<Rightarrow> CoreType
    \<Rightarrow> InterpError + (nat \<times> LValuePath list) \<Rightarrow> bool" where
  "sound_lvalue_result state env storeTyping ty (Inl err) = sound_error_result err"
| "sound_lvalue_result state env storeTyping ty (Inr (addr, path)) =
    (addr < length (IS_Store state) \<and>
     type_at_path env (storeTyping ! addr) path = Some ty)"

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

fun sound_function_call_result :: "CoreTyEnv \<Rightarrow> CoreType list \<Rightarrow> CoreType \<Rightarrow>
    InterpError + ('w InterpState \<times> CoreValue) \<Rightarrow> bool" where
  "sound_function_call_result env storeTyping retTy (Inl err) = sound_error_result err"
| "sound_function_call_result env storeTyping retTy (Inr (newState, retVal)) =
    ((\<exists>storeTyping'. state_matches_env newState env storeTyping'
                   \<and> storeTyping_extends storeTyping storeTyping')
     \<and> value_has_type env retVal retTy)"

fun sound_statement_result :: "CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> CoreType list
    \<Rightarrow> InterpError + 'w ExecResult \<Rightarrow> bool" where
  "sound_statement_result env env' storeTyping (Inl err) = sound_error_result err"
| "sound_statement_result env env' storeTyping (Inr (Continue state')) =
    (\<exists>storeTyping'. state_matches_env state' env' storeTyping'
                  \<and> storeTyping_extends storeTyping storeTyping')"
| "sound_statement_result env env' storeTyping (Inr (Return state' retVal)) =
    (value_has_type env retVal (TE_ReturnType env) \<and>
     (\<exists>env_mid storeTyping'. tyenv_fixed_eq env env_mid \<and> tyenv_fixed_eq env_mid env' \<and>
                tyenv_well_formed env_mid \<and>
                state_matches_env state' env_mid storeTyping'
              \<and> storeTyping_extends storeTyping storeTyping'))"


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
    and val_typed: "value_has_type env val rhsTy"
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
  shows "state_matches_env state'' env' (storeTyping @ [rhsTy])"
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

  (* Facts about the new storeTyping *)
  let ?st' = "storeTyping @ [rhsTy]"
  have st'_len: "length ?st' = length (IS_Store state'')"
    using old_st_len store''_eq by simp
  have st'_at_addr: "?st' ! addr = rhsTy"
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
          and st_eq: "storeTyping ! a = ty"
          unfolding local_var_in_state_with_type_def by auto
        from old_addrs[OF a_valid] have a_valid'': "a < length (IS_Store state'')" by simp
        from st'_at_old[OF a_valid] st_eq have "?st' ! a = ty" by simp
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
          path_ty: "type_at_path env (storeTyping ! aa) ba = Some ty"
          unfolding local_var_in_state_with_type_def by auto
        from old_addrs[OF aa_valid] have aa_valid'': "aa < length (IS_Store state'')" by simp
        from st'_at_old[OF aa_valid] have st_at_aa: "?st' ! aa = storeTyping ! aa" by simp
        from path_ty tap_eq st_at_aa
        have path_ty': "type_at_path env' (?st' ! aa) ba = Some ty" by simp
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

  ultimately show ?thesis unfolding state_matches_env_def by auto
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
    and path_ty: "type_at_path env (storeTyping ! addr) path = Some refTy"
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
      have path_ty': "type_at_path env' (storeTyping ! addr) path = Some refTy"
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
        using old lk_locals lk_refs store_eq tap_eq
        unfolding local_var_in_state_with_type_def
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

  show ?thesis
    unfolding state_matches_env_def
    using lv_tgt gv_tgt no_lv_tgt no_gv_tgt fes_tgt no_fun_tgt nc_tgt cn_tgt swt_tgt
    by blast
qed

(* Const specialization: variable is added to ConstNames (used for let-bindings) *)
corollary state_matches_env_add_const_local:
  assumes state_env: "state_matches_env state env storeTyping"
    and val_typed: "value_has_type env val rhsTy"
    and state'_eq: "(state', addr) = alloc_store state val"
    and state''_eq: "state'' = state' \<lparr> IS_Locals := fmupd var addr (IS_Locals state'),
                                        IS_Refs := fmdrop var (IS_Refs state'),
                                        IS_ConstLocals := finsert var (IS_ConstLocals state') \<rparr>"
    and env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                               TE_GhostLocals := fminus (TE_GhostLocals env) {|var|},
                               TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
  shows "state_matches_env state'' env' (storeTyping @ [rhsTy])"
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
    and val_typed: "value_has_type env val rhsTy"
    and state'_eq: "(state', addr) = alloc_store state val"
    and state''_eq: "state'' = state' \<lparr> IS_Locals := fmupd var addr (IS_Locals state'),
                                         IS_Refs := fmdrop var (IS_Refs state'),
                                         IS_ConstLocals := fminus (IS_ConstLocals state') {|var|} \<rparr>"
    and env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                               TE_GhostLocals := fminus (TE_GhostLocals env) {|var|},
                               TE_ConstLocals := fminus (TE_ConstLocals env) {|var|} \<rparr>"
  shows "state_matches_env state'' env' (storeTyping @ [rhsTy])"
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
          dt_nonghost by simp
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
      ultimately show ?thesis using updatedVal_eq ty_eq elem_wk elem_rt dims_wk dims_match
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
      unfolding local_var_in_state_with_type_def
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

  ultimately show ?thesis unfolding state_matches_env_def by auto
qed

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
(* partial_body_env_for env funInfo tySubst k is body_env_for env funInfo with  *)
(* TE_LocalVars restricted to the first k FI_TmArgs (types substituted via     *)
(* tySubst), and TE_ConstLocals restricted to Var-marked names among them.      *)
(* When k = length (FI_TmArgs funInfo), this equals                            *)
(* apply_subst_to_callee_env tySubst env (body_env_for env funInfo).           *)
(* ========================================================================== *)

definition partial_body_env_for ::
    "CoreTyEnv \<Rightarrow> FunInfo \<Rightarrow> (nat, CoreType) fmap \<Rightarrow> nat \<Rightarrow> CoreTyEnv" where
  "partial_body_env_for env funInfo tySubst k =
    (body_env_for env funInfo) \<lparr>
      TE_LocalVars := fmap_of_list
        (map (\<lambda>(name, ty, _). (name, apply_subst tySubst ty))
             (take k (FI_TmArgs funInfo))),
      TE_ConstLocals := fset_of_list
        (map (\<lambda>(name, _, _). name)
             (filter (\<lambda>(_, _, vor). vor = Var) (take k (FI_TmArgs funInfo)))),
      TE_TypeVars := TE_TypeVars env,
      TE_RuntimeTypeVars := TE_RuntimeTypeVars env,
      TE_ReturnType := apply_subst tySubst (FI_ReturnType funInfo)
    \<rparr>"

(* When k = 0, the partial env has no locals and no const names: a body env
   whose locals/refs have been cleared. *)
lemma partial_body_env_for_zero:
  "TE_LocalVars (partial_body_env_for env funInfo tySubst 0) = fmempty"
  "TE_ConstLocals (partial_body_env_for env funInfo tySubst 0) = {||}"
  by (simp_all add: partial_body_env_for_def)

(* When k = length (FI_TmArgs funInfo), the partial env equals the fully
   substituted body env (up to record-update ordering). This is the bridge
   from the induction's end state to the bodyEnv used in case 6. *)
lemma partial_body_env_for_full:
  shows "partial_body_env_for env funInfo tySubst (length (FI_TmArgs funInfo))
         = apply_subst_to_callee_env tySubst env (body_env_for env funInfo)"
proof -
  have fn_eq: "(\<lambda>x. (fst x, apply_subst tySubst (fst (snd x))))
             = (\<lambda>(name, ty, _). (name, apply_subst tySubst ty))"
    by (rule ext) (auto split: prod.splits)
  have locals_eq:
    "fmmap (apply_subst tySubst)
           (fmap_of_list (map (\<lambda>(name, ty, _). (name, ty)) (FI_TmArgs funInfo)))
     = fmap_of_list (map (\<lambda>(name, ty, _). (name, apply_subst tySubst ty)) (FI_TmArgs funInfo))"
    unfolding fn_eq[symmetric]
    by (simp add: fmmap_of_list apsnd_def map_prod_def case_prod_beta comp_def)
  show ?thesis
    by (simp add: partial_body_env_for_def apply_subst_to_callee_env_def
                  body_env_for_def locals_eq)
qed

(* Shape of the sound arg-processing result: the fold either errors soundly
   or produces a state matching the full (substituted) body env. *)
definition sound_arg_processing_result ::
    "CoreTyEnv \<Rightarrow> FunInfo \<Rightarrow> (nat, CoreType) fmap \<Rightarrow> CoreType list
    \<Rightarrow> InterpError + 'w InterpState \<Rightarrow> bool" where
  "sound_arg_processing_result env funInfo tySubst storeTyping result =
    (case result of
      Inl err \<Rightarrow> sound_error_result err
    | Inr preCallState \<Rightarrow>
        \<exists>bodyStoreTyping.
          state_matches_env preCallState
            (apply_subst_to_callee_env tySubst env (body_env_for env funInfo))
            bodyStoreTyping
        \<and> storeTyping_extends storeTyping bodyStoreTyping)"

(* Partial variant: after k steps, the state matches the partial body env with
   some store typing extending the original. *)
definition sound_partial_arg_processing_result ::
    "CoreTyEnv \<Rightarrow> FunInfo \<Rightarrow> (nat, CoreType) fmap \<Rightarrow> nat \<Rightarrow> CoreType list
    \<Rightarrow> InterpError + 'w InterpState \<Rightarrow> bool" where
  "sound_partial_arg_processing_result env funInfo tySubst k storeTyping result =
    (case result of
      Inl err \<Rightarrow> sound_error_result err
    | Inr state \<Rightarrow>
        \<exists>partialStoreTyping.
          state_matches_env state
            (partial_body_env_for env funInfo tySubst k)
            partialStoreTyping
        \<and> storeTyping_extends storeTyping partialStoreTyping)"

(* -------------------------------------------------------------------------- *)
(* H2a. The cleared state matches the k=0 partial body env under the caller's *)
(* store typing (no new slots needed).                                        *)
(* -------------------------------------------------------------------------- *)
lemma cleared_state_matches_partial_env_zero:
  assumes sme: "state_matches_env state env storeTyping"
      and wf: "tyenv_well_formed env"
      and fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo"
      and not_ghost: "FI_Ghost funInfo = NotGhost"
  shows "state_matches_env
           (state \<lparr> IS_Locals := fmempty,
                    IS_Refs := fmempty,
                    IS_ConstLocals := {||} \<rparr>)
           (partial_body_env_for env funInfo tySubst 0)
           storeTyping"
proof -
  let ?clearedState = "state \<lparr> IS_Locals := fmempty,
                                IS_Refs := fmempty,
                                IS_ConstLocals := {||} \<rparr>"
  let ?pEnv = "partial_body_env_for env funInfo tySubst 0"

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
  have pEnv_tyvars: "TE_TypeVars ?pEnv = TE_TypeVars env"
    by (simp add: partial_body_env_for_def)
  have pEnv_rt_tyvars: "TE_RuntimeTypeVars ?pEnv = TE_RuntimeTypeVars env"
    by (simp add: partial_body_env_for_def)

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
    swt_src: "store_well_typed state env storeTyping"
    unfolding state_matches_env_def by blast+

  \<comment> \<open>Discharge each conjunct of state_matches_env for the cleared state and ?pEnv. \<close>

  have lv_tgt: "local_vars_exist_in_state ?clearedState ?pEnv storeTyping"
    unfolding local_vars_exist_in_state_def pEnv_locals by simp

  \<comment> \<open>Need the value_has_type congruence here since global_var_in_state_with_type
      consults value_has_type under ?pEnv. \<close>
  have vht_cong: "\<And>v t. value_has_type ?pEnv v t = value_has_type env v t"
    using value_has_type_cong_env
            [OF pEnv_dactors pEnv_datatypes pEnv_tyvars pEnv_ghost_dt pEnv_rt_tyvars] .

  have gv_tgt: "global_vars_exist_in_state ?clearedState ?pEnv"
    unfolding global_vars_exist_in_state_def
  proof (intro allI impI)
    fix name ty
    assume "fmlookup (TE_GlobalVars ?pEnv) name = Some ty
             \<and> name |\<notin>| TE_GhostGlobals ?pEnv"
    hence "fmlookup (TE_GlobalVars env) name = Some ty"
          "name |\<notin>| TE_GhostGlobals env"
      by (simp_all add: pEnv_globals pEnv_ghost_globals)
    with gv_src have "global_var_in_state_with_type state env name ty"
      unfolding global_vars_exist_in_state_def by blast
    thus "global_var_in_state_with_type ?clearedState ?pEnv name ty"
      unfolding global_var_in_state_with_type_def
      by (simp add: vht_cong split: option.splits)
  qed

  have no_lv_tgt: "no_extra_local_vars ?clearedState ?pEnv"
    unfolding no_extra_local_vars_def by simp

  have no_gv_tgt: "no_extra_global_vars ?clearedState ?pEnv"
    using no_gv_src pEnv_globals pEnv_ghost_globals
    unfolding no_extra_global_vars_def
    by simp

  \<comment> \<open>funs_exist_in_state: TE_Functions is inherited, and fun_info_matches_interp_fun
      only consults fields of its env that ?pEnv inherits from env. \<close>
  have fi_cong: "\<And>info interpFun.
          fun_info_matches_interp_fun env info interpFun
          = fun_info_matches_interp_fun ?pEnv info interpFun"
    using fun_info_matches_interp_fun_cong_env
            [OF pEnv_globals[symmetric] pEnv_ghost_globals[symmetric]
                pEnv_funs[symmetric] pEnv_datatypes[symmetric] pEnv_dactors[symmetric]
                pEnv_dactors_by_ty[symmetric] pEnv_ghost_dt[symmetric]]
    by auto
  have fes_tgt: "funs_exist_in_state ?clearedState ?pEnv"
    unfolding funs_exist_in_state_def
  proof (intro allI impI)
    fix name info
    assume "fmlookup (TE_Functions ?pEnv) name = Some info \<and> FI_Ghost info = NotGhost"
    hence lookup: "fmlookup (TE_Functions env) name = Some info"
      and nghost: "FI_Ghost info = NotGhost"
      by (simp_all add: pEnv_funs)
    from fes_src lookup nghost have
      "case fmlookup (IS_Functions state) name of None \<Rightarrow> False
       | Some interpFun \<Rightarrow> fun_info_matches_interp_fun env info interpFun"
      unfolding funs_exist_in_state_def by blast
    thus "case fmlookup (IS_Functions ?clearedState) name of None \<Rightarrow> False
          | Some interpFun \<Rightarrow> fun_info_matches_interp_fun ?pEnv info interpFun"
      by (simp add: fi_cong split: option.splits)
  qed

  have no_fun_tgt: "no_extra_funs ?clearedState ?pEnv"
    using no_fun_src pEnv_funs
    unfolding no_extra_funs_def
    by simp

  have nc_tgt: "non_consts_in_locals_or_refs ?clearedState ?pEnv"
    unfolding non_consts_in_locals_or_refs_def pEnv_locals by simp

  have cn_tgt: "const_locals_match ?clearedState ?pEnv"
    unfolding const_locals_match_def pEnv_const by simp

  \<comment> \<open>store_well_typed: the store is unchanged; value_has_type depends on fields of
      the env (TE_Datatypes, TE_DataCtors, ...) that ?pEnv inherits from env. \<close>
  have swt_tgt: "store_well_typed ?clearedState ?pEnv storeTyping"
    using swt_src vht_cong
    unfolding store_well_typed_def by simp

  show ?thesis
    unfolding state_matches_env_def
    using lv_tgt gv_tgt no_lv_tgt no_gv_tgt fes_tgt no_fun_tgt nc_tgt cn_tgt swt_tgt
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
  "TE_GlobalVars (partial_body_env_for env funInfo tySubst k) = TE_GlobalVars env"
  "TE_GhostLocals (partial_body_env_for env funInfo tySubst k) = {||}"
  "TE_GhostGlobals (partial_body_env_for env funInfo tySubst k) = TE_GhostGlobals env"
  "TE_Functions (partial_body_env_for env funInfo tySubst k) = TE_Functions env"
  "TE_Datatypes (partial_body_env_for env funInfo tySubst k) = TE_Datatypes env"
  "TE_DataCtors (partial_body_env_for env funInfo tySubst k) = TE_DataCtors env"
  "TE_DataCtorsByType (partial_body_env_for env funInfo tySubst k) = TE_DataCtorsByType env"
  "TE_GhostDatatypes (partial_body_env_for env funInfo tySubst k) = TE_GhostDatatypes env"
  "TE_TypeVars (partial_body_env_for env funInfo tySubst k) = TE_TypeVars env"
  "TE_RuntimeTypeVars (partial_body_env_for env funInfo tySubst k) = TE_RuntimeTypeVars env"
  "TE_ReturnType (partial_body_env_for env funInfo tySubst k) = apply_subst tySubst (FI_ReturnType funInfo)"
  "TE_FunctionGhost (partial_body_env_for env funInfo tySubst k) = NotGhost"
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
    "partial_body_env_for env funInfo tySubst (Suc k)
     = (partial_body_env_for env funInfo tySubst k) \<lparr>
         TE_LocalVars := fmupd paramName (apply_subst tySubst paramTy)
           (TE_LocalVars (partial_body_env_for env funInfo tySubst k)),
         TE_GhostLocals := fminus
           (TE_GhostLocals (partial_body_env_for env funInfo tySubst k)) {|paramName|},
         TE_ConstLocals :=
           (if vor = Var
            then finsert paramName
                   (TE_ConstLocals (partial_body_env_for env funInfo tySubst k))
            else fminus
                   (TE_ConstLocals (partial_body_env_for env funInfo tySubst k))
                   {|paramName|})
       \<rparr>"
proof -
  let ?args = "FI_TmArgs funInfo"

  \<comment> \<open>Standard: take (Suc k) xs = take k xs @ [xs ! k]. \<close>
  have take_Suc: "take (Suc k) ?args = take k ?args @ [?args ! k]"
    using k_bound by (simp add: take_Suc_conv_app_nth)

  \<comment> \<open>Locals: fmap_of_list of the (Suc k)-prefix pairs equals fmupd of the k-th
      entry onto the k-prefix's fmap. We use fmap_of_list_app, which reverses
      the order of append when converting, and fmadd_fmupd/fmadd_empty. \<close>
  let ?pairs_k = "map (\<lambda>(name, ty, _). (name, apply_subst tySubst ty)) (take k ?args)"
  let ?pairs_Sk = "map (\<lambda>(name, ty, _). (name, apply_subst tySubst ty)) (take (Suc k) ?args)"
  have pairs_Sk_eq:
    "?pairs_Sk = ?pairs_k @ [(paramName, apply_subst tySubst paramTy)]"
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
       = fmupd paramName (apply_subst tySubst paramTy) (fmap_of_list ?pairs_k)"
  proof (rule fmap_ext)
    fix name
    show "fmlookup (fmap_of_list ?pairs_Sk) name
        = fmlookup (fmupd paramName (apply_subst tySubst paramTy) (fmap_of_list ?pairs_k)) name"
    proof (cases "name = paramName")
      case True
      have map_of_pairs_k_none: "map_of ?pairs_k paramName = None"
        using paramName_fresh by (auto simp add: map_of_eq_None_iff image_image)
      have "fmlookup (fmap_of_list ?pairs_Sk) paramName
              = map_of ?pairs_Sk paramName"
        by (simp add: fmap_of_list.rep_eq)
      also have "\<dots> = map_of (?pairs_k @ [(paramName, apply_subst tySubst paramTy)]) paramName"
        using pairs_Sk_eq by simp
      also have "\<dots> = Some (apply_subst tySubst paramTy)"
        using map_of_pairs_k_none by (simp add: map_add_Some_iff)
      finally have lhs: "fmlookup (fmap_of_list ?pairs_Sk) paramName
                           = Some (apply_subst tySubst paramTy)" .
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
    "fminus (TE_GhostLocals (partial_body_env_for env funInfo tySubst k)) {|paramName|}
       = TE_GhostLocals (partial_body_env_for env funInfo tySubst (Suc k))"
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
      and val_sound: "sound_term_result env (apply_subst tySubst paramTy) valResult"
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
  from partial_sound obtain partialStoreTyping where
    sme_partial: "state_matches_env partialState
                    (partial_body_env_for env funInfo tySubst k) partialStoreTyping"
    and ext_partial: "storeTyping_extends storeTyping partialStoreTyping"
    unfolding sound_partial_arg_processing_result_def by auto

  show ?thesis
  proof (cases vor)
    case Var
    show ?thesis
    proof (cases valResult)
      case (Inl err)
      \<comment> \<open>Val computation errored. process_one_arg returns Inl err, which is sound
          because sound_term_result env _ (Inl err) = sound_error_result err. \<close>
      from val_sound Inl have err_sound: "sound_error_result err" by simp
      from Var Inl have step_eq:
        "process_one_arg ((paramName, vor), lvalResult, valResult) (Inr partialState)
           = Inl err"
        by simp
      show ?thesis
        using err_sound step_eq
        unfolding sound_partial_arg_processing_result_def by simp
    next
      case (Inr val)
      \<comment> \<open>Val succeeded with value val. Extend the partial state with a new slot
          for val, and set IS_Locals[paramName] = new addr. The resulting state
          matches partial_body_env_for at k+1 under storeTyping extended by
          [apply_subst tySubst paramTy]. \<close>
      from val_sound Inr have val_typed_env:
        "value_has_type env val (apply_subst tySubst paramTy)" by simp

      \<comment> \<open>Transfer val_typed from env to the partial env via congruence. \<close>
      have val_typed_partial:
        "value_has_type (partial_body_env_for env funInfo tySubst k) val
                        (apply_subst tySubst paramTy)"
      proof -
        have "value_has_type (partial_body_env_for env funInfo tySubst k) v t
              = value_has_type env v t" for v t
          using value_has_type_cong_env
                  [OF partial_body_env_for_fields(6) partial_body_env_for_fields(5)
                      partial_body_env_for_fields(9) partial_body_env_for_fields(8)
                      partial_body_env_for_fields(10)] .
        with val_typed_env show ?thesis by simp
      qed

      \<comment> \<open>alloc_store on partialState gives a new state and addr. \<close>
      obtain state' addr where alloc_eq:
        "(state', addr) = alloc_store partialState val"
        by (cases "alloc_store partialState val") auto

      \<comment> \<open>The concrete state'' that process_one_arg produces for the Var branch. \<close>
      let ?state'' = "state' \<lparr> IS_Locals := fmupd paramName addr (IS_Locals state'),
                                IS_Refs := fmdrop paramName (IS_Refs state'),
                                IS_ConstLocals := finsert paramName (IS_ConstLocals state') \<rparr>"

      \<comment> \<open>process_one_arg reduces to Inr ?state''. \<close>
      have step_eq:
        "process_one_arg ((paramName, vor), lvalResult, valResult) (Inr partialState)
           = Inr ?state''"
        using Var Inr alloc_eq
        by (simp add: case_prod_beta)

      \<comment> \<open>env' in the form state_matches_env_add_const_local expects. Uses
          partial_body_env_for_step combined with the fact that the partial env's
          GhostLocals is empty. \<close>
      from wf_env have distinct: "tyenv_fun_param_names_distinct env"
        unfolding tyenv_well_formed_def by simp
      have env'_shape:
        "partial_body_env_for env funInfo tySubst (Suc k)
         = (partial_body_env_for env funInfo tySubst k) \<lparr>
             TE_LocalVars := fmupd paramName (apply_subst tySubst paramTy)
               (TE_LocalVars (partial_body_env_for env funInfo tySubst k)),
             TE_GhostLocals := fminus
               (TE_GhostLocals (partial_body_env_for env funInfo tySubst k)) {|paramName|},
             TE_ConstLocals := finsert paramName
               (TE_ConstLocals (partial_body_env_for env funInfo tySubst k))
           \<rparr>"
        using partial_body_env_for_step[OF k_bound kth_arg distinct fn_lookup] Var
        by simp

      \<comment> \<open>Apply state_matches_env_add_const_local. \<close>
      have sme_new:
        "state_matches_env ?state''
           (partial_body_env_for env funInfo tySubst (Suc k))
           (partialStoreTyping @ [apply_subst tySubst paramTy])"
        using state_matches_env_add_const_local
                [OF sme_partial val_typed_partial alloc_eq refl env'_shape] .

      \<comment> \<open>The new storeTyping extends the outer storeTyping. \<close>
      have ext_new: "storeTyping_extends storeTyping
                       (partialStoreTyping @ [apply_subst tySubst paramTy])"
      proof -
        from ext_partial obtain suffix where
          "partialStoreTyping = storeTyping @ suffix"
          unfolding storeTyping_extends_def by blast
        hence "partialStoreTyping @ [apply_subst tySubst paramTy]
                 = storeTyping @ (suffix @ [apply_subst tySubst paramTy])"
          by simp
        thus ?thesis unfolding storeTyping_extends_def by blast
      qed

      show ?thesis
        using sme_new ext_new step_eq
        unfolding sound_partial_arg_processing_result_def by auto
    qed
  next
    case Ref
    show ?thesis
    proof (cases lvalResult)
      case (Inl err)
      \<comment> \<open>Lvalue computation errored. In the Ref case process_one_arg returns Inl err. \<close>
      from lval_sound[OF Ref] Inl have err_sound: "sound_error_result err" by simp
      from Ref Inl have step_eq:
        "process_one_arg ((paramName, vor), lvalResult, valResult) (Inr partialState)
           = Inl err"
        by simp
      show ?thesis
        using err_sound step_eq
        unfolding sound_partial_arg_processing_result_def by simp
    next
      case (Inr lval)
      obtain addr path where lval_eq: "lval = (addr, path)"
        by (cases lval) auto
      from lval_sound[OF Ref] Inr lval_eq have lval_good:
        "addr < length (IS_Store state)"
        "type_at_path env (storeTyping ! addr) path = Some (apply_subst tySubst paramTy)"
        by auto
      show ?thesis
      proof (cases valResult)
        case Inl_val: (Inl err)
        \<comment> \<open>The Ref arm also propagates value errors. process_one_arg short-circuits
            to Inl err. \<close>
        from val_sound Inl_val have err_sound: "sound_error_result err" by simp
        from Ref Inr lval_eq Inl_val have step_eq:
          "process_one_arg ((paramName, vor), lvalResult, valResult) (Inr partialState)
             = Inl err"
          by simp
        show ?thesis
          using err_sound step_eq
          unfolding sound_partial_arg_processing_result_def by simp
      next
        case Inr_val: (Inr val)
        \<comment> \<open>Both lval and val succeeded. process_one_arg sets
            IS_Refs[paramName] = (addr, path); the store is unchanged. \<close>
        let ?pEnv_k = "partial_body_env_for env funInfo tySubst k"
        let ?state' = "partialState \<lparr> IS_Locals := fmdrop paramName (IS_Locals partialState),
                                       IS_Refs := fmupd paramName (addr, path)
                                                       (IS_Refs partialState),
                                       IS_ConstLocals := fminus (IS_ConstLocals partialState) {|paramName|} \<rparr>"

        \<comment> \<open>process_one_arg reduces to Inr ?state'. \<close>
        have step_eq:
          "process_one_arg ((paramName, vor), lvalResult, valResult) (Inr partialState)
             = Inr ?state'"
          using Ref Inr lval_eq Inr_val by simp

        \<comment> \<open>The address from lval_good is < length of the caller's store, hence
            < length of the partial store (which only grew). \<close>
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

        \<comment> \<open>partialStoreTyping ! addr = storeTyping ! addr (since addr is in the
            original prefix). \<close>
        have pst_at_addr: "partialStoreTyping ! addr = storeTyping ! addr"
          using pst_eq lval_good(1) len_st by (simp add: nth_append)

        \<comment> \<open>Transfer type_at_path from env to the partial env via congruence. \<close>
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
            using type_at_path_cong_env[OF partial_body_env_for_fields(6)[symmetric]]
            by fastforce
          finally show ?thesis by simp
        qed

        \<comment> \<open>paramName is not yet in the partial env's locals (param names are
            distinct, and only the first k params are bound at this stage). \<close>
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
          let ?pairs_k = "map (\<lambda>(name, ty, _). (name, apply_subst tySubst ty))
                              (take k (FI_TmArgs funInfo))"
          have "paramName \<notin> set (map fst ?pairs_k)"
            using not_in_prefix by (auto simp: comp_def case_prod_beta)
          hence "map_of ?pairs_k paramName = None"
            by (auto simp: map_of_eq_None_iff image_image)
          hence "fmlookup (fmap_of_list ?pairs_k) paramName = None"
            by (simp add: fmap_of_list.rep_eq)
          thus ?thesis by (simp add: partial_body_env_for_def)
        qed

        have var_not_ghost: "paramName |\<notin>| TE_GhostLocals ?pEnv_k"
          using partial_body_env_for_fields(2) by simp

        \<comment> \<open>env' in the shape expected by state_matches_env_add_ref. Uses
            partial_body_env_for_step with vor = Ref. \<close>
        from wf_env have distinct: "tyenv_fun_param_names_distinct env"
          unfolding tyenv_well_formed_def by simp
        have env'_shape:
          "partial_body_env_for env funInfo tySubst (Suc k)
           = ?pEnv_k \<lparr>
               TE_LocalVars := fmupd paramName (apply_subst tySubst paramTy)
                 (TE_LocalVars ?pEnv_k),
               TE_GhostLocals := fminus (TE_GhostLocals ?pEnv_k) {|paramName|},
               TE_ConstLocals := fminus (TE_ConstLocals ?pEnv_k) {|paramName|}
             \<rparr>"
          using partial_body_env_for_step[OF k_bound kth_arg distinct fn_lookup] Ref
          by simp

        have sme_new:
          "state_matches_env ?state'
             (partial_body_env_for env funInfo tySubst (Suc k))
             partialStoreTyping"
          using state_matches_env_add_ref
                  [OF sme_partial addr_valid_partial path_ty_partial refl env'_shape
                      var_fresh var_not_ghost] .

        show ?thesis
          using sme_new ext_partial step_eq
          unfolding sound_partial_arg_processing_result_def by auto
      qed
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
               sound_term_result env
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
  \<comment> \<open>Empty suffix: fold is a no-op, partial_sound_k already gives the goal. \<close>
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
  \<comment> \<open>Destructure the head of each list. \<close>
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

  \<comment> \<open>The k-th formal arg is precisely the head of this suffix. \<close>
  from Cons.prems(1) have k_bound: "k < length (FI_TmArgs funInfo)"
    using Cons.prems(5)
    by (metis drop_eq_Nil2 linorder_le_less_linear neq_Nil_conv)
  from Cons.prems(1) have kth: "FI_TmArgs funInfo ! k = arg"
    using k_bound nth_via_drop by metis
  from kth arg_eq
  have kth_arg: "FI_TmArgs funInfo ! k = (paramName, paramTy, vor)" by simp

  \<comment> \<open>Per-position soundness for position 0 of the suffix, i.e. index k of FI_TmArgs. \<close>
  from Cons.prems(6) have val_sound_head:
    "sound_term_result env (apply_subst tySubst paramTy) valHead"
    using arg_eq vals_eq by force
  from Cons.prems(7) have lval_sound_head:
    "vor = Ref \<Longrightarrow> sound_lvalue_result state env storeTyping
                     (apply_subst tySubst paramTy) refHead"
    using arg_eq refs_eq by force

  \<comment> \<open>Step via H2b (Inr case) or preserve-error (Inl case). \<close>
  let ?step = "process_one_arg ((paramName, vor), refHead, valHead) partialResult"
  have step_sound:
    "sound_partial_arg_processing_result env funInfo tySubst (Suc k) storeTyping ?step"
  proof (cases partialResult)
    case (Inl err)
    \<comment> \<open>Error short-circuit. \<close>
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

  \<comment> \<open>Now apply the IH to the tail with k+1. \<close>
  have rest_at_k1: "restArgs = drop (Suc k) (FI_TmArgs funInfo)"
    using Cons.prems(1)
    by (metis Cons_nth_drop_Suc k_bound list.inject)
  have len_rest: "Suc k + length restArgs = length (FI_TmArgs funInfo)"
    using Cons.prems(5) by simp
  have vals_sound_rest: "\<forall>i < length restArgs.
      sound_term_result env
        (apply_subst tySubst (fst (snd (restArgs ! i))))
        (valRest ! i)"
  proof (intro allI impI)
    fix i assume "i < length restArgs"
    hence "Suc i < length (arg # restArgs)" by simp
    from Cons.prems(6)[rule_format, OF this]
    have "sound_term_result env
            (apply_subst tySubst (fst (snd ((arg # restArgs) ! Suc i))))
            (suffixValResults ! Suc i)" .
    thus "sound_term_result env
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
lemma fold_process_one_arg_sound:
  fixes env :: CoreTyEnv
    and funInfo :: FunInfo
    and tySubst :: "(nat, CoreType) fmap"
    and storeTyping :: "CoreType list"
    and state :: "'w InterpState"
    and f :: "'w InterpFun"
  assumes sme_caller: "state_matches_env state env storeTyping"
      and wf_env: "tyenv_well_formed env"
      and fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo"
      and not_ghost: "FI_Ghost funInfo = NotGhost"
      and fi_match: "fun_info_matches_interp_fun env funInfo f"
      and vals_sound:
            "\<forall>i < length (FI_TmArgs funInfo).
               sound_term_result env
                 (apply_subst tySubst (fst (snd (FI_TmArgs funInfo ! i))))
                 (map (interp_term fuel state) argTms ! i)"
      and lvals_sound:
            "\<forall>i < length (FI_TmArgs funInfo).
               snd (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow>
                 sound_lvalue_result state env storeTyping
                   (apply_subst tySubst (fst (snd (FI_TmArgs funInfo ! i))))
                   (map (interp_writable_lvalue fuel state) argTms ! i)"
      and len_argTms: "length argTms = length (FI_TmArgs funInfo)"
  shows "sound_arg_processing_result env funInfo tySubst storeTyping
           (fold process_one_arg
              (zip (IF_Args f)
                   (zip (map (interp_writable_lvalue fuel state) argTms)
                        (map (interp_term fuel state) argTms)))
              (Inr (state \<lparr> IS_Locals := fmempty,
                             IS_Refs := fmempty,
                             IS_ConstLocals := {||} \<rparr>)))"
proof -
  let ?clearedState = "state \<lparr> IS_Locals := fmempty, IS_Refs := fmempty,
                                IS_ConstLocals := {||} \<rparr>"
  let ?valResults = "map (interp_term fuel state) argTms"
  let ?refResults = "map (interp_writable_lvalue fuel state) argTms"

  \<comment> \<open>H2a: initial state is sound at k=0. \<close>
  from cleared_state_matches_partial_env_zero[OF sme_caller wf_env fn_lookup not_ghost]
  have sme_cleared: "state_matches_env ?clearedState
                       (partial_body_env_for env funInfo tySubst 0) storeTyping" .
  have partial_sound_zero:
    "sound_partial_arg_processing_result env funInfo tySubst 0 storeTyping
       (Inr ?clearedState)"
    unfolding sound_partial_arg_processing_result_def
    using sme_cleared storeTyping_extends_refl by auto

  \<comment> \<open>fi_match gives us var_ref_match. \<close>
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

  \<comment> \<open>Invoke the generalized lemma with k=0, suffixFnArgs = FI_TmArgs funInfo. \<close>
  have k_plus_len_zero: "(0::nat) + length (FI_TmArgs funInfo) = length (FI_TmArgs funInfo)"
    by simp
  have suffix_at_zero: "FI_TmArgs funInfo = drop 0 (FI_TmArgs funInfo)" by simp
  have vals_sound_zero:
    "\<forall>i < length (FI_TmArgs funInfo).
       sound_term_result env
         (apply_subst tySubst (fst (snd (FI_TmArgs funInfo ! i))))
         (?valResults ! i)"
    using vals_sound by simp
  have lvals_sound_zero:
    "\<forall>i < length (FI_TmArgs funInfo).
       snd (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow>
         sound_lvalue_result state env storeTyping
           (apply_subst tySubst (fst (snd (FI_TmArgs funInfo ! i))))
           (?refResults ! i)"
    using lvals_sound by simp
  from fold_process_one_arg_sound_gen[
      OF sme_caller wf_env fn_lookup not_ghost suffix_at_zero var_ref_match
         len_vals len_refs k_plus_len_zero vals_sound_zero lvals_sound_zero
         partial_sound_zero]
  have gen_result:
    "sound_partial_arg_processing_result env funInfo tySubst
       (0 + length (FI_TmArgs funInfo)) storeTyping
       (fold process_one_arg
         (zip (IF_Args f) (zip ?refResults ?valResults)) (Inr ?clearedState))" .

  \<comment> \<open>Transfer from partial_sound at length FI_TmArgs to full body_env_for. \<close>
  let ?bodyEnv = "apply_subst_to_callee_env tySubst env (body_env_for env funInfo)"
  have pbe_full:
    "partial_body_env_for env funInfo tySubst (length (FI_TmArgs funInfo)) = ?bodyEnv"
    using partial_body_env_for_full by simp

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

  \<comment> \<open>Unpack the two inputs into their nine conjuncts. \<close>
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
      using old rs_locals rs_refs rs_store_len st_len
      unfolding local_var_in_state_with_type_def
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

  from rs_lv rs_gv rs_no_lv rs_no_gv rs_fes rs_no_fun rs_nc rs_cn rs_swt
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
