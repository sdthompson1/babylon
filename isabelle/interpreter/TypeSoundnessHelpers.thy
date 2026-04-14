theory TypeSoundnessHelpers
  imports StateMatchesEnv "../core/CoreStmtTypecheck"
begin

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
    case (CoreTy_Meta x) with Cons.prems show ?thesis by (cases step) simp_all
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
    case (CoreTy_Meta x) then show ?thesis by (cases step) simp_all
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
                                        IS_ConstNames := new_state_cn \<rparr>"
    and env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                               TE_GhostLocals := fminus (TE_GhostLocals env) {|var|},
                               TE_ConstNames := new_env_cn \<rparr>"
    and cn_match: "const_names_match state'' env'"
    and cn_other: "\<And>name. name \<noteq> var \<Longrightarrow>
                     (name |\<in>| TE_ConstNames env' \<longleftrightarrow> name |\<in>| TE_ConstNames env)"
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
  have refs''_eq: "IS_Refs state'' = IS_Refs state"
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
      and nc: "name |\<notin>| TE_ConstNames env'"
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
      moreover have "name |\<notin>| TE_ConstNames env"
        using nc cn_other[OF False] by simp
      ultimately have "fmlookup (IS_Locals state) name \<noteq> None \<or>
                       fmlookup (IS_Refs state) name \<noteq> None"
        using state_env
        unfolding state_matches_env_def non_consts_in_locals_or_refs_def by blast
      then show ?thesis using False locals''_eq refs''_eq by simp
    qed
  qed

  (* 8. const_names_match *)
  moreover have "const_names_match state'' env'"
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

(* Const specialization: variable is added to ConstNames (used for let-bindings) *)
corollary state_matches_env_add_const_local:
  assumes state_env: "state_matches_env state env storeTyping"
    and val_typed: "value_has_type env val rhsTy"
    and state'_eq: "(state', addr) = alloc_store state val"
    and state''_eq: "state'' = state' \<lparr> IS_Locals := fmupd var addr (IS_Locals state'),
                                        IS_ConstNames := finsert var (IS_ConstNames state') \<rparr>"
    and env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                               TE_GhostLocals := fminus (TE_GhostLocals env) {|var|},
                               TE_ConstNames := finsert var (TE_ConstNames env) \<rparr>"
  shows "state_matches_env state'' env' (storeTyping @ [rhsTy])"
proof -
  from state'_eq have "IS_ConstNames state' = IS_ConstNames state" by auto
  hence "IS_ConstNames state'' = finsert var (TE_ConstNames env)"
    using state_env state''_eq
    unfolding state_matches_env_def const_names_match_def by simp
  hence cn: "const_names_match state'' env'"
    using env'_eq unfolding const_names_match_def by simp
  have cn_oth: "\<And>name. name \<noteq> var \<Longrightarrow>
      (name |\<in>| TE_ConstNames env' \<longleftrightarrow> name |\<in>| TE_ConstNames env)"
    using env'_eq by auto
  show ?thesis
    using state_matches_env_add_local[OF state_env val_typed state'_eq state''_eq env'_eq
                                        cn cn_oth] .
qed

(* Non-const specialization: ConstNames unchanged (used for var declarations) *)
corollary state_matches_env_add_nonconst_local:
  assumes state_env: "state_matches_env state env storeTyping"
    and val_typed: "value_has_type env val rhsTy"
    and state'_eq: "(state', addr) = alloc_store state val"
    and state''_eq: "state'' = state' \<lparr> IS_Locals := fmupd var addr (IS_Locals state') \<rparr>"
    and env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                               TE_GhostLocals := fminus (TE_GhostLocals env) {|var|},
                               TE_ConstNames := TE_ConstNames env \<rparr>"
  shows "state_matches_env state'' env' (storeTyping @ [rhsTy])"
proof -
  have state''_eq': "state'' = state' \<lparr> IS_Locals := fmupd var addr (IS_Locals state'),
                                         IS_ConstNames := IS_ConstNames state' \<rparr>"
    using state''_eq by simp
  from state'_eq have "IS_ConstNames state' = IS_ConstNames state" by auto
  hence "IS_ConstNames state'' = TE_ConstNames env"
    using state_env state''_eq
    unfolding state_matches_env_def const_names_match_def by simp
  hence cn: "const_names_match state'' env'"
    using env'_eq unfolding const_names_match_def by simp
  have cn_oth: "\<And>name. name \<noteq> var \<Longrightarrow>
      (name |\<in>| TE_ConstNames env' \<longleftrightarrow> name |\<in>| TE_ConstNames env)"
    using env'_eq by simp
  show ?thesis
    using state_matches_env_add_local[OF state_env val_typed state'_eq state''_eq' env'_eq
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
      then show ?thesis using updatedVal_eq ty_eq by simp
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
      from Cons.prems(1) CV_Variant obtain dtName argTypes metavars payloadTy where
        ty_eq: "ty = CoreTy_Datatype dtName argTypes" and
        ctor_lookup: "fmlookup (TE_DataCtors env) ctor = Some (dtName, metavars, payloadTy)" and
        len_eq: "length metavars = length argTypes" and
        args_wk: "list_all (is_well_kinded env) argTypes" and
        args_rt: "list_all (is_runtime_type env) argTypes" and
        dt_nonghost: "dtName |\<notin>| TE_GhostDatatypes env" and
        payload_typed: "value_has_type env payload
            (apply_subst (fmap_of_list (zip metavars argTypes)) payloadTy)"
        by (cases ty) (auto split: option.splits prod.splits)
      let ?payloadTy = "apply_subst (fmap_of_list (zip metavars argTypes)) payloadTy"
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
      from Cons.prems(1) CV_Variant obtain dtName argTypes metavars payloadTy where
        ty_eq: "ty = CoreTy_Datatype dtName argTypes" and
        ctor_lookup: "fmlookup (TE_DataCtors env) ctor = Some (dtName, metavars, payloadTy)" and
        payload_typed: "value_has_type env payload
                          (apply_subst (fmap_of_list (zip metavars argTypes)) payloadTy)"
        by (cases ty) (auto split: option.splits)
      from Cons.prems(2) CV_Variant LVPath_VariantProj have ctor_match: "ctor = expectedCtor"
        and get_rest: "get_value_at_path payload rest = Inr v"
        by (auto split: if_splits)
      let ?subPayloadTy = "apply_subst (fmap_of_list (zip metavars argTypes)) payloadTy"
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
    from Cons.prems(1) CV_Variant obtain dtName argTypes metavars payloadTy where
      slotTy_eq: "slotTy = CoreTy_Datatype dtName argTypes" and
      ctor_lookup: "fmlookup (TE_DataCtors env) ctor = Some (dtName, metavars, payloadTy)" and
      payload_typed: "value_has_type env payload
                        (apply_subst (fmap_of_list (zip metavars argTypes)) payloadTy)"
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
                      (apply_subst (fmap_of_list (zip metavars argTypes)) payloadTy) rest
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
    from Cons.prems(1) CV_Variant obtain dtName argTypes metavars payloadTy where
      slotTy_eq: "slotTy = CoreTy_Datatype dtName argTypes" and
      ctor_lookup: "fmlookup (TE_DataCtors env) ctor = Some (dtName, metavars, payloadTy)" and
      payload_typed: "value_has_type env payload
                        (apply_subst (fmap_of_list (zip metavars argTypes)) payloadTy)"
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
                      (apply_subst (fmap_of_list (zip metavars argTypes)) payloadTy) rest
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
    cn'_eq: "IS_ConstNames state' = IS_ConstNames state"
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

  (* 8. const_names_match: unchanged *)
  moreover have "const_names_match state' env"
    using state_env cn'_eq
    unfolding state_matches_env_def const_names_match_def by simp

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

(* If some pattern in the arm list matches the value, find_matching_arm succeeds *)
lemma find_matching_arm_succeeds:
  assumes "\<exists>pat rhs. (pat, rhs) \<in> set arms \<and> pattern_matches val pat"
  shows "\<exists>rhs. find_matching_arm val arms = Inr rhs"
  using assms
proof (induction arms)
  case Nil then show ?case by simp
next
  case (Cons arm arms)
  obtain pat' rhs' where pr_in: "(pat', rhs') \<in> set (arm # arms)"
    and pr_matches: "pattern_matches val pat'" using Cons.prems by auto
  obtain p r where arm_eq: "arm = (p, r)" by (cases arm) auto
  show ?case
  proof (cases "pattern_matches val p")
    case True then show ?thesis using arm_eq by simp
  next
    case no_match: False
    from pr_in no_match have "(pat', rhs') \<in> set arms"
      using arm_eq pr_matches by auto
    hence "\<exists>pat rhs. (pat, rhs) \<in> set arms \<and> pattern_matches val pat"
      using pr_matches by auto
    from Cons.IH[OF this] show ?thesis
      using no_match arm_eq by simp
  qed
qed

(* If find_matching_arm succeeds, the result is the body of some arm in the list *)
lemma find_matching_arm_in_set:
  assumes "find_matching_arm val arms = Inr rhs"
  shows "\<exists>pat. (pat, rhs) \<in> set arms"
  using assms by (induction arms) (auto split: if_splits)

(* If has_wildcard holds, some element is CorePat_Wildcard *)
lemma has_wildcard_in_set_aux:
  "has_wildcard pats \<Longrightarrow> CorePat_Wildcard \<in> set pats"
  by (induction pats rule: has_wildcard.induct) auto

lemma has_wildcard_in_set:
  "has_wildcard (map fst arms) \<Longrightarrow> \<exists>arm \<in> set arms. fst arm = CorePat_Wildcard"
  using has_wildcard_in_set_aux image_iff by fastforce

(* If has_wildcard holds for the patterns, find_matching_arm succeeds *)
lemma has_wildcard_find_matching_arm:
  assumes "has_wildcard (map fst arms)"
  shows "\<exists>rhs. find_matching_arm val arms = Inr rhs"
proof -
  from has_wildcard_in_set[OF assms]
  obtain pat rhs where in_arms: "(pat, rhs) \<in> set arms" and pat_wild: "pat = CorePat_Wildcard"
    by auto
  have "pattern_matches val CorePat_Wildcard" by (cases val) simp_all
  hence "pattern_matches val pat" using pat_wild by simp
  thus ?thesis using find_matching_arm_succeeds in_arms by fastforce
qed

(* Main exhaustiveness lemma: if patterns are exhaustive and the value has the
   scrutinee type, then find_matching_arm succeeds *)
lemma find_matching_arm_exhaustive:
  assumes val_typed: "value_has_type env val scrutTy"
    and exhaustive: "patterns_exhaustive env scrutTy (map fst arms)"
    and wf: "tyenv_well_formed env"
  shows "\<exists>rhs. find_matching_arm val arms = Inr rhs"
proof (cases "has_wildcard (map fst arms)")
  case True
  then show ?thesis using has_wildcard_find_matching_arm by blast
next
  case no_wildcard: False
  show ?thesis
  proof (cases scrutTy)
    case CoreTy_Bool
    from exhaustive no_wildcard CoreTy_Bool have
      has_true: "list_ex (\<lambda>p. p = CorePat_Bool True) (map fst arms)" and
      has_false: "list_ex (\<lambda>p. p = CorePat_Bool False) (map fst arms)"
      by simp_all
    from val_typed CoreTy_Bool obtain b where val_eq: "val = CV_Bool b"
      using value_has_type_Bool by auto
    show ?thesis
    proof (cases b)
      case True
      from has_true obtain arm where arm_in: "arm \<in> set arms" and arm_pat: "fst arm = CorePat_Bool True"
        by (auto simp: list_ex_iff)
      have "pattern_matches val (fst arm)" using val_eq True arm_pat by simp
      thus ?thesis using find_matching_arm_succeeds arm_in
        by (metis prod.collapse)
    next
      case False
      from has_false obtain arm where arm_in: "arm \<in> set arms" and arm_pat: "fst arm = CorePat_Bool False"
        by (auto simp: list_ex_iff)
      have "pattern_matches val (fst arm)" using val_eq False arm_pat by simp
      thus ?thesis using find_matching_arm_succeeds arm_in
        by (metis prod.collapse)
    qed
  next
    case (CoreTy_Datatype dtName tyArgs)
    from exhaustive no_wildcard CoreTy_Datatype obtain ctors where
      ctors_lookup: "fmlookup (TE_DataCtorsByType env) dtName = Some ctors" and
      all_covered: "list_all (\<lambda>ctor. list_ex (\<lambda>p. p = CorePat_Variant ctor) (map fst arms)) ctors"
      by (auto split: option.splits)
    (* Value must be a variant *)
    from val_typed CoreTy_Datatype obtain actualCtor payload where
      val_eq: "val = CV_Variant actualCtor payload"
      using value_has_type_Name by blast
    (* Extract constructor info from value typing *)
    from val_typed val_eq CoreTy_Datatype obtain dtName2 metavars payloadTy where
      ctor_lookup: "fmlookup (TE_DataCtors env) actualCtor = Some (dtName2, metavars, payloadTy)" and
      dt_eq: "dtName = dtName2"
      by (auto split: option.splits prod.splits)
    (* By tyenv_ctors_by_type_consistent, actualCtor is in ctors *)
    from wf have consistent: "tyenv_ctors_by_type_consistent env"
      unfolding tyenv_well_formed_def by simp
    from consistent ctors_lookup have
      "\<forall>ctorName. ctorName \<in> set ctors \<longleftrightarrow>
        (\<exists>tyArgMetavars payload. fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyArgMetavars, payload))"
      unfolding tyenv_ctors_by_type_consistent_def by simp
    hence ctor_in_ctors: "actualCtor \<in> set ctors"
      using ctor_lookup dt_eq by auto
    (* So there is a CorePat_Variant actualCtor in the pattern list *)
    from all_covered ctor_in_ctors have
      "list_ex (\<lambda>p. p = CorePat_Variant actualCtor) (map fst arms)"
      by (simp add: list_all_iff)
    then obtain arm where arm_in: "arm \<in> set arms" and arm_pat: "fst arm = CorePat_Variant actualCtor"
      by (auto simp: list_ex_iff)
    have "pattern_matches val (fst arm)" using val_eq arm_pat by simp
    thus ?thesis using find_matching_arm_succeeds arm_in
      by (metis prod.collapse)
  next
    (* Remaining type cases: exhaustive is False when no wildcard, contradiction *)
    case (CoreTy_FiniteInt x1 x2)
    then show ?thesis using exhaustive no_wildcard by simp
  next
    case CoreTy_MathInt
    then show ?thesis using exhaustive no_wildcard by simp
  next
    case CoreTy_MathReal
    then show ?thesis using exhaustive no_wildcard by simp
  next
    case (CoreTy_Record x)
    then show ?thesis using exhaustive no_wildcard by simp
  next
    case (CoreTy_Array x1 x2)
    then show ?thesis using exhaustive no_wildcard by simp
  next
    case (CoreTy_Meta x)
    then show ?thesis using exhaustive no_wildcard by simp
  qed
qed

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
    then show ?thesis using "2_2" sizes_eq by simp
  qed
qed


end
