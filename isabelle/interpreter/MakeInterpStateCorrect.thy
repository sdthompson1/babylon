theory MakeInterpStateCorrect
  imports MakeInterpState TypeSoundness "../core/CoreModuleTypecheck"
begin

(* ========================================================================== *)
(* Correctness of make_interp_state                                           *)
(* ========================================================================== *)

(* This theory proves that make_interp_state, applied to a closed and
   well-typed CoreModule (with contract-satisfying extern functions),
   produces a state satisfying state_matches_env against the normalized
   module's type environment, with an empty store typing.

   Proof plan. Write m' = normalize_module m and env = CM_TyEnv m'.
    1. The placeholder defaults are computed against base_interp_state, which
       matches a *stripped* env (globals, ghost-globals and functions emptied)
       vacuously; default_value_sound then types each placeholder, and the
       value typing transfers to env by congruence (value_has_type does not
       read the stripped fields).
    2. The state holding all placeholders and the built function map matches
       env itself (every declared non-ghost global is defined, by closedness,
       and its placeholder has the declared type; every declared non-ghost
       function got a matching InterpFun).
    3. Each initializer evaluation step preserves state_matches_env: the
       initializer typechecks at its declared type (module_globals_well_typed),
       interp_term is sound in a matching state (type_soundness), and
       overwriting a declared non-ghost global with a value of its declared
       type preserves the match. *)


(* ========================================================================== *)
(* The stripped environment                                                   *)
(* ========================================================================== *)

(* env with globals and functions removed: the environment matched (trivially)
   by base_interp_state, used to bootstrap default_value_sound before any
   globals exist. *)
definition strip_module_env :: "CoreTyEnv \<Rightarrow> CoreTyEnv" where
  "strip_module_env env =
     env \<lparr> TE_GlobalVars := fmempty,
           TE_GhostGlobals := {||},
           TE_Functions := fmempty \<rparr>"

lemma strip_module_env_simps [simp]:
  "TE_LocalVars (strip_module_env env) = TE_LocalVars env"
  "TE_GlobalVars (strip_module_env env) = fmempty"
  "TE_GhostLocals (strip_module_env env) = TE_GhostLocals env"
  "TE_GhostGlobals (strip_module_env env) = {||}"
  "TE_ConstLocals (strip_module_env env) = TE_ConstLocals env"
  "TE_TypeVars (strip_module_env env) = TE_TypeVars env"
  "TE_RuntimeTypeVars (strip_module_env env) = TE_RuntimeTypeVars env"
  "TE_AbstractTypes (strip_module_env env) = TE_AbstractTypes env"
  "TE_ReturnType (strip_module_env env) = TE_ReturnType env"
  "TE_FunctionGhost (strip_module_env env) = TE_FunctionGhost env"
  "TE_ProofGoal (strip_module_env env) = TE_ProofGoal env"
  "TE_ProofTopLevel (strip_module_env env) = TE_ProofTopLevel env"
  "TE_Functions (strip_module_env env) = fmempty"
  "TE_Datatypes (strip_module_env env) = TE_Datatypes env"
  "TE_DataCtors (strip_module_env env) = TE_DataCtors env"
  "TE_DataCtorsByType (strip_module_env env) = TE_DataCtorsByType env"
  "TE_GhostDatatypes (strip_module_env env) = TE_GhostDatatypes env"
  by (simp_all add: strip_module_env_def)

(* The stripped fields are invisible to the type-level judgements. *)
lemma strip_module_env_well_kinded [simp]:
  "is_well_kinded (strip_module_env env) ty = is_well_kinded env ty"
  by (rule is_well_kinded_cong_env) simp_all

lemma strip_module_env_runtime_type [simp]:
  "is_runtime_type (strip_module_env env) ty = is_runtime_type env ty"
  by (rule is_runtime_type_cong_env) simp_all

lemma strip_module_env_value_has_type [simp]:
  "value_has_type (strip_module_env env) v ty = value_has_type env v ty"
  by (rule value_has_type_cong_env) simp_all

(* Stripping the globals and functions preserves well-formedness: the clauses
   about globals and functions become vacuous, and every other clause reads
   only unchanged fields. *)
lemma strip_module_env_well_formed:
  assumes wf: "tyenv_well_formed env"
  shows "tyenv_well_formed (strip_module_env env)"
proof -
  let ?se = "strip_module_env env"

  \<comment> \<open>Congruences for the clauses that override TE_TypeVars (and possibly
      TE_RuntimeTypeVars) on the way in.\<close>
  have wk_scope_eq:
    "\<And>tvs ty. is_well_kinded (?se \<lparr> TE_TypeVars := tvs \<rparr>) ty
            = is_well_kinded (env \<lparr> TE_TypeVars := tvs \<rparr>) ty"
    by (rule is_well_kinded_cong_env) (simp_all add: strip_module_env_def)
  have rt_scope_eq:
    "\<And>tvs rtvs ty.
       is_runtime_type (?se \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) ty
     = is_runtime_type (env \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) ty"
    by (rule is_runtime_type_cong_env) (simp_all add: strip_module_env_def)

  from wf have
    vars_wk: "tyenv_vars_well_kinded env" and
    vars_rt: "tyenv_vars_runtime env" and
    ghost_subset: "tyenv_ghost_vars_subset env" and
    ret_wk: "tyenv_return_type_well_kinded env" and
    ret_rt: "tyenv_return_type_runtime env" and
    ctors_cons: "tyenv_ctors_consistent env" and
    payloads_wk: "tyenv_payloads_well_kinded env" and
    ctor_tyvars_distinct: "tyenv_ctor_tyvars_distinct env" and
    ctors_by_type: "tyenv_ctors_by_type_consistent env" and
    nonghost_payloads: "tyenv_nonghost_payloads_runtime env" and
    ghost_dt_subset: "tyenv_ghost_datatypes_subset env" and
    rt_subset: "tyenv_runtime_tyvars_subset env" and
    abs_subset: "tyenv_abstract_types_subset env" and
    dt_nonempty: "tyenv_datatypes_nonempty env"
    unfolding tyenv_well_formed_def by auto

  have c1: "tyenv_vars_well_kinded ?se"
    using vars_wk unfolding tyenv_vars_well_kinded_def by simp
  have c2: "tyenv_vars_runtime ?se"
    using vars_rt unfolding tyenv_vars_runtime_def by simp
  have c3: "tyenv_ghost_vars_subset ?se"
    using ghost_subset unfolding tyenv_ghost_vars_subset_def by simp
  have c4: "tyenv_return_type_well_kinded ?se"
    using ret_wk unfolding tyenv_return_type_well_kinded_def by simp
  have c5: "tyenv_return_type_runtime ?se"
    using ret_rt unfolding tyenv_return_type_runtime_def by simp
  have c6: "tyenv_ctors_consistent ?se"
    using ctors_cons unfolding tyenv_ctors_consistent_def by simp
  have c7: "tyenv_payloads_well_kinded ?se"
    using payloads_wk unfolding tyenv_payloads_well_kinded_def
    by (simp add: wk_scope_eq)
  have c8: "tyenv_ctor_tyvars_distinct ?se"
    using ctor_tyvars_distinct unfolding tyenv_ctor_tyvars_distinct_def by simp
  have c9: "tyenv_ctors_by_type_consistent ?se"
    using ctors_by_type unfolding tyenv_ctors_by_type_consistent_def by simp
  have c10: "tyenv_fun_types_well_kinded ?se"
    unfolding tyenv_fun_types_well_kinded_def by simp
  have c11: "tyenv_fun_tyvars_distinct ?se"
    unfolding tyenv_fun_tyvars_distinct_def by simp
  have c12: "tyenv_fun_ghost_constraint ?se"
    unfolding tyenv_fun_ghost_constraint_def by simp
  have c13: "tyenv_nonghost_payloads_runtime ?se"
    using nonghost_payloads unfolding tyenv_nonghost_payloads_runtime_def
    by (simp add: rt_scope_eq)
  have c14: "tyenv_ghost_datatypes_subset ?se"
    using ghost_dt_subset unfolding tyenv_ghost_datatypes_subset_def by simp
  have c15: "tyenv_runtime_tyvars_subset ?se"
    using rt_subset unfolding tyenv_runtime_tyvars_subset_def by simp
  have c16: "tyenv_abstract_types_subset ?se"
    using abs_subset unfolding tyenv_abstract_types_subset_def by simp
  have c17: "tyenv_datatypes_nonempty ?se"
    using dt_nonempty unfolding tyenv_datatypes_nonempty_def by simp

  from c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17
  show ?thesis unfolding tyenv_well_formed_def by blast
qed


(* ========================================================================== *)
(* default_ctors_map                                                          *)
(* ========================================================================== *)

(* default_ctors_map answers exactly the lookups default_ctors_match asks
   about. *)
lemma default_ctors_map_lookup:
  assumes byType: "fmlookup (TE_DataCtorsByType env) dtName
                     = Some (defCtorName # otherCtors)"
      and ctor: "fmlookup (TE_DataCtors env) defCtorName
                     = Some (dtName', tyVars, payload)"
  shows "fmlookup (default_ctors_map env) dtName = Some (defCtorName, tyVars, payload)"
proof -
  have dc: "default_ctor_for env dtName = Some (defCtorName, tyVars, payload)"
    using byType ctor by (simp add: default_ctor_for_def)
  show ?thesis
    using byType dc by (simp add: default_ctors_map_def)
qed

(* Any state carrying default_ctors_map env satisfies default_ctors_match
   against any environment with the same datatype tables as env. *)
lemma default_ctors_map_match:
  assumes dcs: "IS_DefaultCtors state = default_ctors_map env0"
      and byType_eq: "TE_DataCtorsByType env = TE_DataCtorsByType env0"
      and ctors_eq: "TE_DataCtors env = TE_DataCtors env0"
  shows "default_ctors_match state env"
  unfolding default_ctors_match_def
proof (intro allI impI)
  fix dtName defCtorName otherCtors dtName' tyvars payload
  assume "fmlookup (TE_DataCtorsByType env) dtName = Some (defCtorName # otherCtors)"
     and "fmlookup (TE_DataCtors env) defCtorName = Some (dtName', tyvars, payload)"
  hence "fmlookup (default_ctors_map env0) dtName = Some (defCtorName, tyvars, payload)"
    unfolding byType_eq ctors_eq by (rule default_ctors_map_lookup)
  thus "fmlookup (IS_DefaultCtors state) dtName = Some (defCtorName, tyvars, payload)"
    by (simp add: dcs)
qed


(* ========================================================================== *)
(* The base state matches the stripped environment                            *)
(* ========================================================================== *)

lemma base_interp_state_matches:
  assumes scope: "tyenv_module_scope env"
      and tv: "TE_TypeVars env = {||}"
      and rtv: "TE_RuntimeTypeVars env = {||}"
  shows "state_matches_env (base_interp_state env world) (strip_module_env env) []"
proof -
  let ?st = "base_interp_state env world"
  let ?se = "strip_module_env env"
  from scope have locals: "TE_LocalVars env = fmempty"
    and constlocals: "TE_ConstLocals env = {||}"
    and ghostlocals: "TE_GhostLocals env = {||}"
    and abs_tv: "TE_AbstractTypes env = TE_TypeVars env"
    unfolding tyenv_module_scope_def by simp_all
  have dcm: "default_ctors_match ?st ?se"
  proof -
    have "IS_DefaultCtors ?st = default_ctors_map env"
      by (simp add: base_interp_state_def)
    moreover have "TE_DataCtorsByType ?se = TE_DataCtorsByType env"
      by simp
    moreover have "TE_DataCtors ?se = TE_DataCtors env"
      by simp
    ultimately show ?thesis
      by (rule default_ctors_map_match)
  qed
  have ranEmpty: "fmran' (fmempty :: (string, CoreType) fmap) = {}"
    by (auto simp: fmlookup_ran'_iff)
  have srtEmpty: "subst_range_tyvars fmempty = {}"
    by (simp add: subst_range_tyvars_def ranEmpty)
  show ?thesis
    unfolding state_matches_env_def
              local_vars_exist_in_state_def global_vars_exist_in_state_def
              no_extra_local_vars_def no_extra_global_vars_def
              funs_exist_in_state_def no_extra_funs_def
              const_locals_match_def store_well_typed_def
              ty_args_well_formed_def
    using dcm
    by (simp add: base_interp_state_def locals constlocals ghostlocals
                  tv rtv abs_tv ranEmpty srtEmpty)
qed


(* ========================================================================== *)
(* Body environments                                                          *)
(* ========================================================================== *)

(* For a non-ghost function in a module with no abstract types, the module
   typechecker's body environment coincides with the interpreter's. *)
lemma module_body_env_for_eq_body_env_for:
  assumes abs_empty: "TE_AbstractTypes env = {||}"
      and ng: "FI_Ghost info = NotGhost"
  shows "module_body_env_for env names info = body_env_for env names info"
  using assms unfolding module_body_env_for_def body_env_for_def by simp


(* ========================================================================== *)
(* build_interp_funs                                                          *)
(* ========================================================================== *)

(* A successful build gives every listed non-ghost function a matching
   InterpFun: the fields of make_interp_fun, with the Core body, or the
   supplied ExternFunc for an extern function. *)
lemma build_interp_funs_lookup_some:
  assumes ok: "build_interp_funs externs env pairs = Inr funs"
      and mem: "(name, f) \<in> set pairs"
      and dist: "distinct (map fst pairs)"
      and info_lk: "fmlookup (TE_Functions env) name = Some info"
      and ng: "FI_Ghost info = NotGhost"
  shows "\<exists>body. fmlookup funs name = Some (make_interp_fun info f body)
              \<and> (case CF_Body f of
                   Some stmts \<Rightarrow> body = Inl stmts
                 | None \<Rightarrow> (\<exists>externFun. fmlookup externs name = Some externFun
                                       \<and> body = Inr externFun))"
  using ok mem dist
proof (induction pairs arbitrary: funs)
  case Nil
  then show ?case by simp
next
  case (Cons p rest)
  obtain n1 f1 where p_eq: "p = (n1, f1)" by (cases p) auto
  from Cons.prems(1) p_eq obtain info1 where
    info1_lk: "fmlookup (TE_Functions env) n1 = Some info1"
    by (auto split: option.splits)
  from Cons.prems(1) p_eq info1_lk obtain acc where
    rest_ok: "build_interp_funs externs env rest = Inr acc"
    by (auto split: sum.splits)
  show ?case
  proof (cases "n1 = name")
    case True
    with Cons.prems(3) p_eq have not_in_rest: "name \<notin> fst ` set rest"
      by simp
    from Cons.prems(2) p_eq True not_in_rest have f1_eq: "f1 = f"
      by (metis fst_conv image_eqI set_ConsD prod.inject)
    from True info1_lk info_lk have info1_eq: "info1 = info" by simp
    show ?thesis
    proof (cases "CF_Body f")
      case (Some stmts)
      have "funs = fmupd name (make_interp_fun info f (Inl stmts)) acc"
        using Cons.prems(1) p_eq True f1_eq info1_lk info1_eq rest_ok ng Some
        by (auto split: if_splits)
      then show ?thesis using Some by simp
    next
      case None
      from Cons.prems(1) p_eq True f1_eq info1_lk info1_eq rest_ok ng None
      obtain externFun where
        ext_lk: "fmlookup externs name = Some externFun" and
        funs_eq: "funs = fmupd name (make_interp_fun info f (Inr externFun)) acc"
        by (auto split: if_splits option.splits)
      then show ?thesis using None by auto
    qed
  next
    case False
    from Cons.prems(1) p_eq info1_lk rest_ok False
    have lk_eq: "fmlookup funs name = fmlookup acc name"
      by (auto split: if_splits option.splits)
    from Cons.prems(2) p_eq False have mem_rest: "(name, f) \<in> set rest" by auto
    from Cons.prems(3) have dist_rest: "distinct (map fst rest)" by simp
    from Cons.IH[OF rest_ok mem_rest dist_rest] lk_eq show ?thesis by simp
  qed
qed

(* Names that occur in the list only as ghost functions (or not at all) are
   absent from the built map. *)
lemma build_interp_funs_lookup_none:
  assumes ok: "build_interp_funs externs env pairs = Inr funs"
      and ghost_only:
        "\<And>f. (name, f) \<in> set pairs \<Longrightarrow>
           \<exists>info. fmlookup (TE_Functions env) name = Some info \<and> FI_Ghost info = Ghost"
  shows "fmlookup funs name = None"
  using ok ghost_only
proof (induction pairs arbitrary: funs)
  case Nil
  then show ?case by simp
next
  case (Cons p rest)
  obtain n1 f1 where p_eq: "p = (n1, f1)" by (cases p) auto
  from Cons.prems(1) p_eq obtain info1 where
    info1_lk: "fmlookup (TE_Functions env) n1 = Some info1"
    by (auto split: option.splits)
  from Cons.prems(1) p_eq info1_lk obtain acc where
    rest_ok: "build_interp_funs externs env rest = Inr acc"
    by (auto split: sum.splits)
  have acc_none: "fmlookup acc name = None"
    using Cons.IH[OF rest_ok] Cons.prems(2) p_eq by auto
  show ?case
  proof (cases "n1 = name")
    case True
    from Cons.prems(2) p_eq True obtain info where
      "fmlookup (TE_Functions env) name = Some info" and "FI_Ghost info = Ghost"
      by auto
    with True info1_lk have ghost1: "FI_Ghost info1 = Ghost" by simp
    have "funs = acc"
      using Cons.prems(1) p_eq info1_lk rest_ok ghost1 by auto
    then show ?thesis using acc_none by simp
  next
    case False
    from Cons.prems(1) p_eq info1_lk rest_ok False
    have "fmlookup funs name = fmlookup acc name"
      by (auto split: if_splits option.splits)
    then show ?thesis using acc_none by simp
  qed
qed


(* ========================================================================== *)
(* compute_global_defaults                                                    *)
(* ========================================================================== *)

(* A successful defaults computation covers exactly the listed names. *)
lemma compute_global_defaults_dom:
  assumes ok: "compute_global_defaults fuel baseState env pairs = Inr defaults"
  shows "fmdom defaults = fset_of_list (map fst pairs)"
  using ok
proof (induction pairs arbitrary: defaults)
  case Nil
  then show ?case by simp
next
  case (Cons p rest)
  obtain n1 tm1 where p_eq: "p = (n1, tm1)" by (cases p) auto
  from Cons.prems p_eq obtain declTy v acc where
    "fmlookup (TE_GlobalVars env) n1 = Some declTy" and
    "default_value fuel baseState declTy = Inr v" and
    rest_ok: "compute_global_defaults fuel baseState env rest = Inr acc" and
    defaults_eq: "defaults = fmupd n1 v acc"
    by (auto split: option.splits sum.splits)
  show ?case
    using Cons.IH[OF rest_ok] p_eq defaults_eq by simp
qed

(* Every stored default is default_value at the name's declared type. *)
lemma compute_global_defaults_typing:
  assumes ok: "compute_global_defaults fuel baseState env pairs = Inr defaults"
      and lk: "fmlookup defaults name = Some v"
  shows "\<exists>declTy. fmlookup (TE_GlobalVars env) name = Some declTy
                \<and> default_value fuel baseState declTy = Inr v"
  using ok lk
proof (induction pairs arbitrary: defaults)
  case Nil
  then show ?case by simp
next
  case (Cons p rest)
  obtain n1 tm1 where p_eq: "p = (n1, tm1)" by (cases p) auto
  from Cons.prems(1) p_eq obtain declTy1 v1 acc where
    decl1: "fmlookup (TE_GlobalVars env) n1 = Some declTy1" and
    def1: "default_value fuel baseState declTy1 = Inr v1" and
    rest_ok: "compute_global_defaults fuel baseState env rest = Inr acc" and
    defaults_eq: "defaults = fmupd n1 v1 acc"
    by (auto split: option.splits sum.splits)
  show ?case
  proof (cases "n1 = name")
    case True
    with Cons.prems(2) defaults_eq have "v = v1" by simp
    with True decl1 def1 show ?thesis by auto
  next
    case False
    with Cons.prems(2) defaults_eq have "fmlookup acc name = Some v" by simp
    from Cons.IH[OF rest_ok this] show ?thesis .
  qed
qed


(* ========================================================================== *)
(* Updating one global preserves the match                                    *)
(* ========================================================================== *)

(* If the runtime type variables are empty, a matching state has no type-
   argument bindings. *)
lemma state_matches_env_tyargs_empty:
  assumes sm: "state_matches_env state env storeTyping"
      and rtv: "TE_RuntimeTypeVars env = {||}"
  shows "IS_TyArgs state = fmempty"
proof -
  have "fmdom (IS_TyArgs state) = {||}"
    using sm rtv unfolding state_matches_env_def ty_args_well_formed_def by simp
  thus ?thesis
    by (metis fmrestrict_fset_dom fmrestrict_fset_null)
qed

(* Updating IS_Globals does not affect local_var_in_state_with_type: the
   predicate reads only IS_TyArgs, IS_Locals, IS_Refs and IS_Store. Proved via
   unfolding (plain rewriting) because simp's weak case congruences block
   record simplification inside the case branches. *)
lemma local_var_in_state_with_type_globals_update [simp]:
  "local_var_in_state_with_type (st \<lparr> IS_Globals := g \<rparr>) env storeTyping n ty
     = local_var_in_state_with_type st env storeTyping n ty"
proof -
  have sel:
    "IS_TyArgs (st \<lparr> IS_Globals := g \<rparr>) = IS_TyArgs st"
    "IS_Locals (st \<lparr> IS_Globals := g \<rparr>) = IS_Locals st"
    "IS_Refs (st \<lparr> IS_Globals := g \<rparr>) = IS_Refs st"
    "IS_Store (st \<lparr> IS_Globals := g \<rparr>) = IS_Store st"
    by simp_all
  show ?thesis
    unfolding local_var_in_state_with_type_def sel
    by (rule refl)
qed

(* Overwriting a declared, non-ghost global with a value of its declared type
   preserves state_matches_env. *)
lemma state_matches_env_update_global:
  assumes sm: "state_matches_env state env storeTyping"
      and decl: "fmlookup (TE_GlobalVars env) name = Some declTy"
      and ng: "name |\<notin>| TE_GhostGlobals env"
      and vt: "value_has_type env v declTy"
  shows "state_matches_env
           (state \<lparr> IS_Globals := fmupd name v (IS_Globals state) \<rparr>)
           env storeTyping"
proof -
  let ?st = "state \<lparr> IS_Globals := fmupd name v (IS_Globals state) \<rparr>"
  from sm have
    lv: "local_vars_exist_in_state state env storeTyping" and
    gv: "global_vars_exist_in_state state env" and
    nel: "no_extra_local_vars state env" and
    neg: "no_extra_global_vars state env" and
    fe: "funs_exist_in_state state env" and
    nef: "no_extra_funs state env" and
    clm: "const_locals_match state env" and
    swt: "store_well_typed state env storeTyping" and
    taw: "ty_args_well_formed state env" and
    dcm: "default_ctors_match state env" and
    abs: "TE_AbstractTypes env = {||}"
    unfolding state_matches_env_def by blast+

  have gv': "global_vars_exist_in_state ?st env"
    unfolding global_vars_exist_in_state_def
  proof (intro allI impI)
    fix n ty
    assume a: "fmlookup (TE_GlobalVars env) n = Some ty \<and> n |\<notin>| TE_GhostGlobals env"
    show "global_var_in_state_with_type ?st env n ty"
    proof (cases "n = name")
      case True
      with a decl have "ty = declTy" by simp
      with True vt show ?thesis
        unfolding global_var_in_state_with_type_def by simp
    next
      case False
      have "global_var_in_state_with_type state env n ty"
        using gv a unfolding global_vars_exist_in_state_def by blast
      with False show ?thesis
        unfolding global_var_in_state_with_type_def by simp
    qed
  qed

  have neg': "no_extra_global_vars ?st env"
    unfolding no_extra_global_vars_def
  proof (intro allI impI)
    fix n
    assume a: "fmlookup (TE_GlobalVars env) n = None \<or> n |\<in>| TE_GhostGlobals env"
    have n_ne: "n \<noteq> name" using a decl ng by auto
    have "fmlookup (IS_Globals state) n = None"
      using neg a unfolding no_extra_global_vars_def by blast
    with n_ne show "fmlookup (IS_Globals ?st) n = None" by simp
  qed

  have lv': "local_vars_exist_in_state ?st env storeTyping"
    using lv unfolding local_vars_exist_in_state_def by simp
  have nel': "no_extra_local_vars ?st env"
    using nel unfolding no_extra_local_vars_def by simp
  have fe': "funs_exist_in_state ?st env"
    using fe unfolding funs_exist_in_state_def by simp
  have nef': "no_extra_funs ?st env"
    using nef unfolding no_extra_funs_def by simp
  have clm': "const_locals_match ?st env"
    using clm unfolding const_locals_match_def by simp
  have swt': "store_well_typed ?st env storeTyping"
    using swt unfolding store_well_typed_def by simp
  have taw': "ty_args_well_formed ?st env"
    using taw unfolding ty_args_well_formed_def by simp
  have dcm': "default_ctors_match ?st env"
    using dcm unfolding default_ctors_match_def by simp

  from lv' gv' nel' neg' fe' nef' clm' swt' taw' dcm' abs
  show ?thesis unfolding state_matches_env_def by blast
qed


(* ========================================================================== *)
(* Evaluating the initializers preserves the match                            *)
(* ========================================================================== *)

(* Fold invariant for eval_globals: starting from a matching state and
   evaluating (in any order) initializers of declared non-ghost globals, the
   final state still matches. Each step is interpreter soundness at the
   initializer's declared type, plus the one-global update lemma. *)
lemma eval_globals_preserves_match:
  assumes wf: "tyenv_well_formed env"
      and rtv: "TE_RuntimeTypeVars env = {||}"
      and gwt: "module_globals_well_typed env globals"
      and pairs_ok: "\<forall>p \<in> set pairs.
            fmlookup globals (fst p) = Some (snd p) \<and> fst p |\<notin>| TE_GhostGlobals env"
      and sm: "state_matches_env (state :: 'w InterpState) env storeTyping"
      and ok: "eval_globals fuel state pairs = Inr state'"
  shows "state_matches_env state' env storeTyping"
  using pairs_ok sm ok
proof (induction pairs arbitrary: state)
  case Nil
  then show ?case by simp
next
  case (Cons p rest)
  obtain name tm where p_eq: "p = (name, tm)" by (cases p) auto
  from Cons.prems(3) p_eq obtain v where
    interp: "interp_term fuel state tm = Inr v" and
    rest_ok: "eval_globals fuel
                (state \<lparr> IS_Globals := fmupd name v (IS_Globals state) \<rparr>) rest
              = Inr state'"
    by (auto split: sum.splits)
  from Cons.prems(1) p_eq have
    glk: "fmlookup globals name = Some tm" and
    ng: "name |\<notin>| TE_GhostGlobals env"
    by auto
  from gwt glk ng obtain declTy where
    decl: "fmlookup (TE_GlobalVars env) name = Some declTy" and
    typing: "core_term_type env NotGhost tm = Some declTy"
    unfolding module_globals_well_typed_def by (auto split: if_splits)
  have tyargs: "IS_TyArgs state = fmempty"
    by (rule state_matches_env_tyargs_empty[OF Cons.prems(2) rtv])
  have "sound_term_result state env declTy (interp_term fuel state tm)"
    using interp_term_sound[OF Cons.prems(2) wf] typing by blast
  hence vt: "value_has_type env v declTy"
    using interp tyargs by simp
  have sm': "state_matches_env
               (state \<lparr> IS_Globals := fmupd name v (IS_Globals state) \<rparr>)
               env storeTyping"
    by (rule state_matches_env_update_global[OF Cons.prems(2) decl ng vt])
  show ?case
    using Cons.IH[OF _ sm' rest_ok] Cons.prems(1) by simp
qed


(* ========================================================================== *)
(* sorted_list_of_fmap                                                        *)
(* ========================================================================== *)

(* The keys of the sorted association list are distinct. *)
lemma distinct_map_fst_sorted_list_of_fmap:
  "distinct (map fst (sorted_list_of_fmap m))"
proof -
  have "map fst (sorted_list_of_fmap m) = sorted_list_of_fset (fmdom m)"
    unfolding sorted_list_of_fmap_def by (simp add: comp_def)
  moreover have "distinct (sorted_list_of_fset (fmdom m))"
    by (simp add: sorted_list_of_fset.rep_eq)
  ultimately show ?thesis by simp
qed

(* Membership in the sorted association list is exactly map lookup. *)
lemma sorted_list_of_fmap_mem_iff:
  "((name, v) \<in> set (sorted_list_of_fmap m)) = (fmlookup m name = Some v)"
proof
  assume "(name, v) \<in> set (sorted_list_of_fmap m)"
  hence "map_of (sorted_list_of_fmap m) name = Some v"
    by (rule map_of_is_SomeI[OF distinct_map_fst_sorted_list_of_fmap])
  thus "fmlookup m name = Some v" by simp
next
  assume "fmlookup m name = Some v"
  hence "map_of (sorted_list_of_fmap m) name = Some v" by simp
  thus "(name, v) \<in> set (sorted_list_of_fmap m)" by (rule map_of_SomeD)
qed


(* ========================================================================== *)
(* The placeholder defaults are well-typed values                             *)
(* ========================================================================== *)

(* A successful default_value at a declared non-ghost global's type yields a
   value of that type. Bootstrapped through the stripped environment: the base
   state matches it vacuously, so default_value_sound applies, and the value
   typing transfers back to env by congruence. *)
lemma global_default_value_typed:
  assumes wf: "tyenv_well_formed env"
      and scope: "tyenv_module_scope env"
      and tv: "TE_TypeVars env = {||}"
      and rtv: "TE_RuntimeTypeVars env = {||}"
      and decl: "fmlookup (TE_GlobalVars env) name = Some declTy"
      and ng: "name |\<notin>| TE_GhostGlobals env"
      and dv: "default_value fuel (base_interp_state env world) declTy = Inr v"
  shows "value_has_type env v declTy"
proof -
  let ?se = "strip_module_env env"
  have abs_tv: "TE_AbstractTypes env = TE_TypeVars env"
    using scope unfolding tyenv_module_scope_def by simp

  \<comment> \<open>The declared type is well-kinded in env (the well-formedness clause
      checks it with TE_TypeVars reset to the module-level abstract types,
      which equal TE_TypeVars at module scope).\<close>
  have wk0: "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env \<rparr>) declTy"
    using wf decl
    unfolding tyenv_well_formed_def tyenv_vars_well_kinded_def by blast
  have wk_eq: "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env \<rparr>) declTy
                 = is_well_kinded env declTy"
    by (rule is_well_kinded_cong_env) (simp_all add: abs_tv)
  have wk: "is_well_kinded env declTy" using wk0 wk_eq by simp

  \<comment> \<open>Likewise a runtime type (non-ghost global).\<close>
  have rt0: "is_runtime_type
               (env \<lparr> TE_TypeVars := TE_AbstractTypes env,
                      TE_RuntimeTypeVars :=
                        TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env \<rparr>)
               declTy"
    using wf decl ng
    unfolding tyenv_well_formed_def tyenv_vars_runtime_def by blast
  have rt_eq: "is_runtime_type
                 (env \<lparr> TE_TypeVars := TE_AbstractTypes env,
                        TE_RuntimeTypeVars :=
                          TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env \<rparr>)
                 declTy
               = is_runtime_type env declTy"
    by (rule is_runtime_type_cong_env) (simp_all add: rtv finter_fempty_right)
  have rt: "is_runtime_type env declTy" using rt0 rt_eq by simp

  \<comment> \<open>And ground, since TE_TypeVars is empty.\<close>
  have ground: "type_tyvars declTy = {}"
    using is_well_kinded_type_tyvars_subset[OF wk] tv by auto

  have sm: "state_matches_env (base_interp_state env world) ?se []"
    by (rule base_interp_state_matches[OF scope tv rtv])
  have wf': "tyenv_well_formed ?se"
    by (rule strip_module_env_well_formed[OF wf])
  have dv_sound: "case default_value fuel (base_interp_state env world) declTy of
                    Inl err \<Rightarrow> sound_error_result err
                  | Inr val \<Rightarrow> value_has_type ?se val declTy"
  proof (rule default_value_sound_main[OF sm wf'])
    show "is_well_kinded ?se declTy" by (simp add: wk)
    show "is_runtime_type ?se declTy" by (simp add: rt)
    show "type_tyvars declTy = {}" by (rule ground)
  qed
  with dv show ?thesis by simp
qed


(* ========================================================================== *)
(* The assembled state (defaults + functions) matches the environment         *)
(* ========================================================================== *)

(* The state holding all placeholder defaults and the built function map
   matches env: every declared non-ghost global is defined (by the domain
   equality from closedness) and its placeholder has the declared type; every
   declared non-ghost function has a matching InterpFun; nothing extra
   exists. *)
lemma assembled_state_matches:
  assumes wf: "tyenv_well_formed env"
      and scope: "tyenv_module_scope env"
      and tv: "TE_TypeVars env = {||}"
      and rtv: "TE_RuntimeTypeVars env = {||}"
      and gdom: "fmdom (TE_GlobalVars env) = fmdom globals"
      and fdom: "fmdom (TE_Functions env) = fmdom funDefs"
      and fwt: "module_functions_well_typed env funDefs"
      and defaults_ok: "compute_global_defaults fuel (base_interp_state env world) env
                          (filter (\<lambda>(name, _). name |\<notin>| TE_GhostGlobals env)
                             (sorted_list_of_fmap globals)) = Inr defaults"
      and funs_ok: "build_interp_funs externs env (sorted_list_of_fmap funDefs) = Inr funs"
      and externs_ok: "\<And>name info externFun.
            \<lbrakk> fmlookup (TE_Functions env) name = Some info;
              fmlookup externs name = Some externFun \<rbrakk> \<Longrightarrow>
            extern_fun_contract env info externFun"
  shows "state_matches_env
           (base_interp_state env world \<lparr> IS_Globals := defaults, IS_Functions := funs \<rparr>)
           env []"
proof -
  let ?st = "base_interp_state env world \<lparr> IS_Globals := defaults, IS_Functions := funs \<rparr>"
  let ?ngPairs = "filter (\<lambda>(name, _). name |\<notin>| TE_GhostGlobals env)
                    (sorted_list_of_fmap globals)"

  from scope have locals: "TE_LocalVars env = fmempty"
    and ghostlocals: "TE_GhostLocals env = {||}"
    and constlocals: "TE_ConstLocals env = {||}"
    and abs_tv: "TE_AbstractTypes env = TE_TypeVars env"
    unfolding tyenv_module_scope_def by simp_all
  have abs: "TE_AbstractTypes env = {||}" using abs_tv tv by simp

  have st_sel:
    "IS_Globals ?st = defaults"
    "IS_Locals ?st = fmempty"
    "IS_Refs ?st = fmempty"
    "IS_Store ?st = []"
    "IS_ConstLocals ?st = {||}"
    "IS_TyArgs ?st = fmempty"
    "IS_DefaultCtors ?st = default_ctors_map env"
    "IS_Functions ?st = funs"
    by (simp_all add: base_interp_state_def)

  have defaults_dom: "fmdom defaults = fset_of_list (map fst ?ngPairs)"
    by (rule compute_global_defaults_dom[OF defaults_ok])

  \<comment> \<open>Membership in the filtered global list is lookup plus non-ghostness.\<close>
  have ng_mem: "\<And>n tm. ((n, tm) \<in> set ?ngPairs)
                  = (fmlookup globals n = Some tm \<and> n |\<notin>| TE_GhostGlobals env)"
    by (auto simp add: sorted_list_of_fmap_mem_iff)

  \<comment> \<open>Conjunct: declared non-ghost globals exist with their declared types.\<close>
  have gv: "global_vars_exist_in_state ?st env"
    unfolding global_vars_exist_in_state_def
  proof (intro allI impI)
    fix n ty
    assume a: "fmlookup (TE_GlobalVars env) n = Some ty \<and> n |\<notin>| TE_GhostGlobals env"
    hence decl: "fmlookup (TE_GlobalVars env) n = Some ty"
      and ng: "n |\<notin>| TE_GhostGlobals env" by auto
    have "n |\<in>| fmdom globals" using fmdomI[OF decl] gdom by simp
    then obtain tm where "fmlookup globals n = Some tm"
      by (auto simp add: fmlookup_dom_iff)
    hence "(n, tm) \<in> set ?ngPairs" using ng ng_mem by presburger
    hence "n |\<in>| fmdom defaults"
      unfolding defaults_dom by (force simp add: fset_of_list_elem)
    then obtain v where v_lk: "fmlookup defaults n = Some v"
      by (auto simp add: fmlookup_dom_iff)
    obtain declTy where
      decl': "fmlookup (TE_GlobalVars env) n = Some declTy" and
      dv: "default_value fuel (base_interp_state env world) declTy = Inr v"
      using compute_global_defaults_typing[OF defaults_ok v_lk] by auto
    have "declTy = ty" using decl decl' by simp
    hence vt: "value_has_type env v ty"
      using global_default_value_typed[OF wf scope tv rtv decl' ng dv] by simp
    show "global_var_in_state_with_type ?st env n ty"
      unfolding global_var_in_state_with_type_def
      by (simp add: st_sel v_lk vt)
  qed

  \<comment> \<open>Conjunct: no globals beyond the declared non-ghost ones.\<close>
  have neg: "no_extra_global_vars ?st env"
    unfolding no_extra_global_vars_def
  proof (intro allI impI)
    fix n
    assume a: "fmlookup (TE_GlobalVars env) n = None \<or> n |\<in>| TE_GhostGlobals env"
    have "n |\<notin>| fmdom defaults"
    proof (rule notI)
      assume "n |\<in>| fmdom defaults"
      then obtain tm where "(n, tm) \<in> set ?ngPairs"
        unfolding defaults_dom by (force simp add: fset_of_list_elem)
      hence lk: "fmlookup globals n = Some tm"
        and ng: "n |\<notin>| TE_GhostGlobals env"
        by (simp_all add: sorted_list_of_fmap_mem_iff)
      have "n |\<in>| fmdom (TE_GlobalVars env)" using fmdomI[OF lk] gdom by simp
      hence "fmlookup (TE_GlobalVars env) n \<noteq> None"
        by (auto simp add: fmlookup_dom_iff)
      with a ng show False by auto
    qed
    thus "fmlookup (IS_Globals ?st) n = None"
      using fmdom_notD by (simp add: st_sel)
  qed

  \<comment> \<open>Conjunct: declared non-ghost functions exist with matching InterpFuns.\<close>
  have fe: "funs_exist_in_state ?st env"
    unfolding funs_exist_in_state_def
  proof (intro allI impI)
    fix name info
    assume a: "fmlookup (TE_Functions env) name = Some info \<and> FI_Ghost info = NotGhost"
    hence decl: "fmlookup (TE_Functions env) name = Some info"
      and ng: "FI_Ghost info = NotGhost" by auto
    have "name |\<in>| fmdom funDefs" using fmdomI[OF decl] fdom by simp
    then obtain f where f_lk: "fmlookup funDefs name = Some f"
      by (auto simp add: fmlookup_dom_iff)
    have mem: "(name, f) \<in> set (sorted_list_of_fmap funDefs)"
      using f_lk by (simp add: sorted_list_of_fmap_mem_iff)
    obtain body where
      funs_lk: "fmlookup funs name = Some (make_interp_fun info f body)" and
      body_ok: "(case CF_Body f of
                   Some stmts \<Rightarrow> body = Inl stmts
                 | None \<Rightarrow> (\<exists>externFun. fmlookup externs name = Some externFun
                                       \<and> body = Inr externFun))"
      using build_interp_funs_lookup_some[OF funs_ok mem
              distinct_map_fst_sorted_list_of_fmap decl ng]
      by auto

    \<comment> \<open>Definition-vs-declaration consistency from the module typecheck.\<close>
    obtain info' where
      decl2: "fmlookup (TE_Functions env) name = Some info'" and
      len0: "length (CF_Args f) = length (FI_TmArgs info')" and
      distArgs: "distinct (CF_Args f)" and
      body_wt: "(case CF_Body f of
                   None \<Rightarrow> True
                 | Some stmts \<Rightarrow>
                     core_statement_list_type
                       (module_body_env_for env (CF_Args f) info')
                       (FI_Ghost info') stmts \<noteq> None)"
      using fwt f_lk unfolding module_functions_well_typed_def by blast
    have info'_eq: "info' = info" using decl decl2 by simp
    have len: "length (CF_Args f) = length (FI_TmArgs info)"
      using len0 info'_eq by simp

    \<comment> \<open>The five conjuncts of fun_info_matches_interp_fun.\<close>
    have if_sel:
      "IF_TyArgs (make_interp_fun info f body) = FI_TyArgs info"
      "IF_Args (make_interp_fun info f body) = zip (CF_Args f) (map snd (FI_TmArgs info))"
      "IF_Body (make_interp_fun info f body) = body"
      "IF_Impure (make_interp_fun info f body) = FI_Impure info"
      by (simp_all add: make_interp_fun_def)
    have mapfst: "map fst (zip (CF_Args f) (map snd (FI_TmArgs info))) = CF_Args f"
      by (simp add: len)
    have markers: "list_all2 (\<lambda>(_, vor1) (_, vor2). vor1 = vor2)
                     (FI_TmArgs info) (zip (CF_Args f) (map snd (FI_TmArgs info)))"
      by (auto simp add: list_all2_conv_all_nth len split_def)
    have distZip: "distinct (map fst (zip (CF_Args f) (map snd (FI_TmArgs info))))"
      unfolding mapfst by (rule distArgs)
    have body_match: "case body of
           Inl bodyStmts \<Rightarrow>
             core_statement_list_type
               (body_env_for env
                  (map fst (zip (CF_Args f) (map snd (FI_TmArgs info)))) info)
               NotGhost bodyStmts \<noteq> None
         | Inr externFun \<Rightarrow> extern_fun_contract env info externFun"
      unfolding mapfst
    proof (cases "CF_Body f")
      case (Some stmts)
      with body_ok have body_eq: "body = Inl stmts" by simp
      from body_wt Some info'_eq ng
      have "core_statement_list_type
              (module_body_env_for env (CF_Args f) info) NotGhost stmts \<noteq> None"
        by simp
      thus "case body of
              Inl bodyStmts \<Rightarrow>
                core_statement_list_type
                  (body_env_for env (CF_Args f) info) NotGhost bodyStmts \<noteq> None
            | Inr externFun \<Rightarrow> extern_fun_contract env info externFun"
        unfolding body_eq
        by (simp add: module_body_env_for_eq_body_env_for[OF abs ng])
    next
      case None
      with body_ok obtain externFun where
        ext_lk: "fmlookup externs name = Some externFun" and
        body_eq: "body = Inr externFun"
        by auto
      show "case body of
              Inl bodyStmts \<Rightarrow>
                core_statement_list_type
                  (body_env_for env (CF_Args f) info) NotGhost bodyStmts \<noteq> None
            | Inr externFun \<Rightarrow> extern_fun_contract env info externFun"
        unfolding body_eq
        using externs_ok[OF decl ext_lk] by simp
    qed
    have match: "fun_info_matches_interp_fun env info (make_interp_fun info f body)"
      unfolding fun_info_matches_interp_fun_def if_sel
      using markers distZip body_match by simp

    show "case fmlookup (IS_Functions ?st) name of
            Some interpFun \<Rightarrow> fun_info_matches_interp_fun env info interpFun
          | None \<Rightarrow> False"
      by (simp add: st_sel funs_lk match)
  qed

  \<comment> \<open>Conjunct: no functions beyond the declared non-ghost ones.\<close>
  have nef: "no_extra_funs ?st env"
    unfolding no_extra_funs_def
  proof (intro allI impI)
    fix n
    assume a: "case fmlookup (TE_Functions env) n of
                 None \<Rightarrow> True | Some info \<Rightarrow> FI_Ghost info = Ghost"
    have "fmlookup funs n = None"
    proof (rule build_interp_funs_lookup_none[OF funs_ok])
      fix f assume "(n, f) \<in> set (sorted_list_of_fmap funDefs)"
      hence "fmlookup funDefs n = Some f" by (simp add: sorted_list_of_fmap_mem_iff)
      hence "n |\<in>| fmdom (TE_Functions env)" using fmdomI fdom by fastforce
      then obtain info where info_lk: "fmlookup (TE_Functions env) n = Some info"
        by (auto simp add: fmlookup_dom_iff)
      with a have "FI_Ghost info = Ghost" by simp
      with info_lk
      show "\<exists>info. fmlookup (TE_Functions env) n = Some info \<and> FI_Ghost info = Ghost"
        by auto
    qed
    thus "fmlookup (IS_Functions ?st) n = None" by (simp add: st_sel)
  qed

  have ranEmpty: "fmran' (fmempty :: (string, CoreType) fmap) = {}"
    by (auto simp: fmlookup_ran'_iff)
  have srtEmpty: "subst_range_tyvars fmempty = {}"
    by (simp add: subst_range_tyvars_def ranEmpty)

  show ?thesis
    unfolding state_matches_env_def
  proof (intro conjI)
    show "local_vars_exist_in_state ?st env []"
      unfolding local_vars_exist_in_state_def by (simp add: locals)
    show "global_vars_exist_in_state ?st env" by (rule gv)
    show "no_extra_local_vars ?st env"
      unfolding no_extra_local_vars_def by (simp add: st_sel)
    show "no_extra_global_vars ?st env" by (rule neg)
    show "funs_exist_in_state ?st env" by (rule fe)
    show "no_extra_funs ?st env" by (rule nef)
    show "const_locals_match ?st env"
      unfolding const_locals_match_def
      by (simp add: st_sel constlocals ghostlocals)
    show "store_well_typed ?st env []"
      unfolding store_well_typed_def by (simp add: st_sel)
    show "ty_args_well_formed ?st env"
      unfolding ty_args_well_formed_def
      by (simp add: st_sel rtv ranEmpty srtEmpty)
    show "default_ctors_match ?st env"
    proof -
      have "IS_DefaultCtors ?st = default_ctors_map env" by (rule st_sel(7))
      moreover have "TE_DataCtorsByType env = TE_DataCtorsByType env" by (rule refl)
      moreover have "TE_DataCtors env = TE_DataCtors env" by (rule refl)
      ultimately show ?thesis by (rule default_ctors_map_match)
    qed
    show "TE_AbstractTypes env = {||}" by (rule abs)
  qed
qed


(* ========================================================================== *)
(* Main theorem                                                               *)
(* ========================================================================== *)

(* Building an InterpState from a closed, well-typed CoreModule (with
   contract-satisfying extern functions) yields a state that matches the
   normalized module's type environment, with an empty store typing. *)
theorem make_interp_state_matches_env:
  assumes wt: "core_module_well_typed m"
      and closed: "core_module_closed m"
      and externs_ok: "\<And>name info externFun.
            \<lbrakk> fmlookup (TE_Functions (CM_TyEnv (normalize_module m))) name = Some info;
              fmlookup externs name = Some externFun \<rbrakk> \<Longrightarrow>
            extern_fun_contract (CM_TyEnv (normalize_module m)) info externFun"
      and ok: "make_interp_state fuel world externs m = Inr state"
  shows "state_matches_env state (CM_TyEnv (normalize_module m)) []"
proof -
  define m' where "m' = normalize_module m"
  define env where "env = CM_TyEnv m'"
  define baseState where "baseState = base_interp_state env world"
  define ngPairs where
    "ngPairs = filter (\<lambda>(name, _). name |\<notin>| TE_GhostGlobals env)
                 (sorted_list_of_fmap (CM_GlobalVars m'))"
  define funPairs where "funPairs = sorted_list_of_fmap (CM_Functions m')"

  \<comment> \<open>Facts about the normalized module.\<close>
  have nwt: "normalized_module_well_typed m'"
    using wt unfolding core_module_well_typed_def m'_def by blast
  have wf: "tyenv_well_formed env"
    and scope: "tyenv_module_scope env"
    and gwt: "module_globals_well_typed env (CM_GlobalVars m')"
    and fwt: "module_functions_well_typed env (CM_Functions m')"
    using nwt unfolding normalized_module_well_typed_def env_def by blast+
  have closed': "core_module_closed m'"
    using closed unfolding m'_def by simp
  have gdom: "fmdom (TE_GlobalVars env) = fmdom (CM_GlobalVars m')"
    and fdom: "fmdom (TE_Functions env) = fmdom (CM_Functions m')"
    and tv: "TE_TypeVars env = {||}"
    using closed' unfolding core_module_closed_def env_def by blast+
  have rtv: "TE_RuntimeTypeVars env = {||}"
  proof -
    have "TE_RuntimeTypeVars env |\<subseteq>| TE_TypeVars env"
      using wf
      unfolding tyenv_well_formed_def tyenv_runtime_tyvars_subset_def by blast
    thus ?thesis using tv by simp
  qed
  have externs_ok': "\<And>name info externFun.
        \<lbrakk> fmlookup (TE_Functions env) name = Some info;
          fmlookup externs name = Some externFun \<rbrakk> \<Longrightarrow>
        extern_fun_contract env info externFun"
    using externs_ok unfolding env_def m'_def by blast

  \<comment> \<open>Decompose the construction.\<close>
  from ok obtain funs defaults sortedGlobals where
    funs_ok: "build_interp_funs externs env funPairs = Inr funs" and
    defaults_ok: "compute_global_defaults fuel baseState env ngPairs = Inr defaults" and
    sorted_ok: "sort_globals ngPairs = Inr sortedGlobals" and
    eval_ok: "eval_globals fuel
                (baseState \<lparr> IS_Globals := defaults, IS_Functions := funs \<rparr>)
                sortedGlobals = Inr state"
    unfolding make_interp_state_def Let_def
              m'_def[symmetric] env_def[symmetric] baseState_def[symmetric]
              ngPairs_def[symmetric] funPairs_def[symmetric]
    by (auto split: sum.splits)

  \<comment> \<open>The state before initializer evaluation matches env.\<close>
  have mid_sm: "state_matches_env
                  (baseState \<lparr> IS_Globals := defaults, IS_Functions := funs \<rparr>) env []"
    unfolding baseState_def
    by (rule assembled_state_matches[OF wf scope tv rtv gdom fdom fwt
          defaults_ok[unfolded baseState_def ngPairs_def]
          funs_ok[unfolded funPairs_def]
          externs_ok'])

  \<comment> \<open>Every evaluated pair is a declared non-ghost global's initializer.\<close>
  have pairs_ok: "\<forall>p \<in> set sortedGlobals.
        fmlookup (CM_GlobalVars m') (fst p) = Some (snd p)
        \<and> fst p |\<notin>| TE_GhostGlobals env"
  proof
    fix p assume "p \<in> set sortedGlobals"
    hence "p \<in> set ngPairs"
      using mset_eq_setD[OF sort_globals_mset[OF sorted_ok]] by simp
    then obtain n tm where p_eq: "p = (n, tm)" and
      mem: "(n, tm) \<in> set (sorted_list_of_fmap (CM_GlobalVars m'))" and
      ng: "n |\<notin>| TE_GhostGlobals env"
      unfolding ngPairs_def by auto
    have "fmlookup (CM_GlobalVars m') n = Some tm"
      using mem by (simp add: sorted_list_of_fmap_mem_iff)
    thus "fmlookup (CM_GlobalVars m') (fst p) = Some (snd p)
          \<and> fst p |\<notin>| TE_GhostGlobals env"
      using p_eq ng by simp
  qed

  show ?thesis
    unfolding m'_def[symmetric] env_def[symmetric]
    by (rule eval_globals_preserves_match[OF wf rtv gwt pairs_ok mid_sm eval_ok])
qed

end
