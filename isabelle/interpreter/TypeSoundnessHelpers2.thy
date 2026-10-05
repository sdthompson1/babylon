theory TypeSoundnessHelpers2
  imports TypeSoundnessHelpers1
begin


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
    "CoreTyEnv \<Rightarrow> string list \<Rightarrow> FunInfo \<Rightarrow> nat \<Rightarrow> CoreTyEnv" where
  "partial_body_env_for env names funInfo k =
    (body_env_for env names funInfo) \<lparr>
      TE_LocalVars := fmap_of_list
        (take k (zip names (map fst (FI_TmArgs funInfo)))),
      TE_ConstLocals := fset_of_list
        (map fst
             (filter (\<lambda>(_, vor, _). vor = Var)
                     (take k (zip names (map snd (FI_TmArgs funInfo))))))
    \<rparr>"

(* When k = 0, the partial env has no locals and no const names: a body env
   whose locals/refs have been cleared. *)
lemma partial_body_env_for_zero:
  "TE_LocalVars (partial_body_env_for env names funInfo 0) = fmempty"
  "TE_ConstLocals (partial_body_env_for env names funInfo 0) = {||}"
  by (simp_all add: partial_body_env_for_def)

(* When k = length (FI_TmArgs funInfo), the partial env equals body_env_for
   env names funInfo. This is the bridge from the induction's end state to the
   bodyEnv used in case 6. Needs names to be at least as long as FI_TmArgs (in
   practice they are equal), so that the zip captures every parameter. *)
lemma partial_body_env_for_full:
  assumes "length (FI_TmArgs funInfo) \<le> length names"
  shows "partial_body_env_for env names funInfo (length (FI_TmArgs funInfo))
   = body_env_for env names funInfo"
  using assms by (simp add: partial_body_env_for_def body_env_for_def)

(* The types in a function's signature mention only the function's own type
   variables (given that there are no abstract types). *)
lemma fun_info_types_tyvars_subset:
  assumes wf: "tyenv_well_formed env"
      and abs_empty: "TE_AbstractTypes env = {||}"
      and fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo"
  shows "\<forall>ty \<in> fst ` set (FI_TmArgs funInfo). type_tyvars ty \<subseteq> set (FI_TyArgs funInfo)"
    and "type_tyvars (FI_ReturnType funInfo) \<subseteq> set (FI_TyArgs funInfo)"
proof -
  from wf have fwk: "tyenv_fun_types_well_kinded env"
    unfolding tyenv_well_formed_def by simp
  from fwk fn_lookup have both:
    "(\<forall>ty \<in> fst ` set (FI_TmArgs funInfo).
        is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list (FI_TyArgs funInfo) \<rparr>) ty) \<and>
     is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list (FI_TyArgs funInfo) \<rparr>)
                    (FI_ReturnType funInfo)"
    unfolding tyenv_fun_types_well_kinded_def by blast
  show "\<forall>ty \<in> fst ` set (FI_TmArgs funInfo). type_tyvars ty \<subseteq> set (FI_TyArgs funInfo)"
  proof
    fix ty assume "ty \<in> fst ` set (FI_TmArgs funInfo)"
    with both have
      "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list (FI_TyArgs funInfo) \<rparr>) ty"
      by blast
    from is_well_kinded_type_tyvars_subset[OF this]
    show "type_tyvars ty \<subseteq> set (FI_TyArgs funInfo)"
      by (simp add: abs_empty fset_of_list.rep_eq)
  qed
  from both have
    "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list (FI_TyArgs funInfo) \<rparr>)
                    (FI_ReturnType funInfo)"
    by blast
  from is_well_kinded_type_tyvars_subset[OF this]
  show "type_tyvars (FI_ReturnType funInfo) \<subseteq> set (FI_TyArgs funInfo)"
    by (simp add: abs_empty fset_of_list.rep_eq)
qed

(* Shape of the sound arg-processing result: the fold either errors soundly
   or produces a state matching body_env_for env funInfo (the callee's static
   env), with IS_TyArgs set to the call-site type substitution. *)
definition sound_arg_processing_result ::
    "CoreTyEnv \<Rightarrow> string list \<Rightarrow> FunInfo \<Rightarrow> (string, CoreType) fmap \<Rightarrow> CoreType list
    \<Rightarrow> InterpError + 'w InterpState \<Rightarrow> bool" where
  "sound_arg_processing_result env names funInfo tySubst storeTyping result =
    (case result of
      Inl err \<Rightarrow> sound_error_result err
    | Inr preCallState \<Rightarrow>
        IS_TyArgs preCallState = tySubst
        \<and> (\<exists>bodyStoreTyping.
              state_matches_env preCallState (body_env_for env names funInfo) bodyStoreTyping
            \<and> storeTyping_extends storeTyping bodyStoreTyping))"

(* Partial variant: after k steps, the state matches partial_body_env_for at k
   with some store typing extending the original, and IS_TyArgs is the
   call-site type substitution (preserved by process_one_arg). *)
definition sound_partial_arg_processing_result ::
    "CoreTyEnv \<Rightarrow> string list \<Rightarrow> FunInfo \<Rightarrow> (string, CoreType) fmap \<Rightarrow> nat \<Rightarrow> CoreType list
    \<Rightarrow> InterpError + 'w InterpState \<Rightarrow> bool" where
  "sound_partial_arg_processing_result env names funInfo tySubst k storeTyping result =
    (case result of
      Inl err \<Rightarrow> sound_error_result err
    | Inr state \<Rightarrow>
        IS_TyArgs state = tySubst
        \<and> (\<exists>partialStoreTyping.
              state_matches_env state (partial_body_env_for env names funInfo k)
                partialStoreTyping
            \<and> storeTyping_extends storeTyping partialStoreTyping))"

(* -------------------------------------------------------------------------- *)
(* H2a. The cleared state matches the k=0 partial body env under the caller's *)
(* store typing (no new slots needed).                                        *)
(* -------------------------------------------------------------------------- *)
(* The cleared state's IS_TyArgs is set to the call-site tySubst, and the partial
   body env at k=0 has TE_TypeVars = fset_of_list (FI_TyArgs funInfo). Discharging
   ty_args_well_formed therefore requires the call-site assumptions that
   tyArgs are well-kinded in env and that tySubst is built as
   fmap_of_list (zip (FI_TyArgs funInfo) (map (apply_subst (IS_TyArgs state)) tyArgs)). *)
lemma cleared_state_matches_partial_env_zero:
  assumes sme: "state_matches_env state env storeTyping"
      and ty_len: "length tyArgs = length (FI_TyArgs funInfo)"
      and ty_wk:  "list_all (is_well_kinded env) tyArgs"
      and tySubst_eq:
            "tySubst = fmap_of_list
                         (zip (FI_TyArgs funInfo)
                              (map (apply_subst (IS_TyArgs state)) tyArgs))"
  shows "state_matches_env
           (state \<lparr> IS_Locals := fmempty,
                    IS_Refs := fmempty,
                    IS_ConstLocals := {||},
                    IS_TyArgs := tySubst \<rparr>)
           (partial_body_env_for env names funInfo 0)
           storeTyping"
proof -
  let ?clearedState = "state \<lparr> IS_Locals := fmempty,
                                IS_Refs := fmempty,
                                IS_ConstLocals := {||},
                                IS_TyArgs := tySubst \<rparr>"
  let ?pEnv = "partial_body_env_for env names funInfo 0"

  \<comment> \<open>Field equations for ?pEnv at k=0. \<close>
  have pEnv_locals: "TE_LocalVars ?pEnv = fmempty"
    by (simp add: partial_body_env_for_def)
  have pEnv_const: "TE_ConstLocals ?pEnv = {||}"
    by (simp add: partial_body_env_for_def)
  have pEnv_globals: "TE_GlobalVars ?pEnv = TE_GlobalVars env"
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

  \<comment> \<open>The matched env has no unresolved abstract types (interpreter runs only on
      fully-resolved programs). \<close>
  have abs_empty: "TE_AbstractTypes env = {||}"
    using sme unfolding state_matches_env_def by blast
  have abs_pEnv: "TE_AbstractTypes ?pEnv = {||}"
    using abs_empty by (simp add: partial_body_env_for_def body_env_for_def)

  \<comment> \<open>Extract conjuncts from the source state_matches_env. \<close>
  from sme have
    lv_src: "local_vars_exist_in_state state env storeTyping" and
    gv_src: "global_vars_exist_in_state state env" and
    no_lv_src: "no_extra_local_vars state env" and
    no_gv_src: "no_extra_global_vars state env" and
    fes_src: "funs_exist_in_state state env" and
    no_fun_src: "no_extra_funs state env" and
    cn_src: "const_locals_match state env" and
    swt_src: "store_well_typed state env storeTyping" and
    ta_src: "ty_args_well_formed state env"
    unfolding state_matches_env_def
    by blast+

  \<comment> \<open>value_has_type mentions only ground types, so it is the same in env and in
      ?pEnv, although the two have different type variables. \<close>
  have vht_eq: "value_has_type ?pEnv = value_has_type env"
    by (rule ext)+ (rule value_has_type_ground_cong_env[OF pEnv_dactors pEnv_datatypes])

  \<comment> \<open>Discharge each conjunct of state_matches_env for the cleared state and ?pEnv. \<close>

  have lv_tgt: "local_vars_exist_in_state ?clearedState ?pEnv storeTyping"
    unfolding local_vars_exist_in_state_def pEnv_locals by simp

  have gv_tgt: "global_vars_exist_in_state ?clearedState ?pEnv"
    unfolding global_vars_exist_in_state_def
  proof (intro allI impI)
    fix name ty
    assume lk_pEnv: "fmlookup (TE_GlobalVars ?pEnv) name = Some ty"
    from lk_pEnv have lk_env: "fmlookup (TE_GlobalVars env) name = Some ty"
      by (simp add: pEnv_globals)
    from gv_src lk_env have gvst:
      "global_var_in_state_with_type state env name ty"
      unfolding global_vars_exist_in_state_def by blast
    from gvst obtain val where
      lkup_g: "fmlookup (IS_Globals state) name = Some val" and
      vht_env: "value_has_type env val ty"
      unfolding global_var_in_state_with_type_def
      by (cases "fmlookup (IS_Globals state) name") auto
    from vht_env have vht_pEnv: "value_has_type ?pEnv val ty"
      by (simp add: vht_eq)
    show "global_var_in_state_with_type ?clearedState ?pEnv name ty"
      unfolding global_var_in_state_with_type_def using lkup_g vht_pEnv by simp
  qed

  have no_lv_tgt: "no_extra_local_vars ?clearedState ?pEnv"
    unfolding no_extra_local_vars_def by simp

  have no_gv_tgt: "no_extra_global_vars ?clearedState ?pEnv"
    using no_gv_src pEnv_globals
    unfolding no_extra_global_vars_def
    by simp

  \<comment> \<open>funs_exist_in_state: TE_Functions is inherited from env, and
      fun_info_matches_interp_fun reads only the global fields, on which env and
      ?pEnv agree. \<close>
  have fes_tgt: "funs_exist_in_state ?clearedState ?pEnv"
    unfolding funs_exist_in_state_def
  proof (intro allI impI)
    fix name info'
    assume A: "fmlookup (TE_Functions ?pEnv) name = Some info'"
    from A have lookup: "fmlookup (TE_Functions env) name = Some info'"
      by (simp add: pEnv_funs)
    from fes_src lookup have outer:
      "case fmlookup (IS_Functions state) name of None \<Rightarrow> False
       | Some interpFun \<Rightarrow> fun_info_matches_interp_fun env info' interpFun"
      unfolding funs_exist_in_state_def by blast
    have fi_eq: "\<And>ifn. fun_info_matches_interp_fun ?pEnv info' ifn
                        = fun_info_matches_interp_fun env info' ifn"
      by (rule fun_info_matches_interp_fun_ground_cong_env
                 [OF pEnv_globals pEnv_funs pEnv_datatypes pEnv_dactors
                     pEnv_dactors_by_ty pEnv_ghost_dt])
         (simp add: abs_empty abs_pEnv)
    show "case fmlookup (IS_Functions ?clearedState) name of None \<Rightarrow> False
          | Some interpFun \<Rightarrow> fun_info_matches_interp_fun ?pEnv info' interpFun"
      using outer fi_eq by (auto split: option.splits)
  qed

  have no_fun_tgt: "no_extra_funs ?clearedState ?pEnv"
    using no_fun_src pEnv_funs
    unfolding no_extra_funs_def
    by simp

  have cn_tgt: "const_locals_match ?clearedState ?pEnv"
    unfolding const_locals_match_def pEnv_const by simp

  \<comment> \<open>store_well_typed: the store is unchanged. \<close>
  have swt_tgt: "store_well_typed ?clearedState ?pEnv storeTyping"
    using swt_src
    unfolding store_well_typed_def by (simp add: vht_eq)

  \<comment> \<open>ty_args_well_formed: the domain of tySubst is FI_TyArgs (= TE_TypeVars ?pEnv).
      Each entry of its range is apply_subst (IS_TyArgs state) of a type argument
      that is well-kinded in env, so it is ground and well-kinded in env; being
      ground, it is well-kinded in ?pEnv too. \<close>
  have fmdom_tySubst: "fmdom tySubst = fset_of_list (FI_TyArgs funInfo)"
  proof -
    have len_map: "length (FI_TyArgs funInfo)
                   = length (map (apply_subst (IS_TyArgs state)) tyArgs)"
      using ty_len by simp
    show ?thesis
      using tySubst_eq
      by (simp add: len_map fset_of_list.rep_eq)
  qed
  have dom_tgt: "fmdom (IS_TyArgs ?clearedState) = TE_TypeVars ?pEnv"
    using fmdom_tySubst pEnv_tyvars by simp

  have range_tgt:
    "\<forall>ty \<in> fmran' tySubst. type_tyvars ty = {} \<and> is_well_kinded ?pEnv ty"
  proof
    fix ty assume "ty \<in> fmran' tySubst"
    then obtain n where lk: "fmlookup tySubst n = Some ty"
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
    from ty_wk i_ty have wk_i: "is_well_kinded env (tyArgs ! i)"
      by (simp add: list_all_length)
    have ground: "type_tyvars ty = {}"
      using is_well_kinded_apply_IS_TyArgs_ground[OF sme wk_i] ty_eq by simp
    have "is_well_kinded env ty"
      using is_well_kinded_apply_IS_TyArgs[OF sme wk_i] ty_eq by simp
    hence "is_well_kinded ?pEnv ty"
      using is_well_kinded_ground_cong_env[OF ground pEnv_datatypes] by simp
    with ground show "type_tyvars ty = {} \<and> is_well_kinded ?pEnv ty" by simp
  qed

  have range_ground_tgt: "subst_range_tyvars (IS_TyArgs ?clearedState) = {}"
    unfolding subst_range_tyvars_def
    using range_tgt by auto

  have range_wk_tgt:
    "\<forall>ty \<in> fmran' (IS_TyArgs ?clearedState). is_well_kinded ?pEnv ty"
    using range_tgt by auto

  have ta_tgt: "ty_args_well_formed ?clearedState ?pEnv"
    unfolding ty_args_well_formed_def
    using dom_tgt range_ground_tgt range_wk_tgt by blast

  have dc_tgt: "default_ctors_match ?clearedState ?pEnv"
    using sme
    unfolding state_matches_env_def default_ctors_match_def
              partial_body_env_for_def body_env_for_def
    by simp

  have tm_tgt: "tables_match ?clearedState ?pEnv"
    using sme
    unfolding state_matches_env_def tables_match_def
              partial_body_env_for_def body_env_for_def
    by simp

  have abs_tgt: "TE_AbstractTypes ?pEnv = {||}"
    using abs_empty by (simp add: partial_body_env_for_def body_env_for_def)

  show ?thesis
    unfolding state_matches_env_def
    using lv_tgt gv_tgt no_lv_tgt no_gv_tgt fes_tgt no_fun_tgt cn_tgt swt_tgt ta_tgt dc_tgt
          tm_tgt abs_tgt
    by blast
qed

(* -------------------------------------------------------------------------- *)
(* H2b. One step of process_one_arg extends the partial body env by one local. *)
(*                                                                             *)
(* The interpretation results (lvalue + value) for argument k must be sound    *)
(* w.r.t. the k-th parameter's expected type in the *caller's* env:            *)
(*                                                                             *)
(*   valResult  = interp_term d fuel state argTms[k]                          *)
(*   lvalResult = interp_writable_lvalue d fuel state argTms[k]               *)
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
  "TE_GlobalVars (partial_body_env_for env names funInfo k) = TE_GlobalVars env"
  "TE_GhostLocals (partial_body_env_for env names funInfo k)
     = (if FI_Ghost funInfo = Ghost then fset_of_list names else {||})"
  "TE_Functions (partial_body_env_for env names funInfo k) = TE_Functions env"
  "TE_Datatypes (partial_body_env_for env names funInfo k) = TE_Datatypes env"
  "TE_DataCtors (partial_body_env_for env names funInfo k) = TE_DataCtors env"
  "TE_DataCtorsByType (partial_body_env_for env names funInfo k) = TE_DataCtorsByType env"
  "TE_GhostDatatypes (partial_body_env_for env names funInfo k) = TE_GhostDatatypes env"
  "TE_TypeVars (partial_body_env_for env names funInfo k) = fset_of_list (FI_TyArgs funInfo)"
  "TE_RuntimeTypeVars (partial_body_env_for env names funInfo k)
     = (if FI_Ghost funInfo = NotGhost then fset_of_list (FI_TyArgs funInfo) else {||})"
  "TE_ReturnType (partial_body_env_for env names funInfo k) = FI_ReturnType funInfo"
  "TE_FunctionGhost (partial_body_env_for env names funInfo k) = FI_Ghost funInfo"
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
      and k_names: "k < length names"
      and kth: "FI_TmArgs funInfo ! k = (paramTy, vor, gh)"
      and paramName: "names ! k = paramName"
      and distinct: "distinct names"
  shows
    "partial_body_env_for env names funInfo (Suc k)
     = (partial_body_env_for env names funInfo k) \<lparr>
         TE_LocalVars := fmupd paramName paramTy
           (TE_LocalVars (partial_body_env_for env names funInfo k)),
         TE_ConstLocals :=
           (if vor = Var
            then finsert paramName
                   (TE_ConstLocals (partial_body_env_for env names funInfo k))
            else fminus
                   (TE_ConstLocals (partial_body_env_for env names funInfo k))
                   {|paramName|})
       \<rparr>"
proof -
  \<comment> \<open>The locals list: names zipped with the parameter types. The k-th entry is
      (paramName, paramTy); the (Suc k)-prefix appends it to the k-prefix. \<close>
  let ?lvz = "zip names (map fst (FI_TmArgs funInfo))"
  let ?clz = "zip names (map snd (FI_TmArgs funInfo))"
  have len_lvz: "k < length ?lvz" using k_bound k_names by simp
  have len_clz: "k < length ?clz" using k_bound k_names by simp
  have lvz_k: "?lvz ! k = (paramName, paramTy)"
    using len_lvz kth paramName k_bound by simp
  have clz_k: "?clz ! k = (paramName, vor, gh)"
    using len_clz kth paramName k_bound by simp

  \<comment> \<open>map fst of the locals zip is a prefix of names, hence distinct. \<close>
  have dist_lvz: "distinct (map fst ?lvz)"
    using distinct by (simp add: map_fst_zip_take)

  \<comment> \<open>Standard: take (Suc k) xs = take k xs @ [xs ! k]. \<close>
  have take_Suc_lvz: "take (Suc k) ?lvz = take k ?lvz @ [(paramName, paramTy)]"
    using len_lvz lvz_k by (simp add: take_Suc_conv_app_nth)
  have take_Suc_clz: "take (Suc k) ?clz = take k ?clz @ [(paramName, vor, gh)]"
    using len_clz clz_k by (simp add: take_Suc_conv_app_nth)

  \<comment> \<open>Locals: fmap_of_list of the (Suc k)-prefix equals fmupd of the k-th entry
      onto the k-prefix's fmap. \<close>
  have paramName_fresh: "paramName \<notin> set (map fst (take k ?lvz))"
  proof -
    have "distinct (map fst (take (Suc k) ?lvz))"
      using dist_lvz by (simp add: take_map[symmetric])
    moreover have "map fst (take (Suc k) ?lvz) = map fst (take k ?lvz) @ [paramName]"
      using take_Suc_lvz by simp
    ultimately show ?thesis by simp
  qed

  have fmap_pairs_step:
    "fmap_of_list (take (Suc k) ?lvz)
       = fmupd paramName paramTy (fmap_of_list (take k ?lvz))"
  proof (rule fmap_ext)
    fix name
    show "fmlookup (fmap_of_list (take (Suc k) ?lvz)) name
        = fmlookup (fmupd paramName paramTy (fmap_of_list (take k ?lvz))) name"
    proof (cases "name = paramName")
      case True
      have map_of_k_none: "map_of (take k ?lvz) paramName = None"
        using paramName_fresh by (simp add: map_of_eq_None_iff)
      have "fmlookup (fmap_of_list (take (Suc k) ?lvz)) paramName
              = map_of (take (Suc k) ?lvz) paramName"
        by (simp add: fmap_of_list.rep_eq)
      also have "\<dots> = map_of (take k ?lvz @ [(paramName, paramTy)]) paramName"
        using take_Suc_lvz by simp
      also have "\<dots> = Some paramTy"
        using map_of_k_none by (simp add: map_add_Some_iff)
      finally have lhs: "fmlookup (fmap_of_list (take (Suc k) ?lvz)) paramName
                           = Some paramTy" .
      from True show ?thesis by (simp add: lhs)
    next
      case False
      have "fmlookup (fmap_of_list (take (Suc k) ?lvz)) name
              = map_of (take (Suc k) ?lvz) name"
        by (simp add: fmap_of_list.rep_eq)
      also have "\<dots> = map_of (take k ?lvz) name"
        using take_Suc_lvz False
        by (simp add: map_add_def split: option.split)
      also have "\<dots> = fmlookup (fmap_of_list (take k ?lvz)) name"
        by (simp add: fmap_of_list.rep_eq)
      finally show ?thesis using False by simp
    qed
  qed

  \<comment> \<open>Const names: the filter of the (Suc k)-prefix for Var parameters extends
      the k-prefix filter by either [paramName] (if vor = Var) or []. \<close>
  let ?const_k = "map fst (filter (\<lambda>(_, vor', _). vor' = Var) (take k ?clz))"
  let ?const_Sk = "map fst (filter (\<lambda>(_, vor', _). vor' = Var) (take (Suc k) ?clz))"
  have filter_Sk:
    "filter (\<lambda>(_, vor', _). vor' = Var) (take (Suc k) ?clz)
       = filter (\<lambda>(_, vor', _). vor' = Var) (take k ?clz)
         @ (if vor = Var then [(paramName, vor, gh)] else [])"
    using take_Suc_clz by simp
  have const_Sk_eq:
    "?const_Sk = (if vor = Var then ?const_k @ [paramName] else ?const_k)"
    using filter_Sk by (cases "vor = Var") simp_all
  \<comment> \<open>paramName is not in the k-prefix of names, hence not in ?const_k either. \<close>
  have keys_clz: "map fst (take k ?clz) = take k names"
  proof -
    have "map fst (take k ?clz) = take k (map fst ?clz)" by (simp add: take_map)
    also have "map fst ?clz = take (min (length names) (length (FI_TmArgs funInfo))) names"
      by (simp add: map_fst_zip_take)
    also have "take k \<dots> = take k names"
      using k_names k_bound by simp
    finally show ?thesis .
  qed
  have paramName_not_in_take_k: "paramName \<notin> set (take k names)"
  proof -
    have "distinct (take (Suc k) names)" using distinct by (rule distinct_take)
    moreover have "take (Suc k) names = take k names @ [paramName]"
      using k_names paramName by (simp add: take_Suc_conv_app_nth)
    ultimately show ?thesis by simp
  qed
  have paramName_not_in_const_k: "paramName \<notin> set ?const_k"
  proof -
    have "set ?const_k \<subseteq> fst ` set (take k ?clz)"
      by (auto dest: filter_is_subset[THEN subsetD])
    also have "\<dots> = set (map fst (take k ?clz))" by simp
    also have "\<dots> = set (take k names)" using keys_clz by simp
    finally show ?thesis using paramName_not_in_take_k by blast
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

  show ?thesis
    using fmap_pairs_step fset_const_Sk
    by (simp add: partial_body_env_for_def body_env_for_def)
qed

lemma process_one_arg_step_sound:
  fixes env :: CoreTyEnv
    and funInfo :: FunInfo
    and tySubst :: "(string, CoreType) fmap"
    and storeTyping :: "CoreType list"
    and k :: nat
  assumes sme_caller: "state_matches_env state env storeTyping"  \<comment> \<open>caller state (for value/lvalue soundness)\<close>
      and wf_env: "tyenv_well_formed env"
      and fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo"
      and k_bound: "k < length (FI_TmArgs funInfo)"
      and k_names: "k < length names"
      and dist_names: "distinct names"
      and kth_arg: "FI_TmArgs funInfo ! k = (paramTy, vor, gh)"
      and paramName_eq: "names ! k = paramName"
      and val_sound: "sound_term_result state env (apply_subst tySubst paramTy) valResult"
      and lval_sound: "vor = Ref \<Longrightarrow>
             sound_lvalue_result state env storeTyping
               (apply_subst tySubst paramTy) lvalResult"
      and partial_sound:
            "sound_partial_arg_processing_result env names funInfo tySubst k storeTyping
               (Inr partialState)"
  shows "sound_partial_arg_processing_result env names funInfo tySubst (Suc k) storeTyping
           (process_one_arg ((paramName, vor, gh), lvalResult, valResult) (Inr partialState))"
proof -
  \<comment> \<open>Extract the partial state invariants from partial_sound. \<close>
  from partial_sound have tyargs_partial: "IS_TyArgs partialState = tySubst"
    unfolding sound_partial_arg_processing_result_def by auto
  from partial_sound obtain partialStoreTyping where
    sme_partial: "state_matches_env partialState
                    (partial_body_env_for env names funInfo k) partialStoreTyping"
    and ext_partial: "storeTyping_extends storeTyping partialStoreTyping"
    unfolding sound_partial_arg_processing_result_def by auto

  let ?pEnv_k = "partial_body_env_for env names funInfo k"
  let ?pEnv_Sk = "partial_body_env_for env names funInfo (Suc k)"

  \<comment> \<open>The caller env has no unresolved abstract types. \<close>
  have abs_empty: "TE_AbstractTypes env = {||}"
    using sme_caller unfolding state_matches_env_def by blast

  \<comment> \<open>partialState has ty_args_well_formed wrt ?pEnv_k. \<close>
  from sme_partial have ta_partial: "ty_args_well_formed partialState ?pEnv_k"
    unfolding state_matches_env_def by blast
  from ta_partial have
    dom_tySubst: "fmdom tySubst = TE_TypeVars ?pEnv_k" and
    range_ground: "subst_range_tyvars tySubst = {}"
    unfolding ty_args_well_formed_def using tyargs_partial by auto

  \<comment> \<open>paramTy is the k-th parameter type. Its type variables are among the
      function's own (FI_TyArgs), which is TE_TypeVars ?pEnv_k = fmdom tySubst. \<close>
  have paramTy_tyvars:
    "type_tyvars paramTy \<subseteq> fset (fset_of_list (FI_TyArgs funInfo))"
  proof -
    have "paramTy \<in> fst ` set (FI_TmArgs funInfo)"
      using kth_arg k_bound image_iff nth_mem by fastforce
    with fun_info_types_tyvars_subset(1)[OF wf_env abs_empty fn_lookup]
    have "type_tyvars paramTy \<subseteq> set (FI_TyArgs funInfo)" by blast
    thus ?thesis by (simp add: fset_of_list.rep_eq)
  qed

  \<comment> \<open>fmdom tySubst = fset_of_list (FI_TyArgs funInfo) (via TE_TypeVars ?pEnv_k
      which equals fset_of_list (FI_TyArgs funInfo) by partial_body_env_for_fields). \<close>
  have tv_pEnv_k: "TE_TypeVars ?pEnv_k = fset_of_list (FI_TyArgs funInfo)"
    by (simp add: partial_body_env_for_def body_env_for_def)
  have fmdom_tySubst: "fmdom tySubst = fset_of_list (FI_TyArgs funInfo)"
    using dom_tySubst tv_pEnv_k by simp
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
        "process_one_arg ((paramName, vor, gh), lvalResult, valResult) (Inr partialState) = Inl err"
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

      \<comment> \<open>Transfer val_typed to ?pEnv_k: value_has_type reads only the datatype
          fields, which ?pEnv_k inherits from env. \<close>
      have val_typed_pEnv:
        "value_has_type ?pEnv_k val (apply_subst tySubst paramTy)"
        using val_typed_env
        by (simp add: value_has_type_ground_cong_env
                        [OF partial_body_env_for_fields(5) partial_body_env_for_fields(4)])

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
        "process_one_arg ((paramName, vor, gh), lvalResult, valResult) (Inr partialState)
           = Inr ?state''"
        using Var Inr alloc_eq
        by (simp add: case_prod_beta)

      have env'_shape:
        "?pEnv_Sk = ?pEnv_k \<lparr>
             TE_LocalVars := fmupd paramName paramTy (TE_LocalVars ?pEnv_k),
             TE_ConstLocals := finsert paramName (TE_ConstLocals ?pEnv_k)
           \<rparr>"
        using partial_body_env_for_step[OF k_bound k_names kth_arg paramName_eq dist_names] Var
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
        "process_one_arg ((paramName, vor, gh), lvalResult, valResult) (Inr partialState) = Inl err"
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
          "process_one_arg ((paramName, vor, gh), lvalResult, valResult) (Inr partialState) = Inl err"
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
          "process_one_arg ((paramName, vor, gh), lvalResult, valResult) (Inr partialState)
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
            using partial_body_env_for_fields(5) by auto
          finally show ?thesis by simp
        qed

        \<comment> \<open>Rewrite path_ty_partial to use IS_TyArgs partialState shape. \<close>
        have path_ty_partial':
          "type_at_path ?pEnv_k (partialStoreTyping ! addr) path
             = Some (apply_subst (IS_TyArgs partialState) paramTy)"
          using path_ty_partial tyargs_partial by simp

        have env'_shape:
          "?pEnv_Sk = ?pEnv_k \<lparr>
               TE_LocalVars := fmupd paramName paramTy (TE_LocalVars ?pEnv_k),
               TE_ConstLocals := fminus (TE_ConstLocals ?pEnv_k) {|paramName|}
             \<rparr>"
          using partial_body_env_for_step[OF k_bound k_names kth_arg paramName_eq dist_names] Ref
          by simp

        have sme_new:
          "state_matches_env ?state' ?pEnv_Sk partialStoreTyping"
          using state_matches_env_add_ref
                  [OF sme_partial addr_valid_partial path_ty_partial' refl env'_shape] .

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
  assumes "process_one_arg ((name, vor, gh), refResult, valResult) (Inr state) = Inr state'"
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
           (fst (snd (ifArgs ! i)) = Ref \<longrightarrow> (\<exists>a p. refResults ! i = Inr (a, p)))"
using assms proof (induction ifArgs arbitrary: refResults valResults initState)
  case Nil
  then show ?case by simp
next
  case (Cons ifa ifrest)
  from Cons.prems(2) obtain rr rrest where rr_eq: "refResults = rr # rrest"
    by (cases refResults) auto
  from Cons.prems(3) obtain vv vrest where vv_eq: "valResults = vv # vrest"
    by (cases valResults) auto
  obtain name vor gh where ifa_eq: "ifa = (name, vor, gh)" by (cases ifa)

  let ?step = "process_one_arg ((name, vor, gh), rr, vv) (Inr initState)"
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
                (fst (snd (ifrest ! i)) = Ref \<longrightarrow> (\<exists>a p. rrest ! i = Inr (a, p)))" .

  show ?case
  proof (intro allI impI)
    fix i assume i_lt: "i < length (ifa # ifrest)"
    show "(\<exists>v. valResults ! i = Inr v) \<and>
          (fst (snd ((ifa # ifrest) ! i)) = Ref \<longrightarrow> (\<exists>a p. refResults ! i = Inr (a, p)))"
    proof (cases i)
      case 0
      from head ifa_eq show ?thesis using 0 rr_eq vv_eq by simp
    next
      case (Suc j)
      from i_lt Suc have j_lt: "j < length ifrest" by simp
      from rest j_lt have
        "(\<exists>v. vrest ! j = Inr v) \<and>
         (fst (snd (ifrest ! j)) = Ref \<longrightarrow> (\<exists>a p. rrest ! j = Inr (a, p)))" by simp
      thus ?thesis using Suc rr_eq vv_eq by simp
    qed
  qed
qed

(* Short-circuit: if the running result is already an error, process_one_arg
   preserves it; soundness is preserved too. *)
lemma process_one_arg_preserve_error:
  assumes "sound_partial_arg_processing_result env names funInfo tySubst k storeTyping (Inl err)"
  shows "sound_partial_arg_processing_result env names funInfo tySubst (Suc k) storeTyping
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
    and tySubst :: "(string, CoreType) fmap"
    and storeTyping :: "CoreType list"
    and state :: "'w InterpState"
  assumes sme_caller: "state_matches_env state env storeTyping"
      and wf_env: "tyenv_well_formed env"
      and fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo"
      and dist_names: "distinct names"
      and names_len: "length names = length (FI_TmArgs funInfo)"
      and suffix_at_k:
            "suffixFnArgs = drop k (FI_TmArgs funInfo)"
      and suffix_names:
            "map fst suffixIfArgs = drop k names"
      and var_ref_match:
            "list_all2 (\<lambda>(_, vor1, gh1) (_, vor2, gh2). vor1 = vor2 \<and> gh1 = gh2)
                       suffixFnArgs suffixIfArgs"
      and len_vals: "length suffixIfArgs = length suffixValResults"
      and len_refs: "length suffixIfArgs = length suffixRefResults"
      and k_plus_len: "k + length suffixFnArgs = length (FI_TmArgs funInfo)"
      and vals_sound:
            "\<forall>i < length suffixFnArgs.
               sound_term_result state env
                 (apply_subst tySubst (fst (suffixFnArgs ! i)))
                 (suffixValResults ! i)"
      and lvals_sound:
            "\<forall>i < length suffixFnArgs.
               fst (snd (suffixFnArgs ! i)) = Ref \<longrightarrow>
                 sound_lvalue_result state env storeTyping
                   (apply_subst tySubst (fst (suffixFnArgs ! i)))
                   (suffixRefResults ! i)"
      and partial_sound_k:
            "sound_partial_arg_processing_result env names funInfo tySubst k storeTyping
               partialResult"
  shows "sound_partial_arg_processing_result env names funInfo tySubst
           (k + length suffixFnArgs) storeTyping
           (fold process_one_arg (zip suffixIfArgs (zip suffixRefResults suffixValResults))
                                 partialResult)"
using suffix_at_k suffix_names var_ref_match len_vals len_refs k_plus_len vals_sound lvals_sound
      partial_sound_k
proof (induction suffixFnArgs arbitrary: k suffixIfArgs suffixValResults
                                          suffixRefResults partialResult)
  case Nil
  from Nil.prems(3) have empty_ifArgs: "suffixIfArgs = []"
    by (cases suffixIfArgs) auto
  from Nil.prems(4) empty_ifArgs have empty_vals: "suffixValResults = []"
    by (cases suffixValResults) auto
  from Nil.prems(5) empty_ifArgs have empty_refs: "suffixRefResults = []"
    by (cases suffixRefResults) auto
  have fold_eq: "fold process_one_arg
                   (zip suffixIfArgs (zip suffixRefResults suffixValResults)) partialResult
                  = partialResult"
    using empty_ifArgs empty_vals empty_refs by simp
  show ?case using Nil.prems(9) fold_eq by simp
next
  case (Cons arg restArgs)
  from Cons.prems(3) obtain ifHead ifRest where
    ifArgs_eq: "suffixIfArgs = ifHead # ifRest" and
    ifRest_match: "list_all2 (\<lambda>(_, vor1, gh1) (_, vor2, gh2). vor1 = vor2 \<and> gh1 = gh2)
                              restArgs ifRest"
    by (cases suffixIfArgs) auto
  obtain paramTy vor gh where arg_eq: "arg = (paramTy, vor, gh)"
    by (cases arg) auto
  obtain ifName ifVor ifGh where ifHead_eq: "ifHead = (ifName, ifVor, ifGh)"
    by (cases ifHead)
  \<comment> \<open>The parameter name comes from the InterpFun arg; the Var/Ref and ghost
      markers match. \<close>
  define paramName where "paramName = ifName"
  from Cons.prems(3) ifArgs_eq arg_eq ifHead_eq
  have head_match: "vor = ifVor" and gh_match: "gh = ifGh" by simp_all
  from Cons.prems(4) ifArgs_eq obtain valHead valRest where
    vals_eq: "suffixValResults = valHead # valRest" and
    len_vals': "length ifRest = length valRest"
    by (cases suffixValResults) auto
  from Cons.prems(5) ifArgs_eq obtain refHead refRest where
    refs_eq: "suffixRefResults = refHead # refRest" and
    len_refs': "length ifRest = length refRest"
    by (cases suffixRefResults) auto

  from Cons.prems(1) have k_bound: "k < length (FI_TmArgs funInfo)"
    using Cons.prems(6)
    by (metis drop_eq_Nil2 linorder_le_less_linear neq_Nil_conv)
  hence k_names: "k < length names" using names_len by simp
  from Cons.prems(1) have kth: "FI_TmArgs funInfo ! k = arg"
    using k_bound nth_via_drop by metis
  from kth arg_eq
  have kth_arg: "FI_TmArgs funInfo ! k = (paramTy, vor, gh)" by simp
  \<comment> \<open>names ! k is the head name of the IF-args suffix. \<close>
  have paramName_eq: "names ! k = paramName"
  proof -
    have "names ! k = (drop k names) ! 0" using k_names by simp
    also have "\<dots> = (map fst suffixIfArgs) ! 0" using Cons.prems(2) by simp
    also have "\<dots> = ifName" using ifArgs_eq ifHead_eq by simp
    finally show ?thesis by (simp add: paramName_def)
  qed

  from Cons.prems(7) have val_sound_head:
    "sound_term_result state env (apply_subst tySubst paramTy) valHead"
    using arg_eq vals_eq by force
  from Cons.prems(8) have lval_sound_head:
    "vor = Ref \<Longrightarrow> sound_lvalue_result state env storeTyping
                     (apply_subst tySubst paramTy) refHead"
    using arg_eq refs_eq by force

  let ?step = "process_one_arg ((paramName, vor, gh), refHead, valHead) partialResult"
  have step_sound:
    "sound_partial_arg_processing_result env names funInfo tySubst (Suc k) storeTyping ?step"
  proof (cases partialResult)
    case (Inl err)
    from process_one_arg_preserve_error[of env names funInfo tySubst k storeTyping err
                                           "((paramName, vor, gh), refHead, valHead)"]
         Cons.prems(9) Inl
    show ?thesis by simp
  next
    case (Inr partialState)
    from process_one_arg_step_sound[OF sme_caller wf_env fn_lookup k_bound
                                       k_names dist_names kth_arg paramName_eq
                                       val_sound_head lval_sound_head]
         Cons.prems(9) Inr
    show ?thesis by simp
  qed

  have rest_at_k1: "restArgs = drop (Suc k) (FI_TmArgs funInfo)"
    using Cons.prems(1)
    by (metis Cons_nth_drop_Suc k_bound list.inject)
  have rest_names: "map fst ifRest = drop (Suc k) names"
  proof -
    have "ifName # map fst ifRest = map fst suffixIfArgs"
      using ifArgs_eq ifHead_eq by simp
    also have "\<dots> = drop k names" using Cons.prems(2) .
    finally have "ifName # map fst ifRest = drop k names" .
    thus ?thesis using k_names by (metis Cons_nth_drop_Suc list.inject)
  qed
  have len_rest: "Suc k + length restArgs = length (FI_TmArgs funInfo)"
    using Cons.prems(6) by simp
  have vals_sound_rest: "\<forall>i < length restArgs.
      sound_term_result state env
        (apply_subst tySubst (fst (restArgs ! i)))
        (valRest ! i)"
  proof (intro allI impI)
    fix i assume "i < length restArgs"
    hence "Suc i < length (arg # restArgs)" by simp
    from Cons.prems(7)[rule_format, OF this]
    have "sound_term_result state env
            (apply_subst tySubst (fst ((arg # restArgs) ! Suc i)))
            (suffixValResults ! Suc i)" .
    thus "sound_term_result state env
            (apply_subst tySubst (fst (restArgs ! i)))
            (valRest ! i)"
      by (simp add: vals_eq)
  qed
  have lvals_sound_rest: "\<forall>i < length restArgs.
      fst (snd (restArgs ! i)) = Ref \<longrightarrow>
        sound_lvalue_result state env storeTyping
          (apply_subst tySubst (fst (restArgs ! i)))
          (refRest ! i)"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < length restArgs"
    assume is_ref: "fst (snd (restArgs ! i)) = Ref"
    from i_lt have "Suc i < length (arg # restArgs)" by simp
    moreover from is_ref have "fst (snd ((arg # restArgs) ! Suc i)) = Ref" by simp
    ultimately have "sound_lvalue_result state env storeTyping
                        (apply_subst tySubst (fst ((arg # restArgs) ! Suc i)))
                        (suffixRefResults ! Suc i)"
      using Cons.prems(8)[rule_format] by blast
    thus "sound_lvalue_result state env storeTyping
            (apply_subst tySubst (fst (restArgs ! i))) (refRest ! i)"
      by (simp add: refs_eq)
  qed

  have fold_unfold: "fold process_one_arg
      (zip suffixIfArgs (zip suffixRefResults suffixValResults)) partialResult
    = fold process_one_arg (zip ifRest (zip refRest valRest)) ?step"
    using ifArgs_eq vals_eq refs_eq head_match gh_match ifHead_eq paramName_def by simp

  from Cons.IH[OF rest_at_k1 rest_names ifRest_match len_vals' len_refs' len_rest
                  vals_sound_rest lvals_sound_rest step_sound]
  have "sound_partial_arg_processing_result env names funInfo tySubst
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
      and fi_match: "fun_info_matches_interp_fun env funInfo f"
      and ty_len: "length tyArgs = length (FI_TyArgs funInfo)"
      and ty_wk:  "list_all (is_well_kinded env) tyArgs"
      and vals_sound:
            "\<forall>i < length (FI_TmArgs funInfo).
               sound_term_result state env
                 (apply_subst outerSubst (fst (FI_TmArgs funInfo ! i)))
                 (map (interp_term d fuel state) argTms ! i)"
      and lvals_sound:
            "\<forall>i < length (FI_TmArgs funInfo).
               fst (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow>
                 sound_lvalue_result state env storeTyping
                   (apply_subst outerSubst (fst (FI_TmArgs funInfo ! i)))
                   (map (interp_writable_lvalue d fuel state) argTms ! i)"
      and len_argTms: "length argTms = length (FI_TmArgs funInfo)"
  shows "sound_arg_processing_result env (map fst (IF_Args f)) funInfo tySubst storeTyping
           (fold process_one_arg
              (zip (IF_Args f)
                   (zip (map (interp_writable_lvalue d fuel state) argTms)
                        (map (interp_term d fuel state) argTms)))
              (Inr (state \<lparr> IS_Locals := fmempty,
                             IS_Refs := fmempty,
                             IS_ConstLocals := {||},
                             IS_TyArgs := tySubst \<rparr>)))"
proof -
  let ?clearedState = "state \<lparr> IS_Locals := fmempty, IS_Refs := fmempty,
                                IS_ConstLocals := {||},
                                IS_TyArgs := tySubst \<rparr>"
  let ?valResults = "map (interp_term d fuel state) argTms"
  let ?refResults = "map (interp_writable_lvalue d fuel state) argTms"
  let ?names = "map fst (IF_Args f)"

  \<comment> \<open>From fi_match: parameter names are distinct, the Var/Ref markers align with
      FI_TmArgs, and the arg lists have equal length. \<close>
  from fi_match have vor_match:
    "list_all2 (\<lambda>(_, vor1, gh1) (_, vor2, gh2). vor1 = vor2 \<and> gh1 = gh2) (FI_TmArgs funInfo) (IF_Args f)"
    and dist_names: "distinct ?names"
    unfolding fun_info_matches_interp_fun_def by simp_all
  from vor_match have len_ifargs: "length (IF_Args f) = length (FI_TmArgs funInfo)"
    by (simp add: list_all2_lengthD)
  hence names_len: "length ?names = length (FI_TmArgs funInfo)" by simp

  \<comment> \<open>The caller's env has no unresolved abstract types (interpreter runs only on
      fully-resolved programs), so the fun_ghost_constraint env shapes collapse. \<close>
  have abs_empty: "TE_AbstractTypes env = {||}"
    using sme_caller unfolding state_matches_env_def by blast

  \<comment> \<open>H2a: initial state is sound at k=0. \<close>
  have sme_cleared:
    "state_matches_env ?clearedState (partial_body_env_for env ?names funInfo 0) storeTyping"
    using cleared_state_matches_partial_env_zero
            [OF sme_caller ty_len ty_wk,
             where tySubst=tySubst and names="map fst (IF_Args f)"]
    by (simp add: tySubst_def)
  have partial_sound_zero:
    "sound_partial_arg_processing_result env ?names funInfo tySubst 0 storeTyping
       (Inr ?clearedState)"
    unfolding sound_partial_arg_processing_result_def
    using sme_cleared storeTyping_extends_refl by auto

  \<comment> \<open>Translate vals_sound / lvals_sound from outerSubst-form to tySubst-form.
      The translation uses apply_subst_compose_zip plus apply_state_id (ground). \<close>

  \<comment> \<open>Distinctness and groundness conditions. \<close>
  from wf_env fn_lookup have ty_dist: "distinct (FI_TyArgs funInfo)"
    unfolding tyenv_well_formed_def tyenv_fun_tyvars_distinct_def by blast

  \<comment> \<open>Each parameter type mentions only the function's own type variables. \<close>
  have paramTy_subset:
    "\<And>i. i < length (FI_TmArgs funInfo) \<Longrightarrow>
            type_tyvars (fst (FI_TmArgs funInfo ! i)) \<subseteq> set (FI_TyArgs funInfo)"
  proof -
    fix i assume i_bound: "i < length (FI_TmArgs funInfo)"
    have "fst (FI_TmArgs funInfo ! i) \<in> fst ` set (FI_TmArgs funInfo)"
      using i_bound by force
    with fun_info_types_tyvars_subset(1)[OF wf_env abs_empty fn_lookup]
    show "type_tyvars (fst (FI_TmArgs funInfo ! i)) \<subseteq> set (FI_TyArgs funInfo)" by blast
  qed

  \<comment> \<open>For each i < length FI_TmArgs funInfo, apply_subst tySubst paramTy_i is ground. \<close>
  have paramTy_apply_ground:
    "\<And>i. i < length (FI_TmArgs funInfo) \<Longrightarrow>
            type_tyvars (apply_subst tySubst (fst (FI_TmArgs funInfo ! i))) = {}"
  proof -
    fix i assume i_bound: "i < length (FI_TmArgs funInfo)"
    let ?paramTy_i = "fst (FI_TmArgs funInfo ! i)"
    have paramTy_tyvars:
      "type_tyvars ?paramTy_i \<subseteq> fset (fset_of_list (FI_TyArgs funInfo))"
      using paramTy_subset[OF i_bound] by (simp add: fset_of_list.rep_eq)
    \<comment> \<open>fmdom tySubst = fset_of_list (FI_TyArgs funInfo). \<close>
    have fmdom_tySubst: "fmdom tySubst = fset_of_list (FI_TyArgs funInfo)"
      using tySubst_def ty_len
      by (simp add: fset_of_list.rep_eq)
    \<comment> \<open>subst_range_tyvars tySubst = {} (each entry is apply_subst (IS_TyArgs state) of
        a type that is well-kinded in env, so each entry is ground). \<close>
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
        from ty_wk j_lt have "is_well_kinded env (tyArgs ! j)"
          by (simp add: list_all_length)
        from is_well_kinded_apply_IS_TyArgs_ground[OF sme_caller this]
        show "type_tyvars t = {}" using t_eq by simp
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
       apply_subst tySubst (fst (FI_TmArgs funInfo ! i))
       = apply_subst (IS_TyArgs state)
           (apply_subst outerSubst (fst (FI_TmArgs funInfo ! i)))"
  proof -
    fix i assume i_bound: "i < length (FI_TmArgs funInfo)"
    let ?paramTy_i = "fst (FI_TmArgs funInfo ! i)"
    show "apply_subst tySubst ?paramTy_i
            = apply_subst (IS_TyArgs state) (apply_subst outerSubst ?paramTy_i)"
      unfolding tySubst_def outerSubst_def
      using apply_subst_compose_zip[OF ty_len[symmetric] paramTy_subset[OF i_bound] ty_dist] .
  qed

  \<comment> \<open>vals_sound translated to tySubst form. \<close>
  have vals_sound_tySubst:
    "\<forall>i < length (FI_TmArgs funInfo).
       sound_term_result state env
         (apply_subst tySubst (fst (FI_TmArgs funInfo ! i)))
         (?valResults ! i)"
  proof (intro allI impI)
    fix i assume i_bound: "i < length (FI_TmArgs funInfo)"
    let ?paramTy_i = "fst (FI_TmArgs funInfo ! i)"
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
       fst (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow>
         sound_lvalue_result state env storeTyping
           (apply_subst tySubst (fst (FI_TmArgs funInfo ! i)))
           (?refResults ! i)"
  proof (intro allI impI)
    fix i assume i_bound: "i < length (FI_TmArgs funInfo)"
      and is_ref: "fst (snd (FI_TmArgs funInfo ! i)) = Ref"
    let ?paramTy_i = "fst (FI_TmArgs funInfo ! i)"
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

  \<comment> \<open>length agreement on IF_Args (var_ref_match = vor_match from above). \<close>
  from vor_match have len_ifArgs: "length (FI_TmArgs funInfo) = length (IF_Args f)"
    by (rule list_all2_lengthD)

  have len_vals: "length (IF_Args f) = length ?valResults"
    using len_ifArgs len_argTms by simp
  have len_refs: "length (IF_Args f) = length ?refResults"
    using len_ifArgs len_argTms by simp

  \<comment> \<open>Invoke H2c with k=0. \<close>
  have k_plus_len_zero: "(0::nat) + length (FI_TmArgs funInfo) = length (FI_TmArgs funInfo)"
    by simp
  have suffix_at_zero: "FI_TmArgs funInfo = drop 0 (FI_TmArgs funInfo)" by simp
  have suffix_names_zero: "map fst (IF_Args f) = drop 0 ?names" by simp
  from fold_process_one_arg_sound_gen[
      OF sme_caller wf_env fn_lookup dist_names names_len suffix_at_zero
         suffix_names_zero vor_match
         len_vals len_refs k_plus_len_zero vals_sound_tySubst lvals_sound_tySubst
         partial_sound_zero]
  have gen_result:
    "sound_partial_arg_processing_result env ?names funInfo tySubst
       (0 + length (FI_TmArgs funInfo)) storeTyping
       (fold process_one_arg
         (zip (IF_Args f) (zip ?refResults ?valResults)) (Inr ?clearedState))" .

  \<comment> \<open>Bridge from partial_body_env_for at length FI_TmArgs to body_env_for. \<close>
  have pbe_full:
    "partial_body_env_for env ?names funInfo (length (FI_TmArgs funInfo))
       = body_env_for env ?names funInfo"
    using partial_body_env_for_full[of funInfo ?names env] names_len by simp

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
   - globals_eq, functions_eq, default_ctors_eq: the globals, functions and
     default constructors of postCallState equal those of state. Phrasing these
     as hypotheses keeps the lemma usable in both the Babylon and extern cases.
   - dt_eq, ty_eq: env_mid's datatype fields agree with env (bodyEnv =
     body_env_for env funInfo, and env_mid agrees with bodyEnv on the pinned
     fields via tyenv_fixed_eq). This is all that value_has_type reads.
*)
lemma restore_scope_sound:
  fixes state postCallState :: "'w InterpState"
  assumes state_env: "state_matches_env state env storeTyping"
      and post_env_mid: "state_matches_env postCallState env_mid postStoreTyping"
      and ext_post: "storeTyping_extends storeTyping postStoreTyping"
      and globals_eq: "IS_Globals postCallState = IS_Globals state"
      and functions_eq: "IS_Functions postCallState = IS_Functions state"
      and default_ctors_eq: "IS_DefaultCtors postCallState = IS_DefaultCtors state"
      and dt_eq: "TE_DataCtors env = TE_DataCtors env_mid"
      and ty_eq: "TE_Datatypes env = TE_Datatypes env_mid"
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
    cn_src: "const_locals_match state env" and
    swt_src: "store_well_typed state env storeTyping" and
    ta_src: "ty_args_well_formed state env"
    unfolding state_matches_env_def
    by blast+

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

  \<comment> \<open>Conjunct 1: local_vars_exist_in_state. Locals/refs come from the old state,
      so this reduces to the original state's witness. The store is truncated,
      but since local addresses are all < length storeTyping, the prefix relation
      on storeTyping is unchanged. \<close>
  have rs_lv: "local_vars_exist_in_state ?rs env storeTyping"
    unfolding local_vars_exist_in_state_def
  proof (intro allI impI)
    fix name ty
    assume lk: "fmlookup (TE_LocalVars env) name = Some ty"
    from lv_src lk
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

  \<comment> \<open>Conjunct 7: const_locals_match. Direct. \<close>
  have rs_cn: "const_locals_match ?rs env"
    using cn_src rs_consts
    unfolding const_locals_match_def by simp

  \<comment> \<open>Conjunct 8: store_well_typed. The interesting one.
      For each prefix address, the slot has type (storeTyping ! addr) under env.
      We know (postStoreTyping ! addr) = (storeTyping ! addr) and that the slot
      has type (postStoreTyping ! addr) under env_mid. value_has_type reads only
      the datatype fields, on which env and env_mid agree, so it transfers from
      env_mid to env although the two have different type variables.
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
    have slot_ty_eq: "postStoreTyping ! addr = storeTyping ! addr"
      using post_st_agree a_lt_st by simp
    from vht_mid slot_ty_eq
    have vht_mid': "value_has_type env_mid (IS_Store postCallState ! addr) (storeTyping ! addr)"
      by simp
    \<comment> \<open>Transfer env_mid to env. \<close>
    have vht_env: "value_has_type env (IS_Store postCallState ! addr) (storeTyping ! addr)"
      using vht_mid' value_has_type_ground_cong_env[OF dt_eq ty_eq] by simp
    show "value_has_type env (IS_Store ?rs ! addr) (storeTyping ! addr)"
      using val_eq vht_env by simp
  qed

  have rs_ta: "ty_args_well_formed ?rs env"
    using ta_src rs_tyargs unfolding ty_args_well_formed_def by simp

  have rs_dc: "default_ctors_match ?rs env"
    using state_env default_ctors_eq
    unfolding state_matches_env_def default_ctors_match_def
    by simp

  \<comment> \<open>The tables of the restored state are postCallState's, which are those of
      env_mid, and env_mid has env's. \<close>
  have rs_tm: "tables_match ?rs env"
    using post_env_mid dt_eq ty_eq
    unfolding state_matches_env_def tables_match_def
    by simp

  have rs_abs: "TE_AbstractTypes env = {||}"
    using state_env unfolding state_matches_env_def by blast

  from rs_lv rs_gv rs_no_lv rs_no_gv rs_fes rs_no_fun rs_cn rs_swt rs_ta rs_dc rs_tm rs_abs
  show ?thesis
    unfolding state_matches_env_def by blast
qed


end
