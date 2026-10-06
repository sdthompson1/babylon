theory ModuleBodyEnv
  imports CoreTyEnvWellFormed
begin

(* The type environment in which a function body is typechecked
   (module_body_env_for), and the proof that it is well-formed whenever the
   enclosing environment is (module_body_env_for_well_formed).

   This theory deliberately sits low in the import graph (it does not need
   CoreModule or the statement typechecker), because both the module
   typechecker (CoreModuleTypecheck.thy) and the interpreter's
   state_matches_env (interpreter/StateMatchesEnv.thy) build on it. *)


(* ========================================================================== *)
(* The body environment for checking a function definition                    *)
(* ========================================================================== *)

(* This defines the type environment in which the body of a function must
   typecheck.

   This is the module-level analogue of body_env_for (interpreter/StateMatchesEnv.thy)
   generalized in one way: the module env may have unresolved abstract types,
   so TE_TypeVars is TE_AbstractTypes env plus the function's own type
   parameters (rather than the type parameters alone), and TE_RuntimeTypeVars
   likewise keeps the abstract types that are runtime type variables.

   Ghost functions are covered, as they are in body_env_for: a ghost
   function's parameters are ghost locals and its type parameters are not
   runtime type variables.

   In the NotGhost case, the TE_RuntimeTypeVars formula is the same one used
   by tyenv_fun_ghost_constraint (CoreTyEnvWellFormed.thy) when it checks a
   non-ghost function's argument/return types for being runtime types, so
   runtime-type facts about the signature transfer directly to the body env.

   On a *closed* module (TE_AbstractTypes env = {||}), this definition
   coincides field-for-field with body_env_for, for any function (lemma
   module_body_env_for_eq_body_env_for in StateMatchesEnv.thy) - which is
   why state_matches_env's body-typecheck obligation matches the module-level
   check when an InterpState is built. *)

definition module_body_env_for :: "CoreTyEnv \<Rightarrow> string list \<Rightarrow> FunInfo \<Rightarrow> CoreTyEnv" where
  "module_body_env_for env names info =
    env \<lparr>
      TE_LocalVars := fmap_of_list (zip names (map fst (FI_TmArgs info))),
      TE_GhostLocals := (if FI_Ghost info = Ghost then fset_of_list names
                         else fset_of_list
                                (map fst
                                     (filter (\<lambda>(_, _, gh). gh = Ghost)
                                             (zip names (map snd (FI_TmArgs info)))))),
      TE_ConstLocals := fset_of_list
        (map fst
             (filter (\<lambda>(_, vor, _). vor = Var) (zip names (map snd (FI_TmArgs info))))),
      TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list (FI_TyArgs info),
      TE_RuntimeTypeVars := (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                             |\<union>| (if FI_Ghost info = NotGhost
                                   then fset_of_list (FI_TyArgs info)
                                   else {||}),
      TE_ReturnType := FI_ReturnType info,
      TE_FunctionGhost := FI_Ghost info,
      TE_FunctionImpure := FI_Impure info,
      TE_ProofGoal := None,
      TE_ProofTopLevel := False
    \<rparr>"


(* ========================================================================== *)
(* Well-formedness of function-body environments                              *)
(* ========================================================================== *)

(* The body env of a declared function over a well-formed env is well-formed. *)

(* The interpreter-side body_env_for_well_formed (StateMatchesEnv.thy) is a
   corollary of this lemma, by way of the closed-module equality
   (module_body_env_for_eq_body_env_for). *)

lemma module_body_env_for_well_formed:
  assumes wf: "tyenv_well_formed env"
      and lk: "fmlookup (TE_Functions env) fname = Some info"
      and len: "length names = length (FI_TmArgs info)"
  shows "tyenv_well_formed (module_body_env_for env names info)"
proof -
  let ?be = "module_body_env_for env names info"

  have names_eq: "map fst (zip names (map fst (FI_TmArgs info))) = names"
    using len by simp

  \<comment> \<open>A defined local's type is one of the signature's argument types.\<close>
  have locals_val: "\<And>v ty. fmlookup (TE_LocalVars ?be) v = Some ty
                      \<Longrightarrow> ty \<in> fst ` set (FI_TmArgs info)"
  proof -
    fix v ty assume "fmlookup (TE_LocalVars ?be) v = Some ty"
    then have "(v, ty) \<in> set (zip names (map fst (FI_TmArgs info)))"
      by (auto simp: module_body_env_for_def fmlookup_of_list dest: map_of_SomeD)
    then have "ty \<in> set (map fst (FI_TmArgs info))"
      by (auto dest: set_zip_rightD)
    then show "ty \<in> fst ` set (FI_TmArgs info)" by auto
  qed
  have locals_dom: "fmdom (TE_LocalVars ?be) = fset_of_list names"
    by (simp add: module_body_env_for_def names_eq)

  \<comment> \<open>A non-ghost local of a non-ghost function's body env is a non-ghost
      parameter: its type is paired with NotGhost in the signature.\<close>
  have locals_val_ng: "\<And>v ty. fmlookup (TE_LocalVars ?be) v = Some ty
                        \<Longrightarrow> v |\<notin>| TE_GhostLocals ?be \<Longrightarrow> FI_Ghost info = NotGhost
                        \<Longrightarrow> \<exists>vor. (ty, vor, NotGhost) \<in> set (FI_TmArgs info)"
  proof -
    fix v ty
    assume lk_v: "fmlookup (TE_LocalVars ?be) v = Some ty"
       and ng_v: "v |\<notin>| TE_GhostLocals ?be"
       and ng: "FI_Ghost info = NotGhost"
    from lk_v have "(v, ty) \<in> set (zip names (map fst (FI_TmArgs info)))"
      by (auto simp: module_body_env_for_def fmlookup_of_list dest: map_of_SomeD)
    then obtain i where i_lt: "i < length names" and v_eq: "names ! i = v"
                    and ty_eq: "ty = fst (FI_TmArgs info ! i)"
      using len by (auto simp: in_set_zip)
    obtain vor gh where fi_i: "FI_TmArgs info ! i = (ty, vor, gh)"
      using ty_eq by (cases "FI_TmArgs info ! i") auto
    have "gh = NotGhost"
    proof (rule ccontr)
      assume "gh \<noteq> NotGhost"
      hence g: "gh = Ghost" by (cases gh) auto
      have "(v, vor, gh) \<in> set (zip names (map snd (FI_TmArgs info)))"
        unfolding in_set_zip using fi_i i_lt len v_eq by auto
      hence "v |\<in>| TE_GhostLocals ?be"
        using g ng by (force simp: module_body_env_for_def fset_of_list_elem image_iff)
      thus False using ng_v by simp
    qed
    thus "\<exists>vor. (ty, vor, NotGhost) \<in> set (FI_TmArgs info)"
      using fi_i i_lt len by (metis nth_mem)
  qed

  \<comment> \<open>Side facts from the enclosing env's well-formedness.\<close>
  have gvwk: "\<And>name ty. fmlookup (TE_GlobalVars env) name = Some ty \<Longrightarrow>
                is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env \<rparr>) ty"
    using wf unfolding tyenv_well_formed_def tyenv_vars_well_kinded_def by blast
  have gvrt: "\<And>name ty. fmlookup (TE_GlobalVars env) name = Some ty \<Longrightarrow>
                is_runtime_type (env \<lparr> TE_TypeVars := TE_AbstractTypes env,
                                       TE_RuntimeTypeVars :=
                                         TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env \<rparr>) ty"
    using wf unfolding tyenv_well_formed_def tyenv_vars_runtime_def by blast
  have pwk: "\<And>ctorName dtName tyVars payload.
               fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload) \<Longrightarrow>
               is_well_kinded (env \<lparr> TE_TypeVars :=
                                     TE_AbstractTypes env |\<union>| fset_of_list tyVars \<rparr>) payload"
    using wf unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def by blast
  have ftwk: "\<And>funName info'. fmlookup (TE_Functions env) funName = Some info' \<Longrightarrow>
                (\<forall>ty \<in> fst ` set (FI_TmArgs info').
                   is_well_kinded (env \<lparr> TE_TypeVars :=
                                         TE_AbstractTypes env
                                         |\<union>| fset_of_list (FI_TyArgs info') \<rparr>) ty)
                \<and> is_well_kinded (env \<lparr> TE_TypeVars :=
                                        TE_AbstractTypes env
                                        |\<union>| fset_of_list (FI_TyArgs info') \<rparr>)
                                 (FI_ReturnType info')"
    using wf unfolding tyenv_well_formed_def tyenv_fun_types_well_kinded_def by blast
  have fgc: "\<And>funName info'. fmlookup (TE_Functions env) funName = Some info' \<Longrightarrow>
               FI_Ghost info' = NotGhost \<Longrightarrow>
               (\<forall>ty vor. (ty, vor, NotGhost) \<in> set (FI_TmArgs info') \<longrightarrow>
                  is_runtime_type
                    (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                          |\<union>| fset_of_list (FI_TyArgs info'),
                           TE_RuntimeTypeVars :=
                             (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                             |\<union>| fset_of_list (FI_TyArgs info') \<rparr>) ty)
               \<and> is_runtime_type
                   (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                         |\<union>| fset_of_list (FI_TyArgs info'),
                          TE_RuntimeTypeVars :=
                            (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                            |\<union>| fset_of_list (FI_TyArgs info') \<rparr>)
                   (FI_ReturnType info')"
    using wf
    unfolding tyenv_well_formed_def tyenv_fun_ghost_constraint_def Let_def by blast
  have frc: "\<And>funName info'. fmlookup (TE_Functions env) funName = Some info' \<Longrightarrow>
               FI_Ghost info' = NotGhost \<Longrightarrow> is_complete_type (FI_ReturnType info')"
    using wf
    unfolding tyenv_well_formed_def tyenv_fun_return_types_complete_def by blast
  have npr: "\<And>ctorName dtName tyVars payload.
               fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload) \<Longrightarrow>
               dtName |\<notin>| TE_GhostDatatypes env \<Longrightarrow>
               is_runtime_type
                 (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyVars,
                        TE_RuntimeTypeVars :=
                          (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                          |\<union>| fset_of_list tyVars \<rparr>) payload"
    using wf
    unfolding tyenv_well_formed_def tyenv_nonghost_payloads_runtime_def by blast

  show ?thesis
    unfolding tyenv_well_formed_def
  proof (intro conjI)
    show "tyenv_vars_well_kinded ?be"
      unfolding tyenv_vars_well_kinded_def
    proof (intro conjI allI impI)
      fix v ty assume "fmlookup (TE_LocalVars ?be) v = Some ty"
      then have "ty \<in> fst ` set (FI_TmArgs info)" by (rule locals_val)
      then have "is_well_kinded (env \<lparr> TE_TypeVars :=
                                       TE_AbstractTypes env
                                       |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
        using ftwk[OF lk] by blast
      moreover have "is_well_kinded ?be ty
                       = is_well_kinded (env \<lparr> TE_TypeVars :=
                                               TE_AbstractTypes env
                                               |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
        by (intro is_well_kinded_cong_env) (simp_all add: module_body_env_for_def)
      ultimately show "is_well_kinded ?be ty" by simp
    next
      fix name ty assume "fmlookup (TE_GlobalVars ?be) name = Some ty"
      then have lk_g: "fmlookup (TE_GlobalVars env) name = Some ty"
        by (simp add: module_body_env_for_def)
      have "is_well_kinded (?be \<lparr> TE_TypeVars := TE_AbstractTypes ?be \<rparr>) ty
              = is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env \<rparr>) ty"
        by (intro is_well_kinded_cong_env) (simp_all add: module_body_env_for_def)
      then show "is_well_kinded (?be \<lparr> TE_TypeVars := TE_AbstractTypes ?be \<rparr>) ty"
        using gvwk[OF lk_g] by simp
    qed
  next
    show "tyenv_vars_runtime ?be"
      unfolding tyenv_vars_runtime_def
    proof (intro conjI allI impI)
      fix v ty
      assume asm: "fmlookup (TE_LocalVars ?be) v = Some ty \<and> v |\<notin>| TE_GhostLocals ?be"
      then have lk_l: "fmlookup (TE_LocalVars ?be) v = Some ty"
            and ng_l: "v |\<notin>| TE_GhostLocals ?be" by blast+
      show "is_runtime_type ?be ty"
      proof (cases "FI_Ghost info")
        case Ghost
        have "v |\<in>| fset_of_list names"
          using fmdomI[OF lk_l] locals_dom by simp
        then have "v |\<in>| TE_GhostLocals ?be"
          using Ghost by (simp add: module_body_env_for_def)
        then show ?thesis using ng_l by simp
      next
        case NotGhost
        obtain vor where "(ty, vor, NotGhost) \<in> set (FI_TmArgs info)"
          using locals_val_ng[OF lk_l ng_l NotGhost] by blast
        then have "is_runtime_type
                     (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                           |\<union>| fset_of_list (FI_TyArgs info),
                            TE_RuntimeTypeVars :=
                              (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                              |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
          using fgc[OF lk NotGhost] by blast
        moreover have "is_runtime_type ?be ty
                         = is_runtime_type
                             (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                                   |\<union>| fset_of_list (FI_TyArgs info),
                                    TE_RuntimeTypeVars :=
                                      (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                      |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
          by (intro is_runtime_type_cong_env)
             (simp_all add: module_body_env_for_def NotGhost)
        ultimately show ?thesis by simp
      qed
    next
      fix name ty
      assume asm: "fmlookup (TE_GlobalVars ?be) name = Some ty"
      then have lk_g: "fmlookup (TE_GlobalVars env) name = Some ty"
        by (simp add: module_body_env_for_def)
      have rt0: "is_runtime_type (env \<lparr> TE_TypeVars := TE_AbstractTypes env,
                                        TE_RuntimeTypeVars :=
                                          TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env \<rparr>) ty"
        using gvrt[OF lk_g] .
      show "is_runtime_type (?be \<lparr> TE_TypeVars := TE_AbstractTypes ?be,
                                   TE_RuntimeTypeVars :=
                                     TE_AbstractTypes ?be |\<inter>| TE_RuntimeTypeVars ?be \<rparr>) ty"
      proof (rule is_runtime_type_mono_rtv[OF rt0])
        show "fset (TE_RuntimeTypeVars
                      (env \<lparr> TE_TypeVars := TE_AbstractTypes env,
                             TE_RuntimeTypeVars :=
                               TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env \<rparr>))
                \<subseteq> fset (TE_RuntimeTypeVars
                          (?be \<lparr> TE_TypeVars := TE_AbstractTypes ?be,
                                 TE_RuntimeTypeVars :=
                                   TE_AbstractTypes ?be |\<inter>| TE_RuntimeTypeVars ?be \<rparr>))"
          by (auto simp: module_body_env_for_def)
        show "TE_GhostDatatypes
                (?be \<lparr> TE_TypeVars := TE_AbstractTypes ?be,
                       TE_RuntimeTypeVars :=
                         TE_AbstractTypes ?be |\<inter>| TE_RuntimeTypeVars ?be \<rparr>)
                = TE_GhostDatatypes
                    (env \<lparr> TE_TypeVars := TE_AbstractTypes env,
                           TE_RuntimeTypeVars :=
                             TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env \<rparr>)"
          by (simp add: module_body_env_for_def)
      qed
    qed
  next
    show "tyenv_ghost_vars_subset ?be"
      unfolding tyenv_ghost_vars_subset_def
      \<comment> \<open>Both the ghost-function case (all names) and the ghost-parameter case
          (names of a filtered zip) are subsets of the locals' domain, names.\<close>
      by (auto simp: module_body_env_for_def names_eq less_eq_fset.rep_eq
                     fset_of_list.rep_eq fimage.rep_eq ffilter.rep_eq
               dest: set_zip_leftD)
  next
    show "tyenv_return_type_well_kinded ?be"
    proof -
      have "is_well_kinded (env \<lparr> TE_TypeVars :=
                                  TE_AbstractTypes env
                                  |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) (FI_ReturnType info)"
        using ftwk[OF lk] by blast
      moreover have "is_well_kinded ?be (FI_ReturnType info)
                       = is_well_kinded (env \<lparr> TE_TypeVars :=
                                               TE_AbstractTypes env
                                               |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                                        (FI_ReturnType info)"
        by (intro is_well_kinded_cong_env) (simp_all add: module_body_env_for_def)
      ultimately show ?thesis
        unfolding tyenv_return_type_well_kinded_def
        by (simp add: module_body_env_for_def)
    qed
  next
    show "tyenv_return_type_runtime ?be"
      unfolding tyenv_return_type_runtime_def
    proof (intro impI)
      assume "TE_FunctionGhost ?be = NotGhost"
      then have ng: "FI_Ghost info = NotGhost"
        by (simp add: module_body_env_for_def)
      have "is_runtime_type
              (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                    |\<union>| fset_of_list (FI_TyArgs info),
                     TE_RuntimeTypeVars :=
                       (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                       |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) (FI_ReturnType info)"
        using fgc[OF lk ng] by blast
      moreover have "is_runtime_type ?be (FI_ReturnType info)
                       = is_runtime_type
                           (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                                 |\<union>| fset_of_list (FI_TyArgs info),
                                  TE_RuntimeTypeVars :=
                                    (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                    |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                           (FI_ReturnType info)"
        by (intro is_runtime_type_cong_env)
           (simp_all add: module_body_env_for_def ng)
      ultimately show "is_runtime_type ?be (TE_ReturnType ?be)"
        by (simp add: module_body_env_for_def)
    qed
  next
    show "tyenv_return_type_complete ?be"
      unfolding tyenv_return_type_complete_def
    proof (intro impI)
      assume "TE_FunctionGhost ?be = NotGhost"
      then have ng: "FI_Ghost info = NotGhost"
        by (simp add: module_body_env_for_def)
      show "is_complete_type (TE_ReturnType ?be)"
        using frc[OF lk ng] by (simp add: module_body_env_for_def)
    qed
  next
    show "tyenv_ctors_consistent ?be"
      using wf unfolding tyenv_well_formed_def tyenv_ctors_consistent_def
      by (simp add: module_body_env_for_def)
  next
    show "tyenv_payloads_well_kinded ?be"
      unfolding tyenv_payloads_well_kinded_def
    proof (intro allI impI)
      fix ctorName dtName tyVars payload
      assume "fmlookup (TE_DataCtors ?be) ctorName = Some (dtName, tyVars, payload)"
      then have lk_c: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload)"
        by (simp add: module_body_env_for_def)
      have "is_well_kinded (?be \<lparr> TE_TypeVars :=
                                  TE_AbstractTypes ?be |\<union>| fset_of_list tyVars \<rparr>) payload
              = is_well_kinded (env \<lparr> TE_TypeVars :=
                                      TE_AbstractTypes env |\<union>| fset_of_list tyVars \<rparr>) payload"
        by (intro is_well_kinded_cong_env) (simp_all add: module_body_env_for_def)
      then show "is_well_kinded (?be \<lparr> TE_TypeVars :=
                                       TE_AbstractTypes ?be |\<union>| fset_of_list tyVars \<rparr>) payload"
        using pwk[OF lk_c] by simp
    qed
  next
    show "tyenv_ctor_tyvars_distinct ?be"
      using wf unfolding tyenv_well_formed_def tyenv_ctor_tyvars_distinct_def
      by (simp add: module_body_env_for_def)
  next
    show "tyenv_ctors_by_type_consistent ?be"
      using wf unfolding tyenv_well_formed_def tyenv_ctors_by_type_consistent_def
      by (simp add: module_body_env_for_def)
  next
    show "tyenv_fun_types_well_kinded ?be"
      unfolding tyenv_fun_types_well_kinded_def
    proof (intro allI impI)
      fix funName' info'
      assume "fmlookup (TE_Functions ?be) funName' = Some info'"
      then have lk': "fmlookup (TE_Functions env) funName' = Some info'"
        by (simp add: module_body_env_for_def)
      have cong: "\<And>ty. is_well_kinded (?be \<lparr> TE_TypeVars :=
                                             TE_AbstractTypes ?be
                                             |\<union>| fset_of_list (FI_TyArgs info') \<rparr>) ty
                    = is_well_kinded (env \<lparr> TE_TypeVars :=
                                            TE_AbstractTypes env
                                            |\<union>| fset_of_list (FI_TyArgs info') \<rparr>) ty"
        by (intro is_well_kinded_cong_env) (simp_all add: module_body_env_for_def)
      show "(\<forall>ty \<in> fst ` set (FI_TmArgs info').
               is_well_kinded (?be \<lparr> TE_TypeVars :=
                                     TE_AbstractTypes ?be
                                     |\<union>| fset_of_list (FI_TyArgs info') \<rparr>) ty)
            \<and> is_well_kinded (?be \<lparr> TE_TypeVars :=
                                    TE_AbstractTypes ?be
                                    |\<union>| fset_of_list (FI_TyArgs info') \<rparr>)
                             (FI_ReturnType info')"
        using ftwk[OF lk'] cong by blast
    qed
  next
    show "tyenv_fun_tyvars_distinct ?be"
      using wf unfolding tyenv_well_formed_def tyenv_fun_tyvars_distinct_def
      by (simp add: module_body_env_for_def)
  next
    show "tyenv_fun_ghost_constraint ?be"
      unfolding tyenv_fun_ghost_constraint_def Let_def
    proof (intro allI impI)
      fix funName' info'
      assume asm: "fmlookup (TE_Functions ?be) funName' = Some info'
                     \<and> FI_Ghost info' = NotGhost"
      then have lk': "fmlookup (TE_Functions env) funName' = Some info'"
            and ng': "FI_Ghost info' = NotGhost"
        by (simp_all add: module_body_env_for_def)
      have step: "\<And>ty. is_runtime_type
                          (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                                |\<union>| fset_of_list (FI_TyArgs info'),
                                 TE_RuntimeTypeVars :=
                                   (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                   |\<union>| fset_of_list (FI_TyArgs info') \<rparr>) ty
                    \<Longrightarrow> is_runtime_type
                          (?be \<lparr> TE_TypeVars := TE_AbstractTypes ?be
                                                |\<union>| fset_of_list (FI_TyArgs info'),
                                 TE_RuntimeTypeVars :=
                                   (TE_AbstractTypes ?be |\<inter>| TE_RuntimeTypeVars ?be)
                                   |\<union>| fset_of_list (FI_TyArgs info') \<rparr>) ty"
      proof -
        fix ty
        assume r: "is_runtime_type
                     (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                           |\<union>| fset_of_list (FI_TyArgs info'),
                            TE_RuntimeTypeVars :=
                              (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                              |\<union>| fset_of_list (FI_TyArgs info') \<rparr>) ty"
        show "is_runtime_type
                (?be \<lparr> TE_TypeVars := TE_AbstractTypes ?be
                                      |\<union>| fset_of_list (FI_TyArgs info'),
                       TE_RuntimeTypeVars :=
                         (TE_AbstractTypes ?be |\<inter>| TE_RuntimeTypeVars ?be)
                         |\<union>| fset_of_list (FI_TyArgs info') \<rparr>) ty"
          by (rule is_runtime_type_mono_rtv[OF r])
             (auto simp: module_body_env_for_def)
      qed
      show "(\<forall>ty vor. (ty, vor, NotGhost) \<in> set (FI_TmArgs info') \<longrightarrow>
               is_runtime_type
                 (?be \<lparr> TE_TypeVars := TE_AbstractTypes ?be
                                       |\<union>| fset_of_list (FI_TyArgs info'),
                        TE_RuntimeTypeVars :=
                          (TE_AbstractTypes ?be |\<inter>| TE_RuntimeTypeVars ?be)
                          |\<union>| fset_of_list (FI_TyArgs info') \<rparr>) ty)
            \<and> is_runtime_type
                (?be \<lparr> TE_TypeVars := TE_AbstractTypes ?be
                                      |\<union>| fset_of_list (FI_TyArgs info'),
                       TE_RuntimeTypeVars :=
                         (TE_AbstractTypes ?be |\<inter>| TE_RuntimeTypeVars ?be)
                         |\<union>| fset_of_list (FI_TyArgs info') \<rparr>)
                (FI_ReturnType info')"
        using fgc[OF lk' ng'] step by blast
    qed
  next
    show "tyenv_fun_return_types_complete ?be"
      unfolding tyenv_fun_return_types_complete_def
    proof (intro allI impI)
      fix funName info'
      assume "fmlookup (TE_Functions ?be) funName = Some info' \<and> FI_Ghost info' = NotGhost"
      then have lk': "fmlookup (TE_Functions env) funName = Some info'"
            and ng': "FI_Ghost info' = NotGhost"
        by (simp_all add: module_body_env_for_def)
      show "is_complete_type (FI_ReturnType info')"
        using frc[OF lk' ng'] .
    qed
  next
    show "tyenv_nonghost_payloads_runtime ?be"
      unfolding tyenv_nonghost_payloads_runtime_def
    proof (intro allI impI)
      fix ctorName dtName tyVars payload
      assume "fmlookup (TE_DataCtors ?be) ctorName = Some (dtName, tyVars, payload)"
         and "dtName |\<notin>| TE_GhostDatatypes ?be"
      then have lk_c: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload)"
            and ng_c: "dtName |\<notin>| TE_GhostDatatypes env"
        by (simp_all add: module_body_env_for_def)
      have r: "is_runtime_type
                 (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyVars,
                        TE_RuntimeTypeVars :=
                          (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                          |\<union>| fset_of_list tyVars \<rparr>) payload"
        using npr[OF lk_c ng_c] .
      show "is_runtime_type
              (?be \<lparr> TE_TypeVars := TE_AbstractTypes ?be |\<union>| fset_of_list tyVars,
                     TE_RuntimeTypeVars :=
                       (TE_AbstractTypes ?be |\<inter>| TE_RuntimeTypeVars ?be)
                       |\<union>| fset_of_list tyVars \<rparr>) payload"
        by (rule is_runtime_type_mono_rtv[OF r])
           (auto simp: module_body_env_for_def)
    qed
  next
    show "tyenv_ghost_datatypes_subset ?be"
      using wf unfolding tyenv_well_formed_def tyenv_ghost_datatypes_subset_def
      by (simp add: module_body_env_for_def)
  next
    show "tyenv_runtime_tyvars_subset ?be"
      unfolding tyenv_runtime_tyvars_subset_def
    proof
      fix n assume "n |\<in>| TE_RuntimeTypeVars ?be"
      then show "n |\<in>| TE_TypeVars ?be"
        by (auto simp: module_body_env_for_def split: if_splits)
    qed
  next
    show "tyenv_abstract_types_subset ?be"
      unfolding tyenv_abstract_types_subset_def
      by (auto simp: module_body_env_for_def)
  next
    show "tyenv_datatypes_nonempty ?be"
      using wf unfolding tyenv_well_formed_def tyenv_datatypes_nonempty_def
      by (simp add: module_body_env_for_def)
  qed
qed

end
