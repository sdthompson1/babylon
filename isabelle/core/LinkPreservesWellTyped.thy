theory LinkPreservesWellTyped
  imports LinkSubstRanges TypeSubstModuleEnv TyEnvExtension CoreModuleTypecheck
begin

(* The whole-program "linking preserves well-typedness" theorem:

     link_modules as = Inr a,  core_module_well_typed a,
     link_modules bs = Inr b,  core_module_well_typed b,
     link_modules ms = Inr m,  set ms = set as \<union> set bs,
     \<forall>x \<in> set ms. module_ghost_subsets_ok x
     \<Longrightarrow> core_module_well_typed m

   The core_module_invariant conjunct of core_module_well_typed m follows
   from link_modules_idempotent_subst, link_modules_capture_avoiding, the
   linked result's field shape, and core_module_invariant_intro; the
   typesubst_well_kinded conjunct is link_modules_typesubst_well_kinded; the
   work in this file is normalized_module_well_typed (normalize_module m)
   (this file also proves link_modules_invariant: linking preserves the
   standing invariant when every input satisfies it). The proof route runs
   every A-originating definition through a MIXED intermediate environment
   link_mid_env a b m (and B-originating definitions through the symmetric
   instantiation link_mid_env b a m):

     1. the definition typechecks in CM_TyEnv (normalize_module a)
        (from well-typedness of a);
     2. widen the type-variable axis to the union of both sides' type
        variables (the _irrelevant_tyvar lemmas);
     3. widen the declaration axis into link_mid_env a b m
        (core_term_type_tyenv_extends / core_statement_type_tyenv_extends);
     4. push the whole link's substitution through with the module-level
        substitution engine (core_term_type_subst_module_env /
        core_statement_type_subst_module_env), whose side conditions are
        module_env_subst_ok / module_env_subst_runtime_ok at the mid env
        (proved below from R3's typesubst_well_kinded transfer, the R2
        link_runtime_ok check, and link_modules_capture_avoiding);
     5. the substituted environment COLLAPSES onto
        CM_TyEnv (normalize_module m) (link_mid_env_collapse below), because
        the whole link's closure absorbs each sub-link's closure
        (link_modules_closure_absorb, R3), and the substituted definition is
        exactly the normalize_module m one for the same reason.

   The mid env cannot be avoided: the engine pins the datatype tables of
   source and target equal, so the declaration-axis extension must happen
   BEFORE the substitution - but tyenv_extends preserves entries verbatim, so
   it must happen while the entries still carry their own side's
   substitution. Hence: extend first, substitute second. *)


(* ========================================================================== *)
(* Projections of apply_subst_to_tyenv and normalize_module                   *)
(* ========================================================================== *)

lemma apply_subst_to_tyenv_simps [simp]:
  "TE_LocalVars (apply_subst_to_tyenv subst env) = TE_LocalVars env"
  "TE_GlobalVars (apply_subst_to_tyenv subst env)
     = fmmap (apply_subst subst) (TE_GlobalVars env)"
  "TE_GhostLocals (apply_subst_to_tyenv subst env) = TE_GhostLocals env"
  "TE_GhostGlobals (apply_subst_to_tyenv subst env) = TE_GhostGlobals env"
  "TE_ConstLocals (apply_subst_to_tyenv subst env) = TE_ConstLocals env"
  "TE_TypeVars (apply_subst_to_tyenv subst env) = TE_TypeVars env"
  "TE_RuntimeTypeVars (apply_subst_to_tyenv subst env) = TE_RuntimeTypeVars env"
  "TE_AbstractTypes (apply_subst_to_tyenv subst env) = TE_AbstractTypes env"
  "TE_ReturnType (apply_subst_to_tyenv subst env) = TE_ReturnType env"
  "TE_FunctionGhost (apply_subst_to_tyenv subst env) = TE_FunctionGhost env"
  "TE_ProofGoal (apply_subst_to_tyenv subst env) = TE_ProofGoal env"
  "TE_ProofTopLevel (apply_subst_to_tyenv subst env) = TE_ProofTopLevel env"
  "TE_Functions (apply_subst_to_tyenv subst env)
     = fmmap (apply_subst_to_funinfo subst) (TE_Functions env)"
  "TE_Datatypes (apply_subst_to_tyenv subst env) = TE_Datatypes env"
  "TE_DataCtors (apply_subst_to_tyenv subst env)
     = fmmap (apply_subst_to_datactor subst) (TE_DataCtors env)"
  "TE_DataCtorsByType (apply_subst_to_tyenv subst env) = TE_DataCtorsByType env"
  "TE_GhostDatatypes (apply_subst_to_tyenv subst env) = TE_GhostDatatypes env"
  by (simp_all add: apply_subst_to_tyenv_def)

lemma normalize_module_simps [simp]:
  "CM_TyEnv (normalize_module x) = apply_subst_to_tyenv (CM_TypeSubst x) (CM_TyEnv x)"
  "CM_GlobalVars (normalize_module x)
     = fmmap (apply_subst_to_term (CM_TypeSubst x)) (CM_GlobalVars x)"
  "CM_Functions (normalize_module x)
     = fmmap (\<lambda>f. f \<lparr> CF_Body := map_option (apply_subst_to_statement_list (CM_TypeSubst x))
                                             (CF_Body f) \<rparr>)
             (CM_Functions x)"
  by (simp_all add: normalize_module_def)


(* ========================================================================== *)
(* Small finite-map utilities                                                 *)
(* ========================================================================== *)

(* The A-preferring disjoint overlay used by link_mid_env: on keys of m1 the
   left map wins; elsewhere the right map answers. *)
lemma fmadd_drop_lookup:
  "fmlookup (m1 ++\<^sub>f fmdrop_fset (fmdom m1) m2) k
     = (if k |\<in>| fmdom m1 then fmlookup m1 k else fmlookup m2 k)"
proof (cases "k |\<in>| fmdom m1")
  case True
  then have "fmlookup (fmdrop_fset (fmdom m1) m2) k = None" by simp
  then show ?thesis using True by (simp add: fmlookup_dom_iff)
next
  case False
  then have "fmlookup m1 k = None" by (simp add: fmdom_notD)
  then show ?thesis using False by (simp add: fmdom_notD)
qed

lemma fmadd_drop_dom:
  "fmdom (m1 ++\<^sub>f fmdrop_fset (fmdom m1) m2) = fmdom m1 |\<union>| fmdom m2"
  by (rule fset_eqI) auto

lemma fmdom_fmmap:
  "fmdom (fmmap g m) = fmdom m"
  by (rule fset_eqI) (auto simp: fmlookup_dom_iff)

lemma fmmap_fmempty [simp]:
  "fmmap g fmempty = fmempty"
  by (rule fmap_ext) simp

(* fmmap through fmap_of_list. *)
lemma fmmap_fmap_of_list:
  "fmmap g (fmap_of_list xs) = fmap_of_list (map (\<lambda>(k, v). (k, g v)) xs)"
  by (rule fmap_ext) (simp add: fmlookup_of_list map_of_map)

(* Two members of a pairwise-disjoint projected family that both define a key
   are the same module. (Two occurrences of the same non-empty map value are
   also excluded: they would fail their own pairwise check.) *)
lemma fmdisjoint_list_unique_witness:
  assumes disj: "fmdisjoint_list (map f ms)"
      and z_in: "z \<in> set ms" and x_in: "x \<in> set ms"
      and kz: "k |\<in>| fmdom (f z)" and kx: "k |\<in>| fmdom (f x)"
  shows "z = x"
proof (rule ccontr)
  assume ne: "z \<noteq> x"
  obtain i where i: "i < length ms" "ms ! i = z"
    using z_in by (auto simp: in_set_conv_nth)
  obtain j where j: "j < length ms" "ms ! j = x"
    using x_in by (auto simp: in_set_conv_nth)
  have "i \<noteq> j" using ne i(2) j(2) by auto
  then have "fmdisjoint (map f ms ! i) (map f ms ! j)"
    using disj i(1) j(1) unfolding fmdisjoint_list_def by simp
  then have "fmdisjoint (f z) (f x)"
    using i j by simp
  then show False using kz kx fmdisjoint_not_both by fastforce
qed

(* Splitting an fset union over a list whose set splits. *)
lemma funion_list_split:
  assumes "set ms = set as \<union> set bs"
  shows "funion_list (map f ms) = funion_list (map f as) |\<union>| funion_list (map f bs)"
proof (rule fset_eqI)
  fix x
  have mem: "x |\<in>| funion_list (map f zs) \<longleftrightarrow> (\<exists>y \<in> set zs. x |\<in>| f y)" for zs
    by (auto simp: funion_list_member)
  show "x |\<in>| funion_list (map f ms)
          \<longleftrightarrow> x |\<in>| funion_list (map f as) |\<union>| funion_list (map f bs)"
    using assms by (auto simp: mem)
qed

(* Subtracting a larger domain factors through subtracting a smaller one. *)
lemma fminus_absorb_subset:
  assumes "D1 |\<subseteq>| D2"
  shows "(A |-| D1) |-| D2 = A |-| D2"
  by (rule fset_eqI) (use assms in auto)


(* ========================================================================== *)
(* is_constant_term is invariant under type substitution                      *)
(*                                                                            *)
(* Substitution rewrites types embedded in a term but introduces no           *)
(* CoreTm_FunctionCall, so the compile-time-constant check is unchanged.      *)
(* ========================================================================== *)

lemma is_constant_term_apply_subst [simp]:
  "is_constant_term (apply_subst_to_term subst tm) = is_constant_term tm"
proof (induction tm)
  case (CoreTm_LitArray elemTy tms)
  then show ?case by (fastforce simp: list_all_iff)
next
  case (CoreTm_Record flds)
  have "\<And>nm t. (nm, t) \<in> set flds \<Longrightarrow>
          is_constant_term (apply_subst_to_term subst t) = is_constant_term t"
    using CoreTm_Record.IH by auto
  then show ?case by (fastforce simp: list_all_iff)
next
  case (CoreTm_ArrayProj arr idxs)
  then show ?case by (fastforce simp: list_all_iff)
next
  case (CoreTm_Match scrut arms)
  have "\<And>p t. (p, t) \<in> set arms \<Longrightarrow>
          is_constant_term (apply_subst_to_term subst t) = is_constant_term t"
    using CoreTm_Match.IH by auto
  then show ?case using CoreTm_Match.IH by (fastforce simp: list_all_iff)
qed simp_all


(* ========================================================================== *)
(* Substitutions that agree on all types act identically on terms and         *)
(* statements                                                                 *)
(* ========================================================================== *)

lemma apply_subst_to_term_cong_subst:
  assumes eq: "\<And>ty. apply_subst s1 ty = apply_subst s2 ty"
  shows "apply_subst_to_term s1 tm = apply_subst_to_term s2 tm"
proof (induction tm)
  case (CoreTm_LitArray elemTy tms)
  then show ?case by (simp add: eq cong: map_cong)
next
  case (CoreTm_FunctionCall fnName tyArgs args)
  then show ?case by (simp add: eq cong: map_cong)
next
  case (CoreTm_Record flds)
  have "map (\<lambda>(name, tm). (name, apply_subst_to_term s1 tm)) flds
      = map (\<lambda>(name, tm). (name, apply_subst_to_term s2 tm)) flds"
    by (rule map_cong[OF refl]) (use CoreTm_Record.IH in \<open>auto split: prod.splits\<close>)
  then show ?case by simp
next
  case (CoreTm_ArrayProj arr idxs)
  then show ?case by (simp add: cong: map_cong)
next
  case (CoreTm_Match scrut arms)
  have "map (\<lambda>(pat, tm). (pat, apply_subst_to_term s1 tm)) arms
      = map (\<lambda>(pat, tm). (pat, apply_subst_to_term s2 tm)) arms"
    by (rule map_cong[OF refl]) (use CoreTm_Match.IH in \<open>auto split: prod.splits\<close>)
  then show ?case using CoreTm_Match.IH by simp
qed (simp_all add: eq)

lemma apply_subst_to_statement_cong_subst:
  "(\<And>ty. apply_subst s1 ty = apply_subst s2 ty) \<Longrightarrow>
   apply_subst_to_statement s1 stmt = apply_subst_to_statement s2 stmt"
and apply_subst_to_statement_list_cong_subst:
  "(\<And>ty. apply_subst s1 ty = apply_subst s2 ty) \<Longrightarrow>
   apply_subst_to_statement_list s1 stmts = apply_subst_to_statement_list s2 stmts"
proof (induction s1 stmt and s1 stmts
       rule: apply_subst_to_statement_apply_subst_to_statement_list.induct)
  case (1 s1 ghost varName vr ty initTm)
  show ?case
    by (simp add: "1.prems" apply_subst_to_term_cong_subst[OF "1.prems"])
next
  case (2 s1 ghost varName ty castOpt fnName tyArgs argTms)
  show ?case
    by (simp add: "2.prems" apply_subst_to_term_cong_subst[OF "2.prems"]
             cong: map_cong map_option_cong)
next
  case (3 s1 varName ty)
  show ?case by (simp add: "3.prems")
next
  case (4 s1 varName ty condTm)
  show ?case
    by (simp add: "4.prems" apply_subst_to_term_cong_subst[OF "4.prems"])
next
  case (5 s1 witnessTm)
  show ?case by (simp add: apply_subst_to_term_cong_subst[OF "5.prems"])
next
  case (6 s1 ghost lhsTm rhsTm)
  show ?case by (simp add: apply_subst_to_term_cong_subst[OF "6.prems"])
next
  case (7 s1 ghost lhsTm castOpt fnName tyArgs argTms)
  show ?case
    by (simp add: "7.prems" apply_subst_to_term_cong_subst[OF "7.prems"]
             cong: map_cong map_option_cong)
next
  case (8 s1 ghost lhsTm rhsTm)
  show ?case by (simp add: apply_subst_to_term_cong_subst[OF "8.prems"])
next
  case (9 s1 tm)
  show ?case by (simp add: apply_subst_to_term_cong_subst[OF "9.prems"])
next
  case (10 s1 condOpt proofBody)
  show ?case
    by (simp add: "10.IH"[OF "10.prems"] apply_subst_to_term_cong_subst[OF "10.prems"]
             cong: map_option_cong)
next
  case (11 s1 tm)
  show ?case by (simp add: apply_subst_to_term_cong_subst[OF "11.prems"])
next
  case (12 s1 ghost condTm invars decrTm body)
  show ?case
    by (simp add: "12.IH"[OF "12.prems"] apply_subst_to_term_cong_subst[OF "12.prems"]
             cong: map_cong)
next
  case (13 s1 ghost scrut arms)
  have "map (\<lambda>(pat, body). (pat, apply_subst_to_statement_list s1 body)) arms
      = map (\<lambda>(pat, body). (pat, apply_subst_to_statement_list s2 body)) arms"
    by (rule map_cong[OF refl])
       (use "13.IH" "13.prems" in \<open>auto split: prod.splits\<close>)
  then show ?case
    by (simp add: apply_subst_to_term_cong_subst[OF "13.prems"])
next
  case (14 s1 sh name)
  show ?case by simp
next
  case (15 s1 body)
  show ?case by (simp add: "15.IH"[OF "15.prems"])
next
  case (16 s1)
  show ?case by simp
next
  case (17 s1 stmt stmts)
  show ?case by (simp add: "17.IH"[OF "17.prems"])
qed


(* ========================================================================== *)
(* Absorption identities lifted to terms, statements, funinfos and ctors      *)
(*                                                                            *)
(* Given the type-level absorption apply_subst \<tau> \<circ> apply_subst \<sigma> =              *)
(* apply_subst \<tau> (link_modules_closure_absorb, LinkSubstRanges.thy), the same  *)
(* identity holds for every syntactic class substitution touches.             *)
(* ========================================================================== *)

lemma subst_absorb_term:
  assumes abs: "\<And>ty. apply_subst \<tau> (apply_subst \<sigma> ty) = apply_subst \<tau> ty"
  shows "apply_subst_to_term \<tau> (apply_subst_to_term \<sigma> tm) = apply_subst_to_term \<tau> tm"
proof -
  have eq: "\<And>ty. apply_subst (compose_subst \<tau> \<sigma>) ty = apply_subst \<tau> ty"
    by (simp add: compose_subst_correct abs)
  show ?thesis
    unfolding apply_subst_to_term_compose
    by (rule apply_subst_to_term_cong_subst[OF eq])
qed

lemma subst_absorb_statement_list:
  assumes abs: "\<And>ty. apply_subst \<tau> (apply_subst \<sigma> ty) = apply_subst \<tau> ty"
  shows "apply_subst_to_statement_list \<tau> (apply_subst_to_statement_list \<sigma> stmts)
           = apply_subst_to_statement_list \<tau> stmts"
proof -
  have eq: "\<And>ty. apply_subst (compose_subst \<tau> \<sigma>) ty = apply_subst \<tau> ty"
    by (simp add: compose_subst_correct abs)
  show ?thesis
    unfolding apply_subst_to_statement_list_compose
    by (rule apply_subst_to_statement_list_cong_subst[OF eq])
qed

lemma subst_absorb_funinfo:
  assumes abs: "\<And>ty. apply_subst \<tau> (apply_subst \<sigma> ty) = apply_subst \<tau> ty"
  shows "apply_subst_to_funinfo \<tau> (apply_subst_to_funinfo \<sigma> info)
           = apply_subst_to_funinfo \<tau> info"
proof -
  have "map (\<lambda>(ty, vr). (apply_subst \<tau> ty, vr))
            (map (\<lambda>(ty, vr). (apply_subst \<sigma> ty, vr)) (FI_TmArgs info))
      = map (\<lambda>(ty, vr). (apply_subst \<tau> ty, vr)) (FI_TmArgs info)"
    unfolding map_map
    by (rule map_cong[OF refl]) (auto simp: abs split: prod.splits)
  then show ?thesis
    unfolding apply_subst_to_funinfo_def by (simp add: abs)
qed

lemma subst_absorb_datactor:
  assumes abs: "\<And>ty. apply_subst \<tau> (apply_subst \<sigma> ty) = apply_subst \<tau> ty"
  shows "apply_subst_to_datactor \<tau> (apply_subst_to_datactor \<sigma> entry)
           = apply_subst_to_datactor \<tau> entry"
  by (cases entry) (simp add: abs)


(* ========================================================================== *)
(* Monotone transfer lemmas for is_well_kinded and is_runtime_type            *)
(*                                                                            *)
(* The tyvar-and-table-growth analogues of is_well_kinded_transfer /          *)
(* is_runtime_type_transfer, which demand table EQUALITY (linking breaks it). *)
(* ========================================================================== *)

(* Well-kindedness survives growing TE_TypeVars and the datatype table.
   (Composition of R3's is_well_kinded_transfer_mono with the fact that a
   well-kinded type's tyvars sit inside the source env's TE_TypeVars.) *)
lemma is_well_kinded_mono:
  assumes wk: "is_well_kinded env1 ty"
      and tv: "fset (TE_TypeVars env1) \<subseteq> fset (TE_TypeVars env2)"
      and dt: "\<And>n v. fmlookup (TE_Datatypes env1) n = Some v
                 \<Longrightarrow> fmlookup (TE_Datatypes env2) n = Some v"
  shows "is_well_kinded env2 ty"
proof -
  have "type_tyvars ty \<subseteq> fset (TE_TypeVars env2)"
    using is_well_kinded_type_tyvars_subset[OF wk] tv by blast
  then show ?thesis using is_well_kinded_transfer_mono[OF wk _ dt] by blast
qed

(* Runtime-ness survives growing TE_RuntimeTypeVars and the datatype table,
   for WELL-KINDED types, provided the ghost-datatype marker is unchanged on
   the source env's datatype domain (well-kindedness pins every datatype name
   of the type into that domain). Mirrors is_runtime_type_tyenv_extends. *)
lemma is_runtime_type_transfer_mono:
  assumes wk: "is_well_kinded env1 ty"
      and rt: "is_runtime_type env1 ty"
      and rtv: "fset (TE_RuntimeTypeVars env1) \<subseteq> fset (TE_RuntimeTypeVars env2)"
      and gd: "\<And>n. n |\<in>| fmdom (TE_Datatypes env1) \<Longrightarrow>
                 (n |\<in>| TE_GhostDatatypes env2 \<longleftrightarrow> n |\<in>| TE_GhostDatatypes env1)"
  shows "is_runtime_type env2 ty"
  using wk rt
proof (induction ty)
  case (CoreTy_Datatype name argTypes)
  from CoreTy_Datatype.prems(1) obtain numTyVars where
    dt: "fmlookup (TE_Datatypes env1) name = Some numTyVars" and
    args_wk: "list_all (is_well_kinded env1) argTypes"
    by (auto split: option.splits)
  from CoreTy_Datatype.prems(2) have
    ng: "name |\<notin>| TE_GhostDatatypes env1" and
    args_rt: "list_all (is_runtime_type env1) argTypes"
    by auto
  have "name |\<in>| fmdom (TE_Datatypes env1)"
    using dt by (simp add: fmdomI)
  then have ng': "name |\<notin>| TE_GhostDatatypes env2"
    using gd ng by blast
  have args_rt': "list_all (is_runtime_type env2) argTypes"
    using CoreTy_Datatype.IH args_wk args_rt by (simp add: list_all_iff)
  show ?case using ng' args_rt' by simp
next
  case (CoreTy_Record flds)
  have each: "\<And>nm t. (nm, t) \<in> set flds \<Longrightarrow> is_runtime_type env2 t"
  proof -
    fix nm t assume mem: "(nm, t) \<in> set flds"
    from mem CoreTy_Record.prems(1) have "is_well_kinded env1 t"
      by (auto simp: list_all_iff)
    moreover from mem CoreTy_Record.prems(2) have "is_runtime_type env1 t"
      by (auto simp: list_all_iff)
    ultimately show "is_runtime_type env2 t"
      using CoreTy_Record.IH mem by auto
  qed
  then show ?case by (auto simp: list_all_iff)
next
  case (CoreTy_Array elemTy dims)
  then show ?case by auto
next
  case (CoreTy_Var n)
  then show ?case using rtv by auto
qed simp_all

(* Pure runtime-tyvar growth (tables and markers unchanged) needs no
   well-kindedness: a runtime type's tyvars all sit in the source RTV set. *)
lemma is_runtime_type_mono_rtv:
  assumes rt: "is_runtime_type env1 ty"
      and rtv: "fset (TE_RuntimeTypeVars env1) \<subseteq> fset (TE_RuntimeTypeVars env2)"
      and gd: "TE_GhostDatatypes env2 = TE_GhostDatatypes env1"
  shows "is_runtime_type env2 ty"
proof -
  have "type_tyvars ty \<subseteq> fset (TE_RuntimeTypeVars env2)"
    using is_runtime_type_tyvars_subset[OF rt] rtv by blast
  then show ?thesis using is_runtime_type_transfer[OF rt _ gd] by blast
qed


(* ========================================================================== *)
(* Plumbing: fields and checks of a successful link                           *)
(* ========================================================================== *)

(* Every field of a successful link's result, in terms of the input list and
   the result's own CM_TypeSubst. (Conclusions are numbered; downstream
   references use link_modules_result_fields(n) with this order.) *)
lemma link_modules_result_fields:
  assumes ok: "link_modules ms = Inr m"
  shows "TE_LocalVars (CM_TyEnv m) = fmempty"                                       \<comment> \<open>(1)\<close>
    and "TE_GlobalVars (CM_TyEnv m)
           = fmlist_union (map (\<lambda>x. TE_GlobalVars (CM_TyEnv x)) ms)"               \<comment> \<open>(2)\<close>
    and "TE_GhostLocals (CM_TyEnv m) = {||}"                                        \<comment> \<open>(3)\<close>
    and "TE_GhostGlobals (CM_TyEnv m)
           = funion_list (map (\<lambda>x. TE_GhostGlobals (CM_TyEnv x)) ms)"              \<comment> \<open>(4)\<close>
    and "TE_ConstLocals (CM_TyEnv m) = {||}"                                        \<comment> \<open>(5)\<close>
    and "TE_TypeVars (CM_TyEnv m)
           = funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) ms)
             |-| fmdom (CM_TypeSubst m)"                                            \<comment> \<open>(6)\<close>
    and "TE_RuntimeTypeVars (CM_TyEnv m)
           = funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) ms)
             |-| fmdom (CM_TypeSubst m)"                                            \<comment> \<open>(7)\<close>
    and "TE_AbstractTypes (CM_TyEnv m)
           = funion_list (map (\<lambda>x. TE_AbstractTypes (CM_TyEnv x)) ms)
             |-| fmdom (CM_TypeSubst m)"                                            \<comment> \<open>(8)\<close>
    and "TE_ReturnType (CM_TyEnv m) = CoreTy_Record []"                             \<comment> \<open>(9)\<close>
    and "TE_FunctionGhost (CM_TyEnv m) = NotGhost"                                  \<comment> \<open>(10)\<close>
    and "TE_ProofGoal (CM_TyEnv m) = None"                                          \<comment> \<open>(11)\<close>
    and "TE_ProofTopLevel (CM_TyEnv m) = False"                                     \<comment> \<open>(12)\<close>
    and "TE_Functions (CM_TyEnv m)
           = fmlist_union (map (\<lambda>x. TE_Functions (CM_TyEnv x)) ms)"                \<comment> \<open>(13)\<close>
    and "TE_Datatypes (CM_TyEnv m)
           = fmlist_union (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) ms)"                \<comment> \<open>(14)\<close>
    and "TE_DataCtors (CM_TyEnv m)
           = fmlist_union (map (\<lambda>x. TE_DataCtors (CM_TyEnv x)) ms)"                \<comment> \<open>(15)\<close>
    and "TE_DataCtorsByType (CM_TyEnv m)
           = fmlist_union (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) ms)"          \<comment> \<open>(16)\<close>
    and "TE_GhostDatatypes (CM_TyEnv m)
           = funion_list (map (\<lambda>x. TE_GhostDatatypes (CM_TyEnv x)) ms)"            \<comment> \<open>(17)\<close>
    and "CM_GlobalVars m = fmlist_union (map CM_GlobalVars ms)"                     \<comment> \<open>(18)\<close>
    and "CM_Functions m = fmlist_union (map CM_Functions ms)"                       \<comment> \<open>(19)\<close>
proof -
  obtain \<sigma> where meq: "m = link_result ms \<sigma>"
    using ok link_modules_Inr_iff by blast
  show "TE_LocalVars (CM_TyEnv m) = fmempty"
    and "TE_GlobalVars (CM_TyEnv m)
           = fmlist_union (map (\<lambda>x. TE_GlobalVars (CM_TyEnv x)) ms)"
    and "TE_GhostLocals (CM_TyEnv m) = {||}"
    and "TE_GhostGlobals (CM_TyEnv m)
           = funion_list (map (\<lambda>x. TE_GhostGlobals (CM_TyEnv x)) ms)"
    and "TE_ConstLocals (CM_TyEnv m) = {||}"
    and "TE_TypeVars (CM_TyEnv m)
           = funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) ms)
             |-| fmdom (CM_TypeSubst m)"
    and "TE_RuntimeTypeVars (CM_TyEnv m)
           = funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) ms)
             |-| fmdom (CM_TypeSubst m)"
    and "TE_AbstractTypes (CM_TyEnv m)
           = funion_list (map (\<lambda>x. TE_AbstractTypes (CM_TyEnv x)) ms)
             |-| fmdom (CM_TypeSubst m)"
    and "TE_ReturnType (CM_TyEnv m) = CoreTy_Record []"
    and "TE_FunctionGhost (CM_TyEnv m) = NotGhost"
    and "TE_ProofGoal (CM_TyEnv m) = None"
    and "TE_ProofTopLevel (CM_TyEnv m) = False"
    and "TE_Functions (CM_TyEnv m)
           = fmlist_union (map (\<lambda>x. TE_Functions (CM_TyEnv x)) ms)"
    and "TE_Datatypes (CM_TyEnv m)
           = fmlist_union (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) ms)"
    and "TE_DataCtors (CM_TyEnv m)
           = fmlist_union (map (\<lambda>x. TE_DataCtors (CM_TyEnv x)) ms)"
    and "TE_DataCtorsByType (CM_TyEnv m)
           = fmlist_union (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) ms)"
    and "TE_GhostDatatypes (CM_TyEnv m)
           = funion_list (map (\<lambda>x. TE_GhostDatatypes (CM_TyEnv x)) ms)"
    and "CM_GlobalVars m = fmlist_union (map CM_GlobalVars ms)"
    and "CM_Functions m = fmlist_union (map CM_Functions ms)"
    unfolding meq link_result_def by simp_all
qed

(* The checks and closure facts of a successful link, phrased against the
   result's own CM_TypeSubst. Reference order: (1) link_fields_disjoint,
   (2) fmdisjoint_list of the substitution family, (3) acyclicity of the raw
   union, (4) closure, (5) link_capture_ok, (6) link_runtime_ok. *)
lemma link_modules_success_facts:
  assumes ok: "link_modules ms = Inr m"
  shows "link_fields_disjoint ms"
    and "fmdisjoint_list (map CM_TypeSubst ms)"
    and "acyclic_subst_deps (fmlist_union (map CM_TypeSubst ms))"
    and "is_subst_closure (fmlist_union (map CM_TypeSubst ms)) (CM_TypeSubst m)"
    and "link_capture_ok ms"
    and "link_runtime_ok ms (CM_TypeSubst m)"
proof -
  obtain \<sigma> where
    fdisj: "link_fields_disjoint ms" and
    cap: "link_capture_ok ms" and
    sdisj: "fmdisjoint_list (map CM_TypeSubst ms)" and
    acyc: "acyclic_subst_deps (fmlist_union (map CM_TypeSubst ms))" and
    clos: "is_subst_closure (fmlist_union (map CM_TypeSubst ms)) \<sigma>" and
    rok: "link_runtime_ok ms \<sigma>" and
    meq: "m = link_result ms \<sigma>"
    using ok link_modules_Inr_iff_closure by blast
  have \<sigma>eq: "CM_TypeSubst m = \<sigma>"
    using meq by (simp add: link_result_def)
  show "link_fields_disjoint ms" using fdisj .
  show "fmdisjoint_list (map CM_TypeSubst ms)" using sdisj .
  show "acyclic_subst_deps (fmlist_union (map CM_TypeSubst ms))" using acyc .
  show "is_subst_closure (fmlist_union (map CM_TypeSubst ms)) (CM_TypeSubst m)"
    using clos \<sigma>eq by simp
  show "link_capture_ok ms" using cap .
  show "link_runtime_ok ms (CM_TypeSubst m)" using rok \<sigma>eq by simp
qed

(* The R2 runtime-resolution check, massaged into consumable form: a resolved
   name that was a runtime abstract type of SOME input resolves to a runtime
   type in the linked env. *)
lemma link_modules_runtime_resolution:
  assumes ok: "link_modules ms = Inr m"
      and n_rtv: "n |\<in>| funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) ms)"
      and lk: "fmlookup (CM_TypeSubst m) n = Some ty"
  shows "is_runtime_type (CM_TyEnv m) ty"
proof -
  obtain \<sigma> where rok: "link_runtime_ok ms \<sigma>" and meq: "m = link_result ms \<sigma>"
    using ok link_modules_Inr_iff by blast
  have \<sigma>eq: "CM_TypeSubst m = \<sigma>"
    using meq by (simp add: link_result_def)
  have n_dom: "n |\<in>| fmdom \<sigma>"
    using lk \<sigma>eq by (auto intro: fmdomI)
  have "is_runtime_type (CM_TyEnv (link_result ms \<sigma>)) (the (fmlookup \<sigma> n))"
    using rok n_dom n_rtv unfolding link_runtime_ok_def by auto
  then show ?thesis using meq \<sigma>eq lk by simp
qed

(* Linking preserves the standing module invariant: if every input satisfies
   core_module_invariant, so does a successful link's result. Idempotence and
   capture-avoidance are the existing link_modules_idempotent_subst /
   link_modules_capture_avoiding; the substitution-domain/TE_TypeVars
   disjointness and the inert scope fields are immediate from link_result's
   construction; the ghost-marker, tyvar-subset and abstract-types-equality
   clauses are inherited pointwise from the inputs (these are the conjuncts
   that genuinely need the per-input hypothesis - the linker unions the ghost
   fsets and tyvar fsets with no check of its own). *)
theorem link_modules_invariant:
  assumes ok: "link_modules ms = Inr m"
      and inv: "\<forall>x \<in> set ms. core_module_invariant x"
  shows "core_module_invariant m"
proof -
  note fM = link_modules_result_fields[OF ok]
  have idem: "idempotent_subst (CM_TypeSubst m)"
    using link_modules_idempotent_subst[OF ok] .
  have cap: "capture_avoiding m"
    using link_modules_capture_avoiding[OF ok] .
  have tv: "fmdom (CM_TypeSubst m) |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}"
    unfolding fM(6) by auto

  \<comment> \<open>Ghost markers: every marker comes from some input, which (by its own
     invariant) declares the name in the corresponding parent map; the union
     of the parent maps then contains it.\<close>
  have gg: "TE_GhostGlobals (CM_TyEnv m) |\<subseteq>| fmdom (TE_GlobalVars (CM_TyEnv m))"
  proof
    fix n assume "n |\<in>| TE_GhostGlobals (CM_TyEnv m)"
    then have "\<exists>s \<in> set (map (\<lambda>x. TE_GhostGlobals (CM_TyEnv x)) ms). n |\<in>| s"
      unfolding fM(4) using funion_list_member by fastforce
    then obtain x where x_in: "x \<in> set ms"
                    and n_gg: "n |\<in>| TE_GhostGlobals (CM_TyEnv x)"
      by auto
    have "n |\<in>| fmdom (TE_GlobalVars (CM_TyEnv x))"
      using inv x_in n_gg
      unfolding core_module_invariant_def module_ghost_subsets_ok_def
      by (blast dest: fsubsetD)
    then obtain ty where x_lk: "fmlookup (TE_GlobalVars (CM_TyEnv x)) n = Some ty"
      by (auto simp: fmlookup_dom_iff)
    have gdisj: "fmdisjoint_list (map (\<lambda>x. TE_GlobalVars (CM_TyEnv x)) ms)"
      using link_modules_success_facts(1)[OF ok]
      unfolding link_fields_disjoint_def by blast
    have "fmlookup (TE_GlobalVars (CM_TyEnv m)) n = Some ty"
      unfolding fM(2) using fmlist_union_lookup[OF gdisj] x_in x_lk by fastforce
    then show "n |\<in>| fmdom (TE_GlobalVars (CM_TyEnv m))"
      by (rule fmdomI)
  qed
  have gd: "TE_GhostDatatypes (CM_TyEnv m) |\<subseteq>| fmdom (TE_Datatypes (CM_TyEnv m))"
  proof
    fix n assume "n |\<in>| TE_GhostDatatypes (CM_TyEnv m)"
    then have "\<exists>s \<in> set (map (\<lambda>x. TE_GhostDatatypes (CM_TyEnv x)) ms). n |\<in>| s"
      unfolding fM(17) using funion_list_member by fastforce
    then obtain x where x_in: "x \<in> set ms"
                    and n_gd: "n |\<in>| TE_GhostDatatypes (CM_TyEnv x)"
      by auto
    have "n |\<in>| fmdom (TE_Datatypes (CM_TyEnv x))"
      using inv x_in n_gd
      unfolding core_module_invariant_def module_ghost_subsets_ok_def
      by (blast dest: fsubsetD)
    then obtain d where x_lk: "fmlookup (TE_Datatypes (CM_TyEnv x)) n = Some d"
      by (auto simp: fmlookup_dom_iff)
    have ddisj: "fmdisjoint_list (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) ms)"
      using link_modules_success_facts(1)[OF ok]
      unfolding link_fields_disjoint_def by blast
    have "fmlookup (TE_Datatypes (CM_TyEnv m)) n = Some d"
      unfolding fM(14) using fmlist_union_lookup[OF ddisj] x_in x_lk by fastforce
    then show "n |\<in>| fmdom (TE_Datatypes (CM_TyEnv m))"
      by (rule fmdomI)
  qed
  have ghost: "module_ghost_subsets_ok m"
    unfolding module_ghost_subsets_ok_def using gg gd by blast

  \<comment> \<open>Tyvar subsets: pointwise from the inputs; the same domain is subtracted
     on both sides.\<close>
  have rtv: "TE_RuntimeTypeVars (CM_TyEnv m) |\<subseteq>| TE_TypeVars (CM_TyEnv m)"
  proof
    fix n assume n_in: "n |\<in>| TE_RuntimeTypeVars (CM_TyEnv m)"
    have "\<exists>s \<in> set (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) ms). n |\<in>| s"
      using n_in unfolding fM(7) using funion_list_member by (metis fminus_iff)
    then obtain x where x_in: "x \<in> set ms"
                    and n_rtv: "n |\<in>| TE_RuntimeTypeVars (CM_TyEnv x)"
      by auto
    have "n |\<in>| TE_TypeVars (CM_TyEnv x)"
      using inv x_in n_rtv
      unfolding core_module_invariant_def by (blast dest: fsubsetD)
    then have "n |\<in>| funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) ms)"
      using x_in funion_list_member by fastforce
    moreover have "n |\<notin>| fmdom (CM_TypeSubst m)"
      using n_in unfolding fM(7) by auto
    ultimately show "n |\<in>| TE_TypeVars (CM_TyEnv m)"
      unfolding fM(6) by auto
  qed
  \<comment> \<open>Abstract types: each input has TE_AbstractTypes = TE_TypeVars, and the
     linker builds both fields as the same union-minus-domain, so the
     equality carries over by congruence.\<close>
  have abs_tv: "TE_AbstractTypes (CM_TyEnv m) = TE_TypeVars (CM_TyEnv m)"
  proof -
    have "map (\<lambda>x. TE_AbstractTypes (CM_TyEnv x)) ms
            = map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) ms"
      using inv
      unfolding core_module_invariant_def tyenv_module_scope_def
      by (intro list.map_cong0) blast
    then show ?thesis
      unfolding fM(6) fM(8) by metis
  qed

  have scope: "tyenv_module_scope (CM_TyEnv m)"
    unfolding tyenv_module_scope_def
    by (simp add: fM(1) fM(3) fM(5) fM(9) fM(10) fM(11) fM(12) abs_tv)

  show ?thesis
    unfolding core_module_invariant_def
    using idem cap ghost tv rtv scope by blast
qed

(* A sub-link resolves fewer names than the whole link. *)
lemma link_modules_subst_dom_mono:
  assumes linkA: "link_modules as = Inr a"
      and linkM: "link_modules ms = Inr m"
      and sub: "set as \<subseteq> set ms"
  shows "fmdom (CM_TypeSubst a) |\<subseteq>| fmdom (CM_TypeSubst m)"
proof
  fix k assume "k |\<in>| fmdom (CM_TypeSubst a)"
  then have "k |\<in>| fmdom (fmlist_union (map CM_TypeSubst as))"
    using link_modules_success_facts(4)[OF linkA]
    unfolding is_subst_closure_def by simp
  then obtain v where "fmlookup (fmlist_union (map CM_TypeSubst as)) k = Some v"
    by (auto simp: fmlookup_dom_iff)
  then have "fmlookup (fmlist_union (map CM_TypeSubst ms)) k = Some v"
    using fmlist_union_sublist_lookup[OF link_modules_success_facts(2)[OF linkM]
            link_modules_success_facts(2)[OF linkA]] sub by auto
  then have "k |\<in>| fmdom (fmlist_union (map CM_TypeSubst ms))"
    by (auto intro: fmdomI)
  then show "k |\<in>| fmdom (CM_TypeSubst m)"
    using link_modules_success_facts(4)[OF linkM]
    unfolding is_subst_closure_def by simp
qed

(* Each declaration/definition family of a sub-link is a submap of the whole
   link's. Reference order: (1) TE_GlobalVars, (2) TE_Functions,
   (3) TE_Datatypes, (4) TE_DataCtors, (5) TE_DataCtorsByType,
   (6) CM_GlobalVars, (7) CM_Functions. *)
lemma link_modules_decl_submaps:
  assumes linkA: "link_modules as = Inr a"
      and linkM: "link_modules ms = Inr m"
      and sub: "set as \<subseteq> set ms"
  shows "fmlookup (TE_GlobalVars (CM_TyEnv a)) k = Some v
           \<Longrightarrow> fmlookup (TE_GlobalVars (CM_TyEnv m)) k = Some v"
    and "fmlookup (TE_Functions (CM_TyEnv a)) k2 = Some v2
           \<Longrightarrow> fmlookup (TE_Functions (CM_TyEnv m)) k2 = Some v2"
    and "fmlookup (TE_Datatypes (CM_TyEnv a)) k3 = Some v3
           \<Longrightarrow> fmlookup (TE_Datatypes (CM_TyEnv m)) k3 = Some v3"
    and "fmlookup (TE_DataCtors (CM_TyEnv a)) k4 = Some v4
           \<Longrightarrow> fmlookup (TE_DataCtors (CM_TyEnv m)) k4 = Some v4"
    and "fmlookup (TE_DataCtorsByType (CM_TyEnv a)) k5 = Some v5
           \<Longrightarrow> fmlookup (TE_DataCtorsByType (CM_TyEnv m)) k5 = Some v5"
    and "fmlookup (CM_GlobalVars a) k6 = Some v6
           \<Longrightarrow> fmlookup (CM_GlobalVars m) k6 = Some v6"
    and "fmlookup (CM_Functions a) k7 = Some v7
           \<Longrightarrow> fmlookup (CM_Functions m) k7 = Some v7"
proof -
  note fA = link_modules_result_fields[OF linkA]
  note fM = link_modules_result_fields[OF linkM]
  have dA: "link_fields_disjoint as" and dM: "link_fields_disjoint ms"
    using link_modules_success_facts(1)[OF linkA]
          link_modules_success_facts(1)[OF linkM] by blast+
  \<comment> \<open>One generic step per family.\<close>
  have step: "fmlookup (fmlist_union (map f as)) k0 = Some v0
                \<Longrightarrow> fmdisjoint_list (map f as)
                \<Longrightarrow> fmdisjoint_list (map f ms)
                \<Longrightarrow> fmlookup (fmlist_union (map f ms)) k0 = Some v0"
    for f :: "CoreModule \<Rightarrow> ('x :: type, 'y :: type) fmap" and k0 v0
  proof -
    assume l: "fmlookup (fmlist_union (map f as)) k0 = Some v0"
       and da: "fmdisjoint_list (map f as)" and dm: "fmdisjoint_list (map f ms)"
    have "set (map f as) \<subseteq> set (map f ms)" using sub by auto
    then show "fmlookup (fmlist_union (map f ms)) k0 = Some v0"
      using fmlist_union_sublist_lookup[OF dm da _ l] by blast
  qed
  show "fmlookup (TE_GlobalVars (CM_TyEnv a)) k = Some v
          \<Longrightarrow> fmlookup (TE_GlobalVars (CM_TyEnv m)) k = Some v"
    unfolding fA(2) fM(2)
    using step dA dM unfolding link_fields_disjoint_def by fastforce
  show "fmlookup (TE_Functions (CM_TyEnv a)) k2 = Some v2
          \<Longrightarrow> fmlookup (TE_Functions (CM_TyEnv m)) k2 = Some v2"
    unfolding fA(13) fM(13)
    using step dA dM unfolding link_fields_disjoint_def by fastforce
  show "fmlookup (TE_Datatypes (CM_TyEnv a)) k3 = Some v3
          \<Longrightarrow> fmlookup (TE_Datatypes (CM_TyEnv m)) k3 = Some v3"
    unfolding fA(14) fM(14)
    using step dA dM unfolding link_fields_disjoint_def by fastforce
  show "fmlookup (TE_DataCtors (CM_TyEnv a)) k4 = Some v4
          \<Longrightarrow> fmlookup (TE_DataCtors (CM_TyEnv m)) k4 = Some v4"
    unfolding fA(15) fM(15)
    using step dA dM unfolding link_fields_disjoint_def by fastforce
  show "fmlookup (TE_DataCtorsByType (CM_TyEnv a)) k5 = Some v5
          \<Longrightarrow> fmlookup (TE_DataCtorsByType (CM_TyEnv m)) k5 = Some v5"
    unfolding fA(16) fM(16)
    using step dA dM unfolding link_fields_disjoint_def by fastforce
  show "fmlookup (CM_GlobalVars a) k6 = Some v6
          \<Longrightarrow> fmlookup (CM_GlobalVars m) k6 = Some v6"
    unfolding fA(18) fM(18)
    using step dA dM unfolding link_fields_disjoint_def by fastforce
  show "fmlookup (CM_Functions a) k7 = Some v7
          \<Longrightarrow> fmlookup (CM_Functions m) k7 = Some v7"
    unfolding fA(19) fM(19)
    using step dA dM unfolding link_fields_disjoint_def by fastforce
qed


(* ========================================================================== *)
(* Ghost-marker agreement between a sub-link and the whole link               *)
(*                                                                            *)
(* On a name the sub-link DECLARES, the whole link's ghost marker agrees with *)
(* the sub-link's. This is where module_ghost_subsets_ok earns its keep: it   *)
(* pins every marker to the (unique, by link disjointness) declaring module,  *)
(* which the sub-link contains.                                               *)
(* ========================================================================== *)

lemma link_ghost_globals_agree:
  assumes linkA: "link_modules as = Inr a"
      and linkM: "link_modules ms = Inr m"
      and sub: "set as \<subseteq> set ms"
      and ghostOK: "\<forall>x \<in> set ms. module_ghost_subsets_ok x"
      and dom: "name |\<in>| fmdom (TE_GlobalVars (CM_TyEnv a))"
  shows "name |\<in>| TE_GhostGlobals (CM_TyEnv m) \<longleftrightarrow> name |\<in>| TE_GhostGlobals (CM_TyEnv a)"
proof
  note fA = link_modules_result_fields[OF linkA]
  note fM = link_modules_result_fields[OF linkM]
  \<comment> \<open>The declaring module inside as.\<close>
  have "name |\<in>| funion_list (map (\<lambda>x. fmdom (TE_GlobalVars (CM_TyEnv x))) as)"
    using dom unfolding fA(2) fmdom_fmlist_union by (simp add: o_def)
  then obtain x where x_in: "x \<in> set as"
                  and x_dom: "name |\<in>| fmdom (TE_GlobalVars (CM_TyEnv x))"
    by (auto simp: funion_list_member)
  assume "name |\<in>| TE_GhostGlobals (CM_TyEnv m)"
  then have "name |\<in>| funion_list (map (\<lambda>x. TE_GhostGlobals (CM_TyEnv x)) ms)"
    using fM(4) by simp
  then obtain z where z_in: "z \<in> set ms"
                  and z_gg: "name |\<in>| TE_GhostGlobals (CM_TyEnv z)"
    by (auto simp: funion_list_member)
  have z_dom: "name |\<in>| fmdom (TE_GlobalVars (CM_TyEnv z))"
    using ghostOK z_in z_gg unfolding module_ghost_subsets_ok_def
    by auto
  have gv_disj: "fmdisjoint_list (map (\<lambda>x. TE_GlobalVars (CM_TyEnv x)) ms)"
    using link_modules_success_facts(1)[OF linkM]
    unfolding link_fields_disjoint_def by blast
  have "z = x"
    using fmdisjoint_list_unique_witness[OF gv_disj z_in _ z_dom x_dom]
          x_in sub by auto
  then have "name |\<in>| TE_GhostGlobals (CM_TyEnv x)" using z_gg by simp
  then show "name |\<in>| TE_GhostGlobals (CM_TyEnv a)"
    unfolding fA(4) using x_in by (auto simp: funion_list_member)
next
  note fA = link_modules_result_fields[OF linkA]
  note fM = link_modules_result_fields[OF linkM]
  assume "name |\<in>| TE_GhostGlobals (CM_TyEnv a)"
  then obtain x where "x \<in> set as" and "name |\<in>| TE_GhostGlobals (CM_TyEnv x)"
    unfolding fA(4) by (auto simp: funion_list_member)
  then show "name |\<in>| TE_GhostGlobals (CM_TyEnv m)"
    unfolding fM(4) using sub by (auto simp: funion_list_member)
qed

lemma link_ghost_datatypes_agree:
  assumes linkA: "link_modules as = Inr a"
      and linkM: "link_modules ms = Inr m"
      and sub: "set as \<subseteq> set ms"
      and ghostOK: "\<forall>x \<in> set ms. module_ghost_subsets_ok x"
      and dom: "name |\<in>| fmdom (TE_Datatypes (CM_TyEnv a))"
  shows "name |\<in>| TE_GhostDatatypes (CM_TyEnv m) \<longleftrightarrow> name |\<in>| TE_GhostDatatypes (CM_TyEnv a)"
proof
  note fA = link_modules_result_fields[OF linkA]
  note fM = link_modules_result_fields[OF linkM]
  have "name |\<in>| funion_list (map (\<lambda>x. fmdom (TE_Datatypes (CM_TyEnv x))) as)"
    using dom unfolding fA(14) fmdom_fmlist_union by (simp add: o_def)
  then obtain x where x_in: "x \<in> set as"
                  and x_dom: "name |\<in>| fmdom (TE_Datatypes (CM_TyEnv x))"
    by (auto simp: funion_list_member)
  assume "name |\<in>| TE_GhostDatatypes (CM_TyEnv m)"
  then have "name |\<in>| funion_list (map (\<lambda>x. TE_GhostDatatypes (CM_TyEnv x)) ms)"
    using fM(17) by simp
  then obtain z where z_in: "z \<in> set ms"
                  and z_gd: "name |\<in>| TE_GhostDatatypes (CM_TyEnv z)"
    by (auto simp: funion_list_member)
  have z_dom: "name |\<in>| fmdom (TE_Datatypes (CM_TyEnv z))"
    using ghostOK z_in z_gd unfolding module_ghost_subsets_ok_def
    by auto
  have dt_disj: "fmdisjoint_list (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) ms)"
    using link_modules_success_facts(1)[OF linkM]
    unfolding link_fields_disjoint_def by blast
  have "z = x"
    using fmdisjoint_list_unique_witness[OF dt_disj z_in _ z_dom x_dom]
          x_in sub by auto
  then have "name |\<in>| TE_GhostDatatypes (CM_TyEnv x)" using z_gd by simp
  then show "name |\<in>| TE_GhostDatatypes (CM_TyEnv a)"
    unfolding fA(17) using x_in by (auto simp: funion_list_member)
next
  note fA = link_modules_result_fields[OF linkA]
  note fM = link_modules_result_fields[OF linkM]
  assume "name |\<in>| TE_GhostDatatypes (CM_TyEnv a)"
  then obtain x where "x \<in> set as" and "name |\<in>| TE_GhostDatatypes (CM_TyEnv x)"
    unfolding fA(17) by (auto simp: funion_list_member)
  then show "name |\<in>| TE_GhostDatatypes (CM_TyEnv m)"
    unfolding fM(17) using sub by (auto simp: funion_list_member)
qed


(* ========================================================================== *)
(* Set algebra: the whole link's type-variable fields split by side           *)
(* ========================================================================== *)

(* Reference order: (1) TE_TypeVars, (2) TE_RuntimeTypeVars,
   (3) TE_AbstractTypes, (4) TE_GhostGlobals, (5) TE_GhostDatatypes. *)
lemma link_pair_tyvar_split:
  assumes linkA: "link_modules as = Inr a"
      and linkB: "link_modules bs = Inr b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
  shows "TE_TypeVars (CM_TyEnv m)
           = (TE_TypeVars (CM_TyEnv a) |-| fmdom (CM_TypeSubst m))
             |\<union>| (TE_TypeVars (CM_TyEnv b) |-| fmdom (CM_TypeSubst m))"
    and "TE_RuntimeTypeVars (CM_TyEnv m)
           = (TE_RuntimeTypeVars (CM_TyEnv a) |-| fmdom (CM_TypeSubst m))
             |\<union>| (TE_RuntimeTypeVars (CM_TyEnv b) |-| fmdom (CM_TypeSubst m))"
    and "TE_AbstractTypes (CM_TyEnv m)
           = (TE_AbstractTypes (CM_TyEnv a) |-| fmdom (CM_TypeSubst m))
             |\<union>| (TE_AbstractTypes (CM_TyEnv b) |-| fmdom (CM_TypeSubst m))"
    and "TE_GhostGlobals (CM_TyEnv m)
           = TE_GhostGlobals (CM_TyEnv a) |\<union>| TE_GhostGlobals (CM_TyEnv b)"
    and "TE_GhostDatatypes (CM_TyEnv m)
           = TE_GhostDatatypes (CM_TyEnv a) |\<union>| TE_GhostDatatypes (CM_TyEnv b)"
proof -
  note fA = link_modules_result_fields[OF linkA]
  note fB = link_modules_result_fields[OF linkB]
  note fM = link_modules_result_fields[OF linkM]
  have subA: "set as \<subseteq> set ms" and subB: "set bs \<subseteq> set ms"
    using setMS by auto
  have domA: "fmdom (CM_TypeSubst a) |\<subseteq>| fmdom (CM_TypeSubst m)"
    using link_modules_subst_dom_mono[OF linkA linkM subA] .
  have domB: "fmdom (CM_TypeSubst b) |\<subseteq>| fmdom (CM_TypeSubst m)"
    using link_modules_subst_dom_mono[OF linkB linkM subB] .

  \<comment> \<open>One generic derivation per subtracted field.\<close>
  have gen: "funion_list (map g ms) |-| fmdom (CM_TypeSubst m)
               = ((funion_list (map g as) |-| fmdom (CM_TypeSubst a))
                    |-| fmdom (CM_TypeSubst m))
                 |\<union>| ((funion_list (map g bs) |-| fmdom (CM_TypeSubst b))
                    |-| fmdom (CM_TypeSubst m))"
    for g :: "CoreModule \<Rightarrow> string fset"
  proof -
    have "funion_list (map g ms) |-| fmdom (CM_TypeSubst m)
            = (funion_list (map g as) |-| fmdom (CM_TypeSubst m))
              |\<union>| (funion_list (map g bs) |-| fmdom (CM_TypeSubst m))"
      unfolding funion_list_split[OF setMS, of g] by auto
    then show ?thesis
      by (simp add: fminus_absorb_subset[OF domA] fminus_absorb_subset[OF domB])
  qed
  show "TE_TypeVars (CM_TyEnv m)
          = (TE_TypeVars (CM_TyEnv a) |-| fmdom (CM_TypeSubst m))
            |\<union>| (TE_TypeVars (CM_TyEnv b) |-| fmdom (CM_TypeSubst m))"
    unfolding fM(6) fA(6) fB(6) by (rule gen)
  show "TE_RuntimeTypeVars (CM_TyEnv m)
          = (TE_RuntimeTypeVars (CM_TyEnv a) |-| fmdom (CM_TypeSubst m))
            |\<union>| (TE_RuntimeTypeVars (CM_TyEnv b) |-| fmdom (CM_TypeSubst m))"
    unfolding fM(7) fA(7) fB(7) by (rule gen)
  show "TE_AbstractTypes (CM_TyEnv m)
          = (TE_AbstractTypes (CM_TyEnv a) |-| fmdom (CM_TypeSubst m))
            |\<union>| (TE_AbstractTypes (CM_TyEnv b) |-| fmdom (CM_TypeSubst m))"
    unfolding fM(8) fA(8) fB(8) by (rule gen)
  show "TE_GhostGlobals (CM_TyEnv m)
          = TE_GhostGlobals (CM_TyEnv a) |\<union>| TE_GhostGlobals (CM_TyEnv b)"
    unfolding fM(4) fA(4) fB(4) by (rule funion_list_split[OF setMS])
  show "TE_GhostDatatypes (CM_TyEnv m)
          = TE_GhostDatatypes (CM_TyEnv a) |\<union>| TE_GhostDatatypes (CM_TyEnv b)"
    unfolding fM(17) fA(17) fB(17) by (rule funion_list_split[OF setMS])
qed


(* ========================================================================== *)
(* The mixed intermediate environment                                         *)
(*                                                                            *)
(* link_mid_env a b m: the whole link's env (so the datatype tables, ghost    *)
(* fsets, by-type table and inert scope fields are already m's), except:      *)
(*   - the tyvar fields are the UNIONS of the two sides' (nothing subtracted  *)
(*     - the substitution has not been applied yet), with TE_AbstractTypes =  *)
(*     TE_TypeVars as at any module level;                                    *)
(*   - the three substituted declaration maps hold the a-side entries with    *)
(*     \<sigma>_A applied (= normalize_module a's entries), overlaid (a preferring)  *)
(*     with the b-side entries with \<sigma>_B applied. On keys both sides declare   *)
(*     (shared interface modules) the two values may differ syntactically -   *)
(*     applying \<sigma>_M collapses both onto the same normalize_module m entry     *)
(*     (link_mid_env_collapse).                                               *)
(* This is the A-side mid env; the B-side one is link_mid_env b a m.          *)
(* ========================================================================== *)

definition link_mid_env :: "CoreModule \<Rightarrow> CoreModule \<Rightarrow> CoreModule \<Rightarrow> CoreTyEnv" where
  "link_mid_env a b m =
     (CM_TyEnv m) \<lparr>
       TE_GlobalVars :=
         TE_GlobalVars (CM_TyEnv (normalize_module a))
         ++\<^sub>f fmdrop_fset (fmdom (TE_GlobalVars (CM_TyEnv (normalize_module a))))
                          (TE_GlobalVars (CM_TyEnv (normalize_module b))),
       TE_TypeVars := TE_TypeVars (CM_TyEnv a) |\<union>| TE_TypeVars (CM_TyEnv b),
       TE_RuntimeTypeVars :=
         TE_RuntimeTypeVars (CM_TyEnv a) |\<union>| TE_RuntimeTypeVars (CM_TyEnv b),
       TE_AbstractTypes := TE_TypeVars (CM_TyEnv a) |\<union>| TE_TypeVars (CM_TyEnv b),
       TE_Functions :=
         TE_Functions (CM_TyEnv (normalize_module a))
         ++\<^sub>f fmdrop_fset (fmdom (TE_Functions (CM_TyEnv (normalize_module a))))
                          (TE_Functions (CM_TyEnv (normalize_module b))),
       TE_DataCtors :=
         TE_DataCtors (CM_TyEnv (normalize_module a))
         ++\<^sub>f fmdrop_fset (fmdom (TE_DataCtors (CM_TyEnv (normalize_module a))))
                          (TE_DataCtors (CM_TyEnv (normalize_module b)))
     \<rparr>"

lemma link_mid_env_simps [simp]:
  "TE_LocalVars (link_mid_env a b m) = TE_LocalVars (CM_TyEnv m)"
  "TE_GlobalVars (link_mid_env a b m)
     = TE_GlobalVars (CM_TyEnv (normalize_module a))
       ++\<^sub>f fmdrop_fset (fmdom (TE_GlobalVars (CM_TyEnv (normalize_module a))))
                        (TE_GlobalVars (CM_TyEnv (normalize_module b)))"
  "TE_GhostLocals (link_mid_env a b m) = TE_GhostLocals (CM_TyEnv m)"
  "TE_GhostGlobals (link_mid_env a b m) = TE_GhostGlobals (CM_TyEnv m)"
  "TE_ConstLocals (link_mid_env a b m) = TE_ConstLocals (CM_TyEnv m)"
  "TE_TypeVars (link_mid_env a b m)
     = TE_TypeVars (CM_TyEnv a) |\<union>| TE_TypeVars (CM_TyEnv b)"
  "TE_RuntimeTypeVars (link_mid_env a b m)
     = TE_RuntimeTypeVars (CM_TyEnv a) |\<union>| TE_RuntimeTypeVars (CM_TyEnv b)"
  "TE_AbstractTypes (link_mid_env a b m)
     = TE_TypeVars (CM_TyEnv a) |\<union>| TE_TypeVars (CM_TyEnv b)"
  "TE_ReturnType (link_mid_env a b m) = TE_ReturnType (CM_TyEnv m)"
  "TE_FunctionGhost (link_mid_env a b m) = TE_FunctionGhost (CM_TyEnv m)"
  "TE_ProofGoal (link_mid_env a b m) = TE_ProofGoal (CM_TyEnv m)"
  "TE_ProofTopLevel (link_mid_env a b m) = TE_ProofTopLevel (CM_TyEnv m)"
  "TE_Functions (link_mid_env a b m)
     = TE_Functions (CM_TyEnv (normalize_module a))
       ++\<^sub>f fmdrop_fset (fmdom (TE_Functions (CM_TyEnv (normalize_module a))))
                        (TE_Functions (CM_TyEnv (normalize_module b)))"
  "TE_Datatypes (link_mid_env a b m) = TE_Datatypes (CM_TyEnv m)"
  "TE_DataCtors (link_mid_env a b m)
     = TE_DataCtors (CM_TyEnv (normalize_module a))
       ++\<^sub>f fmdrop_fset (fmdom (TE_DataCtors (CM_TyEnv (normalize_module a))))
                        (TE_DataCtors (CM_TyEnv (normalize_module b)))"
  "TE_DataCtorsByType (link_mid_env a b m) = TE_DataCtorsByType (CM_TyEnv m)"
  "TE_GhostDatatypes (link_mid_env a b m) = TE_GhostDatatypes (CM_TyEnv m)"
  by (simp_all add: link_mid_env_def)


(* ========================================================================== *)
(* The collapse (P5): substituting the mid env with the whole link's          *)
(* substitution gives exactly normalize_module m's env                        *)
(* ========================================================================== *)

(* The generic per-family computation: mapping the whole link's substitution
   action gM over the (gA-mapped as-part overlaid with the gB-mapped bs-part)
   equals mapping gM over the whole raw family - absorption per part. *)
lemma fmmap_mid_collapse:
  fixes f :: "CoreModule \<Rightarrow> (string, 'v :: type) fmap"
  assumes dA: "fmdisjoint_list (map f as)"
      and dB: "fmdisjoint_list (map f bs)"
      and dM: "fmdisjoint_list (map f ms)"
      and setMS: "set ms = set as \<union> set bs"
      and absorbA: "\<And>v. gM (gA v) = gM v"
      and absorbB: "\<And>v. gM (gB v) = gM v"
  shows "fmmap gM (fmmap gA (fmlist_union (map f as))
                   ++\<^sub>f fmdrop_fset (fmdom (fmmap gA (fmlist_union (map f as))))
                                    (fmmap gB (fmlist_union (map f bs))))
           = fmmap gM (fmlist_union (map f ms))"
proof (rule fmap_ext)
  fix k
  let ?uA = "fmlist_union (map f as)"
  let ?uB = "fmlist_union (map f bs)"
  let ?uM = "fmlist_union (map f ms)"
  have subA: "\<And>v. fmlookup ?uA k = Some v \<Longrightarrow> fmlookup ?uM k = Some v"
    using fmlist_union_sublist_lookup[OF dM dA] setMS by auto
  have subB: "\<And>v. fmlookup ?uB k = Some v \<Longrightarrow> fmlookup ?uM k = Some v"
    using fmlist_union_sublist_lookup[OF dM dB] setMS by auto
  have dom_eq: "fmdom (fmmap gA ?uA) = fmdom ?uA"
    by (rule fmdom_fmmap)
  show "fmlookup (fmmap gM (fmmap gA ?uA
                   ++\<^sub>f fmdrop_fset (fmdom (fmmap gA ?uA)) (fmmap gB ?uB))) k
          = fmlookup (fmmap gM ?uM) k"
  proof (cases "fmlookup ?uA k")
    case (Some v)
    have k_inA: "k |\<in>| fmdom ?uA" using Some by (rule fmdomI)
    have rhs: "fmlookup ?uM k = Some v" using subA[OF Some] .
    show ?thesis using Some rhs k_inA by (fastforce simp: absorbA)
  next
    case None
    then have k_notinA: "k |\<notin>| fmdom ?uA"
      by (simp add: fmdom_notI)
    show ?thesis
    proof (cases "fmlookup ?uB k")
      case (Some v)
      have k_inB: "k |\<in>| fmdom ?uB" using Some by (rule fmdomI)
      have rhs: "fmlookup ?uM k = Some v" using subB[OF Some] .
      show ?thesis using Some rhs k_inB k_notinA by (fastforce simp: absorbB)
    next
      case None
      have lhs: "fmlookup (fmmap gA ?uA
                   ++\<^sub>f fmdrop_fset (fmdom (fmmap gA ?uA)) (fmmap gB ?uB)) k = None"
        using k_notinA None by auto
      have "fmlookup ?uM k = None"
      proof (cases "fmlookup ?uM k")
        case None then show ?thesis .
      next
        case (Some w)
        then obtain s where s_in: "s \<in> set (map f ms)" and s_lk: "fmlookup s k = Some w"
          using fmlist_union_lookup[OF dM] by blast
        then obtain z where z_in: "z \<in> set ms" and s_eq: "s = f z" by auto
        have "z \<in> set as \<or> z \<in> set bs" using z_in setMS by auto
        then have False
        proof
          assume "z \<in> set as"
          then have "fmlookup ?uA k = Some w"
            using s_lk s_eq fmlist_union_lookup[OF dA] by auto
          then show False using \<open>fmlookup ?uA k = None\<close> by simp
        next
          assume "z \<in> set bs"
          then have "fmlookup ?uB k = Some w"
            using s_lk s_eq fmlist_union_lookup[OF dB] by auto
          then show False using None by simp
        qed
        then show ?thesis ..
      qed
      then show ?thesis using lhs by auto
    qed
  qed
qed

(* The three substituted families of the mid env collapse onto the whole
   link's raw families under the whole link's substitution. Factored out of
   link_mid_env_collapse because the function-body commutation lemma needs
   the same three equations. *)
lemma link_mid_env_family_collapse:
  assumes linkA: "link_modules as = Inr a"
      and linkB: "link_modules bs = Inr b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
  shows "fmmap (apply_subst (CM_TypeSubst m)) (TE_GlobalVars (link_mid_env a b m))
           = fmmap (apply_subst (CM_TypeSubst m)) (TE_GlobalVars (CM_TyEnv m))"
    and "fmmap (apply_subst_to_funinfo (CM_TypeSubst m)) (TE_Functions (link_mid_env a b m))
           = fmmap (apply_subst_to_funinfo (CM_TypeSubst m)) (TE_Functions (CM_TyEnv m))"
    and "fmmap (apply_subst_to_datactor (CM_TypeSubst m)) (TE_DataCtors (link_mid_env a b m))
           = fmmap (apply_subst_to_datactor (CM_TypeSubst m)) (TE_DataCtors (CM_TyEnv m))"
proof -
  note fA = link_modules_result_fields[OF linkA]
  note fB = link_modules_result_fields[OF linkB]
  note fM = link_modules_result_fields[OF linkM]
  have subA: "set as \<subseteq> set ms" and subB: "set bs \<subseteq> set ms"
    using setMS by auto
  have absA: "\<And>ty. apply_subst (CM_TypeSubst m) (apply_subst (CM_TypeSubst a) ty)
                     = apply_subst (CM_TypeSubst m) ty"
    using link_modules_closure_absorb[OF linkA linkM subA] .
  have absB: "\<And>ty. apply_subst (CM_TypeSubst m) (apply_subst (CM_TypeSubst b) ty)
                     = apply_subst (CM_TypeSubst m) ty"
    using link_modules_closure_absorb[OF linkB linkM subB] .
  have fdA: "link_fields_disjoint as" and fdB: "link_fields_disjoint bs"
   and fdM: "link_fields_disjoint ms"
    using link_modules_success_facts(1)[OF linkA]
          link_modules_success_facts(1)[OF linkB]
          link_modules_success_facts(1)[OF linkM] by blast+
  show "fmmap (apply_subst (CM_TypeSubst m)) (TE_GlobalVars (link_mid_env a b m))
          = fmmap (apply_subst (CM_TypeSubst m)) (TE_GlobalVars (CM_TyEnv m))"
    unfolding link_mid_env_simps normalize_module_simps apply_subst_to_tyenv_simps
              fA(2) fB(2) fM(2)
    using absA absB fdA fdB fdM fmmap_mid_collapse link_fields_disjoint_def setMS by blast
  show "fmmap (apply_subst_to_funinfo (CM_TypeSubst m)) (TE_Functions (link_mid_env a b m))
          = fmmap (apply_subst_to_funinfo (CM_TypeSubst m)) (TE_Functions (CM_TyEnv m))"
    unfolding link_mid_env_simps normalize_module_simps apply_subst_to_tyenv_simps
              fA(13) fB(13) fM(13)
    by (metis (no_types, lifting) absA absB fdA fdB fdM fmmap_mid_collapse link_fields_disjoint_def
        setMS subst_absorb_funinfo)
  show "fmmap (apply_subst_to_datactor (CM_TypeSubst m)) (TE_DataCtors (link_mid_env a b m))
          = fmmap (apply_subst_to_datactor (CM_TypeSubst m)) (TE_DataCtors (CM_TyEnv m))"
    unfolding link_mid_env_simps normalize_module_simps apply_subst_to_tyenv_simps
              fA(15) fB(15) fM(15)
    by (metis (no_types, lifting) absA absB fdA fdB fdM fmmap_mid_collapse link_fields_disjoint_def
        setMS subst_absorb_datactor)
qed

(* P5: pushing the whole link's substitution through the mid env, with
   normalize_module m's env as the tyvar-supplying target, IS
   normalize_module m's env. *)
lemma link_mid_env_collapse:
  assumes linkA: "link_modules as = Inr a"
      and linkB: "link_modules bs = Inr b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
  shows "apply_subst_to_module_env (CM_TypeSubst m) (CM_TyEnv (normalize_module m))
                                   (link_mid_env a b m)
           = CM_TyEnv (normalize_module m)"
proof -
  note fA = link_modules_result_fields[OF linkA]
  note fB = link_modules_result_fields[OF linkB]
  note fM = link_modules_result_fields[OF linkM]
  \<comment> \<open>The three substituted families (link_mid_env_family_collapse).\<close>
  note gv_eq = link_mid_env_family_collapse(1)[OF linkA linkB linkM setMS]
  note fn_eq = link_mid_env_family_collapse(2)[OF linkA linkB linkM setMS]
  note dc_eq = link_mid_env_family_collapse(3)[OF linkA linkB linkM setMS]

  show ?thesis
  proof (rule CoreTyEnv.equality)
    show "TE_LocalVars (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_LocalVars (CM_TyEnv (normalize_module m))"
      by (simp add: fM(1))
    show "TE_GlobalVars (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_GlobalVars (CM_TyEnv (normalize_module m))"
      using gv_eq by simp
    show "TE_GhostLocals (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_GhostLocals (CM_TyEnv (normalize_module m))"
      by simp
    show "TE_GhostGlobals (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_GhostGlobals (CM_TyEnv (normalize_module m))"
      by simp
    show "TE_ConstLocals (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_ConstLocals (CM_TyEnv (normalize_module m))"
      by simp
    show "TE_TypeVars (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_TypeVars (CM_TyEnv (normalize_module m))"
      by simp
    show "TE_RuntimeTypeVars (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_RuntimeTypeVars (CM_TyEnv (normalize_module m))"
      by simp
    show "TE_AbstractTypes (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_AbstractTypes (CM_TyEnv (normalize_module m))"
      by simp
    show "TE_ReturnType (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_ReturnType (CM_TyEnv (normalize_module m))"
      by (simp add: fM(9))
    show "TE_FunctionGhost (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_FunctionGhost (CM_TyEnv (normalize_module m))"
      by simp
    show "TE_ProofGoal (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_ProofGoal (CM_TyEnv (normalize_module m))"
      by (simp add: fM(11))
    show "TE_ProofTopLevel (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_ProofTopLevel (CM_TyEnv (normalize_module m))"
      by simp
    show "TE_Functions (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_Functions (CM_TyEnv (normalize_module m))"
      using fn_eq by simp
    show "TE_Datatypes (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_Datatypes (CM_TyEnv (normalize_module m))"
      by simp
    show "TE_DataCtors (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_DataCtors (CM_TyEnv (normalize_module m))"
      using dc_eq by simp
    show "TE_DataCtorsByType (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_DataCtorsByType (CM_TyEnv (normalize_module m))"
      by simp
    show "TE_GhostDatatypes (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_GhostDatatypes (CM_TyEnv (normalize_module m))"
      by simp
    show "CoreTyEnv.more (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = CoreTyEnv.more (CM_TyEnv (normalize_module m))"
      by (simp add: apply_subst_to_module_env_def link_mid_env_def
                    apply_subst_to_tyenv_def)
  qed
qed


(* ========================================================================== *)
(* Lookups in the mid env's substituted families, characterized against the   *)
(* raw whole-link entry                                                       *)
(* ========================================================================== *)

(* A function entry of the mid env is some raw whole-link entry with one
   side's substitution applied - in particular its FI_TyArgs, FI_Ghost and
   FI_Impure agree with the raw entry's, and the whole link's substitution
   collapses it onto the normalize_module m entry. *)
lemma link_mid_env_functions_lookup:
  assumes linkA: "link_modules as = Inr a"
      and linkB: "link_modules bs = Inr b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
      and lk: "fmlookup (TE_Functions (link_mid_env a b m)) name = Some info"
  obtains info0 where
      "fmlookup (TE_Functions (CM_TyEnv m)) name = Some info0"
  and "info = apply_subst_to_funinfo (CM_TypeSubst a) info0
       \<or> info = apply_subst_to_funinfo (CM_TypeSubst b) info0"
  and "FI_TyArgs info = FI_TyArgs info0"
  and "FI_Ghost info = FI_Ghost info0"
  and "apply_subst_to_funinfo (CM_TypeSubst m) info
         = apply_subst_to_funinfo (CM_TypeSubst m) info0"
proof -
  have subA: "set as \<subseteq> set ms" and subB: "set bs \<subseteq> set ms"
    using setMS by auto
  have absA: "\<And>ty. apply_subst (CM_TypeSubst m) (apply_subst (CM_TypeSubst a) ty)
                     = apply_subst (CM_TypeSubst m) ty"
    using link_modules_closure_absorb[OF linkA linkM subA] .
  have absB: "\<And>ty. apply_subst (CM_TypeSubst m) (apply_subst (CM_TypeSubst b) ty)
                     = apply_subst (CM_TypeSubst m) ty"
    using link_modules_closure_absorb[OF linkB linkM subB] .
  let ?fnA = "TE_Functions (CM_TyEnv a)"
  let ?fnB = "TE_Functions (CM_TyEnv b)"
  have mid_fn: "TE_Functions (link_mid_env a b m)
                  = fmmap (apply_subst_to_funinfo (CM_TypeSubst a)) ?fnA
                    ++\<^sub>f fmdrop_fset (fmdom (fmmap (apply_subst_to_funinfo (CM_TypeSubst a)) ?fnA))
                         (fmmap (apply_subst_to_funinfo (CM_TypeSubst b)) ?fnB)"
    by simp
  show ?thesis
  proof (cases "name |\<in>| fmdom (fmmap (apply_subst_to_funinfo (CM_TypeSubst a)) ?fnA)")
    case True
    then have "fmlookup (fmmap (apply_subst_to_funinfo (CM_TypeSubst a)) ?fnA) name
                 = Some info"
      using lk mid_fn by (simp add: fmadd_drop_lookup)
    then obtain info0 where a_lk: "fmlookup ?fnA name = Some info0"
        and info_eq: "info = apply_subst_to_funinfo (CM_TypeSubst a) info0"
      by (cases "fmlookup ?fnA name") auto
    have m_lk: "fmlookup (TE_Functions (CM_TyEnv m)) name = Some info0"
      using link_modules_decl_submaps(2)[OF linkA linkM subA a_lk] .
    show ?thesis
    proof (rule that[OF m_lk])
      show "info = apply_subst_to_funinfo (CM_TypeSubst a) info0
            \<or> info = apply_subst_to_funinfo (CM_TypeSubst b) info0"
        using info_eq by simp
      show "FI_TyArgs info = FI_TyArgs info0" using info_eq by simp
      show "FI_Ghost info = FI_Ghost info0" using info_eq by simp
      show "apply_subst_to_funinfo (CM_TypeSubst m) info
              = apply_subst_to_funinfo (CM_TypeSubst m) info0"
        using info_eq subst_absorb_funinfo[OF absA] by simp
    qed
  next
    case False
    then have "fmlookup (fmmap (apply_subst_to_funinfo (CM_TypeSubst b)) ?fnB) name
                 = Some info"
      using lk mid_fn by (metis fmadd_drop_lookup)
    then obtain info0 where b_lk: "fmlookup ?fnB name = Some info0"
        and info_eq: "info = apply_subst_to_funinfo (CM_TypeSubst b) info0"
      by (cases "fmlookup ?fnB name") auto
    have m_lk: "fmlookup (TE_Functions (CM_TyEnv m)) name = Some info0"
      using link_modules_decl_submaps(2)[OF linkB linkM subB b_lk] .
    show ?thesis
    proof (rule that[OF m_lk])
      show "info = apply_subst_to_funinfo (CM_TypeSubst a) info0
            \<or> info = apply_subst_to_funinfo (CM_TypeSubst b) info0"
        using info_eq by simp
      show "FI_TyArgs info = FI_TyArgs info0" using info_eq by simp
      show "FI_Ghost info = FI_Ghost info0" using info_eq by simp
      show "apply_subst_to_funinfo (CM_TypeSubst m) info
              = apply_subst_to_funinfo (CM_TypeSubst m) info0"
        using info_eq subst_absorb_funinfo[OF absB] by simp
    qed
  qed
qed

(* Likewise for a data-constructor entry: the datatype name and tyvar list
   agree with the raw whole-link entry's. *)
lemma link_mid_env_ctors_lookup:
  assumes linkA: "link_modules as = Inr a"
      and linkB: "link_modules bs = Inr b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
      and lk: "fmlookup (TE_DataCtors (link_mid_env a b m)) ctorName
                 = Some (dtName, tyVars, payload)"
  obtains payload0 where
      "fmlookup (TE_DataCtors (CM_TyEnv m)) ctorName = Some (dtName, tyVars, payload0)"
proof -
  have subA: "set as \<subseteq> set ms" and subB: "set bs \<subseteq> set ms"
    using setMS by auto
  let ?dcA = "TE_DataCtors (CM_TyEnv a)"
  let ?dcB = "TE_DataCtors (CM_TyEnv b)"
  show ?thesis
  proof (cases "ctorName |\<in>| fmdom (fmmap (apply_subst_to_datactor (CM_TypeSubst a)) ?dcA)")
    case True
    then have "fmlookup (fmmap (apply_subst_to_datactor (CM_TypeSubst a)) ?dcA) ctorName
                 = Some (dtName, tyVars, payload)"
      using lk by (simp add: fmadd_drop_lookup)
    then obtain entry0 where a_lk: "fmlookup ?dcA ctorName = Some entry0"
        and entry_eq: "(dtName, tyVars, payload) = apply_subst_to_datactor (CM_TypeSubst a) entry0"
      by (cases "fmlookup ?dcA ctorName") auto
    obtain dt0 tv0 payload0 where entry0_eq: "entry0 = (dt0, tv0, payload0)"
      by (cases entry0) auto
    have "dt0 = dtName" and "tv0 = tyVars"
      using entry_eq entry0_eq by (auto simp: apply_subst_to_datactor_def)
    then have "fmlookup ?dcA ctorName = Some (dtName, tyVars, payload0)"
      using a_lk entry0_eq by simp
    then have "fmlookup (TE_DataCtors (CM_TyEnv m)) ctorName = Some (dtName, tyVars, payload0)"
      using link_modules_decl_submaps(4)[OF linkA linkM subA] by blast
    then show ?thesis using that by blast
  next
    case False
    then have "fmlookup (fmmap (apply_subst_to_datactor (CM_TypeSubst b)) ?dcB) ctorName
                 = Some (dtName, tyVars, payload)"
      using lk
      by (metis apply_subst_to_tyenv_simps(15) fmadd_drop_lookup link_mid_env_simps(15)
          normalize_module_simps(1))
    then obtain entry0 where b_lk: "fmlookup ?dcB ctorName = Some entry0"
        and entry_eq: "(dtName, tyVars, payload) = apply_subst_to_datactor (CM_TypeSubst b) entry0"
      by (cases "fmlookup ?dcB ctorName") auto
    obtain dt0 tv0 payload0 where entry0_eq: "entry0 = (dt0, tv0, payload0)"
      by (cases entry0) auto
    have "dt0 = dtName" and "tv0 = tyVars"
      using entry_eq entry0_eq by (auto simp: apply_subst_to_datactor_def)
    then have "fmlookup ?dcB ctorName = Some (dtName, tyVars, payload0)"
      using b_lk entry0_eq by simp
    then have "fmlookup (TE_DataCtors (CM_TyEnv m)) ctorName = Some (dtName, tyVars, payload0)"
      using link_modules_decl_submaps(4)[OF linkB linkM subB] by blast
    then show ?thesis using that by blast
  qed
qed


(* ========================================================================== *)
(* The engine's side conditions at the mid env (P3, P4)                       *)
(* ========================================================================== *)

(* module_env_subst_ok: the datatype tables agree by construction; the tyvar
   coverage is R3's transfer theorem (resolved case) plus set algebra
   (unresolved case); the binder-avoidance clauses are
   link_modules_capture_avoiding read back through the raw entries. *)
lemma link_mid_env_subst_ok:
  assumes linkA: "link_modules as = Inr a"
      and wtA: "core_module_well_typed a"
      and linkB: "link_modules bs = Inr b"
      and wtB: "core_module_well_typed b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
  shows "module_env_subst_ok (CM_TypeSubst m) (CM_TyEnv (normalize_module m))
                             (link_mid_env a b m)"
  unfolding module_env_subst_ok_def
proof (intro conjI)
  show "TE_Datatypes (CM_TyEnv (normalize_module m)) = TE_Datatypes (link_mid_env a b m)"
    by simp
  show "TE_GhostDatatypes (CM_TyEnv (normalize_module m))
          = TE_GhostDatatypes (link_mid_env a b m)"
    by simp
next
  note fA = link_modules_result_fields[OF linkA]
  note fB = link_modules_result_fields[OF linkB]
  note fM = link_modules_result_fields[OF linkM]
  have wkA: "typesubst_well_kinded (CM_TyEnv a) (CM_TypeSubst a)"
    and wkB: "typesubst_well_kinded (CM_TyEnv b) (CM_TypeSubst b)"
    using wtA wtB unfolding core_module_well_typed_def by blast+
  have wkM: "typesubst_well_kinded (CM_TyEnv m) (CM_TypeSubst m)"
    using link_modules_typesubst_well_kinded[OF linkA linkB linkM setMS wkA wkB] .
  show "\<forall>n. n |\<in>| TE_TypeVars (link_mid_env a b m) \<longrightarrow>
          (case fmlookup (CM_TypeSubst m) n of
             Some ty' \<Rightarrow> is_well_kinded (CM_TyEnv (normalize_module m)) ty'
           | None \<Rightarrow> n |\<in>| TE_TypeVars (CM_TyEnv (normalize_module m)))"
  proof (intro allI impI)
    fix n assume n_in: "n |\<in>| TE_TypeVars (link_mid_env a b m)"
    show "case fmlookup (CM_TypeSubst m) n of
             Some ty' \<Rightarrow> is_well_kinded (CM_TyEnv (normalize_module m)) ty'
           | None \<Rightarrow> n |\<in>| TE_TypeVars (CM_TyEnv (normalize_module m))"
    proof (cases "fmlookup (CM_TypeSubst m) n")
      case (Some ty')
      have "is_well_kinded (CM_TyEnv m) ty'"
        using wkM Some unfolding typesubst_well_kinded_def by blast
      moreover have "is_well_kinded (CM_TyEnv (normalize_module m)) ty'
                       = is_well_kinded (CM_TyEnv m) ty'"
        by (intro is_well_kinded_cong_env) simp_all
      ultimately show ?thesis using Some by simp
    next
      case None
      have n_notdom: "n |\<notin>| fmdom (CM_TypeSubst m)"
        using None by (simp add: fmdom_notI)
      have "n |\<in>| TE_TypeVars (CM_TyEnv a) \<or> n |\<in>| TE_TypeVars (CM_TyEnv b)"
        using n_in by auto
      then have "n |\<in>| funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) ms)"
      proof
        assume "n |\<in>| TE_TypeVars (CM_TyEnv a)"
        then have "n |\<in>| funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) as)"
          using fA(6) by auto
        then show ?thesis
          unfolding funion_list_split[OF setMS] by auto
      next
        assume "n |\<in>| TE_TypeVars (CM_TyEnv b)"
        then have "n |\<in>| funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) bs)"
          using fB(6) by auto
        then show ?thesis
          unfolding funion_list_split[OF setMS] by auto
      qed
      then have "n |\<in>| TE_TypeVars (CM_TyEnv m)"
        using fM(6) n_notdom by simp
      then show ?thesis using None by simp
    qed
  qed
next
  have capM: "capture_avoiding m"
    using link_modules_capture_avoiding[OF linkM] .
  show "\<forall>funName info.
          fmlookup (TE_Functions (link_mid_env a b m)) funName = Some info \<longrightarrow>
          subst_names (CM_TypeSubst m) |\<inter>| fset_of_list (FI_TyArgs info) = {||}"
  proof (intro allI impI)
    fix funName info
    assume "fmlookup (TE_Functions (link_mid_env a b m)) funName = Some info"
    then obtain info0 where
        m_lk: "fmlookup (TE_Functions (CM_TyEnv m)) funName = Some info0" and
        "info = apply_subst_to_funinfo (CM_TypeSubst a) info0
         \<or> info = apply_subst_to_funinfo (CM_TypeSubst b) info0" and
        tyargs_eq: "FI_TyArgs info = FI_TyArgs info0" and
        "FI_Ghost info = FI_Ghost info0" and
        "apply_subst_to_funinfo (CM_TypeSubst m) info
           = apply_subst_to_funinfo (CM_TypeSubst m) info0"
      by (rule link_mid_env_functions_lookup[OF linkA linkB linkM setMS])
    show "subst_names (CM_TypeSubst m) |\<inter>| fset_of_list (FI_TyArgs info) = {||}"
      using capM m_lk tyargs_eq unfolding capture_avoiding_def by simp
  qed
  show "\<forall>ctorName dtName tyVars payload.
          fmlookup (TE_DataCtors (link_mid_env a b m)) ctorName
            = Some (dtName, tyVars, payload) \<longrightarrow>
          subst_names (CM_TypeSubst m) |\<inter>| fset_of_list tyVars = {||}"
  proof (intro allI impI)
    fix ctorName dtName tyVars payload
    assume "fmlookup (TE_DataCtors (link_mid_env a b m)) ctorName
              = Some (dtName, tyVars, payload)"
    then obtain payload0 where
        m_lk: "fmlookup (TE_DataCtors (CM_TyEnv m)) ctorName
                 = Some (dtName, tyVars, payload0)"
      by (rule link_mid_env_ctors_lookup[OF linkA linkB linkM setMS])
    show "subst_names (CM_TypeSubst m) |\<inter>| fset_of_list tyVars = {||}"
      using capM m_lk unfolding capture_avoiding_def by blast
  qed
qed

(* module_env_subst_runtime_ok: the resolved case is the R2 link_runtime_ok
   check; the unresolved case is set algebra. *)
lemma link_mid_env_runtime_ok:
  assumes linkA: "link_modules as = Inr a"
      and linkB: "link_modules bs = Inr b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
  shows "module_env_subst_runtime_ok (CM_TypeSubst m) (CM_TyEnv (normalize_module m))
                                     (link_mid_env a b m)"
  unfolding module_env_subst_runtime_ok_def
proof (intro allI impI)
  note fA = link_modules_result_fields[OF linkA]
  note fB = link_modules_result_fields[OF linkB]
  note fM = link_modules_result_fields[OF linkM]
  fix n assume n_in: "n |\<in>| TE_RuntimeTypeVars (link_mid_env a b m)"
  have n_union: "n |\<in>| funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) ms)"
  proof -
    have "n |\<in>| TE_RuntimeTypeVars (CM_TyEnv a) \<or> n |\<in>| TE_RuntimeTypeVars (CM_TyEnv b)"
      using n_in by auto
    then show ?thesis
    proof
      assume "n |\<in>| TE_RuntimeTypeVars (CM_TyEnv a)"
      then have "n |\<in>| funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) as)"
        using fA(7) by auto
      then show ?thesis unfolding funion_list_split[OF setMS] by auto
    next
      assume "n |\<in>| TE_RuntimeTypeVars (CM_TyEnv b)"
      then have "n |\<in>| funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) bs)"
        using fB(7) by auto
      then show ?thesis unfolding funion_list_split[OF setMS] by auto
    qed
  qed
  show "case fmlookup (CM_TypeSubst m) n of
           Some ty' \<Rightarrow> is_runtime_type (CM_TyEnv (normalize_module m)) ty'
         | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars (CM_TyEnv (normalize_module m))"
  proof (cases "fmlookup (CM_TypeSubst m) n")
    case (Some ty')
    have "is_runtime_type (CM_TyEnv m) ty'"
      using link_modules_runtime_resolution[OF linkM n_union Some] .
    moreover have "is_runtime_type (CM_TyEnv (normalize_module m)) ty'
                     = is_runtime_type (CM_TyEnv m) ty'"
      by (intro is_runtime_type_cong_env) simp_all
    ultimately show ?thesis using Some by simp
  next
    case None
    have "n |\<notin>| fmdom (CM_TypeSubst m)"
      using None by (simp add: fmdom_notI)
    then have "n |\<in>| TE_RuntimeTypeVars (CM_TyEnv m)"
      using fM(7) n_union by simp
    then show ?thesis using None by simp
  qed
qed


(* ========================================================================== *)
(* Well-formedness of the mid env (P2)                                        *)
(*                                                                            *)
(* Every clause of tyenv_well_formed transfers from the two sides: an entry   *)
(* of an overlaid family comes verbatim from ONE side's normalized env, whose *)
(* well-typedness supplies the side-local fact; the monotone transfer lemmas  *)
(* (is_well_kinded_mono / is_runtime_type_transfer_mono) then carry it to the *)
(* mid env's wider tyvar fields and the whole link's datatype table. The      *)
(* ghost-sensitive clauses additionally use the ghost-agreement lemmas, and   *)
(* the ctors-by-type clause uses whole-link disjointness to identify the      *)
(* unique declaring module of a shared key.                                   *)
(* ========================================================================== *)

(* A defined entry of the A-preferring disjoint overlay comes from one side. *)
lemma fmadd_drop_lookup_Some:
  assumes "fmlookup (m1 ++\<^sub>f fmdrop_fset (fmdom m1) m2) k = Some v"
  shows "fmlookup m1 k = Some v \<or> fmlookup m2 k = Some v"
  using assms by (simp add: fmadd_drop_lookup split: if_splits)

(* If both sub-links define the same key of the same (raw) family, the values
   agree: the key's unique declaring module in ms is shared by as and bs. *)
lemma link_pair_shared_lookup:
  fixes f :: "CoreModule \<Rightarrow> (string, 'v :: type) fmap"
  assumes dA: "fmdisjoint_list (map f as)"
      and dB: "fmdisjoint_list (map f bs)"
      and dM: "fmdisjoint_list (map f ms)"
      and setMS: "set ms = set as \<union> set bs"
      and lkA: "fmlookup (fmlist_union (map f as)) k = Some v1"
      and lkB: "fmlookup (fmlist_union (map f bs)) k = Some v2"
  shows "v1 = v2"
proof -
  obtain sa where sa_in: "sa \<in> set (map f as)" and sa_lk: "fmlookup sa k = Some v1"
    using fmlist_union_lookup[OF dA] lkA by blast
  then obtain y where y_in: "y \<in> set as" and sa_eq: "sa = f y" by auto
  obtain sb where sb_in: "sb \<in> set (map f bs)" and sb_lk: "fmlookup sb k = Some v2"
    using fmlist_union_lookup[OF dB] lkB by blast
  then obtain w where w_in: "w \<in> set bs" and sb_eq: "sb = f w" by auto
  have "y = w"
    using fmdisjoint_list_unique_witness[OF dM, of y w k]
          y_in w_in setMS sa_lk sb_lk sa_eq sb_eq
    by (auto intro: fmdomI)
  then show ?thesis using sa_lk sb_lk sa_eq sb_eq by simp
qed

(* Well-kindedness transfers from a sub-link-based env into a whole-link-based
   env: the sub-link's datatype table is a submap of the whole link's. *)
lemma link_side_wk_transfer:
  assumes linkC: "link_modules cs = Inr c"
      and linkM: "link_modules ms = Inr m"
      and sub: "set cs \<subseteq> set ms"
      and wk: "is_well_kinded env1 ty"
      and dt1: "TE_Datatypes env1 = TE_Datatypes (CM_TyEnv c)"
      and dt2: "TE_Datatypes env2 = TE_Datatypes (CM_TyEnv m)"
      and tv: "fset (TE_TypeVars env1) \<subseteq> fset (TE_TypeVars env2)"
  shows "is_well_kinded env2 ty"
proof -
  have dt: "\<And>n v. fmlookup (TE_Datatypes env1) n = Some v
              \<Longrightarrow> fmlookup (TE_Datatypes env2) n = Some v"
    unfolding dt1 dt2 using link_modules_decl_submaps(3)[OF linkC linkM sub] by blast
  show ?thesis using is_well_kinded_mono[OF wk tv dt] .
qed

(* Likewise for runtime-ness of well-kinded types: the ghost-datatype marker
   agrees on the sub-link's datatype domain (ghost-agreement lemma, using the
   module_ghost_subsets_ok hypothesis). *)
lemma link_side_rt_transfer:
  assumes linkC: "link_modules cs = Inr c"
      and linkM: "link_modules ms = Inr m"
      and sub: "set cs \<subseteq> set ms"
      and ghostOK: "\<forall>x \<in> set ms. module_ghost_subsets_ok x"
      and wk: "is_well_kinded env1 ty"
      and rt: "is_runtime_type env1 ty"
      and dt1: "TE_Datatypes env1 = TE_Datatypes (CM_TyEnv c)"
      and gd1: "TE_GhostDatatypes env1 = TE_GhostDatatypes (CM_TyEnv c)"
      and gd2: "TE_GhostDatatypes env2 = TE_GhostDatatypes (CM_TyEnv m)"
      and rtv: "fset (TE_RuntimeTypeVars env1) \<subseteq> fset (TE_RuntimeTypeVars env2)"
  shows "is_runtime_type env2 ty"
proof -
  have gd: "\<And>n. n |\<in>| fmdom (TE_Datatypes env1) \<Longrightarrow>
              (n |\<in>| TE_GhostDatatypes env2 \<longleftrightarrow> n |\<in>| TE_GhostDatatypes env1)"
    unfolding dt1 gd1 gd2
    using link_ghost_datatypes_agree[OF linkC linkM sub ghostOK] by blast
  show ?thesis using is_runtime_type_transfer_mono[OF wk rt rtv gd] .
qed

(* The whole link's datatype domain splits by side. *)
lemma link_pair_datatypes_dom_split:
  assumes linkA: "link_modules as = Inr a"
      and linkB: "link_modules bs = Inr b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
  shows "fmdom (TE_Datatypes (CM_TyEnv m))
           = fmdom (TE_Datatypes (CM_TyEnv a)) |\<union>| fmdom (TE_Datatypes (CM_TyEnv b))"
proof -
  note fA = link_modules_result_fields[OF linkA]
  note fB = link_modules_result_fields[OF linkB]
  note fM = link_modules_result_fields[OF linkM]
  have gen: "\<And>zs. fmdom (fmlist_union (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) zs))
               = funion_list (map (\<lambda>x. fmdom (TE_Datatypes (CM_TyEnv x))) zs)"
    unfolding fmdom_fmlist_union map_map by (simp add: o_def)
  show ?thesis
    unfolding fM(14) fA(14) fB(14) gen
    by (rule funion_list_split[OF setMS])
qed

(* P2: the mid env is well-formed. *)
lemma link_mid_env_well_formed:
  assumes linkA: "link_modules as = Inr a"
      and wtA: "core_module_well_typed a"
      and linkB: "link_modules bs = Inr b"
      and wtB: "core_module_well_typed b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
      and ghostOK: "\<forall>x \<in> set ms. module_ghost_subsets_ok x"
  shows "tyenv_well_formed (link_mid_env a b m)"
proof -
  let ?mid = "link_mid_env a b m"
  let ?envA = "CM_TyEnv (normalize_module a)"
  let ?envB = "CM_TyEnv (normalize_module b)"
  note fA = link_modules_result_fields[OF linkA]
  note fB = link_modules_result_fields[OF linkB]
  note fM = link_modules_result_fields[OF linkM]
  note gsplit = link_pair_tyvar_split[OF linkA linkB linkM setMS]
  have subA: "set as \<subseteq> set ms" and subB: "set bs \<subseteq> set ms"
    using setMS by auto
  have dtdom: "fmdom (TE_Datatypes (CM_TyEnv m))
                 = fmdom (TE_Datatypes (CM_TyEnv a)) |\<union>| fmdom (TE_Datatypes (CM_TyEnv b))"
    using link_pair_datatypes_dom_split[OF linkA linkB linkM setMS] .

  \<comment> \<open>Side well-formedness and the module-level Abs = TV convention.\<close>
  have wfA: "tyenv_well_formed ?envA"
    and absa0: "TE_AbstractTypes ?envA = TE_TypeVars ?envA"
    using wtA unfolding core_module_well_typed_def normalized_module_well_typed_def
                        tyenv_module_scope_def
    by blast+
  have wfB: "tyenv_well_formed ?envB"
    and absb0: "TE_AbstractTypes ?envB = TE_TypeVars ?envB"
    using wtB unfolding core_module_well_typed_def normalized_module_well_typed_def
                        tyenv_module_scope_def
    by blast+
  have absa: "TE_AbstractTypes (CM_TyEnv a) = TE_TypeVars (CM_TyEnv a)"
    using absa0 by simp
  have absb: "TE_AbstractTypes (CM_TyEnv b) = TE_TypeVars (CM_TyEnv b)"
    using absb0 by simp
  have rtvA: "TE_RuntimeTypeVars (CM_TyEnv a) |\<subseteq>| TE_TypeVars (CM_TyEnv a)"
    using wfA unfolding tyenv_well_formed_def tyenv_runtime_tyvars_subset_def by simp
  have rtvB: "TE_RuntimeTypeVars (CM_TyEnv b) |\<subseteq>| TE_TypeVars (CM_TyEnv b)"
    using wfB unfolding tyenv_well_formed_def tyenv_runtime_tyvars_subset_def by simp

  \<comment> \<open>Ghost-marker agreement, raw form.\<close>
  have ggA: "\<And>name. name |\<in>| fmdom (TE_GlobalVars (CM_TyEnv a)) \<Longrightarrow>
               (name |\<in>| TE_GhostGlobals (CM_TyEnv m)
                  \<longleftrightarrow> name |\<in>| TE_GhostGlobals (CM_TyEnv a))"
    using link_ghost_globals_agree[OF linkA linkM subA ghostOK] by blast
  have ggB: "\<And>name. name |\<in>| fmdom (TE_GlobalVars (CM_TyEnv b)) \<Longrightarrow>
               (name |\<in>| TE_GhostGlobals (CM_TyEnv m)
                  \<longleftrightarrow> name |\<in>| TE_GhostGlobals (CM_TyEnv b))"
    using link_ghost_globals_agree[OF linkB linkM subB ghostOK] by blast
  have gdA: "\<And>name. name |\<in>| fmdom (TE_Datatypes (CM_TyEnv a)) \<Longrightarrow>
               (name |\<in>| TE_GhostDatatypes (CM_TyEnv m)
                  \<longleftrightarrow> name |\<in>| TE_GhostDatatypes (CM_TyEnv a))"
    using link_ghost_datatypes_agree[OF linkA linkM subA ghostOK] by blast
  have gdB: "\<And>name. name |\<in>| fmdom (TE_Datatypes (CM_TyEnv b)) \<Longrightarrow>
               (name |\<in>| TE_GhostDatatypes (CM_TyEnv m)
                  \<longleftrightarrow> name |\<in>| TE_GhostDatatypes (CM_TyEnv b))"
    using link_ghost_datatypes_agree[OF linkB linkM subB ghostOK] by blast

  \<comment> \<open>Overlaid-family dichotomies.\<close>
  have gv_cases: "\<And>name ty. fmlookup (TE_GlobalVars ?mid) name = Some ty \<Longrightarrow>
                    fmlookup (TE_GlobalVars ?envA) name = Some ty
                    \<or> fmlookup (TE_GlobalVars ?envB) name = Some ty"
    unfolding link_mid_env_simps using fmadd_drop_lookup_Some by fastforce
  have fn_cases: "\<And>name info. fmlookup (TE_Functions ?mid) name = Some info \<Longrightarrow>
                    fmlookup (TE_Functions ?envA) name = Some info
                    \<or> fmlookup (TE_Functions ?envB) name = Some info"
    unfolding link_mid_env_simps using fmadd_drop_lookup_Some by fastforce
  have dc_cases: "\<And>name entry. fmlookup (TE_DataCtors ?mid) name = Some entry \<Longrightarrow>
                    fmlookup (TE_DataCtors ?envA) name = Some entry
                    \<or> fmlookup (TE_DataCtors ?envB) name = Some entry"
    unfolding link_mid_env_simps using fmadd_drop_lookup_Some by fastforce

  \<comment> \<open>Per-family whole-link disjointness.\<close>
  have dcdisjA: "fmdisjoint_list (map (\<lambda>x. TE_DataCtors (CM_TyEnv x)) as)"
    and btdisjA: "fmdisjoint_list (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) as)"
    using link_modules_success_facts(1)[OF linkA]
    unfolding link_fields_disjoint_def by blast+
  have dcdisjB: "fmdisjoint_list (map (\<lambda>x. TE_DataCtors (CM_TyEnv x)) bs)"
    and btdisjB: "fmdisjoint_list (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) bs)"
    using link_modules_success_facts(1)[OF linkB]
    unfolding link_fields_disjoint_def by blast+
  have dcdisjM: "fmdisjoint_list (map (\<lambda>x. TE_DataCtors (CM_TyEnv x)) ms)"
    and btdisjM: "fmdisjoint_list (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) ms)"
    using link_modules_success_facts(1)[OF linkM]
    unfolding link_fields_disjoint_def by blast+

  \<comment> \<open>Side clause extractions (stated at the normalized side envs).\<close>
  have gvwkA: "\<And>name ty. fmlookup (TE_GlobalVars ?envA) name = Some ty \<Longrightarrow>
                 is_well_kinded (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA \<rparr>) ty"
    using wfA unfolding tyenv_well_formed_def tyenv_vars_well_kinded_def by blast
  have gvwkB: "\<And>name ty. fmlookup (TE_GlobalVars ?envB) name = Some ty \<Longrightarrow>
                 is_well_kinded (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB \<rparr>) ty"
    using wfB unfolding tyenv_well_formed_def tyenv_vars_well_kinded_def by blast
  have gvrtA: "\<And>name ty. fmlookup (TE_GlobalVars ?envA) name = Some ty \<Longrightarrow>
                 name |\<notin>| TE_GhostGlobals ?envA \<Longrightarrow>
                 is_runtime_type (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA,
                                          TE_RuntimeTypeVars :=
                                            TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA \<rparr>) ty"
    using wfA unfolding tyenv_well_formed_def tyenv_vars_runtime_def by blast
  have gvrtB: "\<And>name ty. fmlookup (TE_GlobalVars ?envB) name = Some ty \<Longrightarrow>
                 name |\<notin>| TE_GhostGlobals ?envB \<Longrightarrow>
                 is_runtime_type (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB,
                                          TE_RuntimeTypeVars :=
                                            TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB \<rparr>) ty"
    using wfB unfolding tyenv_well_formed_def tyenv_vars_runtime_def by blast
  have ggsubA: "TE_GhostGlobals (CM_TyEnv a) |\<subseteq>| fmdom (TE_GlobalVars (CM_TyEnv a))"
    using wfA unfolding tyenv_well_formed_def tyenv_ghost_vars_subset_def by simp
  have ggsubB: "TE_GhostGlobals (CM_TyEnv b) |\<subseteq>| fmdom (TE_GlobalVars (CM_TyEnv b))"
    using wfB unfolding tyenv_well_formed_def tyenv_ghost_vars_subset_def by simp
  have ccA: "\<And>ctorName dtName tyVars payload.
               fmlookup (TE_DataCtors ?envA) ctorName = Some (dtName, tyVars, payload) \<Longrightarrow>
               fmlookup (TE_Datatypes ?envA) dtName = Some (length tyVars)"
    using wfA unfolding tyenv_well_formed_def tyenv_ctors_consistent_def by blast
  have ccB: "\<And>ctorName dtName tyVars payload.
               fmlookup (TE_DataCtors ?envB) ctorName = Some (dtName, tyVars, payload) \<Longrightarrow>
               fmlookup (TE_Datatypes ?envB) dtName = Some (length tyVars)"
    using wfB unfolding tyenv_well_formed_def tyenv_ctors_consistent_def by blast
  have pwkA: "\<And>ctorName dtName tyVars payload.
                fmlookup (TE_DataCtors ?envA) ctorName = Some (dtName, tyVars, payload) \<Longrightarrow>
                is_well_kinded (?envA \<lparr> TE_TypeVars :=
                                        TE_AbstractTypes ?envA |\<union>| fset_of_list tyVars \<rparr>) payload"
    using wfA unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def by blast
  have pwkB: "\<And>ctorName dtName tyVars payload.
                fmlookup (TE_DataCtors ?envB) ctorName = Some (dtName, tyVars, payload) \<Longrightarrow>
                is_well_kinded (?envB \<lparr> TE_TypeVars :=
                                        TE_AbstractTypes ?envB |\<union>| fset_of_list tyVars \<rparr>) payload"
    using wfB unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def by blast
  have ctdA: "\<And>ctorName dtName tyVars payload.
                fmlookup (TE_DataCtors ?envA) ctorName = Some (dtName, tyVars, payload) \<Longrightarrow>
                distinct tyVars"
    using wfA unfolding tyenv_well_formed_def tyenv_ctor_tyvars_distinct_def by blast
  have ctdB: "\<And>ctorName dtName tyVars payload.
                fmlookup (TE_DataCtors ?envB) ctorName = Some (dtName, tyVars, payload) \<Longrightarrow>
                distinct tyVars"
    using wfB unfolding tyenv_well_formed_def tyenv_ctor_tyvars_distinct_def by blast
  have btcA: "\<And>dtName ctors ctorName.
                fmlookup (TE_DataCtorsByType ?envA) dtName = Some ctors \<Longrightarrow>
                (ctorName \<in> set ctors)
                  = (\<exists>tyVars payload.
                       fmlookup (TE_DataCtors ?envA) ctorName = Some (dtName, tyVars, payload))"
    using wfA unfolding tyenv_well_formed_def tyenv_ctors_by_type_consistent_def by blast
  have btcB: "\<And>dtName ctors ctorName.
                fmlookup (TE_DataCtorsByType ?envB) dtName = Some ctors \<Longrightarrow>
                (ctorName \<in> set ctors)
                  = (\<exists>tyVars payload.
                       fmlookup (TE_DataCtors ?envB) ctorName = Some (dtName, tyVars, payload))"
    using wfB unfolding tyenv_well_formed_def tyenv_ctors_by_type_consistent_def by blast
  have ftwkA: "\<And>funName info. fmlookup (TE_Functions ?envA) funName = Some info \<Longrightarrow>
                 (\<forall>ty \<in> fst ` set (FI_TmArgs info).
                    is_well_kinded (?envA \<lparr> TE_TypeVars :=
                                            TE_AbstractTypes ?envA
                                            |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
                 \<and> is_well_kinded (?envA \<lparr> TE_TypeVars :=
                                           TE_AbstractTypes ?envA
                                           |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                                  (FI_ReturnType info)"
    using wfA unfolding tyenv_well_formed_def tyenv_fun_types_well_kinded_def by blast
  have ftwkB: "\<And>funName info. fmlookup (TE_Functions ?envB) funName = Some info \<Longrightarrow>
                 (\<forall>ty \<in> fst ` set (FI_TmArgs info).
                    is_well_kinded (?envB \<lparr> TE_TypeVars :=
                                            TE_AbstractTypes ?envB
                                            |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
                 \<and> is_well_kinded (?envB \<lparr> TE_TypeVars :=
                                           TE_AbstractTypes ?envB
                                           |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                                  (FI_ReturnType info)"
    using wfB unfolding tyenv_well_formed_def tyenv_fun_types_well_kinded_def by blast
  have ftdA: "\<And>funName info. fmlookup (TE_Functions ?envA) funName = Some info \<Longrightarrow>
                distinct (FI_TyArgs info)"
    using wfA unfolding tyenv_well_formed_def tyenv_fun_tyvars_distinct_def by blast
  have ftdB: "\<And>funName info. fmlookup (TE_Functions ?envB) funName = Some info \<Longrightarrow>
                distinct (FI_TyArgs info)"
    using wfB unfolding tyenv_well_formed_def tyenv_fun_tyvars_distinct_def by blast
  have fgcA: "\<And>funName info. fmlookup (TE_Functions ?envA) funName = Some info \<Longrightarrow>
                FI_Ghost info = NotGhost \<Longrightarrow>
                (\<forall>ty \<in> fst ` set (FI_TmArgs info).
                   is_runtime_type
                     (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA
                                             |\<union>| fset_of_list (FI_TyArgs info),
                              TE_RuntimeTypeVars :=
                                (TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA)
                                |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
                \<and> is_runtime_type
                    (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA
                                            |\<union>| fset_of_list (FI_TyArgs info),
                             TE_RuntimeTypeVars :=
                               (TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA)
                               |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                    (FI_ReturnType info)"
    using wfA
    unfolding tyenv_well_formed_def tyenv_fun_ghost_constraint_def Let_def by blast
  have fgcB: "\<And>funName info. fmlookup (TE_Functions ?envB) funName = Some info \<Longrightarrow>
                FI_Ghost info = NotGhost \<Longrightarrow>
                (\<forall>ty \<in> fst ` set (FI_TmArgs info).
                   is_runtime_type
                     (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB
                                             |\<union>| fset_of_list (FI_TyArgs info),
                              TE_RuntimeTypeVars :=
                                (TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB)
                                |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
                \<and> is_runtime_type
                    (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB
                                            |\<union>| fset_of_list (FI_TyArgs info),
                             TE_RuntimeTypeVars :=
                               (TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB)
                               |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                    (FI_ReturnType info)"
    using wfB
    unfolding tyenv_well_formed_def tyenv_fun_ghost_constraint_def Let_def by blast
  have nprA: "\<And>ctorName dtName tyVars payload.
                fmlookup (TE_DataCtors ?envA) ctorName = Some (dtName, tyVars, payload) \<Longrightarrow>
                dtName |\<notin>| TE_GhostDatatypes ?envA \<Longrightarrow>
                is_runtime_type
                  (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA |\<union>| fset_of_list tyVars,
                           TE_RuntimeTypeVars :=
                             (TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA)
                             |\<union>| fset_of_list tyVars \<rparr>) payload"
    using wfA
    unfolding tyenv_well_formed_def tyenv_nonghost_payloads_runtime_def by blast
  have nprB: "\<And>ctorName dtName tyVars payload.
                fmlookup (TE_DataCtors ?envB) ctorName = Some (dtName, tyVars, payload) \<Longrightarrow>
                dtName |\<notin>| TE_GhostDatatypes ?envB \<Longrightarrow>
                is_runtime_type
                  (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB |\<union>| fset_of_list tyVars,
                           TE_RuntimeTypeVars :=
                             (TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB)
                             |\<union>| fset_of_list tyVars \<rparr>) payload"
    using wfB
    unfolding tyenv_well_formed_def tyenv_nonghost_payloads_runtime_def by blast
  have gdsubA: "TE_GhostDatatypes (CM_TyEnv a) |\<subseteq>| fmdom (TE_Datatypes (CM_TyEnv a))"
    using wfA unfolding tyenv_well_formed_def tyenv_ghost_datatypes_subset_def by simp
  have gdsubB: "TE_GhostDatatypes (CM_TyEnv b) |\<subseteq>| fmdom (TE_Datatypes (CM_TyEnv b))"
    using wfB unfolding tyenv_well_formed_def tyenv_ghost_datatypes_subset_def by simp
  have dneA0: "tyenv_datatypes_nonempty ?envA"
    using wfA unfolding tyenv_well_formed_def by blast
  have dneB0: "tyenv_datatypes_nonempty ?envB"
    using wfB unfolding tyenv_well_formed_def by blast
  have dneA: "\<And>dt. dt |\<in>| fmdom (TE_Datatypes ?envA) \<Longrightarrow>
                \<exists>c cs. fmlookup (TE_DataCtorsByType ?envA) dt = Some (c # cs)"
    using tyenv_datatypes_nonempty_first_ctor[OF dneA0] by blast
  have dneB: "\<And>dt. dt |\<in>| fmdom (TE_Datatypes ?envB) \<Longrightarrow>
                \<exists>c cs. fmlookup (TE_DataCtorsByType ?envB) dt = Some (c # cs)"
    using tyenv_datatypes_nonempty_first_ctor[OF dneB0] by blast
  have dneA2: "\<And>dt ctors. fmlookup (TE_DataCtorsByType ?envA) dt = Some ctors \<Longrightarrow>
                 ctors \<noteq> []"
    using dneA0 unfolding tyenv_datatypes_nonempty_def by blast
  have dneB2: "\<And>dt ctors. fmlookup (TE_DataCtorsByType ?envB) dt = Some ctors \<Longrightarrow>
                 ctors \<noteq> []"
    using dneB0 unfolding tyenv_datatypes_nonempty_def by blast

  show ?thesis
    unfolding tyenv_well_formed_def
  proof (intro conjI)
    show "tyenv_vars_well_kinded ?mid"
      unfolding tyenv_vars_well_kinded_def
    proof (intro conjI allI impI)
      fix name ty assume "fmlookup (TE_LocalVars ?mid) name = Some ty"
      then show "is_well_kinded ?mid ty" by (simp add: fM(1))
    next
      fix name ty assume lk: "fmlookup (TE_GlobalVars ?mid) name = Some ty"
      from gv_cases[OF lk]
      show "is_well_kinded (?mid \<lparr> TE_TypeVars := TE_AbstractTypes ?mid \<rparr>) ty"
      proof
        assume lkA: "fmlookup (TE_GlobalVars ?envA) name = Some ty"
        show ?thesis
          by (rule link_side_wk_transfer[OF linkA linkM subA gvwkA[OF lkA]])
             (auto simp: absa)
      next
        assume lkB: "fmlookup (TE_GlobalVars ?envB) name = Some ty"
        show ?thesis
          by (rule link_side_wk_transfer[OF linkB linkM subB gvwkB[OF lkB]])
             (auto simp: absb)
      qed
    qed
  next
    show "tyenv_vars_runtime ?mid"
      unfolding tyenv_vars_runtime_def
    proof (intro conjI allI impI)
      fix name ty
      assume "fmlookup (TE_LocalVars ?mid) name = Some ty
                \<and> name |\<notin>| TE_GhostLocals ?mid"
      then show "is_runtime_type ?mid ty" by (simp add: fM(1))
    next
      fix name ty
      assume asm: "fmlookup (TE_GlobalVars ?mid) name = Some ty
                     \<and> name |\<notin>| TE_GhostGlobals ?mid"
      then have lk: "fmlookup (TE_GlobalVars ?mid) name = Some ty"
            and ng: "name |\<notin>| TE_GhostGlobals (CM_TyEnv m)"
        by simp_all
      from gv_cases[OF lk]
      show "is_runtime_type
              (?mid \<lparr> TE_TypeVars := TE_AbstractTypes ?mid,
                      TE_RuntimeTypeVars :=
                        TE_AbstractTypes ?mid |\<inter>| TE_RuntimeTypeVars ?mid \<rparr>) ty"
      proof
        assume lkA: "fmlookup (TE_GlobalVars ?envA) name = Some ty"
        have "name |\<in>| fmdom (TE_GlobalVars ?envA)" using lkA by (rule fmdomI)
        then have "name |\<in>| fmdom (TE_GlobalVars (CM_TyEnv a))" by simp
        then have ngA: "name |\<notin>| TE_GhostGlobals ?envA"
          using ggA ng by simp
        have rt1: "is_runtime_type
                     (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA,
                              TE_RuntimeTypeVars :=
                                TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA \<rparr>) ty"
          using gvrtA[OF lkA ngA] .
        have "is_well_kinded
                (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA,
                         TE_RuntimeTypeVars :=
                           TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA \<rparr>) ty
              = is_well_kinded (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA \<rparr>) ty"
          by (intro is_well_kinded_cong_env) simp_all
        then have wk1: "is_well_kinded
                          (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA,
                                   TE_RuntimeTypeVars :=
                                     TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA \<rparr>) ty"
          using gvwkA[OF lkA] by simp
        show ?thesis
          by (rule link_side_rt_transfer[OF linkA linkM subA ghostOK wk1 rt1])
             (auto simp: absa absb)
      next
        assume lkB: "fmlookup (TE_GlobalVars ?envB) name = Some ty"
        have "name |\<in>| fmdom (TE_GlobalVars ?envB)" using lkB by (rule fmdomI)
        then have "name |\<in>| fmdom (TE_GlobalVars (CM_TyEnv b))" by simp
        then have ngB: "name |\<notin>| TE_GhostGlobals ?envB"
          using ggB ng by simp
        have rt1: "is_runtime_type
                     (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB,
                              TE_RuntimeTypeVars :=
                                TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB \<rparr>) ty"
          using gvrtB[OF lkB ngB] .
        have "is_well_kinded
                (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB,
                         TE_RuntimeTypeVars :=
                           TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB \<rparr>) ty
              = is_well_kinded (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB \<rparr>) ty"
          by (intro is_well_kinded_cong_env) simp_all
        then have wk1: "is_well_kinded
                          (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB,
                                   TE_RuntimeTypeVars :=
                                     TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB \<rparr>) ty"
          using gvwkB[OF lkB] by simp
        show ?thesis
          by (rule link_side_rt_transfer[OF linkB linkM subB ghostOK wk1 rt1])
             (auto simp: absa absb)
      qed
    qed
  next
    show "tyenv_ghost_vars_subset ?mid"
      unfolding tyenv_ghost_vars_subset_def
    proof (intro conjI)
      show "TE_GhostLocals ?mid |\<subseteq>| fmdom (TE_LocalVars ?mid)"
        by (simp add: fM(3))
      show "TE_GhostGlobals ?mid |\<subseteq>| fmdom (TE_GlobalVars ?mid)"
      proof
        fix name assume "name |\<in>| TE_GhostGlobals ?mid"
        then have "name |\<in>| TE_GhostGlobals (CM_TyEnv a)
                     \<or> name |\<in>| TE_GhostGlobals (CM_TyEnv b)"
          using gsplit(4) by auto
        then have "name |\<in>| fmdom (TE_GlobalVars (CM_TyEnv a))
                     \<or> name |\<in>| fmdom (TE_GlobalVars (CM_TyEnv b))"
          using ggsubA ggsubB by (auto dest: fsubsetD)
        then show "name |\<in>| fmdom (TE_GlobalVars ?mid)"
          by (auto simp: fmadd_drop_dom)
      qed
    qed
  next
    show "tyenv_return_type_well_kinded ?mid"
      unfolding tyenv_return_type_well_kinded_def by (simp add: fM(9))
  next
    show "tyenv_return_type_runtime ?mid"
      unfolding tyenv_return_type_runtime_def by (simp add: fM(9))
  next
    show "tyenv_ctors_consistent ?mid"
      unfolding tyenv_ctors_consistent_def
    proof (intro allI impI)
      fix ctorName dtName tyVars payload
      assume lk: "fmlookup (TE_DataCtors ?mid) ctorName = Some (dtName, tyVars, payload)"
      from dc_cases[OF lk]
      show "fmlookup (TE_Datatypes ?mid) dtName = Some (length tyVars)"
      proof
        assume "fmlookup (TE_DataCtors ?envA) ctorName = Some (dtName, tyVars, payload)"
        then have "fmlookup (TE_Datatypes (CM_TyEnv a)) dtName = Some (length tyVars)"
          using ccA by simp
        then have "fmlookup (TE_Datatypes (CM_TyEnv m)) dtName = Some (length tyVars)"
          using link_modules_decl_submaps(3)[OF linkA linkM subA] by blast
        then show ?thesis by simp
      next
        assume "fmlookup (TE_DataCtors ?envB) ctorName = Some (dtName, tyVars, payload)"
        then have "fmlookup (TE_Datatypes (CM_TyEnv b)) dtName = Some (length tyVars)"
          using ccB by simp
        then have "fmlookup (TE_Datatypes (CM_TyEnv m)) dtName = Some (length tyVars)"
          using link_modules_decl_submaps(3)[OF linkB linkM subB] by blast
        then show ?thesis by simp
      qed
    qed
  next
    show "tyenv_payloads_well_kinded ?mid"
      unfolding tyenv_payloads_well_kinded_def
    proof (intro allI impI)
      fix ctorName dtName tyVars payload
      assume lk: "fmlookup (TE_DataCtors ?mid) ctorName = Some (dtName, tyVars, payload)"
      from dc_cases[OF lk]
      show "is_well_kinded (?mid \<lparr> TE_TypeVars :=
                                   TE_AbstractTypes ?mid |\<union>| fset_of_list tyVars \<rparr>) payload"
      proof
        assume lkA: "fmlookup (TE_DataCtors ?envA) ctorName = Some (dtName, tyVars, payload)"
        show ?thesis
          by (rule link_side_wk_transfer[OF linkA linkM subA pwkA[OF lkA]])
             (auto simp: absa)
      next
        assume lkB: "fmlookup (TE_DataCtors ?envB) ctorName = Some (dtName, tyVars, payload)"
        show ?thesis
          by (rule link_side_wk_transfer[OF linkB linkM subB pwkB[OF lkB]])
             (auto simp: absb)
      qed
    qed
  next
    show "tyenv_ctor_tyvars_distinct ?mid"
      unfolding tyenv_ctor_tyvars_distinct_def
    proof (intro allI impI)
      fix ctorName dtName tyVars payload
      assume lk: "fmlookup (TE_DataCtors ?mid) ctorName = Some (dtName, tyVars, payload)"
      show "distinct tyVars"
        using dc_cases[OF lk] ctdA ctdB by blast
    qed
  next
    show "tyenv_ctors_by_type_consistent ?mid"
      unfolding tyenv_ctors_by_type_consistent_def
    proof (intro allI impI)
      fix dtName ctors ctorName
      assume "fmlookup (TE_DataCtorsByType ?mid) dtName = Some ctors"
      then have btM: "fmlookup (TE_DataCtorsByType (CM_TyEnv m)) dtName = Some ctors"
        by simp
      show "(ctorName \<in> set ctors)
              = (\<exists>tyVars payload.
                   fmlookup (TE_DataCtors ?mid) ctorName = Some (dtName, tyVars, payload))"
      proof
        assume mem: "ctorName \<in> set ctors"
        obtain z where z_in: "z \<in> set ms"
                   and z_bt: "fmlookup (TE_DataCtorsByType (CM_TyEnv z)) dtName = Some ctors"
          using fmlist_union_lookup[OF btdisjM] btM[unfolded fM(16)] by auto
        from z_in setMS have "z \<in> set as \<or> z \<in> set bs" by auto
        then show "\<exists>tyVars payload.
                     fmlookup (TE_DataCtors ?mid) ctorName = Some (dtName, tyVars, payload)"
        proof
          assume z_as: "z \<in> set as"
          have btA': "fmlookup (TE_DataCtorsByType ?envA) dtName = Some ctors"
            using fmlist_union_lookup[OF btdisjA] z_as z_bt by (auto simp: fA(16))
          obtain tyVars payload where
              lkA: "fmlookup (TE_DataCtors ?envA) ctorName = Some (dtName, tyVars, payload)"
            using btcA[OF btA'] mem by blast
          have "fmlookup (TE_DataCtors ?mid) ctorName = Some (dtName, tyVars, payload)"
            using lkA fmdomI[OF lkA] by (simp add: fmadd_drop_lookup)
          then show ?thesis by blast
        next
          assume z_bs: "z \<in> set bs"
          have btB': "fmlookup (TE_DataCtorsByType ?envB) dtName = Some ctors"
            using fmlist_union_lookup[OF btdisjB] z_bs z_bt by (auto simp: fB(16))
          obtain tyVarsB payloadB where
              lkB: "fmlookup (TE_DataCtors ?envB) ctorName = Some (dtName, tyVarsB, payloadB)"
            using btcB[OF btB'] mem by blast
          show ?thesis
          proof (cases "ctorName |\<in>| fmdom (TE_DataCtors ?envA)")
            case False
            have "ctorName |\<in>| fmdom (TE_DataCtors ?envB)"
              using lkB by (rule fmdomI)
            then have "fmlookup (TE_DataCtors ?mid) ctorName
                         = Some (dtName, tyVarsB, payloadB)"
              using lkB False by (auto simp: fmadd_drop_lookup)
            then show ?thesis by blast
          next
            case True
            \<comment> \<open>Both sides declare this ctor: same module, same raw entry.\<close>
            then obtain eA where lkA_e: "fmlookup (TE_DataCtors ?envA) ctorName = Some eA"
              by (auto simp: fmlookup_dom_iff)
            obtain eA0 where rawA: "fmlookup (TE_DataCtors (CM_TyEnv a)) ctorName = Some eA0"
                and eA_eq: "eA = apply_subst_to_datactor (CM_TypeSubst a) eA0"
              using lkA_e by (cases "fmlookup (TE_DataCtors (CM_TyEnv a)) ctorName") auto
            obtain eB0 where rawB: "fmlookup (TE_DataCtors (CM_TyEnv b)) ctorName = Some eB0"
                and eB_eq: "(dtName, tyVarsB, payloadB)
                              = apply_subst_to_datactor (CM_TypeSubst b) eB0"
              using lkB by (cases "fmlookup (TE_DataCtors (CM_TyEnv b)) ctorName") auto
            have e_eq: "eA0 = eB0"
              by (rule link_pair_shared_lookup[OF dcdisjA dcdisjB dcdisjM setMS
                        rawA[unfolded fA(15)] rawB[unfolded fB(15)]])
            obtain dt0 tv0 pl0 where e0shape: "eB0 = (dt0, tv0, pl0)"
              by (cases eB0) auto
            have "dt0 = dtName"
              using eB_eq e0shape by (auto simp: apply_subst_to_datactor_def)
            then have eA_shape: "eA = (dtName, tv0, apply_subst (CM_TypeSubst a) pl0)"
              using eA_eq e_eq e0shape by (simp add: apply_subst_to_datactor_def)
            have "fmlookup (TE_DataCtors ?mid) ctorName = Some eA"
              using lkA_e True by (simp add: fmadd_drop_lookup)
            then show ?thesis using eA_shape by auto
          qed
        qed
      next
        assume "\<exists>tyVars payload.
                  fmlookup (TE_DataCtors ?mid) ctorName = Some (dtName, tyVars, payload)"
        then obtain tyVars payload where
            lk2: "fmlookup (TE_DataCtors ?mid) ctorName = Some (dtName, tyVars, payload)"
          by blast
        from dc_cases[OF lk2] show "ctorName \<in> set ctors"
        proof
          assume lkA: "fmlookup (TE_DataCtors ?envA) ctorName = Some (dtName, tyVars, payload)"
          have "fmlookup (TE_Datatypes ?envA) dtName = Some (length tyVars)"
            using ccA[OF lkA] .
          then have "dtName |\<in>| fmdom (TE_Datatypes ?envA)"
            by (auto intro: fmdomI)
          then obtain c cs where
              btA': "fmlookup (TE_DataCtorsByType ?envA) dtName = Some (c # cs)"
            using dneA by blast
          then have "fmlookup (TE_DataCtorsByType (CM_TyEnv a)) dtName = Some (c # cs)"
            by simp
          then have "fmlookup (TE_DataCtorsByType (CM_TyEnv m)) dtName = Some (c # cs)"
            using link_modules_decl_submaps(5)[OF linkA linkM subA] by blast
          with btM have ctors_eq: "ctors = c # cs" by simp
          show "ctorName \<in> set ctors"
            using btcA[OF btA'] lkA ctors_eq by blast
        next
          assume lkB: "fmlookup (TE_DataCtors ?envB) ctorName = Some (dtName, tyVars, payload)"
          have "fmlookup (TE_Datatypes ?envB) dtName = Some (length tyVars)"
            using ccB[OF lkB] .
          then have "dtName |\<in>| fmdom (TE_Datatypes ?envB)"
            by (auto intro: fmdomI)
          then obtain c cs where
              btB': "fmlookup (TE_DataCtorsByType ?envB) dtName = Some (c # cs)"
            using dneB by blast
          then have "fmlookup (TE_DataCtorsByType (CM_TyEnv b)) dtName = Some (c # cs)"
            by simp
          then have "fmlookup (TE_DataCtorsByType (CM_TyEnv m)) dtName = Some (c # cs)"
            using link_modules_decl_submaps(5)[OF linkB linkM subB] by blast
          with btM have ctors_eq: "ctors = c # cs" by simp
          show "ctorName \<in> set ctors"
            using btcB[OF btB'] lkB ctors_eq by blast
        qed
      qed
    qed
  next
    show "tyenv_fun_types_well_kinded ?mid"
      unfolding tyenv_fun_types_well_kinded_def
    proof (intro allI impI)
      fix funName info
      assume lk: "fmlookup (TE_Functions ?mid) funName = Some info"
      from fn_cases[OF lk]
      show "(\<forall>ty \<in> fst ` set (FI_TmArgs info).
               is_well_kinded (?mid \<lparr> TE_TypeVars :=
                                      TE_AbstractTypes ?mid
                                      |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
            \<and> is_well_kinded (?mid \<lparr> TE_TypeVars :=
                                     TE_AbstractTypes ?mid
                                     |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                             (FI_ReturnType info)"
      proof
        assume lkA: "fmlookup (TE_Functions ?envA) funName = Some info"
        have step: "\<And>ty. is_well_kinded (?envA \<lparr> TE_TypeVars :=
                                                  TE_AbstractTypes ?envA
                                                  |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty
                      \<Longrightarrow> is_well_kinded (?mid \<lparr> TE_TypeVars :=
                                                 TE_AbstractTypes ?mid
                                                 |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
        proof -
          fix ty
          assume w: "is_well_kinded (?envA \<lparr> TE_TypeVars :=
                                             TE_AbstractTypes ?envA
                                             |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
          show "is_well_kinded (?mid \<lparr> TE_TypeVars :=
                                       TE_AbstractTypes ?mid
                                       |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
            by (rule link_side_wk_transfer[OF linkA linkM subA w]) (auto simp: absa)
        qed
        show ?thesis using ftwkA[OF lkA] step by blast
      next
        assume lkB: "fmlookup (TE_Functions ?envB) funName = Some info"
        have step: "\<And>ty. is_well_kinded (?envB \<lparr> TE_TypeVars :=
                                                  TE_AbstractTypes ?envB
                                                  |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty
                      \<Longrightarrow> is_well_kinded (?mid \<lparr> TE_TypeVars :=
                                                 TE_AbstractTypes ?mid
                                                 |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
        proof -
          fix ty
          assume w: "is_well_kinded (?envB \<lparr> TE_TypeVars :=
                                             TE_AbstractTypes ?envB
                                             |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
          show "is_well_kinded (?mid \<lparr> TE_TypeVars :=
                                       TE_AbstractTypes ?mid
                                       |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
            by (rule link_side_wk_transfer[OF linkB linkM subB w]) (auto simp: absb)
        qed
        show ?thesis using ftwkB[OF lkB] step by blast
      qed
    qed
  next
    show "tyenv_fun_tyvars_distinct ?mid"
      unfolding tyenv_fun_tyvars_distinct_def
    proof (intro allI impI)
      fix funName info
      assume lk: "fmlookup (TE_Functions ?mid) funName = Some info"
      show "distinct (FI_TyArgs info)"
        using fn_cases[OF lk] ftdA ftdB by blast
    qed
  next
    show "tyenv_fun_ghost_constraint ?mid"
      unfolding tyenv_fun_ghost_constraint_def Let_def
    proof (intro allI impI)
      fix funName info
      assume asm: "fmlookup (TE_Functions ?mid) funName = Some info
                     \<and> FI_Ghost info = NotGhost"
      then have lk: "fmlookup (TE_Functions ?mid) funName = Some info"
            and ng: "FI_Ghost info = NotGhost"
        by simp_all
      from fn_cases[OF lk]
      show "(\<forall>ty \<in> fst ` set (FI_TmArgs info).
               is_runtime_type
                 (?mid \<lparr> TE_TypeVars := TE_AbstractTypes ?mid
                                        |\<union>| fset_of_list (FI_TyArgs info),
                         TE_RuntimeTypeVars :=
                           (TE_AbstractTypes ?mid |\<inter>| TE_RuntimeTypeVars ?mid)
                           |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
            \<and> is_runtime_type
                (?mid \<lparr> TE_TypeVars := TE_AbstractTypes ?mid
                                       |\<union>| fset_of_list (FI_TyArgs info),
                        TE_RuntimeTypeVars :=
                          (TE_AbstractTypes ?mid |\<inter>| TE_RuntimeTypeVars ?mid)
                          |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                (FI_ReturnType info)"
      proof
        assume lkA: "fmlookup (TE_Functions ?envA) funName = Some info"
        have step: "\<And>ty.
                is_runtime_type
                  (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA
                                          |\<union>| fset_of_list (FI_TyArgs info),
                           TE_RuntimeTypeVars :=
                             (TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA)
                             |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty
                \<Longrightarrow> is_well_kinded (?envA \<lparr> TE_TypeVars :=
                                            TE_AbstractTypes ?envA
                                            |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty
                \<Longrightarrow> is_runtime_type
                      (?mid \<lparr> TE_TypeVars := TE_AbstractTypes ?mid
                                             |\<union>| fset_of_list (FI_TyArgs info),
                              TE_RuntimeTypeVars :=
                                (TE_AbstractTypes ?mid |\<inter>| TE_RuntimeTypeVars ?mid)
                                |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
        proof -
          fix ty
          assume r: "is_runtime_type
                       (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA
                                               |\<union>| fset_of_list (FI_TyArgs info),
                                TE_RuntimeTypeVars :=
                                  (TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA)
                                  |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
             and w0: "is_well_kinded (?envA \<lparr> TE_TypeVars :=
                                              TE_AbstractTypes ?envA
                                              |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
          have "is_well_kinded
                  (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA
                                          |\<union>| fset_of_list (FI_TyArgs info),
                           TE_RuntimeTypeVars :=
                             (TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA)
                             |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty
                = is_well_kinded (?envA \<lparr> TE_TypeVars :=
                                          TE_AbstractTypes ?envA
                                          |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
            by (intro is_well_kinded_cong_env) simp_all
          then have w: "is_well_kinded
                          (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA
                                                  |\<union>| fset_of_list (FI_TyArgs info),
                                   TE_RuntimeTypeVars :=
                                     (TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA)
                                     |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
            using w0 by simp
          show "is_runtime_type
                  (?mid \<lparr> TE_TypeVars := TE_AbstractTypes ?mid
                                         |\<union>| fset_of_list (FI_TyArgs info),
                          TE_RuntimeTypeVars :=
                            (TE_AbstractTypes ?mid |\<inter>| TE_RuntimeTypeVars ?mid)
                            |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
            by (rule link_side_rt_transfer[OF linkA linkM subA ghostOK w r])
               (auto simp: absa absb)
        qed
        show ?thesis using fgcA[OF lkA ng] ftwkA[OF lkA] step by blast
      next
        assume lkB: "fmlookup (TE_Functions ?envB) funName = Some info"
        have step: "\<And>ty.
                is_runtime_type
                  (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB
                                          |\<union>| fset_of_list (FI_TyArgs info),
                           TE_RuntimeTypeVars :=
                             (TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB)
                             |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty
                \<Longrightarrow> is_well_kinded (?envB \<lparr> TE_TypeVars :=
                                            TE_AbstractTypes ?envB
                                            |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty
                \<Longrightarrow> is_runtime_type
                      (?mid \<lparr> TE_TypeVars := TE_AbstractTypes ?mid
                                             |\<union>| fset_of_list (FI_TyArgs info),
                              TE_RuntimeTypeVars :=
                                (TE_AbstractTypes ?mid |\<inter>| TE_RuntimeTypeVars ?mid)
                                |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
        proof -
          fix ty
          assume r: "is_runtime_type
                       (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB
                                               |\<union>| fset_of_list (FI_TyArgs info),
                                TE_RuntimeTypeVars :=
                                  (TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB)
                                  |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
             and w0: "is_well_kinded (?envB \<lparr> TE_TypeVars :=
                                              TE_AbstractTypes ?envB
                                              |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
          have "is_well_kinded
                  (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB
                                          |\<union>| fset_of_list (FI_TyArgs info),
                           TE_RuntimeTypeVars :=
                             (TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB)
                             |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty
                = is_well_kinded (?envB \<lparr> TE_TypeVars :=
                                          TE_AbstractTypes ?envB
                                          |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
            by (intro is_well_kinded_cong_env) simp_all
          then have w: "is_well_kinded
                          (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB
                                                  |\<union>| fset_of_list (FI_TyArgs info),
                                   TE_RuntimeTypeVars :=
                                     (TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB)
                                     |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
            using w0 by simp
          show "is_runtime_type
                  (?mid \<lparr> TE_TypeVars := TE_AbstractTypes ?mid
                                         |\<union>| fset_of_list (FI_TyArgs info),
                          TE_RuntimeTypeVars :=
                            (TE_AbstractTypes ?mid |\<inter>| TE_RuntimeTypeVars ?mid)
                            |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
            by (rule link_side_rt_transfer[OF linkB linkM subB ghostOK w r])
               (auto simp: absa absb)
        qed
        show ?thesis using fgcB[OF lkB ng] ftwkB[OF lkB] step by blast
      qed
    qed
  next
    show "tyenv_nonghost_payloads_runtime ?mid"
      unfolding tyenv_nonghost_payloads_runtime_def
    proof (intro allI impI)
      fix ctorName dtName tyVars payload
      assume lk: "fmlookup (TE_DataCtors ?mid) ctorName = Some (dtName, tyVars, payload)"
         and ng: "dtName |\<notin>| TE_GhostDatatypes ?mid"
      have ngM: "dtName |\<notin>| TE_GhostDatatypes (CM_TyEnv m)" using ng by simp
      from dc_cases[OF lk]
      show "is_runtime_type
              (?mid \<lparr> TE_TypeVars := TE_AbstractTypes ?mid |\<union>| fset_of_list tyVars,
                      TE_RuntimeTypeVars :=
                        (TE_AbstractTypes ?mid |\<inter>| TE_RuntimeTypeVars ?mid)
                        |\<union>| fset_of_list tyVars \<rparr>) payload"
      proof
        assume lkA: "fmlookup (TE_DataCtors ?envA) ctorName = Some (dtName, tyVars, payload)"
        have "fmlookup (TE_Datatypes ?envA) dtName = Some (length tyVars)"
          using ccA[OF lkA] .
        then have "dtName |\<in>| fmdom (TE_Datatypes (CM_TyEnv a))"
          by (auto intro: fmdomI)
        then have ngA: "dtName |\<notin>| TE_GhostDatatypes ?envA"
          using gdA ngM by simp
        have rt1: "is_runtime_type
                     (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA |\<union>| fset_of_list tyVars,
                              TE_RuntimeTypeVars :=
                                (TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA)
                                |\<union>| fset_of_list tyVars \<rparr>) payload"
          using nprA[OF lkA ngA] .
        have "is_well_kinded
                (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA |\<union>| fset_of_list tyVars,
                         TE_RuntimeTypeVars :=
                           (TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA)
                           |\<union>| fset_of_list tyVars \<rparr>) payload
              = is_well_kinded (?envA \<lparr> TE_TypeVars :=
                                        TE_AbstractTypes ?envA |\<union>| fset_of_list tyVars \<rparr>) payload"
          by (intro is_well_kinded_cong_env) simp_all
        then have wk1: "is_well_kinded
                          (?envA \<lparr> TE_TypeVars :=
                                     TE_AbstractTypes ?envA |\<union>| fset_of_list tyVars,
                                   TE_RuntimeTypeVars :=
                                     (TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA)
                                     |\<union>| fset_of_list tyVars \<rparr>) payload"
          using pwkA[OF lkA] by simp
        show ?thesis
          by (rule link_side_rt_transfer[OF linkA linkM subA ghostOK wk1 rt1])
             (auto simp: absa absb)
      next
        assume lkB: "fmlookup (TE_DataCtors ?envB) ctorName = Some (dtName, tyVars, payload)"
        have "fmlookup (TE_Datatypes ?envB) dtName = Some (length tyVars)"
          using ccB[OF lkB] .
        then have "dtName |\<in>| fmdom (TE_Datatypes (CM_TyEnv b))"
          by (auto intro: fmdomI)
        then have ngB: "dtName |\<notin>| TE_GhostDatatypes ?envB"
          using gdB ngM by simp
        have rt1: "is_runtime_type
                     (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB |\<union>| fset_of_list tyVars,
                              TE_RuntimeTypeVars :=
                                (TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB)
                                |\<union>| fset_of_list tyVars \<rparr>) payload"
          using nprB[OF lkB ngB] .
        have "is_well_kinded
                (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB |\<union>| fset_of_list tyVars,
                         TE_RuntimeTypeVars :=
                           (TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB)
                           |\<union>| fset_of_list tyVars \<rparr>) payload
              = is_well_kinded (?envB \<lparr> TE_TypeVars :=
                                        TE_AbstractTypes ?envB |\<union>| fset_of_list tyVars \<rparr>) payload"
          by (intro is_well_kinded_cong_env) simp_all
        then have wk1: "is_well_kinded
                          (?envB \<lparr> TE_TypeVars :=
                                     TE_AbstractTypes ?envB |\<union>| fset_of_list tyVars,
                                   TE_RuntimeTypeVars :=
                                     (TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB)
                                     |\<union>| fset_of_list tyVars \<rparr>) payload"
          using pwkB[OF lkB] by simp
        show ?thesis
          by (rule link_side_rt_transfer[OF linkB linkM subB ghostOK wk1 rt1])
             (auto simp: absa absb)
      qed
    qed
  next
    show "tyenv_ghost_datatypes_subset ?mid"
      unfolding tyenv_ghost_datatypes_subset_def
    proof
      fix name assume "name |\<in>| TE_GhostDatatypes ?mid"
      then have "name |\<in>| TE_GhostDatatypes (CM_TyEnv a)
                   \<or> name |\<in>| TE_GhostDatatypes (CM_TyEnv b)"
        using gsplit(5) by auto
      then have "name |\<in>| fmdom (TE_Datatypes (CM_TyEnv a))
                   \<or> name |\<in>| fmdom (TE_Datatypes (CM_TyEnv b))"
        using gdsubA gdsubB by (auto dest: fsubsetD)
      then show "name |\<in>| fmdom (TE_Datatypes ?mid)"
        using dtdom by auto
    qed
  next
    show "tyenv_runtime_tyvars_subset ?mid"
      unfolding tyenv_runtime_tyvars_subset_def
    proof
      fix n assume "n |\<in>| TE_RuntimeTypeVars ?mid"
      then show "n |\<in>| TE_TypeVars ?mid"
        using rtvA rtvB by (auto dest: fsubsetD)
    qed
  next
    show "tyenv_abstract_types_subset ?mid"
      unfolding tyenv_abstract_types_subset_def by simp
  next
    have H: "\<And>dtName. dtName |\<in>| fmdom (TE_Datatypes ?mid) \<Longrightarrow>
               \<exists>ctorName ctors.
                 fmlookup (TE_DataCtorsByType ?mid) dtName = Some (ctorName # ctors)"
    proof -
      fix dtName assume "dtName |\<in>| fmdom (TE_Datatypes ?mid)"
      then have "dtName |\<in>| fmdom (TE_Datatypes (CM_TyEnv a))
                   \<or> dtName |\<in>| fmdom (TE_Datatypes (CM_TyEnv b))"
        using dtdom by auto
      then show "\<exists>ctorName ctors.
                   fmlookup (TE_DataCtorsByType ?mid) dtName = Some (ctorName # ctors)"
      proof
        assume "dtName |\<in>| fmdom (TE_Datatypes (CM_TyEnv a))"
        then have "dtName |\<in>| fmdom (TE_Datatypes ?envA)" by simp
        then obtain c cs where "fmlookup (TE_DataCtorsByType ?envA) dtName = Some (c # cs)"
          using dneA by blast
        then have "fmlookup (TE_DataCtorsByType (CM_TyEnv a)) dtName = Some (c # cs)"
          by simp
        then have "fmlookup (TE_DataCtorsByType (CM_TyEnv m)) dtName = Some (c # cs)"
          using link_modules_decl_submaps(5)[OF linkA linkM subA] by blast
        then show ?thesis by auto
      next
        assume "dtName |\<in>| fmdom (TE_Datatypes (CM_TyEnv b))"
        then have "dtName |\<in>| fmdom (TE_Datatypes ?envB)" by simp
        then obtain c cs where "fmlookup (TE_DataCtorsByType ?envB) dtName = Some (c # cs)"
          using dneB by blast
        then have "fmlookup (TE_DataCtorsByType (CM_TyEnv b)) dtName = Some (c # cs)"
          by simp
        then have "fmlookup (TE_DataCtorsByType (CM_TyEnv m)) dtName = Some (c # cs)"
          using link_modules_decl_submaps(5)[OF linkB linkM subB] by blast
        then show ?thesis by auto
      qed
    qed
    \<comment> \<open>Every TE_DataCtorsByType entry of the linked module comes from one of
        the member modules, hence from the a-side or the b-side, and each
        side's entries are nonempty.\<close>
    have H2: "\<And>dtName ctors.
                fmlookup (TE_DataCtorsByType ?mid) dtName = Some ctors \<Longrightarrow> ctors \<noteq> []"
    proof -
      fix dtName ctors
      assume lk: "fmlookup (TE_DataCtorsByType ?mid) dtName = Some ctors"
      have dM: "fmdisjoint_list (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) ms)"
        using link_modules_success_facts(1)[OF linkM]
        unfolding link_fields_disjoint_def by blast
      from lk have "fmlookup (fmlist_union
                       (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) ms)) dtName
                      = Some ctors"
        by (simp add: fM(16))
      then obtain x where x_in: "x \<in> set ms"
        and x_lk: "fmlookup (TE_DataCtorsByType (CM_TyEnv x)) dtName = Some ctors"
        using fmlist_union_lookup[OF dM] by auto
      from x_in setMS have "x \<in> set as \<or> x \<in> set bs" by auto
      then show "ctors \<noteq> []"
      proof
        assume xA: "x \<in> set as"
        have dA: "fmdisjoint_list (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) as)"
          using link_modules_success_facts(1)[OF linkA]
          unfolding link_fields_disjoint_def by blast
        have "fmlookup (fmlist_union
                (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) as)) dtName = Some ctors"
          using fmlist_union_lookup[OF dA] xA x_lk by auto
        then have "fmlookup (TE_DataCtorsByType ?envA) dtName = Some ctors"
          by (simp add: fA(16))
        then show ?thesis using dneA2 by blast
      next
        assume xB: "x \<in> set bs"
        have dB: "fmdisjoint_list (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) bs)"
          using link_modules_success_facts(1)[OF linkB]
          unfolding link_fields_disjoint_def by blast
        have "fmlookup (fmlist_union
                (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) bs)) dtName = Some ctors"
          using fmlist_union_lookup[OF dB] xB x_lk by auto
        then have "fmlookup (TE_DataCtorsByType ?envB) dtName = Some ctors"
          by (simp add: fB(16))
        then show ?thesis using dneB2 by blast
      qed
    qed
    show "tyenv_datatypes_nonempty ?mid"
      unfolding tyenv_datatypes_nonempty_def
    proof (intro conjI)
      show "fmdom (TE_Datatypes ?mid) |\<subseteq>| fmdom (TE_DataCtorsByType ?mid)"
        using H by (metis fmdomI fsubsetI)
      show "\<forall>dtName ctors.
              fmlookup (TE_DataCtorsByType ?mid) dtName = Some ctors \<longrightarrow> ctors \<noteq> []"
        using H2 by blast
    qed
  qed
qed


(* ========================================================================== *)
(* The declaration-axis extension into the mid env                            *)
(*                                                                            *)
(* normalize_module a's env, with its tyvar fields widened by b's, extends    *)
(* (tyenv_extends) into the mid env: the scope fields agree (both inert), the *)
(* a-side declaration entries survive verbatim (the overlay prefers the       *)
(* a-side), and the ghost markers agree on a-declared names (the ghost        *)
(* agreement lemmas - this is the module_ghost_subsets_ok hypothesis at       *)
(* work).                                                                     *)
(* ========================================================================== *)

lemma link_mid_env_extends:
  assumes linkA: "link_modules as = Inr a"
      and linkB: "link_modules bs = Inr b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
      and ghostOK: "\<forall>x \<in> set ms. module_ghost_subsets_ok x"
  shows "tyenv_extends
           ((CM_TyEnv (normalize_module a))
              \<lparr> TE_TypeVars := TE_TypeVars (CM_TyEnv a) |\<union>| TE_TypeVars (CM_TyEnv b),
                TE_RuntimeTypeVars :=
                  TE_RuntimeTypeVars (CM_TyEnv a) |\<union>| TE_RuntimeTypeVars (CM_TyEnv b) \<rparr>)
           (link_mid_env a b m)"
proof -
  note fA = link_modules_result_fields[OF linkA]
  note fM = link_modules_result_fields[OF linkM]
  have subA: "set as \<subseteq> set ms" using setMS by auto
  let ?envA = "(CM_TyEnv (normalize_module a))
                 \<lparr> TE_TypeVars := TE_TypeVars (CM_TyEnv a) |\<union>| TE_TypeVars (CM_TyEnv b),
                   TE_RuntimeTypeVars :=
                     TE_RuntimeTypeVars (CM_TyEnv a) |\<union>| TE_RuntimeTypeVars (CM_TyEnv b) \<rparr>"
  let ?mid = "link_mid_env a b m"

  \<comment> \<open>The a-side substituted families are submaps of the mid env's overlays.\<close>
  have gv_pres: "\<And>name ty. fmlookup (TE_GlobalVars ?envA) name = Some ty
                   \<Longrightarrow> fmlookup (TE_GlobalVars ?mid) name = Some ty"
  proof -
    fix name ty assume "fmlookup (TE_GlobalVars ?envA) name = Some ty"
    then have lk: "fmlookup (TE_GlobalVars (CM_TyEnv (normalize_module a))) name = Some ty"
      by simp
    then have "name |\<in>| fmdom (TE_GlobalVars (CM_TyEnv (normalize_module a)))"
      by (auto intro: fmdomI)
    then show "fmlookup (TE_GlobalVars ?mid) name = Some ty"
      using lk by (simp add: fmadd_drop_lookup)
  qed
  have fn_pres: "\<And>name info. fmlookup (TE_Functions ?envA) name = Some info
                   \<Longrightarrow> fmlookup (TE_Functions ?mid) name = Some info"
  proof -
    fix name info assume "fmlookup (TE_Functions ?envA) name = Some info"
    then have lk: "fmlookup (TE_Functions (CM_TyEnv (normalize_module a))) name = Some info"
      by simp
    then have "name |\<in>| fmdom (TE_Functions (CM_TyEnv (normalize_module a)))"
      by (auto intro: fmdomI)
    then show "fmlookup (TE_Functions ?mid) name = Some info"
      using lk by (simp add: fmadd_drop_lookup)
  qed
  have dc_pres: "\<And>name entry. fmlookup (TE_DataCtors ?envA) name = Some entry
                   \<Longrightarrow> fmlookup (TE_DataCtors ?mid) name = Some entry"
  proof -
    fix name entry assume "fmlookup (TE_DataCtors ?envA) name = Some entry"
    then have lk: "fmlookup (TE_DataCtors (CM_TyEnv (normalize_module a))) name = Some entry"
      by simp
    then have "name |\<in>| fmdom (TE_DataCtors (CM_TyEnv (normalize_module a)))"
      by (auto intro: fmdomI)
    then show "fmlookup (TE_DataCtors ?mid) name = Some entry"
      using lk by (simp add: fmadd_drop_lookup)
  qed
  have dt_pres: "\<And>name v. fmlookup (TE_Datatypes ?envA) name = Some v
                   \<Longrightarrow> fmlookup (TE_Datatypes ?mid) name = Some v"
  proof -
    fix name v assume "fmlookup (TE_Datatypes ?envA) name = Some v"
    then have "fmlookup (TE_Datatypes (CM_TyEnv a)) name = Some v" by simp
    then have "fmlookup (TE_Datatypes (CM_TyEnv m)) name = Some v"
      using link_modules_decl_submaps(3)[OF linkA linkM subA] by blast
    then show "fmlookup (TE_Datatypes ?mid) name = Some v" by simp
  qed
  have bt_pres: "\<And>name ctors. fmlookup (TE_DataCtorsByType ?envA) name = Some ctors
                   \<Longrightarrow> fmlookup (TE_DataCtorsByType ?mid) name = Some ctors"
  proof -
    fix name ctors assume "fmlookup (TE_DataCtorsByType ?envA) name = Some ctors"
    then have "fmlookup (TE_DataCtorsByType (CM_TyEnv a)) name = Some ctors" by simp
    then have "fmlookup (TE_DataCtorsByType (CM_TyEnv m)) name = Some ctors"
      using link_modules_decl_submaps(5)[OF linkA linkM subA] by blast
    then show "fmlookup (TE_DataCtorsByType ?mid) name = Some ctors" by simp
  qed

  \<comment> \<open>Ghost markers agree on a-declared names.\<close>
  have gg_agree: "\<And>name. name |\<in>| fmdom (TE_GlobalVars ?envA)
                    \<Longrightarrow> (name |\<in>| TE_GhostGlobals ?mid \<longleftrightarrow> name |\<in>| TE_GhostGlobals ?envA)"
  proof -
    fix name assume "name |\<in>| fmdom (TE_GlobalVars ?envA)"
    then have "name |\<in>| fmdom (TE_GlobalVars (CM_TyEnv a))"
      by (simp add: fmdom_fmmap)
    then have "name |\<in>| TE_GhostGlobals (CM_TyEnv m)
                 \<longleftrightarrow> name |\<in>| TE_GhostGlobals (CM_TyEnv a)"
      using link_ghost_globals_agree[OF linkA linkM subA ghostOK] by blast
    then show "name |\<in>| TE_GhostGlobals ?mid \<longleftrightarrow> name |\<in>| TE_GhostGlobals ?envA"
      by simp
  qed
  have gd_agree: "\<And>name. name |\<in>| fmdom (TE_Datatypes ?envA)
                    \<Longrightarrow> (name |\<in>| TE_GhostDatatypes ?mid \<longleftrightarrow> name |\<in>| TE_GhostDatatypes ?envA)"
  proof -
    fix name assume "name |\<in>| fmdom (TE_Datatypes ?envA)"
    then have "name |\<in>| fmdom (TE_Datatypes (CM_TyEnv a))" by simp
    then have "name |\<in>| TE_GhostDatatypes (CM_TyEnv m)
                 \<longleftrightarrow> name |\<in>| TE_GhostDatatypes (CM_TyEnv a)"
      using link_ghost_datatypes_agree[OF linkA linkM subA ghostOK] by blast
    then show "name |\<in>| TE_GhostDatatypes ?mid \<longleftrightarrow> name |\<in>| TE_GhostDatatypes ?envA"
      by simp
  qed

  show ?thesis
    unfolding tyenv_extends_def
  proof (intro conjI)
    show "TE_LocalVars ?mid = TE_LocalVars ?envA"
      by (simp add: fA(1) fM(1))
    show "TE_GhostLocals ?mid = TE_GhostLocals ?envA"
      by (simp add: fA(3) fM(3))
    show "TE_ConstLocals ?mid = TE_ConstLocals ?envA"
      by (simp add: fA(5) fM(5))
    show "TE_TypeVars ?mid = TE_TypeVars ?envA" by simp
    show "TE_RuntimeTypeVars ?mid = TE_RuntimeTypeVars ?envA" by simp
    show "TE_ReturnType ?mid = TE_ReturnType ?envA"
      by (simp add: fA(9) fM(9))
    show "TE_FunctionGhost ?mid = TE_FunctionGhost ?envA"
      by (simp add: fA(10) fM(10))
    show "TE_ProofGoal ?mid = TE_ProofGoal ?envA"
      by (simp add: fA(11) fM(11))
    show "TE_ProofTopLevel ?mid = TE_ProofTopLevel ?envA"
      by (simp add: fA(12) fM(12))
    show "\<forall>name ty. fmlookup (TE_GlobalVars ?envA) name = Some ty \<longrightarrow>
            fmlookup (TE_GlobalVars ?mid) name = Some ty"
      using gv_pres by blast
    show "\<forall>name info. fmlookup (TE_Functions ?envA) name = Some info \<longrightarrow>
            fmlookup (TE_Functions ?mid) name = Some info"
      using fn_pres by blast
    show "\<forall>name n. fmlookup (TE_Datatypes ?envA) name = Some n \<longrightarrow>
            fmlookup (TE_Datatypes ?mid) name = Some n"
      using dt_pres by blast
    show "\<forall>name entry. fmlookup (TE_DataCtors ?envA) name = Some entry \<longrightarrow>
            fmlookup (TE_DataCtors ?mid) name = Some entry"
      using dc_pres by blast
    show "\<forall>name ctors. fmlookup (TE_DataCtorsByType ?envA) name = Some ctors \<longrightarrow>
            fmlookup (TE_DataCtorsByType ?mid) name = Some ctors"
      using bt_pres by blast
    show "\<forall>name. name |\<in>| fmdom (TE_GlobalVars ?envA) \<longrightarrow>
            (name |\<in>| TE_GhostGlobals ?mid \<longleftrightarrow> name |\<in>| TE_GhostGlobals ?envA)"
      using gg_agree by blast
    show "\<forall>name. name |\<in>| fmdom (TE_Datatypes ?envA) \<longrightarrow>
            (name |\<in>| TE_GhostDatatypes ?mid \<longleftrightarrow> name |\<in>| TE_GhostDatatypes ?envA)"
      using gd_agree by blast
  qed
qed


(* ========================================================================== *)
(* Small helpers for the function-body layer                                  *)
(* ========================================================================== *)

lemma map_fst_subst_tmargs:
  "map fst (map (\<lambda>(ty, vr). (apply_subst s ty, vr)) xs) = map (apply_subst s) (map fst xs)"
  by (induction xs) auto

lemma map_snd_subst_tmargs:
  "map snd (map (\<lambda>(ty, vr). (apply_subst s ty, vr)) xs) = map snd xs"
  by (induction xs) auto

lemma fmdom_subst_names:
  "fmdom s |\<subseteq>| subst_names s"
  unfolding subst_names_def by auto

(* The whole link's tyvar fields inherit the module-level conventions from the
   two (well-typed) sides: TE_AbstractTypes = TE_TypeVars, and the runtime
   type variables sit inside the type variables. *)
lemma link_pair_abs_tv:
  assumes linkA: "link_modules as = Inr a"
      and wtA: "core_module_well_typed a"
      and linkB: "link_modules bs = Inr b"
      and wtB: "core_module_well_typed b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
  shows "TE_AbstractTypes (CM_TyEnv m) = TE_TypeVars (CM_TyEnv m)"
    and "TE_RuntimeTypeVars (CM_TyEnv m) |\<subseteq>| TE_TypeVars (CM_TyEnv m)"
proof -
  note gsplit = link_pair_tyvar_split[OF linkA linkB linkM setMS]
  have wfA: "tyenv_well_formed (CM_TyEnv (normalize_module a))"
    and absa0: "TE_AbstractTypes (CM_TyEnv (normalize_module a))
                  = TE_TypeVars (CM_TyEnv (normalize_module a))"
    using wtA unfolding core_module_well_typed_def normalized_module_well_typed_def
                        tyenv_module_scope_def
    by blast+
  have wfB: "tyenv_well_formed (CM_TyEnv (normalize_module b))"
    and absb0: "TE_AbstractTypes (CM_TyEnv (normalize_module b))
                  = TE_TypeVars (CM_TyEnv (normalize_module b))"
    using wtB unfolding core_module_well_typed_def normalized_module_well_typed_def
                        tyenv_module_scope_def
    by blast+
  have absa: "TE_AbstractTypes (CM_TyEnv a) = TE_TypeVars (CM_TyEnv a)"
    using absa0 by simp
  have absb: "TE_AbstractTypes (CM_TyEnv b) = TE_TypeVars (CM_TyEnv b)"
    using absb0 by simp
  have rtvA: "TE_RuntimeTypeVars (CM_TyEnv a) |\<subseteq>| TE_TypeVars (CM_TyEnv a)"
    using wfA unfolding tyenv_well_formed_def tyenv_runtime_tyvars_subset_def by simp
  have rtvB: "TE_RuntimeTypeVars (CM_TyEnv b) |\<subseteq>| TE_TypeVars (CM_TyEnv b)"
    using wfB unfolding tyenv_well_formed_def tyenv_runtime_tyvars_subset_def by simp
  show "TE_AbstractTypes (CM_TyEnv m) = TE_TypeVars (CM_TyEnv m)"
    unfolding gsplit(1) gsplit(3) by (simp add: absa absb)
  show "TE_RuntimeTypeVars (CM_TyEnv m) |\<subseteq>| TE_TypeVars (CM_TyEnv m)"
    unfolding gsplit(1) gsplit(2)
  proof
    fix n
    assume "n |\<in>| (TE_RuntimeTypeVars (CM_TyEnv a) |-| fmdom (CM_TypeSubst m))
                  |\<union>| (TE_RuntimeTypeVars (CM_TyEnv b) |-| fmdom (CM_TypeSubst m))"
    then show "n |\<in>| (TE_TypeVars (CM_TyEnv a) |-| fmdom (CM_TypeSubst m))
                     |\<union>| (TE_TypeVars (CM_TyEnv b) |-| fmdom (CM_TypeSubst m))"
      using rtvA rtvB by (auto dest: fsubsetD)
  qed
qed

(* Capture-avoidance of the whole link, read at a single declared function:
   the function's bound type parameters are untouched by the substitution. *)
lemma link_capture_tyargs_none:
  assumes linkM: "link_modules ms = Inr m"
      and m_lk: "fmlookup (TE_Functions (CM_TyEnv m)) fname = Some info0"
      and n_in: "n |\<in>| fset_of_list (FI_TyArgs info0)"
  shows "fmlookup (CM_TypeSubst m) n = None"
proof -
  have cap_this: "subst_names (CM_TypeSubst m) |\<inter>| fset_of_list (FI_TyArgs info0) = {||}"
    using link_modules_capture_avoiding[OF linkM] m_lk
    unfolding capture_avoiding_def by blast
  have "n |\<notin>| fmdom (CM_TypeSubst m)"
  proof
    assume "n |\<in>| fmdom (CM_TypeSubst m)"
    then have "n |\<in>| subst_names (CM_TypeSubst m)"
      using fmdom_subst_names by (auto dest: fsubsetD)
    then have "n |\<in>| subst_names (CM_TypeSubst m) |\<inter>| fset_of_list (FI_TyArgs info0)"
      using n_in by auto
    then show False using cap_this by auto
  qed
  then show ?thesis by (simp add: fmdom_notD)
qed


(* ========================================================================== *)
(* Well-formedness of function-body environments                              *)
(*                                                                            *)
(* Generic (not linking-specific): the body env of a declared function over a *)
(* well-formed module-level env is well-formed. The signature clauses of      *)
(* tyenv_well_formed supply exactly the local-variable facts the body env     *)
(* needs; the remaining clauses either transfer verbatim (the declaration     *)
(* tables are untouched) or follow by growing TE_RuntimeTypeVars              *)
(* (is_runtime_type_mono_rtv - the body env may add the function's own type   *)
(* parameters to the runtime set).                                            *)
(* ========================================================================== *)

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

  \<comment> \<open>Side facts from the enclosing env's well-formedness.\<close>
  have gvwk: "\<And>name ty. fmlookup (TE_GlobalVars env) name = Some ty \<Longrightarrow>
                is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env \<rparr>) ty"
    using wf unfolding tyenv_well_formed_def tyenv_vars_well_kinded_def by blast
  have gvrt: "\<And>name ty. fmlookup (TE_GlobalVars env) name = Some ty \<Longrightarrow>
                name |\<notin>| TE_GhostGlobals env \<Longrightarrow>
                is_runtime_type (env \<lparr> TE_TypeVars := TE_AbstractTypes env,
                                       TE_RuntimeTypeVars :=
                                         TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env \<rparr>) ty"
    using wf unfolding tyenv_well_formed_def tyenv_vars_runtime_def by blast
  have ggsub: "TE_GhostGlobals env |\<subseteq>| fmdom (TE_GlobalVars env)"
    using wf unfolding tyenv_well_formed_def tyenv_ghost_vars_subset_def by blast
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
               (\<forall>ty \<in> fst ` set (FI_TmArgs info').
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
        have "ty \<in> fst ` set (FI_TmArgs info)" using lk_l by (rule locals_val)
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
      assume asm: "fmlookup (TE_GlobalVars ?be) name = Some ty
                     \<and> name |\<notin>| TE_GhostGlobals ?be"
      then have lk_g: "fmlookup (TE_GlobalVars env) name = Some ty"
            and ng_g: "name |\<notin>| TE_GhostGlobals env"
        by (simp_all add: module_body_env_for_def)
      have rt0: "is_runtime_type (env \<lparr> TE_TypeVars := TE_AbstractTypes env,
                                        TE_RuntimeTypeVars :=
                                          TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env \<rparr>) ty"
        using gvrt[OF lk_g ng_g] .
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
      using ggsub unfolding tyenv_ghost_vars_subset_def
      by (simp add: module_body_env_for_def names_eq)
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
      show "(\<forall>ty \<in> fst ` set (FI_TmArgs info').
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


(* ========================================================================== *)
(* The function-body layer of the linking proof                               *)
(*                                                                            *)
(* Body-env analogues of link_mid_env_extends / link_mid_env_subst_ok /       *)
(* link_mid_env_runtime_ok / link_mid_env_collapse. The body env of the mid   *)
(* env additionally opens the function's type parameters; the whole link's    *)
(* capture-avoidance check guarantees the substitution never touches them.    *)
(* ========================================================================== *)

(* Extension: normalize_module a's body env, tyvar-widened by b's fields,
   extends into the mid env's body env (same names/info on both sides).

   The two sides' tyvar conventions (abstract types = type variables, runtime
   type variables among the type variables) are taken as premises rather than
   derived from well-typedness, so the lemma also applies when one side
   satisfies only the structural module invariant. *)
lemma link_mid_body_env_extends:
  assumes linkA: "link_modules as = Inr a"
      and linkB: "link_modules bs = Inr b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
      and ghostOK: "\<forall>x \<in> set ms. module_ghost_subsets_ok x"
      and absa: "TE_AbstractTypes (CM_TyEnv a) = TE_TypeVars (CM_TyEnv a)"
      and rtvA: "TE_RuntimeTypeVars (CM_TyEnv a) |\<subseteq>| TE_TypeVars (CM_TyEnv a)"
      and absb: "TE_AbstractTypes (CM_TyEnv b) = TE_TypeVars (CM_TyEnv b)"
      and rtvB: "TE_RuntimeTypeVars (CM_TyEnv b) |\<subseteq>| TE_TypeVars (CM_TyEnv b)"
  shows "tyenv_extends
           ((module_body_env_for (CM_TyEnv (normalize_module a)) names info)
              \<lparr> TE_TypeVars :=
                  TE_TypeVars (module_body_env_for (CM_TyEnv (normalize_module a)) names info)
                  |\<union>| TE_TypeVars (CM_TyEnv b),
                TE_RuntimeTypeVars :=
                  TE_RuntimeTypeVars (module_body_env_for (CM_TyEnv (normalize_module a)) names info)
                  |\<union>| TE_RuntimeTypeVars (CM_TyEnv b) \<rparr>)
           (module_body_env_for (link_mid_env a b m) names info)"
proof -
  let ?envA = "CM_TyEnv (normalize_module a)"
  let ?mid = "link_mid_env a b m"
  let ?beA = "module_body_env_for ?envA names info"
  let ?e1 = "?beA \<lparr> TE_TypeVars := TE_TypeVars ?beA |\<union>| TE_TypeVars (CM_TyEnv b),
                    TE_RuntimeTypeVars :=
                      TE_RuntimeTypeVars ?beA |\<union>| TE_RuntimeTypeVars (CM_TyEnv b) \<rparr>"
  let ?be2 = "module_body_env_for ?mid names info"
  note ext0 = link_mid_env_extends[OF linkA linkB linkM setMS ghostOK]

  \<comment> \<open>Module-level components of ext0.\<close>
  have gv_pres: "\<And>name ty. fmlookup (TE_GlobalVars ?envA) name = Some ty \<Longrightarrow>
                   fmlookup (TE_GlobalVars ?mid) name = Some ty"
    using ext0 unfolding tyenv_extends_def by auto
  have fn_pres: "\<And>name i. fmlookup (TE_Functions ?envA) name = Some i \<Longrightarrow>
                   fmlookup (TE_Functions ?mid) name = Some i"
    using ext0 unfolding tyenv_extends_def by auto
  have dt_pres: "\<And>name n. fmlookup (TE_Datatypes ?envA) name = Some n \<Longrightarrow>
                   fmlookup (TE_Datatypes ?mid) name = Some n"
    using ext0 unfolding tyenv_extends_def by auto
  have dc_pres: "\<And>name e. fmlookup (TE_DataCtors ?envA) name = Some e \<Longrightarrow>
                   fmlookup (TE_DataCtors ?mid) name = Some e"
    using ext0 unfolding tyenv_extends_def by auto
  have bt_pres: "\<And>name cs. fmlookup (TE_DataCtorsByType ?envA) name = Some cs \<Longrightarrow>
                   fmlookup (TE_DataCtorsByType ?mid) name = Some cs"
    using ext0 unfolding tyenv_extends_def by auto
  have gg_agr: "\<And>name. name |\<in>| fmdom (TE_GlobalVars ?envA) \<Longrightarrow>
                  (name |\<in>| TE_GhostGlobals ?mid \<longleftrightarrow> name |\<in>| TE_GhostGlobals ?envA)"
    using ext0 unfolding tyenv_extends_def by auto
  have gd_agr: "\<And>name. name |\<in>| fmdom (TE_Datatypes ?envA) \<Longrightarrow>
                  (name |\<in>| TE_GhostDatatypes ?mid \<longleftrightarrow> name |\<in>| TE_GhostDatatypes ?envA)"
    using ext0 unfolding tyenv_extends_def by auto

  show ?thesis
    unfolding tyenv_extends_def
  proof (intro conjI)
    show "TE_LocalVars ?be2 = TE_LocalVars ?e1"
      by (simp add: module_body_env_for_def)
    show "TE_GhostLocals ?be2 = TE_GhostLocals ?e1"
      by (simp add: module_body_env_for_def)
    show "TE_ConstLocals ?be2 = TE_ConstLocals ?e1"
      by (simp add: module_body_env_for_def)
    show "TE_TypeVars ?be2 = TE_TypeVars ?e1"
      by (rule fset_eqI) (auto simp: module_body_env_for_def absa)
    show "TE_RuntimeTypeVars ?be2 = TE_RuntimeTypeVars ?e1"
    proof (rule fset_eqI)
      fix n
      show "n |\<in>| TE_RuntimeTypeVars ?be2 \<longleftrightarrow> n |\<in>| TE_RuntimeTypeVars ?e1"
        using rtvA rtvB
        by (auto simp: module_body_env_for_def absa absb dest: fsubsetD)
    qed
    show "TE_ReturnType ?be2 = TE_ReturnType ?e1"
      by (simp add: module_body_env_for_def)
    show "TE_FunctionGhost ?be2 = TE_FunctionGhost ?e1"
      by (simp add: module_body_env_for_def)
    show "TE_ProofGoal ?be2 = TE_ProofGoal ?e1"
      by (simp add: module_body_env_for_def)
    show "TE_ProofTopLevel ?be2 = TE_ProofTopLevel ?e1"
      by (simp add: module_body_env_for_def)
    show "\<forall>name ty. fmlookup (TE_GlobalVars ?e1) name = Some ty \<longrightarrow>
            fmlookup (TE_GlobalVars ?be2) name = Some ty"
      using gv_pres by (auto simp: module_body_env_for_def)
    show "\<forall>name i. fmlookup (TE_Functions ?e1) name = Some i \<longrightarrow>
            fmlookup (TE_Functions ?be2) name = Some i"
      using fn_pres by (auto simp: module_body_env_for_def)
    show "\<forall>name n. fmlookup (TE_Datatypes ?e1) name = Some n \<longrightarrow>
            fmlookup (TE_Datatypes ?be2) name = Some n"
      using dt_pres by (auto simp: module_body_env_for_def)
    show "\<forall>name e. fmlookup (TE_DataCtors ?e1) name = Some e \<longrightarrow>
            fmlookup (TE_DataCtors ?be2) name = Some e"
      using dc_pres by (auto simp: module_body_env_for_def)
    show "\<forall>name cs. fmlookup (TE_DataCtorsByType ?e1) name = Some cs \<longrightarrow>
            fmlookup (TE_DataCtorsByType ?be2) name = Some cs"
      using bt_pres by (auto simp: module_body_env_for_def)
    show "\<forall>name. name |\<in>| fmdom (TE_GlobalVars ?e1) \<longrightarrow>
            (name |\<in>| TE_GhostGlobals ?be2 \<longleftrightarrow> name |\<in>| TE_GhostGlobals ?e1)"
      using gg_agr by (auto simp: module_body_env_for_def)
    show "\<forall>name. name |\<in>| fmdom (TE_Datatypes ?e1) \<longrightarrow>
            (name |\<in>| TE_GhostDatatypes ?be2 \<longleftrightarrow> name |\<in>| TE_GhostDatatypes ?e1)"
      using gd_agr by (auto simp: module_body_env_for_def)
  qed
qed

(* module_env_subst_ok at the body level: the datatype tables and the
   function/ctor binder clauses are the mid env's (the body env leaves those
   maps untouched); the tyvar coverage adds the function's own type
   parameters, which the whole link's capture check keeps out of the
   substitution.

   The module-level module_env_subst_ok fact and the whole link's
   abstract-types convention are taken as premises, so this works from any
   proof of the module-level fact (both sides well-typed, or one side carrying
   only the structural invariant). *)
lemma link_mid_body_env_subst_ok:
  assumes linkM: "link_modules ms = Inr m"
      and m_lk: "fmlookup (TE_Functions (CM_TyEnv m)) fname = Some info0"
      and tyargs: "FI_TyArgs info = FI_TyArgs info0"
      and mid_ok: "module_env_subst_ok (CM_TypeSubst m)
                     (CM_TyEnv (normalize_module m)) (link_mid_env a b m)"
      and absM: "TE_AbstractTypes (CM_TyEnv m) = TE_TypeVars (CM_TyEnv m)"
  shows "module_env_subst_ok (CM_TypeSubst m)
           (module_body_env_for (CM_TyEnv (normalize_module m)) names
              (apply_subst_to_funinfo (CM_TypeSubst m) info0))
           (module_body_env_for (link_mid_env a b m) names info)"
proof -
  let ?mid = "link_mid_env a b m"
  let ?tb = "module_body_env_for (CM_TyEnv (normalize_module m)) names
               (apply_subst_to_funinfo (CM_TypeSubst m) info0)"
  let ?sb = "module_body_env_for ?mid names info"
  have mid_cov: "\<And>n. n |\<in>| TE_TypeVars ?mid \<Longrightarrow>
                   (case fmlookup (CM_TypeSubst m) n of
                      Some ty' \<Rightarrow> is_well_kinded (CM_TyEnv (normalize_module m)) ty'
                    | None \<Rightarrow> n |\<in>| TE_TypeVars (CM_TyEnv (normalize_module m)))"
    using mid_ok unfolding module_env_subst_ok_def by blast
  have mid_fun: "\<And>funName inf. fmlookup (TE_Functions ?mid) funName = Some inf \<Longrightarrow>
                   subst_names (CM_TypeSubst m) |\<inter>| fset_of_list (FI_TyArgs inf) = {||}"
    using mid_ok unfolding module_env_subst_ok_def by blast
  have mid_ctor: "\<And>ctorName dtName tyVars payload.
                    fmlookup (TE_DataCtors ?mid) ctorName = Some (dtName, tyVars, payload) \<Longrightarrow>
                    subst_names (CM_TypeSubst m) |\<inter>| fset_of_list tyVars = {||}"
    using mid_ok unfolding module_env_subst_ok_def by blast

  show ?thesis
    unfolding module_env_subst_ok_def
  proof (intro conjI)
    show "TE_Datatypes ?tb = TE_Datatypes ?sb"
      by (simp add: module_body_env_for_def)
    show "TE_GhostDatatypes ?tb = TE_GhostDatatypes ?sb"
      by (simp add: module_body_env_for_def)
  next
    show "\<forall>n. n |\<in>| TE_TypeVars ?sb \<longrightarrow>
            (case fmlookup (CM_TypeSubst m) n of
               Some ty' \<Rightarrow> is_well_kinded ?tb ty'
             | None \<Rightarrow> n |\<in>| TE_TypeVars ?tb)"
    proof (intro allI impI)
      fix n assume "n |\<in>| TE_TypeVars ?sb"
      then have "n |\<in>| TE_TypeVars ?mid \<or> n |\<in>| fset_of_list (FI_TyArgs info0)"
        by (auto simp: module_body_env_for_def tyargs)
      then show "case fmlookup (CM_TypeSubst m) n of
                   Some ty' \<Rightarrow> is_well_kinded ?tb ty'
                 | None \<Rightarrow> n |\<in>| TE_TypeVars ?tb"
      proof
        assume n_mid: "n |\<in>| TE_TypeVars ?mid"
        show ?thesis
        proof (cases "fmlookup (CM_TypeSubst m) n")
          case (Some ty')
          have wk_m: "is_well_kinded (CM_TyEnv (normalize_module m)) ty'"
            using mid_cov[OF n_mid] Some by simp
          have "is_well_kinded ?tb ty'"
          proof (rule is_well_kinded_mono[OF wk_m])
            show "fset (TE_TypeVars (CM_TyEnv (normalize_module m)))
                    \<subseteq> fset (TE_TypeVars ?tb)"
              by (auto simp: module_body_env_for_def absM)
            show "\<And>nn v. fmlookup (TE_Datatypes (CM_TyEnv (normalize_module m))) nn = Some v
                    \<Longrightarrow> fmlookup (TE_Datatypes ?tb) nn = Some v"
              by (simp add: module_body_env_for_def)
          qed
          then show ?thesis using Some by simp
        next
          case None
          then have "n |\<in>| TE_TypeVars (CM_TyEnv (normalize_module m))"
            using mid_cov[OF n_mid] by simp
          then have "n |\<in>| TE_TypeVars ?tb"
            by (auto simp: module_body_env_for_def absM)
          then show ?thesis using None by simp
        qed
      next
        assume n_ty: "n |\<in>| fset_of_list (FI_TyArgs info0)"
        have "fmlookup (CM_TypeSubst m) n = None"
          using link_capture_tyargs_none[OF linkM m_lk n_ty] .
        moreover have "n |\<in>| TE_TypeVars ?tb"
          using n_ty
          by (auto simp: module_body_env_for_def apply_subst_to_funinfo_def)
        ultimately show ?thesis by simp
      qed
    qed
  next
    show "\<forall>funName inf. fmlookup (TE_Functions ?sb) funName = Some inf \<longrightarrow>
            subst_names (CM_TypeSubst m) |\<inter>| fset_of_list (FI_TyArgs inf) = {||}"
    proof (intro allI impI)
      fix funName inf
      assume "fmlookup (TE_Functions ?sb) funName = Some inf"
      then have "fmlookup (TE_Functions ?mid) funName = Some inf"
        by (simp add: module_body_env_for_def)
      then show "subst_names (CM_TypeSubst m) |\<inter>| fset_of_list (FI_TyArgs inf) = {||}"
        by (rule mid_fun)
    qed
    show "\<forall>ctorName dtName tyVars payload.
            fmlookup (TE_DataCtors ?sb) ctorName = Some (dtName, tyVars, payload) \<longrightarrow>
            subst_names (CM_TypeSubst m) |\<inter>| fset_of_list tyVars = {||}"
    proof (intro allI impI)
      fix ctorName dtName tyVars payload
      assume "fmlookup (TE_DataCtors ?sb) ctorName = Some (dtName, tyVars, payload)"
      then have "fmlookup (TE_DataCtors ?mid) ctorName = Some (dtName, tyVars, payload)"
        by (simp add: module_body_env_for_def)
      then show "subst_names (CM_TypeSubst m) |\<inter>| fset_of_list tyVars = {||}"
        by (rule mid_ctor)
    qed
  qed
qed

(* module_env_subst_runtime_ok at the body level. As above, the whole link's
   tyvar conventions are premises rather than derived from side
   well-typedness. *)
lemma link_mid_body_env_runtime_ok:
  assumes linkA: "link_modules as = Inr a"
      and linkB: "link_modules bs = Inr b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
      and m_lk: "fmlookup (TE_Functions (CM_TyEnv m)) fname = Some info0"
      and tyargs: "FI_TyArgs info = FI_TyArgs info0"
      and ghosteq: "FI_Ghost info = FI_Ghost info0"
      and absM: "TE_AbstractTypes (CM_TyEnv m) = TE_TypeVars (CM_TyEnv m)"
      and rtvM: "TE_RuntimeTypeVars (CM_TyEnv m) |\<subseteq>| TE_TypeVars (CM_TyEnv m)"
  shows "module_env_subst_runtime_ok (CM_TypeSubst m)
           (module_body_env_for (CM_TyEnv (normalize_module m)) names
              (apply_subst_to_funinfo (CM_TypeSubst m) info0))
           (module_body_env_for (link_mid_env a b m) names info)"
proof -
  let ?mid = "link_mid_env a b m"
  let ?tb = "module_body_env_for (CM_TyEnv (normalize_module m)) names
               (apply_subst_to_funinfo (CM_TypeSubst m) info0)"
  let ?sb = "module_body_env_for ?mid names info"
  have mid_cov: "\<And>n. n |\<in>| TE_RuntimeTypeVars ?mid \<Longrightarrow>
                   (case fmlookup (CM_TypeSubst m) n of
                      Some ty' \<Rightarrow> is_runtime_type (CM_TyEnv (normalize_module m)) ty'
                    | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars (CM_TyEnv (normalize_module m)))"
    using link_mid_env_runtime_ok[OF linkA linkB linkM setMS]
    unfolding module_env_subst_runtime_ok_def by blast
  have ghost_m: "FI_Ghost (apply_subst_to_funinfo (CM_TypeSubst m) info0) = FI_Ghost info0"
    by (simp add: apply_subst_to_funinfo_def)
  have rtv_tb: "\<And>n. n |\<in>| TE_RuntimeTypeVars (CM_TyEnv m) \<Longrightarrow> n |\<in>| TE_RuntimeTypeVars ?tb"
    using rtvM absM
    by (auto simp: module_body_env_for_def dest: fsubsetD)

  show ?thesis
    unfolding module_env_subst_runtime_ok_def
  proof (intro allI impI)
    fix n assume "n |\<in>| TE_RuntimeTypeVars ?sb"
    then have "n |\<in>| TE_RuntimeTypeVars ?mid
                 \<or> (FI_Ghost info = NotGhost \<and> n |\<in>| fset_of_list (FI_TyArgs info0))"
      by (auto simp: module_body_env_for_def tyargs split: if_splits)
    then show "case fmlookup (CM_TypeSubst m) n of
                 Some ty' \<Rightarrow> is_runtime_type ?tb ty'
               | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars ?tb"
    proof
      assume n_mid: "n |\<in>| TE_RuntimeTypeVars ?mid"
      show ?thesis
      proof (cases "fmlookup (CM_TypeSubst m) n")
        case (Some ty')
        have rt_m: "is_runtime_type (CM_TyEnv (normalize_module m)) ty'"
          using mid_cov[OF n_mid] Some by simp
        have "is_runtime_type ?tb ty'"
        proof (rule is_runtime_type_mono_rtv[OF rt_m])
          show "fset (TE_RuntimeTypeVars (CM_TyEnv (normalize_module m)))
                  \<subseteq> fset (TE_RuntimeTypeVars ?tb)"
            using rtv_tb by auto
          show "TE_GhostDatatypes ?tb
                  = TE_GhostDatatypes (CM_TyEnv (normalize_module m))"
            by (simp add: module_body_env_for_def)
        qed
        then show ?thesis using Some by simp
      next
        case None
        then have "n |\<in>| TE_RuntimeTypeVars (CM_TyEnv (normalize_module m))"
          using mid_cov[OF n_mid] by simp
        then have "n |\<in>| TE_RuntimeTypeVars ?tb" using rtv_tb by simp
        then show ?thesis using None by simp
      qed
    next
      assume asm: "FI_Ghost info = NotGhost \<and> n |\<in>| fset_of_list (FI_TyArgs info0)"
      then have ng: "FI_Ghost info0 = NotGhost" using ghosteq by simp
      have "fmlookup (CM_TypeSubst m) n = None"
        using link_capture_tyargs_none[OF linkM m_lk] asm by blast
      moreover have "n |\<in>| TE_RuntimeTypeVars ?tb"
        using asm ng ghost_m
        by (auto simp: module_body_env_for_def apply_subst_to_funinfo_def)
      ultimately show ?thesis by simp
    qed
  qed
qed

(* Commutation (the body-level P5): substituting the mid env's body env with
   the whole link's substitution, with the normalize_module m body env as the
   tyvar-supplying target, IS the normalize_module m body env. *)
lemma link_mid_body_env_collapse:
  assumes linkA: "link_modules as = Inr a"
      and linkB: "link_modules bs = Inr b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
      and info_rel: "info = apply_subst_to_funinfo (CM_TypeSubst a) info0"
  shows "apply_subst_to_module_env (CM_TypeSubst m)
           (module_body_env_for (CM_TyEnv (normalize_module m)) names
              (apply_subst_to_funinfo (CM_TypeSubst m) info0))
           (module_body_env_for (link_mid_env a b m) names info)
         = module_body_env_for (CM_TyEnv (normalize_module m)) names
              (apply_subst_to_funinfo (CM_TypeSubst m) info0)"
proof -
  let ?\<sigma> = "CM_TypeSubst m"
  let ?mid = "link_mid_env a b m"
  let ?tb = "module_body_env_for (CM_TyEnv (normalize_module m)) names
               (apply_subst_to_funinfo ?\<sigma> info0)"
  let ?sb = "module_body_env_for ?mid names info"
  let ?lhs = "apply_subst_to_module_env ?\<sigma> ?tb ?sb"
  have subA: "set as \<subseteq> set ms" using setMS by auto
  have absA: "\<And>ty. apply_subst ?\<sigma> (apply_subst (CM_TypeSubst a) ty) = apply_subst ?\<sigma> ty"
    using link_modules_closure_absorb[OF linkA linkM subA] .
  note fam = link_mid_env_family_collapse[OF linkA linkB linkM setMS]
  note fM = link_modules_result_fields[OF linkM]

  \<comment> \<open>The three argument-type computations.\<close>
  have tysA: "map fst (FI_TmArgs info)
                = map (apply_subst (CM_TypeSubst a)) (map fst (FI_TmArgs info0))"
    using info_rel by auto
  have tysM: "map fst (FI_TmArgs (apply_subst_to_funinfo ?\<sigma> info0))
                = map (apply_subst ?\<sigma>) (map fst (FI_TmArgs info0))"
    by auto
  have absmap: "map (apply_subst ?\<sigma>) (map (apply_subst (CM_TypeSubst a)) (map fst (FI_TmArgs info0)))
                  = map (apply_subst ?\<sigma>) (map fst (FI_TmArgs info0))"
    unfolding map_map by (rule map_cong[OF refl]) (simp add: absA o_def)
  have snds: "map snd (FI_TmArgs info) = map snd (FI_TmArgs info0)"
    using info_rel by auto
  have sndsM: "map snd (FI_TmArgs (apply_subst_to_funinfo ?\<sigma> info0))
                 = map snd (FI_TmArgs info0)"
    by auto
  \<comment> \<open>Composition normal forms: simp unfolds apply_subst_to_funinfo and
      contracts map-of-map, leaving these composed functions behind.\<close>
  have compF: "\<And>s. fst \<circ> (\<lambda>(ty, y). (apply_subst s ty, y)) = apply_subst s \<circ> fst"
    by (rule ext) auto
  have compS: "\<And>s. snd \<circ> (\<lambda>(ty, y). (apply_subst s ty, y)) = snd"
    by (rule ext) auto

  show ?thesis
  proof (rule CoreTyEnv.equality)
    show "TE_LocalVars ?lhs = TE_LocalVars ?tb"
    proof -
      have "TE_LocalVars ?lhs
              = fmmap (apply_subst ?\<sigma>)
                      (fmap_of_list (zip names (map fst (FI_TmArgs info))))"
        by (simp add: module_body_env_for_def)
      also have "... = fmap_of_list (zip names (map (apply_subst ?\<sigma>) (map fst (FI_TmArgs info))))"
        by (simp add: fmmap_fmap_of_list zip_map2[symmetric])
      also have "... = fmap_of_list (zip names (map (apply_subst ?\<sigma>) (map fst (FI_TmArgs info0))))"
        using tysA absmap by metis
      also have "... = TE_LocalVars ?tb"
        by (simp add: module_body_env_for_def compF)
      finally show ?thesis .
    qed
    show "TE_GlobalVars ?lhs = TE_GlobalVars ?tb"
      using fam(1) by (simp add: module_body_env_for_def)
    show "TE_GhostLocals ?lhs = TE_GhostLocals ?tb"
      by (simp add: module_body_env_for_def info_rel apply_subst_to_funinfo_def)
    show "TE_GhostGlobals ?lhs = TE_GhostGlobals ?tb"
      by (simp add: module_body_env_for_def)
    show "TE_ConstLocals ?lhs = TE_ConstLocals ?tb"
      using snds by (simp add: module_body_env_for_def compS)
    show "TE_TypeVars ?lhs = TE_TypeVars ?tb"
      by simp
    show "TE_RuntimeTypeVars ?lhs = TE_RuntimeTypeVars ?tb"
      by simp
    show "TE_AbstractTypes ?lhs = TE_AbstractTypes ?tb"
      by simp
    show "TE_ReturnType ?lhs = TE_ReturnType ?tb"
      by (simp add: module_body_env_for_def info_rel apply_subst_to_funinfo_def absA)
    show "TE_FunctionGhost ?lhs = TE_FunctionGhost ?tb"
      by (simp add: module_body_env_for_def info_rel apply_subst_to_funinfo_def)
    show "TE_ProofGoal ?lhs = TE_ProofGoal ?tb"
      by (simp add: module_body_env_for_def)
    show "TE_ProofTopLevel ?lhs = TE_ProofTopLevel ?tb"
      by (simp add: module_body_env_for_def)
    show "TE_Functions ?lhs = TE_Functions ?tb"
      using fam(2) by (simp add: module_body_env_for_def)
    show "TE_Datatypes ?lhs = TE_Datatypes ?tb"
      by (simp add: module_body_env_for_def)
    show "TE_DataCtors ?lhs = TE_DataCtors ?tb"
      using fam(3) by (simp add: module_body_env_for_def)
    show "TE_DataCtorsByType ?lhs = TE_DataCtorsByType ?tb"
      by (simp add: module_body_env_for_def)
    show "TE_GhostDatatypes ?lhs = TE_GhostDatatypes ?tb"
      by (simp add: module_body_env_for_def)
    show "CoreTyEnv.more ?lhs = CoreTyEnv.more ?tb"
      by (simp add: apply_subst_to_module_env_def module_body_env_for_def
                    link_mid_env_def apply_subst_to_tyenv_def)
  qed
qed


(* ========================================================================== *)
(* Per-side contribution lemmas                                               *)
(*                                                                            *)
(* Each definition (global or function) of the whole link comes from exactly  *)
(* one input module, hence from one of the two sub-links. These lemmas run    *)
(* the full per-definition chain for a definition contributed by sub-link a:  *)
(*                                                                            *)
(*   side typing at CM_TyEnv (normalize_module a)                             *)
(*     -> tyvar-widen by the other side's TE_TypeVars / TE_RuntimeTypeVars    *)
(*     -> declaration-axis extension into the mid env                         *)
(*     -> module-level substitution by CM_TypeSubst m                         *)
(*     -> collapse onto CM_TyEnv (normalize_module m)                         *)
(*                                                                            *)
(* The b-side instances are obtained by swapping (a, as) with (b, bs) - the   *)
(* hypotheses and conclusion are symmetric (setMS commutes by Un_commute).    *)
(* ========================================================================== *)

lemma link_mid_globals_contribution:
  assumes linkA: "link_modules as = Inr a"
      and wtA: "core_module_well_typed a"
      and linkB: "link_modules bs = Inr b"
      and wtB: "core_module_well_typed b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
      and ghostOK: "\<forall>x \<in> set ms. module_ghost_subsets_ok x"
      and a_def: "fmlookup (CM_GlobalVars a) name = Some tm0"
  shows "\<exists>declTy.
           fmlookup (TE_GlobalVars (CM_TyEnv (normalize_module m))) name = Some declTy \<and>
           (if name |\<in>| TE_GhostGlobals (CM_TyEnv (normalize_module m))
            then core_term_type (CM_TyEnv (normalize_module m)) Ghost
                   (apply_subst_to_term (CM_TypeSubst m) tm0) = Some declTy
            else is_constant_term (apply_subst_to_term (CM_TypeSubst m) tm0) \<and>
                 core_term_type (CM_TyEnv (normalize_module m)) NotGhost
                   (apply_subst_to_term (CM_TypeSubst m) tm0) = Some declTy)"
proof -
  let ?\<sigma>A = "CM_TypeSubst a"
  let ?\<sigma>M = "CM_TypeSubst m"
  let ?envA = "CM_TyEnv (normalize_module a)"
  let ?envM = "CM_TyEnv (normalize_module m)"
  let ?mid = "link_mid_env a b m"
  let ?e1 = "?envA \<lparr> TE_TypeVars := TE_TypeVars (CM_TyEnv a) |\<union>| TE_TypeVars (CM_TyEnv b),
                     TE_RuntimeTypeVars :=
                       TE_RuntimeTypeVars (CM_TyEnv a)
                       |\<union>| TE_RuntimeTypeVars (CM_TyEnv b) \<rparr>"
  have subA: "set as \<subseteq> set ms" using setMS by auto
  have absA: "\<And>ty. apply_subst ?\<sigma>M (apply_subst ?\<sigma>A ty) = apply_subst ?\<sigma>M ty"
    using link_modules_closure_absorb[OF linkA linkM subA] .
  have wfA: "tyenv_well_formed ?envA"
    and gwtA: "module_globals_well_typed ?envA (CM_GlobalVars (normalize_module a))"
    using wtA unfolding core_module_well_typed_def normalized_module_well_typed_def
    by blast+

  \<comment> \<open>The a-side entry and its declared type.\<close>
  have a_def': "fmlookup (CM_GlobalVars (normalize_module a)) name
                  = Some (apply_subst_to_term ?\<sigma>A tm0)"
    using a_def by simp
  obtain declTy0 where
      a_decl: "fmlookup (TE_GlobalVars ?envA) name = Some declTy0" and
      a_typing: "if name |\<in>| TE_GhostGlobals ?envA
                 then core_term_type ?envA Ghost (apply_subst_to_term ?\<sigma>A tm0)
                        = Some declTy0
                 else is_constant_term (apply_subst_to_term ?\<sigma>A tm0) \<and>
                      core_term_type ?envA NotGhost (apply_subst_to_term ?\<sigma>A tm0)
                        = Some declTy0"
    using gwtA a_def' unfolding module_globals_well_typed_def by blast

  \<comment> \<open>Underneath: the raw whole-link declaration.\<close>
  have "fmlookup (fmmap (apply_subst ?\<sigma>A) (TE_GlobalVars (CM_TyEnv a))) name
          = Some declTy0"
    using a_decl by simp
  then obtain declTy00 where
      a_raw: "fmlookup (TE_GlobalVars (CM_TyEnv a)) name = Some declTy00" and
      declTy0_eq: "declTy0 = apply_subst ?\<sigma>A declTy00"
    by (cases "fmlookup (TE_GlobalVars (CM_TyEnv a)) name") auto
  have m_raw: "fmlookup (TE_GlobalVars (CM_TyEnv m)) name = Some declTy00"
    using link_modules_decl_submaps(1)[OF linkA linkM subA a_raw] .
  have m_decl: "fmlookup (TE_GlobalVars ?envM) name = Some (apply_subst ?\<sigma>M declTy00)"
    using m_raw by simp
  have declTy_abs: "apply_subst ?\<sigma>M declTy0 = apply_subst ?\<sigma>M declTy00"
    using declTy0_eq absA by simp

  \<comment> \<open>Ghost status agrees between the two links on this a-declared name.\<close>
  have a_dom: "name |\<in>| fmdom (TE_GlobalVars (CM_TyEnv a))"
    using a_raw by (rule fmdomI)
  have ghost_agree: "name |\<in>| TE_GhostGlobals (CM_TyEnv m)
                       \<longleftrightarrow> name |\<in>| TE_GhostGlobals (CM_TyEnv a)"
    using link_ghost_globals_agree[OF linkA linkM subA ghostOK a_dom] .

  \<comment> \<open>The four-stage typing chain, in whichever ghost mode applies.\<close>
  have chain: "\<And>gh. core_term_type ?envA gh (apply_subst_to_term ?\<sigma>A tm0) = Some declTy0
                 \<Longrightarrow> core_term_type ?envM gh (apply_subst_to_term ?\<sigma>M tm0)
                       = Some (apply_subst ?\<sigma>M declTy00)"
  proof -
    fix gh
    assume t0: "core_term_type ?envA gh (apply_subst_to_term ?\<sigma>A tm0) = Some declTy0"
    \<comment> \<open>Widen the tyvar fields by the b-side's.\<close>
    have t1: "core_term_type ?e1 gh (apply_subst_to_term ?\<sigma>A tm0) = Some declTy0"
      using core_term_type_irrelevant_tyvar[OF t0,
              where extraTV = "TE_TypeVars (CM_TyEnv b)"
                and extraRT = "TE_RuntimeTypeVars (CM_TyEnv b)"]
      by simp
    \<comment> \<open>Extend along the declaration axis into the mid env.\<close>
    have cons1: "tyenv_ctors_consistent ?e1"
      using wfA unfolding tyenv_well_formed_def tyenv_ctors_consistent_def by simp
    have t2: "core_term_type ?mid gh (apply_subst_to_term ?\<sigma>A tm0) = Some declTy0"
      using core_term_type_tyenv_extends[OF
              link_mid_env_extends[OF linkA linkB linkM setMS ghostOK] cons1 t1] .
    \<comment> \<open>Substitute with the whole link's substitution.\<close>
    have t3: "core_term_type (apply_subst_to_module_env ?\<sigma>M ?envM ?mid) gh
                (apply_subst_to_term ?\<sigma>M (apply_subst_to_term ?\<sigma>A tm0))
                = Some (apply_subst ?\<sigma>M declTy0)"
      using core_term_type_subst_module_env[OF t2
              link_mid_env_well_formed[OF linkA wtA linkB wtB linkM setMS ghostOK]
              link_mid_env_subst_ok[OF linkA wtA linkB wtB linkM setMS]]
            link_mid_env_runtime_ok[OF linkA linkB linkM setMS]
      by blast
    \<comment> \<open>Collapse the env and absorb the a-side substitution.\<close>
    show "core_term_type ?envM gh (apply_subst_to_term ?\<sigma>M tm0)
            = Some (apply_subst ?\<sigma>M declTy00)"
      using t3
      unfolding link_mid_env_collapse[OF linkA linkB linkM setMS]
                subst_absorb_term[OF absA] declTy_abs .
  qed

  show ?thesis
  proof (cases "name |\<in>| TE_GhostGlobals (CM_TyEnv a)")
    case True
    then have gm: "name |\<in>| TE_GhostGlobals ?envM"
      using ghost_agree by simp
    have "core_term_type ?envA Ghost (apply_subst_to_term ?\<sigma>A tm0) = Some declTy0"
      using a_typing True by simp
    then have t: "core_term_type ?envM Ghost (apply_subst_to_term ?\<sigma>M tm0)
                    = Some (apply_subst ?\<sigma>M declTy00)"
      by (rule chain)
    show ?thesis using m_decl gm t by auto
  next
    case False
    then have gm: "name |\<notin>| TE_GhostGlobals ?envM"
      using ghost_agree by simp
    have const: "is_constant_term (apply_subst_to_term ?\<sigma>M tm0)"
      using a_typing False by simp
    have "core_term_type ?envA NotGhost (apply_subst_to_term ?\<sigma>A tm0) = Some declTy0"
      using a_typing False by simp
    then have t: "core_term_type ?envM NotGhost (apply_subst_to_term ?\<sigma>M tm0)
                    = Some (apply_subst ?\<sigma>M declTy00)"
      by (rule chain)
    show ?thesis using m_decl gm const t by auto
  qed
qed


lemma link_mid_functions_contribution:
  assumes linkA: "link_modules as = Inr a"
      and wtA: "core_module_well_typed a"
      and linkB: "link_modules bs = Inr b"
      and wtB: "core_module_well_typed b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
      and ghostOK: "\<forall>x \<in> set ms. module_ghost_subsets_ok x"
      and a_def: "fmlookup (CM_Functions a) name = Some f0"
  shows "\<exists>info.
           fmlookup (TE_Functions (CM_TyEnv (normalize_module m))) name = Some info \<and>
           length (CF_Args f0) = length (FI_TmArgs info) \<and>
           distinct (CF_Args f0) \<and>
           (case CF_Body f0 of
              None \<Rightarrow> True
            | Some body0 \<Rightarrow>
                core_statement_list_type
                  (module_body_env_for (CM_TyEnv (normalize_module m)) (CF_Args f0) info)
                  (FI_Ghost info)
                  (apply_subst_to_statement_list (CM_TypeSubst m) body0) \<noteq> None)"
proof -
  let ?\<sigma>A = "CM_TypeSubst a"
  let ?\<sigma>M = "CM_TypeSubst m"
  let ?envA = "CM_TyEnv (normalize_module a)"
  let ?envM = "CM_TyEnv (normalize_module m)"
  let ?mid = "link_mid_env a b m"
  have subA: "set as \<subseteq> set ms" using setMS by auto
  have absA: "\<And>ty. apply_subst ?\<sigma>M (apply_subst ?\<sigma>A ty) = apply_subst ?\<sigma>M ty"
    using link_modules_closure_absorb[OF linkA linkM subA] .
  have wfA: "tyenv_well_formed ?envA"
    and fwtA: "module_functions_well_typed ?envA (CM_Functions (normalize_module a))"
    using wtA unfolding core_module_well_typed_def normalized_module_well_typed_def
    by blast+

  \<comment> \<open>Side and whole-link tyvar conventions, feeding the body-env lemmas.\<close>
  have absa0: "TE_AbstractTypes ?envA = TE_TypeVars ?envA"
    using wtA unfolding core_module_well_typed_def normalized_module_well_typed_def
                        tyenv_module_scope_def
    by blast
  have absa: "TE_AbstractTypes (CM_TyEnv a) = TE_TypeVars (CM_TyEnv a)"
    using absa0 by simp
  have rtva: "TE_RuntimeTypeVars (CM_TyEnv a) |\<subseteq>| TE_TypeVars (CM_TyEnv a)"
    using wfA unfolding tyenv_well_formed_def tyenv_runtime_tyvars_subset_def by simp
  have wfB: "tyenv_well_formed (CM_TyEnv (normalize_module b))"
    and absb0: "TE_AbstractTypes (CM_TyEnv (normalize_module b))
                  = TE_TypeVars (CM_TyEnv (normalize_module b))"
    using wtB unfolding core_module_well_typed_def normalized_module_well_typed_def
                        tyenv_module_scope_def
    by blast+
  have absb: "TE_AbstractTypes (CM_TyEnv b) = TE_TypeVars (CM_TyEnv b)"
    using absb0 by simp
  have rtvb: "TE_RuntimeTypeVars (CM_TyEnv b) |\<subseteq>| TE_TypeVars (CM_TyEnv b)"
    using wfB unfolding tyenv_well_formed_def tyenv_runtime_tyvars_subset_def by simp
  have absM: "TE_AbstractTypes (CM_TyEnv m) = TE_TypeVars (CM_TyEnv m)"
    and rtvM: "TE_RuntimeTypeVars (CM_TyEnv m) |\<subseteq>| TE_TypeVars (CM_TyEnv m)"
    using link_pair_abs_tv[OF linkA wtA linkB wtB linkM setMS] by blast+

  \<comment> \<open>The a-side definition and its declared FunInfo.\<close>
  let ?fA = "f0 \<lparr> CF_Body := map_option (apply_subst_to_statement_list ?\<sigma>A)
                                        (CF_Body f0) \<rparr>"
  have a_def': "fmlookup (CM_Functions (normalize_module a)) name = Some ?fA"
    using a_def by simp
  obtain infoA where
      a_decl: "fmlookup (TE_Functions ?envA) name = Some infoA" and
      lenA: "length (CF_Args ?fA) = length (FI_TmArgs infoA)" and
      distA: "distinct (CF_Args ?fA)" and
      bodyA_ok: "case CF_Body ?fA of
                   None \<Rightarrow> True
                 | Some body \<Rightarrow>
                     core_statement_list_type
                       (module_body_env_for ?envA (CF_Args ?fA) infoA)
                       (FI_Ghost infoA) body \<noteq> None"
    using fwtA a_def' unfolding module_functions_well_typed_def by blast

  \<comment> \<open>Underneath: the raw whole-link declaration.\<close>
  have "fmlookup (fmmap (apply_subst_to_funinfo ?\<sigma>A) (TE_Functions (CM_TyEnv a))) name
          = Some infoA"
    using a_decl by simp
  then obtain info0 where
      a_raw: "fmlookup (TE_Functions (CM_TyEnv a)) name = Some info0" and
      infoA_eq: "infoA = apply_subst_to_funinfo ?\<sigma>A info0"
    by (cases "fmlookup (TE_Functions (CM_TyEnv a)) name") auto
  have m_raw: "fmlookup (TE_Functions (CM_TyEnv m)) name = Some info0"
    using link_modules_decl_submaps(2)[OF linkA linkM subA a_raw] .
  let ?infoM = "apply_subst_to_funinfo ?\<sigma>M info0"
  have m_decl: "fmlookup (TE_Functions ?envM) name = Some ?infoM"
    using m_raw by simp

  \<comment> \<open>Signature facts preserved by funinfo substitution.\<close>
  have tyargs: "FI_TyArgs infoA = FI_TyArgs info0"
    and ghostA: "FI_Ghost infoA = FI_Ghost info0"
    using infoA_eq by (simp_all add: apply_subst_to_funinfo_def)
  have len0: "length (CF_Args f0) = length (FI_TmArgs infoA)"
    using lenA by simp
  have len: "length (CF_Args f0) = length (FI_TmArgs ?infoM)"
    using len0 infoA_eq by (simp add: apply_subst_to_funinfo_def)
  have dist0: "distinct (CF_Args f0)"
    using distA by simp

  \<comment> \<open>The body chain (if there is a body).\<close>
  have body_case: "case CF_Body f0 of
                     None \<Rightarrow> True
                   | Some body0 \<Rightarrow>
                       core_statement_list_type
                         (module_body_env_for ?envM (CF_Args f0) ?infoM)
                         (FI_Ghost ?infoM)
                         (apply_subst_to_statement_list ?\<sigma>M body0) \<noteq> None"
  proof (cases "CF_Body f0")
    case None
    then show ?thesis by simp
  next
    case (Some body0)
    let ?bodyA = "apply_subst_to_statement_list ?\<sigma>A body0"
    let ?beA = "module_body_env_for ?envA (CF_Args f0) infoA"
    let ?e1 = "?beA \<lparr> TE_TypeVars := TE_TypeVars ?beA |\<union>| TE_TypeVars (CM_TyEnv b),
                      TE_RuntimeTypeVars :=
                        TE_RuntimeTypeVars ?beA
                        |\<union>| TE_RuntimeTypeVars (CM_TyEnv b) \<rparr>"
    let ?sb = "module_body_env_for ?mid (CF_Args f0) infoA"
    let ?tb = "module_body_env_for ?envM (CF_Args f0) ?infoM"
    have "core_statement_list_type ?beA (FI_Ghost infoA) ?bodyA \<noteq> None"
      using bodyA_ok Some by simp
    then obtain envOut where
        t0: "core_statement_list_type ?beA (FI_Ghost infoA) ?bodyA = Some envOut"
      by blast
    \<comment> \<open>Widen the tyvar fields by the b-side's.\<close>
    have t1: "core_statement_list_type ?e1 (FI_Ghost infoA) ?bodyA
                = Some (envOut
                    \<lparr> TE_TypeVars := TE_TypeVars envOut |\<union>| TE_TypeVars (CM_TyEnv b),
                      TE_RuntimeTypeVars :=
                        TE_RuntimeTypeVars envOut
                        |\<union>| TE_RuntimeTypeVars (CM_TyEnv b) \<rparr>)"
      using core_statement_list_type_irrelevant_tyvar[OF t0,
              where extraTV = "TE_TypeVars (CM_TyEnv b)"
                and extraRT = "TE_RuntimeTypeVars (CM_TyEnv b)"] .
    \<comment> \<open>Extend along the declaration axis into the mid body env.\<close>
    have cons1: "tyenv_ctors_consistent ?e1"
      using wfA unfolding tyenv_well_formed_def tyenv_ctors_consistent_def
      by (simp add: module_body_env_for_def)
    obtain envOut2 where
        t2: "core_statement_list_type ?sb (FI_Ghost infoA) ?bodyA = Some envOut2"
      using core_statement_list_type_tyenv_extends[OF t1
              link_mid_body_env_extends[OF linkA linkB linkM setMS ghostOK
                                           absa rtva absb rtvb]
              cons1]
      by blast
    \<comment> \<open>Substitute with the whole link's substitution.\<close>
    have mid_lk: "fmlookup (TE_Functions ?mid) name = Some infoA"
    proof -
      have "name |\<in>| fmdom (fmmap (apply_subst_to_funinfo ?\<sigma>A)
                                   (TE_Functions (CM_TyEnv a)))"
        using a_raw by (auto intro: fmdomI)
      then show ?thesis
        using a_raw infoA_eq by (auto simp: fmadd_drop_lookup)
    qed
    have wf_sb: "tyenv_well_formed ?sb"
      using module_body_env_for_well_formed[OF
              link_mid_env_well_formed[OF linkA wtA linkB wtB linkM setMS ghostOK]
              mid_lk len0] .
    have ok_sb: "module_env_subst_ok ?\<sigma>M ?tb ?sb"
      using link_mid_body_env_subst_ok[OF linkM m_raw tyargs
              link_mid_env_subst_ok[OF linkA wtA linkB wtB linkM setMS] absM] .
    have rt_sb: "module_env_subst_runtime_ok ?\<sigma>M ?tb ?sb"
      using link_mid_body_env_runtime_ok[OF linkA linkB linkM setMS
                                            m_raw tyargs ghostA absM rtvM] .
    have t3: "core_statement_list_type (apply_subst_to_module_env ?\<sigma>M ?tb ?sb)
                (FI_Ghost infoA)
                (apply_subst_to_statement_list ?\<sigma>M ?bodyA)
                = Some (apply_subst_to_module_env ?\<sigma>M ?tb envOut2)"
      using core_statement_list_type_subst_module_env[OF t2 wf_sb ok_sb] rt_sb
      by blast
    \<comment> \<open>Collapse the env and absorb the a-side substitution in the body.\<close>
    have t4: "core_statement_list_type ?tb (FI_Ghost infoA)
                (apply_subst_to_statement_list ?\<sigma>M body0)
                = Some (apply_subst_to_module_env ?\<sigma>M ?tb envOut2)"
      using t3
      unfolding link_mid_body_env_collapse[OF linkA linkB linkM setMS infoA_eq]
                subst_absorb_statement_list[OF absA] .
    show ?thesis
      using t4 unfolding Some ghostA by auto
  qed

  have "fmlookup (TE_Functions ?envM) name = Some ?infoM \<and>
        length (CF_Args f0) = length (FI_TmArgs ?infoM) \<and>
        distinct (CF_Args f0) \<and>
        (case CF_Body f0 of
           None \<Rightarrow> True
         | Some body0 \<Rightarrow>
             core_statement_list_type
               (module_body_env_for ?envM (CF_Args f0) ?infoM)
               (FI_Ghost ?infoM)
               (apply_subst_to_statement_list ?\<sigma>M body0) \<noteq> None)"
    using m_decl len dist0 body_case by blast
  then show ?thesis by blast
qed


(* ========================================================================== *)
(* The whole-program theorem: linking preserves well-typedness                *)
(* ========================================================================== *)

theorem link_preserves_well_typed:
  assumes linkA: "link_modules as = Inr a"
      and wtA: "core_module_well_typed a"
      and linkB: "link_modules bs = Inr b"
      and wtB: "core_module_well_typed b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
      and ghostOK: "\<forall>x \<in> set ms. module_ghost_subsets_ok x"
  shows "core_module_well_typed m"
proof -
  let ?\<sigma>M = "CM_TypeSubst m"
  let ?envM = "CM_TyEnv (normalize_module m)"
  note fM = link_modules_result_fields[OF linkM]
  have setMS': "set ms = set bs \<union> set as" using setMS by auto

  \<comment> \<open>Structural conjuncts.\<close>
  have idem: "idempotent_subst ?\<sigma>M"
    using link_modules_idempotent_subst[OF linkM] .
  have cap: "capture_avoiding m"
    using link_modules_capture_avoiding[OF linkM] .
  have wkA: "typesubst_well_kinded (CM_TyEnv a) (CM_TypeSubst a)"
    and wkB: "typesubst_well_kinded (CM_TyEnv b) (CM_TypeSubst b)"
    using wtA wtB unfolding core_module_well_typed_def by blast+
  have wk: "typesubst_well_kinded (CM_TyEnv m) ?\<sigma>M"
    using link_modules_typesubst_well_kinded[OF linkA linkB linkM setMS wkA wkB] .

  \<comment> \<open>Abstract types coincide with type variables (part of the module-scope
     clause below, and a side condition of the wf substitution engine).\<close>
  have abs_tv: "TE_AbstractTypes ?envM = TE_TypeVars ?envM"
    using link_pair_abs_tv(1)[OF linkA wtA linkB wtB linkM setMS] by simp

  \<comment> \<open>Clause 1: well-formedness, via the mid env and the wf substitution engine.\<close>
  have wf: "tyenv_well_formed ?envM"
  proof -
    have absa0: "TE_AbstractTypes (CM_TyEnv (normalize_module a))
                   = TE_TypeVars (CM_TyEnv (normalize_module a))"
      using wtA unfolding core_module_well_typed_def normalized_module_well_typed_def
                          tyenv_module_scope_def
      by blast
    have absb0: "TE_AbstractTypes (CM_TyEnv (normalize_module b))
                   = TE_TypeVars (CM_TyEnv (normalize_module b))"
      using wtB unfolding core_module_well_typed_def normalized_module_well_typed_def
                          tyenv_module_scope_def
      by blast
    have mid_abs: "TE_AbstractTypes (link_mid_env a b m)
                     = TE_TypeVars (link_mid_env a b m)"
      using absa0 absb0 by simp
    have abs_target: "TE_AbstractTypes ?envM = TE_TypeVars ?envM"
      using abs_tv .
    have rtv_target: "TE_RuntimeTypeVars ?envM |\<subseteq>| TE_TypeVars ?envM"
      using link_pair_abs_tv(2)[OF linkA wtA linkB wtB linkM setMS] by simp
    have "tyenv_well_formed (apply_subst_to_module_env ?\<sigma>M ?envM (link_mid_env a b m))"
      using tyenv_well_formed_apply_subst_to_module_env[OF
              link_mid_env_well_formed[OF linkA wtA linkB wtB linkM setMS ghostOK]
              link_mid_env_subst_ok[OF linkA wtA linkB wtB linkM setMS]
              link_mid_env_runtime_ok[OF linkA linkB linkM setMS]
              mid_abs abs_target rtv_target] .
    then show ?thesis
      unfolding link_mid_env_collapse[OF linkA linkB linkM setMS] .
  qed

  \<comment> \<open>Clause 2: module scope (inert scope fields plus Abs = TV).\<close>
  have scope: "tyenv_module_scope ?envM"
    unfolding tyenv_module_scope_def
    using abs_tv fM(1,10,11,12,3,5,9) by auto

  \<comment> \<open>Clause 3: globals. Each defined global comes from one input module,
      hence from one sub-link; route through the matching contribution lemma.\<close>
  have globals: "module_globals_well_typed ?envM (CM_GlobalVars (normalize_module m))"
    unfolding module_globals_well_typed_def
  proof (intro allI impI)
    fix name tm
    assume "fmlookup (CM_GlobalVars (normalize_module m)) name = Some tm"
    then have "fmlookup (fmmap (apply_subst_to_term ?\<sigma>M) (CM_GlobalVars m)) name
                 = Some tm"
      by simp
    then obtain tm0 where
        m_lk: "fmlookup (CM_GlobalVars m) name = Some tm0" and
        tm_eq: "tm = apply_subst_to_term ?\<sigma>M tm0"
      by (cases "fmlookup (CM_GlobalVars m) name") auto
    have gdisj: "fmdisjoint_list (map CM_GlobalVars ms)"
      using link_modules_success_facts(1)[OF linkM]
      unfolding link_fields_disjoint_def by blast
    have "\<exists>s \<in> set (map CM_GlobalVars ms). fmlookup s name = Some tm0"
      using m_lk unfolding fM(18) using fmlist_union_lookup[OF gdisj] by blast
    then obtain z where z_in: "z \<in> set ms"
                    and z_lk: "fmlookup (CM_GlobalVars z) name = Some tm0"
      by auto
    from z_in setMS have "z \<in> set as \<or> z \<in> set bs" by auto
    then have contrib: "\<exists>declTy.
        fmlookup (TE_GlobalVars ?envM) name = Some declTy \<and>
        (if name |\<in>| TE_GhostGlobals ?envM
         then core_term_type ?envM Ghost (apply_subst_to_term ?\<sigma>M tm0) = Some declTy
         else is_constant_term (apply_subst_to_term ?\<sigma>M tm0) \<and>
              core_term_type ?envM NotGhost (apply_subst_to_term ?\<sigma>M tm0)
                = Some declTy)"
    proof (elim disjE)
      assume zA: "z \<in> set as"
      have adisj: "fmdisjoint_list (map CM_GlobalVars as)"
        using link_modules_success_facts(1)[OF linkA]
        unfolding link_fields_disjoint_def by blast
      have a_lk: "fmlookup (CM_GlobalVars a) name = Some tm0"
        unfolding link_modules_result_fields(18)[OF linkA]
        using fmlist_union_lookup[OF adisj] zA z_lk by fastforce
      show ?thesis
        using link_mid_globals_contribution[OF linkA wtA linkB wtB linkM setMS
                                               ghostOK a_lk] .
    next
      assume zB: "z \<in> set bs"
      have bdisj: "fmdisjoint_list (map CM_GlobalVars bs)"
        using link_modules_success_facts(1)[OF linkB]
        unfolding link_fields_disjoint_def by blast
      have b_lk: "fmlookup (CM_GlobalVars b) name = Some tm0"
        unfolding link_modules_result_fields(18)[OF linkB]
        using fmlist_union_lookup[OF bdisj] zB z_lk by fastforce
      show ?thesis
        using link_mid_globals_contribution[OF linkB wtB linkA wtA linkM setMS'
                                               ghostOK b_lk] .
    qed
    show "\<exists>declTy.
        fmlookup (TE_GlobalVars ?envM) name = Some declTy \<and>
        (if name |\<in>| TE_GhostGlobals ?envM
         then core_term_type ?envM Ghost tm = Some declTy
         else is_constant_term tm \<and>
              core_term_type ?envM NotGhost tm = Some declTy)"
      unfolding tm_eq using contrib .
  qed

  \<comment> \<open>Clause 4: functions, likewise.\<close>
  have funcs: "module_functions_well_typed ?envM (CM_Functions (normalize_module m))"
    unfolding module_functions_well_typed_def
  proof (intro allI impI)
    fix name f
    assume "fmlookup (CM_Functions (normalize_module m)) name = Some f"
    then have "fmlookup (fmmap (\<lambda>g. g \<lparr> CF_Body :=
                    map_option (apply_subst_to_statement_list ?\<sigma>M) (CF_Body g) \<rparr>)
                  (CM_Functions m)) name = Some f"
      by simp
    then obtain f0 where
        m_lk: "fmlookup (CM_Functions m) name = Some f0" and
        f_eq: "f = f0 \<lparr> CF_Body :=
                  map_option (apply_subst_to_statement_list ?\<sigma>M) (CF_Body f0) \<rparr>"
      by (cases "fmlookup (CM_Functions m) name") auto
    have fdisj: "fmdisjoint_list (map CM_Functions ms)"
      using link_modules_success_facts(1)[OF linkM]
      unfolding link_fields_disjoint_def by blast
    have "\<exists>s \<in> set (map CM_Functions ms). fmlookup s name = Some f0"
      using m_lk unfolding fM(19) using fmlist_union_lookup[OF fdisj] by blast
    then obtain z where z_in: "z \<in> set ms"
                    and z_lk: "fmlookup (CM_Functions z) name = Some f0"
      by auto
    from z_in setMS have "z \<in> set as \<or> z \<in> set bs" by auto
    then have contrib: "\<exists>info.
        fmlookup (TE_Functions ?envM) name = Some info \<and>
        length (CF_Args f0) = length (FI_TmArgs info) \<and>
        distinct (CF_Args f0) \<and>
        (case CF_Body f0 of
           None \<Rightarrow> True
         | Some body0 \<Rightarrow>
             core_statement_list_type
               (module_body_env_for ?envM (CF_Args f0) info)
               (FI_Ghost info)
               (apply_subst_to_statement_list ?\<sigma>M body0) \<noteq> None)"
    proof (elim disjE)
      assume zA: "z \<in> set as"
      have adisj: "fmdisjoint_list (map CM_Functions as)"
        using link_modules_success_facts(1)[OF linkA]
        unfolding link_fields_disjoint_def by blast
      have a_lk: "fmlookup (CM_Functions a) name = Some f0"
        unfolding link_modules_result_fields(19)[OF linkA]
        using fmlist_union_lookup[OF adisj] zA z_lk by fastforce
      show ?thesis
        using link_mid_functions_contribution[OF linkA wtA linkB wtB linkM setMS
                                                 ghostOK a_lk] .
    next
      assume zB: "z \<in> set bs"
      have bdisj: "fmdisjoint_list (map CM_Functions bs)"
        using link_modules_success_facts(1)[OF linkB]
        unfolding link_fields_disjoint_def by blast
      have b_lk: "fmlookup (CM_Functions b) name = Some f0"
        unfolding link_modules_result_fields(19)[OF linkB]
        using fmlist_union_lookup[OF bdisj] zB z_lk by fastforce
      show ?thesis
        using link_mid_functions_contribution[OF linkB wtB linkA wtA linkM setMS'
                                                 ghostOK b_lk] .
    qed
    then obtain info where
        i_decl: "fmlookup (TE_Functions ?envM) name = Some info" and
        i_len: "length (CF_Args f0) = length (FI_TmArgs info)" and
        i_dist: "distinct (CF_Args f0)" and
        i_body: "case CF_Body f0 of
                   None \<Rightarrow> True
                 | Some body0 \<Rightarrow>
                     core_statement_list_type
                       (module_body_env_for ?envM (CF_Args f0) info)
                       (FI_Ghost info)
                       (apply_subst_to_statement_list ?\<sigma>M body0) \<noteq> None"
      by blast
    show "\<exists>info.
        fmlookup (TE_Functions ?envM) name = Some info \<and>
        length (CF_Args f) = length (FI_TmArgs info) \<and>
        distinct (CF_Args f) \<and>
        (case CF_Body f of
           None \<Rightarrow> True
         | Some body \<Rightarrow>
             core_statement_list_type
               (module_body_env_for ?envM (CF_Args f) info)
               (FI_Ghost info) body \<noteq> None)"
    proof (cases "CF_Body f0")
      case None
      then have fb: "CF_Body f = None"
        using f_eq by simp
      have fa: "CF_Args f = CF_Args f0"
        using f_eq by simp
      have "fmlookup (TE_Functions ?envM) name = Some info \<and>
            length (CF_Args f) = length (FI_TmArgs info) \<and>
            distinct (CF_Args f) \<and>
            (case CF_Body f of
               None \<Rightarrow> True
             | Some body \<Rightarrow>
                 core_statement_list_type
                   (module_body_env_for ?envM (CF_Args f) info)
                   (FI_Ghost info) body \<noteq> None)"
        unfolding fa fb using i_decl i_len i_dist by simp
      then show ?thesis by blast
    next
      case (Some body0)
      then have fb: "CF_Body f = Some (apply_subst_to_statement_list ?\<sigma>M body0)"
        using f_eq by simp
      have fa: "CF_Args f = CF_Args f0"
        using f_eq by simp
      have body': "core_statement_list_type
                     (module_body_env_for ?envM (CF_Args f0) info)
                     (FI_Ghost info)
                     (apply_subst_to_statement_list ?\<sigma>M body0) \<noteq> None"
        using i_body Some by simp
      have "fmlookup (TE_Functions ?envM) name = Some info \<and>
            length (CF_Args f) = length (FI_TmArgs info) \<and>
            distinct (CF_Args f) \<and>
            (case CF_Body f of
               None \<Rightarrow> True
             | Some body \<Rightarrow>
                 core_statement_list_type
                   (module_body_env_for ?envM (CF_Args f) info)
                   (FI_Ghost info) body \<noteq> None)"
        unfolding fa fb using i_decl i_len i_dist body' by simp
      then show ?thesis by blast
    qed
  qed

  have nwt: "normalized_module_well_typed (normalize_module m)"
    unfolding normalized_module_well_typed_def
    using wf scope globals funcs by blast
  have tvdisj: "fmdom ?\<sigma>M |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}"
    unfolding fM(6) by auto
  have inv: "core_module_invariant m"
    using core_module_invariant_intro[OF idem cap tvdisj nwt] .
  show ?thesis
    unfolding core_module_well_typed_def
    using inv wk nwt by blast
qed

end
