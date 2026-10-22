theory LinkPreservesWellTyped
  imports LinkSubstRanges TypeSubstModuleEnv TyEnvExtension CoreModuleTypecheck
          CoreStmtTypecheckLemmas CoreValueTransfer AllocLevelSubst
begin

(* The whole-program "linking preserves well-typedness" theorem:

     link_modules as = Inr a,  core_module_well_typed a,
     link_modules bs = Inr b,  core_module_well_typed b,
     link_modules ms = Inr m,  set ms = set as \<union> set bs
     \<Longrightarrow> core_module_well_typed m

   Proof outline:

   The core_module_invariant conjunct of core_module_well_typed m follows
   from link_modules_idempotent_subst, link_modules_capture_avoiding, the
   linked result's field shape, and core_module_invariant_intro; the
   typesubst_well_kinded conjunct is link_modules_typesubst_well_kinded and
   the typesubst_complete conjunct is link_modules_typesubst_complete; the
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
   substitution. Hence: extend first, substitute second.

   The mid env is NOT well-formed in general: a datatype declared by a
   module both sides share holds the a-side's entry, which may resolve
   fewer abstract types than the b-side's, so a b-side signature can be
   runtime in b but not in the mid env. The engine only needs distinct
   binders (tyenv_binders_distinct), which the mid env has; the
   well-formedness of normalize_module m's env is proved directly
   (link_normalized_env_well_formed), clause by clause, running each entry
   through its own side's mid env. *)


(* ========================================================================== *)
(* Projections of apply_subst_to_tyenv and normalize_module                   *)
(* ========================================================================== *)

lemma apply_subst_to_tyenv_simps [simp]:
  "TE_LocalVars (apply_subst_to_tyenv subst env) = TE_LocalVars env"
  "TE_GlobalVars (apply_subst_to_tyenv subst env)
     = fmmap (apply_subst subst) (TE_GlobalVars env)"
  "TE_GhostLocals (apply_subst_to_tyenv subst env) = TE_GhostLocals env"
  "TE_ConstLocals (apply_subst_to_tyenv subst env) = TE_ConstLocals env"
  "TE_TypeVars (apply_subst_to_tyenv subst env) = TE_TypeVars env"
  "TE_RuntimeTypeVars (apply_subst_to_tyenv subst env) = TE_RuntimeTypeVars env"
  \<comment> \<open>(7) is a consequence of (18): TE_AbstractTypes is the domain of the level
      map. It is kept so that the equation numbering is stable.\<close>
  "TE_AbstractTypes (apply_subst_to_tyenv subst env) = TE_AbstractTypes env"
  "TE_ReturnType (apply_subst_to_tyenv subst env) = TE_ReturnType env"
  "TE_FunctionGhost (apply_subst_to_tyenv subst env) = TE_FunctionGhost env"
  "TE_FunctionImpure (apply_subst_to_tyenv subst env) = TE_FunctionImpure env"
  "TE_ProofGoal (apply_subst_to_tyenv subst env) = TE_ProofGoal env"
  "TE_ProofTopLevel (apply_subst_to_tyenv subst env) = TE_ProofTopLevel env"
  "TE_Functions (apply_subst_to_tyenv subst env)
     = fmmap (apply_subst_to_funinfo subst) (TE_Functions env)"
  "TE_Datatypes (apply_subst_to_tyenv subst env) = TE_Datatypes env"
  "TE_DataCtors (apply_subst_to_tyenv subst env)
     = fmmap (apply_subst_to_datactor subst) (TE_DataCtors env)"
  "TE_DataCtorsByType (apply_subst_to_tyenv subst env) = TE_DataCtorsByType env"
  "TE_AbstractAllocLevels (apply_subst_to_tyenv subst env) = TE_AbstractAllocLevels env"
  by (simp_all add: apply_subst_to_tyenv_def)

(* The ghost set of a substituted env, in the normal form simp leaves. *)
lemma ghost_datatypes_r_apply_subst_to_tyenv:
  assumes "TE_DataCtors env' = fmmap (apply_subst_to_datactor subst) (TE_DataCtors env)"
      and "TE_Datatypes env' = TE_Datatypes env"
      and "TE_DataCtorsByType env' = TE_DataCtorsByType env"
  shows "ghost_datatypes_r (apply_subst_to_tyenv subst env) R = ghost_datatypes_r env' R"
  by (rule ghost_datatypes_r_cong) (simp_all add: assms)

lemma normalize_module_simps [simp]:
  "CM_TyEnv (normalize_module x) = apply_subst_to_tyenv (CM_TypeSubst x) (CM_TyEnv x)"
  "CM_GlobalVars (normalize_module x) = CM_GlobalVars x"
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
(* Substitutions that agree on all types act identically on statements        *)
(* (the term version, apply_subst_to_term_cong_subst, is in TypeSubstTerm)    *)
(* ========================================================================== *)

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
  case (6 s1 ghost ty lhsTm rhsTm)
  show ?case by (simp add: "6.prems" apply_subst_to_term_cong_subst[OF "6.prems"])
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
    by (metis (lifting) ext "12.IH" "12.prems" apply_subst_to_statement.simps(12)
        apply_subst_to_term_cong_subst)
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
  moreover have "\<And>tms. map (apply_subst_to_term \<tau>) (map (apply_subst_to_term \<sigma>) tms)
                       = map (apply_subst_to_term \<tau>) tms"
    and "\<And>tms. map (apply_subst_to_term \<tau> \<circ> apply_subst_to_term \<sigma>) tms
                = map (apply_subst_to_term \<tau>) tms"
    by (simp_all add: subst_absorb_term[OF abs] comp_def)
  ultimately show ?thesis
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
   for WELL-KINDED types, provided no datatype of the source env's domain
   that is runtime there is ghost in the target (well-kindedness pins every
   datatype name of the type into that domain). Mirrors
   is_runtime_type_tyenv_extends. *)
lemma is_runtime_type_transfer_mono:
  assumes wk: "is_well_kinded env1 ty"
      and rt: "is_runtime_type env1 ty"
      and rtv: "fset (TE_RuntimeTypeVars env1) \<subseteq> fset (TE_RuntimeTypeVars env2)"
      and gd: "\<And>n. n |\<in>| fmdom (TE_Datatypes env1) \<Longrightarrow> n \<notin> ghost_datatypes env1
                 \<Longrightarrow> n \<notin> ghost_datatypes env2"
  shows "is_runtime_type env2 ty"
proof (rule is_runtime_type_mono_heads[OF rt _ rtv])
  fix d assume "d \<in> type_datatypes ty" and "d \<notin> ghost_datatypes env1"
  moreover have "d |\<in>| fmdom (TE_Datatypes env1)"
    using is_well_kinded_type_datatypes_subset[OF wk] \<open>d \<in> type_datatypes ty\<close> by auto
  ultimately show "d \<notin> ghost_datatypes env2" using gd by blast
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
    and "TE_ConstLocals (CM_TyEnv m) = {||}"                                        \<comment> \<open>(4)\<close>
    and "TE_TypeVars (CM_TyEnv m)
           = funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) ms)
             |-| fmdom (CM_TypeSubst m)"                                            \<comment> \<open>(5)\<close>
    and "TE_RuntimeTypeVars (CM_TyEnv m)
           = funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) ms)
             |-| fmdom (CM_TypeSubst m)"                                            \<comment> \<open>(6)\<close>
    \<comment> \<open>(7) is the domain form of (19); kept so that the numbering is stable.\<close>
    and "TE_AbstractTypes (CM_TyEnv m)
           = funion_list (map (\<lambda>x. TE_AbstractTypes (CM_TyEnv x)) ms)
             |-| fmdom (CM_TypeSubst m)"                                            \<comment> \<open>(7)\<close>
    and "TE_ReturnType (CM_TyEnv m) = CoreTy_Record []"                             \<comment> \<open>(8)\<close>
    and "TE_FunctionGhost (CM_TyEnv m) = NotGhost"                                  \<comment> \<open>(9)\<close>
    and "TE_ProofGoal (CM_TyEnv m) = None"                                          \<comment> \<open>(10)\<close>
    and "TE_ProofTopLevel (CM_TyEnv m) = False"                                     \<comment> \<open>(11)\<close>
    and "TE_Functions (CM_TyEnv m)
           = fmlist_union (map (\<lambda>x. TE_Functions (CM_TyEnv x)) ms)"                \<comment> \<open>(12)\<close>
    and "TE_Datatypes (CM_TyEnv m)
           = fmlist_union (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) ms)"                \<comment> \<open>(13)\<close>
    and "TE_DataCtors (CM_TyEnv m)
           = fmlist_union (map (\<lambda>x. TE_DataCtors (CM_TyEnv x)) ms)"                \<comment> \<open>(14)\<close>
    and "TE_DataCtorsByType (CM_TyEnv m)
           = fmlist_union (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) ms)"          \<comment> \<open>(15)\<close>
    and "CM_GlobalVars m = fmlist_union (map CM_GlobalVars ms)"                     \<comment> \<open>(16)\<close>
    and "CM_Functions m = fmlist_union (map CM_Functions ms)"                       \<comment> \<open>(17)\<close>
    and "\<not> TE_FunctionImpure (CM_TyEnv m)"                                         \<comment> \<open>(18)\<close>
    and "TE_AbstractAllocLevels (CM_TyEnv m)
           = fmdrop_fset (fmdom (CM_TypeSubst m))
               (fmlist_union (map (\<lambda>x. TE_AbstractAllocLevels (CM_TyEnv x)) ms))"  \<comment> \<open>(19)\<close>
proof -
  obtain \<sigma> where meq: "m = link_result ms \<sigma>"
    using ok link_modules_Inr_iff by blast
  show "TE_LocalVars (CM_TyEnv m) = fmempty"
    and "TE_GlobalVars (CM_TyEnv m)
           = fmlist_union (map (\<lambda>x. TE_GlobalVars (CM_TyEnv x)) ms)"
    and "TE_GhostLocals (CM_TyEnv m) = {||}"
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
    and "CM_GlobalVars m = fmlist_union (map CM_GlobalVars ms)"
    and "CM_Functions m = fmlist_union (map CM_Functions ms)"
    and "\<not> TE_FunctionImpure (CM_TyEnv m)"
    and "TE_AbstractAllocLevels (CM_TyEnv m)
           = fmdrop_fset (fmdom (CM_TypeSubst m))
               (fmlist_union (map (\<lambda>x. TE_AbstractAllocLevels (CM_TyEnv x)) ms))"
    unfolding meq link_result_def by (simp_all add: fmdom_fmlist_union comp_def)
qed

(* The checks and closure facts of a successful link, phrased against the
   result's own CM_TypeSubst. Reference order: (1) link_fields_disjoint,
   (2) fmdisjoint_list of the substitution family, (3) acyclicity of the raw
   union, (4) closure, (5) link_capture_ok, (6) link_runtime_ok,
   (7) link_alloc_ok. *)
lemma link_modules_success_facts:
  assumes ok: "link_modules ms = Inr m"
  shows "link_fields_disjoint ms"
    and "fmdisjoint_list (map CM_TypeSubst ms)"
    and "acyclic_subst_deps (fmlist_union (map CM_TypeSubst ms))"
    and "is_subst_closure (fmlist_union (map CM_TypeSubst ms)) (CM_TypeSubst m)"
    and "link_capture_ok ms"
    and "link_runtime_ok ms (CM_TypeSubst m)"
    and "link_alloc_ok ms (CM_TypeSubst m)"
proof -
  obtain \<sigma> where
    fdisj: "link_fields_disjoint ms" and
    cap: "link_capture_ok ms" and
    sdisj: "fmdisjoint_list (map CM_TypeSubst ms)" and
    acyc: "acyclic_subst_deps (fmlist_union (map CM_TypeSubst ms))" and
    clos: "is_subst_closure (fmlist_union (map CM_TypeSubst ms)) \<sigma>" and
    rok: "link_runtime_ok ms \<sigma>" and
    aok: "link_alloc_ok ms \<sigma>" and
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
  show "link_alloc_ok ms (CM_TypeSubst m)" using aok \<sigma>eq by simp
qed

(* The R2 runtime-resolution check, massaged into consumable form: a resolved
   name that was a runtime abstract type of SOME input resolves to a runtime
   type in the normalized linked env. *)
lemma link_modules_runtime_resolution:
  assumes ok: "link_modules ms = Inr m"
      and n_rtv: "n |\<in>| funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) ms)"
      and lk: "fmlookup (CM_TypeSubst m) n = Some ty"
  shows "is_runtime_type (CM_TyEnv (normalize_module m)) ty"
proof -
  obtain \<sigma> where rok: "link_runtime_ok ms \<sigma>" and meq: "m = link_result ms \<sigma>"
    using ok link_modules_Inr_iff by blast
  have \<sigma>eq: "CM_TypeSubst m = \<sigma>"
    using meq by (simp add: link_result_def)
  have n_dom: "n |\<in>| fmdom \<sigma>"
    using lk \<sigma>eq by (auto intro: fmdomI)
  have "is_runtime_type (CM_TyEnv (normalize_module (link_result ms \<sigma>))) (the (fmlookup \<sigma> n))"
    using rok n_dom n_rtv unfolding link_runtime_ok_def by auto
  then show ?thesis using meq \<sigma>eq lk by simp
qed

(* Linking preserves the standing module invariant: if every input satisfies
   core_module_invariant, so does a successful link's result. Idempotence,
   capture-avoidance and binder freshness are the existing
   link_modules_idempotent_subst / link_modules_capture_avoiding /
   link_modules_tyvars_fresh; the substitution-domain/TE_TypeVars
   disjointness and the inert scope fields are immediate from link_result's
   construction; the tyvar-subset and abstract-types-equality clauses are
   inherited pointwise from the inputs (these are the conjuncts that
   genuinely need the per-input hypothesis - the linker unions the tyvar
   fsets with no check of its own). *)
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
  have ghost: "module_tyvars_fresh m"
    using link_modules_tyvars_fresh[OF ok] .
  have tv: "fmdom (CM_TypeSubst m) |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}"
    unfolding fM(5) by auto

  \<comment> \<open>Tyvar subsets: pointwise from the inputs; the same domain is subtracted
     on both sides.\<close>
  have rtv: "TE_RuntimeTypeVars (CM_TyEnv m) |\<subseteq>| TE_TypeVars (CM_TyEnv m)"
  proof
    fix n assume n_in: "n |\<in>| TE_RuntimeTypeVars (CM_TyEnv m)"
    have "\<exists>s \<in> set (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) ms). n |\<in>| s"
      using n_in unfolding fM(6) using funion_list_member by (metis fminus_iff)
    then obtain x where x_in: "x \<in> set ms"
                    and n_rtv: "n |\<in>| TE_RuntimeTypeVars (CM_TyEnv x)"
      by auto
    have "n |\<in>| TE_TypeVars (CM_TyEnv x)"
      using inv x_in n_rtv
      unfolding core_module_invariant_def by (blast dest: fsubsetD)
    then have "n |\<in>| funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) ms)"
      using x_in funion_list_member by fastforce
    moreover have "n |\<notin>| fmdom (CM_TypeSubst m)"
      using n_in unfolding fM(6) by auto
    ultimately show "n |\<in>| TE_TypeVars (CM_TyEnv m)"
      unfolding fM(5) by auto
  qed
  \<comment> \<open>Abstract types: each input has TE_AbstractTypes = TE_TypeVars, and the
     linker builds the level map's domain and TE_TypeVars as the same
     union-minus-domain, so the equality carries over by congruence.\<close>
  have abs_tv: "TE_AbstractTypes (CM_TyEnv m) = TE_TypeVars (CM_TyEnv m)"
  proof -
    have "map (\<lambda>x. TE_AbstractTypes (CM_TyEnv x)) ms
            = map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) ms"
      using inv
      unfolding core_module_invariant_def tyenv_module_scope_def
      by (intro list.map_cong0) blast
    then show ?thesis
      unfolding fM(5) fM(7) by metis
  qed

  have scope: "tyenv_module_scope (CM_TyEnv m)"
    unfolding tyenv_module_scope_def
    by (simp add: fM(1) fM(3) fM(4) fM(8) fM(9) fM(10) fM(11) fM(18) abs_tv)

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
    using fmlist_union_sublist_lookup[OF link_modules_success_facts(2)[OF linkM],
                                      of "map CM_TypeSubst as"] sub by auto
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
  have dM: "link_fields_disjoint ms"
    using link_modules_success_facts(1)[OF linkM] by blast
  \<comment> \<open>One generic step per family.\<close>
  have step: "fmlookup (fmlist_union (map f as)) k0 = Some v0
                \<Longrightarrow> fmdisjoint_list (map f ms)
                \<Longrightarrow> fmlookup (fmlist_union (map f ms)) k0 = Some v0"
    for f :: "CoreModule \<Rightarrow> ('x :: type, 'y :: type) fmap" and k0 v0
  proof -
    assume l: "fmlookup (fmlist_union (map f as)) k0 = Some v0"
       and dm: "fmdisjoint_list (map f ms)"
    have "set (map f as) \<subseteq> set (map f ms)" using sub by auto
    then show "fmlookup (fmlist_union (map f ms)) k0 = Some v0"
      using fmlist_union_sublist_lookup[OF dm _ l] by blast
  qed
  show "fmlookup (TE_GlobalVars (CM_TyEnv a)) k = Some v
          \<Longrightarrow> fmlookup (TE_GlobalVars (CM_TyEnv m)) k = Some v"
    unfolding fA(2) fM(2)
    using step dM unfolding link_fields_disjoint_def by fastforce
  show "fmlookup (TE_Functions (CM_TyEnv a)) k2 = Some v2
          \<Longrightarrow> fmlookup (TE_Functions (CM_TyEnv m)) k2 = Some v2"
    unfolding fA(12) fM(12)
    using step dM unfolding link_fields_disjoint_def by fastforce
  show "fmlookup (TE_Datatypes (CM_TyEnv a)) k3 = Some v3
          \<Longrightarrow> fmlookup (TE_Datatypes (CM_TyEnv m)) k3 = Some v3"
    unfolding fA(13) fM(13)
    using step dM unfolding link_fields_disjoint_def by fastforce
  show "fmlookup (TE_DataCtors (CM_TyEnv a)) k4 = Some v4
          \<Longrightarrow> fmlookup (TE_DataCtors (CM_TyEnv m)) k4 = Some v4"
    unfolding fA(14) fM(14)
    using step dM unfolding link_fields_disjoint_def by fastforce
  show "fmlookup (TE_DataCtorsByType (CM_TyEnv a)) k5 = Some v5
          \<Longrightarrow> fmlookup (TE_DataCtorsByType (CM_TyEnv m)) k5 = Some v5"
    unfolding fA(15) fM(15)
    using step dM unfolding link_fields_disjoint_def by fastforce
  show "fmlookup (CM_GlobalVars a) k6 = Some v6
          \<Longrightarrow> fmlookup (CM_GlobalVars m) k6 = Some v6"
    unfolding fA(16) fM(16)
    using step dM unfolding link_fields_disjoint_def by fastforce
  show "fmlookup (CM_Functions a) k7 = Some v7
          \<Longrightarrow> fmlookup (CM_Functions m) k7 = Some v7"
    unfolding fA(17) fM(17)
    using step dM unfolding link_fields_disjoint_def by fastforce
qed

(* The binders of a sub-link's declarations avoid the whole link's abstract
   types (the second conjunct of the capture check, read at one declaration
   of a sub-link's env; the entry comes from one input of the sub-link,
   which is an input of the whole link). Reference order: (1) functions,
   (2) constructors. *)
lemma link_side_binders_fresh:
  assumes linkA: "link_modules as = Inr a"
      and linkM: "link_modules ms = Inr m"
      and sub: "set as \<subseteq> set ms"
  shows "fmlookup (TE_Functions (CM_TyEnv a)) k = Some info \<Longrightarrow>
           fset_of_list (FI_TyArgs info)
             |\<inter>| funion_list (map (\<lambda>y. TE_AbstractTypes (CM_TyEnv y)) ms) = {||}"
    and "fmlookup (TE_DataCtors (CM_TyEnv a)) k2 = Some (dtName, tyVars, payload) \<Longrightarrow>
           fset_of_list tyVars
             |\<inter>| funion_list (map (\<lambda>y. TE_AbstractTypes (CM_TyEnv y)) ms) = {||}"
proof -
  note fA = link_modules_result_fields[OF linkA]
  have cap: "link_capture_ok ms"
    using link_modules_success_facts(5)[OF linkM] .
  have dF: "fmdisjoint_list (map (\<lambda>x. TE_Functions (CM_TyEnv x)) as)"
    and dC: "fmdisjoint_list (map (\<lambda>x. TE_DataCtors (CM_TyEnv x)) as)"
    using link_modules_success_facts(1)[OF linkA]
    unfolding link_fields_disjoint_def by blast+
  show "fmlookup (TE_Functions (CM_TyEnv a)) k = Some info \<Longrightarrow>
          fset_of_list (FI_TyArgs info)
            |\<inter>| funion_list (map (\<lambda>y. TE_AbstractTypes (CM_TyEnv y)) ms) = {||}"
  proof -
    assume lk: "fmlookup (TE_Functions (CM_TyEnv a)) k = Some info"
    obtain x where x_in: "x \<in> set as"
        and x_lk: "fmlookup (TE_Functions (CM_TyEnv x)) k = Some info"
      using lk fmlist_union_lookup[OF dF] unfolding fA(12) by auto
    show "fset_of_list (FI_TyArgs info)
            |\<inter>| funion_list (map (\<lambda>y. TE_AbstractTypes (CM_TyEnv y)) ms) = {||}"
      using link_capture_ok_bound_fresh[OF cap _ module_bound_tyvars_fun[OF x_lk]]
            x_in sub fset_of_list.rep_eq in_mono by fastforce
  qed
  show "fmlookup (TE_DataCtors (CM_TyEnv a)) k2 = Some (dtName, tyVars, payload) \<Longrightarrow>
          fset_of_list tyVars
            |\<inter>| funion_list (map (\<lambda>y. TE_AbstractTypes (CM_TyEnv y)) ms) = {||}"
  proof -
    assume lk: "fmlookup (TE_DataCtors (CM_TyEnv a)) k2 = Some (dtName, tyVars, payload)"
    obtain x where x_in: "x \<in> set as"
        and x_lk: "fmlookup (TE_DataCtors (CM_TyEnv x)) k2 = Some (dtName, tyVars, payload)"
      using lk fmlist_union_lookup[OF dC] unfolding fA(14) by auto
    show "fset_of_list tyVars
            |\<inter>| funion_list (map (\<lambda>y. TE_AbstractTypes (CM_TyEnv y)) ms) = {||}"
      using link_capture_ok_bound_fresh[OF cap _ module_bound_tyvars_ctor[OF x_lk]]
            x_in sub fset_of_list.rep_eq subsetD by fastforce
  qed
qed


(* ========================================================================== *)
(* Set algebra: the whole link's type-variable fields split by side           *)
(* ========================================================================== *)

(* Reference order: (1) TE_TypeVars, (2) TE_RuntimeTypeVars,
   (3) TE_AbstractTypes. *)
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
    unfolding fM(5) fA(5) fB(5) by (rule gen)
  show "TE_RuntimeTypeVars (CM_TyEnv m)
          = (TE_RuntimeTypeVars (CM_TyEnv a) |-| fmdom (CM_TypeSubst m))
            |\<union>| (TE_RuntimeTypeVars (CM_TyEnv b) |-| fmdom (CM_TypeSubst m))"
    unfolding fM(6) fA(6) fB(6) by (rule gen)
  show "TE_AbstractTypes (CM_TyEnv m)
          = (TE_AbstractTypes (CM_TyEnv a) |-| fmdom (CM_TypeSubst m))
            |\<union>| (TE_AbstractTypes (CM_TyEnv b) |-| fmdom (CM_TypeSubst m))"
    unfolding fM(7) fA(7) fB(7) by (rule gen)
qed

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


(* ========================================================================== *)
(* The mixed intermediate environment                                         *)
(*                                                                            *)
(* link_mid_env a b m: the whole link's env (so the datatype table, by-type   *)
(* table and inert scope fields are already m's), except:                     *)
(*   - the tyvar fields are the UNIONS of the two sides' (nothing subtracted  *)
(*     - the substitution has not been applied yet), and so is the level map  *)
(*     (whose domain is then TE_TypeVars, as at any module level, since each  *)
(*     side's is);                                                            *)
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
       TE_AbstractAllocLevels :=
         TE_AbstractAllocLevels (CM_TyEnv a) ++\<^sub>f TE_AbstractAllocLevels (CM_TyEnv b),
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
  "TE_ConstLocals (link_mid_env a b m) = TE_ConstLocals (CM_TyEnv m)"
  "TE_TypeVars (link_mid_env a b m)
     = TE_TypeVars (CM_TyEnv a) |\<union>| TE_TypeVars (CM_TyEnv b)"
  "TE_RuntimeTypeVars (link_mid_env a b m)
     = TE_RuntimeTypeVars (CM_TyEnv a) |\<union>| TE_RuntimeTypeVars (CM_TyEnv b)"
  \<comment> \<open>(7) is the domain form of (18), kept for stable numbering. On
      module-level sides it is TE_TypeVars (CM_TyEnv a) |\<union>| TE_TypeVars
      (CM_TyEnv b), given each side's TE_AbstractTypes = TE_TypeVars.\<close>
  "TE_AbstractTypes (link_mid_env a b m)
     = TE_AbstractTypes (CM_TyEnv a) |\<union>| TE_AbstractTypes (CM_TyEnv b)"
  "TE_ReturnType (link_mid_env a b m) = TE_ReturnType (CM_TyEnv m)"
  "TE_FunctionGhost (link_mid_env a b m) = TE_FunctionGhost (CM_TyEnv m)"
  "TE_FunctionImpure (link_mid_env a b m) = TE_FunctionImpure (CM_TyEnv m)"
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
  "TE_AbstractAllocLevels (link_mid_env a b m)
     = TE_AbstractAllocLevels (CM_TyEnv a) ++\<^sub>f TE_AbstractAllocLevels (CM_TyEnv b)"
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
    using fmlist_union_sublist_lookup[OF dM, of "map f as"] setMS by auto
  have subB: "\<And>v. fmlookup ?uB k = Some v \<Longrightarrow> fmlookup ?uM k = Some v"
    using fmlist_union_sublist_lookup[OF dM, of "map f bs"] setMS by auto
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
              fA(12) fB(12) fM(12)
    by (metis (no_types, lifting) absA absB fdA fdB fdM fmmap_mid_collapse link_fields_disjoint_def
        setMS subst_absorb_funinfo)
  show "fmmap (apply_subst_to_datactor (CM_TypeSubst m)) (TE_DataCtors (link_mid_env a b m))
          = fmmap (apply_subst_to_datactor (CM_TypeSubst m)) (TE_DataCtors (CM_TyEnv m))"
    unfolding link_mid_env_simps normalize_module_simps apply_subst_to_tyenv_simps
              fA(14) fB(14) fM(14)
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
    show "TE_ReturnType (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_ReturnType (CM_TyEnv (normalize_module m))"
      by (simp add: fM(8))
    show "TE_FunctionGhost (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_FunctionGhost (CM_TyEnv (normalize_module m))"
      by simp
    show "TE_FunctionImpure (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_FunctionImpure (CM_TyEnv (normalize_module m))"
      by simp
    show "TE_ProofGoal (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_ProofGoal (CM_TyEnv (normalize_module m))"
      by (simp add: fM(10))
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
    show "TE_AbstractAllocLevels (apply_subst_to_module_env (CM_TypeSubst m)
            (CM_TyEnv (normalize_module m)) (link_mid_env a b m))
            = TE_AbstractAllocLevels (CM_TyEnv (normalize_module m))"
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
        using fA(6) by auto
      then show ?thesis unfolding funion_list_split[OF setMS] by auto
    next
      assume "n |\<in>| TE_RuntimeTypeVars (CM_TyEnv b)"
      then have "n |\<in>| funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) bs)"
        using fB(6) by auto
      then show ?thesis unfolding funion_list_split[OF setMS] by auto
    qed
  qed
  show "case fmlookup (CM_TypeSubst m) n of
           Some ty' \<Rightarrow> is_runtime_type (CM_TyEnv (normalize_module m)) ty'
         | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars (CM_TyEnv (normalize_module m))"
  proof (cases "fmlookup (CM_TypeSubst m) n")
    case (Some ty')
    have "is_runtime_type (CM_TyEnv (normalize_module m)) ty'"
      using link_modules_runtime_resolution[OF linkM n_union Some] .
    then show ?thesis using Some by simp
  next
    case None
    have "n |\<notin>| fmdom (CM_TypeSubst m)"
      using None by (simp add: fmdom_notI)
    then have "n |\<in>| TE_RuntimeTypeVars (CM_TyEnv m)"
      using fM(6) n_union by simp
    then show ?thesis using None by simp
  qed
qed

(* module_env_subst_ok: the datatype tables agree by construction (the
   normalized constructor table is the mid env's with the whole link's
   substitution applied, link_mid_env_family_collapse); the abstract types
   are the mid env's minus the resolved ones; the tyvar coverage is R3's
   transfer theorem (resolved case) plus set algebra (unresolved case); the
   binder-avoidance clauses are link_modules_capture_avoiding read back
   through the raw entries; and the ghost clause is antitonicity under the
   substitution (ghost_datatypes_subst_antitone), from the runtime check. *)
lemma link_mid_env_subst_ok:
  assumes linkA: "link_modules as = Inr a"
      and wtA: "core_module_well_typed a"
      and linkB: "link_modules bs = Inr b"
      and wtB: "core_module_well_typed b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
  shows "module_env_subst_ok (CM_TypeSubst m) (CM_TyEnv (normalize_module m))
                             (link_mid_env a b m)"
proof -
  note fA = link_modules_result_fields[OF linkA]
  note fB = link_modules_result_fields[OF linkB]
  note fM = link_modules_result_fields[OF linkM]
  note gsplit = link_pair_tyvar_split[OF linkA linkB linkM setMS]
  have wkA: "typesubst_well_kinded (CM_TyEnv a) (CM_TypeSubst a)"
    and wkB: "typesubst_well_kinded (CM_TyEnv b) (CM_TypeSubst b)"
    using wtA wtB unfolding core_module_well_typed_def by blast+
  have wkM: "typesubst_well_kinded (CM_TyEnv m) (CM_TypeSubst m)"
    using link_modules_typesubst_well_kinded[OF linkA linkB linkM setMS wkA wkB] .
  have capM: "capture_avoiding m"
    using link_modules_capture_avoiding[OF linkM] .

  \<comment> \<open>The table and tyvar clauses.\<close>
  have dt: "TE_Datatypes (CM_TyEnv (normalize_module m)) = TE_Datatypes (link_mid_env a b m)"
    by simp
  have bt: "TE_DataCtorsByType (CM_TyEnv (normalize_module m))
              = TE_DataCtorsByType (link_mid_env a b m)"
    by simp
  have dc: "TE_DataCtors (CM_TyEnv (normalize_module m))
              = fmmap (apply_subst_to_datactor (CM_TypeSubst m))
                      (TE_DataCtors (link_mid_env a b m))"
    by (simp add: link_mid_env_family_collapse(3)[OF linkA linkB linkM setMS, symmetric])
  have abs: "TE_AbstractTypes (CM_TyEnv (normalize_module m))
               = TE_AbstractTypes (link_mid_env a b m) |-| fmdom (CM_TypeSubst m)"
  proof (rule fset_eqI)
    fix x
    show "x |\<in>| TE_AbstractTypes (CM_TyEnv (normalize_module m))
            \<longleftrightarrow> x |\<in>| TE_AbstractTypes (link_mid_env a b m) |-| fmdom (CM_TypeSubst m)"
      by (auto simp: gsplit(3))
  qed

  have cov: "\<forall>n. n |\<in>| TE_TypeVars (link_mid_env a b m) \<longrightarrow>
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
          using fA(5) by auto
        then show ?thesis
          unfolding funion_list_split[OF setMS] by auto
      next
        assume "n |\<in>| TE_TypeVars (CM_TyEnv b)"
        then have "n |\<in>| funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) bs)"
          using fB(5) by auto
        then show ?thesis
          unfolding funion_list_split[OF setMS] by auto
      qed
      then have "n |\<in>| TE_TypeVars (CM_TyEnv m)"
        using fM(5) n_notdom by simp
      then show ?thesis using None by simp
    qed
  qed

  have fun_cap: "\<forall>funName info.
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
  have ctor_cap: "\<forall>ctorName dtName tyVars payload.
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

  \<comment> \<open>The ghost clause: resolving the runtime abstract types by runtime types
      (the runtime check) can only make datatypes runtime.\<close>
  have gd: "ghost_datatypes (CM_TyEnv (normalize_module m))
              \<subseteq> ghost_datatypes (link_mid_env a b m)"
  proof (rule ghost_datatypes_subst_antitone[OF dt bt dc abs _
                                               link_mid_env_runtime_ok[OF linkA linkB linkM setMS]])
    show "\<And>ctorName dtName tyVars payload.
            fmlookup (TE_DataCtors (link_mid_env a b m)) ctorName
              = Some (dtName, tyVars, payload) \<Longrightarrow>
            subst_names (CM_TypeSubst m) |\<inter>| fset_of_list tyVars = {||}"
      using ctor_cap by blast
    show "TE_RuntimeTypeVars (CM_TyEnv (normalize_module m))
            |\<subseteq>| TE_AbstractTypes (CM_TyEnv (normalize_module m))"
      using link_pair_abs_tv[OF linkA wtA linkB wtB linkM setMS] by simp
  qed

  show ?thesis
    unfolding module_env_subst_ok_def
    using dt bt dc abs gd cov fun_cap ctor_cap by blast
qed


(* ========================================================================== *)
(* Transfer into the mid env, and well-formedness of the normalized result   *)
(* (P2)                                                                       *)
(*                                                                            *)
(* An entry of an overlaid family comes verbatim from ONE side's normalized   *)
(* env, whose well-typedness supplies the side-local fact; the monotone       *)
(* transfer lemmas (link_side_wk_transfer / link_side_rt_transfer) carry it   *)
(* to that side's mid env (wider tyvar fields, the whole link's datatype      *)
(* table, and - for runtime-ness - the locality of the ghost set on the       *)
(* side's own datatypes); the substitution engine's lifting lemmas then carry *)
(* it through the whole link's substitution, where the mid env collapses onto *)
(* the normalized env. The ctors-by-type clause uses whole-link disjointness  *)
(* to identify the unique declaring module of a shared key.                   *)
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

(* On a sub-link's datatype, the mid env holds exactly the sub-link's
   constructor entries: the by-type list is the sub-link's (a submap of the
   whole link's), and the overlay prefers the a-side on every constructor
   the list names (which the sub-link declares, by its by-type
   consistency). *)
lemma link_mid_env_ctor_entries:
  assumes linkA: "link_modules as = Inr a"
      and linkM: "link_modules ms = Inr m"
      and sub: "set as \<subseteq> set ms"
      and wfA: "tyenv_well_formed (CM_TyEnv (normalize_module a))"
      and dom: "dt |\<in>| fmdom (TE_Datatypes (CM_TyEnv a))"
  shows "datatype_ctor_entries (link_mid_env a b m) dt
           = datatype_ctor_entries (CM_TyEnv (normalize_module a)) dt"
proof -
  let ?envA = "CM_TyEnv (normalize_module a)"
  have ne: "tyenv_datatypes_nonempty ?envA"
    and btc: "tyenv_ctors_by_type_consistent ?envA"
    using wfA unfolding tyenv_well_formed_def by blast+
  have "dt |\<in>| fmdom (TE_DataCtorsByType ?envA)"
    using ne dom unfolding tyenv_datatypes_nonempty_def by (auto dest: fsubsetD)
  then obtain cs where btA: "fmlookup (TE_DataCtorsByType ?envA) dt = Some cs"
    by (auto simp: fmlookup_dom_iff)
  have btM: "fmlookup (TE_DataCtorsByType (link_mid_env a b m)) dt = Some cs"
    using link_modules_decl_submaps(5)[OF linkA linkM sub, of dt cs] btA by simp
  have each: "\<And>cn. cn \<in> set cs \<Longrightarrow>
                fmlookup (TE_DataCtors (link_mid_env a b m)) cn
                  = fmlookup (TE_DataCtors ?envA) cn"
  proof -
    fix cn assume "cn \<in> set cs"
    then obtain tv p where "fmlookup (TE_DataCtors ?envA) cn = Some (dt, tv, p)"
      using btc btA unfolding tyenv_ctors_by_type_consistent_def by blast
    then have "cn |\<in>| fmdom (TE_DataCtors ?envA)" by (rule fmdomI)
    then show "fmlookup (TE_DataCtors (link_mid_env a b m)) cn
                 = fmlookup (TE_DataCtors ?envA) cn"
      by (simp add: fmadd_drop_lookup)
  qed
  show ?thesis
    unfolding datatype_ctor_entries_def btM btA option.case(2)
    by (rule arg_cong[where f = concat], rule map_cong[OF refl]) (simp only: each)
qed

(* Locality of the ghost set: a sub-link's datatype that is runtime in the
   sub-link's normalized env is runtime in the sub-link's mid env, for any
   runtime abstract types extending the sub-link's: the mid env holds the
   same constructor entries for the sub-link's datatypes, and their payloads
   mention only the sub-link's datatypes (well-kindedness). *)
lemma link_mid_env_ghost_local:
  assumes linkA: "link_modules as = Inr a"
      and linkM: "link_modules ms = Inr m"
      and sub: "set as \<subseteq> set ms"
      and wfA: "tyenv_well_formed (CM_TyEnv (normalize_module a))"
      and R: "R1 |\<subseteq>| R2"
      and dom: "dt |\<in>| fmdom (TE_Datatypes (CM_TyEnv a))"
      and ng: "dt \<notin> ghost_datatypes_r (CM_TyEnv (normalize_module a)) R1"
  shows "dt \<notin> ghost_datatypes_r (link_mid_env a b m) R2"
proof -
  let ?envA = "CM_TyEnv (normalize_module a)"
  let ?D = "fset (fmdom (TE_Datatypes (CM_TyEnv a)))"
  have pwk: "\<And>ctorName dtName tyVars payload.
               fmlookup (TE_DataCtors ?envA) ctorName = Some (dtName, tyVars, payload) \<Longrightarrow>
               is_well_kinded (?envA \<lparr> TE_TypeVars :=
                                        TE_AbstractTypes ?envA |\<union>| fset_of_list tyVars \<rparr>) payload"
    using wfA unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def by blast
  show ?thesis
  proof (rule ghost_datatypes_r_subst_local[where D = ?D and subst = fmempty,
                                            OF _ _ _ _ _ _ ng])
    fix x assume "x \<in> ?D" "x |\<in>| fmdom (TE_Datatypes (link_mid_env a b m))"
    then show "x |\<in>| fmdom (TE_Datatypes ?envA)" by simp
  next
    fix x assume "x \<in> ?D" "x |\<in>| fmdom (TE_Datatypes (link_mid_env a b m))"
    then show "datatype_ctor_entries (link_mid_env a b m) x
                 = map (\<lambda>(tyvars, payload). (tyvars, apply_subst fmempty payload))
                       (datatype_ctor_entries ?envA x)"
      using link_mid_env_ctor_entries[OF linkA linkM sub wfA, of x b]
      by (simp add: case_prod_beta)
  next
    fix x tyvars payload d
    assume "x \<in> ?D" "x |\<in>| fmdom (TE_Datatypes (link_mid_env a b m))"
       and mem: "(tyvars, payload) \<in> set (datatype_ctor_entries ?envA x)"
       and d_in: "d \<in> type_datatypes payload"
    obtain ctorName dtName where
      lk: "fmlookup (TE_DataCtors ?envA) ctorName = Some (dtName, tyvars, payload)"
      using datatype_ctor_entries_source[OF mem] by blast
    have "type_datatypes payload \<subseteq> fset (fmdom (TE_Datatypes (CM_TyEnv a)))"
      using is_well_kinded_type_datatypes_subset[OF pwk[OF lk]] by simp
    then show "d \<in> ?D" using d_in by blast
  next
    fix x tyvars payload n
    assume "x \<in> ?D" "x |\<in>| fmdom (TE_Datatypes (link_mid_env a b m))"
           "(tyvars, payload) \<in> set (datatype_ctor_entries ?envA x)"
           "n |\<in>| fset_of_list tyvars"
    show "fmlookup fmempty n = None" by simp
  next
    fix x tyvars payload n
    assume "x \<in> ?D" "x |\<in>| fmdom (TE_Datatypes (link_mid_env a b m))"
           "(tyvars, payload) \<in> set (datatype_ctor_entries ?envA x)"
           "n \<in> type_tyvars payload" and n_R: "n |\<in>| R1"
    show "case fmlookup fmempty n of
            Some ty' \<Rightarrow> is_runtime_type_g (ghost_datatypes_r (link_mid_env a b m) R2) R2 ty'
          | None \<Rightarrow> n |\<in>| R2"
      using R n_R by (auto dest: fsubsetD)
  next
    show "dt \<in> ?D" using dom by simp
  qed
qed

(* Likewise for runtime-ness of well-kinded types, into the sub-link's own
   mid env: the sub-link's datatypes keep their ghost status there
   (link_mid_env_ghost_local), and well-kindedness pins the type's datatype
   heads to the sub-link's domain. The ghost sets of the two envs are taken
   in the normal form simp leaves (ghost_datatypes_r with explicit runtime
   abstract types), so the lemma applies to the scope-extended envs of the
   well-formedness clauses as well. *)
lemma link_side_rt_transfer:
  assumes linkA: "link_modules as = Inr a"
      and linkM: "link_modules ms = Inr m"
      and sub: "set as \<subseteq> set ms"
      and wfA: "tyenv_well_formed (CM_TyEnv (normalize_module a))"
      and gd1: "ghost_datatypes env1 = ghost_datatypes_r (CM_TyEnv (normalize_module a)) R1"
      and gd2: "ghost_datatypes env2 = ghost_datatypes_r (link_mid_env a b m) R2"
      and R: "R1 |\<subseteq>| R2"
      and dt1: "TE_Datatypes env1 = TE_Datatypes (CM_TyEnv a)"
      and rtv: "fset (TE_RuntimeTypeVars env1) \<subseteq> fset (TE_RuntimeTypeVars env2)"
      and wk: "is_well_kinded env1 ty"
      and rt: "is_runtime_type env1 ty"
  shows "is_runtime_type env2 ty"
proof (rule is_runtime_type_mono_heads[OF rt _ rtv])
  fix d assume d_in: "d \<in> type_datatypes ty" and d_ng: "d \<notin> ghost_datatypes env1"
  have "d |\<in>| fmdom (TE_Datatypes (CM_TyEnv a))"
    using is_well_kinded_type_datatypes_subset[OF wk] d_in unfolding dt1 by auto
  then show "d \<notin> ghost_datatypes env2"
    unfolding gd2
    by (rule link_mid_env_ghost_local[OF linkA linkM sub wfA R _ d_ng[unfolded gd1]])
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
    unfolding fM(13) fA(13) fB(13) gen
    by (rule funion_list_split[OF setMS])
qed

(* The mid env has distinct binders (all the substitution engine needs of
   it): every signature comes from one side's normalized env. *)
lemma link_mid_env_binders_distinct:
  assumes wtA: "core_module_well_typed a"
      and wtB: "core_module_well_typed b"
  shows "tyenv_binders_distinct (link_mid_env a b m)"
proof -
  let ?envA = "CM_TyEnv (normalize_module a)"
  let ?envB = "CM_TyEnv (normalize_module b)"
  have wfA: "tyenv_well_formed ?envA" and wfB: "tyenv_well_formed ?envB"
    using wtA wtB unfolding core_module_well_typed_def normalized_module_well_typed_def
    by blast+
  have ctdA: "\<And>ctorName dtName tyVars payload.
                fmlookup (TE_DataCtors ?envA) ctorName = Some (dtName, tyVars, payload) \<Longrightarrow>
                distinct tyVars"
    using wfA unfolding tyenv_well_formed_def tyenv_ctor_tyvars_distinct_def by blast
  have ctdB: "\<And>ctorName dtName tyVars payload.
                fmlookup (TE_DataCtors ?envB) ctorName = Some (dtName, tyVars, payload) \<Longrightarrow>
                distinct tyVars"
    using wfB unfolding tyenv_well_formed_def tyenv_ctor_tyvars_distinct_def by blast
  have ftdA: "\<And>funName info. fmlookup (TE_Functions ?envA) funName = Some info \<Longrightarrow>
                distinct (FI_TyArgs info)"
    using wfA unfolding tyenv_well_formed_def tyenv_fun_tyvars_distinct_def by blast
  have ftdB: "\<And>funName info. fmlookup (TE_Functions ?envB) funName = Some info \<Longrightarrow>
                distinct (FI_TyArgs info)"
    using wfB unfolding tyenv_well_formed_def tyenv_fun_tyvars_distinct_def by blast
  have fn_cases: "\<And>name info. fmlookup (TE_Functions (link_mid_env a b m)) name = Some info \<Longrightarrow>
                    fmlookup (TE_Functions ?envA) name = Some info
                    \<or> fmlookup (TE_Functions ?envB) name = Some info"
    unfolding link_mid_env_simps using fmadd_drop_lookup_Some by fastforce
  have dc_cases: "\<And>name entry. fmlookup (TE_DataCtors (link_mid_env a b m)) name = Some entry \<Longrightarrow>
                    fmlookup (TE_DataCtors ?envA) name = Some entry
                    \<or> fmlookup (TE_DataCtors ?envB) name = Some entry"
    unfolding link_mid_env_simps using fmadd_drop_lookup_Some by fastforce
  show ?thesis
    unfolding tyenv_binders_distinct_def tyenv_ctor_tyvars_distinct_def
              tyenv_fun_tyvars_distinct_def
    using fn_cases dc_cases ctdA ctdB ftdA ftdB by blast
qed

(* P2: the normalized result's env is well-formed. Each clause is proved
   entry by entry: an entry of the normalized env is some entry of one
   side's normalized env with the whole link's substitution applied
   (link_mid_env_family_collapse); the side's well-typedness supplies the
   side-local fact; the transfer lemmas carry it into that side's mid env;
   and the substitution engine's lifting lemmas carry it through the
   substitution, where the mid env collapses onto the normalized env
   (link_mid_env_collapse). The b-side runs through link_mid_env b a m. The
   two binder-freshness clauses are the whole link's capture check. *)
lemma link_normalized_env_well_formed:
  assumes linkA: "link_modules as = Inr a"
      and wtA: "core_module_well_typed a"
      and linkB: "link_modules bs = Inr b"
      and wtB: "core_module_well_typed b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
  shows "tyenv_well_formed (CM_TyEnv (normalize_module m))"
proof -
  let ?\<sigma> = "CM_TypeSubst m"
  let ?envM = "CM_TyEnv (normalize_module m)"
  let ?envA = "CM_TyEnv (normalize_module a)"
  let ?envB = "CM_TyEnv (normalize_module b)"
  let ?midA = "link_mid_env a b m"
  let ?midB = "link_mid_env b a m"
  let ?U = "funion_list (map (\<lambda>y. TE_AbstractTypes (CM_TyEnv y)) ms)"
  note fA = link_modules_result_fields[OF linkA]
  note fB = link_modules_result_fields[OF linkB]
  note fM = link_modules_result_fields[OF linkM]
  have setMS': "set ms = set bs \<union> set as" using setMS by auto
  have subA: "set as \<subseteq> set ms" and subB: "set bs \<subseteq> set ms"
    using setMS by auto

  \<comment> \<open>Side well-formedness and the module-level conventions.\<close>
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
  have tv_inter_a: "TE_TypeVars (CM_TyEnv a) |\<inter>| TE_RuntimeTypeVars (CM_TyEnv a)
                      = TE_RuntimeTypeVars (CM_TyEnv a)"
    using rtvA by (simp add: inf_absorb2)
  have tv_inter_b: "TE_TypeVars (CM_TyEnv b) |\<inter>| TE_RuntimeTypeVars (CM_TyEnv b)
                      = TE_RuntimeTypeVars (CM_TyEnv b)"
    using rtvB by (simp add: inf_absorb2)
  have absM: "TE_AbstractTypes (CM_TyEnv m) = TE_TypeVars (CM_TyEnv m)"
    and rtvM: "TE_RuntimeTypeVars (CM_TyEnv m) |\<subseteq>| TE_TypeVars (CM_TyEnv m)"
    using link_pair_abs_tv[OF linkA wtA linkB wtB linkM setMS] by blast+
  have tv_inter_m: "TE_TypeVars (CM_TyEnv m) |\<inter>| TE_RuntimeTypeVars (CM_TyEnv m)
                      = TE_RuntimeTypeVars (CM_TyEnv m)"
    using rtvM by (simp add: inf_absorb2)

  \<comment> \<open>The abstract types of the sides, the mid envs and the result are among
      the inputs' - which the capture check keeps every binder away from.\<close>
  have absU_a: "TE_AbstractTypes (CM_TyEnv a) |\<subseteq>| ?U"
    unfolding fA(7) funion_list_split[OF setMS] by auto
  have absU_b: "TE_AbstractTypes (CM_TyEnv b) |\<subseteq>| ?U"
    unfolding fB(7) funion_list_split[OF setMS] by auto
  have absU_m: "TE_AbstractTypes (CM_TyEnv m) |\<subseteq>| ?U"
    unfolding fM(7) by auto
  have fresh_sub: "\<And>B X. fset_of_list B |\<inter>| ?U = {||} \<Longrightarrow> X |\<subseteq>| ?U
                      \<Longrightarrow> fset_of_list B |\<inter>| X = {||}"
    by auto

  \<comment> \<open>The engine's side conditions and collapse, for both sides.\<close>
  have okA: "module_env_subst_ok ?\<sigma> ?envM ?midA"
    using link_mid_env_subst_ok[OF linkA wtA linkB wtB linkM setMS] .
  have okB: "module_env_subst_ok ?\<sigma> ?envM ?midB"
    using link_mid_env_subst_ok[OF linkB wtB linkA wtA linkM setMS'] .
  have ok_rtA: "module_env_subst_runtime_ok ?\<sigma> ?envM ?midA"
    using link_mid_env_runtime_ok[OF linkA linkB linkM setMS] .
  have ok_rtB: "module_env_subst_runtime_ok ?\<sigma> ?envM ?midB"
    using link_mid_env_runtime_ok[OF linkB linkA linkM setMS'] .
  have collA: "apply_subst_to_module_env ?\<sigma> ?envM ?midA = ?envM"
    using link_mid_env_collapse[OF linkA linkB linkM setMS] .
  have collB: "apply_subst_to_module_env ?\<sigma> ?envM ?midB = ?envM"
    using link_mid_env_collapse[OF linkB linkA linkM setMS'] .
  have cpA: "typesubst_complete (CM_TypeSubst a)"
    and cpB: "typesubst_complete (CM_TypeSubst b)"
    using wtA wtB unfolding core_module_well_typed_def by blast+
  have cp: "\<forall>ty' \<in> fmran' ?\<sigma>. is_complete_type ty'"
    using link_modules_typesubst_complete[OF linkA linkB linkM setMS cpA cpB]
    unfolding typesubst_complete_def .
  have capM: "capture_avoiding m"
    using link_modules_capture_avoiding[OF linkM] .

  \<comment> \<open>Every entry of the normalized env is one side's entry, substituted.\<close>
  have gv_cases: "\<And>name ty. fmlookup (TE_GlobalVars ?envM) name = Some ty \<Longrightarrow>
       (\<exists>ty0. fmlookup (TE_GlobalVars ?envA) name = Some ty0 \<and> ty = apply_subst ?\<sigma> ty0)
       \<or> (\<exists>ty0. fmlookup (TE_GlobalVars ?envB) name = Some ty0 \<and> ty = apply_subst ?\<sigma> ty0)"
  proof -
    fix name ty assume lk: "fmlookup (TE_GlobalVars ?envM) name = Some ty"
    have "TE_GlobalVars ?envM = fmmap (apply_subst ?\<sigma>) (TE_GlobalVars ?midA)"
      using link_mid_env_family_collapse(1)[OF linkA linkB linkM setMS] by simp
    with lk obtain ty0 where mid_lk: "fmlookup (TE_GlobalVars ?midA) name = Some ty0"
                         and ty_eq: "ty = apply_subst ?\<sigma> ty0"
      by (metis fmlookup_map map_option_eq_Some)
    from fmadd_drop_lookup_Some[OF mid_lk[unfolded link_mid_env_simps]] ty_eq
    show "(\<exists>ty0. fmlookup (TE_GlobalVars ?envA) name = Some ty0 \<and> ty = apply_subst ?\<sigma> ty0)
          \<or> (\<exists>ty0. fmlookup (TE_GlobalVars ?envB) name = Some ty0 \<and> ty = apply_subst ?\<sigma> ty0)"
      by blast
  qed
  have fn_cases: "\<And>name info. fmlookup (TE_Functions ?envM) name = Some info \<Longrightarrow>
       (\<exists>info0. fmlookup (TE_Functions ?envA) name = Some info0
                \<and> info = apply_subst_to_funinfo ?\<sigma> info0)
       \<or> (\<exists>info0. fmlookup (TE_Functions ?envB) name = Some info0
                  \<and> info = apply_subst_to_funinfo ?\<sigma> info0)"
  proof -
    fix name info assume lk: "fmlookup (TE_Functions ?envM) name = Some info"
    have "TE_Functions ?envM = fmmap (apply_subst_to_funinfo ?\<sigma>) (TE_Functions ?midA)"
      using link_mid_env_family_collapse(2)[OF linkA linkB linkM setMS] by simp
    with lk obtain info0 where mid_lk: "fmlookup (TE_Functions ?midA) name = Some info0"
                           and i_eq: "info = apply_subst_to_funinfo ?\<sigma> info0"
      by (metis fmlookup_map map_option_eq_Some)
    from fmadd_drop_lookup_Some[OF mid_lk[unfolded link_mid_env_simps]] i_eq
    show "(\<exists>info0. fmlookup (TE_Functions ?envA) name = Some info0
                   \<and> info = apply_subst_to_funinfo ?\<sigma> info0)
          \<or> (\<exists>info0. fmlookup (TE_Functions ?envB) name = Some info0
                     \<and> info = apply_subst_to_funinfo ?\<sigma> info0)"
      by blast
  qed
  have dc_cases: "\<And>c dt tv p. fmlookup (TE_DataCtors ?envM) c = Some (dt, tv, p) \<Longrightarrow>
       (\<exists>p0. fmlookup (TE_DataCtors ?envA) c = Some (dt, tv, p0) \<and> p = apply_subst ?\<sigma> p0)
       \<or> (\<exists>p0. fmlookup (TE_DataCtors ?envB) c = Some (dt, tv, p0) \<and> p = apply_subst ?\<sigma> p0)"
  proof -
    fix c dt tv p assume lk: "fmlookup (TE_DataCtors ?envM) c = Some (dt, tv, p)"
    have eqM: "TE_DataCtors ?envM = fmmap (apply_subst_to_datactor ?\<sigma>) (TE_DataCtors ?midA)"
      using link_mid_env_family_collapse(3)[OF linkA linkB linkM setMS] by simp
    have "map_option (apply_subst_to_datactor ?\<sigma>) (fmlookup (TE_DataCtors ?midA) c)
            = Some (dt, tv, p)"
      using lk unfolding eqM fmlookup_map .
    then obtain e0 where mid_lk0: "fmlookup (TE_DataCtors ?midA) c = Some e0"
                     and e_eq: "(dt, tv, p) = apply_subst_to_datactor ?\<sigma> e0"
      unfolding map_option_eq_Some by fastforce
    obtain dt0 tv0 p0 where e0_eq: "e0 = (dt0, tv0, p0)" by (rule prod_cases3)
    have mid_lk: "fmlookup (TE_DataCtors ?midA) c = Some (dt, tv, p0)"
     and p_eq: "p = apply_subst ?\<sigma> p0"
      using mid_lk0 e_eq unfolding e0_eq apply_subst_to_datactor_simps by simp_all
    from fmadd_drop_lookup_Some[OF mid_lk[unfolded link_mid_env_simps]] p_eq
    show "(\<exists>p0. fmlookup (TE_DataCtors ?envA) c = Some (dt, tv, p0) \<and> p = apply_subst ?\<sigma> p0)
          \<or> (\<exists>p0. fmlookup (TE_DataCtors ?envB) c = Some (dt, tv, p0) \<and> p = apply_subst ?\<sigma> p0)"
      by blast
  qed

  \<comment> \<open>Raw entries underneath a side's normalized ones, and in the whole link.\<close>
  have rawA_fn: "\<And>name info0. fmlookup (TE_Functions ?envA) name = Some info0 \<Longrightarrow>
                  \<exists>info00. fmlookup (TE_Functions (CM_TyEnv a)) name = Some info00
                           \<and> info0 = apply_subst_to_funinfo (CM_TypeSubst a) info00"
  proof -
    fix name info0 assume "fmlookup (TE_Functions ?envA) name = Some info0"
    then show "\<exists>info00. fmlookup (TE_Functions (CM_TyEnv a)) name = Some info00
                        \<and> info0 = apply_subst_to_funinfo (CM_TypeSubst a) info00"
      by (cases "fmlookup (TE_Functions (CM_TyEnv a)) name") auto
  qed
  have rawB_fn: "\<And>name info0. fmlookup (TE_Functions ?envB) name = Some info0 \<Longrightarrow>
                  \<exists>info00. fmlookup (TE_Functions (CM_TyEnv b)) name = Some info00
                           \<and> info0 = apply_subst_to_funinfo (CM_TypeSubst b) info00"
  proof -
    fix name info0 assume "fmlookup (TE_Functions ?envB) name = Some info0"
    then show "\<exists>info00. fmlookup (TE_Functions (CM_TyEnv b)) name = Some info00
                        \<and> info0 = apply_subst_to_funinfo (CM_TypeSubst b) info00"
      by (cases "fmlookup (TE_Functions (CM_TyEnv b)) name") auto
  qed
  have rawA_dc: "\<And>c dt tv p0. fmlookup (TE_DataCtors ?envA) c = Some (dt, tv, p0) \<Longrightarrow>
                  \<exists>p00. fmlookup (TE_DataCtors (CM_TyEnv a)) c = Some (dt, tv, p00)"
  proof -
    fix c dt tv p0 assume "fmlookup (TE_DataCtors ?envA) c = Some (dt, tv, p0)"
    then show "\<exists>p00. fmlookup (TE_DataCtors (CM_TyEnv a)) c = Some (dt, tv, p00)"
      by (cases "fmlookup (TE_DataCtors (CM_TyEnv a)) c")
         (auto simp: apply_subst_to_datactor_def split: prod.splits)
  qed
  have rawB_dc: "\<And>c dt tv p0. fmlookup (TE_DataCtors ?envB) c = Some (dt, tv, p0) \<Longrightarrow>
                  \<exists>p00. fmlookup (TE_DataCtors (CM_TyEnv b)) c = Some (dt, tv, p00)"
  proof -
    fix c dt tv p0 assume "fmlookup (TE_DataCtors ?envB) c = Some (dt, tv, p0)"
    then show "\<exists>p00. fmlookup (TE_DataCtors (CM_TyEnv b)) c = Some (dt, tv, p00)"
      by (cases "fmlookup (TE_DataCtors (CM_TyEnv b)) c")
         (auto simp: apply_subst_to_datactor_def split: prod.splits)
  qed
  \<comment> \<open>Capture-avoidance and freshness of a side's binders.\<close>
  have avoidA_fn: "\<And>name info0. fmlookup (TE_Functions ?envA) name = Some info0 \<Longrightarrow>
                     subst_names ?\<sigma> |\<inter>| fset_of_list (FI_TyArgs info0) = {||}
                     \<and> fset_of_list (FI_TyArgs info0) |\<inter>| ?U = {||}"
  proof -
    fix name info0 assume "fmlookup (TE_Functions ?envA) name = Some info0"
    then obtain info00 where
      raw: "fmlookup (TE_Functions (CM_TyEnv a)) name = Some info00" and
      i_eq: "info0 = apply_subst_to_funinfo (CM_TypeSubst a) info00"
      using rawA_fn by blast
    have m_raw: "fmlookup (TE_Functions (CM_TyEnv m)) name = Some info00"
      using link_modules_decl_submaps(2)[OF linkA linkM subA raw] .
    show "subst_names ?\<sigma> |\<inter>| fset_of_list (FI_TyArgs info0) = {||}
          \<and> fset_of_list (FI_TyArgs info0) |\<inter>| ?U = {||}"
      using capM m_raw link_side_binders_fresh(1)[OF linkA linkM subA raw]
      unfolding capture_avoiding_def by (simp add: i_eq)
  qed
  have avoidB_fn: "\<And>name info0. fmlookup (TE_Functions ?envB) name = Some info0 \<Longrightarrow>
                     subst_names ?\<sigma> |\<inter>| fset_of_list (FI_TyArgs info0) = {||}
                     \<and> fset_of_list (FI_TyArgs info0) |\<inter>| ?U = {||}"
  proof -
    fix name info0 assume "fmlookup (TE_Functions ?envB) name = Some info0"
    then obtain info00 where
      raw: "fmlookup (TE_Functions (CM_TyEnv b)) name = Some info00" and
      i_eq: "info0 = apply_subst_to_funinfo (CM_TypeSubst b) info00"
      using rawB_fn by blast
    have m_raw: "fmlookup (TE_Functions (CM_TyEnv m)) name = Some info00"
      using link_modules_decl_submaps(2)[OF linkB linkM subB raw] .
    show "subst_names ?\<sigma> |\<inter>| fset_of_list (FI_TyArgs info0) = {||}
          \<and> fset_of_list (FI_TyArgs info0) |\<inter>| ?U = {||}"
      using capM m_raw link_side_binders_fresh(1)[OF linkB linkM subB raw]
      unfolding capture_avoiding_def by (simp add: i_eq)
  qed
  have avoidA_dc: "\<And>c dt tv p0. fmlookup (TE_DataCtors ?envA) c = Some (dt, tv, p0) \<Longrightarrow>
                     subst_names ?\<sigma> |\<inter>| fset_of_list tv = {||}
                     \<and> fset_of_list tv |\<inter>| ?U = {||}"
  proof -
    fix c dt tv p0 assume "fmlookup (TE_DataCtors ?envA) c = Some (dt, tv, p0)"
    then obtain p00 where raw: "fmlookup (TE_DataCtors (CM_TyEnv a)) c = Some (dt, tv, p00)"
      using rawA_dc by blast
    have m_raw: "fmlookup (TE_DataCtors (CM_TyEnv m)) c = Some (dt, tv, p00)"
      using link_modules_decl_submaps(4)[OF linkA linkM subA raw] .
    show "subst_names ?\<sigma> |\<inter>| fset_of_list tv = {||} \<and> fset_of_list tv |\<inter>| ?U = {||}"
      using capM m_raw link_side_binders_fresh(2)[OF linkA linkM subA raw]
      unfolding capture_avoiding_def by blast
  qed
  have avoidB_dc: "\<And>c dt tv p0. fmlookup (TE_DataCtors ?envB) c = Some (dt, tv, p0) \<Longrightarrow>
                     subst_names ?\<sigma> |\<inter>| fset_of_list tv = {||}
                     \<and> fset_of_list tv |\<inter>| ?U = {||}"
  proof -
    fix c dt tv p0 assume "fmlookup (TE_DataCtors ?envB) c = Some (dt, tv, p0)"
    then obtain p00 where raw: "fmlookup (TE_DataCtors (CM_TyEnv b)) c = Some (dt, tv, p00)"
      using rawB_dc by blast
    have m_raw: "fmlookup (TE_DataCtors (CM_TyEnv m)) c = Some (dt, tv, p00)"
      using link_modules_decl_submaps(4)[OF linkB linkM subB raw] .
    show "subst_names ?\<sigma> |\<inter>| fset_of_list tv = {||} \<and> fset_of_list tv |\<inter>| ?U = {||}"
      using capM m_raw link_side_binders_fresh(2)[OF linkB linkM subB raw]
      unfolding capture_avoiding_def by blast
  qed

  \<comment> \<open>Side clause extractions (stated at the normalized side envs).\<close>
  have gvwkA: "\<And>name ty. fmlookup (TE_GlobalVars ?envA) name = Some ty \<Longrightarrow>
                 is_well_kinded (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA \<rparr>) ty"
    using wfA unfolding tyenv_well_formed_def tyenv_vars_well_kinded_def by blast
  have gvwkB: "\<And>name ty. fmlookup (TE_GlobalVars ?envB) name = Some ty \<Longrightarrow>
                 is_well_kinded (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB \<rparr>) ty"
    using wfB unfolding tyenv_well_formed_def tyenv_vars_well_kinded_def by blast
  have gvrtA: "\<And>name ty. fmlookup (TE_GlobalVars ?envA) name = Some ty \<Longrightarrow>
                 is_runtime_type (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA,
                                          TE_RuntimeTypeVars :=
                                            TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA \<rparr>) ty"
    using wfA unfolding tyenv_well_formed_def tyenv_vars_runtime_def by blast
  have gvrtB: "\<And>name ty. fmlookup (TE_GlobalVars ?envB) name = Some ty \<Longrightarrow>
                 is_runtime_type (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB,
                                          TE_RuntimeTypeVars :=
                                            TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB \<rparr>) ty"
    using wfB unfolding tyenv_well_formed_def tyenv_vars_runtime_def by blast
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
  have frcA: "\<And>funName info. fmlookup (TE_Functions ?envA) funName = Some info \<Longrightarrow>
                FI_Ghost info = NotGhost \<Longrightarrow> is_complete_type (FI_ReturnType info)"
    using wfA unfolding tyenv_well_formed_def tyenv_fun_return_types_complete_def by blast
  have frcB: "\<And>funName info. fmlookup (TE_Functions ?envB) funName = Some info \<Longrightarrow>
                FI_Ghost info = NotGhost \<Longrightarrow> is_complete_type (FI_ReturnType info)"
    using wfB unfolding tyenv_well_formed_def tyenv_fun_return_types_complete_def by blast
  have fgcA: "\<And>funName info. fmlookup (TE_Functions ?envA) funName = Some info \<Longrightarrow>
                FI_Ghost info = NotGhost \<Longrightarrow>
                (\<forall>ty vor. (ty, vor, NotGhost) \<in> set (FI_TmArgs info) \<longrightarrow>
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
                (\<forall>ty vor. (ty, vor, NotGhost) \<in> set (FI_TmArgs info) \<longrightarrow>
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

  \<comment> \<open>Transfer of a well-kinded type from a side's normalized env to the
      normalized result, through the side's mid env and the substitution:
      plain types, and types in the scope of binders.\<close>
  have wkA_M: "\<And>ty. is_well_kinded ?envA ty \<Longrightarrow> is_well_kinded ?envM (apply_subst ?\<sigma> ty)"
  proof -
    fix ty assume wk: "is_well_kinded ?envA ty"
    have "is_well_kinded ?midA ty"
      by (rule link_side_wk_transfer[OF linkA linkM subA wk]) auto
    then have "is_well_kinded (apply_subst_to_module_env ?\<sigma> ?envM ?midA) (apply_subst ?\<sigma> ty)"
      by (rule apply_subst_preserves_well_kinded_module[OF _ okA])
    then show "is_well_kinded ?envM (apply_subst ?\<sigma> ty)" unfolding collA .
  qed
  have wkB_M: "\<And>ty. is_well_kinded ?envB ty \<Longrightarrow> is_well_kinded ?envM (apply_subst ?\<sigma> ty)"
  proof -
    fix ty assume wk: "is_well_kinded ?envB ty"
    have "is_well_kinded ?midB ty"
      by (rule link_side_wk_transfer[OF linkB linkM subB wk]) auto
    then have "is_well_kinded (apply_subst_to_module_env ?\<sigma> ?envM ?midB) (apply_subst ?\<sigma> ty)"
      by (rule apply_subst_preserves_well_kinded_module[OF _ okB])
    then show "is_well_kinded ?envM (apply_subst ?\<sigma> ty)" unfolding collB .
  qed
  have wkA_M_b: "\<And>ty B. is_well_kinded (?envA \<lparr> TE_TypeVars :=
                                                TE_AbstractTypes ?envA |\<union>| fset_of_list B \<rparr>) ty
                  \<Longrightarrow> subst_names ?\<sigma> |\<inter>| fset_of_list B = {||}
                  \<Longrightarrow> is_well_kinded (?envM \<lparr> TE_TypeVars :=
                                                TE_AbstractTypes ?envM |\<union>| fset_of_list B \<rparr>)
                                     (apply_subst ?\<sigma> ty)"
  proof -
    fix ty B
    assume wk: "is_well_kinded (?envA \<lparr> TE_TypeVars :=
                                         TE_AbstractTypes ?envA |\<union>| fset_of_list B \<rparr>) ty"
       and avoid: "subst_names ?\<sigma> |\<inter>| fset_of_list B = {||}"
    have wk_mid: "is_well_kinded (?midA \<lparr> TE_TypeVars := TE_TypeVars ?midA |\<union>| fset_of_list B \<rparr>) ty"
      by (rule link_side_wk_transfer[OF linkA linkM subA wk]) (auto simp: absa)
    have "is_well_kinded (?envM \<lparr> TE_TypeVars := TE_TypeVars ?envM |\<union>| fset_of_list B \<rparr>)
            (apply_subst ?\<sigma> ty)"
      by (rule apply_subst_preserves_well_kinded_module_binders[OF wk_mid okA avoid])
    moreover have "is_well_kinded (?envM \<lparr> TE_TypeVars := TE_TypeVars ?envM |\<union>| fset_of_list B \<rparr>)
                     (apply_subst ?\<sigma> ty)
                   = is_well_kinded (?envM \<lparr> TE_TypeVars :=
                                               TE_AbstractTypes ?envM |\<union>| fset_of_list B \<rparr>)
                       (apply_subst ?\<sigma> ty)"
      by (intro is_well_kinded_cong_env) (simp_all add: absM)
    ultimately show "is_well_kinded (?envM \<lparr> TE_TypeVars :=
                                                TE_AbstractTypes ?envM |\<union>| fset_of_list B \<rparr>)
                       (apply_subst ?\<sigma> ty)"
      by simp
  qed
  have wkB_M_b: "\<And>ty B. is_well_kinded (?envB \<lparr> TE_TypeVars :=
                                                TE_AbstractTypes ?envB |\<union>| fset_of_list B \<rparr>) ty
                  \<Longrightarrow> subst_names ?\<sigma> |\<inter>| fset_of_list B = {||}
                  \<Longrightarrow> is_well_kinded (?envM \<lparr> TE_TypeVars :=
                                                TE_AbstractTypes ?envM |\<union>| fset_of_list B \<rparr>)
                                     (apply_subst ?\<sigma> ty)"
  proof -
    fix ty B
    assume wk: "is_well_kinded (?envB \<lparr> TE_TypeVars :=
                                         TE_AbstractTypes ?envB |\<union>| fset_of_list B \<rparr>) ty"
       and avoid: "subst_names ?\<sigma> |\<inter>| fset_of_list B = {||}"
    have wk_mid: "is_well_kinded (?midB \<lparr> TE_TypeVars := TE_TypeVars ?midB |\<union>| fset_of_list B \<rparr>) ty"
      by (rule link_side_wk_transfer[OF linkB linkM subB wk]) (auto simp: absb)
    have "is_well_kinded (?envM \<lparr> TE_TypeVars := TE_TypeVars ?envM |\<union>| fset_of_list B \<rparr>)
            (apply_subst ?\<sigma> ty)"
      by (rule apply_subst_preserves_well_kinded_module_binders[OF wk_mid okB avoid])
    moreover have "is_well_kinded (?envM \<lparr> TE_TypeVars := TE_TypeVars ?envM |\<union>| fset_of_list B \<rparr>)
                     (apply_subst ?\<sigma> ty)
                   = is_well_kinded (?envM \<lparr> TE_TypeVars :=
                                               TE_AbstractTypes ?envM |\<union>| fset_of_list B \<rparr>)
                       (apply_subst ?\<sigma> ty)"
      by (intro is_well_kinded_cong_env) (simp_all add: absM)
    ultimately show "is_well_kinded (?envM \<lparr> TE_TypeVars :=
                                                TE_AbstractTypes ?envM |\<union>| fset_of_list B \<rparr>)
                       (apply_subst ?\<sigma> ty)"
      by simp
  qed

  \<comment> \<open>The same for runtime-ness.\<close>
  have rtA_M: "\<And>ty. is_well_kinded ?envA ty \<Longrightarrow> is_runtime_type ?envA ty
                  \<Longrightarrow> is_runtime_type ?envM (apply_subst ?\<sigma> ty)"
  proof -
    fix ty assume wk: "is_well_kinded ?envA ty" and rt: "is_runtime_type ?envA ty"
    have "is_runtime_type ?midA ty"
    proof (rule link_side_rt_transfer[OF linkA linkM subA wfA _ _ _ _ _ wk rt])
      show "ghost_datatypes ?envA
              = ghost_datatypes_r ?envA (TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA)" ..
      show "ghost_datatypes ?midA
              = ghost_datatypes_r ?midA (TE_AbstractTypes ?midA |\<inter>| TE_RuntimeTypeVars ?midA)" ..
      show "TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA
              |\<subseteq>| TE_AbstractTypes ?midA |\<inter>| TE_RuntimeTypeVars ?midA" by auto
      show "TE_Datatypes ?envA = TE_Datatypes (CM_TyEnv a)" by simp
      show "fset (TE_RuntimeTypeVars ?envA) \<subseteq> fset (TE_RuntimeTypeVars ?midA)" by auto
    qed
    then have "is_runtime_type (apply_subst_to_module_env ?\<sigma> ?envM ?midA) (apply_subst ?\<sigma> ty)"
      by (rule apply_subst_preserves_runtime_module[OF _ okA ok_rtA])
    then show "is_runtime_type ?envM (apply_subst ?\<sigma> ty)" unfolding collA .
  qed
  have rtB_M: "\<And>ty. is_well_kinded ?envB ty \<Longrightarrow> is_runtime_type ?envB ty
                  \<Longrightarrow> is_runtime_type ?envM (apply_subst ?\<sigma> ty)"
  proof -
    fix ty assume wk: "is_well_kinded ?envB ty" and rt: "is_runtime_type ?envB ty"
    have "is_runtime_type ?midB ty"
    proof (rule link_side_rt_transfer[OF linkB linkM subB wfB _ _ _ _ _ wk rt])
      show "ghost_datatypes ?envB
              = ghost_datatypes_r ?envB (TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB)" ..
      show "ghost_datatypes ?midB
              = ghost_datatypes_r ?midB (TE_AbstractTypes ?midB |\<inter>| TE_RuntimeTypeVars ?midB)" ..
      show "TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB
              |\<subseteq>| TE_AbstractTypes ?midB |\<inter>| TE_RuntimeTypeVars ?midB" by auto
      show "TE_Datatypes ?envB = TE_Datatypes (CM_TyEnv b)" by simp
      show "fset (TE_RuntimeTypeVars ?envB) \<subseteq> fset (TE_RuntimeTypeVars ?midB)" by auto
    qed
    then have "is_runtime_type (apply_subst_to_module_env ?\<sigma> ?envM ?midB) (apply_subst ?\<sigma> ty)"
      by (rule apply_subst_preserves_runtime_module[OF _ okB ok_rtB])
    then show "is_runtime_type ?envM (apply_subst ?\<sigma> ty)" unfolding collB .
  qed
  \<comment> \<open>In the scope of binders B that shadow no abstract type (so that they
      leave the ghost sets unchanged).\<close>
  have rtA_M_b: "\<And>ty B. fset_of_list B |\<inter>| ?U = {||}
                  \<Longrightarrow> subst_names ?\<sigma> |\<inter>| fset_of_list B = {||}
                  \<Longrightarrow> is_well_kinded (?envA \<lparr> TE_TypeVars :=
                                                TE_AbstractTypes ?envA |\<union>| fset_of_list B \<rparr>) ty
                  \<Longrightarrow> is_runtime_type (?envA \<lparr> TE_TypeVars :=
                                                 TE_AbstractTypes ?envA |\<union>| fset_of_list B,
                                               TE_RuntimeTypeVars :=
                                                 (TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA)
                                                 |\<union>| fset_of_list B \<rparr>) ty
                  \<Longrightarrow> is_runtime_type (?envM \<lparr> TE_TypeVars :=
                                                 TE_AbstractTypes ?envM |\<union>| fset_of_list B,
                                               TE_RuntimeTypeVars :=
                                                 (TE_AbstractTypes ?envM |\<inter>| TE_RuntimeTypeVars ?envM)
                                                 |\<union>| fset_of_list B \<rparr>) (apply_subst ?\<sigma> ty)"
  proof -
    fix ty B
    assume freshU: "fset_of_list B |\<inter>| ?U = {||}"
       and avoid: "subst_names ?\<sigma> |\<inter>| fset_of_list B = {||}"
       and wk: "is_well_kinded (?envA \<lparr> TE_TypeVars :=
                                         TE_AbstractTypes ?envA |\<union>| fset_of_list B \<rparr>) ty"
       and rt: "is_runtime_type (?envA \<lparr> TE_TypeVars :=
                                          TE_AbstractTypes ?envA |\<union>| fset_of_list B,
                                        TE_RuntimeTypeVars :=
                                          (TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA)
                                          |\<union>| fset_of_list B \<rparr>) ty"
    let ?e1 = "?envA \<lparr> TE_TypeVars := TE_TypeVars ?envA |\<union>| fset_of_list B,
                       TE_RuntimeTypeVars := TE_RuntimeTypeVars ?envA |\<union>| fset_of_list B \<rparr>"
    let ?e2 = "?midA \<lparr> TE_TypeVars := TE_TypeVars ?midA |\<union>| fset_of_list B,
                       TE_RuntimeTypeVars := TE_RuntimeTypeVars ?midA |\<union>| fset_of_list B \<rparr>"
    let ?e3 = "?envM \<lparr> TE_TypeVars := TE_TypeVars ?envM |\<union>| fset_of_list B,
                       TE_RuntimeTypeVars := TE_RuntimeTypeVars ?envM |\<union>| fset_of_list B \<rparr>"
    have freshA: "fset_of_list B |\<inter>| TE_AbstractTypes (CM_TyEnv a) = {||}"
      using fresh_sub[OF freshU absU_a] .
    have freshB: "fset_of_list B |\<inter>| TE_AbstractTypes (CM_TyEnv b) = {||}"
      using fresh_sub[OF freshU absU_b] .
    have freshMid0: "fset_of_list B
                       |\<inter>| (TE_AbstractTypes (CM_TyEnv a) |\<union>| TE_AbstractTypes (CM_TyEnv b)) = {||}"
      using freshA freshB by auto
    have freshMid: "fset_of_list B |\<inter>| TE_AbstractTypes ?midA = {||}"
      by (simp add: freshMid0)
    \<comment> \<open>The binders leave the runtime abstract types, hence the ghost sets, alone.\<close>
    have eqA: "TE_AbstractTypes (CM_TyEnv a)
                 |\<inter>| (TE_RuntimeTypeVars (CM_TyEnv a) |\<union>| fset_of_list B)
               = TE_AbstractTypes (CM_TyEnv a) |\<inter>| TE_RuntimeTypeVars (CM_TyEnv a)"
      by (rule fset_eqI) (metis freshA fempty_iff finter_iff funion_iff)
    have eqMid: "(TE_AbstractTypes (CM_TyEnv a) |\<union>| TE_AbstractTypes (CM_TyEnv b))
                   |\<inter>| ((TE_RuntimeTypeVars (CM_TyEnv a) |\<union>| TE_RuntimeTypeVars (CM_TyEnv b))
                        |\<union>| fset_of_list B)
                 = (TE_AbstractTypes (CM_TyEnv a) |\<union>| TE_AbstractTypes (CM_TyEnv b))
                   |\<inter>| (TE_RuntimeTypeVars (CM_TyEnv a) |\<union>| TE_RuntimeTypeVars (CM_TyEnv b))"
      by (rule fset_eqI) (metis freshMid0 fempty_iff finter_iff funion_iff)
    \<comment> \<open>From the Abs-form to the TV-form of the side env, then into the mid env,
        through the substitution, and back to the Abs-form at the result.\<close>
    have wk1: "is_well_kinded ?e1 ty"
    proof -
      have "is_well_kinded (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA |\<union>| fset_of_list B \<rparr>) ty
              = is_well_kinded ?e1 ty"
        by (intro is_well_kinded_cong_env) (simp_all add: absa)
      then show ?thesis using wk by simp
    qed
    have rt1: "is_runtime_type ?e1 ty"
    proof -
      have "is_runtime_type (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA |\<union>| fset_of_list B,
                                     TE_RuntimeTypeVars :=
                                       (TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA)
                                       |\<union>| fset_of_list B \<rparr>) ty
              = is_runtime_type ?e1 ty"
        by (intro is_runtime_type_cong_env) (simp_all add: absa tv_inter_a)
      then show ?thesis using rt by simp
    qed
    have rt2: "is_runtime_type ?e2 ty"
    proof (rule link_side_rt_transfer[OF linkA linkM subA wfA _ _ _ _ _ wk1 rt1])
      show "ghost_datatypes ?e1
              = ghost_datatypes_r ?envA (TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA)"
        by (simp add: eqA)
      show "ghost_datatypes ?e2
              = ghost_datatypes_r ?midA (TE_AbstractTypes ?midA |\<inter>| TE_RuntimeTypeVars ?midA)"
        by (simp add: eqMid)
      show "TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA
              |\<subseteq>| TE_AbstractTypes ?midA |\<inter>| TE_RuntimeTypeVars ?midA" by auto
      show "TE_Datatypes ?e1 = TE_Datatypes (CM_TyEnv a)" by simp
      show "fset (TE_RuntimeTypeVars ?e1) \<subseteq> fset (TE_RuntimeTypeVars ?e2)" by auto
    qed
    have rt3: "is_runtime_type ?e3 (apply_subst ?\<sigma> ty)"
      by (rule apply_subst_preserves_runtime_module_binders[OF rt2 okA ok_rtA avoid freshMid])
    have "is_runtime_type ?e3 (apply_subst ?\<sigma> ty)
            = is_runtime_type (?envM \<lparr> TE_TypeVars := TE_AbstractTypes ?envM |\<union>| fset_of_list B,
                                       TE_RuntimeTypeVars :=
                                         (TE_AbstractTypes ?envM |\<inter>| TE_RuntimeTypeVars ?envM)
                                         |\<union>| fset_of_list B \<rparr>) (apply_subst ?\<sigma> ty)"
      by (intro is_runtime_type_cong_env) (simp_all add: absM tv_inter_m)
    then show "is_runtime_type (?envM \<lparr> TE_TypeVars := TE_AbstractTypes ?envM |\<union>| fset_of_list B,
                                        TE_RuntimeTypeVars :=
                                          (TE_AbstractTypes ?envM |\<inter>| TE_RuntimeTypeVars ?envM)
                                          |\<union>| fset_of_list B \<rparr>) (apply_subst ?\<sigma> ty)"
      using rt3 by simp
  qed
  have rtB_M_b: "\<And>ty B. fset_of_list B |\<inter>| ?U = {||}
                  \<Longrightarrow> subst_names ?\<sigma> |\<inter>| fset_of_list B = {||}
                  \<Longrightarrow> is_well_kinded (?envB \<lparr> TE_TypeVars :=
                                                TE_AbstractTypes ?envB |\<union>| fset_of_list B \<rparr>) ty
                  \<Longrightarrow> is_runtime_type (?envB \<lparr> TE_TypeVars :=
                                                 TE_AbstractTypes ?envB |\<union>| fset_of_list B,
                                               TE_RuntimeTypeVars :=
                                                 (TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB)
                                                 |\<union>| fset_of_list B \<rparr>) ty
                  \<Longrightarrow> is_runtime_type (?envM \<lparr> TE_TypeVars :=
                                                 TE_AbstractTypes ?envM |\<union>| fset_of_list B,
                                               TE_RuntimeTypeVars :=
                                                 (TE_AbstractTypes ?envM |\<inter>| TE_RuntimeTypeVars ?envM)
                                                 |\<union>| fset_of_list B \<rparr>) (apply_subst ?\<sigma> ty)"
  proof -
    fix ty B
    assume freshU: "fset_of_list B |\<inter>| ?U = {||}"
       and avoid: "subst_names ?\<sigma> |\<inter>| fset_of_list B = {||}"
       and wk: "is_well_kinded (?envB \<lparr> TE_TypeVars :=
                                         TE_AbstractTypes ?envB |\<union>| fset_of_list B \<rparr>) ty"
       and rt: "is_runtime_type (?envB \<lparr> TE_TypeVars :=
                                          TE_AbstractTypes ?envB |\<union>| fset_of_list B,
                                        TE_RuntimeTypeVars :=
                                          (TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB)
                                          |\<union>| fset_of_list B \<rparr>) ty"
    let ?e1 = "?envB \<lparr> TE_TypeVars := TE_TypeVars ?envB |\<union>| fset_of_list B,
                       TE_RuntimeTypeVars := TE_RuntimeTypeVars ?envB |\<union>| fset_of_list B \<rparr>"
    let ?e2 = "?midB \<lparr> TE_TypeVars := TE_TypeVars ?midB |\<union>| fset_of_list B,
                       TE_RuntimeTypeVars := TE_RuntimeTypeVars ?midB |\<union>| fset_of_list B \<rparr>"
    let ?e3 = "?envM \<lparr> TE_TypeVars := TE_TypeVars ?envM |\<union>| fset_of_list B,
                       TE_RuntimeTypeVars := TE_RuntimeTypeVars ?envM |\<union>| fset_of_list B \<rparr>"
    have freshA: "fset_of_list B |\<inter>| TE_AbstractTypes (CM_TyEnv a) = {||}"
      using fresh_sub[OF freshU absU_a] .
    have freshB: "fset_of_list B |\<inter>| TE_AbstractTypes (CM_TyEnv b) = {||}"
      using fresh_sub[OF freshU absU_b] .
    have freshMid0: "fset_of_list B
                       |\<inter>| (TE_AbstractTypes (CM_TyEnv b) |\<union>| TE_AbstractTypes (CM_TyEnv a)) = {||}"
      using freshA freshB by auto
    have freshMid: "fset_of_list B |\<inter>| TE_AbstractTypes ?midB = {||}"
      by (simp add: freshMid0)
    have eqB: "TE_AbstractTypes (CM_TyEnv b)
                 |\<inter>| (TE_RuntimeTypeVars (CM_TyEnv b) |\<union>| fset_of_list B)
               = TE_AbstractTypes (CM_TyEnv b) |\<inter>| TE_RuntimeTypeVars (CM_TyEnv b)"
      by (rule fset_eqI) (metis freshB fempty_iff finter_iff funion_iff)
    have eqMid: "(TE_AbstractTypes (CM_TyEnv b) |\<union>| TE_AbstractTypes (CM_TyEnv a))
                   |\<inter>| ((TE_RuntimeTypeVars (CM_TyEnv b) |\<union>| TE_RuntimeTypeVars (CM_TyEnv a))
                        |\<union>| fset_of_list B)
                 = (TE_AbstractTypes (CM_TyEnv b) |\<union>| TE_AbstractTypes (CM_TyEnv a))
                   |\<inter>| (TE_RuntimeTypeVars (CM_TyEnv b) |\<union>| TE_RuntimeTypeVars (CM_TyEnv a))"
      by (rule fset_eqI) (metis freshMid0 fempty_iff finter_iff funion_iff)
    have wk1: "is_well_kinded ?e1 ty"
    proof -
      have "is_well_kinded (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB |\<union>| fset_of_list B \<rparr>) ty
              = is_well_kinded ?e1 ty"
        by (intro is_well_kinded_cong_env) (simp_all add: absb)
      then show ?thesis using wk by simp
    qed
    have rt1: "is_runtime_type ?e1 ty"
    proof -
      have "is_runtime_type (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB |\<union>| fset_of_list B,
                                     TE_RuntimeTypeVars :=
                                       (TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB)
                                       |\<union>| fset_of_list B \<rparr>) ty
              = is_runtime_type ?e1 ty"
        by (intro is_runtime_type_cong_env) (simp_all add: absb tv_inter_b)
      then show ?thesis using rt by simp
    qed
    have rt2: "is_runtime_type ?e2 ty"
    proof (rule link_side_rt_transfer[OF linkB linkM subB wfB _ _ _ _ _ wk1 rt1])
      show "ghost_datatypes ?e1
              = ghost_datatypes_r ?envB (TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB)"
        by (simp add: eqB)
      show "ghost_datatypes ?e2
              = ghost_datatypes_r ?midB (TE_AbstractTypes ?midB |\<inter>| TE_RuntimeTypeVars ?midB)"
        by (simp add: eqMid)
      show "TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB
              |\<subseteq>| TE_AbstractTypes ?midB |\<inter>| TE_RuntimeTypeVars ?midB" by auto
      show "TE_Datatypes ?e1 = TE_Datatypes (CM_TyEnv b)" by simp
      show "fset (TE_RuntimeTypeVars ?e1) \<subseteq> fset (TE_RuntimeTypeVars ?e2)" by auto
    qed
    have rt3: "is_runtime_type ?e3 (apply_subst ?\<sigma> ty)"
      by (rule apply_subst_preserves_runtime_module_binders[OF rt2 okB ok_rtB avoid freshMid])
    have "is_runtime_type ?e3 (apply_subst ?\<sigma> ty)
            = is_runtime_type (?envM \<lparr> TE_TypeVars := TE_AbstractTypes ?envM |\<union>| fset_of_list B,
                                       TE_RuntimeTypeVars :=
                                         (TE_AbstractTypes ?envM |\<inter>| TE_RuntimeTypeVars ?envM)
                                         |\<union>| fset_of_list B \<rparr>) (apply_subst ?\<sigma> ty)"
      by (intro is_runtime_type_cong_env) (simp_all add: absM tv_inter_m)
    then show "is_runtime_type (?envM \<lparr> TE_TypeVars := TE_AbstractTypes ?envM |\<union>| fset_of_list B,
                                        TE_RuntimeTypeVars :=
                                          (TE_AbstractTypes ?envM |\<inter>| TE_RuntimeTypeVars ?envM)
                                          |\<union>| fset_of_list B \<rparr>) (apply_subst ?\<sigma> ty)"
      using rt3 by simp
  qed

  \<comment> \<open>Per-family whole-link disjointness.\<close>
  have btdisjA: "fmdisjoint_list (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) as)"
    using link_modules_success_facts(1)[OF linkA]
    unfolding link_fields_disjoint_def by blast
  have btdisjB: "fmdisjoint_list (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) bs)"
    using link_modules_success_facts(1)[OF linkB]
    unfolding link_fields_disjoint_def by blast
  have btdisjM: "fmdisjoint_list (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) ms)"
    using link_modules_success_facts(1)[OF linkM]
    unfolding link_fields_disjoint_def by blast
  have dtdom: "fmdom (TE_Datatypes (CM_TyEnv m))
                 = fmdom (TE_Datatypes (CM_TyEnv a)) |\<union>| fmdom (TE_Datatypes (CM_TyEnv b))"
    using link_pair_datatypes_dom_split[OF linkA linkB linkM setMS] .

  show ?thesis
    unfolding tyenv_well_formed_def
  proof (intro conjI)
    show "tyenv_vars_well_kinded ?envM"
      unfolding tyenv_vars_well_kinded_def
    proof (intro conjI allI impI)
      fix name ty assume "fmlookup (TE_LocalVars ?envM) name = Some ty"
      then show "is_well_kinded ?envM ty" by (simp add: fM(1))
    next
      fix name ty assume lk: "fmlookup (TE_GlobalVars ?envM) name = Some ty"
      have "is_well_kinded ?envM ty"
        using gv_cases[OF lk]
      proof
        assume "\<exists>ty0. fmlookup (TE_GlobalVars ?envA) name = Some ty0 \<and> ty = apply_subst ?\<sigma> ty0"
        then obtain ty0 where lkA: "fmlookup (TE_GlobalVars ?envA) name = Some ty0"
                          and ty_eq: "ty = apply_subst ?\<sigma> ty0" by blast
        have "is_well_kinded (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA \<rparr>) ty0
                = is_well_kinded ?envA ty0"
          by (intro is_well_kinded_cong_env) (simp_all add: absa)
        with gvwkA[OF lkA] have "is_well_kinded ?envA ty0" by simp
        then show ?thesis unfolding ty_eq by (rule wkA_M)
      next
        assume "\<exists>ty0. fmlookup (TE_GlobalVars ?envB) name = Some ty0 \<and> ty = apply_subst ?\<sigma> ty0"
        then obtain ty0 where lkB: "fmlookup (TE_GlobalVars ?envB) name = Some ty0"
                          and ty_eq: "ty = apply_subst ?\<sigma> ty0" by blast
        have "is_well_kinded (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB \<rparr>) ty0
                = is_well_kinded ?envB ty0"
          by (intro is_well_kinded_cong_env) (simp_all add: absb)
        with gvwkB[OF lkB] have "is_well_kinded ?envB ty0" by simp
        then show ?thesis unfolding ty_eq by (rule wkB_M)
      qed
      moreover have "is_well_kinded (?envM \<lparr> TE_TypeVars := TE_AbstractTypes ?envM \<rparr>) ty
                       = is_well_kinded ?envM ty"
        by (intro is_well_kinded_cong_env) (simp_all add: absM)
      ultimately show "is_well_kinded (?envM \<lparr> TE_TypeVars := TE_AbstractTypes ?envM \<rparr>) ty"
        by simp
    qed
  next
    show "tyenv_vars_runtime ?envM"
      unfolding tyenv_vars_runtime_def
    proof (intro conjI allI impI)
      fix name ty
      assume "fmlookup (TE_LocalVars ?envM) name = Some ty \<and> name |\<notin>| TE_GhostLocals ?envM"
      then show "is_runtime_type ?envM ty" by (simp add: fM(1))
    next
      fix name ty
      assume lk: "fmlookup (TE_GlobalVars ?envM) name = Some ty"
      have "is_runtime_type ?envM ty"
        using gv_cases[OF lk]
      proof
        assume "\<exists>ty0. fmlookup (TE_GlobalVars ?envA) name = Some ty0 \<and> ty = apply_subst ?\<sigma> ty0"
        then obtain ty0 where lkA: "fmlookup (TE_GlobalVars ?envA) name = Some ty0"
                          and ty_eq: "ty = apply_subst ?\<sigma> ty0" by blast
        have "is_well_kinded (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA \<rparr>) ty0
                = is_well_kinded ?envA ty0"
          by (intro is_well_kinded_cong_env) (simp_all add: absa)
        with gvwkA[OF lkA] have wk0: "is_well_kinded ?envA ty0" by simp
        have "is_runtime_type (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA,
                                       TE_RuntimeTypeVars :=
                                         TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA \<rparr>) ty0
                = is_runtime_type ?envA ty0"
          by (intro is_runtime_type_cong_env) (simp_all add: absa tv_inter_a)
        with gvrtA[OF lkA] have "is_runtime_type ?envA ty0" by simp
        then show ?thesis unfolding ty_eq by (rule rtA_M[OF wk0])
      next
        assume "\<exists>ty0. fmlookup (TE_GlobalVars ?envB) name = Some ty0 \<and> ty = apply_subst ?\<sigma> ty0"
        then obtain ty0 where lkB: "fmlookup (TE_GlobalVars ?envB) name = Some ty0"
                          and ty_eq: "ty = apply_subst ?\<sigma> ty0" by blast
        have "is_well_kinded (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB \<rparr>) ty0
                = is_well_kinded ?envB ty0"
          by (intro is_well_kinded_cong_env) (simp_all add: absb)
        with gvwkB[OF lkB] have wk0: "is_well_kinded ?envB ty0" by simp
        have "is_runtime_type (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB,
                                       TE_RuntimeTypeVars :=
                                         TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB \<rparr>) ty0
                = is_runtime_type ?envB ty0"
          by (intro is_runtime_type_cong_env) (simp_all add: absb tv_inter_b)
        with gvrtB[OF lkB] have "is_runtime_type ?envB ty0" by simp
        then show ?thesis unfolding ty_eq by (rule rtB_M[OF wk0])
      qed
      moreover have "is_runtime_type (?envM \<lparr> TE_TypeVars := TE_AbstractTypes ?envM,
                                              TE_RuntimeTypeVars :=
                                                TE_AbstractTypes ?envM |\<inter>| TE_RuntimeTypeVars ?envM \<rparr>) ty
                       = is_runtime_type ?envM ty"
        by (intro is_runtime_type_cong_env) (simp_all add: absM tv_inter_m)
      ultimately show "is_runtime_type (?envM \<lparr> TE_TypeVars := TE_AbstractTypes ?envM,
                                                TE_RuntimeTypeVars :=
                                                  TE_AbstractTypes ?envM
                                                  |\<inter>| TE_RuntimeTypeVars ?envM \<rparr>) ty"
        by simp
    qed
  next
    show "tyenv_ghost_vars_subset ?envM"
      unfolding tyenv_ghost_vars_subset_def by (simp add: fM(3))
  next
    show "tyenv_return_type_well_kinded ?envM"
      unfolding tyenv_return_type_well_kinded_def by (simp add: fM(8))
  next
    show "tyenv_return_type_runtime ?envM"
      unfolding tyenv_return_type_runtime_def by (simp add: fM(8))
  next
    show "tyenv_return_type_complete ?envM"
      unfolding tyenv_return_type_complete_def by (simp add: fM(8))
  next
    show "tyenv_ctors_consistent ?envM"
      unfolding tyenv_ctors_consistent_def
    proof (intro allI impI)
      fix ctorName dtName tyVars payload
      assume lk: "fmlookup (TE_DataCtors ?envM) ctorName = Some (dtName, tyVars, payload)"
      from dc_cases[OF lk]
      show "fmlookup (TE_Datatypes ?envM) dtName = Some (length tyVars)"
      proof
        assume "\<exists>p0. fmlookup (TE_DataCtors ?envA) ctorName = Some (dtName, tyVars, p0)
                     \<and> payload = apply_subst ?\<sigma> p0"
        then obtain p0 where lkA: "fmlookup (TE_DataCtors ?envA) ctorName = Some (dtName, tyVars, p0)"
          by blast
        have "fmlookup (TE_Datatypes (CM_TyEnv a)) dtName = Some (length tyVars)"
          using ccA[OF lkA] by simp
        then have "fmlookup (TE_Datatypes (CM_TyEnv m)) dtName = Some (length tyVars)"
          using link_modules_decl_submaps(3)[OF linkA linkM subA] by blast
        then show ?thesis by simp
      next
        assume "\<exists>p0. fmlookup (TE_DataCtors ?envB) ctorName = Some (dtName, tyVars, p0)
                     \<and> payload = apply_subst ?\<sigma> p0"
        then obtain p0 where lkB: "fmlookup (TE_DataCtors ?envB) ctorName = Some (dtName, tyVars, p0)"
          by blast
        have "fmlookup (TE_Datatypes (CM_TyEnv b)) dtName = Some (length tyVars)"
          using ccB[OF lkB] by simp
        then have "fmlookup (TE_Datatypes (CM_TyEnv m)) dtName = Some (length tyVars)"
          using link_modules_decl_submaps(3)[OF linkB linkM subB] by blast
        then show ?thesis by simp
      qed
    qed
  next
    show "tyenv_payloads_well_kinded ?envM"
      unfolding tyenv_payloads_well_kinded_def
    proof (intro allI impI)
      fix ctorName dtName tyVars payload
      assume lk: "fmlookup (TE_DataCtors ?envM) ctorName = Some (dtName, tyVars, payload)"
      from dc_cases[OF lk]
      show "is_well_kinded (?envM \<lparr> TE_TypeVars :=
                                    TE_AbstractTypes ?envM |\<union>| fset_of_list tyVars \<rparr>) payload"
      proof
        assume "\<exists>p0. fmlookup (TE_DataCtors ?envA) ctorName = Some (dtName, tyVars, p0)
                     \<and> payload = apply_subst ?\<sigma> p0"
        then obtain p0 where lkA: "fmlookup (TE_DataCtors ?envA) ctorName = Some (dtName, tyVars, p0)"
                         and p_eq: "payload = apply_subst ?\<sigma> p0" by blast
        show ?thesis
          unfolding p_eq
          by (rule wkA_M_b[OF pwkA[OF lkA] avoidA_dc[OF lkA, THEN conjunct1]])
      next
        assume "\<exists>p0. fmlookup (TE_DataCtors ?envB) ctorName = Some (dtName, tyVars, p0)
                     \<and> payload = apply_subst ?\<sigma> p0"
        then obtain p0 where lkB: "fmlookup (TE_DataCtors ?envB) ctorName = Some (dtName, tyVars, p0)"
                         and p_eq: "payload = apply_subst ?\<sigma> p0" by blast
        show ?thesis
          unfolding p_eq
          by (rule wkB_M_b[OF pwkB[OF lkB] avoidB_dc[OF lkB, THEN conjunct1]])
      qed
    qed
  next
    show "tyenv_ctor_tyvars_distinct ?envM"
      unfolding tyenv_ctor_tyvars_distinct_def
    proof (intro allI impI)
      fix ctorName dtName tyVars payload
      assume lk: "fmlookup (TE_DataCtors ?envM) ctorName = Some (dtName, tyVars, payload)"
      show "distinct tyVars"
        using dc_cases[OF lk] ctdA ctdB by blast
    qed
  next
    show "tyenv_ctor_tyvars_fresh ?envM"
      unfolding tyenv_ctor_tyvars_fresh_def
    proof (intro allI impI)
      fix ctorName dtName tyVars payload
      assume lk: "fmlookup (TE_DataCtors ?envM) ctorName = Some (dtName, tyVars, payload)"
      have "fset_of_list tyVars |\<inter>| ?U = {||}"
        using dc_cases[OF lk] avoidA_dc avoidB_dc by blast
      then have "fset_of_list tyVars |\<inter>| TE_AbstractTypes (CM_TyEnv m) = {||}"
        using fresh_sub[OF _ absU_m] by blast
      then show "fset_of_list tyVars |\<inter>| TE_AbstractTypes ?envM = {||}" by simp
    qed
  next
    show "tyenv_ctors_by_type_consistent ?envM"
      unfolding tyenv_ctors_by_type_consistent_def
    proof (intro allI impI)
      fix dtName ctors ctorName
      assume "fmlookup (TE_DataCtorsByType ?envM) dtName = Some ctors"
      then have btM: "fmlookup (TE_DataCtorsByType (CM_TyEnv m)) dtName = Some ctors"
        by simp
      show "(ctorName \<in> set ctors)
              = (\<exists>tyVars payload.
                   fmlookup (TE_DataCtors ?envM) ctorName = Some (dtName, tyVars, payload))"
      proof
        assume mem: "ctorName \<in> set ctors"
        obtain z where z_in: "z \<in> set ms"
                   and z_bt: "fmlookup (TE_DataCtorsByType (CM_TyEnv z)) dtName = Some ctors"
          using fmlist_union_lookup[OF btdisjM] btM[unfolded fM(15)] by auto
        from z_in setMS have "z \<in> set as \<or> z \<in> set bs" by auto
        then show "\<exists>tyVars payload.
                     fmlookup (TE_DataCtors ?envM) ctorName = Some (dtName, tyVars, payload)"
        proof
          assume z_as: "z \<in> set as"
          have btA': "fmlookup (TE_DataCtorsByType ?envA) dtName = Some ctors"
            using fmlist_union_lookup[OF btdisjA] z_as z_bt by (auto simp: fA(15))
          obtain tyVars payload where
              lkA: "fmlookup (TE_DataCtors ?envA) ctorName = Some (dtName, tyVars, payload)"
            using btcA[OF btA'] mem by blast
          obtain p00 where raw: "fmlookup (TE_DataCtors (CM_TyEnv a)) ctorName = Some (dtName, tyVars, p00)"
            using rawA_dc[OF lkA] by blast
          have "fmlookup (TE_DataCtors (CM_TyEnv m)) ctorName = Some (dtName, tyVars, p00)"
            using link_modules_decl_submaps(4)[OF linkA linkM subA raw] .
          then have "fmlookup (TE_DataCtors ?envM) ctorName
                       = Some (dtName, tyVars, apply_subst ?\<sigma> p00)"
            by simp
          then show ?thesis by blast
        next
          assume z_bs: "z \<in> set bs"
          have btB': "fmlookup (TE_DataCtorsByType ?envB) dtName = Some ctors"
            using fmlist_union_lookup[OF btdisjB] z_bs z_bt by (auto simp: fB(15))
          obtain tyVars payload where
              lkB: "fmlookup (TE_DataCtors ?envB) ctorName = Some (dtName, tyVars, payload)"
            using btcB[OF btB'] mem by blast
          obtain p00 where raw: "fmlookup (TE_DataCtors (CM_TyEnv b)) ctorName = Some (dtName, tyVars, p00)"
            using rawB_dc[OF lkB] by blast
          have "fmlookup (TE_DataCtors (CM_TyEnv m)) ctorName = Some (dtName, tyVars, p00)"
            using link_modules_decl_submaps(4)[OF linkB linkM subB raw] .
          then have "fmlookup (TE_DataCtors ?envM) ctorName
                       = Some (dtName, tyVars, apply_subst ?\<sigma> p00)"
            by simp
          then show ?thesis by blast
        qed
      next
        assume "\<exists>tyVars payload.
                  fmlookup (TE_DataCtors ?envM) ctorName = Some (dtName, tyVars, payload)"
        then obtain tyVars payload where
            lk2: "fmlookup (TE_DataCtors ?envM) ctorName = Some (dtName, tyVars, payload)"
          by blast
        from dc_cases[OF lk2] show "ctorName \<in> set ctors"
        proof
          assume "\<exists>p0. fmlookup (TE_DataCtors ?envA) ctorName = Some (dtName, tyVars, p0)
                       \<and> payload = apply_subst ?\<sigma> p0"
          then obtain p0 where lkA: "fmlookup (TE_DataCtors ?envA) ctorName = Some (dtName, tyVars, p0)"
            by blast
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
          assume "\<exists>p0. fmlookup (TE_DataCtors ?envB) ctorName = Some (dtName, tyVars, p0)
                       \<and> payload = apply_subst ?\<sigma> p0"
          then obtain p0 where lkB: "fmlookup (TE_DataCtors ?envB) ctorName = Some (dtName, tyVars, p0)"
            by blast
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
    show "tyenv_fun_types_well_kinded ?envM"
      unfolding tyenv_fun_types_well_kinded_def
    proof (intro allI impI)
      fix funName info
      assume lk: "fmlookup (TE_Functions ?envM) funName = Some info"
      from fn_cases[OF lk]
      show "(\<forall>ty \<in> fst ` set (FI_TmArgs info).
               is_well_kinded (?envM \<lparr> TE_TypeVars :=
                                       TE_AbstractTypes ?envM
                                       |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
            \<and> is_well_kinded (?envM \<lparr> TE_TypeVars :=
                                      TE_AbstractTypes ?envM
                                      |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                             (FI_ReturnType info)"
      proof
        assume "\<exists>info0. fmlookup (TE_Functions ?envA) funName = Some info0
                        \<and> info = apply_subst_to_funinfo ?\<sigma> info0"
        then obtain info0 where lkA: "fmlookup (TE_Functions ?envA) funName = Some info0"
                            and i_eq: "info = apply_subst_to_funinfo ?\<sigma> info0" by blast
        have tyargs: "FI_TyArgs info = FI_TyArgs info0" by (simp add: i_eq)
        note avoid = avoidA_fn[OF lkA, THEN conjunct1]
        have args: "\<And>ty. ty \<in> fst ` set (FI_TmArgs info) \<Longrightarrow>
                      is_well_kinded (?envM \<lparr> TE_TypeVars :=
                                              TE_AbstractTypes ?envM
                                              |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty"
        proof -
          fix ty assume "ty \<in> fst ` set (FI_TmArgs info)"
          then obtain ty0 where ty0_in: "ty0 \<in> fst ` set (FI_TmArgs info0)"
                            and ty_eq: "ty = apply_subst ?\<sigma> ty0"
            by (force simp: i_eq apply_subst_to_funinfo_def)
          have "is_well_kinded (?envA \<lparr> TE_TypeVars :=
                                        TE_AbstractTypes ?envA
                                        |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty0"
            using ftwkA[OF lkA] ty0_in by blast
          from wkA_M_b[OF this avoid] show "is_well_kinded (?envM \<lparr> TE_TypeVars :=
                                              TE_AbstractTypes ?envM
                                              |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty"
            unfolding ty_eq .
        qed
        have ret: "is_well_kinded (?envM \<lparr> TE_TypeVars :=
                                           TE_AbstractTypes ?envM
                                           |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>)
                     (FI_ReturnType info)"
          using wkA_M_b[OF ftwkA[OF lkA, THEN conjunct2] avoid] by (simp add: i_eq)
        show ?thesis using args ret unfolding tyargs by blast
      next
        assume "\<exists>info0. fmlookup (TE_Functions ?envB) funName = Some info0
                        \<and> info = apply_subst_to_funinfo ?\<sigma> info0"
        then obtain info0 where lkB: "fmlookup (TE_Functions ?envB) funName = Some info0"
                            and i_eq: "info = apply_subst_to_funinfo ?\<sigma> info0" by blast
        have tyargs: "FI_TyArgs info = FI_TyArgs info0" by (simp add: i_eq)
        note avoid = avoidB_fn[OF lkB, THEN conjunct1]
        have args: "\<And>ty. ty \<in> fst ` set (FI_TmArgs info) \<Longrightarrow>
                      is_well_kinded (?envM \<lparr> TE_TypeVars :=
                                              TE_AbstractTypes ?envM
                                              |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty"
        proof -
          fix ty assume "ty \<in> fst ` set (FI_TmArgs info)"
          then obtain ty0 where ty0_in: "ty0 \<in> fst ` set (FI_TmArgs info0)"
                            and ty_eq: "ty = apply_subst ?\<sigma> ty0"
            by (force simp: i_eq apply_subst_to_funinfo_def)
          have "is_well_kinded (?envB \<lparr> TE_TypeVars :=
                                        TE_AbstractTypes ?envB
                                        |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty0"
            using ftwkB[OF lkB] ty0_in by blast
          from wkB_M_b[OF this avoid] show "is_well_kinded (?envM \<lparr> TE_TypeVars :=
                                              TE_AbstractTypes ?envM
                                              |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty"
            unfolding ty_eq .
        qed
        have ret: "is_well_kinded (?envM \<lparr> TE_TypeVars :=
                                           TE_AbstractTypes ?envM
                                           |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>)
                     (FI_ReturnType info)"
          using wkB_M_b[OF ftwkB[OF lkB, THEN conjunct2] avoid] by (simp add: i_eq)
        show ?thesis using args ret unfolding tyargs by blast
      qed
    qed
  next
    show "tyenv_fun_tyvars_distinct ?envM"
      unfolding tyenv_fun_tyvars_distinct_def
    proof (intro allI impI)
      fix funName info
      assume lk: "fmlookup (TE_Functions ?envM) funName = Some info"
      show "distinct (FI_TyArgs info)"
        using fn_cases[OF lk] ftdA ftdB by (metis apply_subst_to_funinfo_FI_TyArgs)
    qed
  next
    show "tyenv_fun_tyvars_fresh ?envM"
      unfolding tyenv_fun_tyvars_fresh_def
    proof (intro allI impI)
      fix funName info
      assume lk: "fmlookup (TE_Functions ?envM) funName = Some info"
      have "fset_of_list (FI_TyArgs info) |\<inter>| ?U = {||}"
        using fn_cases[OF lk] avoidA_fn avoidB_fn by (metis apply_subst_to_funinfo_FI_TyArgs)
      then have "fset_of_list (FI_TyArgs info) |\<inter>| TE_AbstractTypes (CM_TyEnv m) = {||}"
        using fresh_sub[OF _ absU_m] by blast
      then show "fset_of_list (FI_TyArgs info) |\<inter>| TE_AbstractTypes ?envM = {||}" by simp
    qed
  next
    show "tyenv_fun_ghost_constraint ?envM"
      unfolding tyenv_fun_ghost_constraint_def Let_def
    proof (intro allI impI)
      fix funName info
      assume asm: "fmlookup (TE_Functions ?envM) funName = Some info
                     \<and> FI_Ghost info = NotGhost"
      then have lk: "fmlookup (TE_Functions ?envM) funName = Some info"
            and ng: "FI_Ghost info = NotGhost"
        by simp_all
      from fn_cases[OF lk]
      show "(\<forall>ty vor. (ty, vor, NotGhost) \<in> set (FI_TmArgs info) \<longrightarrow>
               is_runtime_type
                 (?envM \<lparr> TE_TypeVars := TE_AbstractTypes ?envM
                                         |\<union>| fset_of_list (FI_TyArgs info),
                          TE_RuntimeTypeVars :=
                            (TE_AbstractTypes ?envM |\<inter>| TE_RuntimeTypeVars ?envM)
                            |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
            \<and> is_runtime_type
                (?envM \<lparr> TE_TypeVars := TE_AbstractTypes ?envM
                                        |\<union>| fset_of_list (FI_TyArgs info),
                         TE_RuntimeTypeVars :=
                           (TE_AbstractTypes ?envM |\<inter>| TE_RuntimeTypeVars ?envM)
                           |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                (FI_ReturnType info)"
      proof
        assume "\<exists>info0. fmlookup (TE_Functions ?envA) funName = Some info0
                        \<and> info = apply_subst_to_funinfo ?\<sigma> info0"
        then obtain info0 where lkA: "fmlookup (TE_Functions ?envA) funName = Some info0"
                            and i_eq: "info = apply_subst_to_funinfo ?\<sigma> info0" by blast
        have tyargs: "FI_TyArgs info = FI_TyArgs info0" by (simp add: i_eq)
        have ng0: "FI_Ghost info0 = NotGhost" using ng by (simp add: i_eq)
        note avoid = avoidA_fn[OF lkA, THEN conjunct1]
        note freshU = avoidA_fn[OF lkA, THEN conjunct2]
        have lift: "\<And>ty0. ty0 \<in> fst ` set (FI_TmArgs info0) \<or> ty0 = FI_ReturnType info0 \<Longrightarrow>
                      is_runtime_type
                        (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA
                                                |\<union>| fset_of_list (FI_TyArgs info0),
                                 TE_RuntimeTypeVars :=
                                   (TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA)
                                   |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty0 \<Longrightarrow>
                      is_runtime_type
                        (?envM \<lparr> TE_TypeVars := TE_AbstractTypes ?envM
                                                |\<union>| fset_of_list (FI_TyArgs info0),
                                 TE_RuntimeTypeVars :=
                                   (TE_AbstractTypes ?envM |\<inter>| TE_RuntimeTypeVars ?envM)
                                   |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) (apply_subst ?\<sigma> ty0)"
        proof -
          fix ty0
          assume which: "ty0 \<in> fst ` set (FI_TmArgs info0) \<or> ty0 = FI_ReturnType info0"
             and r: "is_runtime_type
                        (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA
                                                |\<union>| fset_of_list (FI_TyArgs info0),
                                 TE_RuntimeTypeVars :=
                                   (TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA)
                                   |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty0"
          have w: "is_well_kinded (?envA \<lparr> TE_TypeVars :=
                                           TE_AbstractTypes ?envA
                                           |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty0"
            using ftwkA[OF lkA] which by blast
          show "is_runtime_type
                  (?envM \<lparr> TE_TypeVars := TE_AbstractTypes ?envM
                                          |\<union>| fset_of_list (FI_TyArgs info0),
                           TE_RuntimeTypeVars :=
                             (TE_AbstractTypes ?envM |\<inter>| TE_RuntimeTypeVars ?envM)
                             |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) (apply_subst ?\<sigma> ty0)"
            by (rule rtA_M_b[OF freshU avoid w r])
        qed
        have args: "\<forall>ty vor. (ty, vor, NotGhost) \<in> set (FI_TmArgs info) \<longrightarrow>
                      is_runtime_type
                        (?envM \<lparr> TE_TypeVars := TE_AbstractTypes ?envM
                                                |\<union>| fset_of_list (FI_TyArgs info0),
                                 TE_RuntimeTypeVars :=
                                   (TE_AbstractTypes ?envM |\<inter>| TE_RuntimeTypeVars ?envM)
                                   |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty"
        proof (intro allI impI)
          fix ty vor assume "(ty, vor, NotGhost) \<in> set (FI_TmArgs info)"
          then obtain ty0 where ty0_in: "(ty0, vor, NotGhost) \<in> set (FI_TmArgs info0)"
                            and ty_eq: "ty = apply_subst ?\<sigma> ty0"
            by (force simp: i_eq apply_subst_to_funinfo_def)
          have "ty0 \<in> fst ` set (FI_TmArgs info0)" using ty0_in by force
          moreover have "is_runtime_type
                           (?envA \<lparr> TE_TypeVars := TE_AbstractTypes ?envA
                                                   |\<union>| fset_of_list (FI_TyArgs info0),
                                    TE_RuntimeTypeVars :=
                                      (TE_AbstractTypes ?envA |\<inter>| TE_RuntimeTypeVars ?envA)
                                      |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty0"
            using fgcA[OF lkA ng0] ty0_in by blast
          ultimately show "is_runtime_type
                             (?envM \<lparr> TE_TypeVars := TE_AbstractTypes ?envM
                                                     |\<union>| fset_of_list (FI_TyArgs info0),
                                      TE_RuntimeTypeVars :=
                                        (TE_AbstractTypes ?envM |\<inter>| TE_RuntimeTypeVars ?envM)
                                        |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty"
            unfolding ty_eq by (intro lift) blast
        qed
        have ret: "is_runtime_type
                     (?envM \<lparr> TE_TypeVars := TE_AbstractTypes ?envM
                                             |\<union>| fset_of_list (FI_TyArgs info0),
                              TE_RuntimeTypeVars :=
                                (TE_AbstractTypes ?envM |\<inter>| TE_RuntimeTypeVars ?envM)
                                |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) (FI_ReturnType info)"
          using lift[of "FI_ReturnType info0"] fgcA[OF lkA ng0] by (simp add: i_eq)
        show ?thesis using args ret unfolding tyargs by blast
      next
        assume "\<exists>info0. fmlookup (TE_Functions ?envB) funName = Some info0
                        \<and> info = apply_subst_to_funinfo ?\<sigma> info0"
        then obtain info0 where lkB: "fmlookup (TE_Functions ?envB) funName = Some info0"
                            and i_eq: "info = apply_subst_to_funinfo ?\<sigma> info0" by blast
        have tyargs: "FI_TyArgs info = FI_TyArgs info0" by (simp add: i_eq)
        have ng0: "FI_Ghost info0 = NotGhost" using ng by (simp add: i_eq)
        note avoid = avoidB_fn[OF lkB, THEN conjunct1]
        note freshU = avoidB_fn[OF lkB, THEN conjunct2]
        have lift: "\<And>ty0. ty0 \<in> fst ` set (FI_TmArgs info0) \<or> ty0 = FI_ReturnType info0 \<Longrightarrow>
                      is_runtime_type
                        (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB
                                                |\<union>| fset_of_list (FI_TyArgs info0),
                                 TE_RuntimeTypeVars :=
                                   (TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB)
                                   |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty0 \<Longrightarrow>
                      is_runtime_type
                        (?envM \<lparr> TE_TypeVars := TE_AbstractTypes ?envM
                                                |\<union>| fset_of_list (FI_TyArgs info0),
                                 TE_RuntimeTypeVars :=
                                   (TE_AbstractTypes ?envM |\<inter>| TE_RuntimeTypeVars ?envM)
                                   |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) (apply_subst ?\<sigma> ty0)"
        proof -
          fix ty0
          assume which: "ty0 \<in> fst ` set (FI_TmArgs info0) \<or> ty0 = FI_ReturnType info0"
             and r: "is_runtime_type
                        (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB
                                                |\<union>| fset_of_list (FI_TyArgs info0),
                                 TE_RuntimeTypeVars :=
                                   (TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB)
                                   |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty0"
          have w: "is_well_kinded (?envB \<lparr> TE_TypeVars :=
                                           TE_AbstractTypes ?envB
                                           |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty0"
            using ftwkB[OF lkB] which by blast
          show "is_runtime_type
                  (?envM \<lparr> TE_TypeVars := TE_AbstractTypes ?envM
                                          |\<union>| fset_of_list (FI_TyArgs info0),
                           TE_RuntimeTypeVars :=
                             (TE_AbstractTypes ?envM |\<inter>| TE_RuntimeTypeVars ?envM)
                             |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) (apply_subst ?\<sigma> ty0)"
            by (rule rtB_M_b[OF freshU avoid w r])
        qed
        have args: "\<forall>ty vor. (ty, vor, NotGhost) \<in> set (FI_TmArgs info) \<longrightarrow>
                      is_runtime_type
                        (?envM \<lparr> TE_TypeVars := TE_AbstractTypes ?envM
                                                |\<union>| fset_of_list (FI_TyArgs info0),
                                 TE_RuntimeTypeVars :=
                                   (TE_AbstractTypes ?envM |\<inter>| TE_RuntimeTypeVars ?envM)
                                   |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty"
        proof (intro allI impI)
          fix ty vor assume "(ty, vor, NotGhost) \<in> set (FI_TmArgs info)"
          then obtain ty0 where ty0_in: "(ty0, vor, NotGhost) \<in> set (FI_TmArgs info0)"
                            and ty_eq: "ty = apply_subst ?\<sigma> ty0"
            by (force simp: i_eq apply_subst_to_funinfo_def)
          have "ty0 \<in> fst ` set (FI_TmArgs info0)" using ty0_in by force
          moreover have "is_runtime_type
                           (?envB \<lparr> TE_TypeVars := TE_AbstractTypes ?envB
                                                   |\<union>| fset_of_list (FI_TyArgs info0),
                                    TE_RuntimeTypeVars :=
                                      (TE_AbstractTypes ?envB |\<inter>| TE_RuntimeTypeVars ?envB)
                                      |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty0"
            using fgcB[OF lkB ng0] ty0_in by blast
          ultimately show "is_runtime_type
                             (?envM \<lparr> TE_TypeVars := TE_AbstractTypes ?envM
                                                     |\<union>| fset_of_list (FI_TyArgs info0),
                                      TE_RuntimeTypeVars :=
                                        (TE_AbstractTypes ?envM |\<inter>| TE_RuntimeTypeVars ?envM)
                                        |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) ty"
            unfolding ty_eq by (intro lift) blast
        qed
        have ret: "is_runtime_type
                     (?envM \<lparr> TE_TypeVars := TE_AbstractTypes ?envM
                                             |\<union>| fset_of_list (FI_TyArgs info0),
                              TE_RuntimeTypeVars :=
                                (TE_AbstractTypes ?envM |\<inter>| TE_RuntimeTypeVars ?envM)
                                |\<union>| fset_of_list (FI_TyArgs info0) \<rparr>) (FI_ReturnType info)"
          using lift[of "FI_ReturnType info0"] fgcB[OF lkB ng0] by (simp add: i_eq)
        show ?thesis using args ret unfolding tyargs by blast
      qed
    qed
  next
    show "tyenv_fun_return_types_complete ?envM"
      unfolding tyenv_fun_return_types_complete_def
    proof (intro allI impI)
      fix funName info
      assume asm: "fmlookup (TE_Functions ?envM) funName = Some info
                     \<and> FI_Ghost info = NotGhost"
      then have lk: "fmlookup (TE_Functions ?envM) funName = Some info"
            and ng: "FI_Ghost info = NotGhost"
        by simp_all
      from fn_cases[OF lk]
      show "is_complete_type (FI_ReturnType info)"
      proof
        assume "\<exists>info0. fmlookup (TE_Functions ?envA) funName = Some info0
                        \<and> info = apply_subst_to_funinfo ?\<sigma> info0"
        then obtain info0 where lkA: "fmlookup (TE_Functions ?envA) funName = Some info0"
                            and i_eq: "info = apply_subst_to_funinfo ?\<sigma> info0" by blast
        have "is_complete_type (FI_ReturnType info0)"
          using frcA[OF lkA] ng by (simp add: i_eq)
        then show ?thesis
          using apply_subst_preserves_complete[OF _ cp] by (simp add: i_eq)
      next
        assume "\<exists>info0. fmlookup (TE_Functions ?envB) funName = Some info0
                        \<and> info = apply_subst_to_funinfo ?\<sigma> info0"
        then obtain info0 where lkB: "fmlookup (TE_Functions ?envB) funName = Some info0"
                            and i_eq: "info = apply_subst_to_funinfo ?\<sigma> info0" by blast
        have "is_complete_type (FI_ReturnType info0)"
          using frcB[OF lkB] ng by (simp add: i_eq)
        then show ?thesis
          using apply_subst_preserves_complete[OF _ cp] by (simp add: i_eq)
      qed
    qed
  next
    show "tyenv_runtime_tyvars_subset ?envM"
      unfolding tyenv_runtime_tyvars_subset_def using rtvM by simp
  next
    show "tyenv_abstract_types_subset ?envM"
      unfolding tyenv_abstract_types_subset_def using absM by simp
  next
    have H: "\<And>dtName. dtName |\<in>| fmdom (TE_Datatypes ?envM) \<Longrightarrow>
               \<exists>ctorName ctors.
                 fmlookup (TE_DataCtorsByType ?envM) dtName = Some (ctorName # ctors)"
    proof -
      fix dtName assume "dtName |\<in>| fmdom (TE_Datatypes ?envM)"
      then have "dtName |\<in>| fmdom (TE_Datatypes (CM_TyEnv a))
                   \<or> dtName |\<in>| fmdom (TE_Datatypes (CM_TyEnv b))"
        using dtdom by auto
      then show "\<exists>ctorName ctors.
                   fmlookup (TE_DataCtorsByType ?envM) dtName = Some (ctorName # ctors)"
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
                fmlookup (TE_DataCtorsByType ?envM) dtName = Some ctors \<Longrightarrow> ctors \<noteq> []"
    proof -
      fix dtName ctors
      assume lk: "fmlookup (TE_DataCtorsByType ?envM) dtName = Some ctors"
      from lk have "fmlookup (fmlist_union
                       (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) ms)) dtName
                      = Some ctors"
        by (simp add: fM(15))
      then obtain x where x_in: "x \<in> set ms"
        and x_lk: "fmlookup (TE_DataCtorsByType (CM_TyEnv x)) dtName = Some ctors"
        using fmlist_union_lookup[OF btdisjM] by auto
      from x_in setMS have "x \<in> set as \<or> x \<in> set bs" by auto
      then show "ctors \<noteq> []"
      proof
        assume xA: "x \<in> set as"
        have "fmlookup (fmlist_union
                (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) as)) dtName = Some ctors"
          using fmlist_union_lookup[OF btdisjA] xA x_lk by auto
        then have "fmlookup (TE_DataCtorsByType ?envA) dtName = Some ctors"
          by (simp add: fA(15))
        then show ?thesis using dneA2 by blast
      next
        assume xB: "x \<in> set bs"
        have "fmlookup (fmlist_union
                (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) bs)) dtName = Some ctors"
          using fmlist_union_lookup[OF btdisjB] xB x_lk by auto
        then have "fmlookup (TE_DataCtorsByType ?envB) dtName = Some ctors"
          by (simp add: fB(15))
        then show ?thesis using dneB2 by blast
      qed
    qed
    show "tyenv_datatypes_nonempty ?envM"
      unfolding tyenv_datatypes_nonempty_def
    proof (intro conjI)
      show "fmdom (TE_Datatypes ?envM) |\<subseteq>| fmdom (TE_DataCtorsByType ?envM)"
        using H by (metis fmdomI fsubsetI)
      show "\<forall>dtName ctors.
              fmlookup (TE_DataCtorsByType ?envM) dtName = Some ctors \<longrightarrow> ctors \<noteq> []"
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
(* a-side), and an a-declared datatype that is runtime on the a-side stays   *)
(* runtime (the locality of the ghost set, link_mid_env_ghost_local, which   *)
(* needs the a-side's well-formedness).                                       *)
(* ========================================================================== *)

lemma link_mid_env_extends:
  assumes linkA: "link_modules as = Inr a"
      and linkB: "link_modules bs = Inr b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
      and wfA: "tyenv_well_formed (CM_TyEnv (normalize_module a))"
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

  \<comment> \<open>An a-declared datatype that is runtime on the a-side is runtime in the
      mid env: the mid env's runtime abstract types extend the a-side's.\<close>
  have gd_agree: "\<And>name. name |\<in>| fmdom (TE_Datatypes ?envA)
                    \<Longrightarrow> name \<notin> ghost_datatypes ?envA \<Longrightarrow> name \<notin> ghost_datatypes ?mid"
  proof -
    fix name
    assume "name |\<in>| fmdom (TE_Datatypes ?envA)" and ng: "name \<notin> ghost_datatypes ?envA"
    then have dom: "name |\<in>| fmdom (TE_Datatypes (CM_TyEnv a))" by simp
    have ng': "name \<notin> ghost_datatypes_r (CM_TyEnv (normalize_module a))
                        (TE_AbstractTypes (CM_TyEnv a)
                         |\<inter>| (TE_RuntimeTypeVars (CM_TyEnv a) |\<union>| TE_RuntimeTypeVars (CM_TyEnv b)))"
      using ng by simp
    have "name \<notin> ghost_datatypes_r (link_mid_env a b m)
                   ((TE_AbstractTypes (CM_TyEnv a) |\<union>| TE_AbstractTypes (CM_TyEnv b))
                    |\<inter>| (TE_RuntimeTypeVars (CM_TyEnv a) |\<union>| TE_RuntimeTypeVars (CM_TyEnv b)))"
      by (rule link_mid_env_ghost_local[OF linkA linkM subA wfA _ dom ng']) auto
    then show "name \<notin> ghost_datatypes ?mid" by simp
  qed

  show ?thesis
    unfolding tyenv_extends_def
  proof (intro conjI)
    show "TE_LocalVars ?mid = TE_LocalVars ?envA"
      by (simp add: fA(1) fM(1))
    show "TE_GhostLocals ?mid = TE_GhostLocals ?envA"
      by (simp add: fA(3) fM(3))
    show "TE_ConstLocals ?mid = TE_ConstLocals ?envA"
      by (simp add: fA(4) fM(4))
    show "TE_TypeVars ?mid = TE_TypeVars ?envA" by simp
    show "TE_RuntimeTypeVars ?mid = TE_RuntimeTypeVars ?envA" by simp
    show "TE_ReturnType ?mid = TE_ReturnType ?envA"
      by (simp add: fA(8) fM(8))
    show "TE_FunctionGhost ?mid = TE_FunctionGhost ?envA"
      by (simp add: fA(9) fM(9))
    show "TE_FunctionImpure ?mid = TE_FunctionImpure ?envA"
      by (simp add: fA(18) fM(18))
    show "TE_ProofGoal ?mid = TE_ProofGoal ?envA"
      by (simp add: fA(10) fM(10))
    show "TE_ProofTopLevel ?mid = TE_ProofTopLevel ?envA"
      by (simp add: fA(11) fM(11))
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
    show "\<forall>name. name |\<in>| fmdom (TE_Datatypes ?envA) \<longrightarrow>
            name \<notin> ghost_datatypes ?envA \<longrightarrow> name \<notin> ghost_datatypes ?mid"
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
      and wfA: "tyenv_well_formed (CM_TyEnv (normalize_module a))"
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
  have subA: "set as \<subseteq> set ms" using setMS by auto
  note ext0 = link_mid_env_extends[OF linkA linkB linkM setMS wfA]

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
  \<comment> \<open>The ghost clause: both body envs' runtime abstract types are those of
      the module-level envs underneath (the function's type parameters shadow
      no abstract type), so the module-level locality applies.\<close>
  have gd_agr: "\<And>name. name |\<in>| fmdom (TE_Datatypes ?envA) \<Longrightarrow>
                  name \<notin> ghost_datatypes ?e1 \<Longrightarrow> name \<notin> ghost_datatypes ?be2"
  proof -
    fix name
    assume dom: "name |\<in>| fmdom (TE_Datatypes ?envA)" and ng: "name \<notin> ghost_datatypes ?e1"
    let ?T = "if FI_Ghost info = NotGhost then fset_of_list (FI_TyArgs info) else {||}"
    have dom': "name |\<in>| fmdom (TE_Datatypes (CM_TyEnv a))" using dom by simp
    have ng': "name \<notin> ghost_datatypes_r (CM_TyEnv (normalize_module a))
                 (TE_AbstractTypes (CM_TyEnv a)
                  |\<inter>| (((TE_AbstractTypes (CM_TyEnv a) |\<inter>| TE_RuntimeTypeVars (CM_TyEnv a)) |\<union>| ?T)
                       |\<union>| TE_RuntimeTypeVars (CM_TyEnv b)))"
      using ng by (simp add: module_body_env_for_def)
    have "name \<notin> ghost_datatypes_r (link_mid_env a b m)
            ((TE_AbstractTypes (CM_TyEnv a) |\<union>| TE_AbstractTypes (CM_TyEnv b))
             |\<inter>| (((TE_AbstractTypes (CM_TyEnv a) |\<union>| TE_AbstractTypes (CM_TyEnv b))
                   |\<inter>| (TE_RuntimeTypeVars (CM_TyEnv a) |\<union>| TE_RuntimeTypeVars (CM_TyEnv b)))
                  |\<union>| ?T))"
      by (rule link_mid_env_ghost_local[OF linkA linkM subA wfA _ dom' ng']) auto
    then show "name \<notin> ghost_datatypes ?be2"
      by (simp add: module_body_env_for_def)
  qed

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
      by (rule fset_eqI) (auto simp: module_body_env_for_def absa absb)
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
    show "TE_FunctionImpure ?be2 = TE_FunctionImpure ?e1"
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
    show "\<forall>name. name |\<in>| fmdom (TE_Datatypes ?e1) \<longrightarrow>
            name \<notin> ghost_datatypes ?e1 \<longrightarrow> name \<notin> ghost_datatypes ?be2"
      using gd_agr by (simp add: module_body_env_for_def)
  qed
qed

(* module_env_subst_ok at the body level: the datatype tables and the
   function/ctor binder clauses are the mid env's (the body env leaves those
   maps untouched); the tyvar coverage adds the function's own type
   parameters, which the whole link's capture check keeps out of the
   substitution.

   The module-level module_env_subst_ok fact and the abstract-types
   convention of the whole link and of both sides are taken as premises, so
   this works from any proof of the module-level fact (both sides well-typed,
   or one side carrying only the structural invariant). The sides' convention
   is what identifies the mid env's abstract types (the union of the two
   level maps' domains) with its type variables.

   The signature info0 need not itself be declared in m: it is enough that it
   has the type parameters of some function info1 that is (for instance,
   info0 = post_funinfo info1, for a postcondition). Those type parameters
   must shadow no abstract type of the mid env (freshMid, from the whole
   link's capture check), so that opening them leaves the ghost sets of both
   body envs those of the module-level envs. *)
lemma link_mid_body_env_subst_ok:
  assumes linkM: "link_modules ms = Inr m"
      and m_lk: "fmlookup (TE_Functions (CM_TyEnv m)) fname = Some info1"
      and tyargs: "FI_TyArgs info = FI_TyArgs info0"
      and mid_ok: "module_env_subst_ok (CM_TypeSubst m)
                     (CM_TyEnv (normalize_module m)) (link_mid_env a b m)"
      and absM: "TE_AbstractTypes (CM_TyEnv m) = TE_TypeVars (CM_TyEnv m)"
      and tyargs1: "FI_TyArgs info0 = FI_TyArgs info1"
      and absa: "TE_AbstractTypes (CM_TyEnv a) = TE_TypeVars (CM_TyEnv a)"
      and absb: "TE_AbstractTypes (CM_TyEnv b) = TE_TypeVars (CM_TyEnv b)"
      and freshMid: "fset_of_list (FI_TyArgs info0)
                       |\<inter>| TE_AbstractTypes (link_mid_env a b m) = {||}"
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
  have mid_dc: "TE_DataCtors (CM_TyEnv (normalize_module m))
                  = fmmap (apply_subst_to_datactor (CM_TypeSubst m)) (TE_DataCtors ?mid)"
   and mid_abs: "TE_AbstractTypes (CM_TyEnv (normalize_module m))
                   = TE_AbstractTypes ?mid |-| fmdom (CM_TypeSubst m)"
   and mid_gd: "ghost_datatypes (CM_TyEnv (normalize_module m)) \<subseteq> ghost_datatypes ?mid"
    using mid_ok unfolding module_env_subst_ok_def by blast+

  \<comment> \<open>The type parameters shadow no abstract type of either env, so the
      runtime abstract types of the body envs are the module-level ones.\<close>
  have absM_mid: "TE_AbstractTypes (CM_TyEnv m) = TE_AbstractTypes ?mid |-| fmdom (CM_TypeSubst m)"
    using mid_abs by simp
  have freshM: "fset_of_list (FI_TyArgs info0) |\<inter>| TE_AbstractTypes (CM_TyEnv m) = {||}"
    unfolding absM_mid using freshMid by auto
  have freshMid': "fset_of_list (FI_TyArgs info0)
                     |\<inter>| (TE_AbstractTypes (CM_TyEnv a) |\<union>| TE_AbstractTypes (CM_TyEnv b)) = {||}"
    using freshMid by simp
  have eqM: "TE_AbstractTypes (CM_TyEnv m)
               |\<inter>| ((TE_AbstractTypes (CM_TyEnv m) |\<inter>| TE_RuntimeTypeVars (CM_TyEnv m))
                    |\<union>| fset_of_list (FI_TyArgs info0))
             = TE_AbstractTypes (CM_TyEnv m) |\<inter>| TE_RuntimeTypeVars (CM_TyEnv m)"
    by (rule fset_eqI) (metis freshM fempty_iff finter_iff funion_iff)
  have eqMid: "(TE_AbstractTypes (CM_TyEnv a) |\<union>| TE_AbstractTypes (CM_TyEnv b))
                 |\<inter>| (((TE_AbstractTypes (CM_TyEnv a) |\<union>| TE_AbstractTypes (CM_TyEnv b))
                       |\<inter>| (TE_RuntimeTypeVars (CM_TyEnv a) |\<union>| TE_RuntimeTypeVars (CM_TyEnv b)))
                      |\<union>| fset_of_list (FI_TyArgs info0))
               = (TE_AbstractTypes (CM_TyEnv a) |\<union>| TE_AbstractTypes (CM_TyEnv b))
                 |\<inter>| (TE_RuntimeTypeVars (CM_TyEnv a) |\<union>| TE_RuntimeTypeVars (CM_TyEnv b))"
    by (rule fset_eqI) (metis freshMid' fempty_iff finter_iff funion_iff)

  show ?thesis
    unfolding module_env_subst_ok_def
  proof (intro conjI)
    show "TE_Datatypes ?tb = TE_Datatypes ?sb"
      by (simp add: module_body_env_for_def)
    show "TE_DataCtorsByType ?tb = TE_DataCtorsByType ?sb"
      by (simp add: module_body_env_for_def)
    show "TE_DataCtors ?tb = fmmap (apply_subst_to_datactor (CM_TypeSubst m)) (TE_DataCtors ?sb)"
      using mid_dc by (simp add: module_body_env_for_def)
    show "TE_AbstractTypes ?tb = TE_AbstractTypes ?sb |-| fmdom (CM_TypeSubst m)"
      using mid_abs by (simp add: module_body_env_for_def)
    show "ghost_datatypes ?tb \<subseteq> ghost_datatypes ?sb"
      using mid_gd by (simp add: module_body_env_for_def tyargs eqM eqMid)
  next
    show "\<forall>n. n |\<in>| TE_TypeVars ?sb \<longrightarrow>
            (case fmlookup (CM_TypeSubst m) n of
               Some ty' \<Rightarrow> is_well_kinded ?tb ty'
             | None \<Rightarrow> n |\<in>| TE_TypeVars ?tb)"
    proof (intro allI impI)
      fix n assume "n |\<in>| TE_TypeVars ?sb"
      then have "n |\<in>| TE_TypeVars ?mid \<or> n |\<in>| fset_of_list (FI_TyArgs info0)"
        by (auto simp: module_body_env_for_def tyargs absa absb)
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
          using link_capture_tyargs_none[OF linkM m_lk n_ty[unfolded tyargs1]] .
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
          \<comment> \<open>Opening the function's type parameters as runtime can only
              shrink the ghost set.\<close>
          show "ghost_datatypes ?tb \<subseteq> ghost_datatypes (CM_TyEnv (normalize_module m))"
            by (simp add: module_body_env_for_def)
               (intro impI ghost_datatypes_r_antitone; auto)
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
      using snds by (simp add: module_body_env_for_def info_rel apply_subst_to_funinfo_def compS)
    show "TE_ConstLocals ?lhs = TE_ConstLocals ?tb"
      using snds by (simp add: module_body_env_for_def compS)
    show "TE_TypeVars ?lhs = TE_TypeVars ?tb"
      by simp
    show "TE_RuntimeTypeVars ?lhs = TE_RuntimeTypeVars ?tb"
      by simp
    show "TE_ReturnType ?lhs = TE_ReturnType ?tb"
      by (simp add: module_body_env_for_def info_rel apply_subst_to_funinfo_def absA)
    show "TE_FunctionGhost ?lhs = TE_FunctionGhost ?tb"
      by (simp add: module_body_env_for_def info_rel apply_subst_to_funinfo_def)
    show "TE_FunctionImpure ?lhs = TE_FunctionImpure ?tb"
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
    show "TE_AbstractAllocLevels ?lhs = TE_AbstractAllocLevels ?tb"
      by simp
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
      and a_def: "fmlookup (CM_GlobalVars a) name = Some v"
  shows "\<exists>declTy.
           fmlookup (TE_GlobalVars (CM_TyEnv (normalize_module m))) name = Some declTy \<and>
           value_has_type (CM_TyEnv (normalize_module m)) v declTy"
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
  have a_def': "fmlookup (CM_GlobalVars (normalize_module a)) name = Some v"
    using a_def by simp
  obtain declTy0 where
      a_decl: "fmlookup (TE_GlobalVars ?envA) name = Some declTy0" and
      a_vht: "value_has_type ?envA v declTy0"
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

  \<comment> \<open>The value-typing chain, mirroring the term chain - but the value itself
      never moves, only the environment does. The tyvar-widening step of the
      term chain is unnecessary: value_has_type ignores the tyvar fields, so
      one value_has_type_env_mono application reaches the mid env directly.\<close>
  have ext: "tyenv_extends ?e1 ?mid"
    using link_mid_env_extends[OF linkA linkB linkM setMS wfA] .
  have v_mid: "value_has_type ?mid v declTy0"
  proof (rule value_has_type_env_mono[OF _ _ a_vht])
    fix c e assume "fmlookup (TE_DataCtors ?envA) c = Some e"
    hence "fmlookup (TE_DataCtors ?e1) c = Some e" by simp
    thus "fmlookup (TE_DataCtors ?mid) c = Some e"
      using ext unfolding tyenv_extends_def by blast
  next
    fix d n assume "fmlookup (TE_Datatypes ?envA) d = Some n"
    hence "fmlookup (TE_Datatypes ?e1) d = Some n" by simp
    thus "fmlookup (TE_Datatypes ?mid) d = Some n"
      using ext unfolding tyenv_extends_def by blast
  qed
  \<comment> \<open>Substitute with the whole link's substitution, then collapse the env.\<close>
  have v_subst: "value_has_type (apply_subst_to_module_env ?\<sigma>M ?envM ?mid) v
                   (apply_subst ?\<sigma>M declTy0)"
    using value_has_type_subst_module_env[OF v_mid
            link_mid_env_binders_distinct[OF wtA wtB]
            link_mid_env_subst_ok[OF linkA wtA linkB wtB linkM setMS]] .
  have v_final: "value_has_type ?envM v (apply_subst ?\<sigma>M declTy00)"
    using v_subst
    unfolding link_mid_env_collapse[OF linkA linkB linkM setMS] declTy_abs .
  show ?thesis using m_decl v_final by auto
qed


lemma link_mid_functions_contribution:
  assumes linkA: "link_modules as = Inr a"
      and wtA: "core_module_well_typed a"
      and linkB: "link_modules bs = Inr b"
      and wtB: "core_module_well_typed b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
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
                  (apply_subst_to_statement_list (CM_TypeSubst m) body0) \<noteq> None) \<and>
           fun_contracts_well_typed (CM_TyEnv (normalize_module m)) info"
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
  have cpA: "typesubst_complete (CM_TypeSubst a)"
    and cpB: "typesubst_complete (CM_TypeSubst b)"
    using wtA wtB unfolding core_module_well_typed_def by blast+

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
                       (FI_Ghost infoA) body \<noteq> None" and
      ctrA: "fun_contracts_well_typed ?envA infoA"
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
  \<comment> \<open>The function's type parameters shadow no abstract type of the mid env
      (the whole link's capture check).\<close>
  have freshMid: "fset_of_list (FI_TyArgs info0) |\<inter>| TE_AbstractTypes ?mid = {||}"
  proof -
    note fA = link_modules_result_fields[OF linkA]
    note fB = link_modules_result_fields[OF linkB]
    have absU_a: "TE_AbstractTypes (CM_TyEnv a)
                    |\<subseteq>| funion_list (map (\<lambda>y. TE_AbstractTypes (CM_TyEnv y)) ms)"
      unfolding fA(7) funion_list_split[OF setMS] by auto
    have absU_b: "TE_AbstractTypes (CM_TyEnv b)
                    |\<subseteq>| funion_list (map (\<lambda>y. TE_AbstractTypes (CM_TyEnv y)) ms)"
      unfolding fB(7) funion_list_split[OF setMS] by auto
    have "fset_of_list (FI_TyArgs info0)
            |\<inter>| (TE_AbstractTypes (CM_TyEnv a) |\<union>| TE_AbstractTypes (CM_TyEnv b)) = {||}"
      using link_side_binders_fresh(1)[OF linkA linkM subA a_raw] absU_a absU_b
      by auto
    then show ?thesis by simp
  qed
  have mid_bd: "tyenv_binders_distinct ?mid"
    using link_mid_env_binders_distinct[OF wtA wtB] .

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
              link_mid_body_env_extends[OF linkA linkB linkM setMS wfA
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
    have wf_sb: "tyenv_binders_distinct ?sb"
      using mid_bd by simp
    have ok_sb: "module_env_subst_ok ?\<sigma>M ?tb ?sb"
      using link_mid_body_env_subst_ok[OF linkM m_raw tyargs
              link_mid_env_subst_ok[OF linkA wtA linkB wtB linkM setMS] absM refl
              absa absb freshMid] .
    have rt_sb: "module_env_subst_runtime_ok ?\<sigma>M ?tb ?sb"
      using link_mid_body_env_runtime_ok[OF linkA linkB linkM setMS
                                            m_raw tyargs ghostA absM rtvM] .
    have cp_sb: "\<forall>ty' \<in> fmran' ?\<sigma>M. is_complete_type ty'"
      using link_modules_typesubst_complete[OF linkA linkB linkM setMS cpA cpB]
      unfolding typesubst_complete_def .
    have t3: "core_statement_list_type (apply_subst_to_module_env ?\<sigma>M ?tb ?sb)
                (FI_Ghost infoA)
                (apply_subst_to_statement_list ?\<sigma>M ?bodyA)
                = Some (apply_subst_to_module_env ?\<sigma>M ?tb envOut2)"
      using core_statement_list_type_subst_module_env[OF cp_sb t2 wf_sb ok_sb] rt_sb
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

  \<comment> \<open>The contract chain: widen and extend the a-side contract envs into the
      mid env's, then substitute with the whole link's substitution and
      collapse, as for the body.\<close>
  have ctr_mid: "fun_contracts_well_typed ?mid infoA"
  proof (rule fun_contracts_well_typed_mono[OF ctrA])
    fix names info' tm
    assume t0: "core_term_type (module_body_env_for ?envA names info') Ghost tm
                  = Some CoreTy_Bool"
    let ?be = "module_body_env_for ?envA names info'"
    let ?e1' = "?be \<lparr> TE_TypeVars := TE_TypeVars ?be |\<union>| TE_TypeVars (CM_TyEnv b),
                      TE_RuntimeTypeVars :=
                        TE_RuntimeTypeVars ?be |\<union>| TE_RuntimeTypeVars (CM_TyEnv b) \<rparr>"
    have t1: "core_term_type ?e1' Ghost tm = Some CoreTy_Bool"
      using core_term_type_irrelevant_tyvar[OF t0,
              where extraTV = "TE_TypeVars (CM_TyEnv b)"
                and extraRT = "TE_RuntimeTypeVars (CM_TyEnv b)"] .
    have ext1: "tyenv_extends ?e1' (module_body_env_for ?mid names info')"
      using link_mid_body_env_extends[OF linkA linkB linkM setMS wfA
                                         absa rtva absb rtvb,
                                       where names = names and info = info'] .
    have cons1': "tyenv_ctors_consistent ?e1'"
      using wfA unfolding tyenv_well_formed_def tyenv_ctors_consistent_def
      by (simp add: module_body_env_for_def)
    show "core_term_type (module_body_env_for ?mid names info') Ghost tm = Some CoreTy_Bool"
      using core_term_type_tyenv_extends[OF ext1 cons1' t1] .
  qed
  have mid_lk0: "fmlookup (TE_Functions ?mid) name = Some infoA"
  proof -
    have "name |\<in>| fmdom (fmmap (apply_subst_to_funinfo ?\<sigma>A)
                                 (TE_Functions (CM_TyEnv a)))"
      using a_raw by (auto intro: fmdomI)
    then show ?thesis
      using a_raw infoA_eq by (auto simp: fmadd_drop_lookup)
  qed
  have mid_ok: "module_env_subst_ok ?\<sigma>M ?envM ?mid"
    using link_mid_env_subst_ok[OF linkA wtA linkB wtB linkM setMS] .
  have cp_M: "\<forall>ty' \<in> fmran' ?\<sigma>M. is_complete_type ty'"
    using link_modules_typesubst_complete[OF linkA linkB linkM setMS cpA cpB]
    unfolding typesubst_complete_def .
  have ctr_sub: "fun_contracts_well_typed ?envM (apply_subst_to_funinfo ?\<sigma>M infoA)"
  proof (rule fun_contracts_well_typed_subst[OF ctr_mid])
    fix names info'' tm
    assume which: "info'' = infoA \<or> info'' = post_funinfo infoA"
       and lenN: "length names = length (FI_TmArgs info'')"
       and typed: "core_term_type (module_body_env_for ?mid names info'') Ghost tm
                     = Some CoreTy_Bool"
    \<comment> \<open>The unsubstituted signature behind info''.\<close>
    obtain info0'' where rel: "info'' = apply_subst_to_funinfo ?\<sigma>A info0''"
                     and ty1: "FI_TyArgs info0'' = FI_TyArgs info0"
    proof -
      from which show ?thesis
      proof
        assume "info'' = infoA"
        then show ?thesis using that[of info0] infoA_eq by simp
      next
        assume "info'' = post_funinfo infoA"
        then show ?thesis
          using that[of "post_funinfo info0"] infoA_eq
          by (simp add: apply_subst_to_funinfo_post_funinfo)
      qed
    qed
    have ty_n: "FI_TyArgs info'' = FI_TyArgs info0''"
      by (simp add: rel)
    have wf_n: "tyenv_binders_distinct (module_body_env_for ?mid names info'')"
      using mid_bd by simp
    have ok_n: "module_env_subst_ok ?\<sigma>M
                  (module_body_env_for ?envM names (apply_subst_to_funinfo ?\<sigma>M info0''))
                  (module_body_env_for ?mid names info'')"
      using link_mid_body_env_subst_ok[OF linkM m_raw ty_n mid_ok absM ty1 absa absb
                                          freshMid[folded ty1]] .
    have coll: "apply_subst_to_module_env ?\<sigma>M
                  (module_body_env_for ?envM names (apply_subst_to_funinfo ?\<sigma>M info0''))
                  (module_body_env_for ?mid names info'')
                = module_body_env_for ?envM names (apply_subst_to_funinfo ?\<sigma>M info0'')"
      using link_mid_body_env_collapse[OF linkA linkB linkM setMS rel] .
    have tgt_eq: "apply_subst_to_funinfo ?\<sigma>M info0'' = apply_subst_to_funinfo ?\<sigma>M info''"
      by (simp add: rel subst_absorb_funinfo[OF absA])
    show "core_term_type (module_body_env_for ?envM names (apply_subst_to_funinfo ?\<sigma>M info''))
            Ghost (apply_subst_to_term ?\<sigma>M tm) = Some CoreTy_Bool"
      using core_term_type_ghost_bool_subst_module_env[OF typed wf_n ok_n cp_M]
      unfolding coll unfolding tgt_eq .
  qed
  have ctrM: "fun_contracts_well_typed ?envM ?infoM"
    using ctr_sub unfolding infoA_eq subst_absorb_funinfo[OF absA] .

  have "fmlookup (TE_Functions ?envM) name = Some ?infoM \<and>
        length (CF_Args f0) = length (FI_TmArgs ?infoM) \<and>
        distinct (CF_Args f0) \<and>
        (case CF_Body f0 of
           None \<Rightarrow> True
         | Some body0 \<Rightarrow>
             core_statement_list_type
               (module_body_env_for ?envM (CF_Args f0) ?infoM)
               (FI_Ghost ?infoM)
               (apply_subst_to_statement_list ?\<sigma>M body0) \<noteq> None) \<and>
        fun_contracts_well_typed ?envM ?infoM"
    using m_decl len dist0 body_case ctrM by blast
  then show ?thesis by auto
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
  have cpA: "typesubst_complete (CM_TypeSubst a)"
    and cpB: "typesubst_complete (CM_TypeSubst b)"
    using wtA wtB unfolding core_module_well_typed_def by blast+
  have cp: "typesubst_complete ?\<sigma>M"
    using link_modules_typesubst_complete[OF linkA linkB linkM setMS cpA cpB] .
  have cp': "\<forall>ty' \<in> fmran' ?\<sigma>M. is_complete_type ty'"
    using cp unfolding typesubst_complete_def .

  \<comment> \<open>Abstract types coincide with type variables (part of the module-scope
     clause below, and a side condition of the wf substitution engine).\<close>
  have abs_tv: "TE_AbstractTypes ?envM = TE_TypeVars ?envM"
    using link_pair_abs_tv(1)[OF linkA wtA linkB wtB linkM setMS] by simp

  \<comment> \<open>Clause 1: well-formedness, entry by entry through the two mid envs.\<close>
  have wf: "tyenv_well_formed ?envM"
    using link_normalized_env_well_formed[OF linkA wtA linkB wtB linkM setMS] .

  \<comment> \<open>Clause 2: module scope (inert scope fields plus Abs = TV).\<close>
  have scope: "tyenv_module_scope ?envM"
    unfolding tyenv_module_scope_def
    using abs_tv fM(1,9,10,11,3,4,8,18) by auto

  \<comment> \<open>Clause 3: globals. Each defined global comes from one input module,
      hence from one sub-link; route through the matching contribution lemma.\<close>
  have globals: "module_globals_well_typed ?envM (CM_GlobalVars (normalize_module m))"
    unfolding module_globals_well_typed_def
  proof (intro allI impI)
    fix name v
    assume "fmlookup (CM_GlobalVars (normalize_module m)) name = Some v"
    then have m_lk: "fmlookup (CM_GlobalVars m) name = Some v"
      by simp
    have gdisj: "fmdisjoint_list (map CM_GlobalVars ms)"
      using link_modules_success_facts(1)[OF linkM]
      unfolding link_fields_disjoint_def by blast
    have "\<exists>s \<in> set (map CM_GlobalVars ms). fmlookup s name = Some v"
      using m_lk unfolding fM(16) using fmlist_union_lookup[OF gdisj] by blast
    then obtain z where z_in: "z \<in> set ms"
                    and z_lk: "fmlookup (CM_GlobalVars z) name = Some v"
      by auto
    from z_in setMS have "z \<in> set as \<or> z \<in> set bs" by auto
    then show "\<exists>declTy.
        fmlookup (TE_GlobalVars ?envM) name = Some declTy \<and>
        value_has_type ?envM v declTy"
    proof (elim disjE)
      assume zA: "z \<in> set as"
      have adisj: "fmdisjoint_list (map CM_GlobalVars as)"
        using link_modules_success_facts(1)[OF linkA]
        unfolding link_fields_disjoint_def by blast
      have a_lk: "fmlookup (CM_GlobalVars a) name = Some v"
        unfolding link_modules_result_fields(16)[OF linkA]
        using fmlist_union_lookup[OF adisj] zA z_lk by fastforce
      show ?thesis
        using link_mid_globals_contribution[OF linkA wtA linkB wtB linkM setMS a_lk] .
    next
      assume zB: "z \<in> set bs"
      have bdisj: "fmdisjoint_list (map CM_GlobalVars bs)"
        using link_modules_success_facts(1)[OF linkB]
        unfolding link_fields_disjoint_def by blast
      have b_lk: "fmlookup (CM_GlobalVars b) name = Some v"
        unfolding link_modules_result_fields(16)[OF linkB]
        using fmlist_union_lookup[OF bdisj] zB z_lk by fastforce
      show ?thesis
        using link_mid_globals_contribution[OF linkB wtB linkA wtA linkM setMS' b_lk] .
    qed
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
      using m_lk unfolding fM(17) using fmlist_union_lookup[OF fdisj] by blast
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
               (apply_subst_to_statement_list ?\<sigma>M body0) \<noteq> None) \<and>
        fun_contracts_well_typed ?envM info"
    proof (elim disjE)
      assume zA: "z \<in> set as"
      have adisj: "fmdisjoint_list (map CM_Functions as)"
        using link_modules_success_facts(1)[OF linkA]
        unfolding link_fields_disjoint_def by blast
      have a_lk: "fmlookup (CM_Functions a) name = Some f0"
        unfolding link_modules_result_fields(17)[OF linkA]
        using fmlist_union_lookup[OF adisj] zA z_lk by fastforce
      show ?thesis
        using link_mid_functions_contribution[OF linkA wtA linkB wtB linkM setMS a_lk] .
    next
      assume zB: "z \<in> set bs"
      have bdisj: "fmdisjoint_list (map CM_Functions bs)"
        using link_modules_success_facts(1)[OF linkB]
        unfolding link_fields_disjoint_def by blast
      have b_lk: "fmlookup (CM_Functions b) name = Some f0"
        unfolding link_modules_result_fields(17)[OF linkB]
        using fmlist_union_lookup[OF bdisj] zB z_lk by fastforce
      show ?thesis
        using link_mid_functions_contribution[OF linkB wtB linkA wtA linkM setMS' b_lk] .
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
                       (apply_subst_to_statement_list ?\<sigma>M body0) \<noteq> None" and
        i_ctr: "fun_contracts_well_typed ?envM info"
      by auto
    show "\<exists>info.
        fmlookup (TE_Functions ?envM) name = Some info \<and>
        length (CF_Args f) = length (FI_TmArgs info) \<and>
        distinct (CF_Args f) \<and>
        (case CF_Body f of
           None \<Rightarrow> True
         | Some body \<Rightarrow>
             core_statement_list_type
               (module_body_env_for ?envM (CF_Args f) info)
               (FI_Ghost info) body \<noteq> None) \<and>
        fun_contracts_well_typed ?envM info"
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
                   (FI_Ghost info) body \<noteq> None) \<and>
            fun_contracts_well_typed ?envM info"
        unfolding fa fb using i_decl i_len i_dist None i_ctr by simp
      then show ?thesis by auto
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
                   (FI_Ghost info) body \<noteq> None) \<and>
            fun_contracts_well_typed ?envM info"
        unfolding fa fb using i_decl i_len i_dist body' i_ctr by simp
      then show ?thesis by auto
    qed
  qed

  have nwt: "normalized_module_well_typed (normalize_module m)"
    unfolding normalized_module_well_typed_def
    using wf scope globals funcs by blast
  have tvdisj: "fmdom ?\<sigma>M |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}"
    unfolding fM(5) by auto
  have inv: "core_module_invariant m"
    using core_module_invariant_intro[OF idem cap tvdisj nwt] .
  show ?thesis
    unfolding core_module_well_typed_def
    using inv wk cp nwt by blast
qed

end
