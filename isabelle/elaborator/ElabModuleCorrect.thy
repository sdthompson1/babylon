theory ElabModuleCorrect
  imports ElabModule ElabDeclCorrect "../core/LinkCollapse"
begin                          

(* Correctness theorems for elab_module:

   1) elab_module_well_typed:
       If elab_module succeeds, with the input "intDeps" and "implDeps" satisfying the
       relevant invariants (compiled_module_ok, core_module_well_typed after linking,
       elab-env-well-formed), then:
        - the output CoreModules are well-typed after linking (assuming no link error);
        - the interface output satisfies compiled_module_ok and has a well-formed ElabEnv;
        - and various other properties hold (see theorem statement for details).

      Note: compiled_module_ok is defined below; it says (inter alia) that
      core_module_invariant is true, and the CM_TypeSubst is empty.

      This theorem is used in proving the correctness of the pipeline as a whole -- see
      also ElabProgramCorrect.thy, EndToEnd.thy.

   2) elab_module_defs_complete:
       If elab_module succeeds, then the resulting module is closed, in the sense
       that every function or constant declared in the type environment has a
       corresponding definition (either in the interface or implementation, as 
       appropriate).
*)


(* ========================================================================== *)
(* Metavariable-freshness of a module's type-variable names                   *)
(* ========================================================================== *)

(* The tyvar-freshness facts elab_link_well_typed assumes about its context
   module, packaged per-module: every in-scope type variable, and every type
   parameter of every declared function, is metavariable-fresh. The pipeline
   carries this fact for every compiled interface (housekeeping conclusion of
   elab_module_well_typed), and it transfers through linking (below). *)
definition module_tyvars_fresh_ok :: "CoreModule \<Rightarrow> bool" where
  "module_tyvars_fresh_ok m =
    ((\<forall>n. n |\<in>| TE_TypeVars (CM_TyEnv m) \<longrightarrow> tyvar_fresh_ok n 0)
     \<and> (\<forall>name info. fmlookup (TE_Functions (CM_TyEnv m)) name = Some info \<longrightarrow>
          list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)))"

(* Freshness transfers through linking: the linked module's type variables
   and function signatures all come verbatim from some input. *)
lemma link_modules_tyvars_fresh_ok:
  assumes ok: "link_modules ms = Inr L"
      and each: "\<forall>x \<in> set ms. module_tyvars_fresh_ok x"
  shows "module_tyvars_fresh_ok L"
  unfolding module_tyvars_fresh_ok_def
proof (intro conjI allI impI)
  fix n assume "n |\<in>| TE_TypeVars (CM_TyEnv L)"
  then obtain x where "x \<in> set ms" and "n |\<in>| TE_TypeVars (CM_TyEnv x)"
    using link_modules_TypeVars_member[OF ok] by blast
  then show "tyvar_fresh_ok n 0"
    using each unfolding module_tyvars_fresh_ok_def by blast
next
  fix name info
  assume "fmlookup (TE_Functions (CM_TyEnv L)) name = Some info"
  then obtain x where "x \<in> set ms"
      and "fmlookup (TE_Functions (CM_TyEnv x)) name = Some info"
    using link_modules_Functions_lookup[OF ok] by blast
  then show "list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)"
    using each unfolding module_tyvars_fresh_ok_def by blast
qed


(* ========================================================================== *)
(* Fold-invariant exports for elab_declarations                               *)
(* ========================================================================== *)

(* Repackage ElabDeclCorrect's fold-invariant machinery as a fact about
   elab_declarations itself: a successful run from a valid context yields the
   invariant at some final state env. elab_module_well_typed reads several
   per-module conclusions directly off this instance (the structural
   invariant, the substitution-domain bound, well-formedness of the final
   ElabEnv over the state env). *)
lemma elab_declarations_invariant:
  assumes ctx: "elab_context_ok env0 ownAbstract"
      and ee: "elabenv_well_formed env0 elabEnv0"
      and elab: "elab_declarations env0 elabEnv0 ownAbstract decls = Inr (M, elabEnv')"
  obtains envF where "elab_decls_invariant env0 ownAbstract envF elabEnv' M"
proof -
  have fresh: "list_all decl_tyvars_fresh_ok decls"
    using elab_declarations_decls_fresh[OF elab] .
  have init: "elab_decls_invariant env0 ownAbstract env0 elabEnv0 empty_core_module"
    using elab_decls_invariant_init[OF ctx ee] .
  from elab obtain envF where
    run: "elab_declaration_list env0 elabEnv0 ownAbstract empty_core_module decls
            = Inr (envF, elabEnv', M)"
    unfolding elab_declarations_def Let_def
    by (auto split: sum.splits prod.splits if_splits)
  have "elab_decls_invariant env0 ownAbstract envF elabEnv' M"
    using elab_declaration_list_invariant[OF run init fresh] .
  then show thesis using that by blast
qed

(* With no realizable abstract types, elaboration records no realizations:
   the produced module's substitution is empty (its domain is bounded by
   ownAbstract). This is what normalizes an interface CoreModule, as
   elab_link_well_typed's context premise requires of its downstream
   users. *)
lemma elab_decls_invariant_empty_subst:
  assumes inv: "elab_decls_invariant env0 {||} env elabEnv m"
  shows "CM_TypeSubst m = fmempty"
proof -
  have "fmdom (CM_TypeSubst m) |\<subseteq>| {||}"
    using inv unfolding elab_decls_invariant_def by blast
  then have "fmdom (CM_TypeSubst m) = {||}" by simp
  then show ?thesis
    by (metis fmrestrict_fset_dom fmrestrict_fset_null)
qed

(* The produced module inherits metavariable-freshness from the fold: the
   state env's freshness clauses cover the module's own type variables
   (which survive the substitution-domain subtraction - the module's own
   abstract types are never realizable ones) and its function signatures
   (the state env's function table right-biased-includes the module's, and
   apply_subst_to_funinfo preserves FI_TyArgs). *)
lemma elab_decls_invariant_module_fresh:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
  shows "module_tyvars_fresh_ok m"
proof -
  have env_eq: "env = module_context_env env0 m"
   and own_disj: "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}"
   and dom_own: "fmdom (CM_TypeSubst m) |\<subseteq>| ownAbstract"
   and tv_fresh: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n 0"
   and fn_fresh: "\<forall>name info. fmlookup (TE_Functions env) name = Some info \<longrightarrow>
                    list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)"
    using inv unfolding elab_decls_invariant_def by blast+
  have own_disj': "TE_TypeVars (CM_TyEnv m) |\<inter>| ownAbstract = {||}"
    using own_disj by (simp add: inf_commute)
  have tv_dom: "TE_TypeVars (CM_TyEnv m) |\<inter>| fmdom (CM_TypeSubst m) = {||}"
    using empty_inter_subset[OF own_disj' dom_own] .
  show ?thesis
    unfolding module_tyvars_fresh_ok_def
  proof (intro conjI allI impI)
    fix n assume n_in: "n |\<in>| TE_TypeVars (CM_TyEnv m)"
    have n_notin: "n |\<notin>| fmdom (CM_TypeSubst m)"
    proof
      assume "n |\<in>| fmdom (CM_TypeSubst m)"
      then have "n |\<in>| TE_TypeVars (CM_TyEnv m) |\<inter>| fmdom (CM_TypeSubst m)"
        using n_in by simp
      then show False using tv_dom by simp
    qed
    have "n |\<in>| TE_TypeVars env"
      unfolding env_eq module_context_env_tyvar_fields(1)
      using n_in n_notin by simp
    then show "tyvar_fresh_ok n 0" using tv_fresh by blast
  next
    fix name info
    assume lk: "fmlookup (TE_Functions (CM_TyEnv m)) name = Some info"
    have lk_env: "fmlookup (TE_Functions env) name
                    = Some (apply_subst_to_funinfo (CM_TypeSubst m) info)"
      unfolding env_eq module_context_env_def apply_subst_to_tyenv_def
      using lk by auto
    then have "list_all (\<lambda>n. tyvar_fresh_ok n 0)
                 (FI_TyArgs (apply_subst_to_funinfo (CM_TypeSubst m) info))"
      using fn_fresh by blast
    then show "list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)"
      by simp
  qed
qed


(* ========================================================================== *)
(* Well-formedness of ElabEnv combination                                     *)
(* ========================================================================== *)

(* elabenv_well_formed is monotone in the env, for an ElabEnv whose
   per-function scratch flag is clear: growing the type variables and the
   datatype/constructor tables (preserving existing entries) can only widen
   what is well-kinded. This is how a dep's exported delta, well-formed over
   the dep's own linked context, transfers to the larger linked context of a
   downstream module. *)
lemma elabenv_well_formed_mono:
  assumes wf: "elabenv_well_formed env1 ee"
      and tv: "TE_TypeVars env1 |\<subseteq>| TE_TypeVars env2"
      and dt: "\<And>n v. fmlookup (TE_Datatypes env1) n = Some v
                 \<Longrightarrow> fmlookup (TE_Datatypes env2) n = Some v"
      and dc: "\<And>n v. fmlookup (TE_DataCtors env1) n = Some v
                 \<Longrightarrow> fmlookup (TE_DataCtors env2) n = Some v"
      and fn: "\<And>n v. fmlookup (TE_Functions env1) n = Some v
                 \<Longrightarrow> fmlookup (TE_Functions env2) n = Some v"
      and nv: "\<not> EE_CurrentFunctionVoid ee"
  shows "elabenv_well_formed env2 ee"
proof -
  have td: "typedefs_well_formed env2 (EE_Typedefs ee)"
    unfolding typedefs_well_formed_def
  proof (intro allI impI)
    fix name tyvars targetTy
    assume lk: "fmlookup (EE_Typedefs ee) name = Some (tyvars, targetTy)"
    have d: "distinct tyvars"
     and wk1: "is_well_kinded
                 (env1 \<lparr> TE_TypeVars := TE_TypeVars env1 |\<union>| fset_of_list tyvars \<rparr>)
                 targetTy"
      using wf lk
      unfolding elabenv_well_formed_def typedefs_well_formed_def by blast+
    have wk2: "is_well_kinded
                 (env2 \<lparr> TE_TypeVars := TE_TypeVars env2 |\<union>| fset_of_list tyvars \<rparr>)
                 targetTy"
    proof (rule is_well_kinded_mono[OF wk1])
      have "TE_TypeVars env1 |\<union>| fset_of_list tyvars
              |\<subseteq>| TE_TypeVars env2 |\<union>| fset_of_list tyvars"
        using tv by (metis order_refl sup.mono)
      then show
        "fset (TE_TypeVars (env1 \<lparr> TE_TypeVars := TE_TypeVars env1 |\<union>| fset_of_list tyvars \<rparr>))
           \<subseteq> fset (TE_TypeVars (env2 \<lparr> TE_TypeVars := TE_TypeVars env2 |\<union>| fset_of_list tyvars \<rparr>))"
        by (simp add: less_eq_fset.rep_eq)
    next
      fix n v
      assume "fmlookup (TE_Datatypes
                (env1 \<lparr> TE_TypeVars := TE_TypeVars env1 |\<union>| fset_of_list tyvars \<rparr>)) n
                = Some v"
      then have l1: "fmlookup (TE_Datatypes env1) n = Some v" by simp
      have "fmlookup (TE_Datatypes env2) n = Some v" using dt[OF l1] .
      then show "fmlookup (TE_Datatypes
                   (env2 \<lparr> TE_TypeVars := TE_TypeVars env2 |\<union>| fset_of_list tyvars \<rparr>)) n
                   = Some v"
        by simp
    qed
    show "distinct tyvars \<and>
          is_well_kinded
            (env2 \<lparr> TE_TypeVars := TE_TypeVars env2 |\<union>| fset_of_list tyvars \<rparr>)
            targetTy"
      using d wk2 by blast
  qed
  have nc: "nullary_data_ctors_consistent env2 ee"
    unfolding nullary_data_ctors_consistent_def
  proof (intro allI impI)
    fix name assume "name |\<in>| EE_NullaryDataCtors ee"
    then obtain dtName tyvars where
      "fmlookup (TE_DataCtors env1) name = Some (dtName, tyvars, CoreTy_Record [])"
      using wf
      unfolding elabenv_well_formed_def nullary_data_ctors_consistent_def by blast
    then show "\<exists>dtName tyvars.
                 fmlookup (TE_DataCtors env2) name = Some (dtName, tyvars, CoreTy_Record [])"
      using dc by blast
  qed
  have gc: "ghost_constants_consistent env2 ee"
    unfolding ghost_constants_consistent_def
  proof (intro allI impI)
    fix name assume "name |\<in>| EE_GhostConstants ee"
    then obtain retTy where
      "fmlookup (TE_Functions env1) name =
         Some \<lparr> FI_TyArgs = [], FI_TmArgs = [], FI_ReturnType = retTy,
                FI_Ghost = Ghost, FI_Impure = False \<rparr>"
      using wf
      unfolding elabenv_well_formed_def ghost_constants_consistent_def by blast
    then show "\<exists>retTy. fmlookup (TE_Functions env2) name =
                 Some \<lparr> FI_TyArgs = [], FI_TmArgs = [], FI_ReturnType = retTy,
                        FI_Ghost = Ghost, FI_Impure = False \<rparr>"
      using fn by blast
  qed
  show ?thesis
    unfolding elabenv_well_formed_def
    using td nc gc nv by blast
qed

(* A union of well-formed ElabEnv deltas is well-formed (over the same env):
   every entry of the union is an entry of SOME part, even without domain
   disjointness (fmlist_union_lookup_some) - which entry wins an overlap is
   order-sensitive, but every candidate is well-formed. So well-formedness
   needs no disjointness premise; disjointness matters only for the
   elaboration semantics (deterministic entries), which the pipeline gets
   from global name uniqueness. *)
lemma elabenv_union_well_formed:
  assumes each: "\<forall>e \<in> set es. elabenv_well_formed env e"
  shows "elabenv_well_formed env (elabenv_union es)"
proof -
  have td: "typedefs_well_formed env (EE_Typedefs (elabenv_union es))"
    unfolding typedefs_well_formed_def
  proof (intro allI impI)
    fix name tyvars targetTy
    assume "fmlookup (EE_Typedefs (elabenv_union es)) name = Some (tyvars, targetTy)"
    then have "fmlookup (fmlist_union (map EE_Typedefs es)) name = Some (tyvars, targetTy)"
      by simp
    then obtain e where e_in: "e \<in> set es"
        and e_lk: "fmlookup (EE_Typedefs e) name = Some (tyvars, targetTy)"
      using fmlist_union_lookup_some by fastforce
    show "distinct tyvars \<and>
          is_well_kinded
            (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list tyvars \<rparr>)
            targetTy"
      using each e_in e_lk
      unfolding elabenv_well_formed_def typedefs_well_formed_def by blast
  qed
  have nc: "nullary_data_ctors_consistent env (elabenv_union es)"
    unfolding nullary_data_ctors_consistent_def
  proof (intro allI impI)
    fix name assume "name |\<in>| EE_NullaryDataCtors (elabenv_union es)"
    then have "name |\<in>| funion_list (map EE_NullaryDataCtors es)"
      by simp
    then obtain e where e_in: "e \<in> set es"
        and e_mem: "name |\<in>| EE_NullaryDataCtors e"
      by (auto simp: funion_list_member)
    then show "\<exists>dtName tyvars.
                 fmlookup (TE_DataCtors env) name = Some (dtName, tyvars, CoreTy_Record [])"
      using each
      unfolding elabenv_well_formed_def nullary_data_ctors_consistent_def by blast
  qed
  have gc: "ghost_constants_consistent env (elabenv_union es)"
    unfolding ghost_constants_consistent_def
  proof (intro allI impI)
    fix name assume "name |\<in>| EE_GhostConstants (elabenv_union es)"
    then have "name |\<in>| funion_list (map EE_GhostConstants es)"
      by simp
    then obtain e where e_in: "e \<in> set es"
        and e_mem: "name |\<in>| EE_GhostConstants e"
      by (auto simp: funion_list_member)
    then show "\<exists>retTy. fmlookup (TE_Functions env) name =
                 Some \<lparr> FI_TyArgs = [], FI_TmArgs = [], FI_ReturnType = retTy,
                        FI_Ghost = Ghost, FI_Impure = False \<rparr>"
      using each
      unfolding elabenv_well_formed_def ghost_constants_consistent_def by blast
  qed
  show ?thesis
    unfolding elabenv_well_formed_def
    using td nc gc by simp
qed

(* A delta of a well-formed ElabEnv is well-formed (over the same env): the
   delta's entries are a subset of the final env's, and the scratch flag is
   cleared. *)
lemma elabenv_delta_well_formed:
  assumes wf: "elabenv_well_formed env final"
  shows "elabenv_well_formed env (elabenv_delta initial final)"
proof -
  have td: "typedefs_well_formed env (EE_Typedefs (elabenv_delta initial final))"
    unfolding typedefs_well_formed_def
  proof (intro allI impI)
    fix name tyvars targetTy
    assume "fmlookup (EE_Typedefs (elabenv_delta initial final)) name
              = Some (tyvars, targetTy)"
    then have "fmlookup (EE_Typedefs final) name = Some (tyvars, targetTy)"
      by (auto split: if_splits)
    then show "distinct tyvars \<and>
               is_well_kinded
                 (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list tyvars \<rparr>)
                 targetTy"
      using wf unfolding elabenv_well_formed_def typedefs_well_formed_def by blast
  qed
  have nc: "nullary_data_ctors_consistent env (elabenv_delta initial final)"
    unfolding nullary_data_ctors_consistent_def
  proof (intro allI impI)
    fix name assume "name |\<in>| EE_NullaryDataCtors (elabenv_delta initial final)"
    then have "name |\<in>| EE_NullaryDataCtors final"
      by auto
    then show "\<exists>dtName tyvars.
                 fmlookup (TE_DataCtors env) name = Some (dtName, tyvars, CoreTy_Record [])"
      using wf
      unfolding elabenv_well_formed_def nullary_data_ctors_consistent_def by blast
  qed
  have gc: "ghost_constants_consistent env (elabenv_delta initial final)"
    unfolding ghost_constants_consistent_def
  proof (intro allI impI)
    fix name assume "name |\<in>| EE_GhostConstants (elabenv_delta initial final)"
    then have "name |\<in>| EE_GhostConstants final"
      by auto
    then show "\<exists>retTy. fmlookup (TE_Functions env) name =
                 Some \<lparr> FI_TyArgs = [], FI_TmArgs = [], FI_ReturnType = retTy,
                        FI_Ghost = Ghost, FI_Impure = False \<rparr>"
      using wf
      unfolding elabenv_well_formed_def ghost_constants_consistent_def by blast
  qed
  show ?thesis
    unfolding elabenv_well_formed_def
    using td nc gc by simp
qed

(* A delta's typedef domain avoids its initial env's: the restriction removes
   exactly that domain. With the initial env the union of the imports'
   deltas, this is what makes the face's own delta disjoint from every
   import's - the disjointness elabenv_union_well_formed needs downstream. *)
lemma elabenv_delta_typedefs_disjoint:
  "fmdom (EE_Typedefs (elabenv_delta initial final))
     |\<inter>| fmdom (EE_Typedefs initial) = {||}"
proof (rule fset_eqI)
  fix x
  show "x |\<in>| fmdom (EE_Typedefs (elabenv_delta initial final))
              |\<inter>| fmdom (EE_Typedefs initial)
          \<longleftrightarrow> x |\<in>| {||}"
    by auto
qed

(* ElabEnv well-formedness transfers from a sub-link's env to the whole
   link's, for substitution-free inputs: the type variables embed
   (link_modules_TypeVars_mono) and the declaration tables are submaps
   (link_modules_decl_submaps). *)
lemma elabenv_well_formed_link_mono:
  assumes okA: "link_modules as = Inr a"
      and okM: "link_modules ms = Inr m"
      and empty: "\<forall>x \<in> set ms. CM_TypeSubst x = fmempty"
      and sub: "set as \<subseteq> set ms"
      and wf: "elabenv_well_formed (CM_TyEnv a) ee"
      and nv: "\<not> EE_CurrentFunctionVoid ee"
  shows "elabenv_well_formed (CM_TyEnv m) ee"
proof (rule elabenv_well_formed_mono[OF wf _ _ _ _ nv])
  show "TE_TypeVars (CM_TyEnv a) |\<subseteq>| TE_TypeVars (CM_TyEnv m)"
    using link_modules_TypeVars_mono[OF okA okM empty sub] .
next
  fix n v assume "fmlookup (TE_Datatypes (CM_TyEnv a)) n = Some v"
  then show "fmlookup (TE_Datatypes (CM_TyEnv m)) n = Some v"
    using link_modules_decl_submaps(3)[OF okA okM sub] by blast
next
  fix n v assume "fmlookup (TE_DataCtors (CM_TyEnv a)) n = Some v"
  then show "fmlookup (TE_DataCtors (CM_TyEnv m)) n = Some v"
    using link_modules_decl_submaps(4)[OF okA okM sub] by blast
next
  fix n v assume "fmlookup (TE_Functions (CM_TyEnv a)) n = Some v"
  then show "fmlookup (TE_Functions (CM_TyEnv m)) n = Some v"
    using link_modules_decl_submaps(2)[OF okA okM sub] by blast
qed


(* ========================================================================== *)
(* The compiled-module contract                                               *)
(* ========================================================================== *)

(* The housekeeping facts the pipeline carries for every compiled interface,
   bundled per CompiledModule: the CoreModule satisfies the standing
   structural invariant, is substitution-free (an interface realizes
   nothing), and has metavariable-fresh type-variable names; the ElabEnv
   delta's per-function scratch flag is clear. These are premises of
   elab_module_well_typed about each dep, and its housekeeping conclusion
   about the interface face it produces - the loop the pipeline fold
   closes. *)
definition compiled_module_ok :: "CompiledModule \<Rightarrow> bool" where
  "compiled_module_ok cm =
    (core_module_invariant (fst cm)
     \<and> CM_TypeSubst (fst cm) = fmempty
     \<and> module_tyvars_fresh_ok (fst cm)
     \<and> \<not> EE_CurrentFunctionVoid (snd cm))"


(* ========================================================================== *)
(* The merged substitution of a single-realizer input list                    *)
(* ========================================================================== *)

(* When every input but the last is substitution-free, the raw union of the
   substitutions is the last one's alone... *)
lemma fmlist_union_empties:
  assumes "\<forall>s \<in> set ss. s = fmempty"
  shows "fmlist_union ss = fmempty"
  using assms by (induction ss) (simp_all add: fmlist_union_Cons)

(* ...so a successful merge returns exactly that substitution: merge success
   makes it the idempotent closure of the raw union (merge_all_substs_Inr_iff),
   an idempotent substitution is its own closure, and closures are unique.
   This pins down the merged substitution of the pipeline's derived
   implementation link (dep interfaces + own interface + own implementation):
   it is CM_TypeSubst implMod itself. *)
lemma merge_substs_empties_snoc:
  assumes merge: "merge_all_substs (map CM_TypeSubst (ms @ [m])) = Inr \<sigma>"
      and empties: "\<forall>x \<in> set ms. CM_TypeSubst x = fmempty"
      and idem: "idempotent_subst (CM_TypeSubst m)"
  shows "\<sigma> = CM_TypeSubst m"
proof -
  have u_prefix: "fmlist_union (map CM_TypeSubst ms) = fmempty"
    by (rule fmlist_union_empties) (use empties in auto)
  have u_eq: "fmlist_union (map CM_TypeSubst (ms @ [m])) = CM_TypeSubst m"
    by (simp add: fmlist_union_append u_prefix)
  have "acyclic_subst_deps (fmlist_union (map CM_TypeSubst (ms @ [m])))
        \<and> is_subst_closure (fmlist_union (map CM_TypeSubst (ms @ [m]))) \<sigma>"
    using merge merge_all_substs_Inr_iff by blast
  then have acyc: "acyclic_subst_deps (CM_TypeSubst m)"
        and clos: "is_subst_closure (CM_TypeSubst m) \<sigma>"
    unfolding u_eq by blast+
  show ?thesis
    using subst_closure_unique[OF acyc clos is_subst_closure_self[OF idem]] .
qed

(* The snoc form of a mapped funion_list, for splitting the last input off the
   per-field unions of link_result. *)
lemma funion_list_map_snoc:
  "funion_list (map f (xs @ [x])) = funion_list (map f xs) |\<union>| f x"
  by (rule fset_eqI) (auto simp: funion_list_member)

lemma funion_list_map_empty:
  assumes "\<forall>x \<in> set xs. f x = {||}"
  shows "funion_list (map f xs) = {||}"
  by (rule fset_eqI) (use assms in \<open>auto simp: funion_list_member\<close>)


(* ========================================================================== *)
(* Per-module completeness, in env terms                                      *)
(* ========================================================================== *)

(* A clean check_completeness certifies that every abstract typedef of the
   interface is realized by the implementation. Together with the provenance
   fold lemma (elab_declarations_own_tyvars: every TE_TypeVars entry of a
   produced module names an abstract typedef of its input list), this yields
   the env-level statement the whole-program composition needs: the
   interface's type variables lie within the implementation's substitution
   domain - a prefix of whole modules realizes everything it declares, which
   is what grounds its merged substitution (link_modules_sublink_ground). *)
lemma check_completeness_abstract_realized:
  assumes ok: "check_completeness intf intMod implMod = []"
  shows "decls_abstract_names intf |\<subseteq>| fmdom (CM_TypeSubst implMod)"
proof
  fix n assume "n |\<in>| decls_abstract_names intf"
  then obtain d where d_in: "d \<in> set intf" and n_d: "n |\<in>| decl_abstract_names d"
    unfolding decls_abstract_names_def by (auto simp: funion_list_member)
  from n_d obtain dt where d_eq: "d = BabDecl_Typedef dt"
      and abs: "DT_Definition dt = None"
      and n_eq: "n = DT_Name dt"
    by (cases d) (auto split: if_splits)
  have all_nil: "\<forall>d \<in> set intf.
     (case d of
        BabDecl_Const dc \<Rightarrow>
          (if DC_Value dc = None
              \<and> (if DC_Ghost dc = Ghost
                 then DC_Name dc |\<notin>| fmdom (CM_Functions intMod)
                      \<and> DC_Name dc |\<notin>| fmdom (CM_Functions implMod)
                 else DC_Name dc |\<notin>| fmdom (CM_GlobalVars intMod)
                      \<and> DC_Name dc |\<notin>| fmdom (CM_GlobalVars implMod))
           then [TyErr_DeclaredButNotDefined (DC_Location dc) (DC_Name dc)]
           else [])
      | BabDecl_Function df \<Rightarrow>
          (if DF_Body df = None \<and> \<not> DF_Extern df
              \<and> DF_Name df |\<notin>| fmdom (CM_Functions intMod)
              \<and> DF_Name df |\<notin>| fmdom (CM_Functions implMod)
           then [TyErr_DeclaredButNotDefined (DF_Location df) (DF_Name df)]
           else [])
      | BabDecl_Datatype dd \<Rightarrow> []
      | BabDecl_Typedef dt \<Rightarrow>
          (if DT_Definition dt = None
              \<and> DT_Name dt |\<notin>| fmdom (CM_TypeSubst implMod)
           then [TyErr_AbstractTypeNotRealized (DT_Location dt) (DT_Name dt)]
           else [])) = []"
    using ok unfolding check_completeness_def by simp
  from bspec[OF all_nil d_in] show "n |\<in>| fmdom (CM_TypeSubst implMod)"
    unfolding d_eq using abs n_eq by (auto split: if_splits)
qed


(* ========================================================================== *)
(* Unpacking a successful elab_module run                                     *)
(* ========================================================================== *)

(* The elimination rule for elab_face success: names the link context, the
   sorted declaration list and the fold result, and states the defining
   equation of the returned ElabEnv delta. *)
lemma elab_face_Inr_elim:
  assumes ok: "elab_face deps ownAbstract decls = Inr (m, ee)"
  obtains ctx sortedDecls foldEnv where
    "link_modules (map fst deps) = Inr ctx"
    "sort_declarations (CM_TyEnv ctx) (elabenv_union (map snd deps)) decls
       = Inr sortedDecls"
    "elab_declarations (CM_TyEnv ctx) (elabenv_union (map snd deps))
       ownAbstract sortedDecls = Inr (m, foldEnv)"
    "ee = elabenv_delta (elabenv_union (map snd deps)) foldEnv"
  using ok unfolding elab_face_def Let_def
  by (auto split: sum.splits prod.splits)

(* The elimination rule for elab_module success: names every intermediate
   object of the orchestration (the two link contexts, the sorted
   declaration lists, the two fold results), states the defining equation of
   each returned ElabEnv delta, and records the syntactic gates that must
   have passed (no declaration-only forms in the implementation; per-module
   completeness). *)
lemma elab_module_Inr_elim:
  assumes ok: "elab_module bm intDeps implDeps = Inr ((intMod, intEE), (implMod, implEE))"
  obtains a b sortedInt intFoldEnv sortedImpl implFoldEnv where
    "check_impl_definitions (Mod_Implementation bm) = []"
    "check_completeness (Mod_Interface bm) intMod implMod = []"
    "link_modules (map fst intDeps) = Inr a"
    "sort_declarations (CM_TyEnv a) (elabenv_union (map snd intDeps)) (Mod_Interface bm)
       = Inr sortedInt"
    "elab_declarations (CM_TyEnv a) (elabenv_union (map snd intDeps)) {||} sortedInt
       = Inr (intMod, intFoldEnv)"
    "intEE = elabenv_delta (elabenv_union (map snd intDeps)) intFoldEnv"
    "link_modules (map fst intDeps @ map fst implDeps @ [intMod]) = Inr b"
    "sort_declarations (CM_TyEnv b)
       (elabenv_union (map snd intDeps @ map snd implDeps @ [intEE]))
       (Mod_Implementation bm) = Inr sortedImpl"
    "elab_declarations (CM_TyEnv b)
       (elabenv_union (map snd intDeps @ map snd implDeps @ [intEE]))
       (TE_TypeVars (CM_TyEnv intMod)) sortedImpl = Inr (implMod, implFoldEnv)"
    "implEE = elabenv_delta
       (elabenv_union (map snd intDeps @ map snd implDeps @ [intEE])) implFoldEnv"
  using ok unfolding elab_module_def elab_face_def Let_def
  by (auto split: if_splits sum.splits prod.splits)


(* ========================================================================== *)
(* The main theorem                                                           *)
(* ========================================================================== *)

(* Correctness of elab_module: the statement the pipeline consumes, one
   packaged fact per module, so the pipeline fold never re-opens elaborator
   internals.

   Premises are facts the fold invariant can supply about the two compiled
   dependency lists: the per-dep housekeeping contract (compiled_module_ok);
   well-typedness of the two flat dep-only links (conditional - though given
   elab_module's success both fire, the pipeline discharges them by composing
   the deps' conclusion-(i) facts via link_preserves_well_typed, which is
   also why they are irreducible here: a sub-link of a well-typed link need
   not be well-typed, so neither follows from the other); and well-formedness
   of each dep's ElabEnv delta over those links' envs (from the deps'
   conclusion-(iii) facts plus elabenv_well_formed_link_mono).
   Metavariable-freshness of the declaration binders needs no premise:
   elab_declarations checks it at runtime, so it follows from elab_module's
   success (elab_declarations_decls_fresh).

   Conclusions (i)-(iii) are about links elab_module does NOT itself compute
   and which may fail, hence conditional: (i) the derived linked interface is
   well-typed; (ii) the derived linked implementation - the whole-program
   feeder - is well-typed; (iii) the interface face's exported ElabEnv delta
   is well-formed over the linked interface's env; (iv) the housekeeping
   contract holds of the interface face, closing the pipeline's loop; (v) the
   implementation face satisfies the structural invariant and only realizes
   the module's own interface's abstract types - what the whole-program
   composition (step 8) needs about implementations, which compiled_module_ok
   cannot state (an implementation's substitution is NOT empty in general: a
   realization lives there); (vi) the runtime-resolution gate (link_runtime_ok)
   of the derived linked implementation holds for ANY successfully merged
   substitution of that input list. The pipeline needs conclusion (ii)'s link
   to SUCCEED, not merely to be well-typed if it does; of link_modules' four
   checks, the runtime gate is the only one that does not restrict from the
   (successful) whole-program link to a sub-multiset, so it is exactly the
   hypothesis link_modules_sublink leaves with the caller - and the input list
   here is NOT realization-closed (dep implementations are absent), putting it
   outside link_modules_sublink_ground. (vi) discharges the gate from the
   elaborator's own realization-site checks, carried through the fold by
   subst_runtime_ok. It is conditional on merge success alone, which the
   pipeline inherits from the whole-program link via merge_all_substs_sublist.

   Conclusions (vii)-(ix) feed the OTHER sublink obligation of step 8: the
   growing prefixes of the whole-program link go through
   link_modules_sublink_ground, whose groundedness hypothesis - the merged
   substitution's targets mention no unrealized names - the pipeline
   assembles from per-module facts: (vii) every abstract type of the
   interface is realized by the implementation (check_completeness, carried
   to env level by the provenance fold lemma); (viii) an implementation
   declares no abstract types of its own (declaration-only forms were
   rejected); (ix) the realization targets' type variables all lie among the
   in-scope abstract types of the implementation's linked context (the
   invariant's range well-kindedness). (Nothing is concluded about implEE -
   it has no consumer.)

   Note there is NO disjointness premise on the two dep lists: an overlap
   would put the same module twice into the face-2 link, where the strict
   conflict check fails it, contradicting the elab_module success. *)
theorem elab_module_well_typed:
  assumes elab: "elab_module bm intDeps implDeps
                   = Inr ((intMod, intEE), (implMod, implEE))"
      and deps_ok: "\<forall>d \<in> set (intDeps @ implDeps). compiled_module_ok d"
      and A_wt: "\<And>a. link_modules (map fst intDeps) = Inr a
                   \<Longrightarrow> core_module_well_typed a"
      and C_wt: "\<And>c. link_modules (map fst intDeps @ map fst implDeps) = Inr c
                   \<Longrightarrow> core_module_well_typed c"
      and eeA: "\<And>a. link_modules (map fst intDeps) = Inr a
                  \<Longrightarrow> \<forall>d \<in> set intDeps. elabenv_well_formed (CM_TyEnv a) (snd d)"
      and eeC: "\<And>c. link_modules (map fst intDeps @ map fst implDeps) = Inr c
                  \<Longrightarrow> \<forall>d \<in> set (intDeps @ implDeps).
                        elabenv_well_formed (CM_TyEnv c) (snd d)"
  shows "link_modules (map fst intDeps @ [intMod]) = Inr L
           \<Longrightarrow> core_module_well_typed L"                                     \<comment> \<open>(i)\<close>
    and "link_modules (map fst intDeps @ map fst implDeps @ [intMod, implMod]) = Inr P
           \<Longrightarrow> core_module_well_typed P"                                     \<comment> \<open>(ii)\<close>
    and "link_modules (map fst intDeps @ [intMod]) = Inr L
           \<Longrightarrow> elabenv_well_formed (CM_TyEnv L) intEE"                       \<comment> \<open>(iii)\<close>
    and "compiled_module_ok (intMod, intEE)"                                 \<comment> \<open>(iv)\<close>
    and "core_module_invariant implMod
           \<and> fmdom (CM_TypeSubst implMod) |\<subseteq>| TE_TypeVars (CM_TyEnv intMod)" \<comment> \<open>(v)\<close>
    and "merge_all_substs (map CM_TypeSubst
           (map fst intDeps @ map fst implDeps @ [intMod, implMod])) = Inr \<sigma>
           \<Longrightarrow> link_runtime_ok
                 (map fst intDeps @ map fst implDeps @ [intMod, implMod]) \<sigma>"  \<comment> \<open>(vi)\<close>
    and "TE_TypeVars (CM_TyEnv intMod) |\<subseteq>| fmdom (CM_TypeSubst implMod)"     \<comment> \<open>(vii)\<close>
    and "TE_TypeVars (CM_TyEnv implMod) = {||}"                               \<comment> \<open>(viii)\<close>
    and "subst_range_tyvars (CM_TypeSubst implMod)
           \<subseteq> fset (funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x))
                      (map fst intDeps @ map fst implDeps @ [intMod])))"      \<comment> \<open>(ix)\<close>
proof -
  \<comment> \<open>Unpack the orchestration.\<close>
  obtain a b sortedInt intFoldEnv sortedImpl implFoldEnv where
    implDefs: "check_impl_definitions (Mod_Implementation bm) = []" and
    complete: "check_completeness (Mod_Interface bm) intMod implMod = []" and
    linkA: "link_modules (map fst intDeps) = Inr a" and
    sortInt: "sort_declarations (CM_TyEnv a) (elabenv_union (map snd intDeps))
                (Mod_Interface bm) = Inr sortedInt" and
    elabInt: "elab_declarations (CM_TyEnv a) (elabenv_union (map snd intDeps))
                {||} sortedInt = Inr (intMod, intFoldEnv)" and
    intEE_eq: "intEE = elabenv_delta (elabenv_union (map snd intDeps)) intFoldEnv" and
    linkB: "link_modules (map fst intDeps @ map fst implDeps @ [intMod]) = Inr b" and
    sortImpl: "sort_declarations (CM_TyEnv b)
                 (elabenv_union (map snd intDeps @ map snd implDeps @ [intEE]))
                 (Mod_Implementation bm) = Inr sortedImpl" and
    elabImpl: "elab_declarations (CM_TyEnv b)
                 (elabenv_union (map snd intDeps @ map snd implDeps @ [intEE]))
                 (TE_TypeVars (CM_TyEnv intMod)) sortedImpl
                 = Inr (implMod, implFoldEnv)" and
    implEE_eq: "implEE = elabenv_delta
                  (elabenv_union (map snd intDeps @ map snd implDeps @ [intEE]))
                  implFoldEnv"
    using elab by (rule elab_module_Inr_elim)

  \<comment> \<open>The per-dep contract, projected.\<close>
  have deps_inv: "\<forall>x \<in> set (map fst intDeps @ map fst implDeps). core_module_invariant x"
   and deps_subst: "\<forall>x \<in> set (map fst intDeps @ map fst implDeps). CM_TypeSubst x = fmempty"
   and deps_fresh: "\<forall>x \<in> set (map fst intDeps @ map fst implDeps). module_tyvars_fresh_ok x"
    using deps_ok unfolding compiled_module_ok_def by auto

  \<comment> \<open>Face 1's context: the dep-only link a, well-typed and substitution-free,
     with a well-formed ElabEnv union and metavariable-fresh names.\<close>
  have a_wt: "core_module_well_typed a"
    using A_wt[OF linkA] .
  have a_subst: "CM_TypeSubst a = fmempty"
    using link_modules_empty_subst[OF linkA] deps_subst by auto
  have ea_wf: "elabenv_well_formed (CM_TyEnv a) (elabenv_union (map snd intDeps))"
  proof (rule elabenv_union_well_formed)
    show "\<forall>e \<in> set (map snd intDeps). elabenv_well_formed (CM_TyEnv a) e"
      using eeA[OF linkA] by auto
  qed
  have a_fresh: "module_tyvars_fresh_ok a"
    using link_modules_tyvars_fresh_ok[OF linkA] deps_fresh by auto
  have ctx_freshA: "\<forall>n. n |\<in>| TE_TypeVars (CM_TyEnv a) \<longrightarrow> tyvar_fresh_ok n 0"
   and fun_freshA: "\<forall>name info.
                      fmlookup (TE_Functions (CM_TyEnv a)) name = Some info \<longrightarrow>
                      list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)"
    using a_fresh unfolding module_tyvars_fresh_ok_def by blast+
  have own0: "{||} |\<subseteq>| TE_TypeVars (CM_TyEnv a)"
    by auto

  \<comment> \<open>Face 1's fold invariant, and the housekeeping facts read off it.\<close>
  have a_nwt: "normalized_module_well_typed a"
    using core_module_well_typed_on_normalized[OF a_subst] a_wt by blast
  have ctxA: "elab_context_ok (CM_TyEnv a) {||}"
    using a_nwt own0 ctx_freshA fun_freshA
    unfolding elab_context_ok_def normalized_module_well_typed_def by blast
  obtain envF where invF: "elab_decls_invariant (CM_TyEnv a) {||} envF intFoldEnv intMod"
    using ctxA ea_wf elabInt by (rule elab_declarations_invariant)
  have intMod_subst: "CM_TypeSubst intMod = fmempty"
    using elab_decls_invariant_empty_subst[OF invF] .
  have intMod_inv: "core_module_invariant intMod"
    using invF unfolding elab_decls_invariant_def by blast
  have intMod_fresh: "module_tyvars_fresh_ok intMod"
    using elab_decls_invariant_module_fresh[OF invF] .
  have intEE_nv: "\<not> EE_CurrentFunctionVoid intEE"
    unfolding intEE_eq by simp

  \<comment> \<open>Conclusion (iv).\<close>
  have concl_iv: "compiled_module_ok (intMod, intEE)"
    unfolding compiled_module_ok_def
    using intMod_inv intMod_subst intMod_fresh intEE_nv by simp

  \<comment> \<open>Conclusion (i): collapse the flat linked interface to the pair link
     of elab_link_well_typed.\<close>
  have concl_i: "core_module_well_typed L"
    if linkL: "link_modules (map fst intDeps @ [intMod]) = Inr L" for L
  proof -
    have pair: "link_modules [a, intMod] = Inr L"
      using link_modules_collapse[OF linkA linkL] .
    show ?thesis
      using elab_link_well_typed[OF a_wt a_subst ea_wf own0 ctx_freshA fun_freshA
              elabInt pair] .
  qed

  \<comment> \<open>Conclusion (iii): the fold's final state env IS the linked interface's
     env - the pair link's normalized env by the invariant's pivot equation,
     and normalization is the identity here (every input is
     substitution-free).\<close>
  have concl_iii: "elabenv_well_formed (CM_TyEnv L) intEE"
    if linkL: "link_modules (map fst intDeps @ [intMod]) = Inr L" for L
  proof -
    have pair: "link_modules [a, intMod] = Inr L"
      using link_modules_collapse[OF linkA linkL] .
    have wf_F: "elabenv_well_formed envF intFoldEnv"
      using invF unfolding elab_decls_invariant_def by blast
    have wf_delta: "elabenv_well_formed envF intEE"
      unfolding intEE_eq using elabenv_delta_well_formed[OF wf_F] .
    have envF_eq: "envF = module_context_env (CM_TyEnv a) intMod"
      using invF unfolding elab_decls_invariant_def by blast
    have idemI: "idempotent_subst (CM_TypeSubst intMod)"
      using intMod_subst by simp
    have scopeA: "tyenv_module_scope (CM_TyEnv a)"
      using a_nwt unfolding normalized_module_well_typed_def by blast
    have norm_env: "CM_TyEnv (normalize_module L) = module_context_env (CM_TyEnv a) intMod"
      using module_context_env_link_pair[OF pair a_subst idemI scopeA] .
    have L_subst: "CM_TypeSubst L = fmempty"
      using link_modules_empty_subst[OF linkL] deps_subst intMod_subst by auto
    have env_L: "CM_TyEnv L = envF"
      using norm_env normalize_module_id_when_empty[OF L_subst] envF_eq by simp
    show ?thesis
      using wf_delta env_L by simp
  qed

  \<comment> \<open>Face 2's context: everything b links is substitution-free, so its
     sub-links (the linked interface li and the two-list dep link c) succeed
     unconditionally - only conclusion (ii)'s final collapse depends on the
     conditional link P.\<close>
  have b_inputs_subst: "\<forall>x \<in> set (map fst intDeps @ map fst implDeps @ [intMod]).
                          CM_TypeSubst x = fmempty"
    using deps_subst intMod_subst by auto
  have b_subst: "CM_TypeSubst b = fmempty"
    using link_modules_empty_subst[OF linkB b_inputs_subst] .
  have subL_mset: "mset (map fst intDeps @ [intMod])
                     \<subseteq># mset (map fst intDeps @ map fst implDeps @ [intMod])"
    by (simp add: subseteq_mset_def)
  have subC_mset: "mset (map fst intDeps @ map fst implDeps)
                     \<subseteq># mset (map fst intDeps @ map fst implDeps @ [intMod])"
    by (simp add: subseteq_mset_def)
  have subL_subst: "\<forall>x \<in> set (map fst intDeps @ [intMod]). CM_TypeSubst x = fmempty"
    using b_inputs_subst by auto
  have subC_subst: "\<forall>x \<in> set (map fst intDeps @ map fst implDeps).
                      CM_TypeSubst x = fmempty"
    using b_inputs_subst by auto
  obtain li where linkLI: "link_modules (map fst intDeps @ [intMod]) = Inr li"
    using link_modules_empty_substs_sublink[OF linkB subL_subst subL_mset] by blast
  obtain c where linkC: "link_modules (map fst intDeps @ map fst implDeps) = Inr c"
    using link_modules_empty_substs_sublink[OF linkB subC_subst subC_mset] by blast
  have subL_set: "set (map fst intDeps @ [intMod])
                    \<subseteq> set (map fst intDeps @ map fst implDeps @ [intMod])"
    by auto
  have subC_set: "set (map fst intDeps @ map fst implDeps)
                    \<subseteq> set (map fst intDeps @ map fst implDeps @ [intMod])"
    by auto

  \<comment> \<open>b is well-typed: the two sub-links are (conclusion (i) and the C
     premise), and their union covers b's inputs.\<close>
  have li_wt: "core_module_well_typed li"
    using concl_i[OF linkLI] .
  have c_wt: "core_module_well_typed c"
    using C_wt[OF linkC] .
  have ghostOK: "\<forall>x \<in> set (map fst intDeps @ map fst implDeps @ [intMod]).
                   module_ghost_subsets_ok x"
    using deps_inv intMod_inv unfolding core_module_invariant_def by auto
  have setB: "set (map fst intDeps @ map fst implDeps @ [intMod])
                = set (map fst intDeps @ map fst implDeps)
                  \<union> set (map fst intDeps @ [intMod])"
    by auto
  have b_wt: "core_module_well_typed b"
    using link_preserves_well_typed[OF linkC c_wt linkLI li_wt linkB setB ghostOK] .

  \<comment> \<open>The face-2 ElabEnv union is well-formed over b's env: each dep delta
     transfers from c's env, and the interface's own delta from li's.\<close>
  have eb_wf: "elabenv_well_formed (CM_TyEnv b)
                 (elabenv_union (map snd intDeps @ map snd implDeps @ [intEE]))"
  proof (rule elabenv_union_well_formed)
    show "\<forall>e \<in> set (map snd intDeps @ map snd implDeps @ [intEE]).
            elabenv_well_formed (CM_TyEnv b) e"
    proof
      fix e assume "e \<in> set (map snd intDeps @ map snd implDeps @ [intEE])"
      then consider (dep) "e \<in> snd ` set (intDeps @ implDeps)" | (own) "e = intEE"
        by auto
      then show "elabenv_well_formed (CM_TyEnv b) e"
      proof cases
        case dep
        then obtain d where d_in: "d \<in> set (intDeps @ implDeps)" and e_eq: "e = snd d"
          by auto
        have wf_c: "elabenv_well_formed (CM_TyEnv c) e"
          using eeC[OF linkC] d_in e_eq by auto
        have nv: "\<not> EE_CurrentFunctionVoid e"
          using deps_ok d_in e_eq unfolding compiled_module_ok_def by auto
        show ?thesis
          using elabenv_well_formed_link_mono[OF linkC linkB b_inputs_subst
                  subC_set wf_c nv] .
      next
        case own
        have wf_li: "elabenv_well_formed (CM_TyEnv li) intEE"
          using concl_iii[OF linkLI] .
        show ?thesis
          using elabenv_well_formed_link_mono[OF linkLI linkB b_inputs_subst
                  subL_set wf_li intEE_nv] own by simp
      qed
    qed
  qed

  \<comment> \<open>The remaining elab_link_well_typed premises for face 2.\<close>
  have b_fresh: "module_tyvars_fresh_ok b"
    using link_modules_tyvars_fresh_ok[OF linkB] deps_fresh intMod_fresh by auto
  have ctx_freshB: "\<forall>n. n |\<in>| TE_TypeVars (CM_TyEnv b) \<longrightarrow> tyvar_fresh_ok n 0"
   and fun_freshB: "\<forall>name info.
                      fmlookup (TE_Functions (CM_TyEnv b)) name = Some info \<longrightarrow>
                      list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)"
    using b_fresh unfolding module_tyvars_fresh_ok_def by blast+
  have ownB: "TE_TypeVars (CM_TyEnv intMod) |\<subseteq>| TE_TypeVars (CM_TyEnv b)"
    by (rule link_modules_TypeVars_superset[OF linkB b_inputs_subst]) simp

  \<comment> \<open>Face 2's fold invariant, and conclusion (v) read off it: the
     implementation face satisfies the structural invariant, and its
     substitution domain is bounded by ownAbstract - the abstract types the
     module's own interface declared. (Emptiness would be false: a
     realization lands in CM_TypeSubst implMod.)\<close>
  have b_nwt: "normalized_module_well_typed b"
    using core_module_well_typed_on_normalized[OF b_subst] b_wt by blast
  have ctxB: "elab_context_ok (CM_TyEnv b) (TE_TypeVars (CM_TyEnv intMod))"
    using b_nwt ownB ctx_freshB fun_freshB
    unfolding elab_context_ok_def normalized_module_well_typed_def by blast
  obtain envG where invG: "elab_decls_invariant (CM_TyEnv b)
                             (TE_TypeVars (CM_TyEnv intMod)) envG implFoldEnv implMod"
                and rtokG: "subst_runtime_ok (CM_TyEnv b) envG implMod"
    using ctxB eb_wf elabImpl
    by (rule elab_declarations_subst_runtime)
  have concl_v: "core_module_invariant implMod
                   \<and> fmdom (CM_TypeSubst implMod) |\<subseteq>| TE_TypeVars (CM_TyEnv intMod)"
    using invG unfolding elab_decls_invariant_def by blast
  have envG_eq: "envG = module_context_env (CM_TyEnv b) implMod"
    using invG unfolding elab_decls_invariant_def by blast
  note bF = link_modules_result_fields[OF linkB]

  \<comment> \<open>Conclusion (viii): the implementation face declares no abstract types -
     declaration-only forms were rejected up front, so its input list has no
     definition-less typedefs, and the provenance fold lemma bounds the
     module's TE_TypeVars by exactly those.\<close>
  have no_abs_impl: "\<forall>d \<in> set (Mod_Implementation bm). decl_abstract_names d = {||}"
  proof
    fix d assume d_in: "d \<in> set (Mod_Implementation bm)"
    have "\<not> is_decl_only d"
      using implDefs d_in unfolding check_impl_definitions_def
      by auto
    then show "decl_abstract_names d = {||}"
      by (cases d) auto
  qed
  have implAbs: "decls_abstract_names sortedImpl = {||}"
    unfolding decls_abstract_names_def
  proof (rule funion_list_map_empty)
    show "\<forall>d \<in> set sortedImpl. decl_abstract_names d = {||}"
      using no_abs_impl mset_eq_setD[OF sort_declarations_mset[OF sortImpl]] by blast
  qed
  have concl_viii: "TE_TypeVars (CM_TyEnv implMod) = {||}"
    using elab_declarations_own_tyvars[OF elabImpl] implAbs by auto

  \<comment> \<open>Conclusion (vii): every abstract type of the interface is realized -
     the provenance fold lemma names them all as abstract typedefs of the
     interface's declaration list, and check_completeness put each of those
     into the implementation's substitution domain.\<close>
  have concl_vii: "TE_TypeVars (CM_TyEnv intMod) |\<subseteq>| fmdom (CM_TypeSubst implMod)"
  proof -
    have "TE_TypeVars (CM_TyEnv intMod) |\<subseteq>| decls_abstract_names sortedInt"
      using elab_declarations_own_tyvars[OF elabInt] .
    also have "decls_abstract_names sortedInt
                 = decls_abstract_names (Mod_Interface bm)"
      using decls_abstract_names_mset_cong[OF sort_declarations_mset[OF sortInt]] .
    also have "decls_abstract_names (Mod_Interface bm)
                 |\<subseteq>| fmdom (CM_TypeSubst implMod)"
      using check_completeness_abstract_realized[OF complete] .
    finally show ?thesis .
  qed

  \<comment> \<open>Conclusion (ix): the realization targets only mention the in-scope
     abstract types of the linked context b - each target is well-kinded in
     the fold's final state env (the invariant), whose type variables come
     from b's inputs (the implementation face contributes none, by (viii)).\<close>
  have concl_ix: "subst_range_tyvars (CM_TypeSubst implMod)
                    \<subseteq> fset (funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x))
                               (map fst intDeps @ map fst implDeps @ [intMod])))"
  proof
    fix v assume "v \<in> subst_range_tyvars (CM_TypeSubst implMod)"
    then obtain ty where ty_ran: "ty \<in> fmran' (CM_TypeSubst implMod)"
                     and v_ty: "v \<in> type_tyvars ty"
      unfolding subst_range_tyvars_def by blast
    obtain n where lk: "fmlookup (CM_TypeSubst implMod) n = Some ty"
      using ty_ran by (auto simp: fmlookup_ran'_iff)
    have tswkG: "typesubst_well_kinded envG (CM_TypeSubst implMod)"
      using invG unfolding elab_decls_invariant_def by blast
    have wk: "is_well_kinded envG ty"
      using tswkG lk unfolding typesubst_well_kinded_def by blast
    have v_envG: "v \<in> fset (TE_TypeVars envG)"
      using is_well_kinded_type_tyvars_subset[OF wk] v_ty by blast
    have tv_b: "TE_TypeVars (CM_TyEnv b)
                  = funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x))
                       (map fst intDeps @ map fst implDeps @ [intMod]))"
      using bF(5) unfolding b_subst by simp
    have "TE_TypeVars envG
            |\<subseteq>| funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x))
                    (map fst intDeps @ map fst implDeps @ [intMod]))"
      unfolding envG_eq module_context_env_tyvar_fields(1)
      using concl_viii tv_b by auto
    then show "v \<in> fset (funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x))
                     (map fst intDeps @ map fst implDeps @ [intMod])))"
      using v_envG by (auto simp: less_eq_fset.rep_eq)
  qed

  \<comment> \<open>Conclusion (ii): collapse the flat implementation link to the pair
     link; the context facts are all established above.\<close>
  have concl_ii: "core_module_well_typed P"
    if linkP: "link_modules
                 (map fst intDeps @ map fst implDeps @ [intMod, implMod]) = Inr P" for P
  proof -
    have linkP': "link_modules
                    ((map fst intDeps @ map fst implDeps @ [intMod]) @ [implMod]) = Inr P"
      using linkP by simp
    have pairP: "link_modules [b, implMod] = Inr P"
      using link_modules_collapse[OF linkB linkP'] .
    show ?thesis
      using elab_link_well_typed[OF b_wt b_subst eb_wf ownB ctx_freshB fun_freshB
              elabImpl pairP] .
  qed

  \<comment> \<open>Conclusion (vi): the runtime gate of the derived implementation link.
     Any merged substitution of the input list is CM_TypeSubst implMod itself
     (every other input is substitution-free, and an idempotent substitution
     is its own unique closure), and the two env fields is_runtime_type reads
     agree between link_result of the list and the fold's final state env
     (the invariant's pivot equation env = module_context_env (CM_TyEnv b)
     implMod, both sides being the same union over b's inputs plus implMod).
     So the fold-level fact subst_runtime_ok is exactly the gate.\<close>
  have concl_vi: "link_runtime_ok
                    (map fst intDeps @ map fst implDeps @ [intMod, implMod]) \<sigma>"
    if merge: "merge_all_substs (map CM_TypeSubst
                 (map fst intDeps @ map fst implDeps @ [intMod, implMod])) = Inr \<sigma>"
    for \<sigma>
  proof -
    let ?Bs = "map fst intDeps @ map fst implDeps @ [intMod]"
    let ?Ps = "map fst intDeps @ map fst implDeps @ [intMod, implMod]"
    have implMod_inv: "core_module_invariant implMod"
      using concl_v by blast
    have Ps_snoc: "?Ps = ?Bs @ [implMod]"
      by simp

    \<comment> \<open>Identify the merged substitution.\<close>
    have idemI: "idempotent_subst (CM_TypeSubst implMod)"
      using implMod_inv unfolding core_module_invariant_def by blast
    have merge': "merge_all_substs (map CM_TypeSubst (?Bs @ [implMod])) = Inr \<sigma>"
      using merge by simp
    have \<sigma>_eq: "\<sigma> = CM_TypeSubst implMod"
      using merge_substs_empties_snoc[OF merge' b_inputs_subst idemI] .

    \<comment> \<open>The two runtime-relevant env fields of link_result agree with envG.\<close>
    have rtv_b: "TE_RuntimeTypeVars (CM_TyEnv b)
                   = funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) ?Bs)"
      using bF(6) unfolding b_subst by simp
    have gd_b: "TE_GhostDatatypes (CM_TyEnv b)
                  = funion_list (map (\<lambda>x. TE_GhostDatatypes (CM_TyEnv x)) ?Bs)"
      using bF(16) .
    have splitRT: "funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) ?Ps)
                     = funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) ?Bs)
                       |\<union>| TE_RuntimeTypeVars (CM_TyEnv implMod)"
      unfolding Ps_snoc by (rule funion_list_map_snoc)
    have splitGD: "funion_list (map (\<lambda>x. TE_GhostDatatypes (CM_TyEnv x)) ?Ps)
                     = funion_list (map (\<lambda>x. TE_GhostDatatypes (CM_TyEnv x)) ?Bs)
                       |\<union>| TE_GhostDatatypes (CM_TyEnv implMod)"
      unfolding Ps_snoc by (rule funion_list_map_snoc)
    have gd_P: "TE_GhostDatatypes (CM_TyEnv (link_result ?Ps \<sigma>))
                  = funion_list (map (\<lambda>x. TE_GhostDatatypes (CM_TyEnv x)) ?Ps)"
     and rtv_P: "TE_RuntimeTypeVars (CM_TyEnv (link_result ?Ps \<sigma>))
                  = funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) ?Ps)
                    |-| fmdom \<sigma>"
      unfolding link_result_def by simp_all
    have gd_G: "TE_GhostDatatypes envG
                  = TE_GhostDatatypes (CM_TyEnv b)
                    |\<union>| TE_GhostDatatypes (CM_TyEnv implMod)"
      unfolding envG_eq module_context_env_def apply_subst_to_tyenv_def by simp
    have rtv_G: "TE_RuntimeTypeVars envG
                   = (TE_RuntimeTypeVars (CM_TyEnv b)
                      |\<union>| TE_RuntimeTypeVars (CM_TyEnv implMod))
                     |-| fmdom (CM_TypeSubst implMod)"
      unfolding envG_eq by (rule module_context_env_tyvar_fields(2))
    have gd_eq: "TE_GhostDatatypes (CM_TyEnv (link_result ?Ps \<sigma>))
                   = TE_GhostDatatypes envG"
      unfolding gd_P splitGD gd_G gd_b ..
    have rtv_eq: "TE_RuntimeTypeVars (CM_TyEnv (link_result ?Ps \<sigma>))
                    = TE_RuntimeTypeVars envG"
      using \<sigma>_eq rtv_G rtv_P rtv_b splitRT by presburger

    show ?thesis
      unfolding link_runtime_ok_def
    proof (intro allI impI)
      fix n
      assume n_in: "n |\<in>| fmdom \<sigma>
                      |\<inter>| funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) ?Ps)"
      have n_dom: "n |\<in>| fmdom (CM_TypeSubst implMod)"
        using n_in unfolding \<sigma>_eq by auto
      then obtain ty where lk: "fmlookup (CM_TypeSubst implMod) n = Some ty"
        by (auto simp: fmlookup_dom_iff)
      \<comment> \<open>The declarer of n as a runtime abstract type is one of b's inputs:
         it cannot be implMod, whose substitution domain avoids its own type
         variables.\<close>
      have n_not_impl: "n |\<notin>| TE_RuntimeTypeVars (CM_TyEnv implMod)"
      proof
        assume n_rt: "n |\<in>| TE_RuntimeTypeVars (CM_TyEnv implMod)"
        have "TE_RuntimeTypeVars (CM_TyEnv implMod) |\<subseteq>| TE_TypeVars (CM_TyEnv implMod)"
         and "fmdom (CM_TypeSubst implMod) |\<inter>| TE_TypeVars (CM_TyEnv implMod) = {||}"
          using implMod_inv unfolding core_module_invariant_def by blast+
        then show False
          using n_rt n_dom by (metis fempty_iff finter_iff fsubsetD)
      qed
      have "n |\<in>| funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) ?Ps)"
        using n_in by auto
      then have n_b: "n |\<in>| TE_RuntimeTypeVars (CM_TyEnv b)"
        using splitRT rtv_b n_not_impl by auto
      have rt_G: "is_runtime_type envG ty"
        using rtokG lk n_b unfolding subst_runtime_ok_def by blast
      have "is_runtime_type (CM_TyEnv (link_result ?Ps \<sigma>)) ty"
        using rt_G is_runtime_type_cong_env[OF gd_eq rtv_eq] by blast
      then show "is_runtime_type (CM_TyEnv (link_result ?Ps \<sigma>)) (the (fmlookup \<sigma> n))"
        unfolding \<sigma>_eq using lk by simp
    qed
  qed

  \<comment> \<open>Discharge the conclusions.\<close>
  show "link_modules (map fst intDeps @ [intMod]) = Inr L \<Longrightarrow> core_module_well_typed L"
    by (rule concl_i)
  show "link_modules (map fst intDeps @ map fst implDeps @ [intMod, implMod]) = Inr P
          \<Longrightarrow> core_module_well_typed P"
    by (rule concl_ii)
  show "link_modules (map fst intDeps @ [intMod]) = Inr L
          \<Longrightarrow> elabenv_well_formed (CM_TyEnv L) intEE"
    by (rule concl_iii)
  show "compiled_module_ok (intMod, intEE)"
    using concl_iv .
  show "core_module_invariant implMod
          \<and> fmdom (CM_TypeSubst implMod) |\<subseteq>| TE_TypeVars (CM_TyEnv intMod)"
    using concl_v .
  show "merge_all_substs (map CM_TypeSubst
          (map fst intDeps @ map fst implDeps @ [intMod, implMod])) = Inr \<sigma>
          \<Longrightarrow> link_runtime_ok
                (map fst intDeps @ map fst implDeps @ [intMod, implMod]) \<sigma>"
    by (rule concl_vi)
  show "TE_TypeVars (CM_TyEnv intMod) |\<subseteq>| fmdom (CM_TypeSubst implMod)"
    using concl_vii .
  show "TE_TypeVars (CM_TyEnv implMod) = {||}"
    using concl_viii .
  show "subst_range_tyvars (CM_TypeSubst implMod)
          \<subseteq> fset (funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x))
                     (map fst intDeps @ map fst implDeps @ [intMod])))"
    using concl_ix .
qed


(* ========================================================================== *)
(* Per-module definedness, in env terms (step 8c)                             *)
(* ========================================================================== *)

(* A clean check_completeness certifies that every declared-but-undefined
   const (resp. non-extern bodiless function or declaration-only ghost const)
   of the interface is defined by
   one of the two faces. Composed with the provenance fold lemmas
   (elab_declarations_undefined_globals/_funs), this yields the env-level
   definedness facts whole-program closedness (step 8c) needs. *)
lemma check_completeness_defined:
  assumes ok: "check_completeness intf intMod implMod = []"
  shows "decls_undefined_consts intf
           |\<subseteq>| fmdom (CM_GlobalVars intMod) |\<union>| fmdom (CM_GlobalVars implMod)"
    and "decls_undefined_funs intf
           |\<subseteq>| fmdom (CM_Functions intMod) |\<union>| fmdom (CM_Functions implMod)"
proof -
  have all_nil: "\<forall>d \<in> set intf.
     (case d of
        BabDecl_Const dc \<Rightarrow>
          (if DC_Value dc = None
              \<and> (if DC_Ghost dc = Ghost
                 then DC_Name dc |\<notin>| fmdom (CM_Functions intMod)
                      \<and> DC_Name dc |\<notin>| fmdom (CM_Functions implMod)
                 else DC_Name dc |\<notin>| fmdom (CM_GlobalVars intMod)
                      \<and> DC_Name dc |\<notin>| fmdom (CM_GlobalVars implMod))
           then [TyErr_DeclaredButNotDefined (DC_Location dc) (DC_Name dc)]
           else [])
      | BabDecl_Function df \<Rightarrow>
          (if DF_Body df = None \<and> \<not> DF_Extern df
              \<and> DF_Name df |\<notin>| fmdom (CM_Functions intMod)
              \<and> DF_Name df |\<notin>| fmdom (CM_Functions implMod)
           then [TyErr_DeclaredButNotDefined (DF_Location df) (DF_Name df)]
           else [])
      | BabDecl_Datatype dd \<Rightarrow> []
      | BabDecl_Typedef dt \<Rightarrow>
          (if DT_Definition dt = None
              \<and> DT_Name dt |\<notin>| fmdom (CM_TypeSubst implMod)
           then [TyErr_AbstractTypeNotRealized (DT_Location dt) (DT_Name dt)]
           else [])) = []"
    using ok unfolding check_completeness_def by simp
  show "decls_undefined_consts intf
          |\<subseteq>| fmdom (CM_GlobalVars intMod) |\<union>| fmdom (CM_GlobalVars implMod)"
  proof
    fix n assume "n |\<in>| decls_undefined_consts intf"
    then obtain d where d_in: "d \<in> set intf" and n_d: "n |\<in>| decl_undefined_consts d"
      unfolding decls_undefined_consts_def by (auto simp: funion_list_member)
    from n_d obtain dc where d_eq: "d = BabDecl_Const dc"
        and noval: "DC_Value dc = None"
        and ng: "DC_Ghost dc = NotGhost"
        and n_eq: "n = DC_Name dc"
      by (cases d) (auto split: if_splits)
    from bspec[OF all_nil d_in]
    show "n |\<in>| fmdom (CM_GlobalVars intMod) |\<union>| fmdom (CM_GlobalVars implMod)"
      unfolding d_eq using noval ng n_eq by (auto split: if_splits)
  qed
  show "decls_undefined_funs intf
          |\<subseteq>| fmdom (CM_Functions intMod) |\<union>| fmdom (CM_Functions implMod)"
  proof
    fix n assume "n |\<in>| decls_undefined_funs intf"
    then obtain d where d_in: "d \<in> set intf" and n_d: "n |\<in>| decl_undefined_funs d"
      unfolding decls_undefined_funs_def by (auto simp: funion_list_member)
    \<comment> \<open>Either a bodiless non-extern function, or a declaration-only ghost
       constant (whose desugared definition also lands in CM_Functions).\<close>
    from n_d have
      "(\<exists>df. d = BabDecl_Function df \<and> DF_Body df = None \<and> \<not> DF_Extern df
             \<and> n = DF_Name df)
       \<or> (\<exists>dc. d = BabDecl_Const dc \<and> DC_Value dc = None \<and> DC_Ghost dc = Ghost
               \<and> n = DC_Name dc)"
      by (cases d) (auto split: if_splits)
    then show "n |\<in>| fmdom (CM_Functions intMod) |\<union>| fmdom (CM_Functions implMod)"
    proof (elim disjE exE conjE)
      fix df assume d_eq: "d = BabDecl_Function df"
        and nobody: "DF_Body df = None" and noext: "\<not> DF_Extern df"
        and n_eq: "n = DF_Name df"
      from bspec[OF all_nil d_in] show ?thesis
        unfolding d_eq using nobody noext n_eq by (auto split: if_splits)
    next
      fix dc assume d_eq: "d = BabDecl_Const dc"
        and noval: "DC_Value dc = None" and gh: "DC_Ghost dc = Ghost"
        and n_eq: "n = DC_Name dc"
      from bspec[OF all_nil d_in] show ?thesis
        unfolding d_eq using noval gh n_eq by (auto split: if_splits)
    qed
  qed
qed

(* check_impl_definitions rejects every declaration-only form, so an
   implementation face has no declared-but-undefined names at all. *)
lemma check_impl_definitions_defined:
  assumes ok: "check_impl_definitions impl = []"
  shows "decls_undefined_consts impl = {||}"
    and "decls_undefined_funs impl = {||}"
proof -
  have no_c: "\<forall>d \<in> set impl. decl_undefined_consts d = {||}"
  proof
    fix d assume d_in: "d \<in> set impl"
    have "\<not> is_decl_only d"
      using ok d_in unfolding check_impl_definitions_def by auto
    then show "decl_undefined_consts d = {||}" by (cases d) auto
  qed
  have no_f: "\<forall>d \<in> set impl. decl_undefined_funs d = {||}"
  proof
    fix d assume d_in: "d \<in> set impl"
    have "\<not> is_decl_only d"
      using ok d_in unfolding check_impl_definitions_def by auto
    then show "decl_undefined_funs d = {||}" by (cases d) auto
  qed
  show "decls_undefined_consts impl = {||}"
    unfolding decls_undefined_consts_def
    by (rule funion_list_map_empty) (use no_c in blast)
  show "decls_undefined_funs impl = {||}"
    unfolding decls_undefined_funs_def
    by (rule funion_list_map_empty) (use no_f in blast)
qed

(* From elab_module success alone: everything either face declares is defined
   by one of the two faces (an interface declaration may be defined by either
   face; an implementation declaration is defined by the implementation
   itself). These are the per-module inputs to whole-program closedness -
   the linked program's TE_GlobalVars/TE_Functions domains are the unions of
   these per-face domains, so the facts below make "declared implies defined"
   hold of the whole program. *)
theorem elab_module_defs_complete:
  assumes elab: "elab_module bm intDeps implDeps
                   = Inr ((intMod, intEE), (implMod, implEE))"
  shows "fmdom (TE_GlobalVars (CM_TyEnv intMod))
           |\<subseteq>| fmdom (CM_GlobalVars intMod) |\<union>| fmdom (CM_GlobalVars implMod)"
    and "fmdom (TE_Functions (CM_TyEnv intMod))
           |\<subseteq>| fmdom (CM_Functions intMod) |\<union>| fmdom (CM_Functions implMod)"
    and "fmdom (TE_GlobalVars (CM_TyEnv implMod)) |\<subseteq>| fmdom (CM_GlobalVars implMod)"
    and "fmdom (TE_Functions (CM_TyEnv implMod)) |\<subseteq>| fmdom (CM_Functions implMod)"
proof -
  obtain a b sortedInt intFoldEnv sortedImpl implFoldEnv where
    implDefs: "check_impl_definitions (Mod_Implementation bm) = []" and
    complete: "check_completeness (Mod_Interface bm) intMod implMod = []" and
    linkA: "link_modules (map fst intDeps) = Inr a" and
    sortInt: "sort_declarations (CM_TyEnv a) (elabenv_union (map snd intDeps))
                (Mod_Interface bm) = Inr sortedInt" and
    elabInt: "elab_declarations (CM_TyEnv a) (elabenv_union (map snd intDeps))
                {||} sortedInt = Inr (intMod, intFoldEnv)" and
    intEE_eq: "intEE = elabenv_delta (elabenv_union (map snd intDeps)) intFoldEnv" and
    linkB: "link_modules (map fst intDeps @ map fst implDeps @ [intMod]) = Inr b" and
    sortImpl: "sort_declarations (CM_TyEnv b)
                 (elabenv_union (map snd intDeps @ map snd implDeps @ [intEE]))
                 (Mod_Implementation bm) = Inr sortedImpl" and
    elabImpl: "elab_declarations (CM_TyEnv b)
                 (elabenv_union (map snd intDeps @ map snd implDeps @ [intEE]))
                 (TE_TypeVars (CM_TyEnv intMod)) sortedImpl
                 = Inr (implMod, implFoldEnv)" and
    implEE_eq: "implEE = elabenv_delta
                  (elabenv_union (map snd intDeps @ map snd implDeps @ [intEE]))
                  implFoldEnv"
    using elab by (rule elab_module_Inr_elim)

  \<comment> \<open>The interface face: its undefined names survive the dependency sort and
     were each put into one of the two definition maps by check_completeness.\<close>
  have int_c: "fmdom (TE_GlobalVars (CM_TyEnv intMod))
                 |\<subseteq>| fmdom (CM_GlobalVars intMod) |\<union>| decls_undefined_consts sortedInt"
    using elab_declarations_undefined_globals[OF elabInt] .
  have int_f: "fmdom (TE_Functions (CM_TyEnv intMod))
                 |\<subseteq>| fmdom (CM_Functions intMod) |\<union>| decls_undefined_funs sortedInt"
    using elab_declarations_undefined_funs[OF elabInt] .
  have sortInt_c: "decls_undefined_consts sortedInt
                     = decls_undefined_consts (Mod_Interface bm)"
    using decls_undefined_consts_mset_cong[OF sort_declarations_mset[OF sortInt]] .
  have sortInt_f: "decls_undefined_funs sortedInt
                     = decls_undefined_funs (Mod_Interface bm)"
    using decls_undefined_funs_mset_cong[OF sort_declarations_mset[OF sortInt]] .

  show "fmdom (TE_GlobalVars (CM_TyEnv intMod))
          |\<subseteq>| fmdom (CM_GlobalVars intMod) |\<union>| fmdom (CM_GlobalVars implMod)"
  proof
    fix n assume "n |\<in>| fmdom (TE_GlobalVars (CM_TyEnv intMod))"
    then have "n |\<in>| fmdom (CM_GlobalVars intMod)
                 |\<union>| decls_undefined_consts (Mod_Interface bm)"
      using fsubsetD[OF int_c] unfolding sortInt_c by auto
    then show "n |\<in>| fmdom (CM_GlobalVars intMod) |\<union>| fmdom (CM_GlobalVars implMod)"
      using fsubsetD[OF check_completeness_defined(1)[OF complete]] by auto
  qed
  show "fmdom (TE_Functions (CM_TyEnv intMod))
          |\<subseteq>| fmdom (CM_Functions intMod) |\<union>| fmdom (CM_Functions implMod)"
  proof
    fix n assume "n |\<in>| fmdom (TE_Functions (CM_TyEnv intMod))"
    then have "n |\<in>| fmdom (CM_Functions intMod)
                 |\<union>| decls_undefined_funs (Mod_Interface bm)"
      using fsubsetD[OF int_f] unfolding sortInt_f by auto
    then show "n |\<in>| fmdom (CM_Functions intMod) |\<union>| fmdom (CM_Functions implMod)"
      using fsubsetD[OF check_completeness_defined(2)[OF complete]] by auto
  qed

  \<comment> \<open>The implementation face: it has no undefined names at all.\<close>
  have impl_c: "fmdom (TE_GlobalVars (CM_TyEnv implMod))
                  |\<subseteq>| fmdom (CM_GlobalVars implMod) |\<union>| decls_undefined_consts sortedImpl"
    using elab_declarations_undefined_globals[OF elabImpl] .
  have impl_f: "fmdom (TE_Functions (CM_TyEnv implMod))
                  |\<subseteq>| fmdom (CM_Functions implMod) |\<union>| decls_undefined_funs sortedImpl"
    using elab_declarations_undefined_funs[OF elabImpl] .
  have sortImpl_c: "decls_undefined_consts sortedImpl = {||}"
    using decls_undefined_consts_mset_cong[OF sort_declarations_mset[OF sortImpl]]
          check_impl_definitions_defined(1)[OF implDefs] by simp
  have sortImpl_f: "decls_undefined_funs sortedImpl = {||}"
    using decls_undefined_funs_mset_cong[OF sort_declarations_mset[OF sortImpl]]
          check_impl_definitions_defined(2)[OF implDefs] by simp
  show "fmdom (TE_GlobalVars (CM_TyEnv implMod)) |\<subseteq>| fmdom (CM_GlobalVars implMod)"
    using impl_c unfolding sortImpl_c by (simp add: funion_fempty_right)
  show "fmdom (TE_Functions (CM_TyEnv implMod)) |\<subseteq>| fmdom (CM_Functions implMod)"
    using impl_f unfolding sortImpl_f by (simp add: funion_fempty_right)
qed

end
