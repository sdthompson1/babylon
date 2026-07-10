theory ElabModuleCorrect
  imports ElabModule ElabDeclCorrect "../core/LinkCollapse"
begin

(* Correctness of the per-module orchestrator (step 6b of LINKING.md).

   The target theorem is elab_module_well_typed: from a successful
   elab_module run, plus the facts the pipeline fold can supply about the
   two compiled dependency lists, conclude well-typedness of the module's
   derived linked faces (stated over FLAT links of original modules, the
   form the pipeline composes via link_preserves_well_typed), the
   well-formedness of the interface face's exported ElabEnv delta, and the
   per-module housekeeping facts that feed downstream modules' premises.

   The proof shape, per face: link the compiled deps into a context (the
   same link elab_module computes), establish elab_link_well_typed's
   premises about that context, and bridge its two-module conclusion to the
   flat link via the collapse lemma (core/LinkCollapse.thy).

   The theorem is elab_module_well_typed, at the end of this theory; the
   sections before it are its transfer plumbing: metavariable-freshness of
   type-variable names across links, the fold-invariant exports for
   elab_declarations, well-formedness of ElabEnv combination, the
   compiled-module contract, and the elimination rule for elab_module
   success. *)


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
      and fresh: "list_all decl_tyvars_fresh_ok decls"
      and elab: "elab_declarations env0 elabEnv0 ownAbstract decls = Inr (M, elabEnv')"
  obtains envF where "elab_decls_invariant env0 ownAbstract envF elabEnv' M"
proof -
  have init: "elab_decls_invariant env0 ownAbstract env0 elabEnv0 empty_core_module"
    using elab_decls_invariant_init[OF ctx ee] .
  from elab obtain envF where
    run: "elab_declaration_list env0 elabEnv0 ownAbstract empty_core_module decls
            = Inr (envF, elabEnv', M)"
    unfolding elab_declarations_def
    by (auto split: sum.splits prod.splits)
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
  show ?thesis
    unfolding elabenv_well_formed_def
    using td nc nv by blast
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
  show ?thesis
    unfolding elabenv_well_formed_def
    using td nc by simp
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
  show ?thesis
    unfolding elabenv_well_formed_def
    using td nc by simp
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
proof (rule elabenv_well_formed_mono[OF wf _ _ _ nv])
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
(* Unpacking a successful elab_module run                                     *)
(* ========================================================================== *)

(* The elimination rule for elab_module success: names every intermediate
   object of the orchestration (the two link contexts, the sorted
   declaration lists, the two fold results) and states the defining
   equation of each returned ElabEnv delta. *)
lemma elab_module_Inr_elim:
  assumes ok: "elab_module bm intDeps implDeps = Inr ((intMod, intEE), (implMod, implEE))"
  obtains a b sortedInt intFoldEnv sortedImpl implFoldEnv where
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
  using ok unfolding elab_module_def Let_def
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
   not be well-typed, so neither follows from the other); well-formedness of
   each dep's ElabEnv delta over those links' envs (from the deps'
   conclusion-(iii) facts plus elabenv_well_formed_link_mono); and
   metavariable-freshness of the declaration binders (the renamer's naming
   discipline).

   Conclusions (i)-(iii) are about links elab_module does NOT itself compute
   and which may fail, hence conditional: (i) the derived linked interface is
   well-typed; (ii) the derived linked implementation - the whole-program
   feeder - is well-typed; (iii) the interface face's exported ElabEnv delta
   is well-formed over the linked interface's env; (iv) the housekeeping
   contract holds of the interface face, closing the pipeline's loop.
   (Nothing is concluded about implEE - it has no consumer.)

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
      and fresh_int: "list_all decl_tyvars_fresh_ok (Mod_Interface bm)"
      and fresh_impl: "list_all decl_tyvars_fresh_ok (Mod_Implementation bm)"
  shows "link_modules (map fst intDeps @ [intMod]) = Inr L
           \<Longrightarrow> core_module_well_typed L"                                     \<comment> \<open>(i)\<close>
    and "link_modules (map fst intDeps @ map fst implDeps @ [intMod, implMod]) = Inr P
           \<Longrightarrow> core_module_well_typed P"                                     \<comment> \<open>(ii)\<close>
    and "link_modules (map fst intDeps @ [intMod]) = Inr L
           \<Longrightarrow> elabenv_well_formed (CM_TyEnv L) intEE"                       \<comment> \<open>(iii)\<close>
    and "compiled_module_ok (intMod, intEE)"                                 \<comment> \<open>(iv)\<close>
proof -
  \<comment> \<open>Unpack the orchestration.\<close>
  obtain a b sortedInt intFoldEnv sortedImpl implFoldEnv where
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
  have sortedInt_fresh: "list_all decl_tyvars_fresh_ok sortedInt"
    using sort_declarations_list_all[OF sortInt fresh_int] .

  \<comment> \<open>Face 1's fold invariant, and the housekeeping facts read off it.\<close>
  have a_nwt: "normalized_module_well_typed a"
    using core_module_well_typed_on_normalized[OF a_subst] a_wt by blast
  have ctxA: "elab_context_ok (CM_TyEnv a) {||}"
    using a_nwt own0 ctx_freshA fun_freshA
    unfolding elab_context_ok_def normalized_module_well_typed_def by blast
  obtain envF where invF: "elab_decls_invariant (CM_TyEnv a) {||} envF intFoldEnv intMod"
    using ctxA ea_wf sortedInt_fresh elabInt by (rule elab_declarations_invariant)
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
              sortedInt_fresh elabInt pair] .
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

  \<comment> \<open>Conclusion (ii): derive face 2's context facts from the one link
     elab_module computed, then collapse to the pair link.\<close>
  have concl_ii: "core_module_well_typed P"
    if linkP: "link_modules
                 (map fst intDeps @ map fst implDeps @ [intMod, implMod]) = Inr P" for P
  proof -
    \<comment> \<open>Everything b links is substitution-free, so its sub-links succeed.\<close>
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
    obtain L where linkL: "link_modules (map fst intDeps @ [intMod]) = Inr L"
      using link_modules_empty_substs_sublink[OF linkB b_inputs_subst subL_mset] by blast
    obtain c where linkC: "link_modules (map fst intDeps @ map fst implDeps) = Inr c"
      using link_modules_empty_substs_sublink[OF linkB b_inputs_subst subC_mset] by blast
    have subL_set: "set (map fst intDeps @ [intMod])
                      \<subseteq> set (map fst intDeps @ map fst implDeps @ [intMod])"
      by auto
    have subC_set: "set (map fst intDeps @ map fst implDeps)
                      \<subseteq> set (map fst intDeps @ map fst implDeps @ [intMod])"
      by auto

    \<comment> \<open>b is well-typed: the two sub-links are (conclusion (i) and the C
       premise), and their union covers b's inputs.\<close>
    have L_wt: "core_module_well_typed L"
      using concl_i[OF linkL] .
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
      using link_preserves_well_typed[OF linkC c_wt linkL L_wt linkB setB ghostOK] .

    \<comment> \<open>The face-2 ElabEnv union is well-formed over b's env: each dep delta
       transfers from c's env, and the interface's own delta from L's.\<close>
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
          have wf_L: "elabenv_well_formed (CM_TyEnv L) intEE"
            using concl_iii[OF linkL] .
          show ?thesis
            using elabenv_well_formed_link_mono[OF linkL linkB b_inputs_subst
                    subL_set wf_L intEE_nv] own by simp
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
    have sortedImpl_fresh: "list_all decl_tyvars_fresh_ok sortedImpl"
      using sort_declarations_list_all[OF sortImpl fresh_impl] .

    \<comment> \<open>Collapse the flat implementation link to the pair link.\<close>
    have linkP': "link_modules
                    ((map fst intDeps @ map fst implDeps @ [intMod]) @ [implMod]) = Inr P"
      using linkP by simp
    have pairP: "link_modules [b, implMod] = Inr P"
      using link_modules_collapse[OF linkB linkP'] .

    show ?thesis
      using elab_link_well_typed[OF b_wt b_subst eb_wf ownB ctx_freshB fun_freshB
              sortedImpl_fresh elabImpl pairP] .
  qed

  \<comment> \<open>Discharge the four conclusions.\<close>
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
qed

end
