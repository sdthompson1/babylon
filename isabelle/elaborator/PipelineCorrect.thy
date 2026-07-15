theory PipelineCorrect
  imports Pipeline ElabModuleCorrect
begin

(* Correctness infrastructure for the compilation pipeline (LINKING.md
   step 8b). This theory supplies what the pipeline_fold induction consumes:

    - the properties of analyze_dependencies in the form the pipeline uses
      (module names are distinct; every import names some module of the
      program - together with the strict topological order, each fold step
      therefore finds its imports already in the state, at names distinct
      from its own);
    - a characterization of lookup_entries: success is exactly domain
      membership, the result is the pointwise lookup, and lookups are
      undisturbed by updates at fresh names;
    - the PipelineState invariant: per entry, the housekeeping, groundness
      and conditional-link facts of elab_module_well_typed (step 6b),
      phrased over context lists derived from the state, together with
      dep-set closure - plus the lemmas showing the invariant is stable
      when a fresh module is added.

   The invariant re-proves nothing about elaboration or linking; it only
   shuttles the step-6b conclusions from each pipeline_step to the final
   composition (compile_program_well_typed). *)


(* ========================================================================== *)
(* Properties of analyze_dependencies                                         *)
(* ========================================================================== *)

(* Success of analyze_dependencies means both generic checks passed. *)
lemma analyze_dependencies_checks:
  assumes ok: "analyze_dependencies modules = Inr sortedMods"
  shows "check_duplicate_names Mod_Name modules = None"
    and "check_deps_exist Mod_Name get_module_imports modules
           (build_item_map Mod_Name modules) = None"
proof -
  have no_self: "check_self_imports modules = None"
    using ok by (auto split: option.splits sum.splits)
  obtain sccs where gen:
    "analyze_dependencies_generic modules Mod_Name get_module_imports = Inr sccs"
    using ok no_self
    by (auto split: sum.splits if_splits option.splits simp: Let_def)
  show "check_duplicate_names Mod_Name modules = None"
    using gen by (auto split: option.splits simp: Let_def)
  show "check_deps_exist Mod_Name get_module_imports modules
          (build_item_map Mod_Name modules) = None"
    using gen by (auto split: option.splits simp: Let_def)
qed

(* The sorted output's module names are distinct - so each pipeline_step's
   fmupd is at a name not yet in the state, and the entries stored earlier
   (and every lookup they are phrased over) never change. *)
lemma analyze_dependencies_distinct_names:
  assumes ok: "analyze_dependencies modules = Inr sortedMods"
  shows "distinct (map Mod_Name sortedMods)"
proof -
  have "distinct (map Mod_Name modules)"
    using no_duplicate_errors_means_distinct[OF analyze_dependencies_checks(1)[OF ok]] .
  moreover have "mset (map Mod_Name sortedMods) = mset (map Mod_Name modules)"
    using analyze_dependencies_permutation[OF ok] by (metis mset_map)
  ultimately show ?thesis
    using mset_eq_imp_distinct_iff by blast
qed

(* Every import of every module names some module of the program. Combined
   with the strict topological order, the imported names are in the pipeline
   state's domain when their importer is processed. *)
lemma analyze_dependencies_imports_resolve:
  assumes ok: "analyze_dependencies modules = Inr sortedMods"
      and m_in: "m \<in> set sortedMods"
      and imp: "name \<in> set (get_module_imports m)"
  shows "\<exists>m' \<in> set sortedMods. Mod_Name m' = name"
proof -
  have set_eq: "set sortedMods = set modules"
    using analyze_dependencies_permutation[OF ok] by (metis mset_eq_setD)
  have "fmlookup (build_item_map Mod_Name modules) name \<noteq> None"
    using check_deps_exist_None_means_all_exist[OF analyze_dependencies_checks(2)[OF ok]]
          m_in imp set_eq by blast
  then have "name |\<in>| fmdom (build_item_map Mod_Name modules)"
    by (meson fmdom_notD)
  then have "name \<in> set (map Mod_Name modules)"
    using build_item_map_dom[of Mod_Name modules] by fastforce
  then show ?thesis
    using set_eq by auto
qed


(* ========================================================================== *)
(* Characterization of lookup_entries                                         *)
(* ========================================================================== *)

(* Success means every name is in the state's domain... *)
lemma lookup_entries_dom:
  assumes "lookup_entries ps ns = Inr es"
  shows "\<forall>n \<in> set ns. n |\<in>| fmdom ps"
  using assms
  by (induction ns arbitrary: es) (auto split: option.splits sum.splits intro: fmdomI)

(* ...and the result is the pointwise lookup. *)
lemma lookup_entries_eq:
  assumes "lookup_entries ps ns = Inr es"
  shows "es = map (\<lambda>n. the (fmlookup ps n)) ns"
  using assms
  by (induction ns arbitrary: es) (auto split: option.splits sum.splits)

(* Conversely, domain membership alone makes lookup_entries succeed. *)
lemma lookup_entries_defined:
  assumes "\<forall>n \<in> set ns. n |\<in>| fmdom ps"
  shows "lookup_entries ps ns = Inr (map (\<lambda>n. the (fmlookup ps n)) ns)"
  using assms
  by (induction ns) (auto split: option.splits dest: fmdom_notI)

(* The packaged characterization. *)
lemma lookup_entries_Inr_iff:
  "lookup_entries ps ns = Inr es \<longleftrightarrow>
     (\<forall>n \<in> set ns. n |\<in>| fmdom ps) \<and> es = map (\<lambda>n. the (fmlookup ps n)) ns"
  by (metis lookup_entries_dom lookup_entries_eq lookup_entries_defined)

(* Updating the state at a name outside the list does not disturb it. *)
lemma lookup_entries_fmupd_fresh:
  assumes "name \<notin> set ns"
  shows "lookup_entries (fmupd name x ps) ns = lookup_entries ps ns"
  using assms by (induction ns) (auto split: option.splits sum.splits)


(* ========================================================================== *)
(* The PipelineState invariant                                                *)
(* ========================================================================== *)

(* The elaboration context lists of an entry, derived from the state: the
   compiled interfaces of the entry's transitive interface deps (resp. the
   deps only its implementation face sees), in sorted name order. Under the
   domain conditions of the invariant these are exactly the lists
   pipeline_step passed to elab_module (lookup_entries is the same
   pointwise map, by lookup_entries_eq), and they are stable under updates
   at fresh names - which is what lets the per-entry facts, stated over
   them, survive the rest of the fold. *)
definition entry_int_ctx :: "PipelineState \<Rightarrow> PipelineModule \<Rightarrow> CompiledModule list" where
  "entry_int_ctx ps e =
     map (\<lambda>n. M_CompiledInterface (the (fmlookup ps n)))
         (sorted_list_of_fset (M_IntDeps e))"

definition entry_impl_ctx ::
  "PipelineState \<Rightarrow> string \<Rightarrow> PipelineModule \<Rightarrow> CompiledModule list" where
  "entry_impl_ctx ps name e =
     map (\<lambda>n. M_CompiledInterface (the (fmlookup ps n)))
         (sorted_list_of_fset (M_ImplDeps e |-| M_IntDeps e |-| {|name|}))"

lemma entry_int_ctx_fmupd_fresh:
  assumes "new |\<notin>| M_IntDeps e"
  shows "entry_int_ctx (fmupd new x ps) e = entry_int_ctx ps e"
  using assms unfolding entry_int_ctx_def map_eq_conv by auto

lemma entry_impl_ctx_fmupd_fresh:
  assumes "new |\<notin>| M_ImplDeps e"
  shows "entry_impl_ctx (fmupd new x ps) name e = entry_impl_ctx ps name e"
  using assms unfolding entry_impl_ctx_def map_eq_conv by auto

(* The per-entry invariant: the facts of elab_module_well_typed for the
   module stored at `name`, phrased over the state-derived context lists,
   plus the dep-set bookkeeping pipeline_step establishes. In order:

    - dep-set bookkeeping: both dep sets resolve in the state; the entry's
      own name is in M_ImplDeps (the implementation face sees its own
      interface) but not in M_IntDeps; M_IntDeps is contained in M_ImplDeps;
    - housekeeping: conclusion (iv) for the interface face, conclusion (v)
      for the implementation face;
    - groundness: conclusions (vii)-(ix) - every interface abstract is
      realized by the own implementation, implementations declare no
      abstracts, and the realization targets' type variables lie among the
      linked context's;
    - conditional link facts: conclusions (i)+(iii) for the linked
      interface list As, conclusion (ii) for the derived implementation
      list Bs, and conclusion (vi) certifying Bs's runtime gate for any
      merged substitution;
    - definedness (elab_module_defs_complete, feeding whole-program
      closedness): each face's declared globals/functions are defined by
      the two faces together (interface) resp. by itself (implementation). *)
definition pipeline_entry_ok :: "PipelineState \<Rightarrow> string \<Rightarrow> PipelineModule \<Rightarrow> bool" where
  "pipeline_entry_ok ps name e \<longleftrightarrow>
     (let intCtx = entry_int_ctx ps e;
          implCtx = entry_impl_ctx ps name e;
          intMod = fst (M_CompiledInterface e);
          intEE = snd (M_CompiledInterface e);
          implMod = fst (M_CompiledImplementation e);
          As = map fst intCtx @ [intMod];
          Bs = map fst intCtx @ map fst implCtx @ [intMod, implMod]
      in
        M_IntDeps e |\<subseteq>| fmdom ps
      \<and> M_ImplDeps e |\<subseteq>| fmdom ps
      \<and> name |\<notin>| M_IntDeps e
      \<and> name |\<in>| M_ImplDeps e
      \<and> M_IntDeps e |\<subseteq>| M_ImplDeps e
      \<and> compiled_module_ok (M_CompiledInterface e)
      \<and> core_module_invariant implMod
      \<and> fmdom (CM_TypeSubst implMod) |\<subseteq>| TE_TypeVars (CM_TyEnv intMod)
      \<and> TE_TypeVars (CM_TyEnv intMod) |\<subseteq>| fmdom (CM_TypeSubst implMod)
      \<and> TE_TypeVars (CM_TyEnv implMod) = {||}
      \<and> subst_range_tyvars (CM_TypeSubst implMod)
          \<subseteq> fset (funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x))
                     (map fst intCtx @ map fst implCtx @ [intMod])))
      \<and> (\<forall>L. link_modules As = Inr L \<longrightarrow>
               core_module_well_typed L \<and> elabenv_well_formed (CM_TyEnv L) intEE)
      \<and> (\<forall>P. link_modules Bs = Inr P \<longrightarrow> core_module_well_typed P)
      \<and> (\<forall>\<sigma>. merge_all_substs (map CM_TypeSubst Bs) = Inr \<sigma> \<longrightarrow> link_runtime_ok Bs \<sigma>)
      \<and> fmdom (TE_GlobalVars (CM_TyEnv intMod))
          |\<subseteq>| fmdom (CM_GlobalVars intMod) |\<union>| fmdom (CM_GlobalVars implMod)
      \<and> fmdom (TE_Functions (CM_TyEnv intMod))
          |\<subseteq>| fmdom (CM_Functions intMod) |\<union>| fmdom (CM_Functions implMod)
      \<and> fmdom (TE_GlobalVars (CM_TyEnv implMod)) |\<subseteq>| fmdom (CM_GlobalVars implMod)
      \<and> fmdom (TE_Functions (CM_TyEnv implMod)) |\<subseteq>| fmdom (CM_Functions implMod))"

(* The state invariant: every entry satisfies the per-entry invariant, and
   the dep sets are transitively closed - a dep's own interface deps are
   already among the depender's. Closure is what makes the set-union form
   of link_preserves_well_typed line up when composing the deps'
   conclusion-(i) facts, and what grounds prefix substitutions (every
   realization target's declaring interface is itself in the prefix). *)
definition pipeline_state_ok :: "PipelineState \<Rightarrow> bool" where
  "pipeline_state_ok ps \<longleftrightarrow>
     (\<forall>name e. fmlookup ps name = Some e \<longrightarrow>
        pipeline_entry_ok ps name e
        \<and> (\<forall>d. d |\<in>| M_IntDeps e \<longrightarrow>
                 M_IntDeps (the (fmlookup ps d)) |\<subseteq>| M_IntDeps e)
        \<and> (\<forall>d. d |\<in>| M_ImplDeps e \<longrightarrow>
                 M_IntDeps (the (fmlookup ps d)) |\<subseteq>| M_ImplDeps e))"

(* Projections, for the consumers. *)
lemma pipeline_entry_okD:
  assumes "pipeline_entry_ok ps name e"
  shows "M_IntDeps e |\<subseteq>| fmdom ps"
    and "M_ImplDeps e |\<subseteq>| fmdom ps"
    and "name |\<notin>| M_IntDeps e"
    and "name |\<in>| M_ImplDeps e"
    and "M_IntDeps e |\<subseteq>| M_ImplDeps e"
    and "compiled_module_ok (M_CompiledInterface e)"
    and "core_module_invariant (fst (M_CompiledImplementation e))"
    and "fmdom (CM_TypeSubst (fst (M_CompiledImplementation e)))
           |\<subseteq>| TE_TypeVars (CM_TyEnv (fst (M_CompiledInterface e)))"
    and "TE_TypeVars (CM_TyEnv (fst (M_CompiledInterface e)))
           |\<subseteq>| fmdom (CM_TypeSubst (fst (M_CompiledImplementation e)))"
    and "TE_TypeVars (CM_TyEnv (fst (M_CompiledImplementation e))) = {||}"
    and "subst_range_tyvars (CM_TypeSubst (fst (M_CompiledImplementation e)))
           \<subseteq> fset (funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x))
                      (map fst (entry_int_ctx ps e) @ map fst (entry_impl_ctx ps name e)
                       @ [fst (M_CompiledInterface e)])))"
    and "link_modules (map fst (entry_int_ctx ps e) @ [fst (M_CompiledInterface e)])
           = Inr L
           \<Longrightarrow> core_module_well_typed L
             \<and> elabenv_well_formed (CM_TyEnv L) (snd (M_CompiledInterface e))"
    and "link_modules (map fst (entry_int_ctx ps e) @ map fst (entry_impl_ctx ps name e)
           @ [fst (M_CompiledInterface e), fst (M_CompiledImplementation e)]) = Inr P
           \<Longrightarrow> core_module_well_typed P"
    and "merge_all_substs (map CM_TypeSubst
           (map fst (entry_int_ctx ps e) @ map fst (entry_impl_ctx ps name e)
            @ [fst (M_CompiledInterface e), fst (M_CompiledImplementation e)])) = Inr \<sigma>
           \<Longrightarrow> link_runtime_ok
                 (map fst (entry_int_ctx ps e) @ map fst (entry_impl_ctx ps name e)
                  @ [fst (M_CompiledInterface e), fst (M_CompiledImplementation e)]) \<sigma>"
    and "fmdom (TE_GlobalVars (CM_TyEnv (fst (M_CompiledInterface e))))
           |\<subseteq>| fmdom (CM_GlobalVars (fst (M_CompiledInterface e)))
                |\<union>| fmdom (CM_GlobalVars (fst (M_CompiledImplementation e)))"
    and "fmdom (TE_Functions (CM_TyEnv (fst (M_CompiledInterface e))))
           |\<subseteq>| fmdom (CM_Functions (fst (M_CompiledInterface e)))
                |\<union>| fmdom (CM_Functions (fst (M_CompiledImplementation e)))"
    and "fmdom (TE_GlobalVars (CM_TyEnv (fst (M_CompiledImplementation e))))
           |\<subseteq>| fmdom (CM_GlobalVars (fst (M_CompiledImplementation e)))"
    and "fmdom (TE_Functions (CM_TyEnv (fst (M_CompiledImplementation e))))
           |\<subseteq>| fmdom (CM_Functions (fst (M_CompiledImplementation e)))"
  using assms unfolding pipeline_entry_ok_def Let_def by blast+

lemma pipeline_state_okD:
  assumes "pipeline_state_ok ps"
      and "fmlookup ps name = Some e"
  shows "pipeline_entry_ok ps name e"
    and "d |\<in>| M_IntDeps e \<Longrightarrow> M_IntDeps (the (fmlookup ps d)) |\<subseteq>| M_IntDeps e"
    and "d |\<in>| M_ImplDeps e \<Longrightarrow> M_IntDeps (the (fmlookup ps d)) |\<subseteq>| M_ImplDeps e"
  using assms unfolding pipeline_state_ok_def by blast+

(* The fold's starting point. *)
lemma pipeline_state_ok_empty: "pipeline_state_ok fmempty"
  unfolding pipeline_state_ok_def by simp

(* A per-entry invariant survives an update at a fresh name: the dep sets
   resolve within the old domain, so the context lists - and with them
   every stored fact - are untouched, and domain membership only grows. *)
lemma pipeline_entry_ok_fmupd_fresh:
  assumes ok: "pipeline_entry_ok ps name e"
      and fresh: "new |\<notin>| fmdom ps"
  shows "pipeline_entry_ok (fmupd new x ps) name e"
proof -
  have dom_int: "M_IntDeps e |\<subseteq>| fmdom ps"
    using pipeline_entry_okD(1)[OF ok] .
  have dom_impl: "M_ImplDeps e |\<subseteq>| fmdom ps"
    using pipeline_entry_okD(2)[OF ok] .
  have int_fresh: "new |\<notin>| M_IntDeps e"
    using dom_int fresh by (meson fsubsetD)
  have impl_fresh: "new |\<notin>| M_ImplDeps e"
    using dom_impl fresh by (meson fsubsetD)
  have dom_int': "M_IntDeps e |\<subseteq>| fmdom (fmupd new x ps)"
   and dom_impl': "M_ImplDeps e |\<subseteq>| fmdom (fmupd new x ps)"
    using dom_int dom_impl
    by (metis fmdom_fmupd fsubset_finsertI order_trans)+
  show ?thesis
    using ok dom_int' dom_impl'
    unfolding pipeline_entry_ok_def Let_def
              entry_int_ctx_fmupd_fresh[OF int_fresh]
              entry_impl_ctx_fmupd_fresh[OF impl_fresh]
    by blast
qed

(* The state invariant extends by one fresh, invariant-satisfying entry
   whose dep sets are closed against the old state. This is the packaging
   pipeline_step preservation will discharge: the entry facts come from
   elab_module_well_typed, the closure premises from the closure facts of
   the imports' entries. *)
lemma pipeline_state_ok_fmupd:
  assumes ok: "pipeline_state_ok ps"
      and fresh: "new |\<notin>| fmdom ps"
      and eok: "pipeline_entry_ok (fmupd new x ps) new x"
      and closInt: "\<And>d. d |\<in>| M_IntDeps x \<Longrightarrow>
                      M_IntDeps (the (fmlookup ps d)) |\<subseteq>| M_IntDeps x"
      and closImpl: "\<And>d. \<lbrakk>d |\<in>| M_ImplDeps x; d \<noteq> new\<rbrakk> \<Longrightarrow>
                       M_IntDeps (the (fmlookup ps d)) |\<subseteq>| M_ImplDeps x"
  shows "pipeline_state_ok (fmupd new x ps)"
  unfolding pipeline_state_ok_def
proof (intro allI impI)
  fix name e
  assume lk: "fmlookup (fmupd new x ps) name = Some e"
  show "pipeline_entry_ok (fmupd new x ps) name e
        \<and> (\<forall>d. d |\<in>| M_IntDeps e \<longrightarrow>
                 M_IntDeps (the (fmlookup (fmupd new x ps) d)) |\<subseteq>| M_IntDeps e)
        \<and> (\<forall>d. d |\<in>| M_ImplDeps e \<longrightarrow>
                 M_IntDeps (the (fmlookup (fmupd new x ps) d)) |\<subseteq>| M_ImplDeps e)"
  proof (cases "name = new")
    case True
    have e_eq: "e = x"
      using lk True by simp
    have entry: "pipeline_entry_ok (fmupd new x ps) name e"
      using eok True e_eq by simp
    have self_sub: "M_IntDeps x |\<subseteq>| M_ImplDeps x"
      using pipeline_entry_okD(5)[OF eok] .
    have new_notin: "new |\<notin>| M_IntDeps x"
      using pipeline_entry_okD(3)[OF eok] .
    have closI: "\<forall>d. d |\<in>| M_IntDeps e \<longrightarrow>
                   M_IntDeps (the (fmlookup (fmupd new x ps) d)) |\<subseteq>| M_IntDeps e"
    proof (intro allI impI)
      fix d assume d_in: "d |\<in>| M_IntDeps e"
      have "d \<noteq> new"
        using d_in e_eq new_notin by auto
      then show "M_IntDeps (the (fmlookup (fmupd new x ps) d)) |\<subseteq>| M_IntDeps e"
        using closInt d_in e_eq by simp
    qed
    have closP: "\<forall>d. d |\<in>| M_ImplDeps e \<longrightarrow>
                   M_IntDeps (the (fmlookup (fmupd new x ps) d)) |\<subseteq>| M_ImplDeps e"
    proof (intro allI impI)
      fix d assume d_in: "d |\<in>| M_ImplDeps e"
      show "M_IntDeps (the (fmlookup (fmupd new x ps) d)) |\<subseteq>| M_ImplDeps e"
      proof (cases "d = new")
        case True
        then show ?thesis using self_sub e_eq by simp
      next
        case False
        then show ?thesis using closImpl d_in e_eq by simp
      qed
    qed
    show ?thesis using entry closI closP by blast
  next
    case False
    then have lk_ps: "fmlookup ps name = Some e"
      using lk by simp
    note e_ok = pipeline_state_okD(1)[OF ok lk_ps]
    have entry: "pipeline_entry_ok (fmupd new x ps) name e"
      using pipeline_entry_ok_fmupd_fresh[OF e_ok fresh] .
    have dom_int: "M_IntDeps e |\<subseteq>| fmdom ps"
      using pipeline_entry_okD(1)[OF e_ok] .
    have dom_impl: "M_ImplDeps e |\<subseteq>| fmdom ps"
      using pipeline_entry_okD(2)[OF e_ok] .
    have closI: "\<forall>d. d |\<in>| M_IntDeps e \<longrightarrow>
                   M_IntDeps (the (fmlookup (fmupd new x ps) d)) |\<subseteq>| M_IntDeps e"
    proof (intro allI impI)
      fix d assume d_in: "d |\<in>| M_IntDeps e"
      have "d \<noteq> new"
        using d_in dom_int fresh by (meson fsubsetD)
      then show "M_IntDeps (the (fmlookup (fmupd new x ps) d)) |\<subseteq>| M_IntDeps e"
        using pipeline_state_okD(2)[OF ok lk_ps] d_in by simp
    qed
    have closP: "\<forall>d. d |\<in>| M_ImplDeps e \<longrightarrow>
                   M_IntDeps (the (fmlookup (fmupd new x ps) d)) |\<subseteq>| M_ImplDeps e"
    proof (intro allI impI)
      fix d assume d_in: "d |\<in>| M_ImplDeps e"
      have "d \<noteq> new"
        using d_in dom_impl fresh by (meson fsubsetD)
      then show "M_IntDeps (the (fmlookup (fmupd new x ps) d)) |\<subseteq>| M_ImplDeps e"
        using pipeline_state_okD(3)[OF ok lk_ps] d_in by simp
    qed
    show ?thesis using entry closI closP by blast
  qed
qed


(* ========================================================================== *)
(* Interface-side link composition                                            *)
(* ========================================================================== *)

(* This section proves the fact the pipeline_step preservation proof needs
   for the A_wt / C_wt premises of elab_module_well_typed (and the final
   composition needs for its interface-side prefix links): any successful
   link of the interfaces of a dep-closed, distinct name list is well-typed
   (state_closed_link_well_typed, at the end of the section). *)

(* The interface CoreModule stored at a name. The context lists of the
   invariant are pointwise images of name lists under this map. *)
definition state_iface :: "PipelineState \<Rightarrow> string \<Rightarrow> CoreModule" where
  "state_iface ps n = fst (M_CompiledInterface (the (fmlookup ps n)))"

lemma entry_int_ctx_ifaces:
  "map fst (entry_int_ctx ps e)
     = map (state_iface ps) (sorted_list_of_fset (M_IntDeps e))"
  unfolding entry_int_ctx_def state_iface_def by simp

lemma entry_impl_ctx_ifaces:
  "map fst (entry_impl_ctx ps name e)
     = map (state_iface ps)
         (sorted_list_of_fset (M_ImplDeps e |-| M_IntDeps e |-| {|name|}))"
  unfolding entry_impl_ctx_def state_iface_def by simp

(* Every stored interface satisfies the compiled-module contract... *)
lemma state_entry_interface_ok:
  assumes ok: "pipeline_state_ok ps"
      and k: "k |\<in>| fmdom ps"
  shows "compiled_module_ok (M_CompiledInterface (the (fmlookup ps k)))"
proof -
  obtain e where lk: "fmlookup ps k = Some e"
    using k by (meson fmdomE)
  show ?thesis
    using pipeline_entry_okD(6)[OF pipeline_state_okD(1)[OF ok lk]] lk by simp
qed

(* ...whose parts, read off the interface CoreModule itself, are what the
   sublink and composition lemmas consume. *)
lemma state_iface_facts:
  assumes ok: "pipeline_state_ok ps"
      and k: "k |\<in>| fmdom ps"
  shows "CM_TypeSubst (state_iface ps k) = fmempty"
    and "core_module_invariant (state_iface ps k)"
    and "module_ghost_subsets_ok (state_iface ps k)"
proof -
  have cok: "compiled_module_ok (M_CompiledInterface (the (fmlookup ps k)))"
    using state_entry_interface_ok[OF ok k] .
  show "CM_TypeSubst (state_iface ps k) = fmempty"
    using cok unfolding compiled_module_ok_def state_iface_def by blast
  show inv: "core_module_invariant (state_iface ps k)"
    using cok unfolding compiled_module_ok_def state_iface_def by blast
  show "module_ghost_subsets_ok (state_iface ps k)"
    using core_module_invariant_ghost_subsets_ok[OF inv] .
qed

(* The empty link yields the empty module... *)
lemma link_modules_nil:
  assumes ok: "link_modules [] = Inr m"
  shows "m = empty_core_module"
proof -
  obtain \<sigma> where m_eq: "m = link_result [] \<sigma>"
    using ok link_modules_Inr_iff[of "[]" m] by blast
  have "CM_TypeSubst m = fmempty"
    using link_modules_empty_subst[OF ok] by simp
  then have \<sigma>_eq: "\<sigma> = fmempty"
    using m_eq unfolding link_result_def by simp
  show ?thesis
    unfolding m_eq \<sigma>_eq link_result_def empty_core_module_def empty_module_tyenv_def
    by simp
qed

(* ...and the empty module is well-typed: every conjunct is vacuous over
   empty maps, except the conventional return type CoreTy_Record [], which
   is well-kinded and runtime in any env. This is the base case of the
   interface-side composition (a module with no imports has an empty dep
   link). *)
lemma empty_core_module_well_typed:
  "core_module_well_typed empty_core_module"
proof -
  have subst_empty: "CM_TypeSubst empty_core_module = fmempty"
    by (simp add: empty_core_module_def)
  have norm: "normalize_module empty_core_module = empty_core_module"
    using normalize_module_id_when_empty[OF subst_empty] .
  have wf: "tyenv_well_formed empty_module_tyenv"
    unfolding tyenv_well_formed_def
              tyenv_vars_well_kinded_def tyenv_vars_runtime_def
              tyenv_ghost_vars_subset_def tyenv_return_type_well_kinded_def
              tyenv_return_type_runtime_def tyenv_ctors_consistent_def
              tyenv_payloads_well_kinded_def tyenv_ctor_tyvars_distinct_def
              tyenv_ctors_by_type_consistent_def tyenv_fun_types_well_kinded_def
              tyenv_fun_tyvars_distinct_def tyenv_fun_ghost_constraint_def
              tyenv_nonghost_payloads_runtime_def tyenv_ghost_datatypes_subset_def
              tyenv_runtime_tyvars_subset_def tyenv_abstract_types_subset_def
              tyenv_datatypes_nonempty_def empty_module_tyenv_def
    by simp
  have scope: "tyenv_module_scope empty_module_tyenv"
    unfolding tyenv_module_scope_def empty_module_tyenv_def by simp
  have nwt: "normalized_module_well_typed empty_core_module"
    unfolding normalized_module_well_typed_def
    using wf scope
    by (simp add: empty_core_module_def module_globals_well_typed_def
                  module_functions_well_typed_def)
  have inv: "core_module_invariant empty_core_module"
    unfolding core_module_invariant_def
    using capture_avoiding_empty_subst[OF subst_empty] scope
    by (simp add: empty_core_module_def empty_module_tyenv_def
                  module_ghost_subsets_ok_def)
  show ?thesis
    unfolding core_module_well_typed_def norm
    using inv nwt
    by (simp add: empty_core_module_def typesubst_well_kinded_def)
qed

(* sorted_list_of_fset yields distinct lists (the fset library has the set
   and fset_of_list equations but not this one). *)
lemma distinct_sorted_list_of_fset:
  "distinct (sorted_list_of_fset S)"
  by (simp add: sorted_list_of_fset.rep_eq)

(* A distinct name list's pointwise image is a sub-multiset of any distinct
   superlist's image - the bridge from name-set inclusion to the
   sub-multiset hypotheses of the sublink lemmas. (Set inclusion of the
   images alone would not do: distinct names can map to equal interface
   CoreModules, e.g. two empty interfaces.) *)
lemma distinct_map_submset:
  assumes d1: "distinct ns'" and d2: "distinct ns" and sub: "set ns' \<subseteq> set ns"
  shows "mset (map f ns') \<subseteq># mset (map f ns)"
proof -
  have "mset ns' \<subseteq># mset ns"
    using d1 d2 sub
    unfolding distinct_count_atmost_1 subseteq_mset_def by auto
  then show ?thesis
    by (metis image_mset_subseteq_mono mset_map)
qed

(* A finite nonempty set with a transitive irreflexive relation has a
   maximal element. Applied to the dep relation of a name list, it peels
   off a name on which nothing else in the list depends. *)
lemma finite_transitive_maximal:
  assumes fin: "finite S" and ne: "S \<noteq> {}"
      and trans: "\<And>a b c. \<lbrakk>a \<in> S; b \<in> S; c \<in> S; r a b; r b c\<rbrakk> \<Longrightarrow> r a c"
      and irrefl: "\<And>a. a \<in> S \<Longrightarrow> \<not> r a a"
  shows "\<exists>n \<in> S. \<forall>m \<in> S. \<not> r n m"
  using fin ne trans irrefl
proof (induction "card S" arbitrary: S rule: less_induct)
  case less
  obtain x where x_in: "x \<in> S" using less.prems(2) by blast
  show ?case
  proof (cases "\<forall>m \<in> S. \<not> r x m")
    case True
    then show ?thesis using x_in by blast
  next
    case False
    define T where "T = {m \<in> S. r x m}"
    have T_ne: "T \<noteq> {}" using False T_def by blast
    have T_sub: "T \<subseteq> S" using T_def by blast
    have x_notin: "x \<notin> T" using less.prems(4) x_in T_def by blast
    have T_fin: "finite T" using less.prems(1) T_sub finite_subset by blast
    have "T \<subset> S" using T_sub x_in x_notin by blast
    then have T_card: "card T < card S"
      using psubset_card_mono[OF less.prems(1)] by blast
    have transT: "\<And>a b c. \<lbrakk>a \<in> T; b \<in> T; c \<in> T; r a b; r b c\<rbrakk> \<Longrightarrow> r a c"
      using less.prems(3) T_sub by blast
    have irreflT: "\<And>a. a \<in> T \<Longrightarrow> \<not> r a a"
      using less.prems(4) T_sub by blast
    obtain n where n_in: "n \<in> T" and n_max: "\<forall>m \<in> T. \<not> r n m"
      using less.hyps[OF T_card T_fin T_ne transT irreflT] by fastforce
    have "\<forall>m \<in> S. \<not> r n m"
    proof
      fix m assume m_in: "m \<in> S"
      show "\<not> r n m"
      proof
        assume rnm: "r n m"
        have rxn: "r x n" using n_in T_def by blast
        have "r x m"
          using less.prems(3)[OF x_in _ m_in rxn rnm] n_in T_sub by blast
        then have "m \<in> T" using m_in T_def by blast
        then show False using n_max rnm by blast
      qed
    qed
    then show ?thesis using n_in T_sub by blast
  qed
qed

(* The composition: any successful link of the interfaces of a dep-closed,
   distinct name list is well-typed. The induction peels off a maximal name
   (one on which nothing else in the list depends): the rest of the list is
   still closed, so it is well-typed by induction; the peeled entry's own
   linked interface is well-typed by its stored conclusion (i); both
   sub-links succeed as interface-only sub-multisets of the given link
   (link_modules_empty_substs_sublink); and the set-union form of
   link_preserves_well_typed puts the two halves back together. *)
lemma state_closed_link_well_typed:
  assumes ok: "pipeline_state_ok ps"
      and dom0: "fset_of_list ns |\<subseteq>| fmdom ps"
      and closed0: "\<forall>n \<in> set ns. \<forall>d. d |\<in>| M_IntDeps (the (fmlookup ps n))
                      \<longrightarrow> d \<in> set ns"
      and dist0: "distinct ns"
      and linkM0: "link_modules (map (state_iface ps) ns) = Inr m"
  shows "core_module_well_typed m"
  using dom0 closed0 dist0 linkM0
proof (induction ns arbitrary: m rule: length_induct)
  case (1 ns)
  note dom = "1.prems"(1) and closed = "1.prems"(2)
   and dist = "1.prems"(3) and linkM = "1.prems"(4)
  show ?case
  proof (cases "ns = []")
    case True
    then show ?thesis
      using linkM link_modules_nil empty_core_module_well_typed by auto
  next
    case False
    define deps where "deps = (\<lambda>k. M_IntDeps (the (fmlookup ps k)))"
    have in_dom: "\<And>k. k \<in> set ns \<Longrightarrow> k |\<in>| fmdom ps"
      using dom by (metis fset_of_list_elem fsubsetD)
    \<comment> \<open>The list's dependency relation is transitive (dep sets are closed
       against their members' dep sets) and irreflexive (no entry lists its
       own name), so some listed name has no dependant in the list.\<close>
    have trans: "\<And>a b c. \<lbrakk>c \<in> set ns; a |\<in>| deps b; b |\<in>| deps c\<rbrakk> \<Longrightarrow> a |\<in>| deps c"
    proof -
      fix a b c assume c_in: "c \<in> set ns" and a_b: "a |\<in>| deps b" and b_c: "b |\<in>| deps c"
      obtain ec where lkc: "fmlookup ps c = Some ec"
        using in_dom[OF c_in] by (meson fmdomE)
      have "M_IntDeps (the (fmlookup ps b)) |\<subseteq>| M_IntDeps ec"
        using pipeline_state_okD(2)[OF ok lkc] b_c lkc unfolding deps_def by simp
      then show "a |\<in>| deps c"
        using a_b lkc unfolding deps_def by (auto simp: fsubsetD)
    qed
    have irrefl: "\<And>k. k \<in> set ns \<Longrightarrow> k |\<notin>| deps k"
    proof -
      fix k assume k_in: "k \<in> set ns"
      obtain e where lk: "fmlookup ps k = Some e"
        using in_dom[OF k_in] by (meson fmdomE)
      show "k |\<notin>| deps k"
        using pipeline_entry_okD(3)[OF pipeline_state_okD(1)[OF ok lk]] lk
        unfolding deps_def by simp
    qed
    have "\<exists>n \<in> set ns. \<forall>k \<in> set ns. \<not> n |\<in>| deps k"
    proof (rule finite_transitive_maximal)
      show "finite (set ns)" by simp
      show "set ns \<noteq> {}" using False by simp
      show "\<And>a b c. \<lbrakk>a \<in> set ns; b \<in> set ns; c \<in> set ns;
                     a |\<in>| deps b; b |\<in>| deps c\<rbrakk> \<Longrightarrow> a |\<in>| deps c"
        using trans by blast
      show "\<And>a. a \<in> set ns \<Longrightarrow> \<not> a |\<in>| deps a"
        using irrefl by blast
    qed
    then obtain n where n_in: "n \<in> set ns" and n_max: "\<forall>k \<in> set ns. n |\<notin>| deps k"
      by blast
    obtain en where lkn: "fmlookup ps n = Some en"
      using in_dom[OF n_in] by (meson fmdomE)
    have deps_n: "deps n = M_IntDeps en"
      unfolding deps_def by (simp add: lkn)
    \<comment> \<open>Split the list: the peeled name with its dep closure, and the rest.\<close>
    define ns' where "ns' = remove1 n ns"
    define dn where "dn = sorted_list_of_fset (deps n) @ [n]"
    have set_ns': "set ns' = set ns - {n}"
      unfolding ns'_def using dist by simp
    have dist_ns': "distinct ns'"
      unfolding ns'_def using dist by simp
    have len_ns': "length ns' < length ns"
      unfolding ns'_def using n_in
      by (simp add: dist distinct_remove1_removeAll length_removeAll_less)
    have dist_dn: "distinct dn"
      unfolding dn_def
      using distinct_sorted_list_of_fset irrefl[OF n_in] by auto
    have dn_sub: "set dn \<subseteq> set ns"
      using closed n_in unfolding dn_def deps_def by auto
    \<comment> \<open>Both sub-lists' links succeed: interface-only sub-multisets of the
       given link's inputs.\<close>
    have empty_sub: "\<forall>x \<in> set (map (state_iface ps) ks). CM_TypeSubst x = fmempty"
      if "set ks \<subseteq> set ns" for ks
      using state_iface_facts(1)[OF ok] in_dom that by auto
    have msub_ns': "mset (map (state_iface ps) ns') \<subseteq># mset (map (state_iface ps) ns)"
      using distinct_map_submset[OF dist_ns' dist] set_ns' by auto
    have emptyA: "\<forall>x \<in> set (map (state_iface ps) ns'). CM_TypeSubst x = fmempty"
      using empty_sub set_ns' by blast
    obtain a where linkA: "link_modules (map (state_iface ps) ns') = Inr a"
      using link_modules_empty_substs_sublink[OF linkM emptyA msub_ns'] by blast
    have msub_dn: "mset (map (state_iface ps) dn) \<subseteq># mset (map (state_iface ps) ns)"
      using distinct_map_submset[OF dist_dn dist dn_sub] .
    have emptyB: "\<forall>x \<in> set (map (state_iface ps) dn). CM_TypeSubst x = fmempty"
      using empty_sub dn_sub by blast
    obtain b where linkB: "link_modules (map (state_iface ps) dn) = Inr b"
      using link_modules_empty_substs_sublink[OF linkM emptyB msub_dn] by blast
    \<comment> \<open>The rest of the list is still closed - by maximality, nothing in it
       depends on the peeled name - so the induction hypothesis applies.\<close>
    have dom_ns': "fset_of_list ns' |\<subseteq>| fmdom ps"
      using in_dom set_ns' by (metis DiffD1 fset_of_list_elem fsubsetI)
    have closed_ns': "\<forall>k \<in> set ns'. \<forall>d. d |\<in>| M_IntDeps (the (fmlookup ps k))
                        \<longrightarrow> d \<in> set ns'"
    proof (intro ballI allI impI)
      fix k d assume k_in: "k \<in> set ns'" and d_in: "d |\<in>| M_IntDeps (the (fmlookup ps k))"
      have k_ns: "k \<in> set ns" using k_in set_ns' by blast
      have d_ns: "d \<in> set ns" using closed k_ns d_in by blast
      have "d \<noteq> n" using n_max k_ns d_in unfolding deps_def by blast
      then show "d \<in> set ns'" using d_ns set_ns' by blast
    qed
    have wtA: "core_module_well_typed a"
      using "1.IH" len_ns' dom_ns' closed_ns' dist_ns' linkA by blast
    \<comment> \<open>The peeled entry's link is exactly its stored conclusion (i).\<close>
    have bs_eq: "map fst (entry_int_ctx ps en) @ [fst (M_CompiledInterface en)]
                   = map (state_iface ps) dn"
      unfolding dn_def deps_n entry_int_ctx_ifaces
      by (simp add: state_iface_def lkn)
    have wtB: "core_module_well_typed b"
      using pipeline_entry_okD(12)[OF pipeline_state_okD(1)[OF ok lkn],
              unfolded bs_eq, OF linkB]
      by blast
    \<comment> \<open>Reassemble with the set-union form of link_preserves_well_typed.\<close>
    have setMS: "set (map (state_iface ps) ns)
                   = set (map (state_iface ps) ns') \<union> set (map (state_iface ps) dn)"
    proof -
      have "set ns = set ns' \<union> set dn"
        using set_ns' dn_sub n_in unfolding dn_def by auto
      then show ?thesis by (simp add: image_Un)
    qed
    have ghostOK: "\<forall>x \<in> set (map (state_iface ps) ns). module_ghost_subsets_ok x"
      using state_iface_facts(3)[OF ok] in_dom by auto
    show ?thesis
      using link_preserves_well_typed[OF linkA wtA linkB wtB linkM setMS ghostOK] .
  qed
qed


(* ========================================================================== *)
(* Interface-side ElabEnv well-formedness                                     *)
(* ========================================================================== *)

(* The eeA/eeC discharger: over the link of the interfaces of a dep-closed,
   distinct name list, every listed module's stored ElabEnv delta is
   well-formed. The non-inductive sibling of state_closed_link_well_typed:
   the member's own A-link (its dep interfaces plus itself) succeeds as an
   interface-only sub-multiset of the given link, its stored conclusion (iii)
   gives well-formedness over that sub-link's env, and
   elabenv_well_formed_link_mono transfers it to the whole link's env. *)
lemma state_closed_link_ee_wf:
  assumes ok: "pipeline_state_ok ps"
      and dom0: "fset_of_list ns |\<subseteq>| fmdom ps"
      and closed0: "\<forall>n \<in> set ns. \<forall>d. d |\<in>| M_IntDeps (the (fmlookup ps n))
                      \<longrightarrow> d \<in> set ns"
      and dist0: "distinct ns"
      and linkM: "link_modules (map (state_iface ps) ns) = Inr m"
      and k_in: "k \<in> set ns"
  shows "elabenv_well_formed (CM_TyEnv m)
           (snd (M_CompiledInterface (the (fmlookup ps k))))"
proof -
  have in_dom: "\<And>n. n \<in> set ns \<Longrightarrow> n |\<in>| fmdom ps"
    using dom0 by (metis fset_of_list_elem fsubsetD)
  obtain ek where lkk: "fmlookup ps k = Some ek"
    using in_dom[OF k_in] by (meson fmdomE)
  define dk where "dk = sorted_list_of_fset (M_IntDeps ek) @ [k]"
  have k_notin: "k |\<notin>| M_IntDeps ek"
    using pipeline_entry_okD(3)[OF pipeline_state_okD(1)[OF ok lkk]] .
  have dist_dk: "distinct dk"
    unfolding dk_def using distinct_sorted_list_of_fset k_notin by auto
  have dk_sub: "set dk \<subseteq> set ns"
    unfolding dk_def using closed0 k_in lkk by auto
  have empties: "\<forall>x \<in> set (map (state_iface ps) ns). CM_TypeSubst x = fmempty"
    using state_iface_facts(1)[OF ok] in_dom by auto
  have empties_dk: "\<forall>x \<in> set (map (state_iface ps) dk). CM_TypeSubst x = fmempty"
    using empties dk_sub by auto
  have msub: "mset (map (state_iface ps) dk) \<subseteq># mset (map (state_iface ps) ns)"
    using distinct_map_submset[OF dist_dk dist0 dk_sub] .
  obtain L where linkK: "link_modules (map (state_iface ps) dk) = Inr L"
    using link_modules_empty_substs_sublink[OF linkM empties_dk msub] by blast
  have bs_eq: "map fst (entry_int_ctx ps ek) @ [fst (M_CompiledInterface ek)]
                 = map (state_iface ps) dk"
    unfolding dk_def entry_int_ctx_ifaces
    by (simp add: state_iface_def lkk)
  have wfL: "elabenv_well_formed (CM_TyEnv L) (snd (M_CompiledInterface ek))"
    using pipeline_entry_okD(12)[OF pipeline_state_okD(1)[OF ok lkk],
            unfolded bs_eq, OF linkK]
    by blast
  have nv: "\<not> EE_CurrentFunctionVoid (snd (M_CompiledInterface ek))"
    using state_entry_interface_ok[OF ok in_dom[OF k_in]] lkk
    unfolding compiled_module_ok_def by simp
  have sub: "set (map (state_iface ps) dk) \<subseteq> set (map (state_iface ps) ns)"
    using dk_sub by auto
  show ?thesis
    using elabenv_well_formed_link_mono[OF linkK linkM empties sub wfL nv]
    by (simp add: lkk)
qed


(* ========================================================================== *)
(* Dependency sets of a fold step                                             *)
(* ========================================================================== *)

(* Membership in a face's dependency set: an import itself, or a member of
   an import's own (already transitively closed) interface-dep set. Phrased
   over pointwise-mapped entry lists, the form lookup_entries_eq supplies. *)
lemma face_dep_set_member:
  "d |\<in>| face_dep_set ns (map f ns) \<longleftrightarrow>
     (\<exists>n \<in> set ns. d = n \<or> d |\<in>| M_IntDeps (f n))"
  by (induction ns) (auto simp: face_dep_set_def)

(* Under the state invariant, a face's dep set resolves in the state... *)
lemma face_dep_set_dom:
  assumes ok: "pipeline_state_ok ps"
      and lk: "lookup_entries ps ns = Inr es"
  shows "face_dep_set ns es |\<subseteq>| fmdom ps"
proof
  fix d assume d_in: "d |\<in>| face_dep_set ns es"
  have es_eq: "es = map (\<lambda>n. the (fmlookup ps n)) ns"
    using lookup_entries_eq[OF lk] .
  obtain n where n_in: "n \<in> set ns"
      and n_case: "d = n \<or> d |\<in>| M_IntDeps (the (fmlookup ps n))"
    using d_in unfolding es_eq face_dep_set_member by blast
  have n_dom: "n |\<in>| fmdom ps"
    using lookup_entries_dom[OF lk] n_in by blast
  from n_case show "d |\<in>| fmdom ps"
  proof
    assume "d = n"
    then show ?thesis using n_dom by simp
  next
    assume d_dep: "d |\<in>| M_IntDeps (the (fmlookup ps n))"
    obtain en where lkn: "fmlookup ps n = Some en"
      using n_dom by (meson fmdomE)
    show ?thesis
      using pipeline_entry_okD(1)[OF pipeline_state_okD(1)[OF ok lkn]] d_dep lkn
      by (auto dest: fsubsetD)
  qed
qed

(* ...and is itself transitively closed: a member's own interface-dep set is
   contained in it. This is what seeds both the new entry's closure facts and
   the dep-closedness of the step's link contexts. *)
lemma face_dep_set_closed:
  assumes ok: "pipeline_state_ok ps"
      and lk: "lookup_entries ps ns = Inr es"
      and d_in: "d |\<in>| face_dep_set ns es"
  shows "M_IntDeps (the (fmlookup ps d)) |\<subseteq>| face_dep_set ns es"
proof -
  have es_eq: "es = map (\<lambda>n. the (fmlookup ps n)) ns"
    using lookup_entries_eq[OF lk] .
  have self_sub: "M_IntDeps (the (fmlookup ps n)) |\<subseteq>| face_dep_set ns es"
    if n_in: "n \<in> set ns" for n
  proof
    fix y assume "y |\<in>| M_IntDeps (the (fmlookup ps n))"
    then show "y |\<in>| face_dep_set ns es"
      unfolding es_eq face_dep_set_member using n_in by blast
  qed
  obtain n where n_in: "n \<in> set ns"
      and n_case: "d = n \<or> d |\<in>| M_IntDeps (the (fmlookup ps n))"
    using d_in unfolding es_eq face_dep_set_member by blast
  from n_case show ?thesis
  proof
    assume "d = n"
    then show ?thesis using self_sub[OF n_in] by simp
  next
    assume d_dep: "d |\<in>| M_IntDeps (the (fmlookup ps n))"
    have n_dom: "n |\<in>| fmdom ps"
      using lookup_entries_dom[OF lk] n_in by blast
    obtain en where lkn: "fmlookup ps n = Some en"
      using n_dom by (meson fmdomE)
    have "M_IntDeps (the (fmlookup ps d)) |\<subseteq>| M_IntDeps en"
      using pipeline_state_okD(2)[OF ok lkn] d_dep lkn by simp
    moreover have "M_IntDeps en |\<subseteq>| face_dep_set ns es"
      using self_sub[OF n_in] lkn by simp
    ultimately show ?thesis by (rule order_trans)
  qed
qed


(* ========================================================================== *)
(* pipeline_step preservation                                                 *)
(* ========================================================================== *)

(* The elimination rule for pipeline_step success: names every intermediate
   object of the step and records the equations defining them. *)
lemma pipeline_step_Inr_elim:
  assumes step: "pipeline_step ps bm = Inr ps'"
  obtains intEntries implEntries intDeps implDeps implOnly intCtx implCtx
          compInt compImpl
  where
    "lookup_entries ps (map Imp_ModuleName (Mod_InterfaceImports bm))
       = Inr intEntries"
    "lookup_entries ps (map Imp_ModuleName (Mod_ImplementationImports bm))
       = Inr implEntries"
    "intDeps = face_dep_set (map Imp_ModuleName (Mod_InterfaceImports bm)) intEntries"
    "implDeps = finsert (Mod_Name bm) (intDeps |\<union>|
       face_dep_set (map Imp_ModuleName (Mod_ImplementationImports bm)) implEntries)"
    "implOnly = implDeps |-| intDeps |-| {|Mod_Name bm|}"
    "lookup_entries ps (sorted_list_of_fset intDeps) = Inr intCtx"
    "lookup_entries ps (sorted_list_of_fset implOnly) = Inr implCtx"
    "elab_module bm (map M_CompiledInterface intCtx) (map M_CompiledInterface implCtx)
       = Inr (compInt, compImpl)"
    "ps' = fmupd (Mod_Name bm)
             \<lparr> M_InterfaceImports = map Imp_ModuleName (Mod_InterfaceImports bm),
               M_ImplementationImports = map Imp_ModuleName (Mod_ImplementationImports bm),
               M_IntDeps = intDeps, M_ImplDeps = implDeps,
               M_CompiledInterface = compInt, M_CompiledImplementation = compImpl \<rparr>
             ps"
  using assms unfolding pipeline_step_def Let_def
  by (auto split: sum.splits prod.splits)

(* One fold step preserves the invariant. The freshness premise comes from
   analyze_dependencies (distinct names, dependencies first), the two
   metavariable-freshness premises from the renamer's naming discipline; the
   extra conclusions are the bookkeeping the pipeline_fold induction carries
   (domain growth, stability of old entries, and the new entry's dep sets
   resolving among the modules processed before it). *)
lemma pipeline_step_preserves:
  assumes ok: "pipeline_state_ok ps"
      and step: "pipeline_step ps bm = Inr ps'"
      and fresh: "Mod_Name bm |\<notin>| fmdom ps"
      and fresh_int: "list_all decl_tyvars_fresh_ok (Mod_Interface bm)"
      and fresh_impl: "list_all decl_tyvars_fresh_ok (Mod_Implementation bm)"
  shows "pipeline_state_ok ps'"
    and "fmdom ps' = finsert (Mod_Name bm) (fmdom ps)"
    and "k \<noteq> Mod_Name bm \<Longrightarrow> fmlookup ps' k = fmlookup ps k"
    and "M_IntDeps (the (fmlookup ps' (Mod_Name bm))) |\<subseteq>| fmdom ps"
    and "M_ImplDeps (the (fmlookup ps' (Mod_Name bm)))
           |\<subseteq>| finsert (Mod_Name bm) (fmdom ps)"
proof -
  obtain intEntries implEntries intDeps implDeps implOnly intCtx implCtx
         compInt compImpl
    where lkIntE: "lookup_entries ps (map Imp_ModuleName (Mod_InterfaceImports bm))
             = Inr intEntries"
      and lkImplE: "lookup_entries ps (map Imp_ModuleName (Mod_ImplementationImports bm))
             = Inr implEntries"
      and intDeps_eq: "intDeps
             = face_dep_set (map Imp_ModuleName (Mod_InterfaceImports bm)) intEntries"
      and implDeps_eq: "implDeps = finsert (Mod_Name bm) (intDeps |\<union>|
             face_dep_set (map Imp_ModuleName (Mod_ImplementationImports bm)) implEntries)"
      and implOnly_eq: "implOnly = implDeps |-| intDeps |-| {|Mod_Name bm|}"
      and lkIntC: "lookup_entries ps (sorted_list_of_fset intDeps) = Inr intCtx"
      and lkImplC: "lookup_entries ps (sorted_list_of_fset implOnly) = Inr implCtx"
      and elabEq: "elab_module bm (map M_CompiledInterface intCtx)
             (map M_CompiledInterface implCtx) = Inr (compInt, compImpl)"
      and ps'_eq: "ps' = fmupd (Mod_Name bm)
             \<lparr> M_InterfaceImports = map Imp_ModuleName (Mod_InterfaceImports bm),
               M_ImplementationImports = map Imp_ModuleName (Mod_ImplementationImports bm),
               M_IntDeps = intDeps, M_ImplDeps = implDeps,
               M_CompiledInterface = compInt, M_CompiledImplementation = compImpl \<rparr>
             ps"
    using step by (rule pipeline_step_Inr_elim)

  define x where "x =
    \<lparr> M_InterfaceImports = map Imp_ModuleName (Mod_InterfaceImports bm),
      M_ImplementationImports = map Imp_ModuleName (Mod_ImplementationImports bm),
      M_IntDeps = intDeps, M_ImplDeps = implDeps,
      M_CompiledInterface = compInt, M_CompiledImplementation = compImpl \<rparr>"
  have ps'_x: "ps' = fmupd (Mod_Name bm) x ps"
    using ps'_eq unfolding x_def .
  have x_proj: "M_IntDeps x = intDeps" "M_ImplDeps x = implDeps"
    "M_CompiledInterface x = compInt" "M_CompiledImplementation x = compImpl"
    unfolding x_def by simp_all

  \<comment> \<open>Dep-set domain, freshness and closure bookkeeping.\<close>
  have dom_int: "intDeps |\<subseteq>| fmdom ps"
    unfolding intDeps_eq using face_dep_set_dom[OF ok lkIntE] .
  have dom_S2: "face_dep_set (map Imp_ModuleName (Mod_ImplementationImports bm))
                  implEntries |\<subseteq>| fmdom ps"
    using face_dep_set_dom[OF ok lkImplE] .
  have int_sub_impl: "intDeps |\<subseteq>| implDeps"
    unfolding implDeps_eq by auto
  have dom_impl_minus: "implDeps |-| {|Mod_Name bm|} |\<subseteq>| fmdom ps"
    unfolding implDeps_eq using dom_int dom_S2 by (auto dest: fsubsetD)
  have name_notin_int: "Mod_Name bm |\<notin>| intDeps"
    using dom_int fresh by (meson fsubsetD)
  have name_in_impl: "Mod_Name bm |\<in>| implDeps"
    unfolding implDeps_eq by simp
  have dom_implOnly: "implOnly |\<subseteq>| fmdom ps"
    unfolding implOnly_eq using dom_impl_minus by (auto dest: fsubsetD)

  have closInt: "\<And>d. d |\<in>| intDeps \<Longrightarrow> M_IntDeps (the (fmlookup ps d)) |\<subseteq>| intDeps"
    unfolding intDeps_eq using face_dep_set_closed[OF ok lkIntE] by blast
  have closImpl: "\<And>d. \<lbrakk>d |\<in>| implDeps; d \<noteq> Mod_Name bm\<rbrakk>
                    \<Longrightarrow> M_IntDeps (the (fmlookup ps d)) |\<subseteq>| implDeps"
  proof -
    fix d assume d_in: "d |\<in>| implDeps" and d_ne: "d \<noteq> Mod_Name bm"
    have "d |\<in>| intDeps \<or> d |\<in>| face_dep_set
            (map Imp_ModuleName (Mod_ImplementationImports bm)) implEntries"
      using d_in d_ne unfolding implDeps_eq by auto
    then show "M_IntDeps (the (fmlookup ps d)) |\<subseteq>| implDeps"
    proof
      assume "d |\<in>| intDeps"
      then have "M_IntDeps (the (fmlookup ps d)) |\<subseteq>| intDeps"
        by (rule closInt)
      then show ?thesis using int_sub_impl by (rule order_trans)
    next
      assume d_in2: "d |\<in>| face_dep_set
                       (map Imp_ModuleName (Mod_ImplementationImports bm)) implEntries"
      have "M_IntDeps (the (fmlookup ps d)) |\<subseteq>| face_dep_set
              (map Imp_ModuleName (Mod_ImplementationImports bm)) implEntries"
        using face_dep_set_closed[OF ok lkImplE d_in2] .
      then show ?thesis unfolding implDeps_eq by (auto dest: fsubsetD)
    qed
  qed
  have deps_in_dom: "\<And>d. d |\<in>| fmdom ps
                      \<Longrightarrow> M_IntDeps (the (fmlookup ps d)) |\<subseteq>| fmdom ps"
  proof -
    fix d assume "d |\<in>| fmdom ps"
    then obtain e where lk: "fmlookup ps d = Some e" by (meson fmdomE)
    show "M_IntDeps (the (fmlookup ps d)) |\<subseteq>| fmdom ps"
      using pipeline_entry_okD(1)[OF pipeline_state_okD(1)[OF ok lk]] lk by simp
  qed
  have closImplMinus: "\<And>d. d |\<in>| implDeps |-| {|Mod_Name bm|}
        \<Longrightarrow> M_IntDeps (the (fmlookup ps d)) |\<subseteq>| implDeps |-| {|Mod_Name bm|}"
  proof -
    fix d assume d_in: "d |\<in>| implDeps |-| {|Mod_Name bm|}"
    have d1: "d |\<in>| implDeps" and d2: "d \<noteq> Mod_Name bm"
      using d_in by auto
    have sub1: "M_IntDeps (the (fmlookup ps d)) |\<subseteq>| implDeps"
      using closImpl[OF d1 d2] .
    have "M_IntDeps (the (fmlookup ps d)) |\<subseteq>| fmdom ps"
      using deps_in_dom dom_impl_minus d_in by (meson fsubsetD)
    then have "Mod_Name bm |\<notin>| M_IntDeps (the (fmlookup ps d))"
      using fresh by (meson fsubsetD)
    then show "M_IntDeps (the (fmlookup ps d)) |\<subseteq>| implDeps |-| {|Mod_Name bm|}"
      using sub1 by (auto dest: fsubsetD)
  qed

  \<comment> \<open>The two link-context name lists: the A-list (interface deps) and the
     C-list (all deps of the implementation face except the module itself).\<close>
  have setC_iff: "a \<in> set (sorted_list_of_fset intDeps @ sorted_list_of_fset implOnly)
                  \<longleftrightarrow> a |\<in>| implDeps \<and> a \<noteq> Mod_Name bm" for a
    unfolding implOnly_eq
    using int_sub_impl name_notin_int by (auto dest: fsubsetD)

  have intCtx_eq: "intCtx = map (\<lambda>n. the (fmlookup ps n)) (sorted_list_of_fset intDeps)"
    using lookup_entries_eq[OF lkIntC] .
  have implCtx_eq: "implCtx = map (\<lambda>n. the (fmlookup ps n)) (sorted_list_of_fset implOnly)"
    using lookup_entries_eq[OF lkImplC] .
  have ifacesA: "map fst (map M_CompiledInterface intCtx)
                   = map (state_iface ps) (sorted_list_of_fset intDeps)"
    unfolding intCtx_eq state_iface_def by simp
  have ifacesI: "map fst (map M_CompiledInterface implCtx)
                   = map (state_iface ps) (sorted_list_of_fset implOnly)"
    unfolding implCtx_eq state_iface_def by simp

  have domA: "fset_of_list (sorted_list_of_fset intDeps) |\<subseteq>| fmdom ps"
    using dom_int by simp
  have closedA: "\<forall>n \<in> set (sorted_list_of_fset intDeps). \<forall>d.
       d |\<in>| M_IntDeps (the (fmlookup ps n)) \<longrightarrow> d \<in> set (sorted_list_of_fset intDeps)"
  proof (intro ballI allI impI)
    fix n d
    assume n_in: "n \<in> set (sorted_list_of_fset intDeps)"
       and d_in: "d |\<in>| M_IntDeps (the (fmlookup ps n))"
    have "n |\<in>| intDeps" using n_in by simp
    then have "M_IntDeps (the (fmlookup ps n)) |\<subseteq>| intDeps" by (rule closInt)
    then show "d \<in> set (sorted_list_of_fset intDeps)"
      using d_in by (auto dest: fsubsetD)
  qed
  have distA: "distinct (sorted_list_of_fset intDeps)"
    by (rule distinct_sorted_list_of_fset)

  have domC: "fset_of_list (sorted_list_of_fset intDeps
                @ sorted_list_of_fset implOnly) |\<subseteq>| fmdom ps"
    using dom_int dom_implOnly by (auto simp: fset_of_list_elem dest: fsubsetD)
  have closedC: "\<forall>n \<in> set (sorted_list_of_fset intDeps @ sorted_list_of_fset implOnly).
       \<forall>d. d |\<in>| M_IntDeps (the (fmlookup ps n))
           \<longrightarrow> d \<in> set (sorted_list_of_fset intDeps @ sorted_list_of_fset implOnly)"
  proof (intro ballI allI impI)
    fix n d
    assume n_in: "n \<in> set (sorted_list_of_fset intDeps @ sorted_list_of_fset implOnly)"
       and d_in: "d |\<in>| M_IntDeps (the (fmlookup ps n))"
    have n': "n |\<in>| implDeps |-| {|Mod_Name bm|}"
      using setC_iff n_in by auto
    have "d |\<in>| implDeps |-| {|Mod_Name bm|}"
      using closImplMinus[OF n'] d_in by (meson fsubsetD)
    then show "d \<in> set (sorted_list_of_fset intDeps @ sorted_list_of_fset implOnly)"
      using setC_iff by auto
  qed
  have distC: "distinct (sorted_list_of_fset intDeps @ sorted_list_of_fset implOnly)"
    by (auto simp: implOnly_eq distinct_sorted_list_of_fset)

  \<comment> \<open>Discharge the premises of elab_module_well_typed from the invariant.\<close>
  obtain intMod intEE where compInt_eq: "compInt = (intMod, intEE)"
    by (cases compInt)
  obtain implMod implEE where compImpl_eq: "compImpl = (implMod, implEE)"
    by (cases compImpl)
  have elab': "elab_module bm (map M_CompiledInterface intCtx)
                 (map M_CompiledInterface implCtx)
                 = Inr ((intMod, intEE), (implMod, implEE))"
    using elabEq unfolding compInt_eq compImpl_eq .

  have deps_ok: "\<forall>d \<in> set (map M_CompiledInterface intCtx
                   @ map M_CompiledInterface implCtx). compiled_module_ok d"
  proof
    fix d assume "d \<in> set (map M_CompiledInterface intCtx
                    @ map M_CompiledInterface implCtx)"
    then obtain n where
        n_in: "n \<in> set (sorted_list_of_fset intDeps @ sorted_list_of_fset implOnly)"
        and d_eq: "d = M_CompiledInterface (the (fmlookup ps n))"
      unfolding intCtx_eq implCtx_eq by auto
    have "n |\<in>| fmdom ps"
      using setC_iff n_in dom_impl_minus by (auto dest: fsubsetD)
    then show "compiled_module_ok d"
      using state_entry_interface_ok[OF ok] d_eq by blast
  qed

  have A_wt: "\<And>a. link_modules (map fst (map M_CompiledInterface intCtx)) = Inr a
                \<Longrightarrow> core_module_well_typed a"
    unfolding ifacesA
    using state_closed_link_well_typed[OF ok domA closedA distA] by blast
  have C_wt: "\<And>c. link_modules (map fst (map M_CompiledInterface intCtx)
                    @ map fst (map M_CompiledInterface implCtx)) = Inr c
                \<Longrightarrow> core_module_well_typed c"
    unfolding ifacesA ifacesI map_append[symmetric]
    using state_closed_link_well_typed[OF ok domC closedC distC] by blast

  have eeA: "\<And>a. link_modules (map fst (map M_CompiledInterface intCtx)) = Inr a
               \<Longrightarrow> \<forall>d \<in> set (map M_CompiledInterface intCtx).
                     elabenv_well_formed (CM_TyEnv a) (snd d)"
  proof (intro ballI)
    fix a d
    assume linkA: "link_modules (map fst (map M_CompiledInterface intCtx)) = Inr a"
       and d_in: "d \<in> set (map M_CompiledInterface intCtx)"
    obtain n where n_in: "n \<in> set (sorted_list_of_fset intDeps)"
        and d_eq: "d = M_CompiledInterface (the (fmlookup ps n))"
      using d_in unfolding intCtx_eq by auto
    show "elabenv_well_formed (CM_TyEnv a) (snd d)"
      using state_closed_link_ee_wf[OF ok domA closedA distA
              linkA[unfolded ifacesA] n_in]
      by (simp add: d_eq)
  qed
  have eeC: "\<And>c. link_modules (map fst (map M_CompiledInterface intCtx)
                   @ map fst (map M_CompiledInterface implCtx)) = Inr c
               \<Longrightarrow> \<forall>d \<in> set (map M_CompiledInterface intCtx
                              @ map M_CompiledInterface implCtx).
                     elabenv_well_formed (CM_TyEnv c) (snd d)"
  proof (intro ballI)
    fix c d
    assume linkC: "link_modules (map fst (map M_CompiledInterface intCtx)
                     @ map fst (map M_CompiledInterface implCtx)) = Inr c"
       and d_in: "d \<in> set (map M_CompiledInterface intCtx
                            @ map M_CompiledInterface implCtx)"
    obtain n where
        n_in: "n \<in> set (sorted_list_of_fset intDeps @ sorted_list_of_fset implOnly)"
        and d_eq: "d = M_CompiledInterface (the (fmlookup ps n))"
      using d_in unfolding intCtx_eq implCtx_eq by auto
    show "elabenv_well_formed (CM_TyEnv c) (snd d)"
      using state_closed_link_ee_wf[OF ok domC closedC distC
              linkC[unfolded ifacesA ifacesI map_append[symmetric]] n_in]
      by (simp add: d_eq)
  qed

  note emwt = elab_module_well_typed[OF elab' deps_ok A_wt C_wt eeA eeC
                fresh_int fresh_impl]
  note defsc = elab_module_defs_complete[OF elab']

  \<comment> \<open>The new entry's invariant: its state-derived context lists are exactly
     the lists handed to elab_module, and the update does not disturb them.\<close>
  have int_ctx_x: "entry_int_ctx ps x = map M_CompiledInterface intCtx"
    unfolding entry_int_ctx_def x_proj intCtx_eq by simp
  have impl_ctx_x: "entry_impl_ctx ps (Mod_Name bm) x = map M_CompiledInterface implCtx"
    unfolding entry_impl_ctx_def x_proj implOnly_eq[symmetric] implCtx_eq by simp
  have int_ctx_x': "entry_int_ctx (fmupd (Mod_Name bm) x ps) x = entry_int_ctx ps x"
    by (rule entry_int_ctx_fmupd_fresh) (simp add: x_proj name_notin_int)
  have impl_ctx_x': "entry_impl_ctx (fmupd (Mod_Name bm) x ps) (Mod_Name bm) x
                       = entry_impl_ctx ps (Mod_Name bm) x"
    unfolding entry_impl_ctx_def map_eq_conv by auto

  have dom1: "intDeps |\<subseteq>| fmdom (fmupd (Mod_Name bm) x ps)"
    using dom_int by (metis fmdom_fmupd fsubset_finsertI order_trans)
  have dom2: "implDeps |\<subseteq>| fmdom (fmupd (Mod_Name bm) x ps)"
    unfolding implDeps_eq using dom_int dom_S2 by (auto dest: fsubsetD)

  have eok: "pipeline_entry_ok (fmupd (Mod_Name bm) x ps) (Mod_Name bm) x"
    unfolding pipeline_entry_ok_def Let_def
    unfolding int_ctx_x' impl_ctx_x' int_ctx_x impl_ctx_x x_proj
              compInt_eq compImpl_eq fst_conv snd_conv
    using dom1 dom2 name_notin_int name_in_impl int_sub_impl emwt defsc
    by blast

  have ok': "pipeline_state_ok (fmupd (Mod_Name bm) x ps)"
  proof (rule pipeline_state_ok_fmupd[OF ok fresh eok])
    fix d assume "d |\<in>| M_IntDeps x"
    then have d1: "d |\<in>| intDeps" by (simp add: x_proj)
    show "M_IntDeps (the (fmlookup ps d)) |\<subseteq>| M_IntDeps x"
      using closInt[OF d1] by (simp add: x_proj)
  next
    fix d assume "d |\<in>| M_ImplDeps x" and d_ne: "d \<noteq> Mod_Name bm"
    then have d1: "d |\<in>| implDeps" by (simp add: x_proj)
    show "M_IntDeps (the (fmlookup ps d)) |\<subseteq>| M_ImplDeps x"
      using closImpl[OF d1 d_ne] by (simp add: x_proj)
  qed

  show "pipeline_state_ok ps'"
    using ok' unfolding ps'_x .
  show "fmdom ps' = finsert (Mod_Name bm) (fmdom ps)"
    unfolding ps'_x by simp
  show "k \<noteq> Mod_Name bm \<Longrightarrow> fmlookup ps' k = fmlookup ps k"
    unfolding ps'_x by simp
  show "M_IntDeps (the (fmlookup ps' (Mod_Name bm))) |\<subseteq>| fmdom ps"
    unfolding ps'_x using dom_int by (simp add: x_proj)
  show "M_ImplDeps (the (fmlookup ps' (Mod_Name bm)))
          |\<subseteq>| finsert (Mod_Name bm) (fmdom ps)"
    unfolding ps'_x implDeps_eq
    using dom_int dom_S2 by (auto simp: x_proj implDeps_eq dest: fsubsetD)
qed


(* ========================================================================== *)
(* The pipeline_fold induction                                                *)
(* ========================================================================== *)

(* Folding pipeline_step down a list of fresh, distinctly named modules
   preserves the invariant, and yields the fold bookkeeping the final
   composition consumes: the domain is the old one plus the new names, old
   entries are untouched, and the i-th module's dep sets resolve among the
   old domain plus the names processed up to (for M_IntDeps: strictly
   before) it - the processing-order fact the final state alone cannot
   recover, phrased positionally over the (dependency-sorted) input list. *)
lemma pipeline_fold_invariant:
  assumes "pipeline_state_ok ps"
      and "pipeline_fold ps bms = Inr ps'"
      and "\<forall>bm \<in> set bms. Mod_Name bm |\<notin>| fmdom ps"
      and "distinct (map Mod_Name bms)"
      and "\<forall>bm \<in> set bms. list_all decl_tyvars_fresh_ok (Mod_Interface bm)
             \<and> list_all decl_tyvars_fresh_ok (Mod_Implementation bm)"
  shows "pipeline_state_ok ps'
       \<and> fmdom ps' = fmdom ps |\<union>| fset_of_list (map Mod_Name bms)
       \<and> (\<forall>k. k |\<in>| fmdom ps \<longrightarrow> fmlookup ps' k = fmlookup ps k)
       \<and> (\<forall>i < length bms.
            M_IntDeps (the (fmlookup ps' (Mod_Name (bms ! i))))
              |\<subseteq>| fmdom ps |\<union>| fset_of_list (map Mod_Name (take i bms)))
       \<and> (\<forall>i < length bms.
            M_ImplDeps (the (fmlookup ps' (Mod_Name (bms ! i))))
              |\<subseteq>| fmdom ps |\<union>| fset_of_list (map Mod_Name (take (Suc i) bms)))"
  using assms
proof (induction bms arbitrary: ps)
  case Nil
  then show ?case by (simp add: funion_fempty_right)
next
  case (Cons bm rest)
  obtain ps1 where step: "pipeline_step ps bm = Inr ps1"
      and fold': "pipeline_fold ps1 rest = Inr ps'"
    using Cons.prems(2) by (auto split: sum.splits)
  have name_fresh: "Mod_Name bm |\<notin>| fmdom ps"
    using Cons.prems(3) by simp
  have fi: "list_all decl_tyvars_fresh_ok (Mod_Interface bm)"
   and fim: "list_all decl_tyvars_fresh_ok (Mod_Implementation bm)"
    using Cons.prems(5) by simp_all
  note sp = pipeline_step_preserves[OF Cons.prems(1) step name_fresh fi fim]
  \<comment> \<open>The step's output satisfies the induction hypothesis' premises.\<close>
  have fresh1: "\<forall>bm' \<in> set rest. Mod_Name bm' |\<notin>| fmdom ps1"
  proof
    fix bm' assume in_rest: "bm' \<in> set rest"
    have "Mod_Name bm' \<noteq> Mod_Name bm"
      using Cons.prems(4) in_rest by (metis distinct.simps(2) imageI list.simps(9) set_map)
    moreover have "Mod_Name bm' |\<notin>| fmdom ps"
      using Cons.prems(3) in_rest by simp
    ultimately show "Mod_Name bm' |\<notin>| fmdom ps1"
      using sp(2) by simp
  qed
  have dist1: "distinct (map Mod_Name rest)"
    using Cons.prems(4) by simp
  have decls1: "\<forall>bm' \<in> set rest. list_all decl_tyvars_fresh_ok (Mod_Interface bm')
                  \<and> list_all decl_tyvars_fresh_ok (Mod_Implementation bm')"
    using Cons.prems(5) by simp
  note IH = Cons.IH[OF sp(1) fold' fresh1 dist1 decls1]
  have ok': "pipeline_state_ok ps'"
   and dom': "fmdom ps' = fmdom ps1 |\<union>| fset_of_list (map Mod_Name rest)"
   and stab': "\<forall>k. k |\<in>| fmdom ps1 \<longrightarrow> fmlookup ps' k = fmlookup ps1 k"
   and int': "\<forall>i < length rest.
                M_IntDeps (the (fmlookup ps' (Mod_Name (rest ! i))))
                  |\<subseteq>| fmdom ps1 |\<union>| fset_of_list (map Mod_Name (take i rest))"
   and impl': "\<forall>i < length rest.
                M_ImplDeps (the (fmlookup ps' (Mod_Name (rest ! i))))
                  |\<subseteq>| fmdom ps1 |\<union>| fset_of_list (map Mod_Name (take (Suc i) rest))"
    using IH by blast+
  \<comment> \<open>Reassemble the five conclusions for bm # rest.\<close>
  have dom2: "fmdom ps' = fmdom ps |\<union>| fset_of_list (map Mod_Name (bm # rest))"
    unfolding dom' sp(2) by simp
  have bm_in1: "Mod_Name bm |\<in>| fmdom ps1"
    using sp(2) by simp
  have lk_bm: "fmlookup ps' (Mod_Name bm) = fmlookup ps1 (Mod_Name bm)"
    using stab' bm_in1 by blast
  have stab2: "\<forall>k. k |\<in>| fmdom ps \<longrightarrow> fmlookup ps' k = fmlookup ps k"
  proof (intro allI impI)
    fix k assume k_in: "k |\<in>| fmdom ps"
    have ne: "k \<noteq> Mod_Name bm"
      using k_in name_fresh by auto
    have "k |\<in>| fmdom ps1"
      using k_in sp(2) by simp
    then have "fmlookup ps' k = fmlookup ps1 k"
      using stab' by blast
    also have "... = fmlookup ps k"
      using sp(3)[OF ne] .
    finally show "fmlookup ps' k = fmlookup ps k" .
  qed
  have int2: "\<forall>i < length (bm # rest).
       M_IntDeps (the (fmlookup ps' (Mod_Name ((bm # rest) ! i))))
         |\<subseteq>| fmdom ps |\<union>| fset_of_list (map Mod_Name (take i (bm # rest)))"
  proof (intro allI impI)
    fix i assume i_lt: "i < length (bm # rest)"
    show "M_IntDeps (the (fmlookup ps' (Mod_Name ((bm # rest) ! i))))
            |\<subseteq>| fmdom ps |\<union>| fset_of_list (map Mod_Name (take i (bm # rest)))"
    proof (cases i)
      case 0
      then show ?thesis
        using sp(4) lk_bm by (simp add: funion_fempty_right)
    next
      case (Suc j)
      have j_lt: "j < length rest"
        using i_lt Suc by simp
      have "M_IntDeps (the (fmlookup ps' (Mod_Name (rest ! j))))
              |\<subseteq>| fmdom ps1 |\<union>| fset_of_list (map Mod_Name (take j rest))"
        using int' j_lt by blast
      then show ?thesis
        unfolding Suc sp(2) by (auto dest: fsubsetD)
    qed
  qed
  have impl2: "\<forall>i < length (bm # rest).
       M_ImplDeps (the (fmlookup ps' (Mod_Name ((bm # rest) ! i))))
         |\<subseteq>| fmdom ps |\<union>| fset_of_list (map Mod_Name (take (Suc i) (bm # rest)))"
  proof (intro allI impI)
    fix i assume i_lt: "i < length (bm # rest)"
    show "M_ImplDeps (the (fmlookup ps' (Mod_Name ((bm # rest) ! i))))
            |\<subseteq>| fmdom ps |\<union>| fset_of_list (map Mod_Name (take (Suc i) (bm # rest)))"
    proof (cases i)
      case 0
      then show ?thesis
        using sp(5) lk_bm by (simp add: funion_fempty_left funion_fempty_right)
    next
      case (Suc j)
      have j_lt: "j < length rest"
        using i_lt Suc by simp
      have "M_ImplDeps (the (fmlookup ps' (Mod_Name (rest ! j))))
              |\<subseteq>| fmdom ps1 |\<union>| fset_of_list (map Mod_Name (take (Suc j) rest))"
        using impl' j_lt by blast
      then show ?thesis
        unfolding Suc sp(2) by (auto dest: fsubsetD)
    qed
  qed
  show ?case
    using ok' dom2 stab2 int2 impl2 by blast
qed

(* The projected form, for consumers. *)
lemma pipeline_fold_preserves:
  assumes "pipeline_state_ok ps"
      and "pipeline_fold ps bms = Inr ps'"
      and "\<forall>bm \<in> set bms. Mod_Name bm |\<notin>| fmdom ps"
      and "distinct (map Mod_Name bms)"
      and "\<forall>bm \<in> set bms. list_all decl_tyvars_fresh_ok (Mod_Interface bm)
             \<and> list_all decl_tyvars_fresh_ok (Mod_Implementation bm)"
  shows "pipeline_state_ok ps'"
    and "fmdom ps' = fmdom ps |\<union>| fset_of_list (map Mod_Name bms)"
    and "\<forall>k. k |\<in>| fmdom ps \<longrightarrow> fmlookup ps' k = fmlookup ps k"
    and "\<forall>i < length bms. M_IntDeps (the (fmlookup ps' (Mod_Name (bms ! i))))
           |\<subseteq>| fmdom ps |\<union>| fset_of_list (map Mod_Name (take i bms))"
    and "\<forall>i < length bms. M_ImplDeps (the (fmlookup ps' (Mod_Name (bms ! i))))
           |\<subseteq>| fmdom ps |\<union>| fset_of_list (map Mod_Name (take (Suc i) bms))"
  using pipeline_fold_invariant[OF assms] by blast+


(* ========================================================================== *)
(* Unpacking a successful compile_program run                                 *)
(* ========================================================================== *)

lemma compile_program_Inr_elim:
  assumes ok: "compile_program modules = Inr (ps, prog)"
  obtains sortedMods where
    "analyze_dependencies modules = Inr sortedMods"
    "pipeline_fold fmempty sortedMods = Inr ps"
    "whole_program_link ps sortedMods = Inr prog"
  using assms unfolding compile_program_def
  by (auto split: sum.splits)

(* The fold facts at compile_program's instances: starting state fmempty,
   module list sorted by analyze_dependencies (whose success supplies the
   freshness and distinctness premises). The decl-binder freshness premise is
   the renamer's naming discipline, over the original module list (the sorted
   list is a permutation of it). *)
lemma compile_program_state:
  assumes ad: "analyze_dependencies modules = Inr sortedMods"
      and fold: "pipeline_fold fmempty sortedMods = Inr ps"
      and decls: "\<forall>bm \<in> set modules. list_all decl_tyvars_fresh_ok (Mod_Interface bm)
                    \<and> list_all decl_tyvars_fresh_ok (Mod_Implementation bm)"
  shows "pipeline_state_ok ps"
    and "fmdom ps = fset_of_list (map Mod_Name sortedMods)"
    and "\<forall>i < length sortedMods.
           M_IntDeps (the (fmlookup ps (Mod_Name (sortedMods ! i))))
             |\<subseteq>| fset_of_list (map Mod_Name (take i sortedMods))"
    and "\<forall>i < length sortedMods.
           M_ImplDeps (the (fmlookup ps (Mod_Name (sortedMods ! i))))
             |\<subseteq>| fset_of_list (map Mod_Name (take (Suc i) sortedMods))"
proof -
  have dist: "distinct (map Mod_Name sortedMods)"
    using analyze_dependencies_distinct_names[OF ad] .
  have set_eq: "set sortedMods = set modules"
    using analyze_dependencies_permutation[OF ad] by (metis mset_eq_setD)
  have fresh: "\<forall>bm \<in> set sortedMods.
                 Mod_Name bm |\<notin>| fmdom (fmempty :: PipelineState)"
    by simp
  have decls': "\<forall>bm \<in> set sortedMods. list_all decl_tyvars_fresh_ok (Mod_Interface bm)
                  \<and> list_all decl_tyvars_fresh_ok (Mod_Implementation bm)"
    using decls set_eq by blast
  note fp = pipeline_fold_preserves[OF pipeline_state_ok_empty fold fresh dist decls']
  show "pipeline_state_ok ps"
    using fp(1) .
  show "fmdom ps = fset_of_list (map Mod_Name sortedMods)"
    using fp(2) by (simp add: funion_fempty_left)
  show "\<forall>i < length sortedMods.
          M_IntDeps (the (fmlookup ps (Mod_Name (sortedMods ! i))))
            |\<subseteq>| fset_of_list (map Mod_Name (take i sortedMods))"
    using fp(4) by (simp add: funion_fempty_left)
  show "\<forall>i < length sortedMods.
          M_ImplDeps (the (fmlookup ps (Mod_Name (sortedMods ! i))))
            |\<subseteq>| fset_of_list (map Mod_Name (take (Suc i) sortedMods))"
    using fp(5) by (simp add: funion_fempty_left)
qed


(* ========================================================================== *)
(* The whole-program face list                                                *)
(* ========================================================================== *)

(* The implementation CoreModule stored at a name, and its contract facts:
   the invariant, ghost subsets, and - by conclusions (v)+(vii) - a
   substitution domain that is EXACTLY its own interface's type variables
   (every abstract realized, nothing else). *)
definition state_impl :: "PipelineState \<Rightarrow> string \<Rightarrow> CoreModule" where
  "state_impl ps n = fst (M_CompiledImplementation (the (fmlookup ps n)))"

lemma state_impl_facts:
  assumes ok: "pipeline_state_ok ps"
      and k: "k |\<in>| fmdom ps"
  shows "core_module_invariant (state_impl ps k)"
    and "module_ghost_subsets_ok (state_impl ps k)"
    and "fmdom (CM_TypeSubst (state_impl ps k))
           = TE_TypeVars (CM_TyEnv (state_iface ps k))"
proof -
  obtain e where lk: "fmlookup ps k = Some e"
    using k by (meson fmdomE)
  note eok = pipeline_state_okD(1)[OF ok lk]
  show inv: "core_module_invariant (state_impl ps k)"
    using pipeline_entry_okD(7)[OF eok] lk unfolding state_impl_def by simp
  show "module_ghost_subsets_ok (state_impl ps k)"
    using core_module_invariant_ghost_subsets_ok[OF inv] .
  show "fmdom (CM_TypeSubst (state_impl ps k))
          = TE_TypeVars (CM_TyEnv (state_iface ps k))"
    using pipeline_entry_okD(8)[OF eok] pipeline_entry_okD(9)[OF eok] lk
    unfolding state_impl_def state_iface_def by (simp add: fsubset_antisym)
qed

(* An implementation face declares no abstract types of its own (stored
   conclusion (viii)). *)
lemma state_impl_tyvars:
  assumes ok: "pipeline_state_ok ps"
      and k: "k |\<in>| fmdom ps"
  shows "TE_TypeVars (CM_TyEnv (state_impl ps k)) = {||}"
proof -
  obtain e where lk: "fmlookup ps k = Some e"
    using k by (meson fmdomE)
  show ?thesis
    using pipeline_entry_okD(10)[OF pipeline_state_okD(1)[OF ok lk]] lk
    unfolding state_impl_def by simp
qed

(* The stored definedness facts (elab_module_defs_complete, invariant
   conjuncts 15-18), read off the two face CoreModules: everything a face
   declares is defined by the module's two faces together (interface) resp.
   by the face itself (implementation). *)
lemma state_defs_facts:
  assumes ok: "pipeline_state_ok ps"
      and k: "k |\<in>| fmdom ps"
  shows "fmdom (TE_GlobalVars (CM_TyEnv (state_iface ps k)))
           |\<subseteq>| fmdom (CM_GlobalVars (state_iface ps k))
                |\<union>| fmdom (CM_GlobalVars (state_impl ps k))"
    and "fmdom (TE_Functions (CM_TyEnv (state_iface ps k)))
           |\<subseteq>| fmdom (CM_Functions (state_iface ps k))
                |\<union>| fmdom (CM_Functions (state_impl ps k))"
    and "fmdom (TE_GlobalVars (CM_TyEnv (state_impl ps k)))
           |\<subseteq>| fmdom (CM_GlobalVars (state_impl ps k))"
    and "fmdom (TE_Functions (CM_TyEnv (state_impl ps k)))
           |\<subseteq>| fmdom (CM_Functions (state_impl ps k))"
proof -
  obtain e where lk: "fmlookup ps k = Some e"
    using k by (meson fmdomE)
  note eok = pipeline_state_okD(1)[OF ok lk]
  show "fmdom (TE_GlobalVars (CM_TyEnv (state_iface ps k)))
          |\<subseteq>| fmdom (CM_GlobalVars (state_iface ps k))
               |\<union>| fmdom (CM_GlobalVars (state_impl ps k))"
    using pipeline_entry_okD(15)[OF eok] lk
    unfolding state_iface_def state_impl_def by simp
  show "fmdom (TE_Functions (CM_TyEnv (state_iface ps k)))
          |\<subseteq>| fmdom (CM_Functions (state_iface ps k))
               |\<union>| fmdom (CM_Functions (state_impl ps k))"
    using pipeline_entry_okD(16)[OF eok] lk
    unfolding state_iface_def state_impl_def by simp
  show "fmdom (TE_GlobalVars (CM_TyEnv (state_impl ps k)))
          |\<subseteq>| fmdom (CM_GlobalVars (state_impl ps k))"
    using pipeline_entry_okD(17)[OF eok] lk
    unfolding state_impl_def by simp
  show "fmdom (TE_Functions (CM_TyEnv (state_impl ps k)))
          |\<subseteq>| fmdom (CM_Functions (state_impl ps k))"
    using pipeline_entry_okD(18)[OF eok] lk
    unfolding state_impl_def by simp
qed

(* The whole-program link's input is one interface and one implementation
   per module, interleaved in module order. To reason about its sub-lists by
   name (two distinct modules can compile to EQUAL CoreModules, so module
   multisets lose information), index the faces by (name, is-implementation)
   keys: the key lists are distinct, and distinct_map_submset then turns
   key-set inclusion into the sub-multiset facts the sublink lemmas need. *)
fun face_keys :: "string list \<Rightarrow> (string \<times> bool) list" where
  "face_keys [] = []"
| "face_keys (n # ns) = (n, False) # (n, True) # face_keys ns"

definition face_module :: "PipelineState \<Rightarrow> string \<times> bool \<Rightarrow> CoreModule" where
  "face_module ps k =
     (if snd k then state_impl ps (fst k) else state_iface ps (fst k))"

lemma face_keys_append [simp]:
  "face_keys (xs @ ys) = face_keys xs @ face_keys ys"
  by (induction xs) auto

lemma face_keys_fst:
  "k \<in> set (face_keys ns) \<Longrightarrow> fst k \<in> set ns"
  by (induction ns) auto

lemma face_keys_iface_in:
  "n \<in> set ns \<Longrightarrow> (n, False) \<in> set (face_keys ns)"
  by (induction ns) auto

lemma face_keys_impl_in:
  "n \<in> set ns \<Longrightarrow> (n, True) \<in> set (face_keys ns)"
  by (induction ns) auto

lemma face_keys_mono:
  assumes "set xs \<subseteq> set ys"
  shows "set (face_keys xs) \<subseteq> set (face_keys ys)"
  using assms
  by (induction xs) (auto intro: face_keys_iface_in face_keys_impl_in)

lemma distinct_face_keys:
  assumes "distinct ns"
  shows "distinct (face_keys ns)"
  using assms
proof (induction ns)
  case Nil
  then show ?case by simp
next
  case (Cons n rest)
  have "(n, b) \<notin> set (face_keys rest)" for b
    using Cons.prems face_keys_fst by fastforce
  then show ?case using Cons by simp
qed

(* The list whole_program_link hands to link_modules, re-expressed over the
   face keys. *)
lemma whole_faces_eq:
  "concat (map (\<lambda>e. [fst (M_CompiledInterface e), fst (M_CompiledImplementation e)])
             (map (\<lambda>n. the (fmlookup ps n)) ns))
     = map (face_module ps) (face_keys ns)"
  by (induction ns) (simp_all add: face_module_def state_iface_def state_impl_def)

lemma whole_program_link_Inr_elim:
  assumes ok: "whole_program_link ps mods = Inr prog"
  obtains entries where
    "lookup_entries ps (map Mod_Name mods) = Inr entries"
    "link_modules (concat (map (\<lambda>e. [fst (M_CompiledInterface e),
       fst (M_CompiledImplementation e)]) entries)) = Inr prog"
  using assms unfolding whole_program_link_def
  by (auto split: sum.splits)


(* ========================================================================== *)
(* Groundness of dependency-closed prefixes                                   *)
(* ========================================================================== *)

(* The range of a union is within the union of the ranges. *)
lemma subst_range_tyvars_fmlist_union:
  "subst_range_tyvars (fmlist_union ss) \<subseteq> (\<Union>s \<in> set ss. subst_range_tyvars s)"
proof
  fix y assume "y \<in> subst_range_tyvars (fmlist_union ss)"
  then obtain ty where ty_ran: "ty \<in> fmran' (fmlist_union ss)"
      and y_ty: "y \<in> type_tyvars ty"
    unfolding subst_range_tyvars_def by blast
  obtain k where "fmlookup (fmlist_union ss) k = Some ty"
    using ty_ran by (meson fmran'E)
  then obtain s where s_in: "s \<in> set ss" and lk: "fmlookup s k = Some ty"
    using fmlist_union_lookup_some by metis
  have "ty \<in> fmran' s"
    using lk by (meson fmran'I)
  then show "y \<in> (\<Union>s \<in> set ss. subst_range_tyvars s)"
    using s_in y_ty unfolding subst_range_tyvars_def by blast
qed

(* The groundness hypothesis of link_modules_sublink_ground, discharged for
   the faces of any dep-closed name list: interfaces contribute no
   substitutions; an implementation's substitution ranges over the type
   variables of its context interfaces (conclusion (ix)) - all declared by
   modules in the closed list, and each equal to its OWN implementation's
   substitution domain (conclusions (v)+(vii)), which is present alongside.
   So every range variable is in the union's domain. *)
lemma state_prefix_ground:
  assumes ok: "pipeline_state_ok ps"
      and dom_ns: "fset_of_list ns |\<subseteq>| fmdom ps"
      and closed: "\<forall>n \<in> set ns. \<forall>d. d |\<in>| M_ImplDeps (the (fmlookup ps n))
                     \<longrightarrow> d \<in> set ns"
  shows "subst_range_tyvars
           (fmlist_union (map CM_TypeSubst (map (face_module ps) (face_keys ns))))
           \<subseteq> fset (fmdom (fmlist_union
                (map CM_TypeSubst (map (face_module ps) (face_keys ns)))))"
proof
  fix y assume y_in: "y \<in> subst_range_tyvars
    (fmlist_union (map CM_TypeSubst (map (face_module ps) (face_keys ns))))"
  have in_dom: "\<And>n. n \<in> set ns \<Longrightarrow> n |\<in>| fmdom ps"
    using dom_ns by (metis fset_of_list_elem fsubsetD)
  \<comment> \<open>Find the contributing face; it must be an implementation.\<close>
  have "y \<in> (\<Union>s \<in> set (map CM_TypeSubst (map (face_module ps) (face_keys ns))).
               subst_range_tyvars s)"
    using subst_range_tyvars_fmlist_union y_in by blast
  then obtain z where z_in: "z \<in> set (map (face_module ps) (face_keys ns))"
      and y_z: "y \<in> subst_range_tyvars (CM_TypeSubst z)"
    by auto
  obtain kk where kk_in: "kk \<in> set (face_keys ns)" and z_eq: "z = face_module ps kk"
    using z_in by auto
  have n_in: "fst kk \<in> set ns"
    using face_keys_fst[OF kk_in] .
  obtain e where lk: "fmlookup ps (fst kk) = Some e"
    using in_dom[OF n_in] by (meson fmdomE)
  note eok = pipeline_state_okD(1)[OF ok lk]
  have k_impl: "snd kk"
  proof (rule ccontr)
    assume "\<not> snd kk"
    then have "z = state_iface ps (fst kk)"
      using z_eq unfolding face_module_def by simp
    then have "CM_TypeSubst z = fmempty"
      using state_iface_facts(1)[OF ok in_dom[OF n_in]] by simp
    then show False using y_z by simp
  qed
  have y_z': "y \<in> subst_range_tyvars (CM_TypeSubst (fst (M_CompiledImplementation e)))"
    using y_z z_eq k_impl unfolding face_module_def state_impl_def
    by (simp add: lk)
  \<comment> \<open>Conclusion (ix): the range variable is some context interface's tyvar.\<close>
  have y_ctx: "y \<in> fset (funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x))
       (map fst (entry_int_ctx ps e) @ map fst (entry_impl_ctx ps (fst kk) e)
        @ [fst (M_CompiledInterface e)])))"
    using pipeline_entry_okD(11)[OF eok] y_z' by blast
  then obtain x where x_in: "x \<in> set (map fst (entry_int_ctx ps e)
        @ map fst (entry_impl_ctx ps (fst kk) e) @ [fst (M_CompiledInterface e)])"
      and y_x: "y |\<in>| TE_TypeVars (CM_TyEnv x)"
    by (auto simp: funion_list_member)
  have own_iface: "fst (M_CompiledInterface e) = state_iface ps (fst kk)"
    unfolding state_iface_def by (simp add: lk)
  \<comment> \<open>The declaring interface's name is a dep of the contributor (or the
     contributor itself), hence in the closed list.\<close>
  have "\<exists>d. (d |\<in>| M_ImplDeps e \<or> d = fst kk) \<and> x = state_iface ps d"
    using x_in pipeline_entry_okD(5)[OF eok]
    unfolding entry_int_ctx_ifaces entry_impl_ctx_ifaces own_iface
    by (auto dest: fsubsetD)
  then obtain d where d_impl: "d |\<in>| M_ImplDeps e \<or> d = fst kk"
      and x_eq: "x = state_iface ps d"
    by blast
  have d_in_ns: "d \<in> set ns"
    using d_impl bspec[OF closed n_in] lk n_in by auto
  \<comment> \<open>Its own implementation's substitution domain covers that tyvar, and is
     itself an input of the union.\<close>
  have y_dom: "y |\<in>| fmdom (CM_TypeSubst (state_impl ps d))"
    using y_x x_eq state_impl_facts(3)[OF ok in_dom[OF d_in_ns]] by simp
  have impl_in: "CM_TypeSubst (state_impl ps d)
                   \<in> set (map CM_TypeSubst (map (face_module ps) (face_keys ns)))"
    using face_keys_impl_in[OF d_in_ns] by (force simp: face_module_def)
  show "y \<in> fset (fmdom (fmlist_union
              (map CM_TypeSubst (map (face_module ps) (face_keys ns)))))"
    using y_dom impl_in unfolding fmdom_fmlist_union
    by (auto simp: funion_list_member)
qed


(* ========================================================================== *)
(* The capstone: compile_program produces a well-typed program               *)
(* ========================================================================== *)

(* LINKING.md step 8(b). Induction over the number of modules whose faces
   enter the whole-program link: each prefix links successfully (its faces
   are a realization-closed sub-multiset of the successful whole link, so
   link_modules_sublink_ground applies) and is well-typed (the previous
   prefix by induction; the new module's derived implementation link by its
   stored conclusion (ii), its link success via link_modules_sublink with
   the runtime gate discharged by conclusion (vi); glued by the set-union
   form of link_preserves_well_typed, whose set equation holds because the
   new module's deps all lie among the earlier modules' interfaces - the
   fold's processing-order facts). *)
theorem compile_program_well_typed:
  assumes cp: "compile_program modules = Inr (ps, prog)"
      and decls: "\<forall>bm \<in> set modules. list_all decl_tyvars_fresh_ok (Mod_Interface bm)
                    \<and> list_all decl_tyvars_fresh_ok (Mod_Implementation bm)"
  shows "core_module_well_typed prog"
proof -
  obtain sortedMods where
      ad: "analyze_dependencies modules = Inr sortedMods"
      and fold: "pipeline_fold fmempty sortedMods = Inr ps"
      and wpl: "whole_program_link ps sortedMods = Inr prog"
    using cp by (rule compile_program_Inr_elim)
  note st = compile_program_state[OF ad fold decls]
  define names where "names = map Mod_Name sortedMods"
  have dist_names: "distinct names"
    unfolding names_def using analyze_dependencies_distinct_names[OF ad] .
  have dist_fkeys: "distinct (face_keys names)"
    using distinct_face_keys[OF dist_names] .
  have dom_eq: "fmdom ps = fset_of_list names"
    using st(2) unfolding names_def .

  \<comment> \<open>The whole-program link, over the face keys.\<close>
  obtain entries where lkE: "lookup_entries ps (map Mod_Name sortedMods) = Inr entries"
      and linkW0: "link_modules (concat (map (\<lambda>e. [fst (M_CompiledInterface e),
            fst (M_CompiledImplementation e)]) entries)) = Inr prog"
    using wpl by (rule whole_program_link_Inr_elim)
  have entries_eq: "entries = map (\<lambda>n. the (fmlookup ps n)) names"
    using lookup_entries_eq[OF lkE] unfolding names_def .
  have linkW: "link_modules (map (face_module ps) (face_keys names)) = Inr prog"
    using linkW0 unfolding entries_eq whole_faces_eq .
  obtain \<sigma>W where mergeW: "merge_all_substs
      (map CM_TypeSubst (map (face_module ps) (face_keys names))) = Inr \<sigma>W"
    using linkW link_modules_Inr_iff[of "map (face_module ps) (face_keys names)" prog]
    by blast

  \<comment> \<open>The processing-order facts, re-based onto the name list.\<close>
  have int_ord: "M_IntDeps (the (fmlookup ps (names ! j)))
                   |\<subseteq>| fset_of_list (take j names)"
    if j_lt: "j < length names" for j
  proof -
    have j_lt': "j < length sortedMods"
      using j_lt by (simp add: names_def)
    have "M_IntDeps (the (fmlookup ps (Mod_Name (sortedMods ! j))))
            |\<subseteq>| fset_of_list (map Mod_Name (take j sortedMods))"
      using st(3) j_lt' by blast
    then show ?thesis
      using j_lt' by (simp add: names_def take_map)
  qed
  have impl_ord: "M_ImplDeps (the (fmlookup ps (names ! j)))
                    |\<subseteq>| fset_of_list (take (Suc j) names)"
    if j_lt: "j < length names" for j
  proof -
    have j_lt': "j < length sortedMods"
      using j_lt by (simp add: names_def)
    have "M_ImplDeps (the (fmlookup ps (Mod_Name (sortedMods ! j))))
            |\<subseteq>| fset_of_list (map Mod_Name (take (Suc j) sortedMods))"
      using st(4) j_lt' by blast
    then show ?thesis
      using j_lt' by (simp add: names_def take_map)
  qed

  \<comment> \<open>The prefix induction.\<close>
  have main: "\<exists>p. link_modules (map (face_module ps) (face_keys (take i names))) = Inr p
                \<and> core_module_well_typed p"
    if "i \<le> length names" for i
    using that
  proof (induction i)
    case 0
    have msub0: "mset ([] :: CoreModule list)
                   \<subseteq># mset (map (face_module ps) (face_keys names))"
      by (simp add: empty_le)
    have e0: "\<forall>x \<in> set ([] :: CoreModule list). CM_TypeSubst x = fmempty"
      by simp
    obtain p where lp: "link_modules ([] :: CoreModule list) = Inr p"
      using link_modules_empty_substs_sublink[OF linkW e0 msub0] by blast
    have "core_module_well_typed p"
      using link_modules_nil[OF lp] empty_core_module_well_typed by simp
    then show ?case using lp by auto
  next
    case (Suc i)
    have i_lt: "i < length names"
      using Suc.prems by simp
    obtain a where
        linkA: "link_modules (map (face_module ps) (face_keys (take i names))) = Inr a"
        and wtA: "core_module_well_typed a"
      using Suc.IH Suc.prems by auto
    define m where "m = names ! i"
    have m_in: "m \<in> set names"
      using i_lt unfolding m_def by (rule nth_mem)
    have m_dom: "m |\<in>| fmdom ps"
      using m_in dom_eq by (simp add: fset_of_list_elem)
    obtain em where lkm: "fmlookup ps m = Some em"
      using m_dom by (meson fmdomE)
    note em_ok = pipeline_state_okD(1)[OF st(1) lkm]
    have take_split: "take (Suc i) names = take i names @ [m]"
      using i_lt unfolding m_def by (rule take_Suc_conv_app_nth)
    have keys_split: "face_keys (take (Suc i) names)
                        = face_keys (take i names) @ [(m, False), (m, True)]"
      unfolding take_split by simp
    have P_split: "map (face_module ps) (face_keys (take (Suc i) names))
                     = map (face_module ps) (face_keys (take i names))
                       @ [state_iface ps m, state_impl ps m]"
      unfolding keys_split by (simp add: face_module_def)
    \<comment> \<open>The new module's dep sets resolve strictly earlier.\<close>
    have int_sub: "M_IntDeps em |\<subseteq>| fset_of_list (take i names)"
      using int_ord[OF i_lt] lkm unfolding m_def by simp
    have impl_sub: "M_ImplDeps em |\<subseteq>| fset_of_list (take (Suc i) names)"
      using impl_ord[OF i_lt] lkm unfolding m_def by simp
    have dep_early: "d \<in> set (take i names)"
      if d_impl: "d |\<in>| M_ImplDeps em" and d_ne: "d \<noteq> m" for d
    proof -
      have "d \<in> set (take (Suc i) names)"
        using impl_sub d_impl by (auto simp: fset_of_list_elem dest: fsubsetD)
      then show ?thesis
        using d_ne unfolding take_split by simp
    qed
    \<comment> \<open>The new module's B-list, keyed by name.\<close>
    define depNames where "depNames = sorted_list_of_fset (M_IntDeps em)
        @ sorted_list_of_fset (M_ImplDeps em |-| M_IntDeps em |-| {|m|})"
    define bkeys where "bkeys = map (\<lambda>n. (n, False)) depNames @ [(m, False), (m, True)]"
    have depNames_sub: "set depNames \<subseteq> set (take i names)"
    proof
      fix d assume "d \<in> set depNames"
      then have "d |\<in>| M_IntDeps em \<or> (d |\<in>| M_ImplDeps em \<and> d \<noteq> m)"
        unfolding depNames_def by auto
      then show "d \<in> set (take i names)"
      proof
        assume "d |\<in>| M_IntDeps em"
        then show ?thesis
          using int_sub by (auto simp: fset_of_list_elem dest: fsubsetD)
      next
        assume "d |\<in>| M_ImplDeps em \<and> d \<noteq> m"
        then show ?thesis using dep_early by blast
      qed
    qed
    have dist_depNames: "distinct depNames"
      unfolding depNames_def by (auto simp: distinct_sorted_list_of_fset)
    have m_notin_deps: "m \<notin> set depNames"
      unfolding depNames_def using pipeline_entry_okD(3)[OF em_ok] by auto
    have dist_bkeys: "distinct bkeys"
      unfolding bkeys_def using dist_depNames m_notin_deps
      by (auto simp: distinct_map inj_on_def)
    have bkeys_cases: "\<And>kk. kk \<in> set bkeys \<Longrightarrow>
        (\<exists>n \<in> set depNames. kk = (n, False)) \<or> kk = (m, False) \<or> kk = (m, True)"
      unfolding bkeys_def by auto
    have bkeys_sub: "set bkeys \<subseteq> set (face_keys names)"
    proof
      fix kk assume "kk \<in> set bkeys"
      from bkeys_cases[OF this] show "kk \<in> set (face_keys names)"
      proof (elim disjE bexE)
        fix n assume "n \<in> set depNames" and kk_eq: "kk = (n, False)"
        then have "n \<in> set names"
          using depNames_sub set_take_subset by fastforce
        then show ?thesis using kk_eq face_keys_iface_in by blast
      next
        assume "kk = (m, False)"
        then show ?thesis using m_in face_keys_iface_in by blast
      next
        assume "kk = (m, True)"
        then show ?thesis using m_in face_keys_impl_in by blast
      qed
    qed
    have msubB: "mset (map (face_module ps) bkeys)
                   \<subseteq># mset (map (face_module ps) (face_keys names))"
      using distinct_map_submset[OF dist_bkeys dist_fkeys bkeys_sub] .
    \<comment> \<open>The B-list is the invariant's derived-implementation list.\<close>
    have B_eq: "map (face_module ps) bkeys
                  = map fst (entry_int_ctx ps em) @ map fst (entry_impl_ctx ps m em)
                    @ [fst (M_CompiledInterface em), fst (M_CompiledImplementation em)]"
      unfolding bkeys_def depNames_def entry_int_ctx_ifaces entry_impl_ctx_ifaces
      by (simp add: face_module_def state_iface_def state_impl_def lkm)
    \<comment> \<open>Its link succeeds: merge success restricts from the whole link, and
       the runtime gate is the stored conclusion (vi).\<close>
    have msubB': "mset (map CM_TypeSubst (map (face_module ps) bkeys))
        \<subseteq># mset (map CM_TypeSubst (map (face_module ps) (face_keys names)))"
      using msubB by (metis image_mset_subseteq_mono mset_map)
    obtain \<sigma>B where mergeB: "merge_all_substs
        (map CM_TypeSubst (map (face_module ps) bkeys)) = Inr \<sigma>B"
      using merge_all_substs_sublist[OF mergeW msubB'] by blast
    have rtB: "link_runtime_ok (map (face_module ps) bkeys) \<sigma>B"
      using pipeline_entry_okD(14)[OF em_ok, folded B_eq, OF mergeB] .
    have linkB: "link_modules (map (face_module ps) bkeys)
                   = Inr (link_result (map (face_module ps) bkeys) \<sigma>B)"
      using link_modules_sublink[OF linkW msubB mergeB rtB] .
    have wtB: "core_module_well_typed (link_result (map (face_module ps) bkeys) \<sigma>B)"
      using pipeline_entry_okD(13)[OF em_ok, folded B_eq, OF linkB] .
    \<comment> \<open>The extended prefix links: a realization-closed sub-multiset.\<close>
    have dist_tkeys: "distinct (face_keys (take (Suc i) names))"
      using distinct_face_keys[OF distinct_take[OF dist_names]] .
    have tkeys_sub: "set (face_keys (take (Suc i) names)) \<subseteq> set (face_keys names)"
      using face_keys_mono[OF set_take_subset] .
    have msubT: "mset (map (face_module ps) (face_keys (take (Suc i) names)))
                   \<subseteq># mset (map (face_module ps) (face_keys names))"
      using distinct_map_submset[OF dist_tkeys dist_fkeys tkeys_sub] .
    have closed_take: "\<forall>n \<in> set (take (Suc i) names). \<forall>d.
         d |\<in>| M_ImplDeps (the (fmlookup ps n)) \<longrightarrow> d \<in> set (take (Suc i) names)"
    proof (intro ballI allI impI)
      fix n d assume n_in: "n \<in> set (take (Suc i) names)"
         and d_in: "d |\<in>| M_ImplDeps (the (fmlookup ps n))"
      obtain j where j_len: "j < length (take (Suc i) names)"
          and j_nth: "take (Suc i) names ! j = n"
        using n_in by (metis in_set_conv_nth)
      have j_lt_len: "j < length names"
        using j_len by simp
      have j_le: "j < Suc i"
        using j_len by simp
      have n_eq: "n = names ! j"
        using j_nth j_le by simp
      have "M_ImplDeps (the (fmlookup ps n)) |\<subseteq>| fset_of_list (take (Suc j) names)"
        using impl_ord[OF j_lt_len] n_eq by simp
      then have "d \<in> set (take (Suc j) names)"
        using d_in by (auto simp: fset_of_list_elem dest: fsubsetD)
      then show "d \<in> set (take (Suc i) names)"
        using set_take_subset_set_take[of "Suc j" "Suc i" names] j_le by auto
    qed
    have dom_take: "fset_of_list (take (Suc i) names) |\<subseteq>| fmdom ps"
      unfolding dom_eq by (auto simp: fset_of_list_elem dest: in_set_takeD)
    have ground: "subst_range_tyvars (fmlist_union (map CM_TypeSubst
          (map (face_module ps) (face_keys (take (Suc i) names)))))
          \<subseteq> fset (fmdom (fmlist_union (map CM_TypeSubst
               (map (face_module ps) (face_keys (take (Suc i) names))))))"
      using state_prefix_ground[OF st(1) dom_take closed_take] .
    obtain p where linkP: "link_modules
        (map (face_module ps) (face_keys (take (Suc i) names))) = Inr p"
      using link_modules_sublink_ground[OF linkW msubT ground] by blast
    \<comment> \<open>Reassemble: everything the B-list adds beyond its own two faces is
       an earlier module's interface, already in the previous prefix.\<close>
    have sub1: "set (map (face_module ps) bkeys)
                  \<subseteq> set (map (face_module ps) (face_keys (take i names)))
                    \<union> {state_iface ps m, state_impl ps m}"
    proof
      fix z assume "z \<in> set (map (face_module ps) bkeys)"
      then obtain kk where kk_in: "kk \<in> set bkeys" and z_eq: "z = face_module ps kk"
        by auto
      from bkeys_cases[OF kk_in]
      show "z \<in> set (map (face_module ps) (face_keys (take i names)))
                \<union> {state_iface ps m, state_impl ps m}"
      proof (elim disjE bexE)
        fix n assume n_dep: "n \<in> set depNames" and kk_eq: "kk = (n, False)"
        have "(n, False) \<in> set (face_keys (take i names))"
          using depNames_sub n_dep face_keys_iface_in by blast
        then show ?thesis using z_eq kk_eq by auto
      next
        assume "kk = (m, False)"
        then show ?thesis using z_eq by (simp add: face_module_def)
      next
        assume "kk = (m, True)"
        then show ?thesis using z_eq by (simp add: face_module_def)
      qed
    qed
    have in_B: "state_iface ps m \<in> set (map (face_module ps) bkeys)"
              "state_impl ps m \<in> set (map (face_module ps) bkeys)"
      unfolding bkeys_def by (force simp: face_module_def)+
    have setMS: "set (map (face_module ps) (face_keys (take (Suc i) names)))
                   = set (map (face_module ps) (face_keys (take i names)))
                     \<union> set (map (face_module ps) bkeys)"
      unfolding P_split using sub1 in_B by auto
    have ghostOK: "\<forall>z \<in> set (map (face_module ps) (face_keys (take (Suc i) names))).
                     module_ghost_subsets_ok z"
    proof
      fix z assume "z \<in> set (map (face_module ps) (face_keys (take (Suc i) names)))"
      then obtain kk where kk_in: "kk \<in> set (face_keys (take (Suc i) names))"
          and z_eq: "z = face_module ps kk"
        by auto
      have "fst kk \<in> set names"
        using face_keys_fst[OF kk_in] set_take_subset by fastforce
      then have kk_dom: "fst kk |\<in>| fmdom ps"
        using dom_eq by (simp add: fset_of_list_elem)
      show "module_ghost_subsets_ok z"
      proof (cases "snd kk")
        case True
        then have "z = state_impl ps (fst kk)"
          using z_eq unfolding face_module_def by simp
        then show ?thesis
          using state_impl_facts(2)[OF st(1) kk_dom] by simp
      next
        case False
        then have "z = state_iface ps (fst kk)"
          using z_eq unfolding face_module_def by simp
        then show ?thesis
          using state_iface_facts(3)[OF st(1) kk_dom] by simp
      qed
    qed
    have "core_module_well_typed p"
      using link_preserves_well_typed[OF linkA wtA linkB wtB linkP setMS ghostOK] .
    then show ?case using linkP by blast
  qed

  \<comment> \<open>At the full length, the prefix IS the whole program.\<close>
  have take_len: "take (length names) names = names"
    by simp
  obtain p where linkN: "link_modules (map (face_module ps) (face_keys names)) = Inr p"
      and wtN: "core_module_well_typed p"
    using main[OF le_refl] unfolding take_len by blast
  have "p = prog"
    using linkN linkW by simp
  then show ?thesis
    using wtN by simp
qed


(* ========================================================================== *)
(* The capstone: compile_program produces a closed program                    *)
(* ========================================================================== *)

(* A well-typed module defines only what it declares: each CM_GlobalVars /
   CM_Functions entry has a matching declaration (module_globals_well_typed /
   module_functions_well_typed of the normalized module, whose domains equal
   the original's - normalization only rewrites types and terms). This is the
   easy inclusion of closedness; the converse is the per-module definedness
   carried by the invariant. *)
lemma core_module_well_typed_defined_declared:
  assumes wt: "core_module_well_typed m"
  shows "fmdom (CM_GlobalVars m) |\<subseteq>| fmdom (TE_GlobalVars (CM_TyEnv m))"
    and "fmdom (CM_Functions m) |\<subseteq>| fmdom (TE_Functions (CM_TyEnv m))"
proof -
  have nwt: "normalized_module_well_typed (normalize_module m)"
    using wt unfolding core_module_well_typed_def by blast
  have g: "module_globals_well_typed (CM_TyEnv (normalize_module m))
             (CM_GlobalVars (normalize_module m))"
   and f: "module_functions_well_typed (CM_TyEnv (normalize_module m))
             (CM_Functions (normalize_module m))"
    using nwt unfolding normalized_module_well_typed_def by blast+
  have dg: "fmdom (CM_GlobalVars (normalize_module m)) = fmdom (CM_GlobalVars m)"
   and dtg: "fmdom (TE_GlobalVars (CM_TyEnv (normalize_module m)))
               = fmdom (TE_GlobalVars (CM_TyEnv m))"
   and df: "fmdom (CM_Functions (normalize_module m)) = fmdom (CM_Functions m)"
   and dtf: "fmdom (TE_Functions (CM_TyEnv (normalize_module m)))
               = fmdom (TE_Functions (CM_TyEnv m))"
    unfolding normalize_module_def apply_subst_to_tyenv_def by simp_all
  show "fmdom (CM_GlobalVars m) |\<subseteq>| fmdom (TE_GlobalVars (CM_TyEnv m))"
  proof
    fix n assume "n |\<in>| fmdom (CM_GlobalVars m)"
    then have "n |\<in>| fmdom (CM_GlobalVars (normalize_module m))"
      using dg by simp
    then obtain tm where "fmlookup (CM_GlobalVars (normalize_module m)) n = Some tm"
      by (auto simp: fmlookup_dom_iff)
    then obtain declTy where
        "fmlookup (TE_GlobalVars (CM_TyEnv (normalize_module m))) n = Some declTy"
      using g unfolding module_globals_well_typed_def by blast
    then have "n |\<in>| fmdom (TE_GlobalVars (CM_TyEnv (normalize_module m)))"
      by (rule fmdomI)
    then show "n |\<in>| fmdom (TE_GlobalVars (CM_TyEnv m))"
      using dtg by simp
  qed
  show "fmdom (CM_Functions m) |\<subseteq>| fmdom (TE_Functions (CM_TyEnv m))"
  proof
    fix n assume "n |\<in>| fmdom (CM_Functions m)"
    then have "n |\<in>| fmdom (CM_Functions (normalize_module m))"
      using df by simp
    then obtain fn where "fmlookup (CM_Functions (normalize_module m)) n = Some fn"
      by (auto simp: fmlookup_dom_iff)
    then obtain info where
        "fmlookup (TE_Functions (CM_TyEnv (normalize_module m))) n = Some info"
      using f unfolding module_functions_well_typed_def by blast
    then have "n |\<in>| fmdom (TE_Functions (CM_TyEnv (normalize_module m)))"
      by (rule fmdomI)
    then show "n |\<in>| fmdom (TE_Functions (CM_TyEnv m))"
      using dtf by simp
  qed
qed

(* LINKING.md step 8(c). The linked program is closed: everything declared is
   defined and no abstract types remain.

    - Globals/functions: the linked domains are the unions of the per-face
      domains (link_result); "declared implies defined" is the invariant's
      definedness facts (each face's declarations are defined by faces of
      the SAME module, all present in the whole-program list); "defined
      implies declared" is per-definition typechecking of the linked
      program, which (b) provides.
    - Type variables: the linked TE_TypeVars is the union of the per-face
      TypeVars minus the merged substitution's domain - and these are the
      SAME set: interfaces contribute exactly their TypeVars (implementations
      have none, stored conclusion (viii)), the merged domain is the union of
      the per-face substitution domains (merge_all_substs is a closure), and
      per module the implementation's substitution domain equals its own
      interface's TypeVars (stored conclusions (v)+(vii)) - with both faces
      always present together. *)
theorem compile_program_closed:
  assumes cp: "compile_program modules = Inr (ps, prog)"
      and decls: "\<forall>bm \<in> set modules. list_all decl_tyvars_fresh_ok (Mod_Interface bm)
                    \<and> list_all decl_tyvars_fresh_ok (Mod_Implementation bm)"
  shows "core_module_closed prog"
proof -
  obtain sortedMods where
      ad: "analyze_dependencies modules = Inr sortedMods"
      and fold: "pipeline_fold fmempty sortedMods = Inr ps"
      and wpl: "whole_program_link ps sortedMods = Inr prog"
    using cp by (rule compile_program_Inr_elim)
  note st = compile_program_state[OF ad fold decls]
  define names where "names = map Mod_Name sortedMods"
  have dom_eq: "fmdom ps = fset_of_list names"
    using st(2) unfolding names_def .

  \<comment> \<open>The whole-program link, over the face keys.\<close>
  obtain entries where lkE: "lookup_entries ps (map Mod_Name sortedMods) = Inr entries"
      and linkW0: "link_modules (concat (map (\<lambda>e. [fst (M_CompiledInterface e),
            fst (M_CompiledImplementation e)]) entries)) = Inr prog"
    using wpl by (rule whole_program_link_Inr_elim)
  have entries_eq: "entries = map (\<lambda>n. the (fmlookup ps n)) names"
    using lookup_entries_eq[OF lkE] unfolding names_def .
  define faces where "faces = map (face_module ps) (face_keys names)"
  have linkW: "link_modules faces = Inr prog"
    using linkW0 unfolding entries_eq whole_faces_eq faces_def[symmetric] .
  obtain \<sigma> where merge: "merge_all_substs (map CM_TypeSubst faces) = Inr \<sigma>"
      and prog_eq: "prog = link_result faces \<sigma>"
    using linkW link_modules_Inr_iff[of faces prog] by blast

  have key_dom: "fst kk |\<in>| fmdom ps" if "kk \<in> set (face_keys names)" for kk
    using face_keys_fst[OF that] dom_eq by (simp add: fset_of_list_elem)
  have fm_iface: "face_module ps (n, False) = state_iface ps n" for n
    by (simp add: face_module_def)
  have fm_impl: "face_module ps (n, True) = state_impl ps n" for n
    by (simp add: face_module_def)

  \<comment> \<open>The merged substitution's domain is the union of the per-face domains.\<close>
  have dom_\<sigma>: "fmdom \<sigma> = funion_list (map (\<lambda>x. fmdom (CM_TypeSubst x)) faces)"
  proof -
    have "is_subst_closure (fmlist_union (map CM_TypeSubst faces)) \<sigma>"
      using merge merge_all_substs_Inr_iff by blast
    then have "fmdom \<sigma> = fmdom (fmlist_union (map CM_TypeSubst faces))"
      unfolding is_subst_closure_def by blast
    then show ?thesis
      unfolding fmdom_fmlist_union by (simp add: comp_def)
  qed

  \<comment> \<open>...which is exactly the union of the per-face TypeVars: only interfaces
     declare TypeVars, only implementations carry substitutions, and per
     module the two agree - with both faces always in the list together.\<close>
  have TV_dom: "funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) faces) = fmdom \<sigma>"
  proof (rule fset_eqI)
    fix v
    show "v |\<in>| funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) faces)
            \<longleftrightarrow> v |\<in>| fmdom \<sigma>"
    proof
      assume "v |\<in>| funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) faces)"
      then obtain kk where kk_in: "kk \<in> set (face_keys names)"
          and v_kk: "v |\<in>| TE_TypeVars (CM_TyEnv (face_module ps kk))"
        unfolding faces_def by (auto simp: funion_list_member)
      have n_dom: "fst kk |\<in>| fmdom ps" using key_dom[OF kk_in] .
      have not_impl: "\<not> snd kk"
      proof
        assume "snd kk"
        then have "TE_TypeVars (CM_TyEnv (face_module ps kk)) = {||}"
          using state_impl_tyvars[OF st(1) n_dom] by (simp add: face_module_def)
        then show False using v_kk by simp
      qed
      have "v |\<in>| TE_TypeVars (CM_TyEnv (state_iface ps (fst kk)))"
        using v_kk not_impl by (simp add: face_module_def)
      then have v_sub: "v |\<in>| fmdom (CM_TypeSubst (state_impl ps (fst kk)))"
        using state_impl_facts(3)[OF st(1) n_dom] by simp
      have impl_in: "(fst kk, True) \<in> set (face_keys names)"
        using face_keys_impl_in face_keys_fst[OF kk_in] by blast
      have w_in: "fmdom (CM_TypeSubst (face_module ps (fst kk, True)))
                    \<in> set (map (\<lambda>x. fmdom (CM_TypeSubst x)) faces)"
        using impl_in unfolding faces_def by auto
      have "v |\<in>| fmdom (CM_TypeSubst (face_module ps (fst kk, True)))"
        using v_sub by (simp add: fm_impl)
      then have "v |\<in>| funion_list (map (\<lambda>x. fmdom (CM_TypeSubst x)) faces)"
        using w_in unfolding funion_list_member by blast
      then show "v |\<in>| fmdom \<sigma>" unfolding dom_\<sigma> .
    next
      assume "v |\<in>| fmdom \<sigma>"
      then obtain kk where kk_in: "kk \<in> set (face_keys names)"
          and v_kk: "v |\<in>| fmdom (CM_TypeSubst (face_module ps kk))"
        unfolding dom_\<sigma> faces_def by (auto simp: funion_list_member)
      have n_dom: "fst kk |\<in>| fmdom ps" using key_dom[OF kk_in] .
      have is_impl: "snd kk"
      proof (rule ccontr)
        assume "\<not> snd kk"
        then have "CM_TypeSubst (face_module ps kk) = fmempty"
          using state_iface_facts(1)[OF st(1) n_dom] by (simp add: face_module_def)
        then show False using v_kk by simp
      qed
      have "v |\<in>| fmdom (CM_TypeSubst (state_impl ps (fst kk)))"
        using v_kk is_impl by (simp add: face_module_def)
      then have v_tv: "v |\<in>| TE_TypeVars (CM_TyEnv (state_iface ps (fst kk)))"
        using state_impl_facts(3)[OF st(1) n_dom] by simp
      have iface_in: "(fst kk, False) \<in> set (face_keys names)"
        using face_keys_iface_in face_keys_fst[OF kk_in] by blast
      have w_in: "TE_TypeVars (CM_TyEnv (face_module ps (fst kk, False)))
                    \<in> set (map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) faces)"
        using iface_in unfolding faces_def by auto
      have "v |\<in>| TE_TypeVars (CM_TyEnv (face_module ps (fst kk, False)))"
        using v_tv by (simp add: fm_iface)
      then show "v |\<in>| funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) faces)"
        using w_in unfolding funion_list_member by blast
    qed
  qed

  have tv_empty: "TE_TypeVars (CM_TyEnv prog) = {||}"
    unfolding prog_eq link_result_def by (simp add: TV_dom)

  \<comment> \<open>The linked declaration/definition domains, as unions over the faces.\<close>
  have dom_glob: "fmdom (CM_GlobalVars prog)
      = funion_list (map (\<lambda>x. fmdom (CM_GlobalVars x)) faces)"
    unfolding prog_eq link_result_def by (simp add: fmdom_fmlist_union comp_def)
  have dom_fun: "fmdom (CM_Functions prog)
      = funion_list (map (\<lambda>x. fmdom (CM_Functions x)) faces)"
    unfolding prog_eq link_result_def by (simp add: fmdom_fmlist_union comp_def)
  have dom_tyg: "fmdom (TE_GlobalVars (CM_TyEnv prog))
      = funion_list (map (\<lambda>x. fmdom (TE_GlobalVars (CM_TyEnv x))) faces)"
    unfolding prog_eq link_result_def by (simp add: fmdom_fmlist_union comp_def)
  have dom_tyf: "fmdom (TE_Functions (CM_TyEnv prog))
      = funion_list (map (\<lambda>x. fmdom (TE_Functions (CM_TyEnv x))) faces)"
    unfolding prog_eq link_result_def by (simp add: fmdom_fmlist_union comp_def)

  \<comment> \<open>Witness assembly for the definition maps: a name defined by either face
     of an in-list module is in the linked definition map.\<close>
  have face_def_glob: "v |\<in>| fmdom (CM_GlobalVars prog)"
    if v_in: "v |\<in>| fmdom (CM_GlobalVars (state_iface ps n))
              \<or> v |\<in>| fmdom (CM_GlobalVars (state_impl ps n))"
    and n_in: "n \<in> set names" for v n
  proof -
    have if_in: "(n, False) \<in> set (face_keys names)"
     and ii_in: "(n, True) \<in> set (face_keys names)"
      using face_keys_iface_in[OF n_in] face_keys_impl_in[OF n_in] .
    have w1: "fmdom (CM_GlobalVars (face_module ps (n, False)))
                \<in> set (map (\<lambda>x. fmdom (CM_GlobalVars x)) faces)"
     and w2: "fmdom (CM_GlobalVars (face_module ps (n, True)))
                \<in> set (map (\<lambda>x. fmdom (CM_GlobalVars x)) faces)"
      using if_in ii_in unfolding faces_def by auto
    from v_in have "v |\<in>| fmdom (CM_GlobalVars (face_module ps (n, False)))
                    \<or> v |\<in>| fmdom (CM_GlobalVars (face_module ps (n, True)))"
      by (simp add: fm_iface fm_impl)
    then show ?thesis
      using w1 w2 unfolding dom_glob funion_list_member by blast
  qed
  have face_def_fun: "v |\<in>| fmdom (CM_Functions prog)"
    if v_in: "v |\<in>| fmdom (CM_Functions (state_iface ps n))
              \<or> v |\<in>| fmdom (CM_Functions (state_impl ps n))"
    and n_in: "n \<in> set names" for v n
  proof -
    have if_in: "(n, False) \<in> set (face_keys names)"
     and ii_in: "(n, True) \<in> set (face_keys names)"
      using face_keys_iface_in[OF n_in] face_keys_impl_in[OF n_in] .
    have w1: "fmdom (CM_Functions (face_module ps (n, False)))
                \<in> set (map (\<lambda>x. fmdom (CM_Functions x)) faces)"
     and w2: "fmdom (CM_Functions (face_module ps (n, True)))
                \<in> set (map (\<lambda>x. fmdom (CM_Functions x)) faces)"
      using if_in ii_in unfolding faces_def by auto
    from v_in have "v |\<in>| fmdom (CM_Functions (face_module ps (n, False)))
                    \<or> v |\<in>| fmdom (CM_Functions (face_module ps (n, True)))"
      by (simp add: fm_iface fm_impl)
    then show ?thesis
      using w1 w2 unfolding dom_fun funion_list_member by blast
  qed

  \<comment> \<open>Globals: declared implies defined...\<close>
  have g_sub1: "fmdom (TE_GlobalVars (CM_TyEnv prog)) |\<subseteq>| fmdom (CM_GlobalVars prog)"
  proof
    fix v assume "v |\<in>| fmdom (TE_GlobalVars (CM_TyEnv prog))"
    then obtain kk where kk_in: "kk \<in> set (face_keys names)"
        and v_kk: "v |\<in>| fmdom (TE_GlobalVars (CM_TyEnv (face_module ps kk)))"
      unfolding dom_tyg faces_def by (auto simp: funion_list_member)
    have n_dom: "fst kk |\<in>| fmdom ps" using key_dom[OF kk_in] .
    have n_in: "fst kk \<in> set names" using face_keys_fst[OF kk_in] .
    show "v |\<in>| fmdom (CM_GlobalVars prog)"
    proof (cases "snd kk")
      case True
      then have "v |\<in>| fmdom (CM_GlobalVars (state_impl ps (fst kk)))"
        using v_kk state_defs_facts(3)[OF st(1) n_dom]
        by (auto simp: face_module_def dest: fsubsetD)
      then show ?thesis using face_def_glob n_in by blast
    next
      case False
      then have "v |\<in>| fmdom (CM_GlobalVars (state_iface ps (fst kk)))
                   |\<union>| fmdom (CM_GlobalVars (state_impl ps (fst kk)))"
        using v_kk state_defs_facts(1)[OF st(1) n_dom]
        by (auto simp: face_module_def dest: fsubsetD)
      then show ?thesis using face_def_glob n_in by blast
    qed
  qed
  \<comment> \<open>...and defined implies declared, from well-typedness.\<close>
  have wt: "core_module_well_typed prog"
    using compile_program_well_typed[OF cp decls] .
  have g_sub2: "fmdom (CM_GlobalVars prog) |\<subseteq>| fmdom (TE_GlobalVars (CM_TyEnv prog))"
    using core_module_well_typed_defined_declared(1)[OF wt] .

  \<comment> \<open>Functions, the same way.\<close>
  have f_sub1: "fmdom (TE_Functions (CM_TyEnv prog)) |\<subseteq>| fmdom (CM_Functions prog)"
  proof
    fix v assume "v |\<in>| fmdom (TE_Functions (CM_TyEnv prog))"
    then obtain kk where kk_in: "kk \<in> set (face_keys names)"
        and v_kk: "v |\<in>| fmdom (TE_Functions (CM_TyEnv (face_module ps kk)))"
      unfolding dom_tyf faces_def by (auto simp: funion_list_member)
    have n_dom: "fst kk |\<in>| fmdom ps" using key_dom[OF kk_in] .
    have n_in: "fst kk \<in> set names" using face_keys_fst[OF kk_in] .
    show "v |\<in>| fmdom (CM_Functions prog)"
    proof (cases "snd kk")
      case True
      then have "v |\<in>| fmdom (CM_Functions (state_impl ps (fst kk)))"
        using v_kk state_defs_facts(4)[OF st(1) n_dom]
        by (auto simp: face_module_def dest: fsubsetD)
      then show ?thesis using face_def_fun n_in by blast
    next
      case False
      then have "v |\<in>| fmdom (CM_Functions (state_iface ps (fst kk)))
                   |\<union>| fmdom (CM_Functions (state_impl ps (fst kk)))"
        using v_kk state_defs_facts(2)[OF st(1) n_dom]
        by (auto simp: face_module_def dest: fsubsetD)
      then show ?thesis using face_def_fun n_in by blast
    qed
  qed
  have f_sub2: "fmdom (CM_Functions prog) |\<subseteq>| fmdom (TE_Functions (CM_TyEnv prog))"
    using core_module_well_typed_defined_declared(2)[OF wt] .

  show ?thesis
    unfolding core_module_closed_def
    using fsubset_antisym[OF g_sub1 g_sub2] fsubset_antisym[OF f_sub1 f_sub2] tv_empty
    by blast
qed

end
