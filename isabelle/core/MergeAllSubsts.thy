theory MergeAllSubsts
  imports LinkError SubstClosureExistsUnique
    "../graph/Dependency" "../graph/DependencyRel"
    "../util/FmapDisjointUnion"
begin

(* The **merge_all_substs** function merges a list of substitutions. For example,
   given [A := B] and [B := i32] as input, it returns [A := i32, B := i32].

   This is used during linking to merge together the CM_TypeSubsts of different
   modules.

   The disjointness check and the union of the input substitutions are the
   generic finite-map operations of util/FmapDisjointUnion.thy (fmdisjoint_list,
   fmlist_union, and the fused fmunion_disjoint_all).

   merge_all_substs is **executable**. Its behaviour is specified by the following
   theorems:

     merge_all_substs_Inr_iff:
       merge_all_substs ss = Inr \<sigma> \<longleftrightarrow>
         fmdisjoint_list ss
         \<and> acyclic_subst_deps (fmlist_union ss)
         \<and> is_subst_closure (fmlist_union ss) \<sigma>

     merge_all_substs_LinkConflict_iff:
       "(\<exists>names. merge_all_substs ss = Inl (LinkConflict names)) \<longleftrightarrow>
         \<not> fmdisjoint_list ss"

     merge_all_substs_LinkCycle_iff:
       "(\<exists>names. merge_all_substs ss = Inl (LinkCycle names)) \<longleftrightarrow>
         fmdisjoint_list ss \<and> \<not> acyclic_subst_deps (fmlist_union ss)"

   In other words, merge_all_substs succeeds, returning the (unique) idempotent
   closure, exactly when the input substitutions are disjoint and their dependency
   relation is acyclic. Otherwise, it returns an appropriate error (LinkConflict
   if the substitutions are not disjoint; LinkCycle if they are disjoint but there
   is a dependency cycle).

   We also prove merge_all_substs_perm, which states that merge_all_substs is
   insensitive to the order in which the inputs are provided (except perhaps that
   in the error case, the exact error produced might depend on the input order).
*)


(* ========================================================================== *)
(* The dependency-ordered resolution of the union *)
(* ========================================================================== *)

(* The adjacency function for the abstract-type dependency graph: T's
   dependencies are the domain variables occurring in u(T).

   Executable: type_tyvars_list (CoreFreeVars.thy) lists the tyvars of a type,
   and we keep only those that are themselves domain keys. The list may contain
   duplicates (a tyvar occurring twice), which is harmless - the SCC sorter reads
   adjacency as a set of edges. *)
definition subst_dep_list :: "TypeSubst \<Rightarrow> string \<Rightarrow> string list" where
  "subst_dep_list u T =
     filter (\<lambda>T'. T' |\<in>| fmdom u) (type_tyvars_list (the (fmlookup u T)))"

(* The domain of u, listed deterministically. These are the "items" handed to the
   generic dependency sorter (getName = id, getDeps = subst_dep_list u).
   Executable: sorted_list_of_fset over the finite map domain. *)
definition subst_dom_list :: "TypeSubst \<Rightarrow> string list" where
  "subst_dom_list u = sorted_list_of_fset (fmdom u)"

(* Fold the per-variable equations of u into an accumulator in resolution order
   (dependencies first). Each step composes the running accumulator with the
   singleton {| T \<mapsto> u(T) |}; because dependencies are already resolved in acc,
   apply_subst acc (u T) grounds T in one application. Executable as written. *)
definition build_closure :: "TypeSubst \<Rightarrow> string list \<Rightarrow> TypeSubst" where
  "build_closure u order =
     foldl (\<lambda>acc T. compose_subst acc (fmupd T (the (fmlookup u T)) fmempty))
           fmempty
           order"


(* ========================================================================== *)
(* Error payloads: the offending type names                                   *)
(* ========================================================================== *)

(* The LinkConflict payload (the multiply-defined type names) comes from
   fmunion_disjoint_all's Inl branch (fmdup_keys, util/FmapDisjointUnion.thy).
   Only the LinkCycle payload is computed here. *)

(* The type names involved in dependency cycles, for the LinkCycle payload:
   the members of every non-singleton SCC (multi-variable cycles), together
   with the self-loops (which are singleton SCCs, missed by the length check).
   Computed from data already at hand at the error site - no new analysis. *)
definition cycle_names :: "TypeSubst \<Rightarrow> string list list \<Rightarrow> string list" where
  "cycle_names u sccs =
     concat (filter (\<lambda>c. 1 < length c) sccs)
     @ filter (\<lambda>T. T \<in> set (subst_dep_list u T)) (subst_dom_list u)"


(* ========================================================================== *)
(* Definition of merge_all_substs *)
(* ========================================================================== *)

(* Executable merge_all_substs function.

   First, we call fmunion_disjoint_all to calculate the disjoint union u of
   the inputs (or fail with LinkConflict if inputs are not pairwise disjoint).

   Then, we call the SCC sort (analyze_dependencies_generic) on u's dependency
   graph. If there is an SCC with length > 1, or a dependency from a type onto
   itself, we fail with LinkCycle.

   Otherwise, we call build_closure to build the idempotent closure in dependency order.

   analyze_dependencies_generic already reverses internally so that dependencies
   precede dependents; on the no-cycle branch every SCC is a singleton, so
   concat sccs lists the domain variables in resolution order. *)

definition merge_all_substs :: "TypeSubst list \<Rightarrow> (LinkError, TypeSubst) sum" where
  "merge_all_substs ss =
     (case fmunion_disjoint_all ss of
        Inl keys \<Rightarrow> Inl (LinkConflict keys)
      | Inr u \<Rightarrow>
          (case analyze_dependencies_generic (subst_dom_list u) id (subst_dep_list u) of
             Inl _ \<Rightarrow> Inl (LinkCycle [])
           | Inr sccs \<Rightarrow>
               if (\<exists>c \<in> set sccs. length c > 1)
                  \<or> (\<exists>T \<in> set (subst_dom_list u). T \<in> set (subst_dep_list u T))
               then Inl (LinkCycle (cycle_names u sccs))
               else Inr (build_closure u (concat sccs))))"


(* ========================================================================== *)
(* Correctness proofs *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* Bridge lemmas: executable list functions vs the spec sets                  *)
(*                                                                            *)
(* merge_all_substs runs subst_dom_list / subst_dep_list (lists), but the     *)
(* closure theory (MergeSubstsHelpers.thy) is stated over the sets fmdom u and *)
(* subst_deps u T. These lemmas connect the two.                              *)
(* -------------------------------------------------------------------------- *)

(* The domain list enumerates exactly the domain, without repeats. *)
lemma set_subst_dom_list:
  "set (subst_dom_list u) = fset (fmdom u)"
  unfolding subst_dom_list_def by simp

lemma distinct_subst_dom_list:
  "distinct (subst_dom_list u)"
  unfolding subst_dom_list_def
  by (simp add: sorted_list_of_fset.rep_eq)

(* The adjacency list of a domain variable T enumerates exactly its dependency
   set subst_deps u T. Stated for T in the domain (the only T the sorter visits);
   there subst_dep_rel's domain guard on T is satisfied. *)
lemma set_subst_dep_list:
  assumes "T |\<in>| fmdom u"
  shows "set (subst_dep_list u T) = subst_deps u T"
proof -
  have "set (subst_dep_list u T)
        = {T' \<in> type_tyvars (the (fmlookup u T)). T' |\<in>| fmdom u}"
    unfolding subst_dep_list_def
    by (auto simp: set_type_tyvars_list)
  also have "\<dots> = subst_deps u T"
    using assms
    unfolding subst_deps_def subst_dep_rel_def by auto
  finally show ?thesis .
qed

(* -------------------------------------------------------------------------- *)
(* Bridge to the spec acyclicity predicate                                    *)
(*                                                                            *)
(* The graph-layer dep_rel of merge_all_substs's sorter inputs is exactly the *)
(* CONVERSE of subst_dep_rel u: the sorter orients edges dependent -> depend- *)
(* ency (getName x, getName y with y in getDeps x), whereas subst_dep_rel is  *)
(* oriented dependency -> dependent (T', T with T' in u T) so that wf recurses *)
(* the resolution direction. Acyclicity is converse-invariant, so the two     *)
(* acyclicity notions coincide.                                               *)
(* -------------------------------------------------------------------------- *)

(* dep_rel of the sorter inputs = converse of subst_dep_rel. *)
lemma dep_rel_eq_converse_subst_dep_rel:
  "dep_rel (subst_dom_list u) id (subst_dep_list u) = (subst_dep_rel u)\<inverse>"
proof -
  have "dep_rel (subst_dom_list u) id (subst_dep_list u)
        = {(x, y) | x y. x \<in> fset (fmdom u) \<and> y \<in> fset (fmdom u)
                       \<and> y \<in> set (subst_dep_list u x)}"
    unfolding dep_rel_def by (simp add: set_subst_dom_list)
  also have "\<dots> = {(x, y) | x y. x |\<in>| fmdom u \<and> y |\<in>| fmdom u
                              \<and> y \<in> type_tyvars (the (fmlookup u x))}"
    by (auto simp: set_subst_dep_list subst_deps_def subst_dep_rel_def)
  also have "\<dots> = (subst_dep_rel u)\<inverse>"
    unfolding subst_dep_rel_def by auto
  finally show ?thesis .
qed

(* The graph-layer acyclicity of the sorter inputs is exactly the spec
   acyclic_subst_deps u. (Acyclicity is invariant under taking the converse.) *)
lemma acyclic_dep_rel_iff_acyclic_subst_deps:
  "acyclic (dep_rel (subst_dom_list u) id (subst_dep_list u)) \<longleftrightarrow> acyclic_subst_deps u"
  unfolding acyclic_subst_deps_def dep_rel_eq_converse_subst_dep_rel
  by simp

(* The two runtime guards of merge_all_substs - "no SCC longer than one" and "no
   self-loop" - hold together exactly when the union's dependency relation is
   acyclic. This is the bridge between the executable cycle test and the spec
   predicate acyclic_subst_deps, instantiating analyze_dependencies_acyclic_iff
   at getName = id, getDeps = subst_dep_list u. *)
lemma merge_all_guards_iff_acyclic:
  assumes "analyze_dependencies_generic (subst_dom_list u) id (subst_dep_list u) = Inr sccs"
  shows "( \<not> (\<exists>c \<in> set sccs. length c > 1)
            \<and> \<not> (\<exists>T \<in> set (subst_dom_list u). T \<in> set (subst_dep_list u T)) )
         \<longleftrightarrow> acyclic_subst_deps u"
proof -
  (* Every returned SCC is non-empty, so "no SCC longer than 1" = "all singletons". *)
  have ne: "\<forall>c \<in> set sccs. c \<noteq> []"
    using analyze_dependencies_generic_non_empty[OF assms] .
  have len_iff: "(\<not> (\<exists>c \<in> set sccs. length c > 1)) \<longleftrightarrow> (\<forall>c \<in> set sccs. length c = 1)"
    using ne by (metis One_nat_def length_0_conv less_one nat_neq_iff)
  (* The self-loop guard (over id) is the negation of the no-self-dependency clause. *)
  have self_iff:
    "(\<not> (\<exists>T \<in> set (subst_dom_list u). T \<in> set (subst_dep_list u T)))
       \<longleftrightarrow> (\<forall>x \<in> set (subst_dom_list u). id x \<notin> set (subst_dep_list u x))"
    by simp
  have "( \<not> (\<exists>c \<in> set sccs. length c > 1)
            \<and> \<not> (\<exists>T \<in> set (subst_dom_list u). T \<in> set (subst_dep_list u T)) )
        \<longleftrightarrow> acyclic (dep_rel (subst_dom_list u) id (subst_dep_list u))"
    using analyze_dependencies_acyclic_iff[OF assms] len_iff self_iff by blast
  thus ?thesis using acyclic_dep_rel_iff_acyclic_subst_deps by simp
qed

(* -------------------------------------------------------------------------- *)
(* Layer 3a: properties of the resolution order                               *)
(*                                                                            *)
(* On the no-cycle branch (every SCC a singleton, no self-loop), order =      *)
(* concat sccs is a repetition-free enumeration of the domain in which every  *)
(* dependency strictly precedes its dependent. These are the only facts about *)
(* the SCC sort that the fold invariant (layer 3b) consumes.                  *)
(* -------------------------------------------------------------------------- *)

(* Abbreviation: the items / getName / getDeps merge_all_substs hands the sorter. *)
abbreviation (input) dep_result :: "TypeSubst \<Rightarrow> (DependencyError, string list list) sum" where
  "dep_result u \<equiv> analyze_dependencies_generic (subst_dom_list u) id (subst_dep_list u)"

context
  fixes u :: TypeSubst and sccs :: "string list list"
  assumes res:        "dep_result u = Inr sccs"
      and singletons: "\<forall>c \<in> set sccs. length c = 1"
begin

(* Each SCC is a singleton: nonempty (non_empty theorem) and length 1. *)
lemma scc_is_singleton:
  assumes "c \<in> set sccs"
  shows "\<exists>x. c = [x]"
proof -
  have "c \<noteq> []" using analyze_dependencies_generic_non_empty[OF res] assms by simp
  moreover have "length c = 1" using singletons assms by simp
  ultimately show ?thesis by (cases c) auto
qed

(* With every SCC a singleton, flattening is just taking the heads. *)
lemma concat_sccs_eq_map_hd:
  "concat sccs = map hd sccs"
proof -
  have "\<forall>c \<in> set sccs. c = [hd c]"
    using scc_is_singleton by (metis list.sel(1))
  thus ?thesis by (induct sccs) auto
qed

(* The order enumerates exactly the domain. *)
lemma set_concat_sccs:
  "set (concat sccs) = fset (fmdom u)"
proof -
  have "mset (concat sccs) = mset (subst_dom_list u)"
    using analyze_dependencies_generic_permutation[OF res] by simp
  hence "set (concat sccs) = set (subst_dom_list u)"
    by (metis set_mset_mset)
  thus ?thesis by (simp add: set_subst_dom_list)
qed

(* ...without repetition (the domain list is distinct and order is a permutation). *)
lemma distinct_concat_sccs:
  "distinct (concat sccs)"
proof -
  have "mset (concat sccs) = mset (subst_dom_list u)"
    using analyze_dependencies_generic_permutation[OF res] by simp
  thus ?thesis
    using distinct_subst_dom_list by (metis distinct_count_atmost_1 set_mset_mset)
qed

(* Strict dependencies-first: if T' is a dependency of T (and T is in the domain),
   then T' appears strictly before T in the resolution order. Uses the topological
   theorem (i <= j) plus the no-self-loop guarantee (T' /= T), which together with
   distinctness gives a strict index inequality. *)
lemma dep_precedes_in_order:
  assumes T_dom:   "T |\<in>| fmdom u"
      and dep:     "T' \<in> subst_deps u T"
      and no_self: "\<forall>S \<in> fset (fmdom u). S \<notin> subst_deps u S"
  shows "\<exists>ip iq. ip < iq \<and> iq < length (concat sccs)
                 \<and> concat sccs ! ip = T' \<and> concat sccs ! iq = T"
proof -
  \<comment> \<open>T and T' are both domain items handed to the sorter.\<close>
  have T'_dom: "T' |\<in>| fmdom u" using dep subst_deps_subset_dom by auto
  have T_item: "T \<in> set (subst_dom_list u)"
    using T_dom by (simp add: set_subst_dom_list)
  have T'_item: "T' \<in> set (subst_dom_list u)"
    using T'_dom by (simp add: set_subst_dom_list)
  \<comment> \<open>The dependency edge, in the getDeps form the topological theorem wants.\<close>
  have edge: "id T' \<in> set (subst_dep_list u T)"
    using dep T_dom by (simp add: set_subst_dep_list)
  \<comment> \<open>The topological theorem gives SCC indices i <= j with T' in sccs!i, T in sccs!j.\<close>
  obtain i j where ij: "i \<le> j" "i < length sccs" "j < length sccs"
                       "T' \<in> set (sccs ! i)" "T \<in> set (sccs ! j)"
    using analyze_dependencies_generic_topological_order[OF res T_item T'_item edge]
    by blast
  \<comment> \<open>With singletons, sccs!k = [hd (sccs!k)] = [concat sccs ! k].\<close>
  have hd_k: "\<And>k. k < length sccs \<Longrightarrow> sccs ! k = [concat sccs ! k]"
  proof -
    fix k assume k: "k < length sccs"
    have "sccs ! k \<in> set sccs" using k by simp
    then obtain x where "sccs ! k = [x]" using scc_is_singleton by blast
    moreover have "concat sccs ! k = hd (sccs ! k)"
      using k by (simp add: concat_sccs_eq_map_hd)
    ultimately show "sccs ! k = [concat sccs ! k]" by simp
  qed
  have len_eq: "length (concat sccs) = length sccs"
    by (simp add: concat_sccs_eq_map_hd)
  \<comment> \<open>Read off the concat positions.\<close>
  have pos_i: "concat sccs ! i = T'" using ij(2,4) hd_k[OF ij(2)] by simp
  have pos_j: "concat sccs ! j = T" using ij(3,5) hd_k[OF ij(3)] by simp
  \<comment> \<open>T' /= T (no self-loop), and concat sccs is distinct, so i /= j, hence i < j.\<close>
  have "T' \<noteq> T" using dep no_self T_dom by (metis T'_dom)
  hence "i \<noteq> j" using pos_i pos_j by auto
  hence "i < j" using ij(1) by simp
  thus ?thesis using ij(2,3) pos_i pos_j len_eq by auto
qed

end

(* -------------------------------------------------------------------------- *)
(* Layer 3b: the fold invariant                                               *)
(*                                                                            *)
(* build_closure u order folds the per-variable equations of u into an        *)
(* accumulator in dependency order. We show that, whenever order is a         *)
(* repetition-free enumeration of fmdom u in which every dependency strictly  *)
(* precedes its dependent, build_closure u order is the idempotent closure of *)
(* u (is_subst_closure u (build_closure u order)).                            *)
(* -------------------------------------------------------------------------- *)

(* The fold step, rewritten without compose_subst: composing the accumulator
   with the singleton {| T \<mapsto> ty |} just adds {| T \<mapsto> apply_subst acc ty |}. *)
lemma step_eq:
  "compose_subst acc (fmupd T ty fmempty)
     = acc ++\<^sub>f fmupd T (apply_subst acc ty) fmempty"
  unfolding compose_subst_def by (simp add: fmmap_fmupd)

(* The accumulator after processing the first k entries of order. *)
definition bc_take :: "TypeSubst \<Rightarrow> string list \<Rightarrow> nat \<Rightarrow> TypeSubst" where
  "bc_take u order k =
     foldl (\<lambda>acc T. compose_subst acc (fmupd T (the (fmlookup u T)) fmempty))
           fmempty
           (take k order)"

lemma bc_take_0 [simp]: "bc_take u order 0 = fmempty"
  unfolding bc_take_def by simp

lemma bc_take_full: "bc_take u order (length order) = build_closure u order"
  unfolding bc_take_def build_closure_def by simp

(* Unfolding one more step: bc_take at k+1 adds the entry for order!k. *)
lemma bc_take_Suc:
  assumes "k < length order"
  shows "bc_take u order (Suc k)
           = bc_take u order k
               ++\<^sub>f fmupd (order ! k)
                        (apply_subst (bc_take u order k) (the (fmlookup u (order ! k))))
                        fmempty"
proof -
  have "take (Suc k) order = take k order @ [order ! k]"
    using assms by (simp add: take_Suc_conv_app_nth)
  thus ?thesis
    unfolding bc_take_def by (simp add: step_eq)
qed

(* The range tyvars of acc ++f {| T \<mapsto> v |} are those of acc together with the
   tyvars of the single new value v. *)
lemma subst_range_tyvars_add_singleton:
  "subst_range_tyvars (acc ++\<^sub>f fmupd T v fmempty)
     \<subseteq> subst_range_tyvars acc \<union> type_tyvars v"
proof
  fix x assume "x \<in> subst_range_tyvars (acc ++\<^sub>f fmupd T v fmempty)"
  then obtain ty where ty_ran: "ty \<in> fmran' (acc ++\<^sub>f fmupd T v fmempty)"
                   and x_ty: "x \<in> type_tyvars ty"
    unfolding subst_range_tyvars_def by auto
  from ty_ran obtain n where look: "fmlookup (acc ++\<^sub>f fmupd T v fmempty) n = Some ty"
    by (auto simp: fmlookup_ran'_iff)
  show "x \<in> subst_range_tyvars acc \<union> type_tyvars v"
  proof (cases "n = T")
    case True
    hence "ty = v" using look by simp
    thus ?thesis using x_ty by simp
  next
    case False
    hence "fmlookup acc n = Some ty" using look by (auto split: if_splits)
    hence "ty \<in> fmran' acc" by (auto simp: fmran'I)
    thus ?thesis using x_ty unfolding subst_range_tyvars_def by auto
  qed
qed

lemma subst_range_tyvars_empty [simp]:
  "subst_range_tyvars fmempty = {}"
  unfolding subst_range_tyvars_def by (simp add: fmran'_alt_def)

(* The fold invariant, by induction on the prefix length k. After processing the
   first k entries of order:
   - the domain is exactly those k entries;
   - the accumulator's range mentions no domain variable of u (range_clean) -
     this is the load-bearing strengthening: it gives idempotence (since the
     processed domain is a subset of fmdom u), and it makes resolved values
     *stable* under later steps (a later binding is at a domain variable, which
     the value does not mention);
   - each processed entry satisfies the closure equation against the current acc.
   The precedence hypothesis - every dependency of order!j sits at an earlier
   index - is what lets each step ground its variable in one application. *)
lemma build_closure_invariant:
  assumes dist:   "distinct order"
      and dom_eq: "set order = fset (fmdom u)"
      and deps_before:
            "\<And>j T'. j < length order \<Longrightarrow> T' \<in> subst_deps u (order ! j)
                    \<Longrightarrow> \<exists>i < j. order ! i = T'"
      and k_le: "k \<le> length order"
  shows "fmdom (bc_take u order k) = fset_of_list (take k order)
       \<and> subst_range_tyvars (bc_take u order k) \<inter> fset (fmdom u) = {}
       \<and> (\<forall>j < k. fmlookup (bc_take u order k) (order ! j)
                   = Some (apply_subst (bc_take u order k) (the (fmlookup u (order ! j)))))"
  using k_le
proof (induction k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have k_lt: "k < length order" using Suc.prems by simp
  have IH: "fmdom (bc_take u order k) = fset_of_list (take k order)
          \<and> subst_range_tyvars (bc_take u order k) \<inter> fset (fmdom u) = {}
          \<and> (\<forall>j < k. fmlookup (bc_take u order k) (order ! j)
                      = Some (apply_subst (bc_take u order k) (the (fmlookup u (order ! j)))))"
    using Suc.IH k_lt by simp
  define acc where "acc = bc_take u order k"
  define T  where "T = order ! k"
  define v  where "v = apply_subst acc (the (fmlookup u T))"
  have dom_acc: "fmdom acc = fset_of_list (take k order)" using IH acc_def by simp
  have clean_acc: "subst_range_tyvars acc \<inter> fset (fmdom u) = {}" using IH acc_def by simp
  have eqs_acc: "\<forall>j < k. fmlookup acc (order ! j)
                          = Some (apply_subst acc (the (fmlookup u (order ! j))))"
    using IH acc_def by simp

  \<comment> \<open>The new accumulator.\<close>
  have step: "bc_take u order (Suc k) = acc ++\<^sub>f fmupd T v fmempty"
    unfolding acc_def T_def v_def using bc_take_Suc[OF k_lt] by simp

  \<comment> \<open>Basic facts about T and its stored value v.\<close>
  have T_in_dom_u: "T |\<in>| fmdom u"
    using dom_eq k_lt T_def by (metis nth_mem)
  have T_notin_set: "T \<notin> set (take k order)"
  proof
    assume "T \<in> set (take k order)"
    then obtain i where i: "i < length (take k order)" "take k order ! i = T"
      by (meson in_set_conv_nth)
    hence "i < k" using k_lt by simp
    hence "order ! i = T" using i by simp
    moreover have "order ! k = T" using T_def by simp
    ultimately show False using dist k_lt \<open>i < k\<close>
      by (metis nth_eq_iff_index_eq order.strict_trans nat_neq_iff)
  qed
  have T_notin_acc: "T |\<notin>| fmdom acc"
    using T_notin_set dom_acc by (simp add: fset_of_list_elem)

  \<comment> \<open>Every domain variable of u(T) lies in fmdom acc (its deps precede T).\<close>
  have uT_domvars_in_acc: "type_tyvars (the (fmlookup u T)) \<inter> fset (fmdom u) \<subseteq> fset (fmdom acc)"
  proof
    fix T' assume T'_in: "T' \<in> type_tyvars (the (fmlookup u T)) \<inter> fset (fmdom u)"
    hence "T' \<in> subst_deps u T"
      using T_in_dom_u unfolding subst_deps_def subst_dep_rel_def by auto
    then obtain i where "i < k" "order ! i = T'"
      using deps_before[of k T'] k_lt T_def by auto
    thus "T' \<in> fset (fmdom acc)"
      using dom_acc k_lt
      by (auto simp: fset_of_list_elem in_set_conv_nth)
  qed

  \<comment> \<open>v's tyvars avoid all of fmdom u: domain-vars of u(T) are resolved away by acc,
      and the rest come from acc's (clean) range or are non-domain vars of u(T).\<close>
  have v_clean: "type_tyvars v \<inter> fset (fmdom u) = {}"
  proof -
    have "type_tyvars v
            \<subseteq> (type_tyvars (the (fmlookup u T)) - fset (fmdom acc)) \<union> subst_range_tyvars acc"
      unfolding v_def by (rule apply_subst_tyvars_result)
    moreover have "(type_tyvars (the (fmlookup u T)) - fset (fmdom acc)) \<inter> fset (fmdom u) = {}"
      using uT_domvars_in_acc by auto
    ultimately show ?thesis using clean_acc by auto
  qed

  \<comment> \<open>Domain.\<close>
  have dom_new: "fmdom (bc_take u order (Suc k)) = fset_of_list (take (Suc k) order)"
    using step dom_acc k_lt T_def
    by (simp add: take_Suc_conv_app_nth)

  \<comment> \<open>Range stays clean: range is acc's range plus v's tyvars, both avoiding fmdom u.\<close>
  have clean_new: "subst_range_tyvars (bc_take u order (Suc k)) \<inter> fset (fmdom u) = {}"
  proof -
    have "subst_range_tyvars (bc_take u order (Suc k))
            \<subseteq> subst_range_tyvars acc \<union> type_tyvars v"
      using step subst_range_tyvars_add_singleton by simp
    thus ?thesis using clean_acc v_clean by auto
  qed

  \<comment> \<open>Closure equations: the new entry T, and the preserved earlier entries.\<close>
  have eqs_new: "\<forall>j < Suc k. fmlookup (bc_take u order (Suc k)) (order ! j)
                  = Some (apply_subst (bc_take u order (Suc k)) (the (fmlookup u (order ! j))))"
  proof (intro allI impI)
    fix j assume j: "j < Suc k"
    show "fmlookup (bc_take u order (Suc k)) (order ! j)
            = Some (apply_subst (bc_take u order (Suc k)) (the (fmlookup u (order ! j))))"
    proof (cases "j = k")
      case True
      \<comment> \<open>The freshly added entry: stored value is v = apply_subst acc (u T),
          and apply_subst on the new acc agrees with apply_subst acc (v is stable).\<close>
      have look_T: "fmlookup (bc_take u order (Suc k)) (order ! j) = Some v"
        using step True T_def by simp
      have "apply_subst (bc_take u order (Suc k)) (the (fmlookup u (order ! j)))
              = apply_subst acc (the (fmlookup u T))"
      proof -
        \<comment> \<open>The new acc applied to u(T) equals acc applied to u(T): the only new
            binding is at T itself, and T does not occur in u(T) (no self-loop) -
            shown below via the cong lemma. Hence the stored value is exactly v.\<close>
        have "apply_subst (bc_take u order (Suc k)) (the (fmlookup u T)) = v"
        proof -
          have "apply_subst (bc_take u order (Suc k)) (the (fmlookup u T))
                  = apply_subst (acc ++\<^sub>f fmupd T v fmempty) (the (fmlookup u T))"
            using step by simp
          also have "\<dots> = apply_subst acc (the (fmlookup u T))"
          proof (rule apply_subst_cong_on_tyvars)
            fix w assume w_in: "w \<in> type_tyvars (the (fmlookup u T))"
            show "fmlookup (acc ++\<^sub>f fmupd T v fmempty) w = fmlookup acc w"
            proof (cases "w |\<in>| fmdom acc")
              case True
              hence "w \<noteq> T" using T_notin_acc by auto
              thus ?thesis by simp
            next
              case False
              \<comment> \<open>w not yet resolved; then w is not a domain var of u (else it'd be a
                  dep of T, already in acc), and w /= T, so both sides miss it.\<close>
              have "w \<notin> fset (fmdom u)"
                using w_in uT_domvars_in_acc False by auto
              hence "w \<noteq> T" using T_in_dom_u by metis
              thus ?thesis using False by auto
            qed
          qed
          finally show ?thesis unfolding v_def .
        qed
        thus ?thesis using True T_def v_def by simp
      qed
      thus ?thesis using look_T True T_def v_def by simp
    next
      case False
      hence j_lt_k: "j < k" using j by simp
      \<comment> \<open>An earlier entry: lookup unchanged (order!j /= T), value stable.\<close>
      have neq: "order ! j \<noteq> T"
        using dist j_lt_k k_lt T_def by (simp add: distinct_conv_nth)
      have look_j: "fmlookup (bc_take u order (Suc k)) (order ! j) = fmlookup acc (order ! j)"
        using step neq by simp
      have stored: "fmlookup acc (order ! j)
                      = Some (apply_subst acc (the (fmlookup u (order ! j))))"
        using eqs_acc j_lt_k by simp
      \<comment> \<open>T does not occur in u(order!j): otherwise T would be a dependency of order!j,
          hence (deps_before) precede it - but T = order!k comes strictly after.\<close>
      have T_notin_uj: "T \<notin> type_tyvars (the (fmlookup u (order ! j)))"
      proof
        assume T_in: "T \<in> type_tyvars (the (fmlookup u (order ! j)))"
        have oj_dom: "order ! j |\<in>| fmdom u"
          using dom_eq j_lt_k k_lt by (metis nth_mem less_trans)
        have "T \<in> subst_deps u (order ! j)"
          using T_in T_in_dom_u oj_dom unfolding subst_deps_def subst_dep_rel_def by auto
        then obtain i where "i < j" "order ! i = T"
          using deps_before[of j T] j_lt_k k_lt by auto
        moreover have "order ! k = T" using T_def by simp
        ultimately show False using dist k_lt j_lt_k
          by (metis nth_eq_iff_index_eq less_trans less_not_refl)
      qed
      \<comment> \<open>So the new binding (only at T) does not affect apply_subst on u(order!j).\<close>
      have "apply_subst (bc_take u order (Suc k)) (the (fmlookup u (order ! j)))
              = apply_subst acc (the (fmlookup u (order ! j)))"
      proof (rule apply_subst_cong_on_tyvars)
        fix w assume "w \<in> type_tyvars (the (fmlookup u (order ! j)))"
        hence "w \<noteq> T" using T_notin_uj by auto
        thus "fmlookup (bc_take u order (Suc k)) w = fmlookup acc w"
          using step by simp
      qed
      thus ?thesis using look_j stored by simp
    qed
  qed

  from dom_new clean_new eqs_new show ?case by blast
qed

(* Packaging the invariant at the full length: build_closure u order is *the*
   idempotent closure of u, whenever order is a repetition-free enumeration of
   fmdom u with every dependency strictly before its dependent. *)
lemma build_closure_is_closure:
  assumes dist:   "distinct order"
      and dom_eq: "set order = fset (fmdom u)"
      and deps_before:
            "\<And>j T'. j < length order \<Longrightarrow> T' \<in> subst_deps u (order ! j)
                    \<Longrightarrow> \<exists>i < j. order ! i = T'"
  shows "is_subst_closure u (build_closure u order)"
proof -
  define \<sigma> where "\<sigma> = build_closure u order"
  have inv: "fmdom (bc_take u order (length order)) = fset_of_list (take (length order) order)
           \<and> subst_range_tyvars (bc_take u order (length order)) \<inter> fset (fmdom u) = {}
           \<and> (\<forall>j < length order. fmlookup (bc_take u order (length order)) (order ! j)
                = Some (apply_subst (bc_take u order (length order)) (the (fmlookup u (order ! j)))))"
    using build_closure_invariant[OF dist dom_eq deps_before le_refl] .
  have bc: "bc_take u order (length order) = \<sigma>"
    unfolding \<sigma>_def by (rule bc_take_full)
  \<comment> \<open>Domain.\<close>
  have dom_\<sigma>: "fmdom \<sigma> = fmdom u"
  proof -
    have "fmdom \<sigma> = fset_of_list order" using inv bc by simp
    also have "\<dots> = fmdom u"
      using dom_eq by (metis fset_of_list.rep_eq fset_inject)
    finally show ?thesis .
  qed
  \<comment> \<open>Idempotence: the (clean) range avoids fmdom u = fmdom \<sigma>.\<close>
  have idem_\<sigma>: "idempotent_subst \<sigma>"
    unfolding idempotent_subst_def
    using inv bc dom_\<sigma> by auto
  \<comment> \<open>Closure equations, lifted from index form to "for every key of u".\<close>
  have eqs_\<sigma>: "\<And>T ty. fmlookup u T = Some ty \<Longrightarrow> fmlookup \<sigma> T = Some (apply_subst \<sigma> ty)"
  proof -
    fix T ty assume look: "fmlookup u T = Some ty"
    hence "T \<in> fset (fmdom u)" by (simp add: fmlookup_dom_iff)
    then obtain j where j: "j < length order" "order ! j = T"
      using dom_eq by (metis in_set_conv_nth)
    have "fmlookup \<sigma> (order ! j)
            = Some (apply_subst \<sigma> (the (fmlookup u (order ! j))))"
      using inv bc j by auto
    thus "fmlookup \<sigma> T = Some (apply_subst \<sigma> ty)"
      using j look by simp
  qed
  show ?thesis
    unfolding \<sigma>_def[symmetric] is_subst_closure_def
    using idem_\<sigma> dom_\<sigma> eqs_\<sigma> by blast
qed


(* -------------------------------------------------------------------------- *)
(* Success characterization of merge_all_substs                               *)
(*                                                                            *)
(* merge_all_substs ss returns Inr sigma exactly when the inputs are          *)
(* consistent, their union's dependency relation is acyclic, and sigma is the *)
(* (unique) idempotent closure of that union.                                 *)
(* -------------------------------------------------------------------------- *)

(* On the success branch, the order facts from the layer-3a context discharge
   the three hypotheses of build_closure_is_closure, so build_closure u
   (concat sccs) is the idempotent closure of u. *)
lemma merge_all_substs_Inr_is_closure:
  assumes res:   "analyze_dependencies_generic (subst_dom_list u) id (subst_dep_list u) = Inr sccs"
      and sing:  "\<forall>c \<in> set sccs. length c = 1"
      and noself: "\<forall>T \<in> set (subst_dom_list u). T \<notin> set (subst_dep_list u T)"
  shows "is_subst_closure u (build_closure u (concat sccs))"
proof (rule build_closure_is_closure)
  show "distinct (concat sccs)" using distinct_concat_sccs[OF res sing] .
  show "set (concat sccs) = fset (fmdom u)" using set_concat_sccs[OF res sing] .
next
  fix j T'
  assume j: "j < length (concat sccs)"
     and dep: "T' \<in> subst_deps u (concat sccs ! j)"
  \<comment> \<open>The dependent (concat sccs ! j) is in the domain.\<close>
  have T_dom: "concat sccs ! j |\<in>| fmdom u"
    using j set_concat_sccs[OF res sing] by (metis nth_mem set_subst_dom_list)
  \<comment> \<open>Recast the no-self-loop guard in the subst_deps form dep_precedes_in_order wants.\<close>
  have noself': "\<forall>S \<in> fset (fmdom u). S \<notin> subst_deps u S"
  proof (intro ballI notI)
    fix S assume "S \<in> fset (fmdom u)" "S \<in> subst_deps u S"
    then have "S |\<in>| fmdom u" by simp
    then have "S \<in> set (subst_dep_list u S)"
      using \<open>S \<in> subst_deps u S\<close> set_subst_dep_list by blast
    moreover have "S \<in> set (subst_dom_list u)"
      using \<open>S \<in> fset (fmdom u)\<close> set_subst_dom_list by blast
    ultimately show False using noself by blast
  qed
  obtain ip iq where "ip < iq" "iq < length (concat sccs)"
    "concat sccs ! ip = T'" "concat sccs ! iq = concat sccs ! j"
    using dep_precedes_in_order[OF res sing T_dom dep noself'] by blast
  \<comment> \<open>iq = j by distinctness, so ip < j with concat sccs ! ip = T'.\<close>
  moreover have "iq = j"
    using \<open>iq < length (concat sccs)\<close> j \<open>concat sccs ! iq = concat sccs ! j\<close>
          distinct_concat_sccs[OF res sing] nth_eq_iff_index_eq by blast
  ultimately show "\<exists>i < j. concat sccs ! i = T'" by auto
qed

(* The sorter never errors on merge_all_substs's inputs: the domain list has
   distinct (identity) names, and every adjacency-list entry is itself a domain
   variable. So the Inl DependencyError branch of merge_all_substs is dead. *)
lemma dep_result_never_Inl:
  "\<exists>sccs. analyze_dependencies_generic (subst_dom_list u) id (subst_dep_list u) = Inr sccs"
proof (rule analyze_dependencies_generic_Inr_if)
  show "distinct (map id (subst_dom_list u))"
    using distinct_subst_dom_list by simp
  show "\<forall>item \<in> set (subst_dom_list u).
          set (subst_dep_list u item) \<subseteq> set (map id (subst_dom_list u))"
  proof (intro ballI subsetI)
    fix item dep
    assume "dep \<in> set (subst_dep_list u item)"
    then have "dep |\<in>| fmdom u"
      unfolding subst_dep_list_def by simp
    then show "dep \<in> set (map id (subst_dom_list u))"
      by (simp add: set_subst_dom_list)
  qed
qed

(* ========================================================================== *)
(* The correctness theorems themselves *)
(* ========================================================================== *)

(* merge_all_substs succeeds with result \<sigma> exactly when the input substs are pairwise 
   disjoint, their dependency relation is acyclic, and \<sigma> is the (unique) idempotent
   closure of the disjoint union. *)
theorem merge_all_substs_Inr_iff:
  "merge_all_substs ss = Inr \<sigma> \<longleftrightarrow>
     fmdisjoint_list ss
     \<and> acyclic_subst_deps (fmlist_union ss)
     \<and> is_subst_closure (fmlist_union ss) \<sigma>"
proof -
  define u where "u = fmlist_union ss"
  show ?thesis
  proof (cases "fmdisjoint_list ss")
    case False
    then show ?thesis
      unfolding merge_all_substs_def by (simp add: fmunion_disjoint_all_Inl)
  next
    case cons: True
    have union: "fmunion_disjoint_all ss = Inr u"
      unfolding u_def using cons by (simp add: fmunion_disjoint_all_Inr)
    show ?thesis
    proof (cases "analyze_dependencies_generic (subst_dom_list u) id (subst_dep_list u)")
      case (Inl e)
      \<comment> \<open>This branch is dead: the sorter never errors on these inputs.\<close>
      then show ?thesis using dep_result_never_Inl Inr_Inl_False by metis
    next
      case (Inr sccs)
      show ?thesis
      proof (cases "(\<exists>c \<in> set sccs. length c > 1)
                     \<or> (\<exists>T \<in> set (subst_dom_list u). T \<in> set (subst_dep_list u T))")
        case guards: True
        \<comment> \<open>Cycle detected: some Inl on the left; not acyclic on the right. (Only the
           fact that the result is an Inl matters, not which LinkError it carries.)\<close>
        have lhs: "\<exists>e. merge_all_substs ss = Inl e"
          unfolding merge_all_substs_def using union Inr guards by simp
        have "\<not> acyclic_subst_deps u"
          using guards merge_all_guards_iff_acyclic[OF Inr] by blast
        then show ?thesis using lhs unfolding u_def by auto
      next
        case guards: False
        have sing: "\<forall>c \<in> set sccs. length c = 1"
          using guards analyze_dependencies_generic_non_empty[OF Inr]
          by (metis One_nat_def length_0_conv less_one nat_neq_iff)
        have noself: "\<forall>T \<in> set (subst_dom_list u). T \<notin> set (subst_dep_list u T)"
          using guards by blast
        have lhs: "merge_all_substs ss = Inr (build_closure u (concat sccs))"
          unfolding merge_all_substs_def using union Inr guards by simp
        have acyc: "acyclic_subst_deps u"
          using guards merge_all_guards_iff_acyclic[OF Inr] by blast
        have clos: "is_subst_closure u (build_closure u (concat sccs))"
          using merge_all_substs_Inr_is_closure[OF Inr sing noself] .
        show ?thesis
        proof
          assume "merge_all_substs ss = Inr \<sigma>"
          then have "\<sigma> = build_closure u (concat sccs)" using lhs by simp
          then show "fmdisjoint_list ss \<and> acyclic_subst_deps (fmlist_union ss)
                     \<and> is_subst_closure (fmlist_union ss) \<sigma>"
            using cons acyc clos unfolding u_def by simp
        next
          assume "fmdisjoint_list ss \<and> acyclic_subst_deps (fmlist_union ss)
                  \<and> is_subst_closure (fmlist_union ss) \<sigma>"
          then have "is_subst_closure u \<sigma>" unfolding u_def by simp
          then have "\<sigma> = build_closure u (concat sccs)"
            using clos subst_closure_unique[OF acyc] by blast
          then show "merge_all_substs ss = Inr \<sigma>" using lhs by simp
        qed
      qed
    qed
  qed
qed

(* merge_all_substs fails with LinkConflict exactly when the substitutions are not
   pairwise disjoint (i.e. some type variable is multiply-defined). *)
theorem merge_all_substs_LinkConflict_iff:
  "(\<exists>names. merge_all_substs ss = Inl (LinkConflict names)) \<longleftrightarrow>
    \<not> fmdisjoint_list ss"
proof
  assume "\<exists>names. merge_all_substs ss = Inl (LinkConflict names)"
  then obtain names where conf: "merge_all_substs ss = Inl (LinkConflict names)" by blast
  show "\<not> fmdisjoint_list ss"
  proof
    assume dis: "fmdisjoint_list ss"
    \<comment> \<open>On the disjoint side of the definition the result is a LinkCycle or an Inr,
       never a LinkConflict.\<close>
    define u where "u = fmlist_union ss"
    have union: "fmunion_disjoint_all ss = Inr u"
      unfolding u_def using dis by (simp add: fmunion_disjoint_all_Inr)
    obtain sccs where res: "dep_result u = Inr sccs"
      using dep_result_never_Inl by blast
    show False
    proof (cases "(\<exists>c \<in> set sccs. length c > 1)
                   \<or> (\<exists>T \<in> set (subst_dom_list u). T \<in> set (subst_dep_list u T))")
      case True
      then have "merge_all_substs ss = Inl (LinkCycle (cycle_names u sccs))"
        unfolding merge_all_substs_def using union res by simp
      thus False using conf by simp
    next
      case False
      then have "merge_all_substs ss = Inr (build_closure u (concat sccs))"
        unfolding merge_all_substs_def using union res by simp
      thus False using conf by simp
    qed
  qed
next
  assume "\<not> fmdisjoint_list ss"
  then have "merge_all_substs ss = Inl (LinkConflict (fmdup_keys ss))"
    unfolding merge_all_substs_def by (simp add: fmunion_disjoint_all_Inl)
  thus "\<exists>names. merge_all_substs ss = Inl (LinkConflict names)" by blast
qed

(* merge_all_substs fails with LinkCycle exactly when there is no LinkConflict (so 
   the disjoint union can be formed), but the dependency relation contains a cycle. *)
theorem merge_all_substs_LinkCycle_iff:
  "(\<exists>names. merge_all_substs ss = Inl (LinkCycle names)) \<longleftrightarrow>
    fmdisjoint_list ss \<and> \<not> acyclic_subst_deps (fmlist_union ss)"
proof -
  define u where "u = fmlist_union ss"
  show ?thesis
  proof (cases "fmdisjoint_list ss")
    case False
    \<comment> \<open>Not disjoint: the result is a LinkConflict, not a LinkCycle.\<close>
    then have "merge_all_substs ss = Inl (LinkConflict (fmdup_keys ss))"
      unfolding merge_all_substs_def by (simp add: fmunion_disjoint_all_Inl)
    then show ?thesis using False by simp
  next
    case dis: True
    \<comment> \<open>Disjoint: the sorter succeeds (its error branch is dead), and the cycle
       guards fire exactly when the union's dependency relation is cyclic.\<close>
    have union: "fmunion_disjoint_all ss = Inr u"
      unfolding u_def using dis by (simp add: fmunion_disjoint_all_Inr)
    obtain sccs where res: "dep_result u = Inr sccs"
      using dep_result_never_Inl by blast
    show ?thesis
    proof (cases "(\<exists>c \<in> set sccs. length c > 1)
                   \<or> (\<exists>T \<in> set (subst_dom_list u). T \<in> set (subst_dep_list u T))")
      case guards: True
      have "merge_all_substs ss = Inl (LinkCycle (cycle_names u sccs))"
        unfolding merge_all_substs_def using union res guards by simp
      moreover have "\<not> acyclic_subst_deps u"
        using guards merge_all_guards_iff_acyclic[OF res] by blast
      ultimately show ?thesis using dis unfolding u_def by auto
    next
      case guards: False
      have "merge_all_substs ss = Inr (build_closure u (concat sccs))"
        unfolding merge_all_substs_def using union res guards by simp
      moreover have "acyclic_subst_deps u"
        using guards merge_all_guards_iff_acyclic[OF res] by blast
      ultimately show ?thesis unfolding u_def by auto
    qed
  qed
qed


(* ========================================================================== *)
(* Permutation-invariance                                                     *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* Every conjunct on the right of merge_all_substs_Inr_iff depends only on    *)
(* the *multiset* of inputs: fmdisjoint_list is invariant under reordering,   *)
(* and fmlist_union is order-immaterial on pairwise-disjoint domains (the     *)
(* mset_cong lemmas of util/FmapDisjointUnion.thy). Permutation-invariance of *)
(* merge_all_substs is then immediate from the iff.                           *)
(* This is a sanity check on the definition, not machinery anything           *)
(* downstream consumes. Note it is invariance under REORDERING, not           *)
(* de-duplication: merge_all_substs [s, s] is a LinkConflict for non-empty s  *)
(* (and mset [s, s] \<noteq> mset [s], so the theorem says nothing about it).        *)
(* -------------------------------------------------------------------------- *)

(* The headline law: merge_all_substs is invariant under permuting its input
   list, directly off the success characterization - every conjunct of
   merge_all_substs_Inr_iff depends only on the multiset of inputs. Both
   orderings succeed with the same closure, or both fail. (Stated over Inr:
   we do NOT claim the same LinkError on failure - a different ordering may
   surface a different error first.) *)
theorem merge_all_substs_perm:
  assumes "mset ss = mset ss'"
  shows "merge_all_substs ss = Inr \<sigma> \<longleftrightarrow> merge_all_substs ss' = Inr \<sigma>"
proof -
  have one: "merge_all_substs ys = Inr \<sigma>"
    if ok: "merge_all_substs xs = Inr \<sigma>" and m: "mset xs = mset ys" for xs ys
  proof -
    have disj: "fmdisjoint_list xs"
     and acyc: "acyclic_subst_deps (fmlist_union xs)"
     and clos: "is_subst_closure (fmlist_union xs) \<sigma>"
      using ok merge_all_substs_Inr_iff by auto
    have disj': "fmdisjoint_list ys"
      using fmdisjoint_list_mset_cong[OF m] disj by simp
    have u_eq: "fmlist_union ys = fmlist_union xs"
      using fmlist_union_mset_cong[OF m disj] by simp
    have "fmdisjoint_list ys \<and> acyclic_subst_deps (fmlist_union ys)
          \<and> is_subst_closure (fmlist_union ys) \<sigma>"
      using disj' acyc clos u_eq by simp
    then show ?thesis using merge_all_substs_Inr_iff by blast
  qed
  show ?thesis using one[OF _ assms] one[OF _ assms[symmetric]] by blast
qed

(* Failure-agreement form: two orderings of the same inputs either both
   succeed (necessarily with the same result, by merge_all_substs_perm) or
   both fail. *)
corollary merge_all_substs_perm_fails:
  assumes "mset ss = mset ss'"
  shows "(\<exists>\<sigma>. merge_all_substs ss = Inr \<sigma>) \<longleftrightarrow> (\<exists>\<sigma>. merge_all_substs ss' = Inr \<sigma>)"
  using merge_all_substs_perm[OF assms] by blast


(* ========================================================================== *)
(* Singleton input                                                            *)
(* ========================================================================== *)

(* Merging a single idempotent substitution returns it unchanged: an idempotent
   substitution is its own closure, and its dependency relation is empty, hence
   acyclic. A module's CM_TypeSubst is required to be idempotent, so this is
   the "link one module" case of link_modules (LinkModules.thy). *)
lemma merge_all_substs_singleton:
  assumes "idempotent_subst s"
  shows "merge_all_substs [s] = Inr s"
proof -
  have u: "fmlist_union [s] = s" by simp
  have "fmdisjoint_list [s]" by simp
  moreover have "acyclic_subst_deps (fmlist_union [s])"
    using idempotent_subst_acyclic[OF assms] u by simp
  moreover have "is_subst_closure (fmlist_union [s]) s"
    using is_subst_closure_self[OF assms] u by simp
  ultimately show ?thesis
    by (simp add: merge_all_substs_Inr_iff)
qed

end
