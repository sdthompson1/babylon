theory MergeAllSubsts
  imports MergeSubsts "../graph/Dependency" "../graph/DependencyRel"
begin

(* The merge_all_substs operation: an *executable* version of merging a whole
   list of type substitutions at once.

   merge_substs (MergeSubsts.thy) is the declarative binary specification; folding
   it over a list re-closes a growing accumulator at each of n steps, which is
   O(n^2). merge_all_substs instead computes the same result - the idempotent
   closure of the union of all the input substitutions - in a single batch pass:
   it builds the abstract-type dependency graph, runs the verified Kosaraju SCC
   sorter (via analyze_dependencies_generic, graph/Dependency.thy) to get a
   resolution order (dependencies first) together with the cycle check, then folds
   the per-variable equations into an accumulator in that order with one
   compose_subst each.

   The target equivalence (proved later) is

     merge_all_substs ss = foldl_E merge_substs fmempty ss

   against the *error-propagating* fold foldl_E (Inl short-circuits), since the
   binary merge_substs is (LinkError, TypeSubst) sum-valued.

   merge_all_substs is *executable*: every function it transitively calls must be
   code-generatable. Where an operational definition is most naturally stated as a
   non-executable spec (disjoint_substs, below), a [code] equation is supplied
   so that the spec form is available for proofs while a computable form is what
   actually runs. *)


(* ========================================================================== *)
(* Pairwise domain-disjointness of a whole list of substitutions *)
(* ========================================================================== *)

(* Under the strict linking semantics, the conflict test is domain-disjointness:
   a list of substitutions may be merged only when no abstract type is defined by
   two of them, i.e. their domains are pairwise disjoint. (Same name in two of the
   domains = multiple definition = LinkConflict, regardless of the values.) This
   quantified form is the *specification* - the shape the merge_all_substs /
   merge_substs equivalence proof reasons against; an executable [code] equation is
   provided separately. Note the i \<noteq> j: unlike consistency, disjoint_subst s s is
   false for non-empty s, so the diagonal must be excluded. *)
definition disjoint_substs :: "TypeSubst list \<Rightarrow> bool" where
  "disjoint_substs ss \<equiv>
     \<forall>i j. i < length ss \<and> j < length ss \<and> i \<noteq> j \<longrightarrow> disjoint_subst (ss ! i) (ss ! j)"

(* Executable one-pass disjointness check. We accumulate the domains seen so far
   into a single set of keys; a conflict is a key already seen. Returns Some
   (accumulated keys) on success, None on overlap. As a side effect the success
   result is exactly the domain of the union of all the substitutions. *)
fun disjoint_acc :: "string fset \<Rightarrow> TypeSubst list \<Rightarrow> string fset option" where
  "disjoint_acc acc [] = Some acc"
| "disjoint_acc acc (s # ss) =
     (if fmdom s |\<inter>| acc = {||}
      then disjoint_acc (acc |\<union>| fmdom s) ss
      else None)"

definition disjoint_substs_exec :: "TypeSubst list \<Rightarrow> bool" where
  "disjoint_substs_exec ss \<equiv> disjoint_acc {||} ss \<noteq> None"


(* ========================================================================== *)
(* The union of a list of substitutions *)
(* ========================================================================== *)

(* The raw union of all the input substitutions. Right-biased ++f; under
   disjoint_substs the domains do not overlap, so the order is immaterial.
   Executable as written. *)
definition subst_list_union :: "TypeSubst list \<Rightarrow> TypeSubst" where
  "subst_list_union ss = foldr (++\<^sub>f) ss fmempty"


(* ========================================================================== *)
(* The dependency-ordered resolution of the union *)
(* ========================================================================== *)

(* The adjacency function for the abstract-type dependency graph: T's
   dependencies are the domain variables occurring in u(T).

   Executable: type_tyvars_list (CoreFreeVars.thy) lists the tyvars of a type,
   and we keep only those that are themselves domain keys. The list may contain
   duplicates (a tyvar occurring twice), which is harmless - the SCC sorter reads
   adjacency as a set of edges. set_type_tyvars_list bridges this to the spec set
   subst_deps (MergeSubstsHelpers.thy). *)
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
(* Definition of merge_all_substs *)
(* ========================================================================== *)

(* merge_all_substs ss:
   - LinkConflict if the input domains are not pairwise disjoint (two of them
     define the same abstract type);
   - LinkCycle if the abstract-type dependency relation of the union is cyclic
     (a non-singleton SCC);
   - otherwise the idempotent closure of the union, computed in dependency order.

   The SCC sort (analyze_dependencies_generic) supplies both the resolution order
   and the multi-variable cycle check in one call. Its duplicate-name and
   missing-dependency error branches cannot fire here (domain keys are distinct,
   and subst_dep_list keeps only domain variables), so the Inl DependencyError
   case is dead; we map it to LinkCycle for totality.

   The two cyclicity checks together are the *complete* acyclicity test:
   - a multi-variable cycle (e.g. type a = b; type b = a;) is a non-singleton SCC,
     caught by "length c > 1";
   - a self-loop (e.g. type a = Pair(a, ..);) is a *singleton* SCC, so the SCC
     check misses it; it is caught directly by "T occurs in its own dependency
     list". Unlike the binary merge_substs (whose inputs are assumed idempotent,
     so self-loops cannot arise), merge_all_substs takes arbitrary substitutions,
     so the self-loop case is real and must be rejected explicitly.

   analyze_dependencies_generic already reverses internally so that dependencies
   precede dependents; on the no-cycle branch every SCC is a singleton, so
   concat sccs lists the domain variables in resolution order. *)
definition merge_all_substs :: "TypeSubst list \<Rightarrow> (LinkError, TypeSubst) sum" where
  "merge_all_substs ss =
     (let u = subst_list_union ss in
      if \<not> disjoint_substs ss then Inl LinkConflict
      else case analyze_dependencies_generic (subst_dom_list u) id (subst_dep_list u) of
             Inl _ \<Rightarrow> Inl LinkCycle
           | Inr sccs \<Rightarrow>
               if (\<exists>c \<in> set sccs. length c > 1)
                  \<or> (\<exists>T \<in> set (subst_dom_list u). T \<in> set (subst_dep_list u T))
               then Inl LinkCycle
               else Inr (build_closure u (concat sccs)))"


(* ========================================================================== *)
(* Code equation for disjoint_substs *)
(* ========================================================================== *)

(* disjoint_substs reformulated over set membership for the head element: the
   pairwise condition splits into "s is disjoint from every later element" plus
   "the tail is pairwise disjoint". (We keep the index form for the tail because
   duplicate non-empty elements must register as a conflict.) *)
lemma disjoint_substs_Cons:
  "disjoint_substs (s # ss) \<longleftrightarrow>
     (\<forall>t \<in> set ss. disjoint_subst s t) \<and> disjoint_substs ss"
proof
  assume L: "disjoint_substs (s # ss)"
  have head: "\<forall>t \<in> set ss. disjoint_subst s t"
  proof
    fix t assume "t \<in> set ss"
    then obtain j where j: "j < length ss" "ss ! j = t" by (auto simp: in_set_conv_nth)
    have "disjoint_subst ((s # ss) ! 0) ((s # ss) ! Suc j)"
      using L j unfolding disjoint_substs_def by fastforce
    thus "disjoint_subst s t" using j by simp
  qed
  moreover have "disjoint_substs ss"
    unfolding disjoint_substs_def
  proof (intro allI impI)
    fix i j assume "i < length ss \<and> j < length ss \<and> i \<noteq> j"
    then have "disjoint_subst ((s # ss) ! Suc i) ((s # ss) ! Suc j)"
      using L unfolding disjoint_substs_def by fastforce
    thus "disjoint_subst (ss ! i) (ss ! j)" by simp
  qed
  ultimately show "(\<forall>t \<in> set ss. disjoint_subst s t) \<and> disjoint_substs ss" ..
next
  assume R: "(\<forall>t \<in> set ss. disjoint_subst s t) \<and> disjoint_substs ss"
  show "disjoint_substs (s # ss)"
    unfolding disjoint_substs_def
  proof (intro allI impI)
    fix i j assume ij: "i < length (s # ss) \<and> j < length (s # ss) \<and> i \<noteq> j"
    show "disjoint_subst ((s # ss) ! i) ((s # ss) ! j)"
    proof (cases i; cases j)
      fix j' assume "i = 0" "j = Suc j'"
      then show ?thesis using R ij by (auto simp: disjoint_subst_sym)
    next
      fix i' assume "i = Suc i'" "j = 0"
      then show ?thesis using R ij by (auto simp: disjoint_subst_sym)
    next
      fix i' j' assume "i = Suc i'" "j = Suc j'"
      then show ?thesis using R ij unfolding disjoint_substs_def by auto
    next
      assume "i = 0" "j = 0" then show ?thesis using ij by simp
    qed
  qed
qed

(* Generalized invariant for the one-pass checker: starting from an accumulator
   set of keys acc, the check succeeds exactly when acc is disjoint from every
   element's domain and the elements are pairwise domain-disjoint. *)
lemma disjoint_acc_None_iff:
  "disjoint_acc acc ss \<noteq> None \<longleftrightarrow>
     (\<forall>s \<in> set ss. fmdom s |\<inter>| acc = {||}) \<and> disjoint_substs ss"
proof (induction ss arbitrary: acc)
  case Nil
  show ?case by (simp add: disjoint_substs_def)
next
  case (Cons s ss)
  show ?case
  proof (cases "fmdom s |\<inter>| acc = {||}")
    case overlap: True
    have step: "disjoint_acc acc (s # ss) = disjoint_acc (acc |\<union>| fmdom s) ss"
      using overlap by simp
    show ?thesis
    proof
      assume "disjoint_acc acc (s # ss) \<noteq> None"
      then have rec: "disjoint_acc (acc |\<union>| fmdom s) ss \<noteq> None" using step by simp
      from Cons.IH[of "acc |\<union>| fmdom s"] rec
      have accs_rest: "\<forall>t \<in> set ss. fmdom t |\<inter>| (acc |\<union>| fmdom s) = {||}"
        and pair_rest: "disjoint_substs ss" by auto
      \<comment> \<open>acc disjoint from every element of s#ss.\<close>
      have acc_all: "\<forall>t \<in> set (s # ss). fmdom t |\<inter>| acc = {||}"
        using accs_rest overlap by auto
      \<comment> \<open>s disjoint from every tail element (the accumulator carried fmdom s).\<close>
      have head: "\<forall>t \<in> set ss. disjoint_subst s t"
        using accs_rest unfolding disjoint_subst_def
        by (metis disjoint_subst_def disjoint_subst_sym inf_sup_distrib1 sup_eq_bot_iff)
      have "disjoint_substs (s # ss)"
        using head pair_rest disjoint_substs_Cons by blast
      with acc_all show
        "(\<forall>t \<in> set (s # ss). fmdom t |\<inter>| acc = {||}) \<and> disjoint_substs (s # ss)" by blast
    next
      assume rhs: "(\<forall>t \<in> set (s # ss). fmdom t |\<inter>| acc = {||}) \<and> disjoint_substs (s # ss)"
      have acc_all: "\<forall>t \<in> set (s # ss). fmdom t |\<inter>| acc = {||}" using rhs by blast
      have head: "\<forall>t \<in> set ss. disjoint_subst s t"
        using rhs disjoint_substs_Cons by blast
      have pair_rest: "disjoint_substs ss"
        using rhs disjoint_substs_Cons by blast
      \<comment> \<open>Establish the IH premise for acc |\<union>| fmdom s on the tail.\<close>
      have accs_rest: "\<forall>t \<in> set ss. fmdom t |\<inter>| (acc |\<union>| fmdom s) = {||}"
      proof
        fix t assume t_in: "t \<in> set ss"
        have "fmdom t |\<inter>| acc = {||}" using acc_all t_in by simp
        moreover have "fmdom t |\<inter>| fmdom s = {||}"
          using head t_in unfolding disjoint_subst_def by auto
        ultimately show "fmdom t |\<inter>| (acc |\<union>| fmdom s) = {||}"
          by (simp add: inf_sup_distrib1)
      qed
      from Cons.IH[of "acc |\<union>| fmdom s"] accs_rest pair_rest
      have "disjoint_acc (acc |\<union>| fmdom s) ss \<noteq> None" by blast
      thus "disjoint_acc acc (s # ss) \<noteq> None" using step by simp
    qed
  next
    case False
    \<comment> \<open>Head-check fails: the accumulator already overlaps s's domain.\<close>
    have "disjoint_acc acc (s # ss) = None" using False by auto
    moreover have "\<not> (fmdom s |\<inter>| acc = {||})" using False by simp
    ultimately show ?thesis by auto
  qed
qed

(* disjoint_substs is defined by a quantifier over index pairs (not executable).
   The one-pass disjoint_acc computes the same predicate; this is registered as its
   code equation so merge_all_substs is executable. *)
lemma disjoint_substs_code [code]:
  "disjoint_substs ss = disjoint_substs_exec ss"
  unfolding disjoint_substs_exec_def
  using disjoint_acc_None_iff[of "{||}" ss]
  by auto


(* ========================================================================== *)
(* The rest of this file exists to prove that merge_all_substs is equivalent
   to an error-propagating fold of merge_substs over the list of substitutions.
   The main results below are theorems merge_all_substs_eq_Inr_iff and
   merge_all_substs_eq_fold; everything else is helpers. *)
(* ========================================================================== *)

(* ========================================================================== *)
(* Bridge lemmas: executable list functions vs the spec sets                  *)
(*                                                                            *)
(* merge_all_substs runs subst_dom_list / subst_dep_list (lists), but the     *)
(* closure theory (MergeSubstsHelpers.thy) is stated over the sets fmdom u and *)
(* subst_deps u T. These lemmas connect the two.                              *)
(* ========================================================================== *)

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

(* ========================================================================== *)
(* Bridge to the spec acyclicity predicate                                    *)
(*                                                                            *)
(* The graph-layer dep_rel of merge_all_substs's sorter inputs is exactly the *)
(* CONVERSE of subst_dep_rel u: the sorter orients edges dependent -> depend- *)
(* ency (getName x, getName y with y in getDeps x), whereas subst_dep_rel is  *)
(* oriented dependency -> dependent (T', T with T' in u T) so that wf recurses *)
(* the resolution direction. Acyclicity is converse-invariant, so the two     *)
(* acyclicity notions coincide.                                               *)
(* ========================================================================== *)

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

(* ========================================================================== *)
(* Layer 3a: properties of the resolution order                               *)
(*                                                                            *)
(* On the no-cycle branch (every SCC a singleton, no self-loop), order =      *)
(* concat sccs is a repetition-free enumeration of the domain in which every  *)
(* dependency strictly precedes its dependent. These are the only facts about *)
(* the SCC sort that the fold invariant (layer 3b) consumes.                  *)
(* ========================================================================== *)

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

(* ========================================================================== *)
(* Layer 3b: the fold invariant                                               *)
(*                                                                            *)
(* build_closure u order folds the per-variable equations of u into an        *)
(* accumulator in dependency order. We show that, whenever order is a         *)
(* repetition-free enumeration of fmdom u in which every dependency strictly  *)
(* precedes its dependent, build_closure u order is the idempotent closure of *)
(* u (is_subst_closure u (build_closure u order)).                            *)
(* ========================================================================== *)

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


(* ========================================================================== *)
(* Success characterization of merge_all_substs                               *)
(*                                                                            *)
(* merge_all_substs ss returns Inr sigma exactly when the inputs are          *)
(* consistent, their union's dependency relation is acyclic, and sigma is the *)
(* (unique) idempotent closure of that union. The list analogue of            *)
(* merge_substs_eq_Inr_iff (MergeSubsts.thy), stated over subst_list_union.   *)
(* ========================================================================== *)

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

(* The success characterization of merge_all_substs:
    - If merge_all_substs succeeds, returning \<sigma>, then the input substs are disjoint, their
      union is acyclic, and the idempotent closure of their union is \<sigma>.
    - Conversely, if the input substs are disjoint, and their union is acyclic, then
      merge_all_substs succeeds, and it returns the idempotent closure of the union
      (which exists and is unique by subst_closure_exists_unique).

   Contrapositively, merge_all_substs FAILS if and only if either of its error conditions
   is present: the input substs are not disjoint (multiple definition error), or there is
   a cycle.

   (Note: technically speaking, we don't prove that the "correct" error code is returned
   in each error case, but that is clear by inspection of the definition of merge_all_substs,
   and in any case is not crucial for soundness.)
*)
theorem merge_all_substs_eq_Inr_iff:
  "merge_all_substs ss = Inr \<sigma> \<longleftrightarrow>
     disjoint_substs ss
     \<and> acyclic_subst_deps (subst_list_union ss)
     \<and> is_subst_closure (subst_list_union ss) \<sigma>"
proof -
  define u where "u = subst_list_union ss"
  show ?thesis
  proof (cases "disjoint_substs ss")
    case False
    then show ?thesis
      unfolding merge_all_substs_def u_def[symmetric] by simp
  next
    case cons: True
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
        \<comment> \<open>Cycle detected: Inl LinkCycle on the left; not acyclic on the right.\<close>
        have lhs: "merge_all_substs ss = Inl LinkCycle"
          unfolding merge_all_substs_def u_def[symmetric] using cons Inr guards by simp
        have "\<not> acyclic_subst_deps u"
          using guards merge_all_guards_iff_acyclic[OF Inr] by blast
        then show ?thesis using lhs unfolding u_def by simp
      next
        case guards: False
        have sing: "\<forall>c \<in> set sccs. length c = 1"
          using guards analyze_dependencies_generic_non_empty[OF Inr]
          by (metis One_nat_def length_0_conv less_one nat_neq_iff)
        have noself: "\<forall>T \<in> set (subst_dom_list u). T \<notin> set (subst_dep_list u T)"
          using guards by blast
        have lhs: "merge_all_substs ss = Inr (build_closure u (concat sccs))"
          unfolding merge_all_substs_def u_def[symmetric] using cons Inr guards by simp
        have acyc: "acyclic_subst_deps u"
          using guards merge_all_guards_iff_acyclic[OF Inr] by blast
        have clos: "is_subst_closure u (build_closure u (concat sccs))"
          using merge_all_substs_Inr_is_closure[OF Inr sing noself] .
        show ?thesis
        proof
          assume "merge_all_substs ss = Inr \<sigma>"
          then have "\<sigma> = build_closure u (concat sccs)" using lhs by simp
          then show "disjoint_substs ss \<and> acyclic_subst_deps (subst_list_union ss)
                     \<and> is_subst_closure (subst_list_union ss) \<sigma>"
            using cons acyc clos unfolding u_def by simp
        next
          assume "disjoint_substs ss \<and> acyclic_subst_deps (subst_list_union ss)
                  \<and> is_subst_closure (subst_list_union ss) \<sigma>"
          then have "is_subst_closure u \<sigma>" unfolding u_def by simp
          then have "\<sigma> = build_closure u (concat sccs)"
            using clos subst_closure_unique[OF acyc] by blast
          then show "merge_all_substs ss = Inr \<sigma>" using lhs by simp
        qed
      qed
    qed
  qed
qed

(* ========================================================================== *)
(* Equivalence to the binary error-propagating fold                           *)
(*                                                                            *)
(* merge_all_substs is the executable batch linker; foldl_E merge_substs       *)
(* fmempty is the declarative reference - fold the binary merge_substs over    *)
(* the list, short-circuiting on the first Inl. We prove the two AGREE ON      *)
(* SUCCESS: merge_all_substs ss = Inr sigma iff the fold = Inr sigma. By       *)
(* contraposition this also says one fails (returns some Inl) iff the other    *)
(* does. We deliberately do NOT prove the two report the *same* LinkError:     *)
(* which diagnostic is produced is a UX matter for testing, not a soundness    *)
(* property. What is verified is exactly what matters - the batch algorithm    *)
(* computes the correct result when it succeeds, and succeeds exactly when it  *)
(* should.                                                                     *)
(* ========================================================================== *)

(* The error-propagating left fold: thread the accumulator through the
   (LinkError, _) sum monad, returning the first Inl. *)
fun foldl_E :: "('b \<Rightarrow> 'a \<Rightarrow> ('e, 'b) sum) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> ('e, 'b) sum" where
  "foldl_E f z [] = Inr z"
| "foldl_E f z (x # xs) = (case f z x of Inl e \<Rightarrow> Inl e | Inr z' \<Rightarrow> foldl_E f z' xs)"

(* subst_list_union of a cons is the head added onto the union of the tail. *)
lemma subst_list_union_Cons:
  "subst_list_union (s # ss) = s ++\<^sub>f subst_list_union ss"
  unfolding subst_list_union_def by simp

(* Folding from acc over a snoc list = fold over the front, then merge the last
   element onto the result (structural; holds for any error-propagating fold). *)
lemma foldl_E_snoc:
  "foldl_E f z (xs @ [s]) =
     (case foldl_E f z xs of Inl e \<Rightarrow> Inl e | Inr acc \<Rightarrow> f acc s)"
  by (induct xs arbitrary: z) (auto split: sum.splits)

(* subst_list_union of a snoc, as a finite map, equals the front union with the
   last element added on the right (the foldr base s is pulled out to the top by
   right-bias-respecting reassociation). Both biasings agree under consistency, but
   we only need the plain finite-map identity here. *)
lemma subst_list_union_snoc:
  "subst_list_union (xs @ [s]) = subst_list_union xs ++\<^sub>f s"
proof (induct xs)
  case Nil
  show ?case by (simp add: subst_list_union_def)
next
  case (Cons x xs)
  have "subst_list_union ((x # xs) @ [s]) = x ++\<^sub>f subst_list_union (xs @ [s])"
    by (simp add: subst_list_union_Cons)
  also have "\<dots> = x ++\<^sub>f (subst_list_union xs ++\<^sub>f s)"
    using Cons by simp
  also have "\<dots> = (x ++\<^sub>f subst_list_union xs) ++\<^sub>f s"
    by simp
  also have "\<dots> = subst_list_union (x # xs) ++\<^sub>f s"
    by (simp add: subst_list_union_Cons)
  finally show ?case .
qed

(* One direction of reversal invariance: disjoint_substs is preserved by rev.
   The index map i \<mapsto> length - Suc i is a bijection on the valid indices, and the
   pairwise condition is symmetric, so each rev-pair is a hypothesis-pair. *)
lemma disjoint_substs_rev_imp:
  assumes "disjoint_substs ss"
  shows "disjoint_substs (rev ss)"
  unfolding disjoint_substs_def
proof (intro allI impI)
  fix i j assume ij: "i < length (rev ss) \<and> j < length (rev ss) \<and> i \<noteq> j"
  then have i: "i < length ss" and j: "j < length ss" by auto
  \<comment> \<open>The reversed lookups are forward lookups at the mirrored indices. \<close>
  have ri: "rev ss ! i = ss ! (length ss - Suc i)" using i by (simp add: rev_nth)
  have rj: "rev ss ! j = ss ! (length ss - Suc j)" using j by (simp add: rev_nth)
  \<comment> \<open>Mirrored indices are valid and distinct. \<close>
  have lt_i: "length ss - Suc i < length ss" using i by simp
  have lt_j: "length ss - Suc j < length ss" using j by simp
  have neq: "length ss - Suc i \<noteq> length ss - Suc j" using ij i j by auto
  have "disjoint_subst (ss ! (length ss - Suc i)) (ss ! (length ss - Suc j))"
    using assms lt_i lt_j neq unfolding disjoint_substs_def by blast
  thus "disjoint_subst (rev ss ! i) (rev ss ! j)" using ri rj by simp
qed

(* disjoint_substs is invariant under reversal (involution: rev (rev ss) = ss). *)
lemma disjoint_substs_rev:
  "disjoint_substs (rev ss) = disjoint_substs ss"
  using disjoint_substs_rev_imp[of ss] disjoint_substs_rev_imp[of "rev ss"] by auto

(* Snoc decomposition of disjoint_substs: a list with a last element is pairwise
   disjoint iff the front is and the last is disjoint from every front element.
   Derived from the Cons form by reversal (xs @ [s] = rev (s # rev xs)). *)
lemma disjoint_substs_snoc:
  "disjoint_substs (xs @ [s]) \<longleftrightarrow>
     disjoint_substs xs \<and> (\<forall>t \<in> set xs. disjoint_subst t s)"
proof -
  have "disjoint_substs (xs @ [s]) = disjoint_substs (s # rev xs)"
    using disjoint_substs_rev by force
  also have "\<dots> = ((\<forall>t \<in> set (rev xs). disjoint_subst s t) \<and> disjoint_substs (rev xs))"
    by (rule disjoint_substs_Cons)
  also have "\<dots> = (disjoint_substs xs \<and> (\<forall>t \<in> set xs. disjoint_subst t s))"
    by (auto simp: disjoint_substs_rev disjoint_subst_sym)
  finally show ?thesis .
qed

(* Each element's domain is contained in the union's domain. *)
lemma fmdom_subset_subst_list_union:
  assumes "t \<in> set xs"
  shows "fmdom t |\<subseteq>| fmdom (subst_list_union xs)"
  using assms
proof (induct xs)
  case (Cons x xs)
  from Cons.prems show ?case
    using Cons.hyps subst_list_union_Cons by auto
qed simp

(* Fold soundness: if folding merge_substs from fmempty over ss succeeds with
   sigma, then the inputs were pairwise domain-disjoint, the union of ss is acyclic,
   and sigma is its idempotent closure. Proved by snoc induction: the last merge step
   hands us exactly the domain-disjointness the left-absorb and the acyclicity
   transfer need (acc, the closure of the front union, has the front union's domain,
   disjoint from s), so the front union's closure absorbs into the full union.
   (Acyclicity of the front union is carried in the conclusion - it cannot be
   recovered from the closure alone, since a cyclic union may still admit closures,
   just not a unique one.) *)
lemma foldl_E_merge_substs_sound:
  assumes "foldl_E merge_substs fmempty ss = Inr \<sigma>"
  shows "disjoint_substs ss
         \<and> acyclic_subst_deps (subst_list_union ss)
         \<and> is_subst_closure (subst_list_union ss) \<sigma>"
  using assms
proof (induct ss arbitrary: \<sigma> rule: rev_induct)
  case Nil
  then have "\<sigma> = fmempty" by simp
  then show ?case
    by (simp add: subst_list_union_def is_subst_closure_self disjoint_substs_def
        idempotent_subst_def idempotent_subst_acyclic)
next
  case (snoc s xs)
  have prem: "(case foldl_E merge_substs fmempty xs of
                 Inl e \<Rightarrow> Inl e | Inr acc \<Rightarrow> merge_substs acc s) = Inr \<sigma>"
    using snoc.prems by (simp add: foldl_E_snoc)
  then obtain acc where fxs: "foldl_E merge_substs fmempty xs = Inr acc"
    and last: "merge_substs acc s = Inr \<sigma>"
    by (auto split: sum.splits)
  have ih: "disjoint_substs xs
            \<and> acyclic_subst_deps (subst_list_union xs)
            \<and> is_subst_closure (subst_list_union xs) acc"
    using snoc.hyps fxs by simp
  have disj_front_substs: "disjoint_substs xs" using ih by simp
  have acyc_front: "acyclic_subst_deps (subst_list_union xs)" using ih by simp
  have cl_acc: "is_subst_closure (subst_list_union xs) acc" using ih by simp
  have last': "disjoint_subst acc s \<and> acyclic_subst_deps (acc ++\<^sub>f s)
               \<and> is_subst_closure (acc ++\<^sub>f s) \<sigma>"
    using last merge_substs_eq_Inr_iff by simp
  have disj_accs: "disjoint_subst acc s" using last' by simp
  have acyc_accs: "acyclic_subst_deps (acc ++\<^sub>f s)" using last' by simp
  \<comment> \<open>acc has the front union's domain (it is its closure), so the disjointness of acc
     and s is disjointness of the front union and s - the form the helpers want.\<close>
  have dom_acc: "fmdom acc = fmdom (subst_list_union xs)"
    using cl_acc unfolding is_subst_closure_def by simp
  have disj_front: "fmdom (subst_list_union xs) |\<inter>| fmdom s = {||}"
    using disj_accs dom_acc unfolding disjoint_subst_def by simp
  \<comment> \<open>Pairwise disjointness of the whole list: the front is disjoint (IH) and s is
     disjoint from each front element (its domain is in the front union's domain). \<close>
  have heads: "\<forall>t \<in> set xs. disjoint_subst t s"
  proof
    fix t assume "t \<in> set xs"
    then have "fmdom t |\<inter>| fmdom s |\<subseteq>| fmdom (subst_list_union xs) |\<inter>| fmdom s"
      using fmdom_subset_subst_list_union by auto
    then show "disjoint_subst t s"
      using disj_front unfolding disjoint_subst_def by auto
  qed
  have disj_full: "disjoint_substs (xs @ [s])"
    using disj_front_substs heads disjoint_substs_snoc by blast
  \<comment> \<open>Acyclicity and closure of the full union, via the front closure acc.\<close>
  have acyc_full: "acyclic_subst_deps (subst_list_union xs ++\<^sub>f s)"
    using acyclic_subst_deps_transfer[OF acyc_front disj_front cl_acc acyc_accs] .
  have clos_full: "is_subst_closure (subst_list_union xs ++\<^sub>f s) \<sigma>"
    using is_subst_closure_absorb[OF acyc_front disj_front cl_acc] last' by simp
  show ?case using disj_full acyc_full clos_full by (simp add: subst_list_union_snoc)
qed

(* A substitution disjoint from every element of a list is disjoint from their
   union (the union's domain is the union of the element domains). *)
lemma disjoint_subst_list_union:
  assumes "\<forall>t \<in> set xs. disjoint_subst s t"
  shows "disjoint_subst s (subst_list_union xs)"
  using assms
proof (induct xs)
  case Nil
  show ?case by (simp add: subst_list_union_def)
next
  case (Cons x xs)
  have x: "fmdom s |\<inter>| fmdom x = {||}"
    using Cons.prems unfolding disjoint_subst_def by simp
  have rest: "fmdom s |\<inter>| fmdom (subst_list_union xs) = {||}"
    using Cons unfolding disjoint_subst_def by simp
  have "fmdom s |\<inter>| fmdom (x ++\<^sub>f subst_list_union xs) = {||}"
    using x rest by (simp add: finter_funion_distrib)
  then show ?case
    unfolding subst_list_union_Cons disjoint_subst_def .
qed

(* Fold completeness: if the inputs are pairwise disjoint and their union is
   acyclic, the fold succeeds. Snoc induction: the front is disjoint (sublist) and
   its union acyclic (sub-union, via acyclic_subst_deps_left), so by IH the front
   fold yields acc = closure(front union); then the last merge succeeds because
   acc is disjoint from s (front union disjoint from s) and acc ++f s is acyclic (the
   converse acyclicity transfer from the full union's acyclicity). *)
lemma foldl_E_merge_substs_complete:
  assumes "disjoint_substs ss"
      and "acyclic_subst_deps (subst_list_union ss)"
  shows "\<exists>\<sigma>. foldl_E merge_substs fmempty ss = Inr \<sigma>"
  using assms
proof (induct ss rule: rev_induct)
  case Nil
  show ?case by simp
next
  case (snoc s xs)
  have disj: "disjoint_substs xs" and heads: "\<forall>t \<in> set xs. disjoint_subst t s"
    using snoc.prems(1) disjoint_substs_snoc by blast+
  \<comment> \<open>Front union is acyclic: it is a sub-union of the full (acyclic) union. \<close>
  have heads': "\<forall>t \<in> set xs. disjoint_subst s t"
    using heads disjoint_subst_sym by blast
  have disj_front_s: "fmdom (subst_list_union xs) |\<inter>| fmdom s = {||}"
    using disjoint_subst_list_union[OF heads']
    unfolding disjoint_subst_def by (simp add: inf_commute)
  have acyc_full: "acyclic_subst_deps (subst_list_union xs ++\<^sub>f s)"
    using snoc.prems(2) by (simp add: subst_list_union_snoc)
  have acyc_front: "acyclic_subst_deps (subst_list_union xs)"
    using acyclic_subst_deps_left[OF disj_front_s acyc_full] .
  \<comment> \<open>IH: the front fold succeeds; its result is the front union's closure. \<close>
  obtain acc where fxs: "foldl_E merge_substs fmempty xs = Inr acc"
    using snoc.hyps[OF disj acyc_front] by blast
  have cl_acc: "is_subst_closure (subst_list_union xs) acc"
    using foldl_E_merge_substs_sound[OF fxs] by simp
  have dom_acc: "fmdom acc = fmdom (subst_list_union xs)"
    using cl_acc unfolding is_subst_closure_def by simp
  \<comment> \<open>The last merge succeeds: acc disjoint from s, and acc ++f s acyclic (converse
     transfer of the full union's acyclicity). \<close>
  have disj_acc_s: "disjoint_subst acc s"
    using disj_front_s dom_acc unfolding disjoint_subst_def by simp
  have acyc_acc_s: "acyclic_subst_deps (acc ++\<^sub>f s)"
    using acyclic_subst_deps_transfer_converse[OF disj_front_s cl_acc acyc_full] .
  obtain r where "is_subst_closure (acc ++\<^sub>f s) r"
    using acyc_acc_s subst_closure_exists_unique by blast
  then have "merge_substs acc s = Inr r"
    using disj_acc_s acyc_acc_s merge_substs_eq_Inr_iff by simp
  then show ?case using fxs by (simp add: foldl_E_snoc)
qed

(* ========================================================================== *)
(* The headline equivalence (success-agreement)                               *)
(*                                                                            *)
(* merge_all_substs and the binary error-propagating fold agree on success:   *)
(* one returns Inr sigma iff the other does (the SAME sigma). By contraposition *)
(* one fails iff the other fails. We do NOT claim the same LinkError on        *)
(* failure - which diagnostic is produced is a UX matter, not a soundness one. *)
(* ========================================================================== *)
theorem merge_all_substs_eq_fold:
  "merge_all_substs ss = Inr \<sigma> \<longleftrightarrow> foldl_E merge_substs fmempty ss = Inr \<sigma>"
proof
  assume "merge_all_substs ss = Inr \<sigma>"
  then have disj: "disjoint_substs ss"
    and acyc: "acyclic_subst_deps (subst_list_union ss)"
    and clos: "is_subst_closure (subst_list_union ss) \<sigma>"
    using merge_all_substs_eq_Inr_iff by auto
  \<comment> \<open>The fold succeeds (completeness); its result is the same closure (soundness +
     uniqueness). \<close>
  obtain \<tau> where f: "foldl_E merge_substs fmempty ss = Inr \<tau>"
    using foldl_E_merge_substs_complete[OF disj acyc] by blast
  have "is_subst_closure (subst_list_union ss) \<tau>"
    using foldl_E_merge_substs_sound[OF f] by simp
  then have "\<tau> = \<sigma>" using clos subst_closure_unique[OF acyc] by blast
  then show "foldl_E merge_substs fmempty ss = Inr \<sigma>" using f by simp
next
  assume f: "foldl_E merge_substs fmempty ss = Inr \<sigma>"
  then have "disjoint_substs ss
             \<and> acyclic_subst_deps (subst_list_union ss)
             \<and> is_subst_closure (subst_list_union ss) \<sigma>"
    using foldl_E_merge_substs_sound by simp
  then show "merge_all_substs ss = Inr \<sigma>"
    using merge_all_substs_eq_Inr_iff by simp
qed

end
