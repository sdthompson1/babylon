theory DependencyRel
  imports Dependency
begin

(* This file defines an abstract dependency relation and restates some of the
   results of Dependency.thy in terms of that relation. *)


(*-----------------------------------------------------------------------------*)
(* The abstract dependency relation                                            *)
(*-----------------------------------------------------------------------------*)

(* The name-level dependency relation underlying analyze_dependencies_generic:
   an edge (getName x, getName y) whenever item x depends on item y
   (getName y occurs in getDeps x). Oriented "dependent -> dependency", matching
   subst_dep_rel in the substitution-merge layer. *)
definition dep_rel :: "'a list \<Rightarrow> ('a \<Rightarrow> string) \<Rightarrow> ('a \<Rightarrow> string list) \<Rightarrow> (string \<times> string) set"
  where
  "dep_rel items getName getDeps =
     {(getName x, getName y) | x y. x \<in> set items \<and> y \<in> set items
                                  \<and> getName y \<in> set (getDeps x)}"


(*-----------------------------------------------------------------------------*)
(* dep_rel edges coincide with graph edges                                     *)
(*-----------------------------------------------------------------------------*)

(* On a successfully-analyzed input, a dep_rel edge is exactly a has_edge of the
   built dependency graph. (Forward needs distinct names so the fmap lookup hits
   the intended item; backward needs deps-exist so the dependency is itself an
   item name.) *)
lemma dep_rel_eq_has_edge:
  assumes "analyze_dependencies_generic items getName getDeps = Inr sccs"
    and "a \<in> set (map getName items)"
  shows "(a, b) \<in> dep_rel items getName getDeps
         \<longleftrightarrow> has_edge (build_dep_graph getName getDeps items) a b"
proof -
  have no_dup_errors: "check_duplicate_names getName items = None"
    using assms(1) by (cases "check_duplicate_names getName items") auto
  have names_distinct: "distinct (map getName items)"
    using no_dup_errors no_duplicate_errors_means_distinct by blast

  (* The graph maps a to getDeps of the (unique) item named a. *)
  from assms(2) obtain xa where xa_in: "xa \<in> set items" and xa_name: "getName xa = a"
    by auto
  have look_a: "fmlookup (build_dep_graph getName getDeps items) a = Some (getDeps xa)"
  proof -
    have pair_in: "(a, getDeps xa) \<in> set (map (\<lambda>i. (getName i, getDeps i)) items)"
      using xa_in xa_name by force
    have "map fst (map (\<lambda>i. (getName i, getDeps i)) items) = map getName items"
      by simp
    then have "distinct (map fst (map (\<lambda>i. (getName i, getDeps i)) items))"
      using names_distinct by argo
    then show ?thesis
      unfolding build_dep_graph.simps
      by (metis fmap_of_list.rep_eq map_of_eq_Some_iff pair_in)
  qed
  hence edge_iff: "has_edge (build_dep_graph getName getDeps items) a b
                   \<longleftrightarrow> b \<in> set (getDeps xa)"
    by (simp add: member_def)

  show ?thesis
  proof
    assume "(a, b) \<in> dep_rel items getName getDeps"
    then obtain x y where xy: "a = getName x" "b = getName y"
      "x \<in> set items" "y \<in> set items" "getName y \<in> set (getDeps x)"
      unfolding dep_rel_def by blast
    (* x and xa share the name a, so are equal (distinct names). *)
    have "x = xa" using xy(1,3) xa_in xa_name names_distinct
      by (metis distinct_map inj_on_eq_iff)
    then have "b \<in> set (getDeps xa)" using xy(2,5) by simp
    then show "has_edge (build_dep_graph getName getDeps items) a b"
      using edge_iff by simp
  next
    assume "has_edge (build_dep_graph getName getDeps items) a b"
    then have "b \<in> set (getDeps xa)" using edge_iff by simp
    moreover have "b \<in> set (map getName items)"
    proof -
      have deps_exist:
        "\<forall>item \<in> set items. \<forall>dep \<in> set (getDeps item).
            fmlookup (build_item_map getName items) dep \<noteq> None"
      proof -
        have "check_deps_exist getName getDeps items (build_item_map getName items) = None"
        proof (cases "check_deps_exist getName getDeps items (build_item_map getName items)")
          case None
          then show ?thesis by simp
        next
          case (Some err)
          then have "analyze_dependencies_generic items getName getDeps = Inl err"
            using no_dup_errors by simp
          then show ?thesis using assms(1) by simp
        qed
        then show ?thesis using check_deps_exist_None_means_all_exist by blast
      qed
      have "fmlookup (build_item_map getName items) b \<noteq> None"
        using deps_exist xa_in \<open>b \<in> set (getDeps xa)\<close> by blast
      then have "b \<in> fset (fmdom (build_item_map getName items))"
        by (meson fmdom_notD)
      then show ?thesis using build_item_map_dom by blast
    qed
    then obtain y where "y \<in> set items" "getName y = b" by auto
    ultimately show "(a, b) \<in> dep_rel items getName getDeps"
      unfolding dep_rel_def using xa_in xa_name by blast
  qed
qed


(*-----------------------------------------------------------------------------*)
(* reachable coincides with the reflexive-transitive closure of dep_rel        *)
(*-----------------------------------------------------------------------------*)

(* A non-trivial reachable path is a dep_rel transitive-closure step. *)
lemma reachable_imp_dep_rel_trancl:
  assumes "analyze_dependencies_generic items getName getDeps = Inr sccs"
    and "reachable (build_dep_graph getName getDeps items) a b"
    and "a \<noteq> b"
  shows "(a, b) \<in> (dep_rel items getName getDeps)\<^sup>+"
  using assms(2,3)
proof (induction rule: reachable.induct)
  case (reachable_refl v)
  then show ?case by simp
next
  case (reachable_step v w u)
  define graph where "graph = build_dep_graph getName getDeps items"
  have edge_wu_graph: "has_edge graph w u"
    using reachable_step graph_def by simp
  have w_vertex: "has_vertex graph w"
    using edge_wu_graph by (cases "fmlookup graph w") (auto intro: fmdomI)
  have w_name: "w \<in> set (map getName items)"
    using w_vertex graph_def build_dep_graph_dom has_vertex.simps by blast
  (* edge w -> u is a dep_rel edge *)
  have edge_wu: "(w, u) \<in> dep_rel items getName getDeps"
    using dep_rel_eq_has_edge[OF assms(1) w_name] edge_wu_graph graph_def by simp
  show ?case
  proof (cases "v = w")
    case True
    then show ?thesis using edge_wu by (simp add: r_into_trancl)
  next
    case False
    then have "(v, w) \<in> (dep_rel items getName getDeps)\<^sup>+"
      using reachable_step.IH by simp
    then show ?thesis using edge_wu by (rule trancl_into_trancl)
  qed
qed

(* Conversely, a dep_rel transitive-closure step is a reachable path. *)
lemma dep_rel_trancl_imp_reachable:
  assumes "analyze_dependencies_generic items getName getDeps = Inr sccs"
    and "(a, b) \<in> (dep_rel items getName getDeps)\<^sup>+"
  shows "reachable (build_dep_graph getName getDeps items) a b"
  using assms(2)
proof (induction rule: trancl.induct)
  case (r_into_trancl a b)
  then obtain x where "a = getName x" "x \<in> set items"
    unfolding dep_rel_def by blast
  then have a_name: "a \<in> set (map getName items)" by auto
  have "has_edge (build_dep_graph getName getDeps items) a b"
    using dep_rel_eq_has_edge[OF assms(1) a_name] r_into_trancl by simp
  moreover have "has_vertex (build_dep_graph getName getDeps items) a"
    using a_name build_dep_graph_dom has_vertex.simps by blast
  ultimately show ?case
    using reachable.reachable_refl reachable.reachable_step by blast
next
  case (trancl_into_trancl a b c)
  (* a reaches b (IH), and b -> c is an edge *)
  have step_bc: "(b, c) \<in> dep_rel items getName getDeps"
    using trancl_into_trancl by blast
  obtain x where "b = getName x" "x \<in> set items"
    using step_bc unfolding dep_rel_def by blast
  then have b_name: "b \<in> set (map getName items)" by auto
  have "has_edge (build_dep_graph getName getDeps items) b c"
    using dep_rel_eq_has_edge[OF assms(1) b_name] step_bc by simp
  then show ?case
    using trancl_into_trancl.IH reachable.reachable_step by blast
qed

(* in_same_scc is exactly mutual dep_rel-trancl-reachability, for distinct names. *)
lemma in_same_scc_iff_dep_rel_trancl:
  assumes "analyze_dependencies_generic items getName getDeps = Inr sccs"
    and "a \<noteq> b"
  shows "in_same_scc (build_dep_graph getName getDeps items) a b
         \<longleftrightarrow> (a, b) \<in> (dep_rel items getName getDeps)\<^sup>+
           \<and> (b, a) \<in> (dep_rel items getName getDeps)\<^sup>+"
  using assms(2)
  by (metis assms(1) dep_rel_trancl_imp_reachable in_same_scc.simps
      reachable_imp_dep_rel_trancl)


(*-----------------------------------------------------------------------------*)
(* The acyclicity characterization                                             *)
(*-----------------------------------------------------------------------------*)

(* The two executable cyclicity checks of analyze_dependencies_generic - "every
   SCC is a singleton" and "no item is its own dependency (no self-loop)" -
   together hold exactly when the underlying dependency relation is acyclic.
   This is the bridge between the verified SCC algorithm and the spec-level
   acyclic predicate (e.g. acyclic_subst_deps in the substitution-merge layer). *)
theorem analyze_dependencies_acyclic_iff:
  assumes result: "analyze_dependencies_generic items getName getDeps = Inr sccs"
  shows "( (\<forall>scc \<in> set sccs. length scc = 1)
            \<and> (\<forall>x \<in> set items. getName x \<notin> set (getDeps x)) )
         \<longleftrightarrow> acyclic (dep_rel items getName getDeps)"
proof
  define R where "R = dep_rel items getName getDeps"
  assume lhs: "(\<forall>scc \<in> set sccs. length scc = 1)
               \<and> (\<forall>x \<in> set items. getName x \<notin> set (getDeps x))"
  show "acyclic (dep_rel items getName getDeps)"
  proof (rule acyclicI, intro allI notI)
    fix z assume cyc: "(z, z) \<in> (dep_rel items getName getDeps)\<^sup>+"
    (* The cycle's first step: z -> w, and w reaches back to z. *)
    from cyc obtain w where zw: "(z, w) \<in> dep_rel items getName getDeps"
      and wz: "(w, z) \<in> (dep_rel items getName getDeps)\<^sup>*"
      by (meson tranclD)
    (* z is the source of a dep_rel edge, hence an item name. *)
    obtain x where x: "z = getName x" "x \<in> set items"
      using zw unfolding dep_rel_def by blast
    have z_name: "z \<in> set (map getName items)" using x by auto
    (* The self-loop guard rules out a single-edge cycle, so z \<noteq> w. *)
    have no_self: "(z, z) \<notin> dep_rel items getName getDeps"
    proof
      assume "(z, z) \<in> dep_rel items getName getDeps"
      then obtain x' y' where "z = getName x'" "z = getName y'"
        "x' \<in> set items" "getName y' \<in> set (getDeps x')"
        unfolding dep_rel_def by blast
      then show False using lhs by metis
    qed
    have "z \<noteq> w" using zw no_self by auto
    have wz_t: "(w, z) \<in> (dep_rel items getName getDeps)\<^sup>+"
      using wz \<open>z \<noteq> w\<close> by (metis rtranclD)
    have zw_t: "(z, w) \<in> (dep_rel items getName getDeps)\<^sup>+"
      using zw by (rule r_into_trancl)
    (* z and w are in the same SCC, but all SCCs are singletons - contradiction. *)
    have "in_same_scc (build_dep_graph getName getDeps items) z w"
      using in_same_scc_iff_dep_rel_trancl[OF result \<open>z \<noteq> w\<close>] zw_t wz_t by blast
    moreover obtain wx where "w = getName wx" "wx \<in> set items"
      using zw unfolding dep_rel_def by blast
    then have w_in: "wx \<in> set items" by simp
    have x_in: "x \<in> set items" using x by simp
    (* scc_complete: z, w sit in one returned SCC; singleton forces them equal. *)
    have "\<exists>scc \<in> set sccs. x \<in> set scc \<and> wx \<in> set scc"
      using analyze_dependencies_generic_scc_complete[OF result x_in w_in]
            \<open>w = getName wx\<close> x(1) calculation by simp
    then obtain scc where scc_in: "scc \<in> set sccs"
      and "x \<in> set scc" "wx \<in> set scc" by blast
    then have "length scc = 1" using lhs by simp
    then have "x = wx" using \<open>x \<in> set scc\<close> \<open>wx \<in> set scc\<close>
      by (simp add: in_set_conv_nth)
    then have "z = w" using x(1) \<open>w = getName wx\<close> by simp
    then show False using \<open>z \<noteq> w\<close> by simp
  qed
next
  assume acyc: "acyclic (dep_rel items getName getDeps)"
  show "(\<forall>scc \<in> set sccs. length scc = 1)
        \<and> (\<forall>x \<in> set items. getName x \<notin> set (getDeps x))"
  proof
    (* No self-loop: a self-dependency is a length-1 cycle. *)
    show "\<forall>x \<in> set items. getName x \<notin> set (getDeps x)"
    proof (intro ballI notI)
      fix x assume "x \<in> set items" "getName x \<in> set (getDeps x)"
      then have "(getName x, getName x) \<in> dep_rel items getName getDeps"
        unfolding dep_rel_def by blast
      then have "(getName x, getName x) \<in> (dep_rel items getName getDeps)\<^sup>+"
        by (rule r_into_trancl)
      then show False using acyc unfolding acyclic_def by blast
    qed
  next
    (* All singletons: a length>1 SCC has two distinct mutually-reachable items. *)
    show "\<forall>scc \<in> set sccs. length scc = 1"
    proof (intro ballI)
      fix scc assume scc_in: "scc \<in> set sccs"
      have scc_ne: "scc \<noteq> []"
        using analyze_dependencies_generic_non_empty[OF result] scc_in by blast
      show "length scc = 1"
      proof (rule ccontr)
        assume "length scc \<noteq> 1"
        moreover have "length scc \<noteq> 0" using scc_ne by simp
        ultimately have len2: "length scc \<ge> 2" by linarith
        obtain a b rest where scc_cons: "scc = a # b # rest"
        proof (cases scc)
          case Nil thus ?thesis using len2 by simp
        next
          case (Cons a' tl)
          show ?thesis
          proof (cases tl)
            case Nil thus ?thesis using len2 Cons by simp
          next
            case (Cons b' rest')
            thus ?thesis using \<open>scc = a' # tl\<close> that by simp
          qed
        qed
        have a_in: "a \<in> set scc" and b_in: "b \<in> set scc" using scc_cons by auto
        have ab_scc: "in_same_scc (build_dep_graph getName getDeps items) (getName a) (getName b)"
          using analyze_dependencies_generic_scc_sound[OF result scc_in a_in b_in] .
        (* The names within scc are distinct: concat sccs has the same multiset as
           items, whose names are distinct; scc is a contiguous part of concat sccs.
           So the two leading elements a, b differ in name. *)
        have dist_scc_names: "distinct (map getName scc)"
        proof -
          have dist_items: "distinct (map getName items)"
            using result no_duplicate_errors_means_distinct
            by (cases "check_duplicate_names getName items") auto
          have "mset (map getName (concat sccs)) = mset (map getName items)"
            using analyze_dependencies_generic_permutation[OF result] by (metis mset_map)
          then have dist_concat: "distinct (map getName (concat sccs))"
            using dist_items by (meson mset_eq_imp_distinct_iff)
          obtain pre post where "sccs = pre @ scc # post"
            using scc_in by (meson split_list)
          then have "concat sccs = concat pre @ scc @ concat post" by simp
          then have "map getName (concat sccs)
                     = map getName (concat pre) @ map getName scc @ map getName (concat post)"
            by simp
          then show ?thesis using dist_concat by simp
        qed
        have "getName a \<noteq> getName b" using dist_scc_names scc_cons by simp
        then have "(getName a, getName b) \<in> (dep_rel items getName getDeps)\<^sup>+"
          using in_same_scc_iff_dep_rel_trancl[OF result] ab_scc by blast
        moreover have "(getName b, getName a) \<in> (dep_rel items getName getDeps)\<^sup>+"
          using in_same_scc_iff_dep_rel_trancl[OF result \<open>getName a \<noteq> getName b\<close>]
                ab_scc by simp
        ultimately have "(getName a, getName a) \<in> (dep_rel items getName getDeps)\<^sup>+"
          by (rule trancl_trans)
        then show False using acyc unfolding acyclic_def by blast
      qed
    qed
  qed
qed

end
