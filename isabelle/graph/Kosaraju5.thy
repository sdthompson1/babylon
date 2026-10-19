theory Kosaraju5
  imports Kosaraju4
begin

(* Kosaraju's algorithm for finding strongly connected components: Part 5. *)

(*-----------------------------------------------------------------------------*)
(* Run collect_one_scc repeatedly until all SCCs collected *)
(*-----------------------------------------------------------------------------*)

(* Process vertices in reverse finish order, collecting SCCs *)
fun collect_all_sccs :: "('a::linorder) Graph \<Rightarrow> 'a fset \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "collect_all_sccs graph visited [] = []"
| "collect_all_sccs graph visited (v # rest) =
     (if v |\<in>| visited then
        collect_all_sccs graph visited rest
      else
        let (scc, new_visited) = collect_one_scc graph visited v
        in scc # collect_all_sccs graph new_visited rest)"

(*-----------------------------------------------------------------------------*)
(* Vertex Ordering predicate, and related properties *)
(*-----------------------------------------------------------------------------*)

(* Vertex list order property for collect_all_sccs: *)
(* For all edges (d,c) between different SCCs, where c is unvisited,
   there exists a vertex v_c in c's SCC that appears before all vertices
   in d's SCC in the vertex list.
*)
definition vertex_list_ordered :: "('a::linorder) Graph \<Rightarrow> 'a fset \<Rightarrow> 'a list \<Rightarrow> bool" where
  "vertex_list_ordered graph visited verts =
    (\<forall>c d. has_edge graph d c \<and> \<not>(in_same_scc graph d c) \<and> c |\<notin>| visited \<longrightarrow>
      (\<exists>v_c. List.member verts v_c \<and> has_vertex graph v_c \<and> in_same_scc graph v_c c \<and>
        (\<forall>v_d. List.member verts v_d \<and> has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
          index_of v_c verts < index_of v_d verts)))"

(* If a list is properly ordered and we add more vertices to the visited set,
   it remains properly ordered (because the constraint only applies to unvisited vertices) *)
lemma vertex_list_ordered_monotonic:
  assumes "vertex_list_ordered graph visited verts"
    and "visited |\<subseteq>| visited'"
  shows "vertex_list_ordered graph visited' verts"
  unfolding vertex_list_ordered_def
  using assms unfolding vertex_list_ordered_def
  by blast

(* If a list is properly ordered, and the head is visited, then the tail is properly ordered *)
lemma vertex_list_ordered_tail:
  assumes "vertex_list_ordered graph visited (start # rest)"
    and "start |\<in>| visited"
    and "\<forall>v w. v |\<in>| visited \<and> reachable graph v w \<longrightarrow> w |\<in>| visited"
  shows "vertex_list_ordered graph visited rest"
  unfolding vertex_list_ordered_def
proof (intro allI impI)
  fix d c
  assume hyp: "has_edge graph d c \<and> \<not> in_same_scc graph d c \<and> c |\<notin>| visited"
  obtain witness where witness_def: "List.member (start # rest) witness \<and>
     has_vertex graph witness \<and>
     in_same_scc graph witness c \<and>
     (\<forall>v_d. List.member (start # rest) v_d \<and> has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
            index_of witness (start # rest) < index_of v_d (start # rest))"
    using assms(1) hyp vertex_list_ordered_def by blast

  show "\<exists>v_c. List.member rest v_c \<and> has_vertex graph v_c \<and>
                 in_same_scc graph v_c c \<and>
                 (\<forall>v_d. List.member rest v_d \<and> has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
                        index_of v_c rest < index_of v_d rest)"
  proof (cases "witness = start")
    case True
    then have "start |\<notin>| visited"
      using assms(3) hyp in_same_scc.elims(2) witness_def by blast
    thus ?thesis
      by (simp add: assms(2))
  next
    case False
    then have "List.member rest witness"
      by (metis member_rec(1) witness_def)
    moreover have "(\<forall>v_d. List.member rest v_d \<and> has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
                        index_of witness rest < index_of v_d rest)"
      by (metis False bot_nat_0.extremum_strict index_of.simps(2) less_eq_Suc_le member_rec(1)
          not_less_eq_eq witness_def)
    ultimately show ?thesis
      using witness_def by auto
  qed
qed

(*-----------------------------------------------------------------------------*)
(* Preconditions for collect_all_sccs *)
(*-----------------------------------------------------------------------------*)

(* The invariant maintained by collect_all_sccs:
   1. The graph is valid
   2. All visited vertices are in the graph
   3. All vertices in the list are in the graph
   4. The visited set is closed under reachability
   5. Every graph vertex not in the list is visited
   6. The list is properly ordered *)
definition collect_all_sccs_pre :: "('a::linorder) Graph \<Rightarrow> 'a fset \<Rightarrow> 'a list \<Rightarrow> bool" where
  "collect_all_sccs_pre graph visited verts \<longleftrightarrow>
    valid_graph graph \<and>
    (\<forall>w |\<in>| visited. has_vertex graph w) \<and>
    (\<forall>w. List.member verts w \<longrightarrow> has_vertex graph w) \<and>
    (\<forall>v w. v |\<in>| visited \<and> reachable graph v w \<longrightarrow> w |\<in>| visited) \<and>
    (\<forall>v. has_vertex graph v \<and> \<not>(List.member verts v) \<longrightarrow> v |\<in>| visited) \<and>
    vertex_list_ordered graph visited verts"

(* If start is unvisited and the visited set is closed under reachability,
   then no vertex in start's SCC is visited. *)
lemma same_scc_unvisited:
  assumes "\<forall>v w. v |\<in>| visited \<and> reachable graph v w \<longrightarrow> w |\<in>| visited"
    and "start |\<notin>| visited"
  shows "\<forall>w. has_vertex graph w \<and> in_same_scc graph w start \<longrightarrow> w |\<notin>| visited"
  using assms in_same_scc.simps by blast

(* If start is unvisited and at the head of an ordered vertex list, then all vertices
   reachable from start that are NOT in the same SCC as start are already visited.
   (Proof: follow the path from start; the first edge leaving start's SCC would lead
   to an unvisited SCC that must appear before start in the list, which is impossible
   since start is at the head.) *)
lemma downstream_sccs_visited:
  assumes valid: "valid_graph graph"
    and closed: "\<forall>v w. v |\<in>| visited \<and> reachable graph v w \<longrightarrow> w |\<in>| visited"
    and ordered: "vertex_list_ordered graph visited (start # rest)"
  shows "\<forall>w. has_vertex graph w \<and> reachable graph start w \<and> \<not>(in_same_scc graph w start) \<longrightarrow>
             w |\<in>| visited"
proof -
  have "reachable graph v w \<Longrightarrow> v = start \<Longrightarrow> in_same_scc graph w start \<or> w |\<in>| visited" for v w
  proof (induction rule: reachable.induct)
    case (reachable_refl v)
    then show ?case using in_same_scc_refl by blast
  next
    case (reachable_step v w u)
    then have start_w: "reachable graph start w" and edge: "has_edge graph w u"
      and IH: "in_same_scc graph w start \<or> w |\<in>| visited"
      by blast+
    have start_vertex: "has_vertex graph start"
      using reachable_implies_vertices(1)[OF valid start_w] .
    have w_vertex: "has_vertex graph w"
      using reachable_implies_vertices(2)[OF valid start_w] .
    show ?case
    proof (cases "w |\<in>| visited")
      case True
      have "reachable graph w u"
        using edge w_vertex reachable.reachable_refl reachable.reachable_step by blast
      then show ?thesis using True closed by blast
    next
      case False
      with IH have w_scc: "in_same_scc graph w start" by blast
      show ?thesis
      proof (rule ccontr)
        assume "\<not> (in_same_scc graph u start \<or> u |\<in>| visited)"
        then have u_scc: "\<not> in_same_scc graph u start" and u_unvisited: "u |\<notin>| visited"
          by blast+
        have "\<not> in_same_scc graph w u"
          using w_scc u_scc in_same_scc_sym in_same_scc_trans by blast
        then obtain v_c where v_c_first:
          "\<forall>v_d. List.member (start # rest) v_d \<and> has_vertex graph v_d \<and> in_same_scc graph v_d w \<longrightarrow>
                  index_of v_c (start # rest) < index_of v_d (start # rest)"
          using ordered edge u_unvisited unfolding vertex_list_ordered_def by blast
        have "index_of v_c (start # rest) < index_of start (start # rest)"
          using v_c_first start_vertex w_scc in_same_scc_sym member_rec(1) by metis
        then show False by simp
      qed
    qed
  qed
  then show ?thesis by blast
qed

(* The preconditions are preserved when skipping a visited head *)
lemma collect_all_sccs_pre_skip:
  assumes "collect_all_sccs_pre graph visited (start # rest)"
    and "start |\<in>| visited"
  shows "collect_all_sccs_pre graph visited rest"
proof -
  have pre: "valid_graph graph" "\<forall>w |\<in>| visited. has_vertex graph w"
    "\<forall>w. List.member (start # rest) w \<longrightarrow> has_vertex graph w"
    "\<forall>v w. v |\<in>| visited \<and> reachable graph v w \<longrightarrow> w |\<in>| visited"
    "\<forall>v. has_vertex graph v \<and> \<not>(List.member (start # rest) v) \<longrightarrow> v |\<in>| visited"
    "vertex_list_ordered graph visited (start # rest)"
    using assms(1) unfolding collect_all_sccs_pre_def by blast+
  have "\<forall>w. List.member rest w \<longrightarrow> has_vertex graph w"
    using pre(3) by (simp add: member_rec(1))
  moreover have "\<forall>v. has_vertex graph v \<and> \<not>(List.member rest v) \<longrightarrow> v |\<in>| visited"
    using pre(5) assms(2) by (auto simp: member_rec(1))
  moreover have "vertex_list_ordered graph visited rest"
    using vertex_list_ordered_tail[OF pre(6) assms(2) pre(4)] .
  ultimately show ?thesis
    using pre(1,2,4) unfolding collect_all_sccs_pre_def by blast
qed

(* What happens when collect_all_sccs processes an unvisited head: the collected
   component is exactly start's SCC, the visited set grows by that SCC, and the
   preconditions hold for the rest of the list. *)
lemma collect_all_sccs_head:
  assumes pre: "collect_all_sccs_pre graph visited (start # rest)"
    and start_unvisited: "start |\<notin>| visited"
    and res: "collect_one_scc graph visited start = (scc, new_visited)"
  shows "set scc = {u. has_vertex graph u \<and> in_same_scc graph u start}"
    and "start \<in> set scc"
    and "distinct scc"
    and "new_visited = visited |\<union>| fset_of_list scc"
    and "\<forall>u \<in> set scc. u |\<notin>| visited"
    and "collect_all_sccs_pre graph new_visited rest"
proof -
  have valid: "valid_graph graph"
    and visited_vertices: "\<forall>w |\<in>| visited. has_vertex graph w"
    and verts_vertices: "\<forall>w. List.member (start # rest) w \<longrightarrow> has_vertex graph w"
    and closed: "\<forall>v w. v |\<in>| visited \<and> reachable graph v w \<longrightarrow> w |\<in>| visited"
    and covered: "\<forall>v. has_vertex graph v \<and> \<not>(List.member (start # rest) v) \<longrightarrow> v |\<in>| visited"
    and ordered: "vertex_list_ordered graph visited (start # rest)"
    using pre unfolding collect_all_sccs_pre_def by blast+

  have start_vertex: "has_vertex graph start"
    using verts_vertices by (simp add: member_rec(1))
  have scc_unvisited: "\<forall>w. has_vertex graph w \<and> in_same_scc graph w start \<longrightarrow> w |\<notin>| visited"
    using same_scc_unvisited[OF closed start_unvisited] .
  have downstream: "\<forall>w. has_vertex graph w \<and> reachable graph start w \<and>
                        \<not>(in_same_scc graph w start) \<longrightarrow> w |\<in>| visited"
    using downstream_sccs_visited[OF valid closed ordered] .

  (* The collected component is exactly start's SCC *)
  note correct = collect_one_scc_correct[OF valid start_vertex visited_vertices scc_unvisited
                   downstream res]

  show scc_set: "set scc = {u. has_vertex graph u \<and> in_same_scc graph u start}"
    by (rule correct(1))

  show "start \<in> set scc"
    unfolding scc_set using start_vertex in_same_scc_refl by blast

  show "distinct scc"
    by (rule correct(2))

  show new_eq: "new_visited = visited |\<union>| fset_of_list scc"
    by (rule correct(3))

  show "\<forall>u \<in> set scc. u |\<notin>| visited"
    unfolding scc_set using scc_unvisited by blast

  (* The preconditions hold for the rest of the list *)
  have new_iff: "w |\<in>| new_visited \<longleftrightarrow>
                   w |\<in>| visited \<or> (has_vertex graph w \<and> in_same_scc graph w start)" for w
    using new_eq scc_set by (simp add: fset_of_list_elem)

  have new_vertices: "\<forall>w |\<in>| new_visited. has_vertex graph w"
  proof (rule fBallI)
    fix w
    assume "w |\<in>| new_visited"
    then show "has_vertex graph w"
      using new_iff visited_vertices by (meson fbspec)
  qed

  have rest_vertices: "\<forall>w. List.member rest w \<longrightarrow> has_vertex graph w"
    using verts_vertices by (simp add: member_rec(1))

  have new_closed: "\<forall>v w. v |\<in>| new_visited \<and> reachable graph v w \<longrightarrow> w |\<in>| new_visited"
  proof (intro allI impI, elim conjE)
    fix v w
    assume v_new: "v |\<in>| new_visited" and vw: "reachable graph v w"
    show "w |\<in>| new_visited"
    proof (cases "v |\<in>| visited")
      case True
      then show ?thesis using vw closed new_iff by blast
    next
      case False
      then have "in_same_scc graph v start"
        using v_new new_iff by blast
      then have "reachable graph start w"
        using vw by (meson in_same_scc.simps reachable_trans)
      moreover have "has_vertex graph w"
        using reachable_implies_vertices(2)[OF valid vw] .
      ultimately show ?thesis
        using downstream new_iff by blast
    qed
  qed

  have new_covered: "\<forall>v. has_vertex graph v \<and> \<not>(List.member rest v) \<longrightarrow> v |\<in>| new_visited"
  proof (intro allI impI, elim conjE)
    fix v
    assume v_vertex: "has_vertex graph v" and v_rest: "\<not> List.member rest v"
    show "v |\<in>| new_visited"
    proof (cases "v = start")
      case True
      then show ?thesis using start_vertex in_same_scc_refl new_iff by blast
    next
      case False
      then have "\<not> List.member (start # rest) v"
        using v_rest by (simp add: member_rec(1))
      then show ?thesis using v_vertex covered new_iff by blast
    qed
  qed

  have new_ordered: "vertex_list_ordered graph new_visited rest"
  proof -
    have "visited |\<subseteq>| new_visited"
      by (simp add: new_eq funion_upper1)
    then have "vertex_list_ordered graph new_visited (start # rest)"
      by (rule vertex_list_ordered_monotonic[OF ordered])
    moreover have "start |\<in>| new_visited"
      using start_vertex in_same_scc_refl new_iff by blast
    ultimately show ?thesis
      using vertex_list_ordered_tail new_closed by blast
  qed

  show "collect_all_sccs_pre graph new_visited rest"
    unfolding collect_all_sccs_pre_def
    using valid new_vertices rest_vertices new_closed new_covered new_ordered by blast
qed

(* Induction rule for collect_all_sccs, under the preconditions.
   The Head case is given the facts established by collect_all_sccs_head. *)
lemma collect_all_sccs_induct [consumes 1, case_names Nil Skip Head]:
  assumes "collect_all_sccs_pre graph visited verts"
    and base: "\<And>visited. collect_all_sccs_pre graph visited [] \<Longrightarrow> P visited []"
    and skip_case: "\<And>visited start rest.
          collect_all_sccs_pre graph visited rest \<Longrightarrow>
          start |\<in>| visited \<Longrightarrow>
          collect_all_sccs graph visited (start # rest) = collect_all_sccs graph visited rest \<Longrightarrow>
          P visited rest \<Longrightarrow>
          P visited (start # rest)"
    and head_case: "\<And>visited start rest scc new_visited.
          collect_all_sccs_pre graph new_visited rest \<Longrightarrow>
          start |\<notin>| visited \<Longrightarrow>
          collect_all_sccs graph visited (start # rest) = scc # collect_all_sccs graph new_visited rest \<Longrightarrow>
          set scc = {u. has_vertex graph u \<and> in_same_scc graph u start} \<Longrightarrow>
          start \<in> set scc \<Longrightarrow>
          distinct scc \<Longrightarrow>
          new_visited = visited |\<union>| fset_of_list scc \<Longrightarrow>
          (\<forall>u \<in> set scc. u |\<notin>| visited) \<Longrightarrow>
          P new_visited rest \<Longrightarrow>
          P visited (start # rest)"
  shows "P visited verts"
  using assms(1)
proof (induction verts arbitrary: visited)
  case Nil
  then show ?case by (rule base)
next
  case (Cons start rest)
  show ?case
  proof (cases "start |\<in>| visited")
    case start_visited: True
    have pre_rest: "collect_all_sccs_pre graph visited rest"
      using collect_all_sccs_pre_skip[OF Cons.prems start_visited] .
    show ?thesis
      by (rule skip_case[OF pre_rest start_visited _ Cons.IH[OF pre_rest]])
         (simp add: start_visited)
  next
    case start_unvisited: False
    obtain scc new_visited where res: "collect_one_scc graph visited start = (scc, new_visited)"
      by (metis surj_pair)
    note props = collect_all_sccs_head[OF Cons.prems start_unvisited res]
    show ?thesis
      by (rule head_case[OF props(6) start_unvisited _ props(1-5) Cons.IH[OF props(6)]])
         (simp add: start_unvisited res)
  qed
qed

(*-----------------------------------------------------------------------------*)
(* Correctness Theorems for collect_all_sccs *)
(*-----------------------------------------------------------------------------*)

(* Vertices in SCCs collected by collect_all_sccs were not initially visited *)
lemma collect_all_sccs_vertices_were_unvisited:
  assumes "collect_all_sccs_pre graph visited verts"
    and "scc \<in> set (collect_all_sccs graph visited verts)"
    and "v \<in> set scc"
  shows "v |\<notin>| visited"
  using assms
proof (induction rule: collect_all_sccs_induct)
  case (Nil visited)
  then show ?case by simp
next
  case (Skip visited start rest)
  show ?case
    using Skip.prems unfolding Skip.hyps(3) by (rule Skip.IH)
next
  case (Head visited start rest scc' new_visited)
  have "scc = scc' \<or> scc \<in> set (collect_all_sccs graph new_visited rest)"
    using Head.prems(1) unfolding Head.hyps(3) by simp
  then show ?case
  proof
    assume "scc = scc'"
    then show ?thesis using Head.hyps(8) Head.prems(2) by blast
  next
    assume "scc \<in> set (collect_all_sccs graph new_visited rest)"
    then have "v |\<notin>| new_visited"
      using Head.IH Head.prems(2) by blast
    then show ?thesis
      using Head.hyps(7) by simp
  qed
qed

(* Each component returned by collect_all_sccs is a strongly connected component *)
theorem collect_all_sccs_are_sccs:
  assumes "collect_all_sccs_pre graph visited verts"
    and "scc \<in> set (collect_all_sccs graph visited verts)"
  shows "\<exists>v. v \<in> set scc \<and> (\<forall>u. u \<in> set scc \<longleftrightarrow> (has_vertex graph u \<and> in_same_scc graph u v))"
  using assms
proof (induction rule: collect_all_sccs_induct)
  case (Nil visited)
  then show ?case by simp
next
  case (Skip visited start rest)
  show ?case
    using Skip.prems unfolding Skip.hyps(3) by (rule Skip.IH)
next
  case (Head visited start rest scc' new_visited)
  have "scc = scc' \<or> scc \<in> set (collect_all_sccs graph new_visited rest)"
    using Head.prems unfolding Head.hyps(3) by simp
  then show ?case
  proof
    assume "scc = scc'"
    then have "start \<in> set scc \<and>
               (\<forall>u. u \<in> set scc \<longleftrightarrow> (has_vertex graph u \<and> in_same_scc graph u start))"
      using Head.hyps(4,5) by simp
    then show ?thesis by blast
  next
    assume "scc \<in> set (collect_all_sccs graph new_visited rest)"
    then show ?thesis by (rule Head.IH)
  qed
qed

(* All vertices in the graph that are not already visited appear in some SCC *)
theorem collect_all_sccs_vertices_in_graph:
  assumes "collect_all_sccs_pre graph visited verts"
    and "has_vertex graph v"
    and "v |\<notin>| visited"
  shows "\<exists>scc. scc \<in> set (collect_all_sccs graph visited verts) \<and> v \<in> set scc"
  using assms
proof (induction rule: collect_all_sccs_induct)
  case (Nil visited)
  (* Every graph vertex not in the (empty) list is visited *)
  then show ?case
    unfolding collect_all_sccs_pre_def by (meson member_rec(2))
next
  case (Skip visited start rest)
  show ?case
    unfolding Skip.hyps(3) using Skip.IH Skip.prems by blast
next
  case (Head visited start rest scc' new_visited)
  show ?case
  proof (cases "v |\<in>| new_visited")
    case v_new: True
    have "v \<in> set scc'"
      using Head.hyps(7) Head.prems(2) v_new by (auto simp: fset_of_list_elem)
    then show ?thesis
      unfolding Head.hyps(3) by auto
  next
    case v_not_new: False
    show ?thesis
      unfolding Head.hyps(3) using Head.IH[OF Head.prems(1) v_not_new] by auto
  qed
qed

(* The vertices in each SCC are distinct *)
theorem collect_all_sccs_distinct:
  assumes "collect_all_sccs_pre graph visited verts"
    and "scc \<in> set (collect_all_sccs graph visited verts)"
  shows "distinct scc"
  using assms
proof (induction rule: collect_all_sccs_induct)
  case (Nil visited)
  then show ?case by simp
next
  case (Skip visited start rest)
  show ?case
    using Skip.prems unfolding Skip.hyps(3) by (rule Skip.IH)
next
  case (Head visited start rest scc' new_visited)
  have "scc = scc' \<or> scc \<in> set (collect_all_sccs graph new_visited rest)"
    using Head.prems unfolding Head.hyps(3) by simp
  then show ?case
    using Head.hyps(6) Head.IH by blast
qed

(* There is only one copy of each SCC in the output *)
theorem collect_all_sccs_distinct_list:
  assumes "collect_all_sccs_pre graph visited verts"
  shows "distinct (map set (collect_all_sccs graph visited verts))"
  using assms
proof (induction rule: collect_all_sccs_induct)
  case (Nil visited)
  then show ?case by simp
next
  case (Skip visited start rest)
  show ?case
    unfolding Skip.hyps(3) by (rule Skip.IH)
next
  case (Head visited start rest scc' new_visited)
  (* scc' cannot appear again later: start is in scc' and in new_visited, but every
     vertex of a later SCC is outside new_visited *)
  have "set scc' \<notin> set (map set (collect_all_sccs graph new_visited rest))"
  proof
    assume "set scc' \<in> set (map set (collect_all_sccs graph new_visited rest))"
    then obtain scc where scc: "scc \<in> set (collect_all_sccs graph new_visited rest)"
      and "set scc = set scc'"
      by auto
    then have "start \<in> set scc"
      using Head.hyps(5) by simp
    then have "start |\<notin>| new_visited"
      using collect_all_sccs_vertices_were_unvisited[OF Head.hyps(1) scc] by blast
    moreover have "start |\<in>| new_visited"
      using Head.hyps(5,7) by (simp add: fset_of_list_elem)
    ultimately show False
      by simp
  qed
  then show ?case
    unfolding Head.hyps(3) using Head.IH by simp
qed

(* Definition of reverse topological ordering.
   If SCC at index i appears before SCC at index j (i < j) in the output list,
   then there's no edge from SCC_i to SCC_j. *)
definition sccs_reverse_topologically_ordered :: "('a::linorder) Graph \<Rightarrow> 'a list list \<Rightarrow> bool" where
  "sccs_reverse_topologically_ordered graph sccs \<equiv>
    (\<forall>i j. i < j \<and> j < length sccs \<longrightarrow>
           (\<forall>u v. u \<in> set (sccs ! i) \<and> v \<in> set (sccs ! j) \<longrightarrow>
                  \<not>has_edge graph u v))"

(* Adding an SCC at the front preserves reverse topological order,
   provided there are no edges from it to any later SCC *)
lemma sccs_reverse_topologically_ordered_Cons:
  assumes "\<forall>s \<in> set sccs. \<forall>u \<in> set scc. \<forall>v \<in> set s. \<not> has_edge graph u v"
    and "sccs_reverse_topologically_ordered graph sccs"
  shows "sccs_reverse_topologically_ordered graph (scc # sccs)"
  unfolding sccs_reverse_topologically_ordered_def
proof (intro allI impI)
  fix i j u v
  assume ij: "i < j \<and> j < length (scc # sccs)"
    and uv: "u \<in> set ((scc # sccs) ! i) \<and> v \<in> set ((scc # sccs) ! j)"
  obtain j' where j: "j = Suc j'"
    using ij by (cases j) auto
  show "\<not> has_edge graph u v"
  proof (cases i)
    case 0
    with uv j have "u \<in> set scc" "v \<in> set (sccs ! j')"
      by auto
    moreover have "sccs ! j' \<in> set sccs"
      using ij j by simp
    ultimately show ?thesis
      using assms(1) by blast
  next
    case (Suc i')
    with ij uv j have "i' < j'" "j' < length sccs" "u \<in> set (sccs ! i')" "v \<in> set (sccs ! j')"
      by auto
    then show ?thesis
      using assms(2) unfolding sccs_reverse_topologically_ordered_def by blast
  qed
qed

(* Theorem: collect_all_sccs produces SCCs in reverse topological order. *)
theorem collect_all_sccs_reverse_topologically_ordered:
  assumes "collect_all_sccs_pre graph visited verts"
  shows "sccs_reverse_topologically_ordered graph (collect_all_sccs graph visited verts)"
  using assms
proof (induction rule: collect_all_sccs_induct)
  case (Nil visited)
  then show ?case
    by (simp add: sccs_reverse_topologically_ordered_def)
next
  case (Skip visited start rest)
  show ?case
    unfolding Skip.hyps(3) by (rule Skip.IH)
next
  case (Head visited start rest scc' new_visited)
  (* No edges from scc' to later SCCs: scc' is inside new_visited, which is closed
     under reachability, while later SCCs lie outside new_visited *)
  have "\<forall>s \<in> set (collect_all_sccs graph new_visited rest). \<forall>u \<in> set scc'. \<forall>v \<in> set s.
          \<not> has_edge graph u v"
  proof (intro ballI)
    fix s u v
    assume s: "s \<in> set (collect_all_sccs graph new_visited rest)"
      and u: "u \<in> set scc'" and v: "v \<in> set s"
    have "v |\<notin>| new_visited"
      using collect_all_sccs_vertices_were_unvisited[OF Head.hyps(1) s v] .
    moreover have "u |\<in>| new_visited"
      using Head.hyps(7) u by (simp add: fset_of_list_elem)
    moreover have "\<forall>v w. v |\<in>| new_visited \<and> reachable graph v w \<longrightarrow> w |\<in>| new_visited"
      and "\<forall>w |\<in>| new_visited. has_vertex graph w"
      using Head.hyps(1) unfolding collect_all_sccs_pre_def by blast+
    ultimately show "\<not> has_edge graph u v"
      using reachable.reachable_refl reachable.reachable_step by metis
  qed
  then show ?case
    unfolding Head.hyps(3)
    by (rule sccs_reverse_topologically_ordered_Cons[OF _ Head.IH])
qed

end
