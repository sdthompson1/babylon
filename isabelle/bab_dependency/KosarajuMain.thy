theory KosarajuMain
  imports Kosaraju5
begin

(* Kosaraju's algorithm for finding strongly connected components: Main entry point. *)

(*-----------------------------------------------------------------------------*)
(* Main Kosaraju Algorithm *)
(*-----------------------------------------------------------------------------*)

(* The complete Kosaraju algorithm:
   1. Run DFS on the original graph to compute finish order
   2. Run DFS on the transposed graph in finish order to collect SCCs *)
definition kosaraju :: "('a::linorder) Graph \<Rightarrow> 'a list list" where
  "kosaraju graph = (
     let finish_order = kosaraju_phase_1 graph;
         transposed = transpose_graph graph;
         sccs = collect_all_sccs transposed {||} finish_order
     in sccs)"

(*-----------------------------------------------------------------------------*)
(* Topological Ordering Definition *)
(*-----------------------------------------------------------------------------*)

(* Definition: A list of SCCs is in topological order if: whenever  SCC_i is before
   SCC_j in the list, there is no edge from j to i.
   (In other words, all edges flow left-to-right in the list, never right-to-left.)
*)
definition sccs_topologically_ordered :: "('a::linorder) Graph \<Rightarrow> 'a list list \<Rightarrow> bool" where
  "sccs_topologically_ordered graph sccs \<equiv>
    (\<forall>i j. i < j \<and> j < length sccs \<longrightarrow>
           (\<forall>u v. u \<in> set (sccs ! i) \<and> v \<in> set (sccs ! j) \<longrightarrow>
                  \<not>has_edge graph v u))"

(*-----------------------------------------------------------------------------*)
(* Helper Lemmas *)
(*-----------------------------------------------------------------------------*)

(* Reverse topological order on transposed graph = topological order on original graph *)
lemma transpose_reverse_topo_is_topo:
  assumes "valid_graph graph"
    and "sccs_reverse_topologically_ordered (transpose_graph graph) sccs"
  shows "sccs_topologically_ordered graph sccs"
  unfolding sccs_topologically_ordered_def sccs_reverse_topologically_ordered_def
proof (intro allI impI)
  fix i j u v
  assume indices: "i < j \<and> j < length sccs"
  assume uv: "u \<in> set (sccs ! i) \<and> v \<in> set (sccs ! j)"
  show "\<not>has_edge graph v u"
  proof -
    have u_in: "u \<in> set (sccs ! i)" and v_in: "v \<in> set (sccs ! j)" using uv by simp+

    (* By the assumption, no edge from u to v in the transposed graph *)
    have "\<not>has_edge (transpose_graph graph) u v"
      using assms(2) unfolding sccs_reverse_topologically_ordered_def
      using indices u_in v_in by blast

    (* By transpose_edge_correspondence, this means no edge from v to u in the original *)
    then show "\<not>has_edge graph v u"
      using assms(1) transpose_edge_correspondence by blast
  qed
qed

(* All vertices in the finish order are in the graph *)
lemma finish_order_vertices_in_graph:
  assumes "valid_graph graph"
  shows "\<forall>v. List.member (kosaraju_phase_1 graph) v \<longrightarrow> has_vertex graph v"
  using assms kosaraju_phase_1_vertices_only by blast

(* The finish order is properly ordered for phase 2 *)
lemma finish_order_is_vertex_list_ordered:
  assumes "valid_graph graph"
  shows "vertex_list_ordered (transpose_graph graph) {||} (kosaraju_phase_1 graph)"
  unfolding vertex_list_ordered_def
proof (intro allI impI)
  fix c d
  assume hyp: "has_edge (transpose_graph graph) d c 
                \<and> \<not>(in_same_scc (transpose_graph graph) d c)
                \<and> c |\<notin>| {||}"

  have edge_cd: "has_edge graph c d"
    using assms hyp transpose_edge_correspondence by blast
  have not_same_scc: "\<not>(in_same_scc graph c d)"
    using assms hyp transpose_same_scc in_same_scc_sym by metis
    
  (* Apply kosaraju_phase_1_correct *)
  have "finish_order_correct graph (kosaraju_phase_1 graph)"
    using assms kosaraju_phase_1_correct by simp

  then obtain v_c where
    vc_def: "has_vertex graph v_c \<and> in_same_scc graph v_c c \<and>
          (\<forall>v_d. has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
            index_of v_c (kosaraju_phase_1 graph) < index_of v_d (kosaraju_phase_1 graph))"
    using edge_cd finish_order_correct_def in_same_scc_sym not_same_scc by blast

  moreover have vertex_equiv: "\<forall>v. has_vertex graph v \<longleftrightarrow> List.member (kosaraju_phase_1 graph) v"
    using assms finish_list_contains_all_vertices_def finish_order_vertices_in_graph
      kosaraju_phase_1_complete by blast

  show "\<exists>v_c. List.member (kosaraju_phase_1 graph) v_c \<and>
                  has_vertex (transpose_graph graph) v_c \<and>
                  in_same_scc (transpose_graph graph) v_c c \<and>
                  (\<forall>v_d. List.member (kosaraju_phase_1 graph) v_d \<and>
                         has_vertex (transpose_graph graph) v_d \<and>
                         in_same_scc (transpose_graph graph) v_d d \<longrightarrow>
                         index_of v_c (kosaraju_phase_1 graph)
                         < index_of v_d (kosaraju_phase_1 graph))"
    by (meson assms transpose_same_scc transpose_same_vertices vc_def vertex_equiv)
qed

(* Establish common preconditions for collect_all_sccs theorems *)
lemma kosaraju_collect_preconditions:
  assumes "valid_graph graph"
  defines "finish_order \<equiv> kosaraju_phase_1 graph"
  defines "transposed \<equiv> transpose_graph graph"
  shows "valid_graph transposed"
    and "\<forall>w |\<in>| {||}. has_vertex transposed w"
    and "\<forall>w. List.member finish_order w \<longrightarrow> has_vertex transposed w"
    and "\<forall>v w. v |\<in>| {||} \<and> reachable transposed v w \<longrightarrow> w |\<in>| {||}"
    and "\<forall>v. has_vertex transposed v \<and> \<not>(List.member finish_order v) \<longrightarrow> v |\<in>| {||}"
    and "vertex_list_ordered transposed {||} finish_order"
proof -
  show "valid_graph transposed"
    unfolding transposed_def using assms(1) transpose_valid by simp
next
  show "\<forall>w |\<in>| {||}. has_vertex transposed w" by simp
next
  have finish_order_props: "\<forall>v. List.member finish_order v \<longrightarrow> has_vertex graph v"
    unfolding finish_order_def using assms(1) finish_order_vertices_in_graph by simp
  show "\<forall>w. List.member finish_order w \<longrightarrow> has_vertex transposed w"
    using assms(1) finish_order_props transpose_same_vertices transposed_def by blast
next
  show "\<forall>v w. v |\<in>| {||} \<and> reachable transposed v w \<longrightarrow> w |\<in>| {||}" by simp
next
  have finish_order_props: "\<forall>v. List.member finish_order v \<longrightarrow> has_vertex graph v"
    unfolding finish_order_def using assms(1) finish_order_vertices_in_graph by simp
  show "\<forall>v. has_vertex transposed v \<and> \<not>(List.member finish_order v) \<longrightarrow> v |\<in>| {||}"
    using assms(1) finish_list_contains_all_vertices_def finish_order_def
          kosaraju_phase_1_complete transpose_same_vertices transposed_def by blast
next
  show "vertex_list_ordered transposed {||} finish_order"
    using assms(1) finish_order_is_vertex_list_ordered
    unfolding transposed_def finish_order_def by simp
qed

(*-----------------------------------------------------------------------------*)
(* Main Correctness Theorems *)
(*-----------------------------------------------------------------------------*)

(* kosaraju is sound
   (each component returned by kosaraju is a strongly connected component)
*)
theorem kosaraju_sound:
  assumes "valid_graph graph"
    and "scc \<in> set (kosaraju graph)"
  shows "\<exists>v. v \<in> set scc \<and> (\<forall>u. u \<in> set scc \<longleftrightarrow> (has_vertex graph u \<and> in_same_scc graph u v))"
proof -
  define finish_order where "finish_order = kosaraju_phase_1 graph"
  define transposed where "transposed = transpose_graph graph"
  define sccs where "sccs = collect_all_sccs transposed {||} finish_order"

  have kosaraju_def: "kosaraju graph = sccs"
    unfolding kosaraju_def finish_order_def transposed_def sccs_def by simp

  (* Get all preconditions from helper lemma *)
  have precond: "valid_graph transposed \<and>
    (\<forall>w |\<in>| {||}. has_vertex transposed w) \<and>
    (\<forall>w. List.member finish_order w \<longrightarrow> has_vertex transposed w) \<and>
    (\<forall>v w. v |\<in>| {||} \<and> reachable transposed v w \<longrightarrow> w |\<in>| {||}) \<and>
    (\<forall>v. has_vertex transposed v \<and> \<not>(List.member finish_order v) \<longrightarrow> v |\<in>| {||}) \<and>
    (vertex_list_ordered transposed {||} finish_order)"
    using kosaraju_collect_preconditions
    by (metis (no_types, opaque_lifting) assms(1) finish_order_def transposed_def)

  (* Apply collect_all_sccs_are_sccs *)
  have "\<exists>v. List.member scc v \<and> (\<forall>u. List.member scc u \<longleftrightarrow> (has_vertex transposed u \<and> in_same_scc transposed u v))"
  proof -
    have "List.member (collect_all_sccs transposed {||} finish_order) scc"
      using assms(2) kosaraju_def sccs_def by (simp add: in_set_member)
    then show ?thesis
      using collect_all_sccs_are_sccs precond by blast
  qed

  (* Translate from transposed graph to original graph *)
  then obtain v where v_props:
    "v \<in> set scc" "\<forall>u. u \<in> set scc \<longleftrightarrow> (has_vertex transposed u \<and> in_same_scc transposed u v)"
    by (meson in_set_member)

  have "\<forall>u. u \<in> set scc \<longleftrightarrow> (has_vertex graph u \<and> in_same_scc graph u v)"
  proof (intro allI iffI)
    fix u
    assume "u \<in> set scc"
    then have "has_vertex transposed u" "in_same_scc transposed u v"
      using v_props(2) by blast+
    then show "has_vertex graph u \<and> in_same_scc graph u v"
      by (metis assms(1) in_same_scc.elims(2,3) transpose_reachability
          transpose_same_vertices transposed_def)
  next
    fix u
    assume "has_vertex graph u \<and> in_same_scc graph u v"
    then have "has_vertex transposed u \<and> in_same_scc transposed u v"
      using assms(1) transpose_same_scc transpose_same_vertices transposed_def by blast
    then show "u \<in> set scc"
      using v_props(2) by blast
  qed

  then show ?thesis using v_props(1) by blast
qed

(* kosaraju is complete
   (every vertex in the graph appears in some SCC returned by kosaraju) 
*)
theorem kosaraju_complete:
  assumes "valid_graph graph"
    and "has_vertex graph v"
  shows "\<exists>scc. scc \<in> set (kosaraju graph) \<and> v \<in> set scc"
proof -
  define finish_order where "finish_order = kosaraju_phase_1 graph"
  define transposed where "transposed = transpose_graph graph"
  define sccs where "sccs = collect_all_sccs transposed {||} finish_order"

  have kosaraju_def: "kosaraju graph = sccs"
    unfolding kosaraju_def finish_order_def transposed_def sccs_def by simp

  (* Get all preconditions from helper lemma *)
  have precond: "valid_graph transposed \<and>
    (\<forall>w |\<in>| {||}. has_vertex transposed w) \<and>
    (\<forall>w. List.member finish_order w \<longrightarrow> has_vertex transposed w) \<and>
    (\<forall>v w. v |\<in>| {||} \<and> reachable transposed v w \<longrightarrow> w |\<in>| {||}) \<and>
    (\<forall>v. has_vertex transposed v \<and> \<not>(List.member finish_order v) \<longrightarrow> v |\<in>| {||}) \<and>
    (vertex_list_ordered transposed {||} finish_order)"
    using kosaraju_collect_preconditions
    by (metis (no_types, opaque_lifting) assms(1) finish_order_def transposed_def)

  have "has_vertex transposed v"
    using assms(1,2) transpose_same_vertices transposed_def by blast

  have "\<exists>scc. scc \<in> set (collect_all_sccs transposed {||} finish_order) \<and> v \<in> set scc"
    using collect_all_sccs_vertices_in_graph precond \<open>has_vertex transposed v\<close>
    by blast

  then show ?thesis
    using kosaraju_def sccs_def by auto
qed

(* The vertices of each returned component are distinct *)
theorem kosaraju_distinct:
  assumes "valid_graph graph"
    and "scc \<in> set (kosaraju graph)"
  shows "distinct scc"
proof -
  define finish_order where "finish_order = kosaraju_phase_1 graph"
  define transposed where "transposed = transpose_graph graph"
  define sccs where "sccs = collect_all_sccs transposed {||} finish_order"

  have kosaraju_def: "kosaraju graph = sccs"
    unfolding kosaraju_def finish_order_def transposed_def sccs_def by simp

  (* Get all preconditions from helper lemma *)
  have precond: "valid_graph transposed \<and>
    (\<forall>w |\<in>| {||}. has_vertex transposed w) \<and>
    (\<forall>w. List.member finish_order w \<longrightarrow> has_vertex transposed w) \<and>
    (\<forall>v w. v |\<in>| {||} \<and> reachable transposed v w \<longrightarrow> w |\<in>| {||}) \<and>
    (\<forall>v. has_vertex transposed v \<and> \<not>(List.member finish_order v) \<longrightarrow> v |\<in>| {||}) \<and>
    (vertex_list_ordered transposed {||} finish_order)"
    using kosaraju_collect_preconditions
    by (metis (no_types, opaque_lifting) assms(1) finish_order_def transposed_def)

  show ?thesis
    using collect_all_sccs_distinct precond
    by (metis (mono_tags, lifting) assms(2) local.kosaraju_def sccs_def)
qed

(* The output SCCs are all distinct from each other (as sets),
   i.e. no SCC is listed twice *)
theorem kosaraju_distinct_list:
  assumes "valid_graph graph"
  shows "distinct (map set (kosaraju graph))"
proof -
  define finish_order where "finish_order = kosaraju_phase_1 graph"
  define transposed where "transposed = transpose_graph graph"
  define sccs where "sccs = collect_all_sccs transposed {||} finish_order"

  have kosaraju_def: "kosaraju graph = sccs"
    unfolding kosaraju_def finish_order_def transposed_def sccs_def by simp

  (* Get all preconditions from helper lemma *)
  have precond: "valid_graph transposed \<and>
    (\<forall>w |\<in>| {||}. has_vertex transposed w) \<and>
    (\<forall>w. List.member finish_order w \<longrightarrow> has_vertex transposed w) \<and>
    (\<forall>v w. v |\<in>| {||} \<and> reachable transposed v w \<longrightarrow> w |\<in>| {||}) \<and>
    (\<forall>v. has_vertex transposed v \<and> \<not>(List.member finish_order v) \<longrightarrow> v |\<in>| {||}) \<and>
    (vertex_list_ordered transposed {||} finish_order)"
    using kosaraju_collect_preconditions
    by (metis (no_types, opaque_lifting) assms finish_order_def transposed_def)

  show ?thesis
    using collect_all_sccs_distinct_list precond
    by (metis (no_types, lifting) local.kosaraju_def sccs_def)
qed

(* Ordering property:
   The SCCs returned by kosaraju are in topological order 
*)
theorem kosaraju_topologically_ordered:
  assumes "valid_graph graph"
  shows "sccs_topologically_ordered graph (kosaraju graph)"
proof -
  define finish_order where "finish_order = kosaraju_phase_1 graph"
  define transposed where "transposed = transpose_graph graph"
  define sccs where "sccs = collect_all_sccs transposed {||} finish_order"

  have kosaraju_def: "kosaraju graph = sccs"
    unfolding kosaraju_def finish_order_def transposed_def sccs_def by simp

  (* Get all preconditions from helper lemma *)
  have precond: "valid_graph transposed \<and>
    (\<forall>w |\<in>| {||}. has_vertex transposed w) \<and>
    (\<forall>w. List.member finish_order w \<longrightarrow> has_vertex transposed w) \<and>
    (\<forall>v w. v |\<in>| {||} \<and> reachable transposed v w \<longrightarrow> w |\<in>| {||}) \<and>
    (\<forall>v. has_vertex transposed v \<and> \<not>(List.member finish_order v) \<longrightarrow> v |\<in>| {||}) \<and>
    (vertex_list_ordered transposed {||} finish_order)"
    using kosaraju_collect_preconditions
    by (metis (no_types, opaque_lifting) assms finish_order_def transposed_def)

  (* Apply collect_all_sccs_reverse_topologically_ordered *)
  have "sccs_reverse_topologically_ordered transposed sccs"
    using collect_all_sccs_reverse_topologically_ordered precond sccs_def by blast

  (* Translate to topological order on original graph *)
  then show ?thesis
    using transpose_reverse_topo_is_topo[OF assms]
    unfolding transposed_def kosaraju_def by simp
qed

end
