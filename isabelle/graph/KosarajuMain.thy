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
  "kosaraju graph = collect_all_sccs (transpose_graph graph) {||} (kosaraju_phase_1 graph)"

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
  using assms(2) transpose_edge_correspondence[OF assms(1)]
  unfolding sccs_topologically_ordered_def sccs_reverse_topologically_ordered_def
  by blast

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

  obtain v_c where
    vc_def: "has_vertex graph v_c \<and> in_same_scc graph v_c c \<and>
          (\<forall>v_d. has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
            index_of v_c (kosaraju_phase_1 graph) < index_of v_d (kosaraju_phase_1 graph))"
    using kosaraju_phase_1_correct[OF assms] edge_cd not_same_scc
    unfolding finish_order_correct_def by blast

  have vertex_equiv: "\<forall>v. has_vertex graph v \<longleftrightarrow> List.member (kosaraju_phase_1 graph) v"
    using kosaraju_phase_1_complete[OF assms] kosaraju_phase_1_vertices_only[OF assms]
    unfolding finish_list_contains_all_vertices_def by blast

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

(* The preconditions of the collect_all_sccs theorems hold for the call made by kosaraju *)
lemma kosaraju_collect_pre:
  assumes "valid_graph graph"
  shows "collect_all_sccs_pre (transpose_graph graph) {||} (kosaraju_phase_1 graph)"
  unfolding collect_all_sccs_pre_def
proof (intro conjI)
  show "valid_graph (transpose_graph graph)"
    using transpose_valid[OF assms] .
  show "\<forall>w |\<in>| {||}. has_vertex (transpose_graph graph) w"
    by simp
  show "\<forall>w. List.member (kosaraju_phase_1 graph) w \<longrightarrow> has_vertex (transpose_graph graph) w"
    using kosaraju_phase_1_vertices_only[OF assms] transpose_same_vertices[OF assms] by blast
  show "\<forall>v w. v |\<in>| {||} \<and> reachable (transpose_graph graph) v w \<longrightarrow> w |\<in>| {||}"
    by simp
  show "\<forall>v. has_vertex (transpose_graph graph) v \<and> \<not>(List.member (kosaraju_phase_1 graph) v)
          \<longrightarrow> v |\<in>| {||}"
    using kosaraju_phase_1_complete[OF assms] transpose_same_vertices[OF assms]
    unfolding finish_list_contains_all_vertices_def by blast
  show "vertex_list_ordered (transpose_graph graph) {||} (kosaraju_phase_1 graph)"
    using finish_order_is_vertex_list_ordered[OF assms] .
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
  (* Apply collect_all_sccs_are_sccs on the transposed graph *)
  obtain v where v_in: "v \<in> set scc"
    and v_scc: "\<forall>u. u \<in> set scc \<longleftrightarrow>
                  (has_vertex (transpose_graph graph) u \<and> in_same_scc (transpose_graph graph) u v)"
    using collect_all_sccs_are_sccs[OF kosaraju_collect_pre[OF assms(1)]
            assms(2)[unfolded kosaraju_def]]
    by blast

  (* Translate from the transposed graph back to the original graph *)
  have "u \<in> set scc \<longleftrightarrow> (has_vertex graph u \<and> in_same_scc graph u v)" for u
    using v_scc transpose_same_vertices[OF assms(1)] transpose_same_scc[OF assms(1) refl]
    by blast
  with v_in show ?thesis by blast
qed

(* kosaraju is complete
   (every vertex in the graph appears in some SCC returned by kosaraju)
*)
theorem kosaraju_complete:
  assumes "valid_graph graph"
    and "has_vertex graph v"
  shows "\<exists>scc. scc \<in> set (kosaraju graph) \<and> v \<in> set scc"
proof -
  have "has_vertex (transpose_graph graph) v"
    using assms transpose_same_vertices by blast
  then show ?thesis
    unfolding kosaraju_def
    by (rule collect_all_sccs_vertices_in_graph[OF kosaraju_collect_pre[OF assms(1)]
              _ equalsffemptyD[OF refl]])
qed

(* The vertices of each returned component are distinct *)
theorem kosaraju_distinct:
  assumes "valid_graph graph"
    and "scc \<in> set (kosaraju graph)"
  shows "distinct scc"
  by (rule collect_all_sccs_distinct[OF kosaraju_collect_pre[OF assms(1)]
            assms(2)[unfolded kosaraju_def]])

(* The output SCCs are all distinct from each other (as sets),
   i.e. no SCC is listed twice *)
theorem kosaraju_distinct_list:
  assumes "valid_graph graph"
  shows "distinct (map set (kosaraju graph))"
  unfolding kosaraju_def
  by (rule collect_all_sccs_distinct_list[OF kosaraju_collect_pre[OF assms]])

(* Ordering property:
   The SCCs returned by kosaraju are in topological order
*)
theorem kosaraju_topologically_ordered:
  assumes "valid_graph graph"
  shows "sccs_topologically_ordered graph (kosaraju graph)"
  unfolding kosaraju_def
  by (rule transpose_reverse_topo_is_topo[OF assms
        collect_all_sccs_reverse_topologically_ordered[OF kosaraju_collect_pre[OF assms]]])

end
