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

(* General list lemma: Find first element satisfying a property.
   Given a non-empty list where the first element doesn't satisfy property P,
   but some element does satisfy P, we can decompose the list as prefix @ [z] @ tail
   where all elements in the prefix don't satisfy P, but z does satisfy P. *)
lemma list_first_satisfying:
  fixes xs :: "'a list"
    and P :: "'a \<Rightarrow> bool"
  assumes "xs \<noteq> []"
    and "\<not>P (hd xs)"
    and "\<exists>y \<in> set xs. P y"
  shows "\<exists>prefix z tail. xs = prefix @ [z] @ tail \<and>
                         prefix \<noteq> [] \<and>
                         (\<forall>v \<in> set prefix. \<not>P v) \<and>
                         P z"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x rest)
  show ?case
  proof (cases "rest = []")
    case True
    (* rest is empty, so xs = [x] *)
    then have "xs = [x]" using Cons by simp
    (* But we have \<exists>y \<in> set xs. P y, and \<not>P x, contradiction *)
    then have "x \<in> set xs" by simp
    then have "\<not>P x" using Cons.prems(2) \<open>xs = [x]\<close> by simp
    moreover have "\<exists>y \<in> set xs. P y" using Cons.prems(3)
      by (simp add: assms(3)) 
    ultimately have "\<exists>y \<in> {x}. P y" using \<open>xs = [x]\<close> by simp
    then have "P x" by simp
    then show ?thesis using \<open>\<not>P x\<close> by contradiction
  next
    case False
    (* rest is non-empty *)
    then obtain y ys where rest_decomp: "rest = y # ys" by (cases rest) auto

    show ?thesis
    proof (cases "P y")
      case True
      (* y satisfies P, so we found it: xs = [x] @ [y] @ ys *)
      define prefix where "prefix = [x]"
      define tail where "tail = ys"
      have "x # rest = prefix @ [y] @ tail"
        by (simp add: prefix_def rest_decomp tail_def) 
      thus ?thesis
        by (metis Cons.prems(2) True in_set_replicate length_Cons list.sel(1) list.size(3) prefix_def
            remdups_adj.simps(2) remdups_adj_singleton_iff)
    next
      case False
      (* y doesn't satisfy P either *)
      show ?thesis
      proof (cases "\<exists>z \<in> set rest. P z")
        case True
        (* Some element in rest satisfies P *)
        then have "\<not>P (hd rest)"
          using rest_decomp False by simp

        (* Apply IH to rest *)
        then have "\<exists>prefix z tail. rest = prefix @ [z] @ tail \<and>
                                    prefix \<noteq> [] \<and>
                                    (\<forall>v \<in> set prefix. \<not>P v) \<and>
                                    P z"
          using Cons.IH[OF _ _ True] rest_decomp by simp

        then obtain prefix z tail where rest_props:
          "rest = prefix @ [z] @ tail"
          "prefix \<noteq> []"
          "(\<forall>v \<in> set prefix. \<not>P v)"
          "P z"
          by blast

        (* Now xs = x # (prefix @ [z] @ tail) = (x # prefix) @ [z] @ tail *)
        have "x # rest = (x # prefix) @ [z] @ tail"
          by (simp add: rest_props(1))
        moreover have "x # prefix \<noteq> []" by simp
        moreover have "\<forall>v \<in> set (x # prefix). \<not>P v"
          using Cons.prems(2) rest_props(3) by simp
        moreover have "P z" using rest_props(4) by simp
        ultimately show ?thesis by blast
      next
        case False
        (* No element in rest satisfies P *)
        then have no_p_in_rest: "\<nexists>z. z \<in> set rest \<and> P z" by simp
        (* But we know \<exists>y \<in> set xs. P y *)
        have "\<exists>y \<in> set xs. P y"
          by (simp add: assms(3)) 
        (* xs = x # rest, so y is either x or in rest *)
        then have "P x \<or> (\<exists>y \<in> set rest. P y)"
          using Cons.prems(3) by auto 
        then have "P x" using no_p_in_rest by simp
        (* But \<not>P x *)
        then show ?thesis using Cons.prems(2) by simp
      qed
    qed
  qed
qed

(* Helper lemma: Establish that downstream SCCs are already visited.
   This lemma shows that if we have a vertex 'start' at the head of an ordered vertex list,
   and start is unvisited, then all vertices reachable from start that are NOT in the same
   SCC as start must already be visited. This is the key precondition needed for
   collect_one_scc_sound. *)
lemma downstream_sccs_visited:
  assumes "valid_graph graph"
    and "\<forall>w |\<in>| visited. has_vertex graph w"
    and "\<forall>v w. v |\<in>| visited \<and> reachable graph v w \<longrightarrow> w |\<in>| visited"
    and "\<forall>v. has_vertex graph v \<and> \<not>(List.member vertices v) \<longrightarrow> v |\<in>| visited"
    and "vertex_list_ordered graph visited vertices"
    and "vertices = start # rest"
    and "start |\<notin>| visited"
  shows "\<forall>w. has_vertex graph w \<and> reachable graph start w \<and> \<not>(in_same_scc graph w start) \<longrightarrow>
             w |\<in>| visited"
proof (intro allI impI)
  fix w
  assume w_props: "has_vertex graph w \<and> reachable graph start w \<and> \<not>(in_same_scc graph w start)"

  (* Since start reaches w, there exists a valid path from start to w *)
  obtain path where path_props:
    "valid_path graph path"
    "path_start path = start"
    "path_end path = w"
    using assms(1) w_props reachable_implies_valid_path by blast

  (* Find the first vertex on the path that is not in start's SCC.
     This gives us a path prefix [y1,...,yn,x] where:
     - y1 = start
     - y1,...,yn are all in start's SCC
     - x is the first vertex not in start's SCC
     - yn -> x is a cross-SCC edge *)

  (* Since w is not in start's SCC, and the path ends at w, there must be
     at least one vertex on the path that is not in start's SCC *)
  have "\<exists>x. List.member path x \<and> \<not>(in_same_scc graph x start)"
  proof -
    have "path \<noteq> []"
      using path_props(1) by auto
    hence "List.member path w"
      using path_props(3) path_end_in_path by auto
    thus ?thesis
      using w_props by blast
  qed

  (* Let x be the first such vertex on the path *)
  obtain prefix x path_tail where x_def:
    "path = prefix @ [x] @ path_tail"
    "prefix \<noteq> []"
    "\<forall>y \<in> set prefix. in_same_scc graph y start"
    "\<not>(in_same_scc graph x start)"
  proof -
    (* Apply list_first_satisfying with P = \<lambda>v. \<not>(in_same_scc graph v start) *)
    define P where "P = (\<lambda>v. \<not>(in_same_scc graph v start))"

    (* path is non-empty *)
    have "path \<noteq> []"
      using path_props(1) by auto

    (* The first element of path is start *)
    have "hd path = start"
      using path_props(1,2)
      by (metis \<open>path \<noteq> []\<close> list.sel(1) path_start.elims)

    (* start is in the same SCC as start, so \<not>P (hd path) *)
    have "\<not>P (hd path)"
      unfolding P_def
      using \<open>hd path = start\<close>
      by (metis assms(1) edge_implies_vertices(1) in_same_scc_refl reachable_first_step w_props)

    (* We know \<exists>x. List.member path x \<and> \<not>(in_same_scc graph x start) *)
    (* which means \<exists>x \<in> set path. P x *)
    have "\<exists>y \<in> set path. P y"
      unfolding P_def
      using \<open>\<exists>x. List.member path x \<and> \<not>(in_same_scc graph x start)\<close>
      by (meson in_set_member)

    (* Apply list_first_satisfying *)
    then obtain prefix z tail where decomp:
      "path = prefix @ [z] @ tail"
      "prefix \<noteq> []"
      "(\<forall>v \<in> set prefix. \<not>P v)"
      "P z"
      using \<open>\<not> P (hd path)\<close> \<open>path \<noteq> []\<close> list_first_satisfying by blast

    (* Translate back from P *)
    have "\<forall>y \<in> set prefix. in_same_scc graph y start"
      using decomp(3) unfolding P_def by simp
    moreover have "\<not>(in_same_scc graph z start)"
      using decomp(4) unfolding P_def by simp

    ultimately show ?thesis
      using decomp(1,2) that by blast
  qed

  (* x must be a vertex in the graph *)
  have x_in_graph: "has_vertex graph x"
    by (metis append_Cons assms(1) edge_implies_vertices(1) in_set_conv_decomp path_props(1,3)
        reachable_first_step vertex_on_path_reachable w_props x_def(1))
    
  (* There must be a vertex yn in start's SCC with an edge yn -> x *)
  obtain yn where yn_props:
    "has_edge graph yn x"
    "in_same_scc graph yn start"
  proof -
    (* Since prefix is non-empty, we can decompose it as prefix' @ [yn] *)
    obtain prefix' yn where prefix_decomp: "prefix = prefix' @ [yn]"
      by (metis append_butlast_last_id x_def(2))

    (* Therefore path = prefix' @ [yn, x] *)
    then have path_decomp: "path = prefix' @ [yn, x] @ path_tail"
      using x_def(1) by auto
      
    (* By valid_path, there must be an edge yn -> x *)
    have "has_edge graph yn x"
      using path_props(1) path_decomp
    proof (induction prefix' arbitrary: path)
      case Nil
      then have "path = [yn, x] @ path_tail"
        by simp
      then show ?case
        using Nil.prems(1) by auto
    next
      case (Cons a prefix'')
      then have "path = a # prefix'' @ [yn, x] @ path_tail"
        by simp
      then have "valid_path graph (prefix'' @ [yn, x] @ path_tail)"
        using Cons.prems(1) valid_path.elims(3) by fastforce
      then show ?case
        using Cons.IH by blast
    qed

    (* By x_def(3), yn is in prefix, so yn is in start's SCC *)
    moreover have "in_same_scc graph yn start"
      using x_def(3) prefix_decomp by simp

    ultimately show ?thesis
      using that by blast
  qed

  (* Now we have two cases for x *)
  show "w |\<in>| visited"
  proof (cases "x |\<in>| visited")
    case True
    (* Case 1: x is visited *)
    (* Since x is visited and x reaches w (x is on the path to w),
       w must also be visited by assumption 3 *)
    have "reachable graph x w"
      by (metis append_Cons assms(1) in_set_conv_decomp path_props(1,3) vertex_on_path_reachable
          x_def(1))
    then show ?thesis
      using assms(3) True by blast
  next
    case False
    (* Case 2: x is unvisited *)
    (* Since x is unvisited but in the graph, x must be in the vertices list *)
    have "List.member vertices x"
      using assms(4) x_in_graph False by blast

    (* start is also in the vertices list (it's at the head) *)
    have "List.member vertices start"
      using assms(6) by (simp add: member_rec(1))

    (* We have edge yn -> x, where x and yn are in different SCCs,
       and x appears in the vertices list *)
    have "has_edge graph yn x"
      using yn_props(1) by simp
    moreover have "\<not>(in_same_scc graph yn x)"
      using yn_props(2) x_def(2) in_same_scc_sym in_same_scc_trans
      using x_def(4) by blast 
    moreover have "List.member vertices x"
      using \<open>List.member vertices x\<close> by simp
    ultimately have "\<exists>v_x. List.member vertices v_x \<and> has_vertex graph v_x \<and> in_same_scc graph v_x x \<and>
                          (\<forall>v_yn. List.member vertices v_yn \<and> has_vertex graph v_yn \<and> in_same_scc graph v_yn yn \<longrightarrow>
                            index_of v_x vertices < index_of v_yn vertices)"
      using assms(5) unfolding vertex_list_ordered_def
      by (simp add: False) 

    (* This gives us v_x in x's SCC that appears before all vertices in yn's SCC *)
    then obtain v_x where v_x_props:
      "has_vertex graph v_x"
      "in_same_scc graph v_x x"
      "(\<forall>v_yn. List.member vertices v_yn \<and> has_vertex graph v_yn \<and> in_same_scc graph v_yn yn \<longrightarrow>
         index_of v_x vertices < index_of v_yn vertices)"
      by auto

    (* start is in yn's SCC (by transitivity: start ~ yn) *)
    have "in_same_scc graph start yn"
      using yn_props(2) in_same_scc_sym by simp

    (* Therefore v_x appears before start in the vertices list *)
    have "index_of v_x vertices < index_of start vertices"
      using v_x_props(1,3) \<open>in_same_scc graph start yn\<close>
      using assms(1) edge_implies_vertices(1) reachable_first_step w_props
      using \<open>List.member vertices start\<close> by blast 

    (* But start is at the head of the vertices list, so it has index 0 *)
    have "index_of start vertices = 0"
      by (metis assms(6) index_of.simps(2))

    (* This means index_of v_x vertices < 0, which is impossible *)
    then show ?thesis
      using \<open>index_of v_x vertices < index_of start vertices\<close> by simp
  qed
qed

(* Helper lemma: Establish that all vertices in the same SCC as start are unvisited.
   This shows that when processing vertex start, no other vertex in start's SCC
   has been visited yet. This is a key precondition for collect_one_scc_complete. *)
lemma same_scc_unvisited:
  assumes "\<forall>v w. v |\<in>| visited \<and> reachable graph v w \<longrightarrow> w |\<in>| visited"
    and "start |\<notin>| visited"
  shows "\<forall>w. has_vertex graph w \<and> in_same_scc graph w start \<longrightarrow> w |\<notin>| visited"
proof (intro allI impI)
  fix w
  assume w_props: "has_vertex graph w \<and> in_same_scc graph w start"

  (* We need to show w is not visited *)
  (* By contradiction: assume w is visited *)
  show "w |\<notin>| visited"
  proof (rule ccontr)
    assume "\<not> w |\<notin>| visited"
    then have w_visited: "w |\<in>| visited" by simp

    (* Since w and start are in the same SCC, start is reachable from w *)
    have "reachable graph w start"
      using w_props in_same_scc_sym by auto

    (* By assumption 1, if w is visited and start is reachable from w,
       then start must also be visited *)
    have "start |\<in>| visited"
      using assms(1) w_visited \<open>reachable graph w start\<close>
      using in_same_scc.simps w_props by blast

    (* But this contradicts assumption 2 that start is not visited *)
    then show False
      using assms(2) by simp
  qed
qed

(* Helper lemma establishing properties needed for recursive calls in collect_all_sccs proofs *)
lemma collect_all_sccs_recursive_properties:
  assumes "valid_graph graph"
    and "\<forall>w |\<in>| visited. has_vertex graph w"
    and "\<forall>w. List.member (start # rest) w \<longrightarrow> has_vertex graph w"
    and "\<forall>v w. v |\<in>| visited \<and> reachable graph v w \<longrightarrow> w |\<in>| visited"
    and "\<forall>v. has_vertex graph v \<and> \<not>(List.member (start # rest) v) \<longrightarrow> v |\<in>| visited"
    and "vertex_list_ordered graph visited (start # rest)"
    and "start |\<notin>| visited"
    and "collect_one_scc graph visited start = (scc_start, new_visited)"
  shows "\<forall>w |\<in>| new_visited. has_vertex graph w"
    and "\<forall>w. List.member rest w \<longrightarrow> has_vertex graph w"
    and "\<forall>v w. v |\<in>| new_visited \<and> reachable graph v w \<longrightarrow> w |\<in>| new_visited"
    and "\<forall>v. has_vertex graph v \<and> \<not>(List.member rest v) \<longrightarrow> v |\<in>| new_visited"
    and "vertex_list_ordered graph new_visited rest"
proof -
  have start_in_graph: "has_vertex graph start"
    using assms(3,7) by (simp add: member_rec(1))

  (* Establish fundamental properties *)
  have downstream_visited: "\<forall>w. has_vertex graph w \<and> reachable graph start w 
                              \<and> \<not>(in_same_scc graph w start) \<longrightarrow> w |\<in>| visited"
    using downstream_sccs_visited
    by (metis (no_types, lifting) assms(1,2,4,5,6))

  have scc_unvisited: "\<forall>w. has_vertex graph w \<and> in_same_scc graph w start \<longrightarrow> w |\<notin>| visited"
    using same_scc_unvisited
    using assms(4,7) by blast

  (* Rest members are in graph *)
  show "\<forall>w. List.member rest w \<longrightarrow> has_vertex graph w"
    using assms(3,7) by (simp add: member_rec(1))

  (* New visited contains vertices *)
  show "\<forall>w |\<in>| new_visited. has_vertex graph w"
  proof
    fix w assume "w |\<in>| new_visited"
    have "new_visited = visited |\<union>| fset_of_list scc_start"
      using assms(1,2,7,8) collect_one_scc_visited_update downstream_visited scc_unvisited
        start_in_graph by blast
    then have "w |\<in>| visited \<or> w \<in> set scc_start"
      using \<open>w |\<in>| new_visited\<close> by (simp add: fset_of_list_elem)
    then show "has_vertex graph w"
    proof
      assume "w |\<in>| visited"
      then show ?thesis using assms(2) by simp
    next
      assume "w \<in> set scc_start"
      then have "List.member scc_start w" by (simp add: in_set_member)
      have "in_same_scc graph w start"
        using \<open>List.member scc_start w\<close> assms(1,2,7,8) collect_one_scc_sound downstream_visited
          scc_unvisited start_in_graph by blast
      then show ?thesis
        by (metis assms(1) edge_implies_vertices(1) scc_path_avoiding_vertex start_in_graph)
    qed
  qed

  (* Closure under reachability *)
  show "\<forall>v w. v |\<in>| new_visited \<and> reachable graph v w \<longrightarrow> w |\<in>| new_visited"
  proof (intro allI impI)
    fix v' w
    assume "v' |\<in>| new_visited \<and> reachable graph v' w"
    then have v'_visited: "v' |\<in>| new_visited" and reachable_vw: "reachable graph v' w" by auto

    have "new_visited = visited |\<union>| fset_of_list scc_start"
      using assms(1,2,7,8) collect_one_scc_visited_update downstream_visited scc_unvisited
        start_in_graph by blast
    then have "v' |\<in>| visited \<or> v' \<in> set scc_start"
      using v'_visited by (simp add: fset_of_list_elem)
    then show "w |\<in>| new_visited"
    proof
      assume "v' |\<in>| visited"
      then have "w |\<in>| visited"
        using assms(4) reachable_vw by blast
      then show ?thesis
        using \<open>new_visited = visited |\<union>| fset_of_list scc_start\<close> by simp
    next
      assume "v' \<in> set scc_start"
      then have "List.member scc_start v'" by (simp add: in_set_member)
      have "in_same_scc graph v' start"
        using \<open>List.member scc_start v'\<close> assms(1,2,7,8) collect_one_scc_sound downstream_visited
          scc_unvisited start_in_graph by blast
      have "reachable graph start w"
        using \<open>in_same_scc graph v' start\<close> reachable_vw reachable_trans by auto
      show ?thesis
      proof (cases "in_same_scc graph w start")
        case True
        have "has_vertex graph w"
          using True assms(1) edge_implies_vertices(1) scc_path_avoiding_vertex start_in_graph
          by blast
        then have "w \<in> set scc_start"
          using collect_one_scc_complete[OF assms(1) start_in_graph \<open>has_vertex graph w\<close>
                assms(2) True scc_unvisited downstream_visited assms(8)]
          by (simp add: in_set_member)
        then show ?thesis
          using \<open>new_visited = visited |\<union>| fset_of_list scc_start\<close>
          by (simp add: fset_of_list_elem)
      next
        case False
        have "has_vertex graph w"
          by (metis \<open>reachable graph start w\<close> assms(1) edge_implies_vertices(2) reachable.cases)
        then have "w |\<in>| visited"
          using downstream_visited \<open>reachable graph start w\<close> False by simp
        then show ?thesis
          using \<open>new_visited = visited |\<union>| fset_of_list scc_start\<close> by simp
      qed
    qed
  qed

  (* Vertices not in rest are in new_visited *)
  show "\<forall>v'. has_vertex graph v' \<and> \<not>(List.member rest v') \<longrightarrow> v' |\<in>| new_visited"
  proof (intro allI impI)
    fix v'
    assume v'_props: "has_vertex graph v' \<and> \<not>(List.member rest v')"
    show "v' |\<in>| new_visited"
    proof (cases "v' = start")
      case True
      have "start \<in> set scc_start"
        using collect_one_scc_complete[OF assms(1) start_in_graph start_in_graph
              assms(2) _ scc_unvisited downstream_visited assms(8)]
        using in_same_scc_refl start_in_graph
        by (metis in_set_member)
      then show ?thesis
        using True collect_one_scc_visited_update[OF assms(1) start_in_graph assms(2) 
                      scc_unvisited downstream_visited assms(7,8)]
        by (simp add: fset_of_list_elem)
    next
      case False
      then have "\<not>(List.member (start # rest) v')"
        using v'_props by (simp add: member_rec(1))
      then have "v' |\<in>| visited"
        using assms(5,7) v'_props by auto
      then show ?thesis
        using collect_one_scc_visited_update[OF assms(1) start_in_graph assms(2)
                      scc_unvisited downstream_visited assms(7,8)]
        by auto
    qed
  qed

  (* Rest is properly ordered *)
  show "vertex_list_ordered graph new_visited rest"
  proof -
    have "vertex_list_ordered graph visited (start # rest)"
      using assms(6,7) by auto
    moreover have "visited |\<subseteq>| new_visited"
      using collect_one_scc_visited_update[OF assms(1) start_in_graph assms(2)
                      scc_unvisited downstream_visited assms(7,8)]
      by auto
    ultimately have "vertex_list_ordered graph new_visited (start # rest)"
      using vertex_list_ordered_monotonic by blast
    moreover have "start |\<in>| new_visited"
    proof -
      have "start \<in> set scc_start"
        using collect_one_scc_complete[OF assms(1) start_in_graph start_in_graph
              assms(2) _ scc_unvisited downstream_visited assms(8)]
        using in_same_scc_refl start_in_graph
        by (metis in_set_member)
      then show ?thesis
        using collect_one_scc_visited_update[OF assms(1) start_in_graph assms(2)
                        scc_unvisited downstream_visited assms(7,8)]
        by (simp add: fset_of_list_elem)
    qed
    ultimately show ?thesis
      using vertex_list_ordered_tail
      using \<open>\<forall>v w. v |\<in>| new_visited \<and> reachable graph v w \<longrightarrow> w |\<in>| new_visited\<close> by blast
  qed
qed

(* Helper lemma for the case when start is already visited in collect_all_sccs proofs *)
lemma collect_all_sccs_skip_visited_properties:
  assumes "valid_graph graph"
    and "\<forall>w |\<in>| visited. has_vertex graph w"
    and "\<forall>w. List.member (start # rest) w \<longrightarrow> has_vertex graph w"
    and "\<forall>v w. v |\<in>| visited \<and> reachable graph v w \<longrightarrow> w |\<in>| visited"
    and "\<forall>v. has_vertex graph v \<and> \<not>(List.member (start # rest) v) \<longrightarrow> v |\<in>| visited"
    and "vertex_list_ordered graph visited (start # rest)"
    and "start |\<in>| visited"
  shows "\<forall>w. List.member rest w \<longrightarrow> has_vertex graph w"
    and "vertex_list_ordered graph visited rest"
    and "\<forall>v. has_vertex graph v \<and> \<not>(List.member rest v) \<longrightarrow> v |\<in>| visited"
proof -
  show "\<forall>w. List.member rest w \<longrightarrow> has_vertex graph w"
    using assms(3) by (simp add: member_rec(1))

  show "vertex_list_ordered graph visited rest"
    using assms(4,6,7) vertex_list_ordered_tail by blast

  show "\<forall>v. has_vertex graph v \<and> \<not>(List.member rest v) \<longrightarrow> v |\<in>| visited"
  proof (intro allI impI)
    fix v
    assume "has_vertex graph v \<and> \<not>(List.member rest v)"
    show "v |\<in>| visited"
    proof (cases "v = start")
      case True
      then show ?thesis using assms(7) by simp
    next
      case False
      then have "\<not>(List.member (start # rest) v)"
        using \<open>has_vertex graph v \<and> \<not>(List.member rest v)\<close> by (simp add: member_rec(1))
      then show ?thesis
        using assms(5) \<open>has_vertex graph v \<and> \<not>(List.member rest v)\<close> by simp
    qed
  qed
qed

(* Vertices in SCCs collected by collect_all_sccs were not initially visited *)
lemma collect_all_sccs_vertices_were_unvisited:
  assumes "valid_graph graph"
    and "\<forall>w |\<in>| visited. has_vertex graph w"
    and "\<forall>w. List.member vertices w \<longrightarrow> has_vertex graph w"
    and "\<forall>v w. v |\<in>| visited \<and> reachable graph v w \<longrightarrow> w |\<in>| visited"
    and "\<forall>v. has_vertex graph v \<and> \<not>(List.member vertices v) \<longrightarrow> v |\<in>| visited"
    and "vertex_list_ordered graph visited vertices"
    and "set scc \<in> set (map set (collect_all_sccs graph visited vertices))"
    and "v \<in> set scc"
  shows "v |\<notin>| visited"
  using assms
proof (induction vertices arbitrary: visited scc v)
  case Nil
  then show ?case
    by (metis collect_all_sccs.simps(1) in_set_member list.simps(8) member_rec(2))
next
  case (Cons start rest)
  show ?case
  proof (cases "start |\<in>| visited")
    case True
    then have "collect_all_sccs graph visited (start # rest) = collect_all_sccs graph visited rest"
      by simp
    then have prem: "set scc \<in> set (map set (collect_all_sccs graph visited rest))"
      using Cons.prems(7) by simp

    have skip_props:
      "\<forall>w. List.member rest w \<longrightarrow> has_vertex graph w"
      "vertex_list_ordered graph visited rest"
      "\<forall>v. has_vertex graph v \<and> \<not>(List.member rest v) \<longrightarrow> v |\<in>| visited"
      using collect_all_sccs_skip_visited_properties[OF Cons.prems(1,2,3,4,5,6) True]
      by blast+

    show ?thesis
      using Cons.IH Cons.prems(2,4,8) prem assms(1)
        skip_props(1,2,3) by blast
  next
    case False
    have start_in_graph: "has_vertex graph start"
      using Cons.prems(3) by (simp add: member_rec(1))
    have same_scc_unvisited: "\<forall>w. has_vertex graph w \<and> in_same_scc graph w start \<longrightarrow> w |\<notin>| visited"
      using False in_same_scc.simps Cons.prems(4) by blast
    have downstream_visited: "\<forall>w. has_vertex graph w \<and> reachable graph start w \<and> \<not>(in_same_scc graph w start) \<longrightarrow> w |\<in>| visited"
      using Cons.prems(2,4,5,6) assms(1) downstream_sccs_visited by blast

    obtain scc_start new_visited where collect_result:
      "collect_one_scc graph visited start = (scc_start, new_visited)"
      by (metis surj_pair)

    have "collect_all_sccs graph visited (start # rest) =
          scc_start # collect_all_sccs graph new_visited rest"
      using False collect_result by simp
    then have "set scc = set scc_start \<or> set scc \<in> set (map set (collect_all_sccs graph new_visited rest))"
      using Cons.prems(7) by auto

    then show ?thesis
    proof
      assume "set scc = set scc_start"
      show ?thesis
      proof -
        have "List.member scc_start v"
          using \<open>set scc = set scc_start\<close> Cons.prems(8)
          by (simp add: in_set_member)
        have "in_same_scc graph v start"
          using collect_one_scc_sound[OF Cons.prems(1) start_in_graph Cons.prems(2) False
                same_scc_unvisited downstream_visited collect_result \<open>List.member scc_start v\<close>]
          by blast
        show ?thesis
          using same_scc_unvisited \<open>in_same_scc graph v start\<close> Cons.prems(8)
          using Cons.prems(2) by blast
      qed

    next
      assume prem: "set scc \<in> set (map set (collect_all_sccs graph new_visited rest))"

      (* Use helper lemma to establish all properties for recursive call *)
      have recursive_props:
        "\<forall>w |\<in>| new_visited. has_vertex graph w"
        "\<forall>w. List.member rest w \<longrightarrow> has_vertex graph w"
        "\<forall>v w. v |\<in>| new_visited \<and> reachable graph v w \<longrightarrow> w |\<in>| new_visited"
        "\<forall>v. has_vertex graph v \<and> \<not>(List.member rest v) \<longrightarrow> v |\<in>| new_visited"
        "vertex_list_ordered graph new_visited rest"
        using collect_all_sccs_recursive_properties[OF Cons.prems(1,2,3,4,5,6) False collect_result]
        by blast+

      have "v |\<notin>| new_visited"
        using Cons.IH[OF Cons.prems(1) recursive_props prem]
        by (simp add: Cons.prems(8)) 

      moreover have "visited |\<subseteq>| new_visited"
        using collect_one_scc_visited_update[OF Cons.prems(1) start_in_graph Cons.prems(2)
              same_scc_unvisited downstream_visited False collect_result]
        by auto

      ultimately show ?thesis by auto
    qed
  qed
qed

(*-----------------------------------------------------------------------------*)
(* Correctness Theorems for collect_all_sccs *)
(*-----------------------------------------------------------------------------*)

(* Each component returned by collect_all_sccs is a strongly connected component *)
theorem collect_all_sccs_are_sccs:
  assumes "valid_graph graph"
    and "\<forall>w |\<in>| visited. has_vertex graph w"
    and "\<forall>w. List.member vertices w \<longrightarrow> has_vertex graph w"
    and "\<forall>v w. v |\<in>| visited \<and> reachable graph v w \<longrightarrow> w |\<in>| visited"
    and "\<forall>v. has_vertex graph v \<and> \<not>(List.member vertices v) \<longrightarrow> v |\<in>| visited"
    and "vertex_list_ordered graph visited vertices"
    and "List.member (collect_all_sccs graph visited vertices) scc"
  shows "\<exists>v. List.member scc v \<and> (\<forall>u. List.member scc u \<longleftrightarrow> (has_vertex graph u \<and> in_same_scc graph u v))"
  using assms
proof (induction vertices arbitrary: visited scc)
  case Nil
  (* Empty vertices list: no SCCs returned *)
  then show ?case
    by (metis collect_all_sccs.simps(1) member_rec(2)) 
next
  case (Cons start rest)
  show ?case
  proof (cases "start |\<in>| visited")
    case True
    (* start is already visited, skip it *)
    have "collect_all_sccs graph visited (start # rest) = collect_all_sccs graph visited rest"
      using True by simp
    then have "List.member (collect_all_sccs graph visited rest) scc"
      using Cons.prems(7) by simp

    have skip_props:
      "\<forall>w. List.member rest w \<longrightarrow> has_vertex graph w"
      "vertex_list_ordered graph visited rest"
      "\<forall>v. has_vertex graph v \<and> \<not>(List.member rest v) \<longrightarrow> v |\<in>| visited"
      using collect_all_sccs_skip_visited_properties[OF assms(1) Cons.prems(2,3,4,5,6) True]
      by blast+

    (* Apply IH to rest with same visited set *)
    show ?thesis
      using Cons.IH Cons.prems(2,4) \<open>List.member (collect_all_sccs graph visited rest) scc\<close> assms(1)
        skip_props(1,2,3) by blast
      
  next
    case False
    (* start is unvisited, so we collect its SCC *)
    have start_unvisited: "start |\<notin>| visited" using False by simp

    (* start must be in the vertices list *)
    have "List.member (start # rest) start"
      by (simp add: member_rec(1))

    (* Therefore start must be a vertex in the graph *)
    have start_in_graph: "has_vertex graph start"
      using Cons.prems(3) \<open>List.member (start # rest) start\<close> by blast

    (* By downstream_sccs_visited, all downstream SCCs are already visited *)
    have downstream_visited: "\<forall>w. has_vertex graph w \<and> reachable graph start w \<and>
                                    \<not>(in_same_scc graph w start) \<longrightarrow> w |\<in>| visited"
      using Cons.prems(2,4,5,6) assms(1) downstream_sccs_visited by blast

    (* By same_scc_unvisited, all vertices in start's SCC are unvisited *)
    have same_scc_unvisited: "\<forall>w. has_vertex graph w \<and> in_same_scc graph w start \<longrightarrow> w |\<notin>| visited"
      using Cons.prems(4) in_same_scc.simps start_unvisited by blast
      
    (* Collect start's SCC *)
    obtain scc_start new_visited where collect_result:
      "collect_one_scc graph visited start = (scc_start, new_visited)"
      by (metis surj_pair)

    (* The result is scc_start # collect_all_sccs graph new_visited rest *)
    have collect_decomp: "collect_all_sccs graph visited (start # rest) =
                          scc_start # collect_all_sccs graph new_visited rest"
      using False collect_result by simp

    (* start is in scc_start *)
    have start_in_scc_start: "List.member scc_start start"
      using collect_one_scc_complete[OF Cons.prems(1) start_in_graph start_in_graph
            Cons.prems(2) _ same_scc_unvisited downstream_visited collect_result]
      using in_same_scc_refl start_in_graph by blast

    (* scc is either scc_start or in the recursive call *)
    have "scc = scc_start \<or> List.member (collect_all_sccs graph new_visited rest) scc"
      by (metis Cons.prems(7) collect_decomp member_rec(1))
      
    then show ?thesis
    proof
      assume "scc = scc_start"
      (* scc is the one we just collected from start *)

      (* Forward direction: All vertices in scc_start are in the same SCC as start *)
      have forward: "\<forall>u. List.member scc_start u \<longrightarrow> in_same_scc graph u start"
        using Cons.prems(2) assms(1) collect_one_scc_sound collect_result downstream_visited
          local.same_scc_unvisited start_in_graph start_unvisited by blast

      (* Backward direction: All vertices in start's SCC are in scc_start *)
      have backward: "\<forall>u. has_vertex graph u \<and> in_same_scc graph u start \<longrightarrow> List.member scc_start u"
        using collect_one_scc_complete[OF Cons.prems(1) start_in_graph _ Cons.prems(2) _
              same_scc_unvisited downstream_visited collect_result]
        by blast

      (* Combine both directions *)
      have "\<forall>u. List.member scc_start u \<longleftrightarrow> (has_vertex graph u \<and> in_same_scc graph u start)"
        using forward backward
        by (metis Cons.prems(1) edge_implies_vertices(1) scc_path_avoiding_vertex start_in_graph)

      (* Therefore scc is a valid SCC *)
      show ?thesis
        using \<open>scc = scc_start\<close> start_in_scc_start
              \<open>\<forall>u. List.member scc_start u \<longleftrightarrow> (has_vertex graph u \<and> in_same_scc graph u start)\<close>
        by blast
    next
      assume "List.member (collect_all_sccs graph new_visited rest) scc"
      (* scc is from the recursive call *)

      (* Use helper lemma to establish all properties for recursive call *)
      have recursive_props:
        "\<forall>w |\<in>| new_visited. has_vertex graph w"
        "\<forall>w. List.member rest w \<longrightarrow> has_vertex graph w"
        "\<forall>v w. v |\<in>| new_visited \<and> reachable graph v w \<longrightarrow> w |\<in>| new_visited"
        "\<forall>v. has_vertex graph v \<and> \<not>(List.member rest v) \<longrightarrow> v |\<in>| new_visited"
        "vertex_list_ordered graph new_visited rest"
        using collect_all_sccs_recursive_properties[OF Cons.prems(1,2,3,4,5,6) start_unvisited collect_result]
        by blast+

      (* Apply IH *)
      show ?thesis
        using Cons.IH[OF Cons.prems(1) recursive_props
              \<open>List.member (collect_all_sccs graph new_visited rest) scc\<close>]
        by simp
    qed
  qed
qed

(* All vertices in the graph that are not already visited appear in some SCC *)
theorem collect_all_sccs_vertices_in_graph:
  assumes "valid_graph graph"
    and "\<forall>w |\<in>| visited. has_vertex graph w"
    and "\<forall>w. List.member vertices w \<longrightarrow> has_vertex graph w"
    and "\<forall>v w. v |\<in>| visited \<and> reachable graph v w \<longrightarrow> w |\<in>| visited"
    and "\<forall>v. has_vertex graph v \<and> \<not>(List.member vertices v) \<longrightarrow> v |\<in>| visited"
    and "vertex_list_ordered graph visited vertices"
    and "has_vertex graph v"
    and "v |\<notin>| visited"
  shows "\<exists>scc. scc \<in> set (collect_all_sccs graph visited vertices) \<and> v \<in> set scc"
  using assms
proof (induction vertices arbitrary: visited v)
  case Nil
  (* If vertices is empty, then by assumption 5, v must be in visited *)
  then show ?case
    by (meson member_rec(2))
next
  case (Cons start rest)
  show ?case
  proof (cases "start |\<in>| visited")
    case True
    (* start is already visited, skip it *)
    have "collect_all_sccs graph visited (start # rest) = collect_all_sccs graph visited rest"
      using True by simp

    have skip_props:
      "\<forall>w. List.member rest w \<longrightarrow> has_vertex graph w"
      "vertex_list_ordered graph visited rest"
      "\<forall>v. has_vertex graph v \<and> \<not>(List.member rest v) \<longrightarrow> v |\<in>| visited"
      using collect_all_sccs_skip_visited_properties[OF Cons.prems(1,2,3,4,5,6) True]
      by blast+

    show ?thesis
      using Cons.IH[OF Cons.prems(1,2) skip_props(1) Cons.prems(4) skip_props(3,2) Cons.prems(7,8)]
      using \<open>collect_all_sccs graph visited (start # rest) = collect_all_sccs graph visited rest\<close>
      by auto
  next
    case False
    (* start is unvisited, so we collect its SCC *)
    have start_in_graph: "has_vertex graph start"
      using Cons.prems(3) by (simp add: member_rec(1))

    have same_scc_unvisited: "\<forall>w. has_vertex graph w \<and> in_same_scc graph w start \<longrightarrow> w |\<notin>| visited"
      using Cons.prems(4) False in_same_scc.simps by blast

    have downstream_visited: "\<forall>w. has_vertex graph w \<and> reachable graph start w \<and>
                                  \<not>(in_same_scc graph w start) \<longrightarrow> w |\<in>| visited"
      using Cons.prems(2,4,5,6) assms(1) downstream_sccs_visited by blast

    obtain scc_start new_visited where collect_result:
      "collect_one_scc graph visited start = (scc_start, new_visited)"
      by (metis surj_pair)

    have collect_decomp: "collect_all_sccs graph visited (start # rest) =
          scc_start # collect_all_sccs graph new_visited rest"
      using False collect_result by simp

    (* Use helper lemma to establish all properties for recursive call *)
    have recursive_props:
      "\<forall>w |\<in>| new_visited. has_vertex graph w"
      "\<forall>w. List.member rest w \<longrightarrow> has_vertex graph w"
      "\<forall>v w. v |\<in>| new_visited \<and> reachable graph v w \<longrightarrow> w |\<in>| new_visited"
      "\<forall>v. has_vertex graph v \<and> \<not>(List.member rest v) \<longrightarrow> v |\<in>| new_visited"
      "vertex_list_ordered graph new_visited rest"
      using collect_all_sccs_recursive_properties[OF Cons.prems(1,2,3,4,5,6) False collect_result]
      by blast+

    show ?thesis
    proof (cases "v |\<in>| new_visited")
      case True
      (* v is in new_visited but was not in visited, so it must be in scc_start *)
      have "new_visited = visited |\<union>| fset_of_list scc_start"
        using collect_one_scc_visited_update[OF Cons.prems(1) start_in_graph Cons.prems(2)
              same_scc_unvisited downstream_visited False collect_result]
        by simp
      then have "v \<in> set scc_start"
        using True Cons.prems(8) by (simp add: fset_of_list_elem)
      then show ?thesis
        using collect_decomp by auto
    next
      case False
      (* v is not in new_visited, so apply IH to the recursive call *)
      have "\<exists>scc. scc \<in> set (collect_all_sccs graph new_visited rest) \<and> v \<in> set scc"
        using Cons.IH[OF Cons.prems(1) recursive_props Cons.prems(7) False]
        by simp
      then show ?thesis
        using collect_decomp by auto
    qed
  qed
qed

(* The vertices in each SCC are distinct *)
theorem collect_all_sccs_distinct:
  assumes "valid_graph graph"
    and "\<forall>w |\<in>| visited. has_vertex graph w"
    and "\<forall>w. List.member vertices w \<longrightarrow> has_vertex graph w"
    and "\<forall>v w. v |\<in>| visited \<and> reachable graph v w \<longrightarrow> w |\<in>| visited"
    and "\<forall>v. has_vertex graph v \<and> \<not>(List.member vertices v) \<longrightarrow> v |\<in>| visited"
    and "vertex_list_ordered graph visited vertices"
    and "scc \<in> set (collect_all_sccs graph visited vertices)"
  shows "distinct scc"
  using assms
proof (induction vertices arbitrary: visited scc)
  case Nil
  then show ?case
    by (metis collect_all_sccs.simps(1) length_greater_0_conv length_pos_if_in_set)
next
  case (Cons start rest)
  show ?case
  proof (cases "start |\<in>| visited")
    case True
    (* start is already visited, skip it *)
    have "collect_all_sccs graph visited (start # rest) = collect_all_sccs graph visited rest"
      using True by simp
    then have "scc \<in> set (collect_all_sccs graph visited rest)"
      using Cons.prems(7) by auto

    have skip_props:
      "\<forall>w. List.member rest w \<longrightarrow> has_vertex graph w"
      "vertex_list_ordered graph visited rest"
      "\<forall>v. has_vertex graph v \<and> \<not>(List.member rest v) \<longrightarrow> v |\<in>| visited"
      using collect_all_sccs_skip_visited_properties[OF Cons.prems(1,2,3,4,5,6) True]
      by blast+

    show ?thesis
      using Cons.IH Cons.prems(2,4) \<open>scc \<in> set (collect_all_sccs graph visited rest)\<close> assms(1)
        skip_props(1,2,3) by blast
  next
    case False
    (* start is unvisited, so we collect its SCC *)
    have start_in_graph: "has_vertex graph start"
      using Cons.prems(3) by (simp add: member_rec(1))

    have same_scc_unvisited: "\<forall>w. has_vertex graph w \<and> in_same_scc graph w start \<longrightarrow> w |\<notin>| visited"
      using Cons.prems(4) False in_same_scc.simps by blast

    have downstream_visited: "\<forall>w. has_vertex graph w \<and> reachable graph start w \<and>
                                  \<not>(in_same_scc graph w start) \<longrightarrow> w |\<in>| visited"
      using Cons.prems(2,4,5,6) assms(1) downstream_sccs_visited by blast

    obtain scc_start new_visited where collect_result:
      "collect_one_scc graph visited start = (scc_start, new_visited)"
      by (metis surj_pair)

    have "collect_all_sccs graph visited (start # rest) =
          scc_start # collect_all_sccs graph new_visited rest"
      using False collect_result by simp

    then have "scc = scc_start \<or> scc \<in> set (collect_all_sccs graph new_visited rest)"
      using Cons.prems(7) by auto

    then show ?thesis
    proof
      assume "scc = scc_start"
      (* scc is the one we just collected from start, use collect_one_scc_distinct *)
      show ?thesis
        using \<open>scc = scc_start\<close> collect_one_scc_distinct[OF Cons.prems(1) start_in_graph
              Cons.prems(2) same_scc_unvisited downstream_visited False collect_result]
        by simp
    next
      assume "scc \<in> set (collect_all_sccs graph new_visited rest)"
      (* scc is from the recursive call *)

      (* Use helper lemma to establish all properties for recursive call *)
      have recursive_props:
        "\<forall>w |\<in>| new_visited. has_vertex graph w"
        "\<forall>w. List.member rest w \<longrightarrow> has_vertex graph w"
        "\<forall>v w. v |\<in>| new_visited \<and> reachable graph v w \<longrightarrow> w |\<in>| new_visited"
        "\<forall>v. has_vertex graph v \<and> \<not>(List.member rest v) \<longrightarrow> v |\<in>| new_visited"
        "vertex_list_ordered graph new_visited rest"
        using collect_all_sccs_recursive_properties[OF Cons.prems(1,2,3,4,5,6) False collect_result]
        by blast+

      show ?thesis
        using Cons.IH[OF Cons.prems(1) recursive_props
              \<open>scc \<in> set (collect_all_sccs graph new_visited rest)\<close>]
        by simp
    qed
  qed
qed

(* There is only one copy of each SCC in the output *)
(* Note: this is also a consequence of the reverse topological order property (next theorem),
   as two repeated SCCs would not be topologically orderable, but here we prove it directly
   by induction on the vertices list. *)
theorem collect_all_sccs_distinct_list:
  assumes "valid_graph graph"
    and "\<forall>w |\<in>| visited. has_vertex graph w"
    and "\<forall>w. List.member vertices w \<longrightarrow> has_vertex graph w"
    and "\<forall>v w. v |\<in>| visited \<and> reachable graph v w \<longrightarrow> w |\<in>| visited"
    and "\<forall>v. has_vertex graph v \<and> \<not>(List.member vertices v) \<longrightarrow> v |\<in>| visited"
    and "vertex_list_ordered graph visited vertices"
  shows "distinct (map set (collect_all_sccs graph visited vertices))"
  using assms
proof (induction vertices arbitrary: visited)
  case Nil
  then show ?case
    by (metis collect_all_sccs.simps(1) distinct.simps(1) list.map_disc_iff)
next
  case (Cons start rest)
  show ?case
  proof (cases "start |\<in>| visited")
    case True
    (* start is already visited, skip it *)
    have "collect_all_sccs graph visited (start # rest) = collect_all_sccs graph visited rest"
      using True by simp

    have skip_props:
      "\<forall>w. List.member rest w \<longrightarrow> has_vertex graph w"
      "vertex_list_ordered graph visited rest"
      "\<forall>v. has_vertex graph v \<and> \<not>(List.member rest v) \<longrightarrow> v |\<in>| visited"
      using collect_all_sccs_skip_visited_properties[OF Cons.prems(1,2,3,4,5,6) True]
      by blast+

    show ?thesis
      using Cons.IH[OF Cons.prems(1,2) skip_props(1) Cons.prems(4) skip_props(3,2)]
      using `collect_all_sccs graph visited (start # rest) = collect_all_sccs graph visited rest`
      by simp
  next
    case False
    (* start is unvisited, so we collect its SCC *)
    have start_in_graph: "has_vertex graph start"
      using Cons.prems(3) by (simp add: member_rec(1))

    have same_scc_unvisited: "\<forall>w. has_vertex graph w \<and> in_same_scc graph w start \<longrightarrow> w |\<notin>| visited"
      using Cons.prems(4) False in_same_scc.simps by blast

    have downstream_visited: "\<forall>w. has_vertex graph w \<and> reachable graph start w \<and>
                                  \<not>(in_same_scc graph w start) \<longrightarrow> w |\<in>| visited"
      using Cons.prems(2,4,5,6) assms(1) downstream_sccs_visited by blast

    obtain scc_start new_visited where collect_result:
      "collect_one_scc graph visited start = (scc_start, new_visited)"
      by (metis surj_pair)

    have "collect_all_sccs graph visited (start # rest) =
          scc_start # collect_all_sccs graph new_visited rest"
      using False collect_result by simp

    (* Use helper lemma to establish all properties for recursive call *)
    have recursive_props:
      "\<forall>w |\<in>| new_visited. has_vertex graph w"
      "\<forall>w. List.member rest w \<longrightarrow> has_vertex graph w"
      "\<forall>v w. v |\<in>| new_visited \<and> reachable graph v w \<longrightarrow> w |\<in>| new_visited"
      "\<forall>v. has_vertex graph v \<and> \<not>(List.member rest v) \<longrightarrow> v |\<in>| new_visited"
      "vertex_list_ordered graph new_visited rest"
      using collect_all_sccs_recursive_properties[OF Cons.prems(1,2,3,4,5,6) False collect_result]
      by blast+

    (* By IH, the recursive list is distinct *)
    have IH: "distinct (map set (collect_all_sccs graph new_visited rest))"
      using Cons.IH[OF Cons.prems(1) recursive_props]
      by simp

    (* Now show that set scc_start is not in the recursive list *)
    have "set scc_start \<notin> set (map set (collect_all_sccs graph new_visited rest))"
    proof (rule ccontr)
      assume "\<not> set scc_start \<notin> set (map set (collect_all_sccs graph new_visited rest))"
      then have hyp: "set scc_start \<in> set (map set (collect_all_sccs graph new_visited rest))" by simp

      (* All vertices in scc_start were not in new_visited when the recursive list was collected *)
      have "\<forall>v \<in> set scc_start. v |\<notin>| new_visited"
        using collect_all_sccs_vertices_were_unvisited[OF Cons.prems(1) recursive_props]
        using hyp by blast

      (* But start is in scc_start *)
      have "start \<in> set scc_start"
        using collect_one_scc_complete[OF Cons.prems(1) start_in_graph start_in_graph
              Cons.prems(2) _ same_scc_unvisited downstream_visited collect_result]
        using in_same_scc_refl start_in_graph
        by (metis in_set_member)

      (* And start is in new_visited *)
      have "new_visited = visited |\<union>| fset_of_list scc_start"
        using collect_one_scc_visited_update[OF Cons.prems(1) start_in_graph Cons.prems(2)
              same_scc_unvisited downstream_visited False collect_result]
        by simp
      then have "start |\<in>| new_visited"
        using `start \<in> set scc_start` by (simp add: fset_of_list_elem)

      (* This contradicts the fact that all vertices in scc_start were not in new_visited *)
      then show False
        using `\<forall>v \<in> set scc_start. v |\<notin>| new_visited` `start \<in> set scc_start` by blast
    qed

    then show ?thesis
      using `collect_all_sccs graph visited (start # rest) =
             scc_start # collect_all_sccs graph new_visited rest` IH
      by simp
  qed
qed

(* Definition of reverse topological ordering.
   If SCC at index i appears before SCC at index j (i < j) in the output list,
   then there's no edge from SCC_i to SCC_j. *)
definition sccs_reverse_topologically_ordered :: "('a::linorder) Graph \<Rightarrow> 'a list list \<Rightarrow> bool" where
  "sccs_reverse_topologically_ordered graph sccs \<equiv>
    (\<forall>i j. i < j \<and> j < length sccs \<longrightarrow>
           (\<forall>u v. u \<in> set (sccs ! i) \<and> v \<in> set (sccs ! j) \<longrightarrow>
                  \<not>has_edge graph u v))"

(* Theorem: collect_all_sccs produces SCCs in reverse topological order. *)
theorem collect_all_sccs_reverse_topologically_ordered:
  assumes "valid_graph graph"
    and "\<forall>w |\<in>| visited. has_vertex graph w"
    and "\<forall>w. List.member vertices w \<longrightarrow> has_vertex graph w"
    and "\<forall>v w. v |\<in>| visited \<and> reachable graph v w \<longrightarrow> w |\<in>| visited"
    and "\<forall>v. has_vertex graph v \<and> \<not>(List.member vertices v) \<longrightarrow> v |\<in>| visited"
    and "vertex_list_ordered graph visited vertices"
  shows "sccs_reverse_topologically_ordered graph (collect_all_sccs graph visited vertices)"
  using assms
proof (induction vertices arbitrary: visited)
  case Nil
  (* Base case: empty list is trivially ordered *)
  then show ?case
    unfolding sccs_reverse_topologically_ordered_def
    by (metis bot.extremum_strict bot_nat_def collect_all_sccs.simps(1) list.size(3))
next
  case (Cons start rest)
  show ?case
  proof (cases "start |\<in>| visited")
    case True
    (* Case 1: start already visited, skip it *)
    have "collect_all_sccs graph visited (start # rest) = collect_all_sccs graph visited rest"
      using True by simp

    (* By IH, the result is reverse topologically ordered *)
    have skip_props:
      "\<forall>w. List.member rest w \<longrightarrow> has_vertex graph w"
      "vertex_list_ordered graph visited rest"
      "\<forall>v. has_vertex graph v \<and> \<not>(List.member rest v) \<longrightarrow> v |\<in>| visited"
      using collect_all_sccs_skip_visited_properties[OF Cons.prems(1,2,3,4,5,6) True]
      by blast+

    show ?thesis
      using Cons.IH[OF Cons.prems(1,2) skip_props(1) Cons.prems(4) skip_props(3,2)]
      using `collect_all_sccs graph visited (start # rest) = collect_all_sccs graph visited rest`
      by simp

  next
    case False
    (* Case 2: start unvisited, collect its SCC *)
    obtain scc_start new_visited where collect_result:
      "collect_one_scc graph visited start = (scc_start, new_visited)"
      by (metis surj_pair)

    have step_def: "collect_all_sccs graph visited (start # rest) =
          scc_start # collect_all_sccs graph new_visited rest"
      using False collect_result by simp

    (* Get properties for recursive call *)
    have recursive_props:
      "\<forall>w |\<in>| new_visited. has_vertex graph w"
      "\<forall>w. List.member rest w \<longrightarrow> has_vertex graph w"
      "\<forall>v w. v |\<in>| new_visited \<and> reachable graph v w \<longrightarrow> w |\<in>| new_visited"
      "\<forall>v. has_vertex graph v \<and> \<not>(List.member rest v) \<longrightarrow> v |\<in>| new_visited"
      "vertex_list_ordered graph new_visited rest"
      using collect_all_sccs_recursive_properties[OF Cons.prems(1,2,3,4,5,6) False collect_result]
      by blast+

    (* By IH, the recursive result is reverse topologically ordered *)
    have IH: "sccs_reverse_topologically_ordered graph (collect_all_sccs graph new_visited rest)"
      using Cons.IH[OF Cons.prems(1) recursive_props]
      by simp

    (* Need to show: scc_start # collect_all_sccs graph new_visited rest is reverse 
       topologically ordered *)
    (* This requires showing:
       1. The recursive list is ordered (by IH)
       2. No edges from scc_start to any SCC in the recursive list *)

    show ?thesis
      unfolding sccs_reverse_topologically_ordered_def
    proof (intro allI impI)
      fix i j u v
      assume indices: "i < j 
          \<and> j < length (collect_all_sccs graph visited (start # rest))"
      assume uv: "u \<in> set (collect_all_sccs graph visited (start # rest) ! i)
          \<and> v \<in> set (collect_all_sccs graph visited (start # rest) ! j)"

      show "\<not>has_edge graph u v"
      proof (cases i)
        case 0
        (* i = 0, so scc_i is scc_start *)
        then have "u \<in> set scc_start" using uv step_def by auto
        (* j > 0, so scc_j is from the recursive call *)
        then have "j > 0" using indices by auto
        then have "v \<in> set ((collect_all_sccs graph new_visited rest) ! (j - 1))"
          using step_def uv by auto

        (* Key: v was not in new_visited when the recursive call was made *)
        have "v |\<notin>| new_visited"
        proof -
          have "v \<in> set ((collect_all_sccs graph new_visited rest) ! (j - 1))"
            using `v \<in> set ((collect_all_sccs graph new_visited rest) ! (j - 1))` .
          moreover have "(collect_all_sccs graph new_visited rest) ! (j - 1)
                         \<in> set (collect_all_sccs graph new_visited rest)"
            using `j > 0` indices step_def
            by force
          ultimately have "\<exists>scc. scc \<in> set (collect_all_sccs graph new_visited rest) \<and> v \<in> set scc"
            by blast
          then show ?thesis
            using collect_all_sccs_vertices_were_unvisited[OF Cons.prems(1) recursive_props]
            by auto
        qed

        (* But u is in scc_start, so u \<in> new_visited *)
        have "u |\<in>| new_visited"
        proof -
          have "u \<in> set scc_start" using `u \<in> set scc_start` .

          (* Establish the preconditions for collect_one_scc_visited_update *)
          have start_in_graph: "has_vertex graph start"
            using Cons.prems(3) by (simp add: member_rec(1))
          have same_scc_unvisited: "\<forall>w. has_vertex graph w \<and> in_same_scc graph w start \<longrightarrow> w |\<notin>| visited"
            using False Cons.prems(4) in_same_scc.simps by blast
          have downstream_visited: "\<forall>w. has_vertex graph w \<and> reachable graph start w \<and> \<not>in_same_scc graph w start \<longrightarrow> w |\<in>| visited"
            using Cons.prems(2,4,5,6) assms(1) downstream_sccs_visited by blast

          have "new_visited = visited |\<union>| fset_of_list scc_start"
            using collect_one_scc_visited_update[OF Cons.prems(1) start_in_graph Cons.prems(2)
                  same_scc_unvisited downstream_visited False collect_result]
            by simp
          then show ?thesis
            using `u \<in> set scc_start` by (simp add: fset_of_list_elem)
        qed

        (* If there were an edge u \<rightarrow> v, then v would be reachable from u *)
        (* And since u \<in> new_visited and new_visited is closed under reachability,
           v would be in new_visited, contradicting v \<notin> new_visited *)
        show ?thesis
        proof (rule ccontr)
          assume "\<not>\<not>has_edge graph u v"
          then have "has_edge graph u v" by simp
          then have "reachable graph u v"
            by (meson `u |\<in>| new_visited` recursive_props(1)
                reachable.reachable_refl reachable.reachable_step)
          then have "v |\<in>| new_visited"
            using `u |\<in>| new_visited` recursive_props(3) by blast
          then show False
            using `v |\<notin>| new_visited` by simp
        qed

      next
        case (Suc i')
        (* Both i and j are > 0, so both SCCs are from the recursive call *)
        then have "j > 0" using indices by simp
        then have "u \<in> set ((collect_all_sccs graph new_visited rest) ! i')"
              and "v \<in> set ((collect_all_sccs graph new_visited rest) ! (j - 1))"
          using Suc step_def uv by auto+

        (* This follows from IH on the recursive list *)
        have "i' < j - 1" using Suc indices
          by linarith
        have "j - 1 < length (collect_all_sccs graph new_visited rest)"
          using indices step_def by fastforce

        show ?thesis
          using IH unfolding sccs_reverse_topologically_ordered_def
          using `i' < j - 1` `j - 1 < length (collect_all_sccs graph new_visited rest)`
          using `u \<in> set ((collect_all_sccs graph new_visited rest) ! i')`
          using `v \<in> set ((collect_all_sccs graph new_visited rest) ! (j - 1))`
          by blast
      qed
    qed
  qed
qed

end
