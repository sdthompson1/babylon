theory Kosaraju1
  imports Graphs
begin

(* Kosaraju's algorithm for finding strongly connected components: Part 1. *)

(*-----------------------------------------------------------------------------*)
(* Depth first search - for first pass of Kosaraju's algorithm *)
(*-----------------------------------------------------------------------------*)

(* Stack frame for iterative DFS - tracks whether we're before or after visiting neighbors *)
datatype ('a::linorder) dfs_frame = PreVisit 'a | PostVisit 'a

(* DFS state *)
record ('a::linorder) dfs_state =
  dfs_visited :: "'a fset"
  dfs_finish_order :: "'a list"
  dfs_stack :: "'a dfs_frame list"

fun initial_dfs_state :: "('a::linorder) list \<Rightarrow> 'a dfs_state" where
  "initial_dfs_state vertices = 
    \<lparr> dfs_visited = {||}, 
      dfs_finish_order = [],
      dfs_stack = map PreVisit vertices \<rparr>"

(* Single step of DFS *)
fun dfs_step :: "('a::linorder) Graph \<Rightarrow> 'a dfs_state \<Rightarrow> 'a dfs_state" where
  "dfs_step graph state =
    (case dfs_stack state of
      [] \<Rightarrow> state
    | PreVisit v # rest \<Rightarrow>
        if v |\<in>| dfs_visited state then
          state \<lparr> dfs_stack := rest \<rparr>
        else
          (case fmlookup graph v of
              None \<Rightarrow> state \<lparr> dfs_stack := [] \<rparr>
            | Some neighbors \<Rightarrow>
                state \<lparr> dfs_visited := finsert v (dfs_visited state),
                        dfs_stack := map PreVisit neighbors @ [PostVisit v] @ rest \<rparr>)
    | PostVisit v # rest \<Rightarrow>
        state \<lparr> dfs_finish_order := v # (dfs_finish_order state),
                dfs_stack := rest \<rparr>
    )"

(*-----------------------------------------------------------------------------*)
(* Basic validity property for DFS state *)
(*-----------------------------------------------------------------------------*)

(* Helper predicates for DFS state validity *)

(* All frames on the stack refer to vertices in the graph *)
fun dfs_stack_vertices_valid :: "('a::linorder) Graph \<Rightarrow> 'a dfs_frame list \<Rightarrow> bool" where
  "dfs_stack_vertices_valid graph stack \<longleftrightarrow>
    (\<forall>frame. List.member stack frame \<longrightarrow>
      (case frame of
        PreVisit v \<Rightarrow> has_vertex graph v
      | PostVisit v \<Rightarrow> has_vertex graph v))"

(* PostVisit nodes on stack correspond to visited vertices *)
fun dfs_post_visit_visited :: "('a::linorder) fset \<Rightarrow> 'a dfs_frame list \<Rightarrow> bool" where
  "dfs_post_visit_visited visited stack \<longleftrightarrow>
    (\<forall>v. List.member stack (PostVisit v) \<longrightarrow> v |\<in>| visited)"

(* PostVisit frames are distinct on the stack *)
fun dfs_post_visit_distinct :: "('a::linorder) dfs_frame list \<Rightarrow> bool" where
  "dfs_post_visit_distinct [] \<longleftrightarrow> True"
| "dfs_post_visit_distinct (PreVisit v # rest) \<longleftrightarrow> dfs_post_visit_distinct rest"
| "dfs_post_visit_distinct (PostVisit v # rest) \<longleftrightarrow>
    \<not> List.member rest (PostVisit v) \<and> dfs_post_visit_distinct rest"

(* Visited vertices are either finished or have PostVisit on stack *)
fun dfs_visited_accounted :: "('a::linorder) fset \<Rightarrow> 'a list \<Rightarrow> 'a dfs_frame list \<Rightarrow> bool" where
  "dfs_visited_accounted visited finish_order stack \<longleftrightarrow>
    (\<forall>v. v |\<in>| visited \<longrightarrow>
      List.member finish_order v \<or> List.member stack (PostVisit v))"

(* Main predicate: DFS state is valid with respect to a graph *)
(* This is preserved by dfs_step *)
fun dfs_state_valid :: "('a::linorder) Graph \<Rightarrow> 'a dfs_state \<Rightarrow> bool" where
  "dfs_state_valid graph state \<longleftrightarrow>
    valid_graph graph \<and>
    dfs_stack_vertices_valid graph (dfs_stack state) \<and>
    (\<forall>v. v |\<in>| dfs_visited state \<longrightarrow> has_vertex graph v) \<and>
    (\<forall>v. List.member (dfs_finish_order state) v \<longrightarrow> has_vertex graph v) \<and>
    dfs_post_visit_visited (dfs_visited state) (dfs_stack state) \<and>
    dfs_post_visit_distinct (dfs_stack state) \<and>
    distinct (dfs_finish_order state) \<and>
    dfs_visited_accounted (dfs_visited state) (dfs_finish_order state) (dfs_stack state) \<and>
    (\<forall>v. List.member (dfs_finish_order state) v \<longrightarrow> v |\<in>| dfs_visited state) \<and>
    (\<forall>v. List.member (dfs_finish_order state) v \<longrightarrow> \<not> List.member (dfs_stack state) (PostVisit v))"

(* Some lemmas *)

(* Expansion of dfs_step from valid state when unvisited PreVisit u on stack *)
lemma dfs_step_previsit_expand: 
  assumes "dfs_state_valid graph state"
    and "dfs_stack state = PreVisit u # rest"
    and "u |\<notin>| dfs_visited state"
    and "neighbors = the (fmlookup graph u)"
  shows "dfs_step graph state = state \<lparr> dfs_visited := finsert u (dfs_visited state),
            dfs_stack := map PreVisit neighbors @ [PostVisit u] @ rest \<rparr>"
proof -
  have "has_vertex graph u" using assms(1,2)
    by (metis dfs_frame.simps(5) dfs_stack_vertices_valid.elims(2) dfs_state_valid.simps
        member_rec(1))
  hence "fmlookup graph u \<noteq> None" 
    by auto
  thus ?thesis using assms(2,3,4)
    by (simp, cases "fmlookup graph u", auto)
qed

(* The possible outcomes of dfs_step on a valid state with a non-empty stack *)
lemma dfs_step_cases:
  assumes "dfs_state_valid graph state"
    and "dfs_stack state \<noteq> []"
  obtains (skip) v rest where "dfs_stack state = PreVisit v # rest" "v |\<in>| dfs_visited state"
      "dfs_step graph state = state \<lparr> dfs_stack := rest \<rparr>"
  | (expand) v rest where "dfs_stack state = PreVisit v # rest" "v |\<notin>| dfs_visited state"
      "has_vertex graph v"
      "dfs_step graph state =
         state \<lparr> dfs_visited := finsert v (dfs_visited state),
                 dfs_stack := map PreVisit (the (fmlookup graph v)) @ [PostVisit v] @ rest \<rparr>"
  | (finish) v rest where "dfs_stack state = PostVisit v # rest"
      "dfs_step graph state =
         state \<lparr> dfs_finish_order := v # dfs_finish_order state, dfs_stack := rest \<rparr>"
proof -
  obtain frame rest where stack: "dfs_stack state = frame # rest"
    using assms(2) by (cases "dfs_stack state") auto
  show ?thesis
  proof (cases frame)
    case (PreVisit v)
    then have stack': "dfs_stack state = PreVisit v # rest"
      using stack by simp
    show ?thesis
    proof (cases "v |\<in>| dfs_visited state")
      case visited: True
      show ?thesis
        by (rule skip[OF stack' visited]) (simp add: stack' visited)
    next
      case unvisited: False
      have "has_vertex graph v"
        using assms(1) stack'
        by (metis dfs_frame.simps(5) dfs_stack_vertices_valid.elims(2) dfs_state_valid.simps
            member_rec(1))
      then show ?thesis
        by (rule expand[OF stack' unvisited _ dfs_step_previsit_expand[OF assms(1) stack' unvisited refl]])
    qed
  next
    case (PostVisit v)
    then have stack': "dfs_stack state = PostVisit v # rest"
      using stack by simp
    show ?thesis
      by (rule finish[OF stack']) (simp add: stack')
  qed
qed

(* Helper lemma: map PreVisit preserves vertices validity *)
lemma map_PreVisit_valid:
  assumes "\<forall>v. List.member neighbors v \<longrightarrow> has_vertex graph v"
  shows "dfs_stack_vertices_valid graph (map PreVisit neighbors)"
  using assms
  by (induction neighbors) (auto simp: member_rec)

(* Helper lemma: extending stack with map PreVisit and one PostVisit preserves distinctness *)
lemma dfs_post_visit_distinct_extend:
  assumes "dfs_post_visit_distinct stack"
    and "\<not> List.member stack (PostVisit v)"
  shows "dfs_post_visit_distinct (map PreVisit neighbors @ [PostVisit v] @ stack)"
  using assms
  by (induction neighbors) simp_all

(* Lemma: dfs_step preserves dfs_state_valid *)
lemma dfs_step_preserves_validity:
  assumes valid: "dfs_state_valid graph state"
    and non_empty: "dfs_stack state \<noteq> []"
  shows "dfs_state_valid graph (dfs_step graph state)"
proof -
  (* Note: giving the whole (unfolded) invariant to simp/auto is slow and risks loops,
     so each conjunct of the new invariant is proved from just the facts it needs *)
  have valid_g: "valid_graph graph"
    and stack_vertices: "dfs_stack_vertices_valid graph (dfs_stack state)"
    and visited_vertices: "\<forall>v. v |\<in>| dfs_visited state \<longrightarrow> has_vertex graph v"
    and finish_vertices: "\<forall>v. List.member (dfs_finish_order state) v \<longrightarrow> has_vertex graph v"
    and post_visited: "dfs_post_visit_visited (dfs_visited state) (dfs_stack state)"
    and post_distinct: "dfs_post_visit_distinct (dfs_stack state)"
    and finish_distinct: "distinct (dfs_finish_order state)"
    and accounted: "dfs_visited_accounted (dfs_visited state) (dfs_finish_order state)
                      (dfs_stack state)"
    and finish_visited: "\<forall>v. List.member (dfs_finish_order state) v \<longrightarrow> v |\<in>| dfs_visited state"
    and finish_not_post: "\<forall>v. List.member (dfs_finish_order state) v \<longrightarrow>
                              \<not> List.member (dfs_stack state) (PostVisit v)"
    using valid unfolding dfs_state_valid.simps by blast+

  show ?thesis
  proof (cases rule: dfs_step_cases[OF valid non_empty, case_names skip expand finish])
    case (skip u rest)
    (* The visited PreVisit u is popped *)
    have new: "dfs_visited (dfs_step graph state) = dfs_visited state"
      "dfs_finish_order (dfs_step graph state) = dfs_finish_order state"
      "dfs_stack (dfs_step graph state) = rest"
      using skip(3) by simp_all
    have "dfs_stack_vertices_valid graph rest"
      using stack_vertices unfolding skip(1) by (auto simp: member_rec(1))
    moreover have "dfs_post_visit_visited (dfs_visited state) rest"
      using post_visited unfolding skip(1) by (auto simp: member_rec(1))
    moreover have "dfs_post_visit_distinct rest"
      using post_distinct unfolding skip(1) by simp
    moreover have "dfs_visited_accounted (dfs_visited state) (dfs_finish_order state) rest"
      using accounted unfolding skip(1) by (auto simp: member_rec(1))
    moreover have "\<forall>v. List.member (dfs_finish_order state) v \<longrightarrow> \<not> List.member rest (PostVisit v)"
      using finish_not_post unfolding skip(1) by (auto simp: member_rec(1))
    ultimately show ?thesis
      unfolding dfs_state_valid.simps new
      using valid_g visited_vertices finish_vertices finish_distinct finish_visited by blast
  next
    case (finish u rest)
    (* PostVisit u is popped, and u is added to the finish order *)
    have new: "dfs_visited (dfs_step graph state) = dfs_visited state"
      "dfs_finish_order (dfs_step graph state) = u # dfs_finish_order state"
      "dfs_stack (dfs_step graph state) = rest"
      using finish(2) by simp_all
    have u_visited: "u |\<in>| dfs_visited state"
      using post_visited unfolding finish(1) by (simp add: member_rec(1))
    have u_unfinished: "\<not> List.member (dfs_finish_order state) u"
      using finish_not_post unfolding finish(1) by (auto simp: member_rec(1))
    have u_not_in_rest: "\<not> List.member rest (PostVisit u)"
      and rest_distinct: "dfs_post_visit_distinct rest"
      using post_distinct unfolding finish(1) by simp_all
    have "dfs_stack_vertices_valid graph rest"
      using stack_vertices unfolding finish(1) by (auto simp: member_rec(1))
    moreover have "\<forall>v. List.member (u # dfs_finish_order state) v \<longrightarrow> has_vertex graph v"
      using finish_vertices visited_vertices u_visited by (auto simp: member_rec(1))
    moreover have "dfs_post_visit_visited (dfs_visited state) rest"
      using post_visited unfolding finish(1) by (auto simp: member_rec(1))
    moreover have "distinct (u # dfs_finish_order state)"
      using finish_distinct u_unfinished by (simp add: in_set_member)
    moreover have "dfs_visited_accounted (dfs_visited state) (u # dfs_finish_order state) rest"
      using accounted unfolding finish(1) by (auto simp: member_rec(1))
    moreover have "\<forall>v. List.member (u # dfs_finish_order state) v \<longrightarrow> v |\<in>| dfs_visited state"
      using finish_visited u_visited by (auto simp: member_rec(1))
    moreover have "\<forall>v. List.member (u # dfs_finish_order state) v \<longrightarrow>
                       \<not> List.member rest (PostVisit v)"
      using finish_not_post u_not_in_rest unfolding finish(1) by (auto simp: member_rec(1))
    ultimately show ?thesis
      unfolding dfs_state_valid.simps new
      using valid_g visited_vertices rest_distinct by blast
  next
    case (expand u rest)
    (* PreVisit u is replaced by u's successors and PostVisit u, and u becomes visited *)
    let ?ns = "the (fmlookup graph u)"
    let ?new_stack = "map PreVisit ?ns @ [PostVisit u] @ rest"
    have new: "dfs_visited (dfs_step graph state) = finsert u (dfs_visited state)"
      "dfs_finish_order (dfs_step graph state) = dfs_finish_order state"
      "dfs_stack (dfs_step graph state) = ?new_stack"
      using expand(4) by simp_all
    have ns_vertices: "\<forall>w. List.member ?ns w \<longrightarrow> has_vertex graph w"
      using valid_g has_edge_member_conv[OF expand(3)] expand(3)
      unfolding valid_graph.simps by blast
    have u_not_in_rest: "\<not> List.member rest (PostVisit u)"
      using post_visited expand(2) unfolding expand(1) by (auto simp: member_rec(1))
    have rest_distinct: "dfs_post_visit_distinct rest"
      using post_distinct unfolding expand(1) by simp
    have "dfs_stack_vertices_valid graph ?new_stack"
      using stack_vertices ns_vertices expand(3) unfolding expand(1) by (auto simp: member_def)
    moreover have "\<forall>v. v |\<in>| finsert u (dfs_visited state) \<longrightarrow> has_vertex graph v"
      using visited_vertices expand(3) by auto
    moreover have "dfs_post_visit_visited (finsert u (dfs_visited state)) ?new_stack"
      using post_visited unfolding expand(1) by (auto simp: member_def)
    moreover have "dfs_post_visit_distinct ?new_stack"
      by (rule dfs_post_visit_distinct_extend[OF rest_distinct u_not_in_rest])
    moreover have "dfs_visited_accounted (finsert u (dfs_visited state)) (dfs_finish_order state)
                     ?new_stack"
      using accounted unfolding expand(1) by (auto simp: member_def)
    moreover have "\<forall>v. List.member (dfs_finish_order state) v \<longrightarrow>
                       v |\<in>| finsert u (dfs_visited state)"
      using finish_visited by auto
    (* A finished vertex is visited, so it is not u; and it had no PostVisit frame before *)
    moreover have "\<forall>v. List.member (dfs_finish_order state) v \<longrightarrow>
                       \<not> List.member ?new_stack (PostVisit v)"
      using finish_not_post finish_visited expand(2) unfolding expand(1)
      by (auto simp: member_def)
    ultimately show ?thesis
      unfolding dfs_state_valid.simps new
      using valid_g finish_vertices finish_distinct by blast
  qed
qed

(*-----------------------------------------------------------------------------*)
(* Additional definitions *)
(*-----------------------------------------------------------------------------*)

(* Predicate that says that a path from a to b, consisting entirely of unvisited
   vertices, exists. *)
inductive unvisited_path :: "('a::linorder) Graph \<Rightarrow> 'a fset \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  for graph visited where
  unvisited_refl: "has_vertex graph u \<Longrightarrow> u |\<notin>| visited \<Longrightarrow> unvisited_path graph visited u u"
| unvisited_step: "u |\<notin>| visited \<Longrightarrow> has_edge graph u w \<Longrightarrow>
                    unvisited_path graph visited w v \<Longrightarrow>
                    unvisited_path graph visited u v"

(* Helper function to find index of element in list *)
fun index_of :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "index_of x [] = 0"
| "index_of x (y # ys) = (if x = y then 0 else Suc (index_of x ys))"

(* Definition: If the stack is prefix @ PostVisit x # rest, then
   will_finish_before_me(state, prefix) =
     { all vertices currently finished } \<union>
     { all z such that there is a PostVisit z in the prefix } \<union>
     { all z such that there is some PreVisit w in the prefix
       with an unvisited path from w to z } *)
fun will_finish_before_me :: "('a::linorder) Graph \<Rightarrow> 'a dfs_state \<Rightarrow> 'a dfs_frame list \<Rightarrow> 'a set" where
  "will_finish_before_me graph state prefix =
    set (dfs_finish_order state) \<union>
    {z. PostVisit z \<in> set prefix} \<union>
    {z. \<exists>w. PreVisit w \<in> set prefix \<and> unvisited_path graph (dfs_visited state) w z}"


(*-----------------------------------------------------------------------------*)
(* Additional invariants preserved by DFS step *)
(*-----------------------------------------------------------------------------*)

(* PreVisit ordering property: if PreVisit u appears before PostVisit v on the stack,
   then v reaches u *)
fun dfs_previsit_ordered :: "('a::linorder) Graph \<Rightarrow> 'a dfs_state \<Rightarrow> bool" where
  "dfs_previsit_ordered graph state \<longleftrightarrow>
    (\<forall>prefix v rest u. dfs_stack state = prefix @ PostVisit v # rest \<and>
                       PreVisit u \<in> set prefix \<longrightarrow>
                       reachable graph v u)"

(* PostVisit ordering property: if PostVisit u appears before PostVisit v on the stack,
   then v reaches u *)
fun dfs_postvisit_ordered :: "('a::linorder) Graph \<Rightarrow> 'a dfs_state \<Rightarrow> bool" where
  "dfs_postvisit_ordered graph state \<longleftrightarrow>
    (\<forall>prefix v rest u. dfs_stack state = prefix @ PostVisit v # rest \<and>
                       PostVisit u \<in> set prefix \<longrightarrow>
                       reachable graph v u)"

(* Finish Order Invariant: For each edge c \<rightarrow> d where c, d are in different SCCs,
   at least one of the following is true:
    1) All vertices in same SCC as either c or d are unvisited.
    2) All vertices in same SCC as d are finished, and at least one vertex in
       same SCC as c is unfinished.
    3) All vertices in same SCC as either c or d are finished, and the finish list
       obeys the following property: The first vertex from c's SCC in the finish order
       comes before all vertices from d's SCC in the finish order.
    4) At least one vertex in c's SCC is visited (but not finished),
       and its WillFinishBeforeMe set contains everything in d's SCC.
    5) At least one vertex "x" in d's SCC is visited (but not finished),
       and its WillFinishBeforeMe set contains everything in d's SCC,
       apart from x itself; also, not everything in c's SCC is finished yet.
*)
fun finish_order_1 :: "('a::linorder) Graph \<Rightarrow> 'a dfs_state \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "finish_order_1 graph state c d =
    (\<forall> v. has_vertex graph v \<and> (in_same_scc graph v c \<or> in_same_scc graph v d) \<longrightarrow>
            v |\<notin>| (dfs_visited state))"

fun finish_order_2 :: "('a::linorder) Graph \<Rightarrow> 'a dfs_state \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "finish_order_2 graph state c d =
    ((\<forall>v. has_vertex graph v \<and> in_same_scc graph v d \<longrightarrow>
            List.member (dfs_finish_order state) v) \<and>
     (\<exists>v. has_vertex graph v \<and> in_same_scc graph v c \<and>
            \<not>List.member (dfs_finish_order state) v))"

fun finish_order_3 :: "('a::linorder) Graph \<Rightarrow> 'a dfs_state \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "finish_order_3 graph state c d \<longleftrightarrow>
    (\<forall>v. has_vertex graph v \<and> (in_same_scc graph v c \<or> in_same_scc graph v d) \<longrightarrow>
            List.member (dfs_finish_order state) v)
  \<and> (\<exists>v_c. has_vertex graph v_c \<and> in_same_scc graph v_c c \<and>
      (\<forall>v_d. has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
        index_of v_c (dfs_finish_order state) < index_of v_d (dfs_finish_order state)))"

fun finish_order_4 :: "('a::linorder) Graph \<Rightarrow> 'a dfs_state \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "finish_order_4 graph state c d =
    (\<exists>v prefix rest. has_vertex graph v \<and> in_same_scc graph v c \<and>
          dfs_stack state = prefix @ PostVisit v # rest \<and>
          (\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<longrightarrow>
                z \<in> will_finish_before_me graph state prefix))"

fun finish_order_5 :: "('a::linorder) Graph \<Rightarrow> 'a dfs_state \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "finish_order_5 graph state c d \<longleftrightarrow>
    (\<exists>v. has_vertex graph v \<and> in_same_scc graph v c \<and>
          \<not>List.member (dfs_finish_order state) v)
  \<and> (\<exists>x prefix rest. has_vertex graph x \<and> in_same_scc graph x d \<and>
          dfs_stack state = prefix @ PostVisit x # rest \<and>
          (\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<and> z \<noteq> x \<longrightarrow>
                z \<in> will_finish_before_me graph state prefix))"

fun dfs_finish_order_prop :: "('a::linorder) Graph \<Rightarrow> 'a dfs_state \<Rightarrow> bool" where
  "dfs_finish_order_prop graph state =
    (\<forall>c d. has_edge graph c d \<and> \<not>(in_same_scc graph c d) \<longrightarrow>
      (finish_order_1 graph state c d) \<or>
      (finish_order_2 graph state c d) \<or>
      (finish_order_3 graph state c d) \<or>
      (finish_order_4 graph state c d) \<or>
      (finish_order_5 graph state c d))"


(*-----------------------------------------------------------------------------*)
(* Lemmas relating to properties of paths *)
(*-----------------------------------------------------------------------------*)

(* Lemma: the start of an unvisited_path is unvisited *)
lemma unvisited_path_start_unvisited:
  assumes "unvisited_path graph visited w z"
  shows "w |\<notin>| visited"
  using assms by (cases rule: unvisited_path.cases) auto

(* Lemma: If v becomes visited, an unvisited path to some z \<noteq> v either survives,
   or (if it went through v) its part after the last visit to v starts at a
   successor of v *)
lemma unvisited_path_finsert:
  assumes "unvisited_path graph visited w z"
    and "z \<noteq> v"
  shows "unvisited_path graph (finsert v visited) w z \<or>
         (\<exists>n. has_edge graph v n \<and> unvisited_path graph (finsert v visited) n z)"
  using assms
proof (induction rule: unvisited_path.induct)
  case (unvisited_refl u)
  then show ?case
    by (auto intro: unvisited_path.unvisited_refl)
next
  case (unvisited_step u w' z')
  from unvisited_step.IH[OF unvisited_step.prems] show ?case
  proof
    assume path: "unvisited_path graph (finsert v visited) w' z'"
    show ?thesis
    proof (cases "u = v")
      case True
      then show ?thesis
        using unvisited_step.hyps(2) path by blast
    next
      case False
      then have "u |\<notin>| finsert v visited"
        using unvisited_step.hyps(1) by simp
      then show ?thesis
        using unvisited_step.hyps(2) path unvisited_path.unvisited_step by blast
    qed
  next
    assume "\<exists>n. has_edge graph v n \<and> unvisited_path graph (finsert v visited) n z'"
    then show ?thesis by blast
  qed
qed

(* Predicate stating that all vertices in a path are unvisited *)
fun all_unvisited :: "'a fset \<Rightarrow> 'a list \<Rightarrow> bool" where
  "all_unvisited visited path = (\<forall>v. List.member path v \<longrightarrow> v |\<notin>| visited)"

(* Lemma: A valid path with all unvisited vertices implies unvisited_path *)
lemma valid_path_implies_unvisited_path:
  assumes "valid_graph graph"
    and "valid_path graph path"
    and "path_start path = start"
    and "path_end path = target"
    and "all_unvisited visited path"
  shows "unvisited_path graph visited start target"
  using assms(2-5,1)
proof (induction path arbitrary: start rule: valid_path.induct)
  case (1 graph)
  then show ?case by simp
next
  case (2 graph v)
  then have "start = v" by simp
  moreover have "target = v" using 2 by simp
  moreover have "v |\<notin>| visited"
    using 2 by (simp add: member_rec)
  moreover have "has_vertex graph v"
    using 2 by simp
  ultimately show ?case
    using unvisited_refl by simp
next
  case (3 graph u w rest)
  then have "start = u" by simp
  have "has_edge graph u w" using 3 by simp
  have "u |\<notin>| visited"
    using 3 by (simp add: member_rec)
  have "path_start (w # rest) = w" by simp
  moreover have "path_end (w # rest) = target" using 3 by simp
  moreover have "valid_path graph (w # rest)" using 3 by simp
  moreover have "all_unvisited visited (w # rest)"
    using 3 by (simp add: member_rec)
  ultimately have "unvisited_path graph visited w target"
    using 3(1) 3(6) by blast
  then show ?case
    using \<open>u |\<notin>| visited\<close> \<open>has_edge graph u w\<close> \<open>start = u\<close> unvisited_step by blast
qed


(*-----------------------------------------------------------------------------*)
(* More helper lemmas *)
(*-----------------------------------------------------------------------------*)

(* Helper lemma: map PreVisit doesn't contain PostVisit frames *)
lemma map_PreVisit_no_PostVisit:
  "\<not> List.member (map PreVisit neighbors) (PostVisit v)"
  by (induction neighbors) (auto simp: member_rec)

(* Helper lemma: a list of PreVisit frames cannot be split at a PostVisit frame *)
lemma map_PreVisit_neq_split:
  "map PreVisit ns \<noteq> prefix @ PostVisit v # rest"
proof
  assume "map PreVisit ns = prefix @ PostVisit v # rest"
  then have "PostVisit v \<in> set (map PreVisit ns)"
    by simp
  then show False
    by auto
qed

(* Helper lemma: the vertex of a PostVisit frame on top of the stack is a graph vertex,
   and is not yet finished *)
lemma postvisit_top_props:
  assumes "dfs_state_valid graph state"
    and "dfs_stack state = PostVisit v # rest"
  shows "has_vertex graph v"
    and "\<not> List.member (dfs_finish_order state) v"
  using assms by (auto simp: member_rec(1))


end
