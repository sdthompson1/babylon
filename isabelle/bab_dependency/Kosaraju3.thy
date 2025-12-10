theory Kosaraju3
  imports Kosaraju2
begin

(* Kosaraju's algorithm for finding strongly connected components: Part 3. *)

(*-----------------------------------------------------------------------------*)
(* Running DFS to Completion *)
(*-----------------------------------------------------------------------------*)

(* Run DFS until the stack is empty *)
function dfs_run :: "('a::linorder) Graph \<Rightarrow> 'a dfs_state \<Rightarrow> 'a dfs_state" where
  "dfs_run graph state =
    (if dfs_stack state = []
     then state
     else dfs_run graph (dfs_step graph state))"
  by pat_completeness auto

(* Termination proof: we use a lexicographic measure on (unvisited vertices, stack length) *)
termination dfs_run
proof (relation "measures [\<lambda>(graph,state). fcard (fmdom graph |-|  dfs_visited state),
                           \<lambda>(graph,state). length (dfs_stack state)]")
  show "wf (measures [\<lambda>(graph,state). fcard (fmdom graph |-| dfs_visited state),
                      \<lambda>(graph,state). length (dfs_stack state)])"
    by auto
next
  fix graph :: "('a::linorder) Graph" and state :: "'a dfs_state"
  assume stack_nonempty: "\<not> dfs_stack state = []"

  (* We need to show the measure decreases after one step *)
  show "((graph, dfs_step graph state), (graph, state))
        \<in> measures [\<lambda>(graph,state). fcard (fmdom graph |-| dfs_visited state),
                    \<lambda>(graph,state). length (dfs_stack state)]"
  proof -
    define state' where "state' = dfs_step graph state"

    (* Analyze what dfs_step does based on the stack *)
    obtain frame rest where stack_decomp: "dfs_stack state = frame # rest"
      using stack_nonempty by (cases "dfs_stack state") auto

    show ?thesis
    proof (cases frame)
      case (PreVisit v)
      then show ?thesis
      proof (cases "v |\<in>| dfs_visited state")
        case True
        (* v already visited - just pop the stack *)
        have new_state: "state' = state \<lparr> dfs_stack := rest \<rparr>"
          using state'_def stack_decomp PreVisit True by auto
        hence "length (dfs_stack state') < length (dfs_stack state)"
          using stack_decomp by simp
        moreover have "dfs_visited state' = dfs_visited state"
          using new_state by simp
        ultimately show ?thesis
          using state'_def by auto
      next
        case False
        then show ?thesis
        proof (cases "fmlookup graph v")
          case None
          (* v not in graph - stack becomes empty *)
          have new_state: "state' = state \<lparr> dfs_stack := [] \<rparr>"
            using state'_def stack_decomp PreVisit False None by auto
          hence "length (dfs_stack state') < length (dfs_stack state)"
            using stack_decomp by simp
          moreover have "dfs_visited state' = dfs_visited state"
            using new_state by simp
          ultimately show ?thesis
            using state'_def by auto
        next
          case (Some neighbors)
          (* v has neighbors - mark visited and push neighbors + PostVisit *)
          have "state' = state \<lparr> dfs_visited := finsert v (dfs_visited state),
                                dfs_stack := map PreVisit neighbors @ [PostVisit v] @ rest \<rparr>"
            using state'_def stack_decomp PreVisit False Some by auto
          hence visited_grows: "dfs_visited state' = finsert v (dfs_visited state)"
            and stack_new: "dfs_stack state' = map PreVisit neighbors @ [PostVisit v] @ rest"
            by auto

          (* The key: v was unvisited, now it's visited, so unvisited count decreased *)
          have "v |\<notin>| dfs_visited state" using False by simp
          have "v |\<in>| dfs_visited state'" using visited_grows by simp
          have "v |\<in>| fmdom graph"
            using Some by (simp add: fmdomI)

          (* v is in the domain, so unvisited count strictly decreases *)
          have "fcard (fmdom graph |-| dfs_visited state')
              < fcard (fmdom graph |-| dfs_visited state)"
          proof -
            have "v |\<in>| fmdom graph |-| dfs_visited state"
              using \<open>v |\<in>| fmdom graph\<close> \<open>v |\<notin>| dfs_visited state\<close> by simp
            moreover have "v |\<notin>| fmdom graph |-| dfs_visited state'"
              using \<open>v |\<in>| dfs_visited state'\<close> by simp
            moreover have "fmdom graph |-| dfs_visited state'
                            |\<subset>| fmdom graph |-| dfs_visited state"
              using visited_grows \<open>v |\<in>| fmdom graph |-| dfs_visited state\<close>
                    \<open>v |\<notin>| fmdom graph |-| dfs_visited state'\<close> by auto
            ultimately show ?thesis
              by (simp add: pfsubset_fcard_mono)
          qed
          thus ?thesis
            by (simp add: state'_def) 
        qed
      qed
    next
      case (PostVisit v)
      (* PostVisit just pops the stack and updates finish order *)
      have new_state: "state' = state \<lparr> dfs_finish_order := v # (dfs_finish_order state),
                              dfs_stack := rest \<rparr>"
        using state'_def stack_decomp PostVisit by auto
      hence "length (dfs_stack state') < length (dfs_stack state)"
        using stack_decomp by simp
      moreover have "dfs_visited state' = dfs_visited state"
        using new_state by simp
      ultimately show ?thesis
        using state'_def by auto
    qed
  qed
qed

(*-----------------------------------------------------------------------------*)
(* Lemmas *)
(*-----------------------------------------------------------------------------*)

(* Lemma: dfs_run returns a state with empty stack *)
lemma dfs_run_stack_empty:
  assumes "final = dfs_run graph state"
  shows "dfs_stack final = []"
  using assms
proof (induction graph state rule: dfs_run.induct)
  case (1 graph state)
  then show ?case
    by (metis dfs_run.elims)
qed

(* Lemma: dfs_run preserves state validity *)
lemma dfs_run_preserves_valid:
  assumes "valid_graph graph"
    and "dfs_state_valid graph state"
  shows "dfs_state_valid graph (dfs_run graph state)"
  using assms
proof (induction graph state rule: dfs_run.induct)
  case (1 graph state)
  then show ?case
  proof (cases "dfs_stack state = []")
    case True
    then show ?thesis using 1 by simp
  next
    case False
    then have "dfs_run graph state = dfs_run graph (dfs_step graph state)"
      by simp
    moreover have "dfs_state_valid graph (dfs_step graph state)"
      using 1 False
      using dfs_step_preserves_validity by blast 
    ultimately show ?thesis
      using 1 False
      by metis 
  qed
qed

(* Lemma: dfs_run preserves previsit ordering *)
lemma dfs_run_preserves_previsit_ordered:
  assumes "valid_graph graph"
    and "dfs_state_valid graph state"
    and "dfs_previsit_ordered graph state"
  shows "dfs_previsit_ordered graph (dfs_run graph state)"
  using assms
proof (induction graph state rule: dfs_run.induct)
  case (1 graph state)
  then show ?case
  proof (cases "dfs_stack state = []")
    case True
    then show ?thesis using 1 by simp
  next
    case False
    then have "dfs_run graph state = dfs_run graph (dfs_step graph state)"
      by simp
    moreover have "dfs_state_valid graph (dfs_step graph state)"
      using 1 False
      by (meson dfs_step_preserves_validity) 
    moreover have "dfs_previsit_ordered graph (dfs_step graph state)"
      using 1 False
      using dfs_step_preserves_previsit_ordered by blast 
    ultimately show ?thesis
      using 1 False
      by metis 
  qed
qed

(* Lemma: dfs_run preserves postvisit ordering *)
lemma dfs_run_preserves_postvisit_ordered:
  assumes "valid_graph graph"
    and "dfs_state_valid graph state"
    and "dfs_previsit_ordered graph state"
    and "dfs_postvisit_ordered graph state"
  shows "dfs_postvisit_ordered graph (dfs_run graph state)"
  using assms
proof (induction graph state rule: dfs_run.induct)
  case (1 graph state)
  then show ?case
  proof (cases "dfs_stack state = []")
    case True
    then show ?thesis using 1 by simp
  next
    case False
    then have "dfs_run graph state = dfs_run graph (dfs_step graph state)"
      by simp
    moreover have "dfs_state_valid graph (dfs_step graph state)"
      using 1 False
      using dfs_step_preserves_validity by blast 
    moreover have "dfs_previsit_ordered graph (dfs_step graph state)"
      using 1 False
      using dfs_step_preserves_previsit_ordered by blast 
    moreover have "dfs_postvisit_ordered graph (dfs_step graph state)"
      using 1 False
      using dfs_step_preserves_postvisit_ordered by blast 
    ultimately show ?thesis
      using 1 False
      by presburger 
  qed
qed

(* Lemma: dfs_run preserves finish order property *)
lemma dfs_run_preserves_finish_order:
  assumes "valid_graph graph"
    and "dfs_state_valid graph state"
    and "dfs_previsit_ordered graph state"
    and "dfs_postvisit_ordered graph state"
    and "dfs_finish_order_prop graph state"
  shows "dfs_finish_order_prop graph (dfs_run graph state)"
  using assms
proof (induction graph state rule: dfs_run.induct)
  case (1 graph state)
  then show ?case
  proof (cases "dfs_stack state = []")
    case True
    then show ?thesis using 1
      by (metis dfs_run.simps) 
  next
    case False
    then have "dfs_run graph state = dfs_run graph (dfs_step graph state)"
      by simp
    moreover have "dfs_state_valid graph (dfs_step graph state)"
      using 1 False
      using dfs_step_preserves_validity by blast 
    moreover have "dfs_previsit_ordered graph (dfs_step graph state)"
      using 1 False
      using dfs_step_preserves_previsit_ordered by blast 
    moreover have "dfs_postvisit_ordered graph (dfs_step graph state)"
      using 1 False
      using dfs_step_preserves_postvisit_ordered by blast 
    moreover have "dfs_finish_order_prop graph (dfs_step graph state)"
      using 1 False
      using dfs_step_preserves_finish_order by blast 
    ultimately show ?thesis
      using 1 False
      by presburger 
  qed
qed

(* Visited set never shrinks during dfs_step *)
lemma dfs_step_visited_monotonic:
  "dfs_visited state |\<subseteq>| dfs_visited (dfs_step graph state)"
proof (cases "dfs_stack state")
  case Nil
  then show ?thesis by simp
next
  case (Cons frame rest)
  then show ?thesis
  proof (cases frame)
    case (PreVisit v)
    then show ?thesis
    proof (cases "v |\<in>| dfs_visited state")
      case True
      then show ?thesis using Cons PreVisit by auto
    next
      case False
      then show ?thesis
      proof (cases "fmlookup graph v")
        case None
        then show ?thesis using Cons PreVisit False by auto
      next
        case (Some neighbors)
        then show ?thesis using Cons PreVisit False by auto
      qed
    qed
  next
    case (PostVisit v)
    then show ?thesis using Cons by auto
  qed
qed

(* Visited set never shrinks during dfs_run *)
lemma dfs_run_visited_monotonic:
  "dfs_visited state |\<subseteq>| dfs_visited (dfs_run graph state)"
proof (induction graph state rule: dfs_run.induct)
  case (1 graph state)
  then show ?case
  proof (cases "dfs_stack state = []")
    case True
    then show ?thesis by simp
  next
    case False
    then have "dfs_run graph state = dfs_run graph (dfs_step graph state)"
      by simp
    moreover have "dfs_visited state |\<subseteq>| dfs_visited (dfs_step graph state)"
      using dfs_step_visited_monotonic by blast
    moreover have "dfs_visited (dfs_step graph state) |\<subseteq>|
                   dfs_visited (dfs_run graph (dfs_step graph state))"
      using 1 False by simp
    ultimately show ?thesis
      by (metis dual_order.trans) 
  qed
qed

(* If PreVisit v is on the stack and v is unvisited, then after one step,
   either PreVisit v is still on the stack or v becomes visited *)
lemma dfs_step_previsit_progress:
  assumes "valid_graph graph"
    and "dfs_state_valid graph state"
    and "List.member (dfs_stack state) (PreVisit v)"
    and "v |\<notin>| dfs_visited state"
  shows "List.member (dfs_stack (dfs_step graph state)) (PreVisit v) \<or>
         v |\<in>| dfs_visited (dfs_step graph state)"
proof (cases "dfs_stack state")
  case Nil
  then show ?thesis using assms(3) by simp
next
  case (Cons frame rest)
  then show ?thesis
  proof (cases frame)
    case (PreVisit u)
    then show ?thesis
    proof (cases "u = v")
      case True
      (* v is at the top of the stack *)
      then show ?thesis
      proof (cases "u |\<in>| dfs_visited state")
        case True
        (* u already visited - just pop it *)
        then have "dfs_step graph state = state \<lparr> dfs_stack := rest \<rparr>"
          using Cons PreVisit by simp
        then show ?thesis
          using assms(3) Cons PreVisit True \<open>u = v\<close> by (auto simp: member_rec)
      next
        case False
        (* u not visited - will visit it *)
        define neighbors where "neighbors = the (fmlookup graph u)"
        have "dfs_step graph state = state \<lparr>
                      dfs_visited := finsert u (dfs_visited state),
                      dfs_stack := map PreVisit neighbors @ [PostVisit u] @ rest \<rparr>"
          using dfs_step_previsit_expand False PreVisit assms(2) local.Cons neighbors_def by blast
        thus ?thesis using \<open>u = v\<close> by simp
      qed
    next
      case u_not_v: False
      (* v is deeper in the stack, not at the top *)
      then have "List.member rest (PreVisit v)"
        using assms(3) Cons PreVisit by (simp add: member_rec)
      then show ?thesis
      proof (cases "u |\<in>| dfs_visited state")
        case True
        then have "dfs_step graph state = state \<lparr> dfs_stack := rest \<rparr>"
          using Cons PreVisit by simp
        then show ?thesis using \<open>List.member rest (PreVisit v)\<close> assms(4) by simp
      next
        case False
        define neighbors where "neighbors = the (fmlookup graph u)"
        have "dfs_step graph state = state \<lparr>
                  dfs_visited := finsert u (dfs_visited state),
                  dfs_stack := map PreVisit neighbors @ [PostVisit u] @ rest \<rparr>"
          using False PreVisit assms(2) dfs_step_previsit_expand local.Cons neighbors_def
          by blast
        hence "dfs_stack (dfs_step graph state) = map PreVisit neighbors @ [PostVisit u] @ rest"
          by simp
        moreover have "List.member (map PreVisit neighbors @ [PostVisit u] @ rest) (PreVisit v)"
          using `List.member rest (PreVisit v)` in_set_member set_append by (metis Un_iff)
        ultimately show ?thesis by simp
      qed
    qed
  next
    case (PostVisit u)
    (* Top of stack is PostVisit, v must be deeper *)
    then have "List.member rest (PreVisit v)"
      using assms(3) Cons by (simp add: member_rec)
    have "dfs_step graph state = state \<lparr>
            dfs_finish_order := u # (dfs_finish_order state),
            dfs_stack := rest \<rparr>"
      using Cons PostVisit by simp
    then show ?thesis using \<open>List.member rest (PreVisit v)\<close> assms(4) by simp
  qed
qed

(* Helper lemma: map PreVisit has no duplicate PostVisit frames *)
lemma map_PreVisit_postvisit_distinct:
  "dfs_post_visit_distinct (map PreVisit vertices)"
proof (induction vertices)
  case Nil
  then show ?case by simp
next
  case (Cons v rest)
  have "map PreVisit (v # rest) = PreVisit v # map PreVisit rest"
    by simp
  moreover have "dfs_post_visit_distinct (map PreVisit rest)"
    using Cons.IH by simp
  ultimately show ?case by simp
qed

(* Lemma: initial_dfs_state produces a valid state *)
lemma initial_dfs_state_valid:
  assumes "valid_graph graph"
    and "vertices = sorted_list_of_fset (fmdom graph)"
  shows "dfs_state_valid graph (initial_dfs_state vertices)"
proof -
  define state where "state = initial_dfs_state vertices"

  (* Show stack vertices are valid *)
  have stack_valid: "dfs_stack_vertices_valid graph (dfs_stack state)"
  proof -
    have "dfs_stack state = map PreVisit vertices"
      using state_def by simp
    moreover have "\<forall>v. List.member vertices v \<longrightarrow> has_vertex graph v"
      using assms(2)
      by (metis Graphs.transpose_graph.simps assms(1) foldr_transpose_step_preserves_vertices
          init_empty_graph_vertices transpose_same_vertices) 
    ultimately show ?thesis
      using map_PreVisit_valid by simp
  qed

  (* Show visited vertices are in graph *)
  have visited_in_graph: "(\<forall>v. v |\<in>| dfs_visited state \<longrightarrow> has_vertex graph v)"
    using state_def by simp

  (* Show initial finish list is in graph *)
  have finish_in_graph: "(\<forall>v. List.member (dfs_finish_order state) v \<longrightarrow> has_vertex graph v)"
  proof -
    have "dfs_finish_order state = []" using state_def by simp
    thus ?thesis
      by (simp add: member_rec(2)) 
  qed

  (* Show all PostVisit frames on stack are visited *)
  have postvisit_visited: "dfs_post_visit_visited (dfs_visited state) (dfs_stack state)"
  proof -
    have "dfs_stack state = map PreVisit vertices"
      using state_def by simp
    then have "\<forall>v. \<not> List.member (dfs_stack state) (PostVisit v)"
      using map_PreVisit_no_PostVisit by auto
    then show ?thesis by simp
  qed

  (* Show PostVisit frames are distinct *)
  have postvisit_distinct: "dfs_post_visit_distinct (dfs_stack state)"
    using state_def map_PreVisit_postvisit_distinct by simp

  (* Show finish order is distinct *)
  have finish_distinct: "distinct (dfs_finish_order state)"
    using state_def by simp

  (* Show visited vertices are accounted *)
  have visited_accounted: "dfs_visited_accounted (dfs_visited state) (dfs_finish_order state) (dfs_stack state)"
    using state_def by simp

  (* Show finish order vertices are visited *)
  have finish_visited: "\<forall>v. List.member (dfs_finish_order state) v \<longrightarrow> v |\<in>| dfs_visited state"
  proof -
    have "dfs_finish_order state = []" using state_def by simp
    thus ?thesis
      by (simp add: member_rec(2)) 
  qed

  (* Show finish order and PostVisit are disjoint *)
  have finish_post_disjoint: "\<forall>v. List.member (dfs_finish_order state) v \<longrightarrow> \<not> List.member (dfs_stack state) (PostVisit v)"
  proof -
    have "dfs_finish_order state = []" using state_def by simp
    thus ?thesis
      by (simp add: member_rec(2)) 
  qed

  show ?thesis
    using assms(1) stack_valid visited_in_graph finish_in_graph
          postvisit_visited
          postvisit_distinct finish_distinct
          visited_accounted finish_visited finish_post_disjoint
          state_def by simp
qed

(* Helper lemma: vertices that start on stack eventually get visited *)
lemma dfs_run_visits_initial_stack:
  assumes "valid_graph graph"
    and "dfs_state_valid graph state"
    and "List.member (dfs_stack state) (PreVisit v)"
    and "v |\<notin>| dfs_visited state"
  shows "v |\<in>| dfs_visited (dfs_run graph state)"
  using assms
proof (induction graph state rule: dfs_run.induct)
  case (1 graph state)
  then show ?case
  proof (cases "dfs_stack state = []")
    case True
    then show ?thesis using 1(3)
      by (metis "1.prems"(3) member_rec(2)) 
  next
    case False
    then have run_eq: "dfs_run graph state = dfs_run graph (dfs_step graph state)"
      by simp

    (* After one step, either v is visited or PreVisit v is still on stack *)
    have "List.member (dfs_stack (dfs_step graph state)) (PreVisit v) \<or>
          v |\<in>| dfs_visited (dfs_step graph state)"
      using 1(2-5) False dfs_step_previsit_progress by blast

    then show ?thesis
    proof
      assume visited: "v |\<in>| dfs_visited (dfs_step graph state)"
      (* Visited set can only grow, so v remains visited *)
      have "dfs_visited (dfs_step graph state) |\<subseteq>| dfs_visited (dfs_run graph (dfs_step graph state))"
        using dfs_run_visited_monotonic by blast
      then show ?thesis
        using visited run_eq
        by (metis fsubsetD) 
    next
      assume member: "List.member (dfs_stack (dfs_step graph state)) (PreVisit v)"
      have valid': "dfs_state_valid graph (dfs_step graph state)"
        using 1(2,3) False dfs_step_preserves_validity by blast
      show ?thesis
      proof (cases "v |\<in>| dfs_visited (dfs_step graph state)")
        case True
        then show ?thesis
          using run_eq 1(2,3) False valid'
          by (metis dfs_run_visited_monotonic fin_mono)
      next
        case False
        then have "v |\<in>| dfs_visited (dfs_run graph (dfs_step graph state))"
          using 1(1)[OF \<open>\<not> dfs_stack state = []\<close> \<open>valid_graph graph\<close> valid' member False]
          by blast
        then show ?thesis using run_eq
          by presburger 
      qed
    qed
  qed
qed

(*-----------------------------------------------------------------------------*)
(* Kosaraju Phase 1: Use dfs_run to compute finish order *)
(*-----------------------------------------------------------------------------*)

(* Runs DFS on all vertices to compute finish order *)
definition kosaraju_phase_1 :: "('a::linorder) Graph \<Rightarrow> 'a list" where
  "kosaraju_phase_1 graph =
    (let vertices = sorted_list_of_fset (fmdom graph);
         initial_state = initial_dfs_state vertices;
         final_state = dfs_run graph initial_state
     in dfs_finish_order final_state)"

(*-----------------------------------------------------------------------------*)
(* Kosaraju Phase 1 correctness theorems *)
(*-----------------------------------------------------------------------------*)

(* Correctness predicate #1 for finish order:
   All vertices in the graph appear in the finish list *)
definition finish_list_contains_all_vertices :: "('a::linorder) Graph \<Rightarrow> 'a list \<Rightarrow> bool" where
  "finish_list_contains_all_vertices graph finish_order \<longleftrightarrow>
    (\<forall>v. has_vertex graph v \<longrightarrow> List.member finish_order v)"

(* Correctness predicate #2 for finish order:
   For all edges (c,d) between different SCCs, there exists a vertex v_c
   in the same SCC as c that appears before all vertices in d's SCC.
   This is the key property needed for Kosaraju's algorithm phase 2. *)
definition finish_order_correct :: "('a::linorder) Graph \<Rightarrow> 'a list \<Rightarrow> bool" where
  "finish_order_correct graph finish_order \<longleftrightarrow>
    (\<forall>c d. has_edge graph c d \<and> \<not>(in_same_scc graph c d) \<longrightarrow>
      (\<exists>v_c. has_vertex graph v_c \<and> in_same_scc graph v_c c \<and>
        (\<forall>v_d. has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
          index_of v_c finish_order < index_of v_d finish_order)))"

(* Theorem: kosaraju_phase_1 produces a finish list containing all vertices *)
theorem kosaraju_phase_1_complete:
  assumes "valid_graph graph"
  shows "finish_list_contains_all_vertices graph (kosaraju_phase_1 graph)"
proof -
  define vertices where "vertices = sorted_list_of_fset (fmdom graph)"
  define initial_state where "initial_state = initial_dfs_state vertices"
  define final_state where "final_state = dfs_run graph initial_state"

  have phase1_eq: "kosaraju_phase_1 graph = dfs_finish_order final_state"
    unfolding kosaraju_phase_1_def vertices_def initial_state_def final_state_def
    by (simp add: Let_def)

  (* Show that the final state has empty stack *)
  have stack_empty: "dfs_stack final_state = []"
    using final_state_def dfs_run_stack_empty by blast

  (* Show the initial state is valid *)
  have initial_valid: "dfs_state_valid graph initial_state"
    using assms initial_state_def vertices_def initial_dfs_state_valid by blast

  (* Show that all graph vertices are visited in final state *)
  have all_visited: "\<forall>v. has_vertex graph v \<longrightarrow> v |\<in>| dfs_visited final_state"
  proof (intro allI impI)
    fix v
    assume "has_vertex graph v"
    then have "v |\<in>| fmdom graph" by simp
    then have "List.member vertices v"
      using vertices_def in_set_member by fastforce
    then have "v \<in> set vertices"
      using in_set_member by metis 
    then have "PreVisit v \<in> set (map PreVisit vertices)"
      by simp
    then have "List.member (map PreVisit vertices) (PreVisit v)"
      using in_set_member by metis
    then have "List.member (dfs_stack initial_state) (PreVisit v)"
      using initial_state_def by simp

    have "v |\<notin>| dfs_visited initial_state"
      using initial_state_def by simp

    show "v |\<in>| dfs_visited final_state"
      using \<open>List.member (dfs_stack initial_state) (PreVisit v)\<close> \<open>v |\<notin>| dfs_visited initial_state\<close>
        assms dfs_run_visits_initial_stack final_state_def initial_valid by blast
  qed

  (* Show that all visited vertices are in finish order when stack is empty *)
  have final_valid: "dfs_state_valid graph final_state"
    using assms initial_valid final_state_def dfs_run_preserves_valid by blast

  have "\<forall>v. v |\<in>| dfs_visited final_state \<longrightarrow> List.member (dfs_finish_order final_state) v"
    using final_valid stack_empty
    by (simp add: member_rec(2))

  (* Combine to show all graph vertices are in finish order *)
  then have "\<forall>v. has_vertex graph v \<longrightarrow> List.member (dfs_finish_order final_state) v"
    using all_visited by blast

  then show ?thesis
    unfolding finish_list_contains_all_vertices_def phase1_eq by simp
qed

(* Theorem: kosaraju_phase_1 produces a correctly ordered finish list *)
theorem kosaraju_phase_1_correct:
  assumes "valid_graph graph"
  shows "finish_order_correct graph (kosaraju_phase_1 graph)"
proof -
  define vertices where "vertices = sorted_list_of_fset (fmdom graph)"
  define initial_state where "initial_state = initial_dfs_state vertices"
  define final_state where "final_state = dfs_run graph initial_state"

  have phase1_eq: "kosaraju_phase_1 graph = dfs_finish_order final_state"
    unfolding kosaraju_phase_1_def vertices_def initial_state_def final_state_def
    by (simp add: Let_def)

  (* Show the initial state is valid *)
  have initial_valid: "dfs_state_valid graph initial_state"
    using assms initial_state_def vertices_def initial_dfs_state_valid by blast

  (* Show that the final state has empty stack *)
  have stack_empty: "dfs_stack final_state = []"
    using final_state_def dfs_run_stack_empty by blast

  (* Show the final state is valid *)
  have final_valid: "dfs_state_valid graph final_state"
    using assms initial_valid final_state_def dfs_run_preserves_valid by blast

  (* There are no PostVisit frames in the initial stack *)
  have initial_is_map_previsit: "dfs_stack initial_state = map PreVisit vertices"
      using initial_state_def by simp
  hence initial_no_postvisit: "\<forall>v. \<not> List.member (dfs_stack initial_state) (PostVisit v)"
    using map_PreVisit_no_PostVisit by auto

  (* Show that initial state satisfies ordering properties *)
  have initial_previsit_ordered: "dfs_previsit_ordered graph initial_state"
    by (simp add: initial_no_postvisit)

  have initial_postvisit_ordered: "dfs_postvisit_ordered graph initial_state"
    by (simp add: initial_no_postvisit)

  have initial_finish_order_prop: "dfs_finish_order_prop graph initial_state"
  proof -
    have empty_visited: "dfs_visited initial_state = {||}"
      using initial_state_def by simp

    (* For any edge between different SCCs, finish_order_1 holds *)
    have "\<forall>c d. has_edge graph c d \<and> \<not>(in_same_scc graph c d) \<longrightarrow>
                finish_order_1 graph initial_state c d"
    proof (intro allI impI)
      fix c d
      assume "has_edge graph c d \<and> \<not>(in_same_scc graph c d)"
      (* All vertices are unvisited, so finish_order_1 holds *)
      have "\<forall>v. has_vertex graph v \<and> (in_same_scc graph v c \<or> in_same_scc graph v d) \<longrightarrow>
                 v |\<notin>| (dfs_visited initial_state)"
        using empty_visited by simp
      then show "finish_order_1 graph initial_state c d"
        by simp
    qed
    then show ?thesis by auto
  qed

  (* Show these properties are preserved *)
  have final_previsit_ordered: "dfs_previsit_ordered graph final_state"
    using assms initial_valid initial_previsit_ordered final_state_def
          dfs_run_preserves_previsit_ordered by blast

  have final_postvisit_ordered: "dfs_postvisit_ordered graph final_state"
    using assms initial_valid initial_previsit_ordered initial_postvisit_ordered
          final_state_def dfs_run_preserves_postvisit_ordered by blast

  have final_finish_order_prop: "dfs_finish_order_prop graph final_state"
    using assms initial_valid initial_previsit_ordered initial_postvisit_ordered
          initial_finish_order_prop final_state_def dfs_run_preserves_finish_order
    by blast

  (* All vertices are visited in final state *)
  have all_visited: "\<forall>v. has_vertex graph v \<longrightarrow> v |\<in>| dfs_visited final_state"
  proof (intro allI impI)
    fix v
    assume "has_vertex graph v"
    then have "v |\<in>| fmdom graph" by simp
    then have "List.member vertices v"
      using vertices_def in_set_member by fastforce
    then have "v \<in> set vertices"
      using in_set_member by metis
    then have "PreVisit v \<in> set (map PreVisit vertices)"
      by simp
    then have "List.member (map PreVisit vertices) (PreVisit v)"
      using in_set_member by metis
    then have "List.member (dfs_stack initial_state) (PreVisit v)"
      using initial_state_def by simp

    have "v |\<notin>| dfs_visited initial_state"
      using initial_state_def by simp

    show "v |\<in>| dfs_visited final_state"
      using \<open>List.member (dfs_stack initial_state) (PreVisit v)\<close> \<open>v |\<notin>| dfs_visited initial_state\<close>
        assms dfs_run_visits_initial_stack final_state_def initial_valid by blast
  qed

  (* The key step: when stack is empty and all vertices are visited,
     dfs_finish_order_prop implies finish_order_correct *)
  have "finish_order_correct graph (dfs_finish_order final_state)"
    unfolding finish_order_correct_def
  proof (intro allI impI)
    fix c d
    assume edge: "has_edge graph c d \<and> \<not> in_same_scc graph c d"

    (* From dfs_finish_order_prop, one of the five cases holds *)
    have "finish_order_1 graph final_state c d \<or>
          finish_order_2 graph final_state c d \<or>
          finish_order_3 graph final_state c d \<or>
          finish_order_4 graph final_state c d \<or>
          finish_order_5 graph final_state c d"
      using final_finish_order_prop edge by simp

    moreover {
      (* finish_order_1 is impossible: all vertices are visited *)
      have "\<not> finish_order_1 graph final_state c d"
        using all_visited edge
        using assms edge_implies_vertices(1) finish_order_1.simps in_same_scc_refl by blast
    }

    moreover {
      (* finish_order_2 is impossible: all vertices are in finish order *)
      have "\<not> finish_order_2 graph final_state c d"
      proof -
        have "\<forall>v. has_vertex graph v \<longrightarrow> List.member (dfs_finish_order final_state) v"
          using final_valid stack_empty all_visited
          by (metis assms finish_list_contains_all_vertices_def kosaraju_phase_1_complete
              phase1_eq)
        then show ?thesis by auto
      qed
    }

    moreover {
      (* finish_order_4 is impossible: stack is empty *)
      have "\<not> finish_order_4 graph final_state c d"
        using stack_empty by simp
    }

    moreover {
      (* finish_order_5 is impossible: stack is empty *)
      have "\<not> finish_order_5 graph final_state c d"
        using stack_empty by simp
    }

    (* Therefore finish_order_3 must hold *)
    ultimately have "finish_order_3 graph final_state c d"
      by blast

    (* finish_order_3 gives us exactly what we need *)
    then show "(\<exists>v_c. has_vertex graph v_c \<and> in_same_scc graph v_c c \<and>
                    (\<forall>v_d. has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
                      index_of v_c (dfs_finish_order final_state) <
                      index_of v_d (dfs_finish_order final_state)))"
      by simp
  qed

  then show ?thesis
    unfolding phase1_eq by simp
qed

(* Theorem: kosaraju_phase_1 produces a finish list with distinct elements *)
theorem kosaraju_phase_1_distinct:
  assumes "valid_graph graph"
  shows "distinct (kosaraju_phase_1 graph)"
proof -
  define vertices where "vertices = sorted_list_of_fset (fmdom graph)"
  define initial_state where "initial_state = initial_dfs_state vertices"
  define final_state where "final_state = dfs_run graph initial_state"

  have phase1_eq: "kosaraju_phase_1 graph = dfs_finish_order final_state"
    unfolding kosaraju_phase_1_def vertices_def initial_state_def final_state_def
    by (simp add: Let_def)

  (* Show the initial state is valid *)
  have initial_valid: "dfs_state_valid graph initial_state"
    using assms initial_state_def vertices_def initial_dfs_state_valid by blast

  (* Show the final state is valid *)
  have final_valid: "dfs_state_valid graph final_state"
    using assms initial_valid final_state_def dfs_run_preserves_valid by blast

  (* Extract distinctness from the validity invariant *)
  have "distinct (dfs_finish_order final_state)"
    using final_valid by simp

  then show ?thesis
    unfolding phase1_eq by simp
qed

(* Theorem: all elements in the finish list are vertices in the graph *)
theorem kosaraju_phase_1_vertices_only:
  assumes "valid_graph graph"
  shows "\<forall>v. List.member (kosaraju_phase_1 graph) v \<longrightarrow> has_vertex graph v"
proof -
  define vertices where "vertices = sorted_list_of_fset (fmdom graph)"
  define initial_state where "initial_state = initial_dfs_state vertices"
  define final_state where "final_state = dfs_run graph initial_state"

  have phase1_eq: "kosaraju_phase_1 graph = dfs_finish_order final_state"
    unfolding kosaraju_phase_1_def vertices_def initial_state_def final_state_def
    by (simp add: Let_def)

  (* Show the initial state is valid *)
  have initial_valid: "dfs_state_valid graph initial_state"
    using assms initial_state_def vertices_def initial_dfs_state_valid by blast

  (* Show the final state is valid *)
  have final_valid: "dfs_state_valid graph final_state"
    using assms initial_valid final_state_def dfs_run_preserves_valid by blast

  (* Extract the property from the validity invariant *)
  have "\<forall>v. List.member (dfs_finish_order final_state) v \<longrightarrow> has_vertex graph v"
    using final_valid by simp

  then show ?thesis
    unfolding phase1_eq by simp
qed

end
