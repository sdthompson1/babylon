theory Kosaraju3
  imports Kosaraju2
begin

(* Kosaraju's algorithm for finding strongly connected components: Part 3. *)

(*-----------------------------------------------------------------------------*)
(* Running DFS to Completion *)
(*-----------------------------------------------------------------------------*)

(* Helper lemma for termination proofs: visiting a new vertex decreases the number
   of unvisited vertices *)
lemma fcard_fminus_finsert_less:
  assumes "v |\<in>| A"
    and "v |\<notin>| B"
  shows "fcard (A |-| finsert v B) < fcard (A |-| B)"
proof (rule pfsubset_fcard_mono)
  have "v |\<in>| A |-| B" "v |\<notin>| A |-| finsert v B"
    using assms by simp_all
  then show "A |-| finsert v B |\<subset>| A |-| B"
    by auto
qed

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
  assume "\<not> dfs_stack state = []"
  then obtain frame rest where stack: "dfs_stack state = frame # rest"
    by (cases "dfs_stack state") auto
  show "((graph, dfs_step graph state), (graph, state))
        \<in> measures [\<lambda>(graph,state). fcard (fmdom graph |-| dfs_visited state),
                    \<lambda>(graph,state). length (dfs_stack state)]"
  proof (cases frame)
    case (PreVisit v)
    show ?thesis
    proof (cases "v |\<in>| dfs_visited state")
      case True
      (* v already visited - the stack shrinks *)
      then show ?thesis using stack PreVisit by simp
    next
      case False
      show ?thesis
      proof (cases "fmlookup graph v")
        case None
        (* v not in graph - the stack is cleared *)
        then show ?thesis using stack PreVisit False by simp
      next
        case (Some neighbors)
        (* v gets visited - the number of unvisited vertices shrinks *)
        then have "v |\<in>| fmdom graph"
          by (rule fmdomI)
        then have "fcard (fmdom graph |-| finsert v (dfs_visited state))
                     < fcard (fmdom graph |-| dfs_visited state)"
          using False by (rule fcard_fminus_finsert_less)
        then show ?thesis using stack PreVisit False Some by simp
      qed
    qed
  next
    case (PostVisit v)
    (* PostVisit just pops the stack *)
    then show ?thesis using stack by simp
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

(* Lemma: dfs_run preserves any invariant preserved by dfs_step *)
lemma dfs_run_invariant:
  assumes "P state"
    and "\<And>s. P s \<Longrightarrow> dfs_stack s \<noteq> [] \<Longrightarrow> P (dfs_step graph s)"
  shows "P (dfs_run graph state)"
  using assms
proof (induction graph state rule: dfs_run.induct)
  case (1 graph state)
  show ?case
  proof (cases "dfs_stack state = []")
    case True
    then show ?thesis using "1.prems"(1) by simp
  next
    case False
    have "P (dfs_step graph state)"
      using "1.prems" False by blast
    then have "P (dfs_run graph (dfs_step graph state))"
      using "1.IH" "1.prems"(2) False by blast
    then show ?thesis
      using False by (simp only: dfs_run.simps[of graph state] if_False)
  qed
qed

(* The invariants maintained by the DFS *)
definition dfs_inv :: "('a::linorder) Graph \<Rightarrow> 'a dfs_state \<Rightarrow> bool" where
  "dfs_inv graph state \<longleftrightarrow>
    dfs_state_valid graph state \<and>
    dfs_previsit_ordered graph state \<and>
    dfs_postvisit_ordered graph state \<and>
    dfs_finish_order_prop graph state"

(* Lemma: dfs_step preserves the invariants *)
lemma dfs_step_preserves_inv:
  assumes "dfs_inv graph state"
    and "dfs_stack state \<noteq> []"
  shows "dfs_inv graph (dfs_step graph state)"
  using assms
    dfs_step_preserves_validity dfs_step_preserves_previsit_ordered
    dfs_step_preserves_postvisit_ordered dfs_step_preserves_finish_order
  unfolding dfs_inv_def by blast

(* Visited set never shrinks during dfs_step *)
lemma dfs_step_visited_monotonic:
  "dfs_visited state |\<subseteq>| dfs_visited (dfs_step graph state)"
  by (auto split: list.split dfs_frame.split option.split)

(* If PreVisit v is on the stack and v is unvisited, then after one step,
   either PreVisit v is still on the stack or v becomes visited *)
lemma dfs_step_previsit_progress:
  assumes "dfs_state_valid graph state"
    and "List.member (dfs_stack state) (PreVisit v)"
    and "v |\<notin>| dfs_visited state"
  shows "List.member (dfs_stack (dfs_step graph state)) (PreVisit v) \<or>
         v |\<in>| dfs_visited (dfs_step graph state)"
proof -
  have nonempty: "dfs_stack state \<noteq> []"
    using assms(2) by (auto simp: member_rec(2))
  show ?thesis
  proof (cases rule: dfs_step_cases[OF assms(1) nonempty, case_names skip expand finish])
    case (skip u rest)
    (* u is visited, so it is not v, and PreVisit v must be in rest *)
    then show ?thesis
      using assms(2,3) by (auto simp: member_rec(1))
  next
    case (expand u rest)
    then show ?thesis
      using assms(2) by (auto simp: member_def)
  next
    case (finish u rest)
    then show ?thesis
      using assms(2) by (auto simp: member_rec(1))
  qed
qed

(* Helper lemma: map PreVisit has no duplicate PostVisit frames *)
lemma map_PreVisit_postvisit_distinct:
  "dfs_post_visit_distinct (map PreVisit vertices)"
  by (induction vertices) simp_all

(* Lemma: initial_dfs_state produces a valid state *)
lemma initial_dfs_state_valid:
  assumes "valid_graph graph"
    and "vertices = sorted_list_of_fset (fmdom graph)"
  shows "dfs_state_valid graph (initial_dfs_state vertices)"
proof -
  have vertices_valid: "\<forall>v. List.member vertices v \<longrightarrow> has_vertex graph v"
    using assms(2) by (simp add: member_def)
  show ?thesis
    using assms(1) map_PreVisit_valid[OF vertices_valid]
    by (simp add: member_rec(2) map_PreVisit_no_PostVisit map_PreVisit_postvisit_distinct)
qed

(* Lemma: vertices that start on the stack eventually get visited *)
lemma dfs_run_visits_initial_stack:
  assumes "dfs_state_valid graph state"
    and "List.member (dfs_stack state) (PreVisit v)"
  shows "v |\<in>| dfs_visited (dfs_run graph state)"
proof -
  (* Invariant: either PreVisit v is still on the stack or v has been visited *)
  define P where "P = (\<lambda>s. dfs_state_valid graph s \<and>
                           (List.member (dfs_stack s) (PreVisit v) \<or> v |\<in>| dfs_visited s))"
  have empty: "dfs_stack (dfs_run graph state) = []"
    by (rule dfs_run_stack_empty[OF refl])
  have "P (dfs_run graph state)"
  proof (rule dfs_run_invariant)
    show "P state"
      using assms unfolding P_def by blast
  next
    fix s
    assume "P s" and "dfs_stack s \<noteq> []"
    then show "P (dfs_step graph s)"
      unfolding P_def
      using dfs_step_preserves_validity dfs_step_previsit_progress dfs_step_visited_monotonic
      by blast
  qed
  then have "List.member (dfs_stack (dfs_run graph state)) (PreVisit v) \<or>
             v |\<in>| dfs_visited (dfs_run graph state)"
    unfolding P_def by blast
  with empty show ?thesis
    by (simp add: member_rec(2))
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

(* The final DFS state of phase 1 satisfies the invariants, has an empty stack,
   and has visited every vertex *)
lemma kosaraju_phase_1_final:
  assumes "valid_graph graph"
  obtains final where "kosaraju_phase_1 graph = dfs_finish_order final"
    and "dfs_state_valid graph final"
    and "dfs_finish_order_prop graph final"
    and "dfs_stack final = []"
    and "\<forall>v. has_vertex graph v \<longrightarrow> v |\<in>| dfs_visited final"
proof -
  define vertices where "vertices = sorted_list_of_fset (fmdom graph)"
  define initial_state where "initial_state = initial_dfs_state vertices"
  define final_state where "final_state = dfs_run graph initial_state"

  have phase1_eq: "kosaraju_phase_1 graph = dfs_finish_order final_state"
    unfolding kosaraju_phase_1_def vertices_def initial_state_def final_state_def
    by (simp add: Let_def)

  have initial_valid: "dfs_state_valid graph initial_state"
    unfolding initial_state_def by (rule initial_dfs_state_valid[OF assms vertices_def])

  (* There are no PostVisit frames, and nothing is visited, in the initial state *)
  have initial_inv: "dfs_inv graph initial_state"
  proof -
    have initial_stack: "dfs_stack initial_state = map PreVisit vertices"
      unfolding initial_state_def by simp
    have "dfs_previsit_ordered graph initial_state"
      using initial_stack map_PreVisit_neq_split
      unfolding dfs_previsit_ordered.simps by auto
    moreover have "dfs_postvisit_ordered graph initial_state"
      using initial_stack map_PreVisit_neq_split
      unfolding dfs_postvisit_ordered.simps by auto
    moreover have "dfs_finish_order_prop graph initial_state"
      unfolding initial_state_def by simp
    ultimately show ?thesis
      using initial_valid unfolding dfs_inv_def by blast
  qed

  have "dfs_inv graph final_state"
    unfolding final_state_def
    by (rule dfs_run_invariant[where P = "dfs_inv graph", OF initial_inv])
       (rule dfs_step_preserves_inv)
  then have final_valid: "dfs_state_valid graph final_state"
    and final_finish_order_prop: "dfs_finish_order_prop graph final_state"
    unfolding dfs_inv_def by blast+

  have stack_empty: "dfs_stack final_state = []"
    unfolding final_state_def by (rule dfs_run_stack_empty[OF refl])

  (* Every vertex starts on the stack, so gets visited *)
  have all_visited: "\<forall>v. has_vertex graph v \<longrightarrow> v |\<in>| dfs_visited final_state"
  proof (intro allI impI)
    fix v
    assume "has_vertex graph v"
    then have "List.member (dfs_stack initial_state) (PreVisit v)"
      unfolding initial_state_def vertices_def by (simp add: member_def image_iff)
    then show "v |\<in>| dfs_visited final_state"
      unfolding final_state_def by (rule dfs_run_visits_initial_stack[OF initial_valid])
  qed

  show ?thesis
    by (rule that[OF phase1_eq final_valid final_finish_order_prop stack_empty all_visited])
qed

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
  obtain final where phase1_eq: "kosaraju_phase_1 graph = dfs_finish_order final"
    and final_valid: "dfs_state_valid graph final"
    and stack_empty: "dfs_stack final = []"
    and all_visited: "\<forall>v. has_vertex graph v \<longrightarrow> v |\<in>| dfs_visited final"
    using kosaraju_phase_1_final[OF assms] by blast

  (* With an empty stack, every visited vertex is finished *)
  have "\<forall>v. v |\<in>| dfs_visited final \<longrightarrow> List.member (dfs_finish_order final) v"
    using final_valid stack_empty
    by (simp add: member_rec(2))

  then show ?thesis
    unfolding finish_list_contains_all_vertices_def phase1_eq
    using all_visited by blast
qed

(* Theorem: kosaraju_phase_1 produces a correctly ordered finish list *)
theorem kosaraju_phase_1_correct:
  assumes "valid_graph graph"
  shows "finish_order_correct graph (kosaraju_phase_1 graph)"
proof -
  obtain final where phase1_eq: "kosaraju_phase_1 graph = dfs_finish_order final"
    and final_finish_order_prop: "dfs_finish_order_prop graph final"
    and stack_empty: "dfs_stack final = []"
    and all_visited: "\<forall>v. has_vertex graph v \<longrightarrow> v |\<in>| dfs_visited final"
    using kosaraju_phase_1_final[OF assms] by blast

  have all_finished: "\<forall>v. has_vertex graph v \<longrightarrow> List.member (dfs_finish_order final) v"
    using kosaraju_phase_1_complete[OF assms]
    unfolding finish_list_contains_all_vertices_def phase1_eq .

  (* When the stack is empty and all vertices are finished, of the five cases
     of dfs_finish_order_prop only finish_order_3 is possible *)
  have "finish_order_3 graph final c d"
    if edge: "has_edge graph c d" "\<not> in_same_scc graph c d" for c d
  proof -
    have c_vertex: "has_vertex graph c"
      using assms edge(1) edge_implies_vertices(1) by blast
    have "finish_order_1 graph final c d \<or>
          finish_order_2 graph final c d \<or>
          finish_order_3 graph final c d \<or>
          finish_order_4 graph final c d \<or>
          finish_order_5 graph final c d"
      using final_finish_order_prop edge unfolding dfs_finish_order_prop.simps by blast
    moreover have "\<not> finish_order_1 graph final c d"
      using all_visited c_vertex in_same_scc_refl unfolding finish_order_1.simps by blast
    moreover have "\<not> finish_order_2 graph final c d"
      using all_finished unfolding finish_order_2.simps by blast
    moreover have "\<not> finish_order_4 graph final c d" "\<not> finish_order_5 graph final c d"
      using stack_empty by simp_all
    ultimately show ?thesis
      by blast
  qed

  then show ?thesis
    unfolding finish_order_correct_def phase1_eq finish_order_3.simps by blast
qed

(* Theorem: kosaraju_phase_1 produces a finish list with distinct elements *)
theorem kosaraju_phase_1_distinct:
  assumes "valid_graph graph"
  shows "distinct (kosaraju_phase_1 graph)"
proof -
  obtain final where phase1_eq: "kosaraju_phase_1 graph = dfs_finish_order final"
    and final_valid: "dfs_state_valid graph final"
    using kosaraju_phase_1_final[OF assms] by blast
  then show ?thesis
    by simp
qed

(* Theorem: all elements in the finish list are vertices in the graph *)
theorem kosaraju_phase_1_vertices_only:
  assumes "valid_graph graph"
  shows "\<forall>v. List.member (kosaraju_phase_1 graph) v \<longrightarrow> has_vertex graph v"
proof -
  obtain final where phase1_eq: "kosaraju_phase_1 graph = dfs_finish_order final"
    and final_valid: "dfs_state_valid graph final"
    using kosaraju_phase_1_final[OF assms] by blast
  then show ?thesis
    by simp
qed

end
