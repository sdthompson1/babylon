theory Kosaraju4
  imports Kosaraju3
begin

(* Kosaraju's algorithm for finding strongly connected components: Part 4. *)

(*-----------------------------------------------------------------------------*)
(* SCC Collection State - for phase 2 of Kosaraju's algorithm *)
(*-----------------------------------------------------------------------------*)

(* State for collecting a single SCC via DFS on transposed graph *)
record ('a::linorder) scc_state =
  scc_visited :: "'a fset"           (* Vertices visited in this DFS *)
  scc_component :: "'a list"         (* The SCC being collected *)
  scc_stack :: "'a list"             (* Stack of vertices to explore *)

(*-----------------------------------------------------------------------------*)
(* State Validity Invariants *)
(*-----------------------------------------------------------------------------*)

(* Basic state validity invariant:
   1. All visited vertices are in the graph
   2. All component vertices have been visited
   3. All stack vertices are in the graph
   4. Initial visited set is preserved
   5. Component only contains newly visited vertices
   6. All newly visited vertices are in the component
   7. Component contains no duplicate vertices *)
definition scc_state_valid :: "('a::linorder) Graph \<Rightarrow> 'a fset \<Rightarrow> 'a \<Rightarrow> 'a scc_state \<Rightarrow> bool" where
  "scc_state_valid graph initial_visited start state \<longleftrightarrow>
    (\<forall>v. v |\<in>| scc_visited state \<longrightarrow> has_vertex graph v) \<and>
    (\<forall>v. List.member (scc_component state) v \<longrightarrow> v |\<in>| scc_visited state) \<and>
    (\<forall>v. List.member (scc_stack state) v \<longrightarrow> has_vertex graph v) \<and>
    (initial_visited |\<subseteq>| scc_visited state) \<and>
    (\<forall>v. List.member (scc_component state) v \<longrightarrow> v |\<notin>| initial_visited) \<and>
    (\<forall>v. v |\<in>| scc_visited state \<and> v |\<notin>| initial_visited \<longrightarrow> List.member (scc_component state) v) \<and>
    distinct (scc_component state)"

(* Reachability invariant: All vertices in the component and stack are reachable from start *)
definition scc_reachability_inv :: "('a::linorder) Graph \<Rightarrow> 'a fset \<Rightarrow> 'a \<Rightarrow> 'a scc_state \<Rightarrow> bool" where
  "scc_reachability_inv graph initial_visited start state \<longleftrightarrow>
    (\<forall>v. List.member (scc_component state) v \<longrightarrow> reachable graph start v) \<and>
    (\<forall>v. List.member (scc_stack state) v \<longrightarrow> reachable graph start v)"

(* Soundness invariant: All visited vertices (not in initial_visited)
   are in the same SCC as start *)
definition scc_soundness_inv :: "('a::linorder) Graph \<Rightarrow> 'a fset \<Rightarrow> 'a \<Rightarrow> 'a scc_state \<Rightarrow> bool" where
  "scc_soundness_inv graph initial_visited start state \<longleftrightarrow>
    (\<forall>v. v |\<in>| scc_visited state \<and> v |\<notin>| initial_visited \<longrightarrow>
         in_same_scc graph v start)"

(* Completeness invariant: All unvisited reachable vertices are either
   on the stack or reachable from something on the stack via an unvisited path *)
definition scc_completeness_inv :: "('a::linorder) Graph \<Rightarrow> 'a fset \<Rightarrow> 'a \<Rightarrow> 'a scc_state \<Rightarrow> bool" where
  "scc_completeness_inv graph initial_visited start state \<longleftrightarrow>
    (\<forall>v. has_vertex graph v \<and> reachable graph start v \<and> v |\<notin>| scc_visited state \<longrightarrow>
         (\<exists>w. List.member (scc_stack state) w \<and> unvisited_path graph (scc_visited state) w v))"

(* All of the above invariants together *)
definition scc_inv :: "('a::linorder) Graph \<Rightarrow> 'a fset \<Rightarrow> 'a \<Rightarrow> 'a scc_state \<Rightarrow> bool" where
  "scc_inv graph initial_visited start state \<longleftrightarrow>
    scc_state_valid graph initial_visited start state \<and>
    scc_reachability_inv graph initial_visited start state \<and>
    scc_soundness_inv graph initial_visited start state \<and>
    scc_completeness_inv graph initial_visited start state"

(*-----------------------------------------------------------------------------*)
(* Single Step of SCC Collection *)
(*-----------------------------------------------------------------------------*)

(* Single step of DFS for collecting an SCC *)
fun collect_scc_step :: "('a::linorder) Graph \<Rightarrow> 'a scc_state \<Rightarrow> 'a scc_state" where
  "collect_scc_step graph state =
    (case scc_stack state of
      [] \<Rightarrow> state
    | v # rest \<Rightarrow>
        if v |\<in>| scc_visited state then
          state \<lparr> scc_stack := rest \<rparr>
        else (case fmlookup graph v of
            None \<Rightarrow> state \<lparr> scc_stack := [] \<rparr>
          | Some neighbors \<Rightarrow>
              state \<lparr> scc_visited := finsert v (scc_visited state),
                      scc_component := v # (scc_component state),
                      scc_stack := neighbors @ rest \<rparr>)
    )"

(* The possible outcomes of collect_scc_step, when all stack vertices are in the graph *)
lemma collect_scc_step_cases:
  assumes "\<forall>v. List.member (scc_stack state) v \<longrightarrow> has_vertex graph v"
  obtains (empty) "scc_stack state = []" "collect_scc_step graph state = state"
  | (skip) v rest where "scc_stack state = v # rest" "v |\<in>| scc_visited state"
      "collect_scc_step graph state = state \<lparr> scc_stack := rest \<rparr>"
  | (visit) v rest neighbors where "scc_stack state = v # rest" "v |\<notin>| scc_visited state"
      "fmlookup graph v = Some neighbors"
      "collect_scc_step graph state =
         state \<lparr> scc_visited := finsert v (scc_visited state),
                 scc_component := v # scc_component state,
                 scc_stack := neighbors @ rest \<rparr>"
proof (cases "scc_stack state")
  case Nil
  show ?thesis
    by (rule empty) (simp_all add: Nil)
next
  case (Cons v rest)
  show ?thesis
  proof (cases "v |\<in>| scc_visited state")
    case visited: True
    show ?thesis
      by (rule skip[OF Cons visited]) (simp add: Cons visited)
  next
    case unvisited: False
    have "has_vertex graph v"
      using Cons assms by (simp add: member_rec(1))
    then obtain neighbors where nb: "fmlookup graph v = Some neighbors"
      by (auto simp: fmlookup_dom_iff)
    show ?thesis
      by (rule visit[OF Cons unvisited nb]) (simp add: Cons unvisited nb)
  qed
qed

(*-----------------------------------------------------------------------------*)
(* Invariant Preservation Lemmas for collect_scc_step *)
(*-----------------------------------------------------------------------------*)

(* Lemma: collect_scc_step preserves validity *)
lemma collect_scc_step_preserves_valid:
  assumes "valid_graph graph"
    and "scc_state_valid graph initial_visited start state"
  shows "scc_state_valid graph initial_visited start (collect_scc_step graph state)"
proof -
  (* Note: conjuncts 2 and 6 of scc_state_valid, used together as conditional rewrite
     rules, make simp loop; so each new conjunct is proved from just the facts it needs *)
  have visited_vertices: "\<forall>v. v |\<in>| scc_visited state \<longrightarrow> has_vertex graph v"
    and comp_visited: "\<forall>v. List.member (scc_component state) v \<longrightarrow> v |\<in>| scc_visited state"
    and stack_vertices: "\<forall>v. List.member (scc_stack state) v \<longrightarrow> has_vertex graph v"
    and initial_sub: "initial_visited |\<subseteq>| scc_visited state"
    and comp_new: "\<forall>v. List.member (scc_component state) v \<longrightarrow> v |\<notin>| initial_visited"
    and new_comp: "\<forall>v. v |\<in>| scc_visited state \<and> v |\<notin>| initial_visited \<longrightarrow>
                        List.member (scc_component state) v"
    and comp_distinct: "distinct (scc_component state)"
    using assms(2) unfolding scc_state_valid_def by blast+
  show ?thesis
  proof (cases rule: collect_scc_step_cases[OF stack_vertices, case_names empty skip visit])
    case empty
    then show ?thesis using assms(2) by simp
  next
    case (skip v rest)
    have fields: "scc_visited (collect_scc_step graph state) = scc_visited state"
      "scc_component (collect_scc_step graph state) = scc_component state"
      "scc_stack (collect_scc_step graph state) = rest"
      using skip(3) by simp_all
    have "\<forall>u. List.member rest u \<longrightarrow> has_vertex graph u"
      using skip(1) stack_vertices by (simp add: member_rec(1))
    then show ?thesis
      using visited_vertices comp_visited initial_sub comp_new new_comp comp_distinct
      unfolding scc_state_valid_def fields by blast
  next
    case (visit v rest neighbors)
    have fields: "scc_visited (collect_scc_step graph state) = finsert v (scc_visited state)"
      "scc_component (collect_scc_step graph state) = v # scc_component state"
      "scc_stack (collect_scc_step graph state) = neighbors @ rest"
      using visit(4) by simp_all
    have v_vertex: "has_vertex graph v"
      using visit(1) stack_vertices by (simp add: member_rec(1))
    have neighbors_vertices: "\<forall>u. List.member neighbors u \<longrightarrow> has_vertex graph u"
      using assms(1) visit(3) v_vertex by (metis has_edge.simps option.simps(5) valid_graph.simps)
    have v_not_comp: "\<not> List.member (scc_component state) v"
      using comp_visited visit(2) by blast
    have v_not_initial: "v |\<notin>| initial_visited"
      using initial_sub visit(2) by blast
    show ?thesis
      unfolding scc_state_valid_def fields
    proof (intro conjI)
      show "\<forall>u. u |\<in>| finsert v (scc_visited state) \<longrightarrow> has_vertex graph u"
        using visited_vertices v_vertex by auto
      show "\<forall>u. List.member (v # scc_component state) u \<longrightarrow> u |\<in>| finsert v (scc_visited state)"
        using comp_visited by (auto simp: member_rec(1))
      show "\<forall>u. List.member (neighbors @ rest) u \<longrightarrow> has_vertex graph u"
        using visit(1) stack_vertices neighbors_vertices by (auto simp: member_def)
      show "initial_visited |\<subseteq>| finsert v (scc_visited state)"
        using initial_sub by auto
      show "\<forall>u. List.member (v # scc_component state) u \<longrightarrow> u |\<notin>| initial_visited"
        using comp_new v_not_initial by (auto simp: member_rec(1))
      show "\<forall>u. u |\<in>| finsert v (scc_visited state) \<and> u |\<notin>| initial_visited \<longrightarrow>
                List.member (v # scc_component state) u"
        using new_comp by (auto simp: member_rec(1))
      show "distinct (v # scc_component state)"
        using comp_distinct v_not_comp by (simp add: in_set_member)
    qed
  qed
qed

(* Lemma: collect_scc_step preserves reachability invariant *)
lemma collect_scc_step_preserves_reachability:
  assumes "scc_state_valid graph initial_visited start state"
    and "scc_reachability_inv graph initial_visited start state"
  shows "scc_reachability_inv graph initial_visited start (collect_scc_step graph state)"
proof -
  have stack_vertices: "\<forall>v. List.member (scc_stack state) v \<longrightarrow> has_vertex graph v"
    using assms(1) unfolding scc_state_valid_def by blast
  show ?thesis
  proof (cases rule: collect_scc_step_cases[OF stack_vertices, case_names empty skip visit])
    case empty
    then show ?thesis using assms(2) by simp
  next
    case (skip v rest)
    then show ?thesis
      using assms(2) unfolding scc_reachability_inv_def by (auto simp: member_def)
  next
    case (visit v rest neighbors)
    have v_reachable: "reachable graph start v"
      using assms(2) visit(1) unfolding scc_reachability_inv_def by (simp add: member_rec(1))
    (* All neighbors of v are reachable from start via v *)
    have neighbors_reachable: "\<forall>u. List.member neighbors u \<longrightarrow> reachable graph start u"
    proof (intro allI impI)
      fix u
      assume "List.member neighbors u"
      then have "has_edge graph v u"
        using visit(3) by simp
      then show "reachable graph start u"
        using v_reachable by (simp add: reachable.reachable_step)
    qed
    have fields: "scc_component (collect_scc_step graph state) = v # scc_component state"
      "scc_stack (collect_scc_step graph state) = neighbors @ rest"
      using visit(4) by simp_all
    show ?thesis
      unfolding scc_reachability_inv_def fields
    proof (intro conjI)
      show "\<forall>u. List.member (v # scc_component state) u \<longrightarrow> reachable graph start u"
        using assms(2) v_reachable unfolding scc_reachability_inv_def
        by (auto simp: member_rec(1))
      show "\<forall>u. List.member (neighbors @ rest) u \<longrightarrow> reachable graph start u"
        using visit(1) assms(2) neighbors_reachable unfolding scc_reachability_inv_def
        by (auto simp: member_def)
    qed
  qed
qed

(* Lemma: collect_scc_step preserves soundness invariant *)
lemma collect_scc_step_preserves_soundness:
  assumes "scc_state_valid graph initial_visited start state"
    and "scc_reachability_inv graph initial_visited start state"
    and "scc_soundness_inv graph initial_visited start state"
    and downstream_visited:
        "(\<forall>w. has_vertex graph w \<and> reachable graph start w \<and> \<not>(in_same_scc graph w start) \<longrightarrow>
              w |\<in>| initial_visited)"
  shows "scc_soundness_inv graph initial_visited start (collect_scc_step graph state)"
proof -
  have stack_vertices: "\<forall>v. List.member (scc_stack state) v \<longrightarrow> has_vertex graph v"
    using assms(1) unfolding scc_state_valid_def by blast
  show ?thesis
  proof (cases rule: collect_scc_step_cases[OF stack_vertices, case_names empty skip visit])
    case empty
    then show ?thesis using assms(3) by simp
  next
    case (skip v rest)
    then show ?thesis
      using assms(3) unfolding scc_soundness_inv_def by simp
  next
    case (visit v rest neighbors)
    (* The newly visited v is reachable from start but not initially visited,
       so by downstream_visited it must be in the same SCC as start *)
    have "has_vertex graph v"
      using stack_vertices visit(1) by (simp add: member_rec(1))
    moreover have "reachable graph start v"
      using assms(2) visit(1) unfolding scc_reachability_inv_def by (simp add: member_rec(1))
    moreover have "v |\<notin>| initial_visited"
      using assms(1) visit(2) unfolding scc_state_valid_def by blast
    ultimately have "in_same_scc graph v start"
      using downstream_visited by blast
    then show ?thesis
      using assms(3) visit(4) unfolding scc_soundness_inv_def by auto
  qed
qed

(* Lemma: collect_scc_step preserves completeness invariant *)
lemma collect_scc_step_preserves_completeness:
  assumes "scc_state_valid graph initial_visited start state"
    and "scc_completeness_inv graph initial_visited start state"
  shows "scc_completeness_inv graph initial_visited start (collect_scc_step graph state)"
proof -
  have stack_vertices: "\<forall>v. List.member (scc_stack state) v \<longrightarrow> has_vertex graph v"
    using assms(1) unfolding scc_state_valid_def by blast
  show ?thesis
  proof (cases rule: collect_scc_step_cases[OF stack_vertices, case_names empty skip visit])
    case empty
    then show ?thesis using assms(2) by simp
  next
    case (skip v rest)
    show ?thesis
      unfolding scc_completeness_inv_def
    proof (intro allI impI)
      fix x
      assume "has_vertex graph x \<and> reachable graph start x \<and>
              x |\<notin>| scc_visited (collect_scc_step graph state)"
      then obtain w where w_stack: "List.member (scc_stack state) w"
        and w_path: "unvisited_path graph (scc_visited state) w x"
        using assms(2) skip(3) unfolding scc_completeness_inv_def by auto
      (* w is unvisited, so it is not the (visited) v that was popped *)
      have "w \<noteq> v"
        using unvisited_path_start_unvisited[OF w_path] skip(2) by blast
      then have "List.member rest w"
        using w_stack skip(1) by (simp add: member_rec(1))
      then show "\<exists>w. List.member (scc_stack (collect_scc_step graph state)) w \<and>
                     unvisited_path graph (scc_visited (collect_scc_step graph state)) w x"
        using w_path skip(3) by auto
    qed
  next
    case (visit v rest neighbors)
    show ?thesis
      unfolding scc_completeness_inv_def
    proof (intro allI impI)
      fix x
      assume x_props: "has_vertex graph x \<and> reachable graph start x \<and>
                       x |\<notin>| scc_visited (collect_scc_step graph state)"
      then have x_unvisited: "x |\<notin>| finsert v (scc_visited state)"
        using visit(4) by simp
      then obtain w where w_stack: "List.member (scc_stack state) w"
        and w_path: "unvisited_path graph (scc_visited state) w x"
        using x_props assms(2) unfolding scc_completeness_inv_def by auto
      have "x \<noteq> v"
        using x_unvisited by simp
      (* Either the path from w avoids v, or its part after v starts at a neighbor of v *)
      from unvisited_path_finsert[OF w_path this]
      show "\<exists>w. List.member (scc_stack (collect_scc_step graph state)) w \<and>
                unvisited_path graph (scc_visited (collect_scc_step graph state)) w x"
      proof
        assume path: "unvisited_path graph (finsert v (scc_visited state)) w x"
        have "w \<noteq> v"
          using unvisited_path_start_unvisited[OF path] by simp
        then have "List.member rest w"
          using w_stack visit(1) by (simp add: member_rec(1))
        then show ?thesis
          using path visit(4) by (auto simp: member_def)
      next
        assume "\<exists>n. has_edge graph v n \<and> unvisited_path graph (finsert v (scc_visited state)) n x"
        then obtain n where edge: "has_edge graph v n"
          and path: "unvisited_path graph (finsert v (scc_visited state)) n x"
          by blast
        have "List.member neighbors n"
          using visit(3) edge by simp
        then show ?thesis
          using path visit(4) by (auto simp: member_def)
      qed
    qed
  qed
qed

(* Lemma: collect_scc_step preserves all the invariants *)
lemma collect_scc_step_preserves_inv:
  assumes "valid_graph graph"
    and downstream_visited:
        "(\<forall>w. has_vertex graph w \<and> reachable graph start w \<and> \<not>(in_same_scc graph w start) \<longrightarrow>
              w |\<in>| initial_visited)"
    and "scc_inv graph initial_visited start state"
  shows "scc_inv graph initial_visited start (collect_scc_step graph state)"
  using assms(3)
    collect_scc_step_preserves_valid[OF assms(1)]
    collect_scc_step_preserves_reachability
    collect_scc_step_preserves_soundness[OF _ _ _ downstream_visited]
    collect_scc_step_preserves_completeness
  unfolding scc_inv_def by blast


(*-----------------------------------------------------------------------------*)
(* collect_scc_run: Runs collect_scc_step until one whole SCC is collected *)
(*-----------------------------------------------------------------------------*)

(* Run DFS until the stack is empty *)
function collect_scc_run :: "('a::linorder) Graph \<Rightarrow> 'a scc_state \<Rightarrow> 'a scc_state" where
  "collect_scc_run graph state =
    (if scc_stack state = []
     then state
     else collect_scc_run graph (collect_scc_step graph state))"
  by pat_completeness auto

(* Termination proof: we use a lexicographic measure on (unvisited vertices, stack length) *)
termination collect_scc_run
proof (relation "measures [\<lambda>(graph,state). fcard (fmdom graph |-| scc_visited state),
                           \<lambda>(graph,state). length (scc_stack state)]")
  show "wf (measures [\<lambda>(graph,state). fcard (fmdom graph |-| scc_visited state),
                      \<lambda>(graph,state). length (scc_stack state)])"
    by auto
next
  fix graph :: "('a::linorder) Graph" and state :: "'a scc_state"
  assume "\<not> scc_stack state = []"
  then obtain v rest where stack: "scc_stack state = v # rest"
    by (cases "scc_stack state") auto
  show "((graph, collect_scc_step graph state), (graph, state))
        \<in> measures [\<lambda>(graph,state). fcard (fmdom graph |-| scc_visited state),
                    \<lambda>(graph,state). length (scc_stack state)]"
  proof (cases "v |\<in>| scc_visited state")
    case True
    (* v already visited - the stack shrinks *)
    then show ?thesis using stack by simp
  next
    case False
    show ?thesis
    proof (cases "fmlookup graph v")
      case None
      (* v not in graph - the stack is cleared *)
      then show ?thesis using stack False by simp
    next
      case (Some neighbors)
      (* v gets visited - the number of unvisited vertices shrinks *)
      then have "v |\<in>| fmdom graph"
        by (rule fmdomI)
      then have "fcard (fmdom graph |-| finsert v (scc_visited state))
                   < fcard (fmdom graph |-| scc_visited state)"
        using False by (rule fcard_fminus_finsert_less)
      then show ?thesis using stack False Some by simp
    qed
  qed
qed

(*-----------------------------------------------------------------------------*)
(* Basic Lemmas about collect_scc_run *)
(*-----------------------------------------------------------------------------*)

(* Lemma: collect_scc_run returns a state with empty stack *)
lemma collect_scc_run_stack_empty:
  assumes "final = collect_scc_run graph state"
  shows "scc_stack final = []"
  using assms
proof (induction graph state rule: collect_scc_run.induct)
  case (1 graph state)
  then show ?case
    by (metis collect_scc_run.elims)
qed

(* Lemma: collect_scc_run preserves any invariant preserved by collect_scc_step *)
lemma collect_scc_run_invariant:
  assumes "P state"
    and "\<And>s. P s \<Longrightarrow> scc_stack s \<noteq> [] \<Longrightarrow> P (collect_scc_step graph s)"
  shows "P (collect_scc_run graph state)"
  using assms
proof (induction graph state rule: collect_scc_run.induct)
  case (1 graph state)
  show ?case
  proof (cases "scc_stack state = []")
    case True
    then show ?thesis using "1.prems"(1) by simp
  next
    case False
    have "P (collect_scc_step graph state)"
      using "1.prems" False by blast
    then have "P (collect_scc_run graph (collect_scc_step graph state))"
      using "1.IH" "1.prems"(2) False by blast
    then show ?thesis
      using False by (simp only: collect_scc_run.simps[of graph state] if_False)
  qed
qed

(* Lemma: collect_scc_run preserves all the invariants *)
lemma collect_scc_run_preserves_inv:
  assumes "valid_graph graph"
    and downstream_visited:
        "(\<forall>w. has_vertex graph w \<and> reachable graph start w \<and> \<not>(in_same_scc graph w start) \<longrightarrow>
              w |\<in>| initial_visited)"
    and "scc_inv graph initial_visited start state"
  shows "scc_inv graph initial_visited start (collect_scc_run graph state)"
  by (rule collect_scc_run_invariant[where P = "scc_inv graph initial_visited start", OF assms(3)])
     (rule collect_scc_step_preserves_inv[OF assms(1) downstream_visited])

(*-----------------------------------------------------------------------------*)
(* collect_one_scc: Uses collect_scc_run to collect one SCC *)
(*-----------------------------------------------------------------------------*)

(* Collect one SCC given a visited-set and a starting vertex.
   Returns (scc, new_visited) where scc is the collected component
   and new_visited is the updated visited set. *)
definition collect_one_scc :: "('a::linorder) Graph \<Rightarrow> 'a fset \<Rightarrow> 'a \<Rightarrow> ('a list \<times> 'a fset)" where
  "collect_one_scc graph visited start =
    (let initial_state = \<lparr> scc_visited = visited, scc_component = [], scc_stack = [start] \<rparr>;
         final_state = collect_scc_run graph initial_state
     in (scc_component final_state, scc_visited final_state))"

(*-----------------------------------------------------------------------------*)
(* Correctness Properties for collect_one_scc *)
(*-----------------------------------------------------------------------------*)

(* collect_one_scc invariants are true in the initial state *)
lemma collect_one_scc_initial_invariants:
  assumes "valid_graph graph"
    and "has_vertex graph start"
    and "\<forall>w |\<in>| visited. has_vertex graph w"
    and "state = \<lparr> scc_visited = visited, scc_component = [], scc_stack = [start] \<rparr>"
    and downstream_visited:
        "(\<forall>w. has_vertex graph w \<and> reachable graph start w \<and> \<not>(in_same_scc graph w start) \<longrightarrow>
              w |\<in>| visited)"
    and scc_unvisited:
        "(\<forall>w. has_vertex graph w \<and> in_same_scc graph w start \<longrightarrow> w |\<notin>| visited)"
  shows "scc_inv graph visited start state"
  unfolding scc_inv_def
proof (intro conjI)
  show "scc_state_valid graph visited start state"
    unfolding scc_state_valid_def assms(4)
    by (metis assms(2,3) distinct.simps(1) member_rec(1,2) order_refl scc_state.select_convs(1,2,3))

  show "scc_reachability_inv graph visited start state"
    unfolding scc_reachability_inv_def assms(4)
    using assms(2) by (simp add: member_rec(1) member_rec(2) reachable.reachable_refl)

  show "scc_soundness_inv graph visited start state"
    unfolding scc_soundness_inv_def assms(4) by simp

  show "scc_completeness_inv graph visited start state"
  proof -
    {
      fix w
      assume w_props: "has_vertex graph w \<and> reachable graph start w \<and> w |\<notin>| visited"

      (* w is unvisited and reachable from start *)
      (* By downstream_visited, w must be in the same SCC as start *)
      have w_same_scc: "in_same_scc graph w start"
        using w_props downstream_visited by blast

      (* Since w is reachable from start, there's some path *)
      then obtain path where path_props:
        "valid_path graph path"
        "path_start path = start"
        "path_end path = w"
        using assms(1) reachable_implies_valid_path w_props by blast

      (* By path_in_scc_all_in_scc, all vertices on the path are in the same SCC as start *)
      have "\<forall>v. v \<in> set path \<longrightarrow> in_same_scc graph v start"
        using path_in_scc_all_in_scc[OF assms(1) path_props(1)] w_same_scc path_props(3)
        using in_same_scc_sym path_props(2) by blast

      (* By scc_unvisited, all vertices in the same SCC as start are unvisited *)
      then have "\<forall>v. v \<in> set path \<longrightarrow> v |\<notin>| visited"
        using scc_unvisited in_same_scc_vertices(1)[OF assms(1)] by blast

      (* Therefore the path is all unvisited *)
      then have "all_unvisited visited path"
        by (simp add: in_set_member)

      (* So there's an unvisited path from start to w *)
      then have "unvisited_path graph visited start w"
        using valid_path_implies_unvisited_path[OF assms(1) path_props(1)]
              path_props(2,3) by simp

      (* And start is on the stack *)
      then have "\<exists>u. List.member [start] u \<and> unvisited_path graph visited start w"
        by (meson member_rec(1))
    }
    thus ?thesis
      by (metis assms(4) member_rec(1) scc_completeness_inv_def
          scc_state.select_convs(1,3))
  qed
qed

(* Correctness of collect_one_scc: provided all "downstream" SCCs have already been
   visited, and start's own SCC is unvisited, collect_one_scc collects exactly start's
   SCC (without duplicates), and adds it to the visited set *)
lemma collect_one_scc_correct:
  assumes valid: "valid_graph graph"
    and start_vertex: "has_vertex graph start"
    and visited_vertices: "\<forall>w |\<in>| visited. has_vertex graph w"
    and scc_unvisited:
        "(\<forall>w. has_vertex graph w \<and> in_same_scc graph w start \<longrightarrow> w |\<notin>| visited)"
    and downstream_visited:
        "(\<forall>w. has_vertex graph w \<and> reachable graph start w \<and> \<not>(in_same_scc graph w start) \<longrightarrow>
              w |\<in>| visited)"
    and res: "collect_one_scc graph visited start = (scc, new_visited)"
  shows "set scc = {u. has_vertex graph u \<and> in_same_scc graph u start}"
    and "distinct scc"
    and "new_visited = visited |\<union>| fset_of_list scc"
proof -
  define initial_state where "initial_state = \<lparr> scc_visited = visited,
                                                 scc_component = [],
                                                 scc_stack = [start] \<rparr>"
  define final_state where "final_state = collect_scc_run graph initial_state"

  have "collect_one_scc graph visited start = (scc_component final_state, scc_visited final_state)"
    unfolding collect_one_scc_def initial_state_def final_state_def by (simp add: Let_def)
  then have scc_eq: "scc = scc_component final_state"
    and new_eq: "new_visited = scc_visited final_state"
    using res by auto

  (* The invariants hold in the final state, whose stack is empty *)
  have "scc_inv graph visited start initial_state"
    by (rule collect_one_scc_initial_invariants[OF valid start_vertex visited_vertices
          initial_state_def downstream_visited scc_unvisited])
  then have "scc_inv graph visited start final_state"
    unfolding final_state_def by (rule collect_scc_run_preserves_inv[OF valid downstream_visited])
  then have final_valid: "scc_state_valid graph visited start final_state"
    and final_sound: "scc_soundness_inv graph visited start final_state"
    and final_complete: "scc_completeness_inv graph visited start final_state"
    unfolding scc_inv_def by blast+
  have stack_empty: "scc_stack final_state = []"
    using final_state_def collect_scc_run_stack_empty by blast

  (* By completeness (and the empty stack), all of start's SCC is visited at the end *)
  have all_visited: "u |\<in>| scc_visited final_state"
    if u_vertex: "has_vertex graph u" and u_scc: "in_same_scc graph u start" for u
  proof (rule ccontr)
    assume "u |\<notin>| scc_visited final_state"
    then obtain w where "List.member (scc_stack final_state) w"
      using final_complete u_vertex u_scc unfolding scc_completeness_inv_def in_same_scc.simps
      by blast
    then show False
      using stack_empty by (simp add: member_rec(2))
  qed

  have comp_set: "set (scc_component final_state) = {u. has_vertex graph u \<and> in_same_scc graph u start}"
  proof (intro set_eqI iffI)
    fix u
    assume "u \<in> set (scc_component final_state)"
    then have "u |\<in>| scc_visited final_state" "u |\<notin>| visited" "has_vertex graph u"
      using final_valid unfolding scc_state_valid_def in_set_member by blast+
    then show "u \<in> {u. has_vertex graph u \<and> in_same_scc graph u start}"
      using final_sound unfolding scc_soundness_inv_def by blast
  next
    fix u
    assume "u \<in> {u. has_vertex graph u \<and> in_same_scc graph u start}"
    then have "u |\<in>| scc_visited final_state" "u |\<notin>| visited"
      using all_visited scc_unvisited by blast+
    then show "u \<in> set (scc_component final_state)"
      using final_valid unfolding scc_state_valid_def in_set_member by blast
  qed

  have comp_distinct: "distinct (scc_component final_state)"
    using final_valid unfolding scc_state_valid_def by blast

  have visited_eq: "scc_visited final_state = visited |\<union>| fset_of_list (scc_component final_state)"
  proof (rule fset_eqI)
    fix u
    have "u |\<in>| visited |\<union>| fset_of_list (scc_component final_state) \<longleftrightarrow>
          u |\<in>| visited \<or> List.member (scc_component final_state) u"
      by (simp add: fset_of_list_elem in_set_member)
    then show "u |\<in>| scc_visited final_state \<longleftrightarrow>
               u |\<in>| visited |\<union>| fset_of_list (scc_component final_state)"
      using final_valid unfolding scc_state_valid_def by blast
  qed

  show "set scc = {u. has_vertex graph u \<and> in_same_scc graph u start}"
    using comp_set scc_eq by simp
  show "distinct scc"
    using comp_distinct scc_eq by simp
  show "new_visited = visited |\<union>| fset_of_list scc"
    using visited_eq new_eq scc_eq by simp
qed

end
