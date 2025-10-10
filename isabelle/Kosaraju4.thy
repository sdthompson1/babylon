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

(*-----------------------------------------------------------------------------*)
(* Basic Lemmas about collect_scc_step *)
(*-----------------------------------------------------------------------------*)

(* Lemma: visited set never shrinks during collect_scc_step *)
lemma collect_scc_step_visited_monotonic:
  "scc_visited state |\<subseteq>| scc_visited (collect_scc_step graph state)"
proof (cases "scc_stack state")
  case Nil
  then show ?thesis by simp
next
  case (Cons v rest)
  then show ?thesis
  proof (cases "v |\<in>| scc_visited state")
    case True
    then show ?thesis using Cons by auto
  next
    case False
    then show ?thesis proof (cases "fmlookup graph v")
      case None
      then show ?thesis using False Cons by auto
    next
      case (Some a)
      then show ?thesis using False Cons by auto
    qed
  qed
qed

(* Lemma: current component never shrinks during collect_scc_step *)
lemma collect_scc_step_current_grows:
  "set (scc_component state) \<subseteq> set (scc_component (collect_scc_step graph state))"
proof (cases "scc_stack state")
  case Nil
  then show ?thesis by simp
next
  case (Cons v rest)
  then show ?thesis
  proof (cases "v |\<in>| scc_visited state")
    case True
    then show ?thesis using Cons by auto
  next
    case False
    then show ?thesis proof (cases "fmlookup graph v")
      case None
      then show ?thesis using Cons False by auto
    next
      case (Some a)
      then show ?thesis using Cons False by auto
    qed
  qed
qed

(*-----------------------------------------------------------------------------*)
(* Invariant Preservation Lemmas for collect_scc_step *)
(*-----------------------------------------------------------------------------*)

(* Lemma: collect_scc_step preserves validity *)
lemma collect_scc_step_preserves_valid:
  assumes "valid_graph graph"
    and "scc_state_valid graph initial_visited start state"
    and "scc_reachability_inv graph initial_visited start state"
  shows "scc_state_valid graph initial_visited start (collect_scc_step graph state)"
proof -
  define state' where "state' = collect_scc_step graph state"

  (* We need to show all seven parts of scc_state_valid *)
  have "(\<forall>v. v |\<in>| scc_visited state' \<longrightarrow> has_vertex graph v) \<and>
        (\<forall>v. List.member (scc_component state') v \<longrightarrow> v |\<in>| scc_visited state') \<and>
        (\<forall>v. List.member (scc_stack state') v \<longrightarrow> has_vertex graph v) \<and>
        (initial_visited |\<subseteq>| scc_visited state') \<and>
        (\<forall>v. List.member (scc_component state') v \<longrightarrow> v |\<notin>| initial_visited) \<and>
        (\<forall>v. v |\<in>| scc_visited state' \<and> v |\<notin>| initial_visited \<longrightarrow> List.member (scc_component state') v) \<and>
        distinct (scc_component state')"
  proof (cases "scc_stack state")
    case Nil
    (* Empty stack: state unchanged *)
    then have "state' = state"
      using state'_def by simp
    then show ?thesis
      using assms(2) unfolding scc_state_valid_def by blast
  next
    case (Cons v rest)
    then show ?thesis
    proof (cases "v |\<in>| scc_visited state")
      case True
      (* v already visited: just pop stack *)
      then have "state' = state \<lparr> scc_stack := rest \<rparr>"
        using state'_def Cons by simp
      then show ?thesis
        using assms(2) unfolding scc_state_valid_def
        by (metis (no_types, lifting) local.Cons member_rec(1) scc_state.ext_inject
            scc_state.surjective scc_state.update_convs(3))
    next
      case False
      (* v not visited *)
      (* First show that v must be in the graph *)
      have v_on_stack: "List.member (scc_stack state) v"
        using Cons by (simp add: member_rec(1))

      have v_in_graph: "has_vertex graph v"
        using assms(2) v_on_stack unfolding scc_state_valid_def
        by blast 

      (* Therefore fmlookup graph v must be Some neighbors *)
      then obtain neighbors where neighbors_def: "fmlookup graph v = Some neighbors"
        by (metis fmdom_notI has_vertex.elims(2) not_None_eq)

      (* v in graph: visit it *)
      have state'_eq: "state' = state \<lparr> scc_visited := finsert v (scc_visited state),
                                        scc_component := v # (scc_component state),
                                        scc_stack := neighbors @ rest \<rparr>"
        using state'_def Cons False neighbors_def by simp

      (* Extract properties from assumptions *)
      have stack_valid: "\<forall>u. List.member (scc_stack state) u \<longrightarrow> has_vertex graph u"
        using assms(2) unfolding scc_state_valid_def by blast

      have neighbors_valid: "\<forall>u. List.member neighbors u \<longrightarrow> has_vertex graph u"
        using assms(1) neighbors_def v_in_graph by (metis has_edge.simps option.simps(5) valid_graph.simps)

      (* Now prove each part *)
      have part1: "\<forall>u. u |\<in>| scc_visited state' \<longrightarrow> has_vertex graph u"
      proof (intro allI impI)
        fix u assume "u |\<in>| scc_visited state'"
        then have "u = v \<or> u |\<in>| scc_visited state"
          using state'_eq by auto
        then show "has_vertex graph u"
          using v_in_graph assms(2) unfolding scc_state_valid_def by blast
      qed

      have part2: "\<forall>u. List.member (scc_component state') u \<longrightarrow> u |\<in>| scc_visited state'"
      proof (intro allI impI)
        fix u assume "List.member (scc_component state') u"
        then have "u = v \<or> List.member (scc_component state) u"
          using state'_eq
          by (metis member_rec(1) scc_state.select_convs(2) scc_state.surjective
              scc_state.update_convs(2,3)) 
        then show "u |\<in>| scc_visited state'"
          using state'_eq assms(2) unfolding scc_state_valid_def
          by (metis collect_scc_step_visited_monotonic finsertI1 fsubsetD scc_state.select_convs(1)
              scc_state.surjective scc_state.update_convs(1,2,3) state'_def)
      qed

      have part3: "\<forall>u. List.member (scc_stack state') u \<longrightarrow> has_vertex graph u"
      proof (intro allI impI)
        fix u assume "List.member (scc_stack state') u"
        then have "List.member neighbors u \<or> List.member rest u"
          using state'_eq
          by (metis list_membership_lemma scc_state.select_convs(3) scc_state.surjective
              scc_state.update_convs(3)) 
        then show "has_vertex graph u"
          using neighbors_valid stack_valid Cons
          by (metis member_rec(1))
      qed

      have part4: "initial_visited |\<subseteq>| scc_visited state'"
        using state'_eq assms(2) unfolding scc_state_valid_def by auto

      have part5: "\<forall>u. List.member (scc_component state') u \<longrightarrow> u |\<notin>| initial_visited"
      proof (intro allI impI)
        fix u assume "List.member (scc_component state') u"
        then have "u = v \<or> List.member (scc_component state) u"
          using state'_eq
          by (metis member_rec(1) scc_state.select_convs(2) scc_state.surjective
              scc_state.update_convs(2,3))
        then show "u |\<notin>| initial_visited"
        proof
          assume "u = v"
          then show "u |\<notin>| initial_visited"
            using False assms(2) unfolding scc_state_valid_def by blast
        next
          assume "List.member (scc_component state) u"
          then show "u |\<notin>| initial_visited"
            using assms(2) unfolding scc_state_valid_def by blast
        qed
      qed

      have part6: "\<forall>u. u |\<in>| scc_visited state' \<and> u |\<notin>| initial_visited \<longrightarrow> List.member (scc_component state') u"
      proof (intro allI impI)
        fix u assume "u |\<in>| scc_visited state' \<and> u |\<notin>| initial_visited"
        then have u_visited: "u |\<in>| scc_visited state'" and u_not_initial: "u |\<notin>| initial_visited" by auto
        then have "u = v \<or> u |\<in>| scc_visited state"
          using state'_eq by auto
        then show "List.member (scc_component state') u"
        proof
          assume "u = v"
          then show "List.member (scc_component state') u"
            using state'_eq by (simp add: member_rec(1))
        next
          assume "u |\<in>| scc_visited state"
          then have "List.member (scc_component state) u"
            using u_not_initial assms(2) unfolding scc_state_valid_def by auto
          then show "List.member (scc_component state') u"
            using state'_eq
            by (metis collect_scc_step_current_grows in_set_member state'_def subsetD)
        qed
      qed

      have part7: "distinct (scc_component state')"
      proof -
        have "distinct (scc_component state)"
          using assms(2) unfolding scc_state_valid_def by simp
        moreover have "v \<notin> set (scc_component state)"
          using False assms(2) unfolding scc_state_valid_def
          by (metis in_set_member)
        ultimately show ?thesis
          using state'_eq by simp
      qed

      then show ?thesis
        using part1 part2 part3 part4 part5 part6 part7
        by (meson assms(2) scc_state_valid_def) 
    qed
  qed

  then show ?thesis
    using scc_state_valid_def state'_def by blast
qed

(* Lemma: collect_scc_step preserves reachability invariant *)
lemma collect_scc_step_preserves_reachability:
  assumes "valid_graph graph"
    and "scc_state_valid graph initial_visited start state"
    and "scc_reachability_inv graph initial_visited start state"
  shows "scc_reachability_inv graph initial_visited start (collect_scc_step graph state)"
proof -
  define state' where "state' = collect_scc_step graph state"

  (* We need to show both parts of scc_reachability_inv *)
  have "(\<forall>v. List.member (scc_component state') v \<longrightarrow> reachable graph start v) \<and>
        (\<forall>v. List.member (scc_stack state') v \<longrightarrow> reachable graph start v)"
  proof (cases "scc_stack state")
    case Nil
    (* Empty stack: state unchanged *)
    then have "state' = state"
      using state'_def by simp
    then show ?thesis
      using assms(3) unfolding scc_reachability_inv_def by simp
  next
    case (Cons v rest)
    then show ?thesis
    proof (cases "v |\<in>| scc_visited state")
      case True
      (* v already visited: just pop stack *)
      then have "state' = state \<lparr> scc_stack := rest \<rparr>"
        using state'_def Cons by simp
      then show ?thesis
        using assms(3) unfolding scc_reachability_inv_def
        by (simp add: local.Cons member_rec(1))
    next
      case False
      (* v not visited *)
      (* First show that v must be in the graph *)
      have v_on_stack: "List.member (scc_stack state) v"
        using Cons by (simp add: member_rec(1))

      have v_in_graph: "has_vertex graph v"
        using assms(2) v_on_stack unfolding scc_state_valid_def by blast

      (* Therefore fmlookup graph v must be Some neighbors *)
      then obtain neighbors where neighbors_def: "fmlookup graph v = Some neighbors"
        by (metis fmdom_notI has_vertex.elims(2) not_None_eq)

      (* v in graph: visit it *)
      have state'_eq: "state' = state \<lparr> scc_visited := finsert v (scc_visited state),
                                        scc_component := v # (scc_component state),
                                        scc_stack := neighbors @ rest \<rparr>"
        using state'_def Cons False neighbors_def by simp

      (* v is reachable from start (by reachability inv) *)
      have v_reachable: "reachable graph start v"
        using assms(3) v_on_stack unfolding scc_reachability_inv_def by simp

      (* All neighbors of v are reachable from start via v *)
      have neighbors_reachable: "\<forall>u. List.member neighbors u \<longrightarrow> reachable graph start u"
      proof (intro allI impI)
        fix u assume "List.member neighbors u"
        then have "has_edge graph v u"
          using neighbors_def by simp
        then show "reachable graph start u"
          using v_reachable by (simp add: reachable.reachable_step)
      qed

      (* All elements of rest are reachable from start (by reachability inv) *)
      have rest_reachable: "\<forall>u. List.member rest u \<longrightarrow> reachable graph start u"
        using assms(3) Cons unfolding scc_reachability_inv_def
        by (simp add: member_rec(1))

      (* Now prove both parts *)
      have part1: "\<forall>u. List.member (scc_component state') u \<longrightarrow> reachable graph start u"
      proof (intro allI impI)
        fix u assume "List.member (scc_component state') u"
        then have "u = v \<or> List.member (scc_component state) u"
          using state'_eq
          by (metis member_rec(1) scc_state.select_convs(2) scc_state.surjective
              scc_state.update_convs(2,3))
        then show "reachable graph start u"
          using v_reachable assms(3) unfolding scc_reachability_inv_def by auto
      qed

      have part2: "\<forall>u. List.member (scc_stack state') u \<longrightarrow> reachable graph start u"
      proof (intro allI impI)
        fix u assume "List.member (scc_stack state') u"
        then have "List.member neighbors u \<or> List.member rest u"
          using state'_eq
          by (metis list_membership_lemma scc_state.select_convs(3) scc_state.surjective
              scc_state.update_convs(3))
        then show "reachable graph start u"
          using neighbors_reachable rest_reachable by blast
      qed

      show ?thesis
        using part1 part2 by blast
    qed
  qed

  then show ?thesis
    using state'_def unfolding scc_reachability_inv_def by simp
qed

(* Lemma: collect_scc_step preserves soundness invariant *)
lemma collect_scc_step_preserves_soundness:
  assumes "valid_graph graph"
    and "scc_state_valid graph initial_visited start state"
    and "scc_reachability_inv graph initial_visited start state"
    and "scc_soundness_inv graph initial_visited start state"
    and downstream_visited:
        "(\<forall>w. has_vertex graph w \<and> reachable graph start w \<and> \<not>(in_same_scc graph w start) \<longrightarrow>
              w |\<in>| initial_visited)"
  shows "scc_soundness_inv graph initial_visited start (collect_scc_step graph state)"
proof -
  define state' where "state' = collect_scc_step graph state"

  (* We need to show all newly visited vertices are in the same SCC as start *)
  have "\<forall>v. v |\<in>| scc_visited state' \<and> v |\<notin>| initial_visited \<longrightarrow> in_same_scc graph v start"
  proof (cases "scc_stack state")
    case Nil
    (* Empty stack: state unchanged *)
    then have "state' = state"
      using state'_def by simp
    then show ?thesis
      using assms(4) unfolding scc_soundness_inv_def by simp
  next
    case (Cons v rest)
    then show ?thesis
    proof (cases "v |\<in>| scc_visited state")
      case True
      (* v already visited: just pop stack *)
      then have "state' = state \<lparr> scc_stack := rest \<rparr>"
        using state'_def Cons by simp
      then show ?thesis
        using assms(4) unfolding scc_soundness_inv_def by simp
    next
      case False
      (* v not visited *)
      (* First show that v must be in the graph *)
      have v_on_stack: "List.member (scc_stack state) v"
        using Cons by (simp add: member_rec(1))

      have v_in_graph: "has_vertex graph v"
        using assms(2) v_on_stack unfolding scc_state_valid_def by blast

      (* Therefore fmlookup graph v must be Some neighbors *)
      then obtain neighbors where neighbors_def: "fmlookup graph v = Some neighbors"
        by (metis fmdom_notI has_vertex.elims(2) not_None_eq)

      (* v in graph: visit it *)
      have state'_eq: "state' = state \<lparr> scc_visited := finsert v (scc_visited state),
                                        scc_component := v # (scc_component state),
                                        scc_stack := neighbors @ rest \<rparr>"
        using state'_def Cons False neighbors_def by simp

      (* v is reachable from start (by reachability inv) *)
      have v_reachable: "reachable graph start v"
        using assms(3) v_on_stack unfolding scc_reachability_inv_def by simp

      (* The key: show that v is in the same SCC as start *)
      have v_same_scc: "in_same_scc graph v start"
      proof -
        (* v is reachable from start, so we need to show start is reachable from v *)
        (* We know v is not in initial_visited (since it's not visited at all) *)
        have "v |\<notin>| initial_visited"
          using False assms(2) unfolding scc_state_valid_def by blast

        (* If v is not in the same SCC as start, then by downstream_visited,
           v would be in initial_visited - contradiction *)
        have "v |\<notin>| initial_visited \<and> reachable graph start v \<and> has_vertex graph v"
          using \<open>v |\<notin>| initial_visited\<close> v_reachable v_in_graph by simp

        then show "in_same_scc graph v start"
          using downstream_visited by blast
      qed

      (* Now show the invariant holds for state' *)
      show ?thesis
      proof (intro allI impI)
        fix u
        assume u_visited: "u |\<in>| scc_visited state' \<and> u |\<notin>| initial_visited"

        (* u is either v (newly visited) or was visited before *)
        have "u = v \<or> u |\<in>| scc_visited state"
          using u_visited state'_eq by auto

        then show "in_same_scc graph u start"
        proof
          assume "u = v"
          then show "in_same_scc graph u start"
            using v_same_scc by simp
        next
          assume "u |\<in>| scc_visited state"
          then show "in_same_scc graph u start"
            using u_visited assms(4) unfolding scc_soundness_inv_def by simp
        qed
      qed
    qed
  qed

  then show ?thesis
    using state'_def unfolding scc_soundness_inv_def by simp
qed

(* Lemma: collect_scc_step preserves completeness invariant *)
lemma collect_scc_step_preserves_completeness:
  assumes "valid_graph graph"
    and "scc_state_valid graph initial_visited start state"
    and "scc_reachability_inv graph initial_visited start state"
    and "scc_completeness_inv graph initial_visited start state"
  shows "scc_completeness_inv graph initial_visited start (collect_scc_step graph state)"
proof -
  define state' where "state' = collect_scc_step graph state"

  (* We need to show all unvisited reachable vertices have unvisited paths from stack *)
  have "\<forall>v. has_vertex graph v \<and> reachable graph start v \<and> v |\<notin>| scc_visited state' \<longrightarrow>
             (\<exists>w. List.member (scc_stack state') w \<and> unvisited_path graph (scc_visited state') w v)"
  proof (cases "scc_stack state")
    case Nil
    (* Empty stack: state unchanged *)
    then have "state' = state"
      using state'_def by simp
    then show ?thesis
      using assms(4) unfolding scc_completeness_inv_def by simp
  next
    case (Cons u rest)
    then show ?thesis
    proof (cases "u |\<in>| scc_visited state")
      case u_visited: True
      (* u already visited: just pop stack *)
      then have "state' = state \<lparr> scc_stack := rest \<rparr>"
        using state'_def Cons by simp

      (* Show completeness still holds *)
      show ?thesis
      proof (intro allI impI)
        fix v
        assume v_props: "has_vertex graph v \<and> reachable graph start v \<and> v |\<notin>| scc_visited state'"
        (* v is still unvisited, so by old completeness, there's a path from old stack *)
        have "v |\<notin>| scc_visited state"
          using v_props \<open>state' = state \<lparr> scc_stack := rest \<rparr>\<close> by simp
        then have "\<exists>w. List.member (scc_stack state) w \<and> unvisited_path graph (scc_visited state) w v"
          using assms(4) v_props unfolding scc_completeness_inv_def by simp
        then obtain w where w_props: "List.member (scc_stack state) w"
                                      "unvisited_path graph (scc_visited state) w v"
          by auto
        (* w is not u, so w is in rest, and the path still works *)
        have "w \<noteq> u"
          using u_visited unvisited_path.simps w_props(2) by blast
        then have "List.member rest w"
          using w_props(1) Cons by (simp add: member_rec(1))
        moreover have "unvisited_path graph (scc_visited state') w v"
          using w_props(2) \<open>state' = state \<lparr> scc_stack := rest \<rparr>\<close> by simp
        ultimately show "(\<exists>w. List.member (scc_stack state') w 
                            \<and> unvisited_path graph (scc_visited state') w v)"
          using \<open>state' = state\<lparr>scc_stack := rest\<rparr>\<close> by auto
      qed

    next
      case u_unvisited: False
      (* u not visited - visit it and add neighbors *)
      have u_on_stack: "List.member (scc_stack state) u"
        using Cons by (simp add: member_rec(1))

      have u_in_graph: "has_vertex graph u"
        using assms(2) u_on_stack unfolding scc_state_valid_def by blast

      then obtain neighbors where neighbors_def: "fmlookup graph u = Some neighbors"
        by (metis fmdom_notI has_vertex.elims(2) not_None_eq)

      have state'_eq: "state' = state \<lparr> scc_visited := finsert u (scc_visited state),
                                        scc_component := u # (scc_component state),
                                        scc_stack := neighbors @ rest \<rparr>"
        using state'_def Cons u_unvisited neighbors_def by simp

      (* Show completeness holds for state' *)
      show ?thesis
      proof (intro allI impI)

        (* Take any v reachable from start, that is unvisited in new state.
           We need to show that there is some w on the new stack, that can
           reach v by an unviisted path. *)
        fix v
        assume v_props: "has_vertex graph v 
              \<and> reachable graph start v 
              \<and> v |\<notin>| scc_visited state'"

        then have "v |\<notin>| scc_visited state"
          using state'_eq by auto

        (* v can't be u, because u is now visited, but v is unvisited *)
        have "v \<noteq> u"
          using v_props state'_eq by auto

        (* By old completeness, there's a path from some w in old stack *)
        have "\<exists>w. List.member (scc_stack state) w \<and> unvisited_path graph (scc_visited state) w v"
          using assms(4) v_props \<open>v |\<notin>| scc_visited state\<close> unfolding scc_completeness_inv_def by simp

        then obtain w where w_props: "List.member (scc_stack state) w"
                                      "unvisited_path graph (scc_visited state) w v"
          by auto

        (* Obtain an explicit path starting on w *)
        obtain path :: "'a list" where
          path_props: "valid_path graph path \<and>
                       path_start path = w \<and>
                       path_end path = v \<and>
                       all_unvisited (scc_visited state) path"
          using unvisited_path_implies_valid_path
          using assms(1) w_props(2) by blast

        (* Either this path contains the newly visited u, or it doesn't *)
        show "(\<exists>w. List.member (scc_stack state') w
                \<and> unvisited_path graph (scc_visited state') w v)"
        proof (cases "List.member path u")
          case path_contains_u: True

          (* The path goes through u, which is now visited *)
          (* Use path_through_v_has_next to get a suffix starting from a neighbor of u *)
          have "\<exists>nxt suffix.
                 has_edge graph u nxt \<and>
                 valid_path graph (nxt # suffix) \<and>
                 path_end (nxt # suffix) = v \<and>
                 \<not>List.member (nxt # suffix) u \<and>
                 (\<forall>x. List.member (nxt # suffix) x \<longrightarrow> List.member path x)"
            using \<open>v \<noteq> u\<close> path_contains_u path_props path_through_v_has_next by blast

          then obtain nxt suffix where nxt_props:
            "has_edge graph u nxt"
            "valid_path graph (nxt # suffix)"
            "path_end (nxt # suffix) = v"
            "\<not>List.member (nxt # suffix) u"
            "(\<forall>x. List.member (nxt # suffix) x \<longrightarrow> List.member path x)"
            by auto

          (* nxt is a neighbor of u, so it's on the new stack *)
          have "List.member neighbors nxt"
            using nxt_props(1) neighbors_def by simp
          then have "List.member (neighbors @ rest) nxt"
            by (simp add: list_membership_lemma_2)
          then have "List.member (scc_stack state') nxt"
            using state'_eq by simp

          (* The path (nxt # suffix) doesn't go through u, so it's still unvisited *)
          have "all_unvisited (scc_visited state') (nxt # suffix)"
          proof -
            have "all_unvisited (scc_visited state) (nxt # suffix)"
              using nxt_props(5) path_props by auto
            moreover have "\<not>List.member (nxt # suffix) u"
              using nxt_props(4) by simp
            ultimately show ?thesis
              using all_unvisited_preserved_without_v state'_eq by auto
          qed

          then have "unvisited_path graph (scc_visited state') nxt v"
            by (metis assms(1) nxt_props(2,3) path_start.simps(2)
                valid_path_implies_unvisited_path)

          then show ?thesis
            using \<open>List.member (scc_stack state') nxt\<close> by auto

        next
          case path_doesnt_contain_u: False
          (* The path doesn't contain u so it is still a valid path for the new stack *)
          then have "all_unvisited (scc_visited state') path"
            using all_unvisited_preserved_without_v path_doesnt_contain_u
            using path_props state'_eq by auto 
          then have "unvisited_path graph (scc_visited state') w v"
            using assms(1) path_props valid_path_implies_unvisited_path by blast
          moreover have "List.member (scc_stack state') w"
          proof -
            have "List.member rest w"
              by (metis local.Cons member_rec(1) path_doesnt_contain_u path_props path_start.elims
                  valid_path.simps(1) w_props(1))
            moreover have "scc_stack state' = neighbors @ rest"
              using state'_eq by simp
            ultimately show ?thesis
              by (metis fset_of_list.rep_eq funionCI in_set_member set_append union_fset)
          qed
          ultimately show ?thesis
            by auto
        qed
      qed
    qed
  qed

  then show ?thesis
    using state'_def unfolding scc_completeness_inv_def by simp
qed


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
  assume stack_nonempty: "\<not> scc_stack state = []"

  (* We need to show the measure decreases after one step *)
  show "((graph, collect_scc_step graph state), (graph, state))
        \<in> measures [\<lambda>(graph,state). fcard (fmdom graph |-| scc_visited state),
                    \<lambda>(graph,state). length (scc_stack state)]"
  proof -
    define state' where "state' = collect_scc_step graph state"

    (* Analyze what collect_scc_step does based on the stack *)
    obtain v rest where stack_decomp: "scc_stack state = v # rest"
      using stack_nonempty by (cases "scc_stack state") auto

    show ?thesis
    proof (cases "v |\<in>| scc_visited state")
      case True
      (* v already visited - just pop the stack *)
      have new_state: "state' = state \<lparr> scc_stack := rest \<rparr>"
        using state'_def stack_decomp True by auto
      hence "length (scc_stack state') < length (scc_stack state)"
        using stack_decomp by simp
      moreover have "scc_visited state' = scc_visited state"
        using new_state by simp
      ultimately show ?thesis
        using state'_def by auto
    next
      case False
      (* v not visited - visit it and add neighbors *)
      show ?thesis proof (cases "fmlookup graph v")
        (* This case arises when scc_step is called with an invalid graph *)
        (* scc_step just bails out and clears the stack in this case *)
        case None
        then have new_state: "state' = state \<lparr> scc_stack := [] \<rparr>" 
          using state'_def stack_decomp False by auto
        hence "length (scc_stack state') < length (scc_stack state)"
          using stack_decomp by simp
        moreover have "scc_visited state' = scc_visited state"
          using new_state by simp
        ultimately show ?thesis
          using state'_def by auto
      next
        case (Some neighbors)
        have new_state: "state' = state \<lparr> scc_visited := finsert v (scc_visited state),
                                          scc_component := v # (scc_component state),
                                          scc_stack := neighbors @ rest \<rparr>"
        using state'_def stack_decomp False Some by auto

        hence visited_grows: "scc_visited state' = finsert v (scc_visited state)"
          and stack_new: "scc_stack state' = neighbors @ rest"
          by auto

        (* The key: v was unvisited, now it's visited *)
        have "v |\<notin>| scc_visited state" using False by simp
        have "v |\<in>| scc_visited state'" using visited_grows by simp

        have "fcard (fmdom graph |-| scc_visited state')
            < fcard (fmdom graph |-| scc_visited state)"
        proof -
          have "v |\<in>| fmdom graph |-| scc_visited state"
            using Some \<open>v |\<notin>| scc_visited state\<close>
            by (simp add: fmlookup_dom_iff) 
          moreover have "v |\<notin>| fmdom graph |-| scc_visited state'"
            using \<open>v |\<in>| scc_visited state'\<close> by simp
          moreover have "fmdom graph |-| scc_visited state'
                          |\<subset>| fmdom graph |-| scc_visited state"
            using visited_grows \<open>v |\<in>| fmdom graph |-| scc_visited state\<close>
                  \<open>v |\<notin>| fmdom graph |-| scc_visited state'\<close> by auto
          ultimately show ?thesis
            by (simp add: pfsubset_fcard_mono)
        qed
        thus ?thesis
          by (simp add: state'_def)
      qed
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

(* Lemma: visited set never shrinks during collect_scc_run *)
lemma collect_scc_run_visited_monotonic:
  "scc_visited state |\<subseteq>| scc_visited (collect_scc_run graph state)"
proof (induction graph state rule: collect_scc_run.induct)
  case (1 graph state)
  then show ?case
  proof (cases "scc_stack state = []")
    case True
    then show ?thesis by simp
  next
    case False
    then have "collect_scc_run graph state = collect_scc_run graph (collect_scc_step graph state)"
      by simp
    moreover have "scc_visited state |\<subseteq>| scc_visited (collect_scc_step graph state)"
      using collect_scc_step_visited_monotonic by blast
    moreover have "scc_visited (collect_scc_step graph state) |\<subseteq>|
                   scc_visited (collect_scc_run graph (collect_scc_step graph state))"
      using 1 False by simp
    ultimately show ?thesis
      by (metis dual_order.trans)
  qed
qed

(* Lemma: current component never shrinks during collect_scc_run *)
lemma collect_scc_run_current_grows:
  "set (scc_component state) \<subseteq> set (scc_component (collect_scc_run graph state))"
proof (induction graph state rule: collect_scc_run.induct)
  case (1 graph state)
  then show ?case
  proof (cases "scc_stack state = []")
    case True
    then show ?thesis by simp
  next
    case False
    then have "collect_scc_run graph state = collect_scc_run graph (collect_scc_step graph state)"
      by simp
    moreover have "set (scc_component state) \<subseteq> set (scc_component (collect_scc_step graph state))"
      using collect_scc_step_current_grows by blast
    moreover have "set (scc_component (collect_scc_step graph state)) \<subseteq>
                   set (scc_component (collect_scc_run graph (collect_scc_step graph state)))"
      using 1 False by simp
    ultimately show ?thesis
      by (metis subset_trans)
  qed
qed

(*-----------------------------------------------------------------------------*)
(* Invariant Preservation Lemmas for collect_scc_run *)
(*-----------------------------------------------------------------------------*)

(* These are proved by induction from the corresponding collect_scc_step lemmas *)

(* Lemma: collect_scc_run preserves validity *)
lemma collect_scc_run_preserves_valid:
  assumes "valid_graph graph"
    and "scc_state_valid graph initial_visited start state"
    and "scc_reachability_inv graph initial_visited start state"
  shows "scc_state_valid graph initial_visited start (collect_scc_run graph state)"
  using assms
proof (induction graph state rule: collect_scc_run.induct)
  case (1 graph state)
  then show ?case
  proof (cases "scc_stack state = []")
    case True
    then show ?thesis using 1 by simp
  next
    case False
    then have run_eq: "collect_scc_run graph state = collect_scc_run graph (collect_scc_step graph state)"
      by simp

    (* Apply step preservation lemma *)
    have step_valid: "scc_state_valid graph initial_visited start (collect_scc_step graph state)"
      using 1(2,3,4) collect_scc_step_preserves_valid by blast

    have step_reach: "scc_reachability_inv graph initial_visited start (collect_scc_step graph state)"
      using 1(2,3,4) collect_scc_step_preserves_reachability by blast

    (* Apply induction hypothesis *)
    have "scc_state_valid graph initial_visited start (collect_scc_run graph (collect_scc_step graph state))"
      using 1(1)[OF False 1(2) step_valid step_reach] by simp

    then show ?thesis using run_eq
      by metis 
  qed
qed

(* Lemma: collect_scc_run preserves reachability invariant *)
lemma collect_scc_run_preserves_reachability:
  assumes "valid_graph graph"
    and "scc_state_valid graph initial_visited start state"
    and "scc_reachability_inv graph initial_visited start state"
  shows "scc_reachability_inv graph initial_visited start (collect_scc_run graph state)"
  using assms
proof (induction graph state rule: collect_scc_run.induct)
  case (1 graph state)
  then show ?case
  proof (cases "scc_stack state = []")
    case True
    then show ?thesis using 1 by simp
  next
    case False
    then have run_eq: "collect_scc_run graph state = collect_scc_run graph (collect_scc_step graph state)"
      by simp

    (* Apply step preservation lemmas *)
    have step_valid: "scc_state_valid graph initial_visited start (collect_scc_step graph state)"
      using 1(2,3,4) collect_scc_step_preserves_valid by blast

    have step_reach: "scc_reachability_inv graph initial_visited start (collect_scc_step graph state)"
      using 1(2,3,4) collect_scc_step_preserves_reachability by blast

    (* Apply induction hypothesis *)
    have "scc_reachability_inv graph initial_visited start (collect_scc_run graph (collect_scc_step graph state))"
      using 1(1)[OF False 1(2) step_valid step_reach] by simp

    then show ?thesis using run_eq by metis
  qed
qed

(* Lemma: collect_scc_run preserves soundness invariant *)
lemma collect_scc_run_preserves_soundness:
  assumes "valid_graph graph"
    and "scc_state_valid graph initial_visited start state"
    and "scc_reachability_inv graph initial_visited start state"
    and "scc_soundness_inv graph initial_visited start state"
    and downstream_visited:
        "(\<forall>w. has_vertex graph w \<and> reachable graph start w \<and> \<not>(in_same_scc graph w start) \<longrightarrow>
              w |\<in>| initial_visited)"
  shows "scc_soundness_inv graph initial_visited start (collect_scc_run graph state)"
  using assms
proof (induction graph state rule: collect_scc_run.induct)
  case (1 graph state)
  then show ?case
  proof (cases "scc_stack state = []")
    case True
    then show ?thesis using 1 by simp
  next
    case False
    then have run_eq: "collect_scc_run graph state = collect_scc_run graph (collect_scc_step graph state)"
      by simp

    (* Apply step preservation lemmas *)
    have step_valid: "scc_state_valid graph initial_visited start (collect_scc_step graph state)"
      using 1(2,3,4) collect_scc_step_preserves_valid by blast

    have step_reach: "scc_reachability_inv graph initial_visited start (collect_scc_step graph state)"
      using 1(2,3,4) collect_scc_step_preserves_reachability by blast

    have step_sound: "scc_soundness_inv graph initial_visited start (collect_scc_step graph state)"
      using 1(2,3,4,5,6) collect_scc_step_preserves_soundness by blast

    (* Apply induction hypothesis *)
    have "scc_soundness_inv graph initial_visited start (collect_scc_run graph (collect_scc_step graph state))"
      using 1(1)[OF False 1(2) step_valid step_reach step_sound 1(6)] by simp

    then show ?thesis using run_eq by metis
  qed
qed

(* Lemma: collect_scc_run preserves completeness invariant *)
lemma collect_scc_run_preserves_completeness:
  assumes "valid_graph graph"
    and "scc_state_valid graph initial_visited start state"
    and "scc_reachability_inv graph initial_visited start state"
    and "scc_completeness_inv graph initial_visited start state"
  shows "scc_completeness_inv graph initial_visited start (collect_scc_run graph state)"
  using assms
proof (induction graph state rule: collect_scc_run.induct)
  case (1 graph state)
  then show ?case
  proof (cases "scc_stack state = []")
    case True
    then show ?thesis using 1 by simp
  next
    case False
    then have run_eq: "collect_scc_run graph state = collect_scc_run graph (collect_scc_step graph state)"
      by simp

    (* Apply step preservation lemmas *)
    have step_valid: "scc_state_valid graph initial_visited start (collect_scc_step graph state)"
      using 1(2,3,4) collect_scc_step_preserves_valid by blast

    have step_reach: "scc_reachability_inv graph initial_visited start (collect_scc_step graph state)"
      using 1(2,3,4) collect_scc_step_preserves_reachability by blast

    have step_complete: "scc_completeness_inv graph initial_visited start (collect_scc_step graph state)"
      using 1(2,3,4,5) collect_scc_step_preserves_completeness by blast

    (* Apply induction hypothesis *)
    have "scc_completeness_inv graph initial_visited start (collect_scc_run graph (collect_scc_step graph state))"
      using 1(1)[OF False 1(2) step_valid step_reach step_complete] by simp

    then show ?thesis using run_eq by metis
  qed
qed

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
  shows "scc_state_valid graph visited start state"
    and "scc_reachability_inv graph visited start state"
    and "scc_soundness_inv graph visited start state"
    and "scc_completeness_inv graph visited start state"
proof -
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
      have "\<forall>v. v \<in> set path \<longrightarrow> v |\<notin>| visited"
      proof (intro allI impI)
        fix v
        assume "v \<in> set path"
        then have "in_same_scc graph v start"
          using \<open>\<forall>v. v \<in> set path \<longrightarrow> in_same_scc graph v start\<close> by simp
        moreover have "has_vertex graph v"
          using assms(1,2) calculation edge_implies_vertices(1) scc_path_avoiding_vertex
          by blast
        ultimately show "v |\<notin>| visited"
          using scc_unvisited by simp
      qed

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

(* Soundness: collect_one_scc only collects vertices from the same SCC,
   provided all "downstream" SCCs have already been visited *)
lemma collect_one_scc_sound:
  assumes "valid_graph graph"
    and "has_vertex graph start"
    and "\<forall>w |\<in>| visited. has_vertex graph w"
    and "start |\<notin>| visited"
    and scc_unvisited:
        "(\<forall>w. has_vertex graph w \<and> in_same_scc graph w start \<longrightarrow> w |\<notin>| visited)"
    and downstream_visited:
        "(\<forall>w. has_vertex graph w \<and>
              reachable graph start w \<and>
              \<not>(in_same_scc graph w start) \<longrightarrow>
              w |\<in>| visited)"
    and "collect_one_scc graph visited start = (scc, new_visited)"
    and "List.member scc v"
  shows "in_same_scc graph v start"
proof -
  define initial_state where "initial_state = \<lparr> scc_visited = visited,
                                                 scc_component = [],
                                                 scc_stack = [start] \<rparr>"
  define final_state where "final_state = collect_scc_run graph initial_state"

  have collect_def: "collect_one_scc graph visited start = (scc_component final_state, scc_visited final_state)"
    unfolding collect_one_scc_def initial_state_def final_state_def by (simp add: Let_def)

  (* Extract scc and new_visited from the definition *)
  have "scc = scc_component final_state" and "new_visited = scc_visited final_state"
    using assms(7) collect_def by auto

  (* Show initial state satisfies all invariants using helper *)
  have initial_valid: "scc_state_valid graph visited start initial_state"
    and initial_reach: "scc_reachability_inv graph visited start initial_state"
    and initial_sound: "scc_soundness_inv graph visited start initial_state"
    using collect_one_scc_initial_invariants[OF assms(1,2,3) initial_state_def
          downstream_visited scc_unvisited]
    by blast+

  (* Apply preservation lemmas *)
  have final_valid: "scc_state_valid graph visited start final_state"
    using assms(1) initial_valid initial_reach final_state_def
          collect_scc_run_preserves_valid by blast

  have final_reach: "scc_reachability_inv graph visited start final_state"
    using assms(1) initial_valid initial_reach final_state_def
          collect_scc_run_preserves_reachability by blast

  have final_sound: "scc_soundness_inv graph visited start final_state"
    using assms(1) initial_valid initial_reach initial_sound downstream_visited final_state_def
          collect_scc_run_preserves_soundness by blast

  (* v is in the component, so by validity it's in visited and not in initial visited *)
  have "List.member (scc_component final_state) v"
    using \<open>scc = scc_component final_state\<close> assms(8) by auto

  then have "v |\<in>| scc_visited final_state"
    using final_valid unfolding scc_state_valid_def by blast

  moreover have "v |\<notin>| visited"
    using \<open>List.member (scc_component final_state) v\<close> final_valid
    unfolding scc_state_valid_def by blast

  (* By soundness invariant, v is in the same SCC as start *)
  ultimately show "in_same_scc graph v start"
    using final_sound unfolding scc_soundness_inv_def by simp
qed

(* Completeness: collect_one_scc collects all unvisited vertices from the same SCC,
   provided no vertex in the same SCC as start has been visited yet *)
lemma collect_one_scc_complete:
  assumes "valid_graph graph"
    and "has_vertex graph start"
    and "has_vertex graph v"
    and "\<forall>w |\<in>| visited. has_vertex graph w"
    and "in_same_scc graph v start"
    and scc_unvisited:
        "(\<forall>w. has_vertex graph w \<and> in_same_scc graph w start \<longrightarrow> w |\<notin>| visited)"
    and downstream_visited:
        "(\<forall>w. has_vertex graph w \<and> reachable graph start w \<and> \<not>(in_same_scc graph w start) \<longrightarrow>
              w |\<in>| visited)"
    and "collect_one_scc graph visited start = (scc, new_visited)"
  shows "List.member scc v"
proof -
  define initial_state where "initial_state = \<lparr> scc_visited = visited,
                                                 scc_component = [],
                                                 scc_stack = [start] \<rparr>"
  define final_state where "final_state = collect_scc_run graph initial_state"

  have collect_def: "collect_one_scc graph visited start = (scc_component final_state, scc_visited final_state)"
    unfolding collect_one_scc_def initial_state_def final_state_def by (simp add: Let_def)

  (* Extract scc and new_visited from the definition *)
  have "scc = scc_component final_state" and "new_visited = scc_visited final_state"
    using assms(8) collect_def by auto

  (* Show initial state satisfies all invariants using helper *)
  have initial_valid: "scc_state_valid graph visited start initial_state"
    and initial_reach: "scc_reachability_inv graph visited start initial_state"
    and initial_complete: "scc_completeness_inv graph visited start initial_state"
    using collect_one_scc_initial_invariants[OF assms(1,2,4) initial_state_def
          downstream_visited scc_unvisited]
    by blast+

  (* Apply completeness preservation *)
  have final_complete: "scc_completeness_inv graph visited start final_state"
    using assms(1) initial_valid initial_reach initial_complete final_state_def
          collect_scc_run_preserves_completeness by blast

  (* The stack is empty in final state *)
  have stack_empty: "scc_stack final_state = []"
    using final_state_def collect_scc_run_stack_empty by blast

  (* v is reachable from start and they're in the same SCC *)
  have "reachable graph start v"
    using assms(5) by simp

  (* By completeness invariant, if v is not visited, there must be something on the stack *)
  have "v |\<in>| scc_visited final_state"
  proof (rule ccontr)
    assume "v |\<notin>| scc_visited final_state"
    then have "\<exists>w. List.member (scc_stack final_state) w \<and> unvisited_path graph (scc_visited final_state) w v"
      using final_complete assms(3) \<open>reachable graph start v\<close> unfolding scc_completeness_inv_def by simp
    then obtain w where "List.member (scc_stack final_state) w"
      by auto
    then show False
      using stack_empty
      by (simp add: member_rec(2)) 
  qed

  (* v was visited but not in initial visited set *)
  moreover have "v |\<notin>| visited"
    using assms(3,5) scc_unvisited by auto

  (* By validity, v must be in the component *)
  have final_valid: "scc_state_valid graph visited start final_state"
    using assms(1) initial_valid initial_reach final_state_def
          collect_scc_run_preserves_valid by blast

  (* v grew from initial visited to final visited, and by validity must be in component *)
  have "List.member (scc_component final_state) v"
    using \<open>v |\<in>| scc_visited final_state\<close> \<open>v |\<notin>| visited\<close> final_valid
    unfolding scc_state_valid_def by simp

  then show ?thesis
    using \<open>scc = scc_component final_state\<close> by simp
qed

(* Visited set update: new_visited is the union of old visited and the collected component *)
lemma collect_one_scc_visited_update:
  assumes "valid_graph graph"
    and "has_vertex graph start"
    and "\<forall>w |\<in>| visited. has_vertex graph w"
    and scc_unvisited:
        "(\<forall>w. has_vertex graph w \<and> in_same_scc graph w start \<longrightarrow> w |\<notin>| visited)"
    and downstream_visited:
        "(\<forall>w. has_vertex graph w \<and> reachable graph start w \<and> \<not>(in_same_scc graph w start) \<longrightarrow>
              w |\<in>| visited)"
    and "start |\<notin>| visited"
    and "collect_one_scc graph visited start = (scc, new_visited)"
  shows "new_visited = visited |\<union>| fset_of_list scc"
proof -
  define initial_state where "initial_state = \<lparr> scc_visited = visited,
                                                 scc_component = [],
                                                 scc_stack = [start] \<rparr>"
  define final_state where "final_state = collect_scc_run graph initial_state"

  have collect_def: "collect_one_scc graph visited start = (scc_component final_state, scc_visited final_state)"
    unfolding collect_one_scc_def initial_state_def final_state_def by (simp add: Let_def)

  (* Extract scc and new_visited from the definition *)
  have scc_def: "scc = scc_component final_state" and 
       new_visited_def: "new_visited = scc_visited final_state"
    using assms(7) collect_def by auto

  (* Show initial state satisfies validity invariants using helper *)
  have initial_valid: "scc_state_valid graph visited start initial_state"
    and initial_reach: "scc_reachability_inv graph visited start initial_state"
    using collect_one_scc_initial_invariants[OF assms(1,2,3) initial_state_def
          downstream_visited scc_unvisited]
    by simp+

  (* Apply preservation lemmas *)
  have final_valid: "scc_state_valid graph visited start final_state"
    using assms(1) initial_valid initial_reach final_state_def
          collect_scc_run_preserves_valid by blast

  (* The visited set grows monotonically *)
  have visited_mono: "visited |\<subseteq>| scc_visited final_state"
    using initial_state_def final_state_def collect_scc_run_visited_monotonic
    by (metis scc_state.select_convs(1))

  (* All vertices in the component are in the final visited set *)
  have all_in_component_visited: "\<forall>v. List.member (scc_component final_state) v \<longrightarrow> 
                                    v |\<in>| scc_visited final_state"
    using final_valid unfolding scc_state_valid_def by blast

  (* All vertices in final visited that weren't in initial visited are in the component *)
  have all_newly_visited_in_component: "\<forall>v. v |\<in>| scc_visited final_state \<and> v |\<notin>| visited \<longrightarrow>
                                         List.member (scc_component final_state) v"
    using final_valid unfolding scc_state_valid_def
    by metis

  (* Therefore new_visited = visited \<union> component *)
  have "new_visited |\<subseteq>| visited |\<union>| fset_of_list scc"
    by (metis all_newly_visited_in_component new_visited_def scc_def 
        fset_of_list.rep_eq fsubsetI funionCI in_set_member)
  moreover have "visited |\<union>| fset_of_list scc |\<subseteq>| new_visited"
    by (metis all_in_component_visited new_visited_def scc_def visited_mono
        fset_of_list.rep_eq fsubsetI funion_iff in_set_member
        sup.order_iff)
  ultimately show ?thesis
    by auto
qed

(* The SCC returned by collect_one_scc contains no duplicates *)
lemma collect_one_scc_distinct:
  assumes "valid_graph graph"
    and "has_vertex graph start"
    and "\<forall>w |\<in>| visited. has_vertex graph w"
    and scc_unvisited:
        "(\<forall>w. has_vertex graph w \<and> in_same_scc graph w start \<longrightarrow> w |\<notin>| visited)"
    and downstream_visited:
        "(\<forall>w. has_vertex graph w \<and> reachable graph start w \<and> \<not>(in_same_scc graph w start) \<longrightarrow>
              w |\<in>| visited)"
    and "start |\<notin>| visited"
    and "collect_one_scc graph visited start = (scc, new_visited)"
  shows "distinct scc"
proof -
  define initial_state where "initial_state = \<lparr> scc_visited = visited,
                                                 scc_component = [],
                                                 scc_stack = [start] \<rparr>"
  define final_state where "final_state = collect_scc_run graph initial_state"

  have collect_def: "collect_one_scc graph visited start = (scc_component final_state, scc_visited final_state)"
    unfolding collect_one_scc_def initial_state_def final_state_def by (simp add: Let_def)

  (* Extract scc from the definition *)
  have scc_def: "scc = scc_component final_state"
    using assms(7) collect_def by auto

  (* Show initial state satisfies validity invariants using helper *)
  have initial_valid: "scc_state_valid graph visited start initial_state"
    and initial_reach: "scc_reachability_inv graph visited start initial_state"
    using collect_one_scc_initial_invariants[OF assms(1,2,3) initial_state_def
          downstream_visited scc_unvisited]
    by simp+

  (* Apply preservation lemma *)
  have final_valid: "scc_state_valid graph visited start final_state"
    using assms(1) initial_valid initial_reach final_state_def
          collect_scc_run_preserves_valid by blast

  (* Extract distinctness from validity *)
  then show ?thesis
    using scc_def unfolding scc_state_valid_def by simp
qed

end
