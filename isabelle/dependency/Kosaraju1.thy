theory Kosaraju1
  imports "../base/Graphs"
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

(* Helper lemma: dfs_post_visit_distinct preserved when removing from stack *)
lemma dfs_post_visit_distinct_tail:
  assumes "dfs_post_visit_distinct (frame # rest)"
  shows "dfs_post_visit_distinct rest"
  using assms by (cases frame) auto

(* Helper lemma: PostVisit frames are visited after adding to visited set *)
lemma dfs_post_visit_visited_insert:
  assumes "dfs_post_visit_visited visited stack"
  shows "dfs_post_visit_visited (finsert v visited) stack"
  using assms by auto

(* Helper lemma about list membership *)
lemma list_membership_lemma:
  assumes "\<not>List.member a x"
    and "List.member (a @ b) x"
  shows "List.member b x"
  using assms
  by (induction a) (auto simp: member_rec)

(* Helper lemma about list membership - reverse direction *)
lemma list_membership_lemma_2:
  assumes "List.member a x"
  shows "List.member (a @ b) x"
  using assms
  by (induction a) (auto simp: member_rec)

(* Helper lemma: Adding PreVisit neighbors and PostVisit v preserves post_visit_visited *)
lemma dfs_post_visit_visited_extend:
  assumes "dfs_post_visit_visited (finsert v visited) stack"
  shows "dfs_post_visit_visited (finsert v visited) (map PreVisit neighbors @ [PostVisit v] @ stack)"
  using assms
proof -
  have "\<forall>v'. List.member (map PreVisit neighbors @ [PostVisit v] @ stack) (PostVisit v')
       \<longrightarrow> v' |\<in>| (finsert v visited)"
  proof (rule allI, rule impI)
    fix v'
    assume member_post: "List.member (map PreVisit neighbors @ [PostVisit v] @ stack) (PostVisit v')"
    have "v = v' \<or> List.member stack (PostVisit v')"
    proof -
      have not_in_map: "\<not> List.member (map PreVisit neighbors) (PostVisit v')"
        by (induction neighbors) (auto simp: member_rec)
      then have "List.member ([PostVisit v] @ stack) (PostVisit v')"
        using not_in_map list_membership_lemma
        by (metis member_post)
      then show ?thesis
        by (auto simp: member_rec)
    qed
    show "v' |\<in>| (finsert v visited)"
    proof (cases "v = v'")
      case True
      then show ?thesis by simp
    next
      case False
      then show ?thesis
        using \<open>v = v' \<or> List.member stack (PostVisit v')\<close> assms by auto 
    qed
  qed
  thus ?thesis
    by auto
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
proof (induction neighbors)
  case Nil
  then show ?case by simp
next
  case (Cons n ns)
  then show ?case
    by simp 
qed

(* Helper lemma: visited vertices remain accounted after PreVisit expansion *)
lemma dfs_visited_accounted_expand:
  assumes "dfs_visited_accounted visited finish_order stack"
  shows "dfs_visited_accounted (finsert v visited) finish_order (map PreVisit neighbors @ [PostVisit v] @ stack)"
  using assms
proof -
  have "\<forall>u. u |\<in>| finsert v visited \<longrightarrow>
        List.member finish_order u \<or> List.member (map PreVisit neighbors @ [PostVisit v] @ stack) (PostVisit u)"
  proof (rule allI, rule impI)
    fix u
    assume "u |\<in>| finsert v visited"
    then have "u = v \<or> u |\<in>| visited"
      by auto
    then show "List.member finish_order u \<or> List.member (map PreVisit neighbors @ [PostVisit v] @ stack) (PostVisit u)"
    proof
      assume "u = v"
      then have "List.member ([PostVisit v] @ stack) (PostVisit u)"
        by (simp add: member_rec)
      then show ?thesis
        by (simp add: \<open>u = v\<close> member_def)
    next
      assume "u |\<in>| visited"
      then have "List.member finish_order u \<or> List.member stack (PostVisit u)"
        using assms by auto
      then show ?thesis
        by (metis append.assoc in_set_conv_decomp member_def)
    qed
  qed
  then show ?thesis
    by auto
qed

(* Helper lemma: visited vertices remain accounted after PostVisit *)
lemma dfs_visited_accounted_post:
  assumes "dfs_visited_accounted visited finish_order (PostVisit v # stack)"
  shows "dfs_visited_accounted visited (v # finish_order) stack"
  using assms
  by (auto simp: member_rec)

(* Helper lemma: distinctness preserved when adding element not in list *)
lemma distinct_cons_member:
  assumes "distinct xs"
    and "\<not> List.member xs x"
  shows "distinct (x # xs)"
  by (simp add: assms(1,2) in_set_member)

(* Lemma: dfs_step preserves dfs_state_valid *)
lemma dfs_step_preserves_validity:
  assumes valid: "dfs_state_valid graph state"
    and non_empty: "dfs_stack state \<noteq> []"
  shows "dfs_state_valid graph (dfs_step graph state)"
proof -
  obtain frame rest where stack_split: "dfs_stack state = frame # rest"
    using non_empty by (cases "dfs_stack state") auto

  show ?thesis
  proof (cases frame)
    case (PreVisit v)
    show ?thesis
    proof (cases "v |\<in>| dfs_visited state")
      case True
      (* v already visited, just pop the stack *)
      have "dfs_step graph state = state \<lparr> dfs_stack := rest \<rparr>"
        using stack_split PreVisit True by simp

      (* Most properties are preserved trivially *)
      have "valid_graph graph"
        using valid by simp

      have "dfs_stack_vertices_valid graph rest"
        using valid stack_split PreVisit by (auto simp: member_rec)

      have "\<forall>v. v |\<in>| dfs_visited state \<longrightarrow> has_vertex graph v"
        using valid by simp

      have "\<forall>v. List.member (dfs_finish_order state) v \<longrightarrow> has_vertex graph v"
        using valid by simp

      have "dfs_post_visit_visited (dfs_visited state) rest"
        using valid stack_split by (auto simp: member_rec)

      have "dfs_post_visit_distinct rest"
        using valid stack_split dfs_post_visit_distinct_tail
        by auto

      have "distinct (dfs_finish_order state)"
        using valid by simp

      have "dfs_visited_accounted (dfs_visited state) (dfs_finish_order state) rest"
        using valid stack_split
        by (simp add: PreVisit member_rec(1)) 

      have "\<forall>v. List.member (dfs_finish_order state) v \<longrightarrow> v |\<in>| dfs_visited state"
        using valid by simp

      have "\<forall>u. List.member (dfs_finish_order state) u \<longrightarrow> \<not> List.member rest (PostVisit u)"
        using valid stack_split by (auto simp: member_rec)

      thus ?thesis
        using \<open>dfs_step graph state = state \<lparr> dfs_stack := rest \<rparr>\<close>
              \<open>valid_graph graph\<close>
              \<open>dfs_stack_vertices_valid graph rest\<close>
              \<open>\<forall>v. v |\<in>| dfs_visited state \<longrightarrow> has_vertex graph v\<close>
              \<open>\<forall>v. List.member (dfs_finish_order state) v \<longrightarrow> has_vertex graph v\<close>
              \<open>dfs_post_visit_visited (dfs_visited state) rest\<close>
              \<open>dfs_post_visit_distinct rest\<close>
              \<open>distinct (dfs_finish_order state)\<close>
              \<open>dfs_visited_accounted (dfs_visited state) (dfs_finish_order state) rest\<close>
              \<open>\<forall>v. List.member (dfs_finish_order state) v \<longrightarrow> v |\<in>| dfs_visited state\<close>
        using valid by simp

    next
      case False
      (* v not visited, expand it *)

      (* Find neighbors of v *)
      have "valid_graph graph"
        using valid by simp
      have v_vertex: "has_vertex graph v" 
        using valid stack_split PreVisit by (auto simp: member_rec)
      define neighbors where "neighbors = the (fmlookup graph v)"

      (* All neighbors are vertices *)
      have neighbors_valid: "\<forall>w. List.member neighbors w \<longrightarrow> has_vertex graph w"
        using valid v_vertex neighbors_def
        by (meson dfs_state_valid.elims(2) has_edge_member_conv valid_graph.simps) 

      (* Expand definition of dfs_step in this case *)
      have "dfs_step graph state =
            state \<lparr> dfs_visited := finsert v (dfs_visited state),
                   dfs_stack := map PreVisit neighbors @ [PostVisit v] @ rest \<rparr>"
        using PreVisit dfs_step_previsit_expand neighbors_def stack_split valid False by blast 

      (* Build the proof *)
      have "dfs_stack_vertices_valid graph (map PreVisit neighbors @ [PostVisit v] @ rest)"
      proof -
        have "dfs_stack_vertices_valid graph (map PreVisit neighbors)"
          using map_PreVisit_valid[OF neighbors_valid] by simp
        moreover have "dfs_stack_vertices_valid graph [PostVisit v]"
          using v_vertex by (auto simp: member_rec)
        moreover have "dfs_stack_vertices_valid graph rest"
          using valid stack_split by (auto simp: member_rec)
        ultimately show ?thesis
          by (metis dfs_stack_vertices_valid.elims(1) list_membership_lemma)
      qed

      have "\<forall>u. u |\<in>| finsert v (dfs_visited state) \<longrightarrow> has_vertex graph u"
        using valid v_vertex by simp

      have "\<forall>u. List.member (dfs_finish_order state) u \<longrightarrow> has_vertex graph u"
        using valid by simp

      have "dfs_post_visit_visited (finsert v (dfs_visited state))
               (map PreVisit neighbors @ [PostVisit v] @ rest)"
        using valid stack_split dfs_post_visit_visited_insert dfs_post_visit_visited_extend
        by (metis dfs_post_visit_visited.elims(1) dfs_state_valid.elims(1) member_rec(1))

      have "dfs_post_visit_distinct (map PreVisit neighbors @ [PostVisit v] @ rest)"
      proof -
        have "dfs_post_visit_distinct rest"
          using valid stack_split dfs_post_visit_distinct_tail by auto
        moreover have "\<not> List.member rest (PostVisit v)"
          using False valid
          by (metis dfs_post_visit_visited.elims(2) dfs_state_valid.elims(1)
              member_rec(1) stack_split) 
        ultimately show ?thesis
          using dfs_post_visit_distinct_extend
          by auto 
      qed

      have "distinct (dfs_finish_order state)"
        using valid by simp

      have "dfs_visited_accounted (finsert v (dfs_visited state)) (dfs_finish_order state) 
                (map PreVisit neighbors @ [PostVisit v] @ rest)"
        using valid stack_split dfs_visited_accounted_expand
        by (metis (no_types, lifting) PreVisit dfs_frame.distinct(1) dfs_state_valid.elims(1) 
            dfs_visited_accounted.elims(1) member_rec(1))

      have "\<forall>u. List.member (dfs_finish_order state) u \<longrightarrow> u |\<in>| finsert v (dfs_visited state)"
        using valid by simp

      have "\<forall>u. List.member (dfs_finish_order state) u \<longrightarrow>
                \<not> List.member (map PreVisit neighbors @ [PostVisit v] @ rest) (PostVisit u)"
      proof (rule allI, rule impI)
        fix u
        assume "List.member (dfs_finish_order state) u"
        then have "\<not> List.member (dfs_stack state) (PostVisit u)"
          using valid by auto
        then have "PostVisit u \<noteq> PreVisit v"
          using stack_split PreVisit by auto
        have "\<not> List.member (map PreVisit neighbors) (PostVisit u)"
          by (induction neighbors) (auto simp: member_rec)
        moreover have "PostVisit u \<noteq> PostVisit v"
          using \<open>\<not> List.member (dfs_stack state) (PostVisit u)\<close> stack_split PreVisit False
          using \<open>List.member (dfs_finish_order state) u\<close> valid by fastforce
        moreover have "\<not> List.member rest (PostVisit u)"
          using \<open>\<not> List.member (dfs_stack state) (PostVisit u)\<close> stack_split PreVisit
          by (auto simp: member_rec)
        ultimately show "\<not> List.member (map PreVisit neighbors @ [PostVisit v] @ rest) (PostVisit u)"
          by (metis append_Cons append_self_conv2 list_membership_lemma member_rec(1))
      qed

      thus ?thesis
        using \<open>dfs_step graph state =
                  state \<lparr> dfs_visited := finsert v (dfs_visited state),
                          dfs_stack := map PreVisit neighbors @ [PostVisit v] @ rest \<rparr>\<close>
              \<open>valid_graph graph\<close>
              \<open>dfs_stack_vertices_valid graph (map PreVisit neighbors @ [PostVisit v] @ rest)\<close>
              \<open>\<forall>u. u |\<in>| finsert v (dfs_visited state) \<longrightarrow> has_vertex graph u\<close>
              \<open>\<forall>u. List.member (dfs_finish_order state) u \<longrightarrow> has_vertex graph u\<close>
              \<open>dfs_post_visit_visited (finsert v (dfs_visited state))
                                      (map PreVisit neighbors @ [PostVisit v] @ rest)\<close>
              \<open>dfs_post_visit_distinct (map PreVisit neighbors @ [PostVisit v] @ rest)\<close>
              \<open>distinct (dfs_finish_order state)\<close>
              \<open>dfs_visited_accounted (finsert v (dfs_visited state)) (dfs_finish_order state)
                    (map PreVisit neighbors @ [PostVisit v] @ rest)\<close>
              \<open>\<forall>u. List.member (dfs_finish_order state) u \<longrightarrow> u |\<in>| finsert v (dfs_visited state)\<close>
              \<open>\<forall>u. List.member (dfs_finish_order state) u \<longrightarrow>
                \<not> List.member (map PreVisit neighbors @ [PostVisit v] @ rest) (PostVisit u)\<close>
        by simp
    qed
  next
    case (PostVisit v)
    (* Popping PostVisit v, adding v to finish order *)
    have "dfs_step graph state =
          state \<lparr> dfs_finish_order := v # (dfs_finish_order state),
                 dfs_stack := rest \<rparr>"
      using stack_split PostVisit by simp

    (* v is in visited set *)
    have v_visited: "v |\<in>| dfs_visited state"
      using valid stack_split PostVisit by (auto simp: member_rec)

    (* v is a vertex *)
    have v_vertex: "has_vertex graph v"
      using valid v_visited by simp

    (* v is not in finish_order yet *)
    have v_not_finished: "\<not> List.member (dfs_finish_order state) v"
    proof -
      (* We know PostVisit v is on the stack (it's the head) *)
      have "List.member (dfs_stack state) (PostVisit v)"
        using stack_split PostVisit by (simp add: member_rec)
      (* By the new invariant, if v were in finish_order, then PostVisit v
         would not be on the stack, which contradicts the above *)
      show ?thesis
        using valid \<open>List.member (dfs_stack state) (PostVisit v)\<close>
        by auto
    qed

    (* Build the proof *)
    have "valid_graph graph"
      using valid by simp

    have "dfs_stack_vertices_valid graph rest"
      using valid stack_split by (auto simp: member_rec)

    have "\<forall>u. u |\<in>| dfs_visited state \<longrightarrow> has_vertex graph u"
      using valid by simp

    have "\<forall>u. List.member (v # dfs_finish_order state) u \<longrightarrow> has_vertex graph u"
      using valid v_vertex by (auto simp: member_rec)

    have "dfs_post_visit_visited (dfs_visited state) rest"
      using valid stack_split by (auto simp: member_rec)

    have "dfs_post_visit_distinct rest"
      using valid stack_split dfs_post_visit_distinct_tail by auto

    have "distinct (v # dfs_finish_order state)"
      using valid v_not_finished distinct_cons_member
      by (metis dfs_state_valid.elims(2)) 

    have "dfs_visited_accounted (dfs_visited state) (v # dfs_finish_order state) rest"
      using valid stack_split dfs_visited_accounted_post
      by (metis PostVisit dfs_state_valid.elims(1))

    have "\<forall>u. List.member (v # dfs_finish_order state) u \<longrightarrow> u |\<in>| dfs_visited state"
      using valid v_visited by (auto simp: member_rec)

    have "\<forall>u. List.member (v # dfs_finish_order state) u \<longrightarrow> \<not> List.member rest (PostVisit u)"
    proof (rule allI, rule impI)
      fix u
      assume "List.member (v # dfs_finish_order state) u"
      then have "u = v \<or> List.member (dfs_finish_order state) u"
        by (auto simp: member_rec)
      then show "\<not> List.member rest (PostVisit u)"
      proof
        assume "u = v"
        (* PostVisit v is on the stack as the head, so by dfs_post_visit_distinct,
           it's not in rest *)
        have "List.member (dfs_stack state) (PostVisit v)"
          using stack_split PostVisit by (simp add: member_rec)
        then have "\<not> List.member rest (PostVisit v)"
          using valid stack_split PostVisit by auto
        then show ?thesis
          using \<open>u = v\<close> by simp
      next
        assume "List.member (dfs_finish_order state) u"
        (* u was already finished, so PostVisit u wasn't on stack *)
        have "\<not> List.member (dfs_stack state) (PostVisit u)"
          using valid \<open>List.member (dfs_finish_order state) u\<close> by auto
        then show ?thesis
          using stack_split by (auto simp: member_rec)
      qed
    qed

    thus ?thesis
      using \<open>dfs_step graph state = state \<lparr> dfs_finish_order := v # (dfs_finish_order state), dfs_stack := rest \<rparr>\<close>
            \<open>valid_graph graph\<close>
            \<open>dfs_stack_vertices_valid graph rest\<close>
            \<open>\<forall>u. u |\<in>| dfs_visited state \<longrightarrow> has_vertex graph u\<close>
            \<open>\<forall>u. List.member (v # dfs_finish_order state) u \<longrightarrow> has_vertex graph u\<close>
            \<open>dfs_post_visit_visited (dfs_visited state) rest\<close>
            \<open>dfs_post_visit_distinct rest\<close>
            \<open>distinct (v # dfs_finish_order state)\<close>
            \<open>dfs_visited_accounted (dfs_visited state) (v # dfs_finish_order state) rest\<close>
            \<open>\<forall>u. List.member (v # dfs_finish_order state) u \<longrightarrow> u |\<in>| dfs_visited state\<close>
            \<open>\<forall>u. List.member (v # dfs_finish_order state) u \<longrightarrow> \<not> List.member rest (PostVisit u)\<close>
      by simp
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

(* Definition: If PostVisit x appears on the stack at index i, then
   will_finish_before_me(state, i) = 
     { all vertices currently finished } \<union>
     { all z such that there is a PostVisit z at stack index < i } \<union>
     { all z such that there is some PreVisit w at stack index < i
       with an unvisited path from w to z }
   Otherwise, will_finish_before_me(state, i) is empty. *)
fun will_finish_before_me :: "('a::linorder) Graph \<Rightarrow> 'a dfs_state \<Rightarrow> nat \<Rightarrow> 'a set" where
  "will_finish_before_me graph state i =
    (case (if i < length (dfs_stack state) then Some (dfs_stack state ! i) else None) of
      Some (PostVisit x) \<Rightarrow>
        (set (dfs_finish_order state)) \<union>
        {z. \<exists>j. j < i \<and> 
                  List.member (dfs_stack state) (PostVisit z) \<and>
                  index_of (PostVisit z) (dfs_stack state) = j} \<union>
        {z. \<exists>j w. j < i \<and>
                  List.member (dfs_stack state) (PreVisit w) \<and>
                  index_of (PreVisit w) (dfs_stack state) = j \<and>
                  unvisited_path graph (dfs_visited state) w z}
    | _ \<Rightarrow> {})"


(*-----------------------------------------------------------------------------*)
(* Additional invariants preserved by DFS step *)
(*-----------------------------------------------------------------------------*)

(* PreVisit ordering property: if PreVisit u appears before PostVisit v on the stack,
   then v reaches u *)
fun dfs_previsit_ordered :: "('a::linorder) Graph \<Rightarrow> 'a dfs_state \<Rightarrow> bool" where
  "dfs_previsit_ordered graph state \<longleftrightarrow>
    (\<forall>u v. List.member (dfs_stack state) (PreVisit u) \<and>
           List.member (dfs_stack state) (PostVisit v) \<and>
           index_of (PreVisit u) (dfs_stack state) < index_of (PostVisit v) (dfs_stack state) \<longrightarrow>
           reachable graph v u)"

(* PostVisit ordering property: if PostVisit u appears before PostVisit v on the stack,
   then v reaches u *)
fun dfs_postvisit_ordered :: "('a::linorder) Graph \<Rightarrow> 'a dfs_state \<Rightarrow> bool" where
  "dfs_postvisit_ordered graph state \<longleftrightarrow>
    (\<forall>u v. List.member (dfs_stack state) (PostVisit u) \<and>
           List.member (dfs_stack state) (PostVisit v) \<and>
           index_of (PostVisit u) (dfs_stack state) < index_of (PostVisit v) (dfs_stack state) \<longrightarrow>
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
    (\<exists>v i. has_vertex graph v \<and> in_same_scc graph v c \<and>
          i < length (dfs_stack state) \<and> (dfs_stack state) ! i = PostVisit v \<and>
          (\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<longrightarrow>
                z \<in> will_finish_before_me graph state i))"

fun finish_order_5 :: "('a::linorder) Graph \<Rightarrow> 'a dfs_state \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "finish_order_5 graph state c d \<longleftrightarrow>
    (\<exists>v. has_vertex graph v \<and> in_same_scc graph v c \<and>
          \<not>List.member (dfs_finish_order state) v)
  \<and> (\<exists>x i. has_vertex graph x \<and> in_same_scc graph x d \<and>
          i < length (dfs_stack state) \<and> (dfs_stack state) ! i = PostVisit x \<and>
          (\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<and> z \<noteq> x \<longrightarrow>
                z \<in> will_finish_before_me graph state i))"

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

(* Lemma: unvisited_path implies reachable *)
lemma unvisited_path_implies_reachable:
  assumes "unvisited_path graph visited x y"
  shows "reachable graph x y"
  using assms
proof (induction)
  case (unvisited_refl u)
  (* u is a vertex and unvisited, so reachable graph u u *)
  then show ?case
    using reachable.reachable_refl by simp
next
  case (unvisited_step u w v)
  then show ?case
    by (metis fmdom_notD has_edge.elims(1) has_vertex.simps
        option.case_eq_if reachable_refl reachable_step
        reachable_trans)
qed

(* Predicate stating that all vertices in a path are unvisited *)
fun all_unvisited :: "'a fset \<Rightarrow> 'a list \<Rightarrow> bool" where
  "all_unvisited visited path = (\<forall>v. List.member path v \<longrightarrow> v |\<notin>| visited)"

(* Lemma: unvisited_path implies existence of a valid path with all vertices unvisited *)
lemma unvisited_path_implies_valid_path:
  assumes "valid_graph graph"
    and "unvisited_path graph visited start target"
  shows "\<exists>path. valid_path graph path \<and>
               path_start path = start \<and>
               path_end path = target \<and>
               all_unvisited visited path"
  using assms(2,1)
proof (induction rule: unvisited_path.induct)
  case (unvisited_refl u)
  have "valid_path graph [u]"
    using unvisited_refl by simp
  moreover have "path_start [u] = u"
    by simp
  moreover have "path_end [u] = u"
    by simp
  moreover have "all_unvisited visited [u]"
    using unvisited_refl by (simp add: member_rec)
  ultimately show ?case by blast
next
  case (unvisited_step u w v)
  (* By IH, there exists a path from w to v *)
  obtain path_wv where
    path_wv_valid: "valid_path graph path_wv"
    and path_wv_start: "path_start path_wv = w"
    and path_wv_end: "path_end path_wv = v"
    and path_wv_unvisited: "all_unvisited visited path_wv"
    using unvisited_step.IH unvisited_step.prems by blast

  (* Prepend u to the path *)
  define pth where "pth = u # path_wv"

  have "valid_path graph pth"
    unfolding pth_def
    using path_wv_valid unvisited_step.hyps(2)
    by (metis path_start.elims path_wv_start valid_path.simps(1,3))

  moreover have "path_start pth = u"
    unfolding pth_def by simp

  moreover have "path_end pth = v"
    unfolding pth_def using path_wv_end
    by (metis path_end.simps(3) path_start.elims path_wv_valid
        valid_path.simps(1))
    
  moreover have "all_unvisited visited pth"
    unfolding pth_def
    using path_wv_unvisited unvisited_step.hyps(1)
    by (simp add: member_rec)

  ultimately show ?case by blast
qed

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

(* Lemma: If a path doesn't contain v and is all unvisited,
   then it remains unvisited when v is added to the visited set *)
lemma all_unvisited_preserved_without_v:
  assumes "all_unvisited visited path"
    and "\<not>List.member path v"
  shows "all_unvisited (finsert v visited) path"
  using assms by auto


(*-----------------------------------------------------------------------------*)
(* More helper lemmas *)
(*-----------------------------------------------------------------------------*)

(* Helper lemma: map PreVisit doesn't contain PostVisit frames *)
lemma map_PreVisit_no_PostVisit:
  "\<not> List.member (map PreVisit neighbors) (PostVisit v)"
  by (induction neighbors) (auto simp: member_rec)

(* Lemma: If dfs_post_visit_distinct frames, then
   we can convert between "frames ! i = PostVisit x"
   and "index_of (PostVisit x) frames = i" *)
lemma index_of_postvisit_conv:
  assumes "dfs_post_visit_distinct frames"
  shows "(i < length frames \<and> frames ! i = PostVisit x)
    \<longleftrightarrow> (List.member frames (PostVisit x) \<and> index_of (PostVisit x) frames = i)"
proof
  assume "i < length frames \<and> frames ! i = PostVisit x"
  then have "i < length frames" and "frames ! i = PostVisit x" by auto
  then have "List.member frames (PostVisit x)"
    by (metis in_set_member nth_mem)
  moreover have "index_of (PostVisit x) frames = i"
    using assms \<open>i < length frames\<close> \<open>frames ! i = PostVisit x\<close>
  proof (induction frames arbitrary: i)
    case Nil
    then show ?case by simp
  next
    case (Cons frame rest)
    show ?case
    proof (cases frame)
      case (PreVisit v)
      then have "dfs_post_visit_distinct rest"
        using Cons.prems(1) by simp
      show ?thesis
      proof (cases i)
        case 0
        then show ?thesis
          using Cons.prems(3) PreVisit by auto
      next
        case (Suc j)
        then have "j < length rest" and "rest ! j = PostVisit x"
          using Cons.prems(2,3) PreVisit by auto
        then have "index_of (PostVisit x) rest = j"
          using Cons.IH[OF \<open>dfs_post_visit_distinct rest\<close>] by auto
        then show ?thesis
          using PreVisit Suc by simp
      qed
    next
      case (PostVisit v)
      then have "dfs_post_visit_distinct rest"
        using Cons.prems(1) by simp
      have "\<not> List.member rest (PostVisit v)"
        using Cons.prems(1) PostVisit by simp
      show ?thesis
      proof (cases i)
        case 0
        then have "frame = PostVisit x"
          using Cons.prems(3) by simp
        then have "PostVisit v = PostVisit x"
          using PostVisit by simp
        then have "v = x" by simp
        then show ?thesis
          using 0 PostVisit by simp
      next
        case (Suc j)
        then have "j < length rest" and "rest ! j = PostVisit x"
          using Cons.prems(2,3) PostVisit by auto
        then have "index_of (PostVisit x) rest = j"
          using Cons.IH[OF \<open>dfs_post_visit_distinct rest\<close>] by auto
        moreover have "PostVisit x \<noteq> PostVisit v"
          using \<open>rest ! j = PostVisit x\<close> \<open>\<not> List.member rest (PostVisit v)\<close>
                \<open>j < length rest\<close>
          by (metis in_set_member nth_mem)
        ultimately show ?thesis
          using PostVisit Suc by simp
      qed
    qed
  qed
  ultimately show "List.member frames (PostVisit x) \<and> index_of (PostVisit x) frames = i"
    by simp
next
  assume "List.member frames (PostVisit x) \<and> index_of (PostVisit x) frames = i"
  then have "List.member frames (PostVisit x)" and "index_of (PostVisit x) frames = i" by auto
  show "i < length frames \<and> frames ! i = PostVisit x"
    using assms \<open>List.member frames (PostVisit x)\<close> \<open>index_of (PostVisit x) frames = i\<close>
  proof (induction frames arbitrary: i)
    case Nil
    then show ?case
      by (simp add: member_rec(2)) 
  next
    case (Cons frame rest)
    show ?case
    proof (cases frame)
      case (PreVisit v)
      then have "dfs_post_visit_distinct rest"
        using Cons.prems(1) by simp
      have "List.member rest (PostVisit x)"
        using Cons.prems(2) PreVisit by (auto simp: member_rec)
      have "index_of (PostVisit x) (PreVisit v # rest) = Suc (index_of (PostVisit x) rest)"
        by simp
      then have "index_of (PostVisit x) rest = i - 1"
        using Cons.prems(3) PreVisit by simp
      moreover have "i > 0"
        using Cons.prems(3) PreVisit by simp
      ultimately have "i - 1 < length rest \<and> rest ! (i - 1) = PostVisit x"
        using Cons.IH[OF \<open>dfs_post_visit_distinct rest\<close> \<open>List.member rest (PostVisit x)\<close>] by auto
      then show ?thesis
        using PreVisit \<open>i > 0\<close> by auto
    next
      case (PostVisit v)
      then have "dfs_post_visit_distinct rest"
        using Cons.prems(1) by simp
      have "\<not> List.member rest (PostVisit v)"
        using Cons.prems(1) PostVisit by simp
      show ?thesis
      proof (cases "PostVisit x = PostVisit v")
        case True
        then have "i = 0"
          using Cons.prems(3) PostVisit by simp
        then show ?thesis
          using True PostVisit by simp
      next
        case False
        then have "List.member rest (PostVisit x)"
          using Cons.prems(2) PostVisit by (auto simp: member_rec)
        have "index_of (PostVisit x) (frame # rest) = Suc (index_of (PostVisit x) rest)"
          using False PostVisit by simp
        then have "index_of (PostVisit x) rest = i - 1"
          using Cons.prems(3) by simp
        then have "i - 1 < length rest \<and> rest ! (i - 1) = PostVisit x"
          using Cons.IH[OF \<open>dfs_post_visit_distinct rest\<close> \<open>List.member rest (PostVisit x)\<close>] by auto
        moreover have "i > 0"
          using \<open>index_of (PostVisit x) rest = i - 1\<close> \<open>List.member rest (PostVisit x)\<close>
          using Cons.prems(3)
            \<open>index_of (PostVisit x) (frame # rest) = Suc (index_of (PostVisit x) rest)\<close>
          by force
        ultimately show ?thesis
          using PostVisit by auto
      qed
    qed
  qed
qed

(* Helper lemma: index_of shifts when prepending an element *)
lemma index_of_cons_shift:
  assumes "x \<noteq> y"
    and "List.member xs x"
  shows "index_of x (y # xs) = Suc (index_of x xs)"
  using assms by simp

(* Helper lemma: index_of shifts by length of prefix when prepending a list *)
lemma index_of_append_shift:
  assumes "List.member xs x"
    and "\<not> List.member prefix x"
  shows "index_of x (prefix @ xs) = length prefix + index_of x xs"
  using assms
  by (induction prefix) (auto simp: member_rec)

(* Helper lemma: if x is in prefix, index is unchanged by appending suffix *)
lemma index_of_prefix:
  assumes "List.member prefix x"
  shows "index_of x (prefix @ suffix) = index_of x prefix"
  using assms
  by (induction prefix) (auto simp: member_rec)

(* Helper lemma: ordering is preserved when prepending a prefix that doesn't contain either element *)
lemma index_of_append_preserves_order:
  assumes "index_of alpha rest < index_of beta rest"
    and "\<not> List.member prefix alpha"
    and "\<not> List.member prefix beta"
    and "List.member rest alpha"
    and "List.member rest beta"
  shows "index_of alpha (prefix @ rest) < index_of beta (prefix @ rest)"
proof -
  have "index_of alpha (prefix @ rest) = length prefix + index_of alpha rest"
    using assms(2,4) index_of_append_shift by fastforce
  moreover have "index_of beta (prefix @ rest) = length prefix + index_of beta rest"
    using assms(3,5) index_of_append_shift by fastforce
  ultimately show ?thesis
    using assms(1) by simp
qed

(* Helper lemma: element in prefix comes before element in rest (not in prefix) *)
lemma index_of_prefix_before_rest:
  assumes "List.member prefix alpha"
    and "List.member rest beta"
    and "\<not> List.member prefix beta"
  shows "index_of alpha (prefix @ rest) < index_of beta (prefix @ rest)"
proof -
  have "index_of alpha (prefix @ rest) < length prefix"
    using assms(1)
    by (induction prefix) (auto simp: member_rec)
  moreover have "index_of beta (prefix @ rest) = length prefix + index_of beta rest"
    using assms(2,3) index_of_append_shift by fastforce
  ultimately show ?thesis
    by simp
qed

(* Lemma: if u reaches w and different SCCs, then u \<noteq> w *)
lemma reachable_diff_scc_neq:
  assumes "reachable graph u w"
    and "\<not>(in_same_scc graph u w)"
  shows "u \<noteq> w"
  using assms(1,2) by force

(* Assuming PostVisit frames are distinct, then if stack index i and j both hold the
   same PostVisit frame, then i = j *)
lemma dfs_post_visit_distinct_unique_index:
  assumes "dfs_post_visit_distinct stack"
    and "i < length stack"
    and "j < length stack"
    and "stack ! i = PostVisit x"
    and "stack ! j = PostVisit x"
  shows "i = j"
  using assms
proof (induction stack arbitrary: i j)
  case Nil
  then show ?case by simp
next
  case (Cons frame rest)
  show ?case
  proof (cases "i = 0")
    case True
    then have "frame = PostVisit x"
      using Cons.prems(4) by simp
    show ?thesis
    proof (cases "j = 0")
      case True
      then show ?thesis using \<open>i = 0\<close> by simp
    next
      case False
      then have "j > 0"
        by simp
      then have "rest ! (j - 1) = PostVisit x"
        using Cons.prems(5) by (metis Suc_diff_1 gr0_conv_Suc nth_Cons_Suc)
      then have "List.member rest (PostVisit x)"
        using Cons.prems(3) False
        by (metis Suc_diff_1 Suc_less_eq \<open>0 < j\<close> in_set_member length_Cons
            nth_mem) 
      moreover have "\<not> List.member rest (PostVisit x)"
        using \<open>frame = PostVisit x\<close> Cons.prems(1) by auto
      ultimately show ?thesis by simp
    qed
  next
    case False
    then have "i > 0" by simp
    show ?thesis
    proof (cases "j = 0")
      case True
      then have "frame = PostVisit x"
        using Cons.prems(5) by simp
      have "rest ! (i - 1) = PostVisit x"
        using Cons.prems(4) \<open>i > 0\<close> by (metis Suc_diff_1 gr0_conv_Suc nth_Cons_Suc)
      then have "List.member rest (PostVisit x)"
        using Cons.prems(2) \<open>i > 0\<close>
        by (metis Suc_diff_1 Suc_less_eq in_set_member length_Cons
            nth_mem) 
      moreover have "\<not> List.member rest (PostVisit x)"
        using \<open>frame = PostVisit x\<close> Cons.prems(1) by auto
      ultimately show ?thesis by simp
    next
      case False
      then have "j > 0" by simp
      have "rest ! (i - 1) = PostVisit x"
        using Cons.prems(4) \<open>i > 0\<close> by (metis Suc_diff_1 gr0_conv_Suc nth_Cons_Suc)
      have "rest ! (j - 1) = PostVisit x"
        using Cons.prems(5) \<open>j > 0\<close> by (metis Suc_diff_1 gr0_conv_Suc nth_Cons_Suc)
      have "dfs_post_visit_distinct rest"
        using Cons.prems(1) dfs_post_visit_distinct_tail by auto
      have "i - 1 < length rest" and "j - 1 < length rest"
        using Cons.prems(2,3) \<open>i > 0\<close> \<open>j > 0\<close> by auto
      then have "i - 1 = j - 1"
        using Cons.IH[OF \<open>dfs_post_visit_distinct rest\<close> _ _ \<open>rest ! (i - 1) = PostVisit x\<close> \<open>rest ! (j - 1) = PostVisit x\<close>]
        by simp
      then show ?thesis
        by (metis Suc_diff_1 \<open>0 < i\<close> \<open>0 < j\<close>) 
    qed
  qed
qed


end
