theory Kosaraju2
  imports Kosaraju1
begin

(* Kosaraju's algorithm for finding strongly connected components: Part 2. *)

(*-----------------------------------------------------------------------------*)
(* Helper lemmas about expanded stacks *)
(*-----------------------------------------------------------------------------*)

(* Splitting a freshly expanded stack at a PostVisit frame: either the split is at the
   new PostVisit frame, or it is inside the old rest of the stack *)
lemma split_expanded_stack:
  assumes "map PreVisit ns @ PostVisit w # rest = prefix @ PostVisit v # post"
  shows "(prefix = map PreVisit ns \<and> v = w \<and> post = rest) \<or>
         (\<exists>prefix'. prefix = map PreVisit ns @ PostVisit w # prefix' \<and>
                    rest = prefix' @ PostVisit v # post)"
  using assms
proof (induction ns arbitrary: prefix)
  case Nil
  then show ?case
    by (cases prefix) auto
next
  case (Cons n ns)
  show ?case
  proof (cases prefix)
    case Nil
    then show ?thesis
      using Cons.prems by simp
  next
    case prefix_cons: (Cons p prefix1)
    then have "p = PreVisit n"
      and split: "map PreVisit ns @ PostVisit w # rest = prefix1 @ PostVisit v # post"
      using Cons.prems by simp_all
    from Cons.IH[OF split] show ?thesis
      using prefix_cons \<open>p = PreVisit n\<close> by auto
  qed
qed

(* The PreVisit frames pushed when expanding u are exactly the successors of u *)
lemma expanded_successor:
  assumes "has_vertex graph u"
    and "PreVisit n \<in> set (map PreVisit (the (fmlookup graph u)))"
  shows "has_edge graph u n"
proof -
  have "List.member (the (fmlookup graph u)) n"
    using assms(2) by (auto simp: member_def)
  then show ?thesis
    using has_edge_member_conv[OF assms(1)] by blast
qed

lemma successor_in_expanded:
  assumes "has_vertex graph u"
    and "has_edge graph u n"
  shows "PreVisit n \<in> set (map PreVisit (the (fmlookup graph u)))"
proof -
  have "List.member (the (fmlookup graph u)) n"
    using has_edge_member_conv[OF assms(1)] assms(2) by blast
  then show ?thesis
    by (auto simp: member_def)
qed

(*-----------------------------------------------------------------------------*)
(* DFS step preserves previsit_ordered and postvisit_ordered *)
(*-----------------------------------------------------------------------------*)

(* Lemma: dfs_step preserves the PreVisit ordering property *)
lemma dfs_step_preserves_previsit_ordered:
  assumes valid: "dfs_state_valid graph state"
    and previsit_ordered: "dfs_previsit_ordered graph state"
    and non_empty: "dfs_stack state \<noteq> []"
  shows "dfs_previsit_ordered graph (dfs_step graph state)"
proof (cases rule: dfs_step_cases[OF valid non_empty, case_names skip expand finish])
  case (skip u rest)
  (* The stack just shrinks *)
  have new_stack: "dfs_stack (dfs_step graph state) = rest"
    using skip(3) by simp
  show ?thesis
    unfolding dfs_previsit_ordered.simps new_stack
  proof (intro allI impI, elim conjE)
    fix prefix v post x
    assume "rest = prefix @ PostVisit v # post" and "PreVisit x \<in> set prefix"
    then have "dfs_stack state = (PreVisit u # prefix) @ PostVisit v # post"
      and "PreVisit x \<in> set (PreVisit u # prefix)"
      using skip(1) by simp_all
    then show "reachable graph v x"
      using previsit_ordered unfolding dfs_previsit_ordered.simps by blast
  qed
next
  case (finish u rest)
  (* The stack just shrinks *)
  have new_stack: "dfs_stack (dfs_step graph state) = rest"
    using finish(2) by simp
  show ?thesis
    unfolding dfs_previsit_ordered.simps new_stack
  proof (intro allI impI, elim conjE)
    fix prefix v post x
    assume "rest = prefix @ PostVisit v # post" and "PreVisit x \<in> set prefix"
    then have "dfs_stack state = (PostVisit u # prefix) @ PostVisit v # post"
      and "PreVisit x \<in> set (PostVisit u # prefix)"
      using finish(1) by simp_all
    then show "reachable graph v x"
      using previsit_ordered unfolding dfs_previsit_ordered.simps by blast
  qed
next
  case (expand u rest)
  let ?ns = "the (fmlookup graph u)"
  have new_stack: "dfs_stack (dfs_step graph state) = map PreVisit ?ns @ PostVisit u # rest"
    using expand(4) by simp
  show ?thesis
    unfolding dfs_previsit_ordered.simps new_stack
  proof (intro allI impI, elim conjE)
    fix prefix v post x
    assume split: "map PreVisit ?ns @ PostVisit u # rest = prefix @ PostVisit v # post"
      and x_in: "PreVisit x \<in> set prefix"
    from split_expanded_stack[OF split] show "reachable graph v x"
    proof (elim disjE exE conjE)
      (* Split at the new PostVisit u: x is a successor of u *)
      assume "prefix = map PreVisit ?ns" "v = u" "post = rest"
      then have "has_edge graph u x"
        using x_in expanded_successor[OF expand(3)] by blast
      then show ?thesis
        using \<open>v = u\<close> expand(3) reachable.reachable_refl reachable.reachable_step by blast
    next
      (* Split inside the old rest of the stack *)
      fix prefix'
      assume prefix_eq: "prefix = map PreVisit ?ns @ PostVisit u # prefix'"
        and rest_eq: "rest = prefix' @ PostVisit v # post"
      have old_split: "dfs_stack state = (PreVisit u # prefix') @ PostVisit v # post"
        using expand(1) rest_eq by simp
      have "PreVisit u \<in> set (PreVisit u # prefix')"
        by simp
      then have v_reaches_u: "reachable graph v u"
        using old_split previsit_ordered unfolding dfs_previsit_ordered.simps by blast
      show ?thesis
      proof (cases "PreVisit x \<in> set prefix'")
        case True
        then have "PreVisit x \<in> set (PreVisit u # prefix')"
          by simp
        then show ?thesis
          using old_split previsit_ordered unfolding dfs_previsit_ordered.simps by blast
      next
        case False
        (* x was pushed by this step, so it is a successor of u *)
        have "PreVisit x \<in> set (map PreVisit ?ns)"
          using prefix_eq x_in False by auto
        then have "has_edge graph u x"
          by (rule expanded_successor[OF expand(3)])
        then have "reachable graph u x"
          using expand(3) reachable.reachable_refl reachable.reachable_step by blast
        then show ?thesis
          using v_reaches_u reachable_trans by blast
      qed
    qed
  qed
qed

(* Lemma: dfs_step preserves the PostVisit ordering property *)
lemma dfs_step_preserves_postvisit_ordered:
  assumes valid: "dfs_state_valid graph state"
    and postvisit_ordered: "dfs_postvisit_ordered graph state"
    and previsit_ordered: "dfs_previsit_ordered graph state"
    and non_empty: "dfs_stack state \<noteq> []"
  shows "dfs_postvisit_ordered graph (dfs_step graph state)"
proof (cases rule: dfs_step_cases[OF valid non_empty, case_names skip expand finish])
  case (skip u rest)
  (* The stack just shrinks *)
  have new_stack: "dfs_stack (dfs_step graph state) = rest"
    using skip(3) by simp
  show ?thesis
    unfolding dfs_postvisit_ordered.simps new_stack
  proof (intro allI impI, elim conjE)
    fix prefix v post x
    assume "rest = prefix @ PostVisit v # post" and "PostVisit x \<in> set prefix"
    then have "dfs_stack state = (PreVisit u # prefix) @ PostVisit v # post"
      and "PostVisit x \<in> set (PreVisit u # prefix)"
      using skip(1) by simp_all
    then show "reachable graph v x"
      using postvisit_ordered unfolding dfs_postvisit_ordered.simps by blast
  qed
next
  case (finish u rest)
  (* The stack just shrinks *)
  have new_stack: "dfs_stack (dfs_step graph state) = rest"
    using finish(2) by simp
  show ?thesis
    unfolding dfs_postvisit_ordered.simps new_stack
  proof (intro allI impI, elim conjE)
    fix prefix v post x
    assume "rest = prefix @ PostVisit v # post" and "PostVisit x \<in> set prefix"
    then have "dfs_stack state = (PostVisit u # prefix) @ PostVisit v # post"
      and "PostVisit x \<in> set (PostVisit u # prefix)"
      using finish(1) by simp_all
    then show "reachable graph v x"
      using postvisit_ordered unfolding dfs_postvisit_ordered.simps by blast
  qed
next
  case (expand u rest)
  let ?ns = "the (fmlookup graph u)"
  have new_stack: "dfs_stack (dfs_step graph state) = map PreVisit ?ns @ PostVisit u # rest"
    using expand(4) by simp
  show ?thesis
    unfolding dfs_postvisit_ordered.simps new_stack
  proof (intro allI impI, elim conjE)
    fix prefix v post x
    assume split: "map PreVisit ?ns @ PostVisit u # rest = prefix @ PostVisit v # post"
      and x_in: "PostVisit x \<in> set prefix"
    from split_expanded_stack[OF split] show "reachable graph v x"
    proof (elim disjE exE conjE)
      (* Split at the new PostVisit u: the prefix has no PostVisit frames *)
      assume "prefix = map PreVisit ?ns" "v = u" "post = rest"
      then show ?thesis
        using x_in by auto
    next
      (* Split inside the old rest of the stack *)
      fix prefix'
      assume prefix_eq: "prefix = map PreVisit ?ns @ PostVisit u # prefix'"
        and rest_eq: "rest = prefix' @ PostVisit v # post"
      have old_split: "dfs_stack state = (PreVisit u # prefix') @ PostVisit v # post"
        using expand(1) rest_eq by simp
      show ?thesis
      proof (cases "x = u")
        case True
        (* PreVisit u was before PostVisit v on the old stack *)
        have "PreVisit u \<in> set (PreVisit u # prefix')"
          by simp
        then show ?thesis
          using True old_split previsit_ordered unfolding dfs_previsit_ordered.simps by blast
      next
        case False
        have "PostVisit x \<in> set (PreVisit u # prefix')"
          using prefix_eq x_in False by auto
        then show ?thesis
          using old_split postvisit_ordered unfolding dfs_postvisit_ordered.simps by blast
      qed
    qed
  qed
qed

(*-----------------------------------------------------------------------------*)
(* DFS step expands the WillFinishBeforeMe sets *)
(*-----------------------------------------------------------------------------*)

(* Lemma: If PostVisit x is on the stack (but not on top), then it is still on the stack
   after dfs_step, and its will_finish_before_me set does not shrink *)
lemma dfs_step_expands_will_finish:
  assumes valid: "dfs_state_valid graph state"
    and stack: "dfs_stack state = prefix @ PostVisit x # post"
    and prefix_nonempty: "prefix \<noteq> []"
  shows "\<exists>prefix'. dfs_stack (dfs_step graph state) = prefix' @ PostVisit x # post \<and>
                   will_finish_before_me graph state prefix \<subseteq>
                   will_finish_before_me graph (dfs_step graph state) prefix'"
proof -
  have non_empty: "dfs_stack state \<noteq> []"
    using stack by simp
  obtain f prefix'' where prefix_eq: "prefix = f # prefix''"
    using prefix_nonempty by (cases prefix) auto
  show ?thesis
  proof (cases rule: dfs_step_cases[OF valid non_empty, case_names skip expand finish])
    case (skip u rest)
    (* The visited PreVisit u is popped *)
    have new_visited: "dfs_visited (dfs_step graph state) = dfs_visited state"
      and new_finish: "dfs_finish_order (dfs_step graph state) = dfs_finish_order state"
      and new_stack: "dfs_stack (dfs_step graph state) = rest"
      using skip(3) by simp_all
    have prefix_u: "prefix = PreVisit u # prefix''"
      and rest_eq: "rest = prefix'' @ PostVisit x # post"
      using prefix_eq stack skip(1) by simp_all
    show ?thesis
    proof (intro exI conjI)
      show "dfs_stack (dfs_step graph state) = prefix'' @ PostVisit x # post"
        unfolding new_stack by (rule rest_eq)
      (* PreVisit u contributes nothing, as u is visited *)
      show "will_finish_before_me graph state prefix \<subseteq>
            will_finish_before_me graph (dfs_step graph state) prefix''"
        unfolding will_finish_before_me.simps new_visited new_finish prefix_u
        using skip(2) by (auto dest: unvisited_path_start_unvisited)
    qed
  next
    case (finish u rest)
    (* PostVisit u is popped, and u is added to the finish order *)
    have new_visited: "dfs_visited (dfs_step graph state) = dfs_visited state"
      and new_finish: "dfs_finish_order (dfs_step graph state) = u # dfs_finish_order state"
      and new_stack: "dfs_stack (dfs_step graph state) = rest"
      using finish(2) by simp_all
    have prefix_u: "prefix = PostVisit u # prefix''"
      and rest_eq: "rest = prefix'' @ PostVisit x # post"
      using prefix_eq stack finish(1) by simp_all
    show ?thesis
    proof (intro exI conjI)
      show "dfs_stack (dfs_step graph state) = prefix'' @ PostVisit x # post"
        unfolding new_stack by (rule rest_eq)
      show "will_finish_before_me graph state prefix \<subseteq>
            will_finish_before_me graph (dfs_step graph state) prefix''"
        unfolding will_finish_before_me.simps new_visited new_finish prefix_u by auto
    qed
  next
    case (expand u rest)
    (* PreVisit u is replaced by u's successors and PostVisit u, and u becomes visited *)
    let ?ns = "the (fmlookup graph u)"
    let ?prefix' = "map PreVisit ?ns @ PostVisit u # prefix''"
    have new_visited: "dfs_visited (dfs_step graph state) = finsert u (dfs_visited state)"
      and new_finish: "dfs_finish_order (dfs_step graph state) = dfs_finish_order state"
      and new_stack: "dfs_stack (dfs_step graph state) = map PreVisit ?ns @ PostVisit u # rest"
      using expand(4) by simp_all
    have prefix_u: "prefix = PreVisit u # prefix''"
      and rest_eq: "rest = prefix'' @ PostVisit x # post"
      using prefix_eq stack expand(1) by simp_all
    show ?thesis
    proof (intro exI conjI)
      show "dfs_stack (dfs_step graph state) = ?prefix' @ PostVisit x # post"
        unfolding new_stack using rest_eq by simp
      show "will_finish_before_me graph state prefix \<subseteq>
            will_finish_before_me graph (dfs_step graph state) ?prefix'"
      proof
        fix z
        assume z: "z \<in> will_finish_before_me graph state prefix"
        have new_iff: "z \<in> will_finish_before_me graph (dfs_step graph state) ?prefix' \<longleftrightarrow>
                         z \<in> set (dfs_finish_order state) \<or> PostVisit z \<in> set ?prefix' \<or>
                         (\<exists>w. PreVisit w \<in> set ?prefix' \<and>
                              unvisited_path graph (finsert u (dfs_visited state)) w z)"
          unfolding will_finish_before_me.simps new_visited new_finish by simp
        show "z \<in> will_finish_before_me graph (dfs_step graph state) ?prefix'"
        proof (cases "z = u")
          case True
          (* u itself: PostVisit u is in the new prefix *)
          then show ?thesis
            unfolding new_iff by simp
        next
          case z_neq_u: False
          have "z \<in> set (dfs_finish_order state) \<or> PostVisit z \<in> set prefix'' \<or>
                (\<exists>w. PreVisit w \<in> set (PreVisit u # prefix'') \<and>
                     unvisited_path graph (dfs_visited state) w z)"
            using z unfolding will_finish_before_me.simps prefix_u by simp
          then show ?thesis
          proof (elim disjE exE conjE)
            assume "z \<in> set (dfs_finish_order state)"
            then show ?thesis
              unfolding new_iff by simp
          next
            assume "PostVisit z \<in> set prefix''"
            then show ?thesis
              unfolding new_iff by simp
          next
            fix w
            assume w_in: "PreVisit w \<in> set (PreVisit u # prefix'')"
              and path: "unvisited_path graph (dfs_visited state) w z"
            (* Either the path from w avoids u, or its part after u starts at a successor of u *)
            from unvisited_path_finsert[OF path z_neq_u] show ?thesis
            proof (elim disjE exE conjE)
              assume path': "unvisited_path graph (finsert u (dfs_visited state)) w z"
              have "w \<noteq> u"
                using unvisited_path_start_unvisited[OF path'] by simp
              then have "PreVisit w \<in> set prefix''"
                using w_in by simp
              then show ?thesis
                unfolding new_iff using path' by auto
            next
              fix n
              assume edge: "has_edge graph u n"
                and path': "unvisited_path graph (finsert u (dfs_visited state)) n z"
              have "PreVisit n \<in> set (map PreVisit ?ns)"
                by (rule successor_in_expanded[OF expand(3) edge])
              then show ?thesis
                unfolding new_iff using path' by auto
            qed
          qed
        qed
      qed
    qed
  qed
qed

(*-----------------------------------------------------------------------------*)
(* Helper lemmas for finish order invariant *)
(*-----------------------------------------------------------------------------*)

(* Lemma: Constructing a path through an edge without revisiting start vertex
   when the edge crosses SCC boundaries *)
lemma path_through_edge_without_revisit:
  assumes "valid_graph graph"
    and "reachable graph x c"
    and "has_edge graph c d"
    and "reachable graph d z"
    and "\<not>(in_same_scc graph c d)"  (* c and d are in different SCCs *)
    and "in_same_scc graph x c"  (* x and c are in the same SCC *)
    and "in_same_scc graph d z"  (* d and z are in the same SCC *)
  shows "\<exists>path. valid_path graph path \<and>
               path_start path = x \<and>
               path_end path = z \<and>
               (\<forall>v. v \<in> set (tl path) \<longrightarrow> v \<noteq> x) \<and>
               (\<forall>v. v \<in> set path \<longrightarrow> in_same_scc graph v c \<or> in_same_scc graph v d)"
proof (cases "x = c")
  case x_eq_c: True
  (* x = c, so we have x -> d -> ... -> z *)
  (* Just prepend x to a path from d to z *)

  (* Get path from d to z *)
  obtain path_dz where path_dz_props:
    "valid_path graph path_dz"
    "path_start path_dz = d"
    "path_end path_dz = z"
    using reachable_implies_valid_path[OF assms(1,4)]
    by blast

  (* Prepend x to path_dz *)
  define path where "path = x # path_dz"

  have "valid_path graph path"
    unfolding path_def
    by (metis assms(3) path_dz_props(1,2) path_start.elims valid_path.simps(1,3) x_eq_c)

  moreover have "path_start path = x"
    unfolding path_def by simp

  moreover have "path_end path = z"
    unfolding path_def using path_dz_props(1,3)
    by (cases path_dz) auto

  moreover have "\<forall>v. v \<in> set (tl path) \<longrightarrow> v \<noteq> x"
  proof (intro allI impI)
    fix v
    assume "v \<in> set (tl path)"
    then have "v \<in> set path_dz"
      unfolding path_def by simp
    (* v is on path from d to z, so v is in same SCC as d *)
    (* x = c and c, d are in different SCCs, so v \<noteq> x *)
    have "in_same_scc graph v d"
      using path_in_scc_all_in_scc[OF assms(1) path_dz_props(1)] assms(7)
      using path_dz_props(2,3) \<open>v \<in> set path_dz\<close>
      by blast 
    moreover have "in_same_scc graph x c"
      using assms(6) by simp
    ultimately show "v \<noteq> x"
      using assms(5) x_eq_c by auto
  qed

  moreover have "\<forall>v. v \<in> set path \<longrightarrow> in_same_scc graph v c \<or> in_same_scc graph v d"
  proof (intro allI impI)
    fix v
    assume "v \<in> set path"
    then have "v = x \<or> v \<in> set path_dz"
      unfolding path_def by auto
    then show "in_same_scc graph v c \<or> in_same_scc graph v d"
    proof
      assume "v = x"
      then show ?thesis using x_eq_c assms(6) by simp
    next
      assume "v \<in> set path_dz"
      then have "in_same_scc graph v d"
        using path_in_scc_all_in_scc[OF assms(1) path_dz_props(1)] assms(7)
        using path_dz_props(2,3)
        by blast 
      then show ?thesis by simp
    qed
  qed

  ultimately show ?thesis by blast
next
  case False
  (* x \<noteq> c *)
  (* Get path from x to c without revisiting x *)
  obtain path_xc where path_xc_props:
    "valid_path graph path_xc"
    "path_start path_xc = x"
    "path_end path_xc = c"
    "\<forall>v. v \<in> set (tl path_xc) \<longrightarrow> v \<noteq> x"
    using reachable_implies_path_without_revisit[OF assms(1,2) False]
    by blast

  (* Get path from d to z *)
  obtain path_dz where path_dz_props:
    "valid_path graph path_dz"
    "path_start path_dz = d"
    "path_end path_dz = z"
    using reachable_implies_valid_path[OF assms(1,4)]
    by blast

  (* Concatenate: path_xc @ path_dz using the edge c -> d *)
  define combined where "combined = path_xc @ path_dz"

  have "valid_path graph combined"
    using path_concat_with_edge[OF assms(1) path_xc_props(1) path_dz_props(1)
          path_xc_props(3) path_dz_props(2) assms(3)]
    unfolding combined_def by simp

  moreover have "path_start combined = x"
    using path_concat_with_edge[OF assms(1) path_xc_props(1) path_dz_props(1)
          path_xc_props(3) path_dz_props(2) assms(3)]
    using path_xc_props(2) unfolding combined_def by simp

  moreover have "path_end combined = z"
    using path_concat_with_edge[OF assms(1) path_xc_props(1) path_dz_props(1)
          path_xc_props(3) path_dz_props(2) assms(3)]
    using path_dz_props(3) unfolding combined_def by simp

  moreover have "\<forall>v. v \<in> set (tl combined) \<longrightarrow> v \<noteq> x"
  proof (intro allI impI)
    fix v
    assume v_in_tl: "v \<in> set (tl combined)"
    then have "v \<in> set (tl path_xc) \<or> v \<in> set path_dz"
      unfolding combined_def
      using path_xc_props(1)
      by (cases path_xc) (auto simp: tl_append)
    then show "v \<noteq> x"
    proof
      assume "v \<in> set (tl path_xc)"
      then show "v \<noteq> x" using path_xc_props(4) by blast
    next
      assume v_in_dz: "v \<in> set path_dz"
      (* v is on path from d to z, so d reaches v and v reaches z *)
      have "reachable graph d v \<and> reachable graph v z"
        using vertex_on_path_reachable[OF assms(1) path_dz_props(1,2,3) v_in_dz]
        by simp
      then have d_reaches_v: "reachable graph d v"
        and v_reaches_z: "reachable graph v z" by simp_all

      (* x reaches c, and c reaches d through the edge *)
      have c_reaches_d: "reachable graph c d"
        using assms(1,3) reachable.reachable_step
        by (metis fmdom_notD has_edge.elims(1) has_vertex.simps option.case_eq_if
            reachable.reachable_refl)

      (* Now show x \<noteq> v by contradiction *)
      show "v \<noteq> x"
      proof (rule ccontr)
        assume "\<not>(v \<noteq> x)"
        then have "v = x" by simp
        (* Then d reaches x and x reaches c, so d reaches c *)
        have "reachable graph d c"
          using d_reaches_v \<open>v = x\<close> assms(2) reachable_trans by blast
        (* Combined with c reaches d, we have c and d in same SCC *)
        then have "in_same_scc graph c d"
          using c_reaches_d by simp
        (* Contradiction with assms(5) *)
        then show False using assms(5) by simp
      qed
    qed
  qed

  moreover have "\<forall>v. v \<in> set combined \<longrightarrow> in_same_scc graph v c \<or> in_same_scc graph v d"
  proof (intro allI impI)
    fix v
    assume "v \<in> set combined"
    then have "v \<in> set path_xc \<or> v \<in> set path_dz"
      unfolding combined_def by auto
    then show "in_same_scc graph v c \<or> in_same_scc graph v d"
    proof
      assume "v \<in> set path_xc"
      (* v is on path from x to c, and x and c are in same SCC *)
      then have "in_same_scc graph v c"
        using path_in_scc_all_in_scc[OF assms(1) path_xc_props(1)] assms(6)
        using path_xc_props(2,3)
        using in_same_scc_trans by blast 
      then show ?thesis by simp
    next
      assume "v \<in> set path_dz"
      (* v is on path from d to z, and d and z are in same SCC *)
      then have "in_same_scc graph v d"
        using path_in_scc_all_in_scc[OF assms(1) path_dz_props(1)] assms(7)
        using path_dz_props(2,3)
        by blast 
      then show ?thesis by simp
    qed
  qed

  ultimately show ?thesis by blast
qed

(* Lemma: If all of d's SCC is finished and some vertex of c's SCC is not, then after
   finishing one more (previously unfinished) vertex v, case 2 or case 3 holds *)
lemma finish_order_2_after_finish:
  assumes new_finish: "dfs_finish_order state' = v # dfs_finish_order state"
    and v_vertex: "has_vertex graph v"
    and v_unfinished: "\<not> List.member (dfs_finish_order state) v"
    and case2_before: "finish_order_2 graph state c d"
  shows "finish_order_2 graph state' c d \<or> finish_order_3 graph state' c d"
proof -
  have all_d_finished: "\<forall>u. has_vertex graph u \<and> in_same_scc graph u d \<longrightarrow>
                             List.member (dfs_finish_order state) u"
    and c_unfinished: "\<exists>u. has_vertex graph u \<and> in_same_scc graph u c \<and>
                             \<not>List.member (dfs_finish_order state) u"
    using case2_before unfolding finish_order_2.simps by blast+
  show ?thesis
  proof (cases "in_same_scc graph v c \<and>
                (\<forall>u. has_vertex graph u \<and> in_same_scc graph u c \<and> u \<noteq> v \<longrightarrow>
                     List.member (dfs_finish_order state) u)")
    case True
    (* v was the last unfinished vertex of c's SCC, and is now the first in the
       finish order, before all of d's SCC: case 3 *)
    have "finish_order_3 graph state' c d"
      unfolding finish_order_3.simps new_finish
    proof (intro conjI exI)
      show "\<forall>u. has_vertex graph u \<and> (in_same_scc graph u c \<or> in_same_scc graph u d) \<longrightarrow>
                List.member (v # dfs_finish_order state) u"
        using True all_d_finished by (auto simp: member_rec(1))
      show "has_vertex graph v"
        by (rule v_vertex)
      show "in_same_scc graph v c"
        using True by blast
      show "\<forall>v_d. has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
                  index_of v (v # dfs_finish_order state) < index_of v_d (v # dfs_finish_order state)"
        using all_d_finished v_unfinished by auto
    qed
    then show ?thesis by blast
  next
    case False
    (* Some vertex of c's SCC other than v is still unfinished: case 2 *)
    have "\<exists>u. has_vertex graph u \<and> in_same_scc graph u c \<and>
              \<not>List.member (v # dfs_finish_order state) u"
    proof (cases "in_same_scc graph v c")
      case True
      with False obtain u where "has_vertex graph u" "in_same_scc graph u c" "u \<noteq> v"
          "\<not>List.member (dfs_finish_order state) u"
        by blast
      then show ?thesis
        by (auto simp: member_rec(1))
    next
      case v_not_in_c: False
      obtain u where u: "has_vertex graph u" "in_same_scc graph u c"
          "\<not>List.member (dfs_finish_order state) u"
        using c_unfinished by blast
      have "u \<noteq> v"
        using u(2) v_not_in_c by blast
      then show ?thesis
        using u by (auto simp: member_rec(1))
    qed
    then have "finish_order_2 graph state' c d"
      unfolding finish_order_2.simps new_finish
      using all_d_finished by (auto simp: member_rec(1))
    then show ?thesis by blast
  qed
qed

(*-----------------------------------------------------------------------------*)
(* DFS step preserves dfs_finish_order_prop *)
(*-----------------------------------------------------------------------------*)

(* Case 1: Previously, all vertices in both SCCs were unvisited *)
lemma dfs_step_preserves_finish_order_case1:
  assumes valid: "dfs_state_valid graph state"
    and non_empty: "dfs_stack state \<noteq> []"
    and edge_cd: "has_edge graph c d"
    and diff_scc: "\<not>(in_same_scc graph c d)"
    and case1_before: "finish_order_1 graph state c d"
  shows "finish_order_1 graph (dfs_step graph state) c d \<or>
         finish_order_4 graph (dfs_step graph state) c d \<or>
         finish_order_5 graph (dfs_step graph state) c d"
proof -
  have valid_g: "valid_graph graph"
    using valid by simp
  (* From case1_before, all vertices in both SCCs are unvisited *)
  have all_unvisited: "\<forall>v. has_vertex graph v \<and> (in_same_scc graph v c \<or> in_same_scc graph v d) \<longrightarrow>
                            v |\<notin>| dfs_visited state"
    using case1_before by simp
  show ?thesis
  proof (cases rule: dfs_step_cases[OF valid non_empty, case_names skip expand finish])
    case (skip u rest)
    (* The visited set is unchanged: case 1 persists *)
    have new_visited: "dfs_visited (dfs_step graph state) = dfs_visited state"
      using skip(3) by simp
    have "finish_order_1 graph (dfs_step graph state) c d"
      unfolding finish_order_1.simps new_visited by (rule all_unvisited)
    then show ?thesis by blast
  next
    case (finish u rest)
    (* The visited set is unchanged: case 1 persists *)
    have new_visited: "dfs_visited (dfs_step graph state) = dfs_visited state"
      using finish(2) by simp
    have "finish_order_1 graph (dfs_step graph state) c d"
      unfolding finish_order_1.simps new_visited by (rule all_unvisited)
    then show ?thesis by blast
  next
    case (expand x rest)
    (* x becomes visited *)
    let ?ns = "the (fmlookup graph x)"
    have new_visited: "dfs_visited (dfs_step graph state) = finsert x (dfs_visited state)"
      and new_finish: "dfs_finish_order (dfs_step graph state) = dfs_finish_order state"
      and new_stack: "dfs_stack (dfs_step graph state) = map PreVisit ?ns @ PostVisit x # rest"
      using expand(4) by simp_all
    have x_vertex: "has_vertex graph x"
      by (rule expand(3))

    (* Anything reachable by an unvisited path from a successor of x is in the
       will_finish_before_me set of the new PostVisit x *)
    have wfbm_new: "z \<in> will_finish_before_me graph (dfs_step graph state) (map PreVisit ?ns)"
      if "has_edge graph x w" "unvisited_path graph (finsert x (dfs_visited state)) w z" for w z
    proof -
      have "PreVisit w \<in> set (map PreVisit ?ns)"
        by (rule successor_in_expanded[OF x_vertex that(1)])
      then show ?thesis
        unfolding will_finish_before_me.simps new_visited using that(2) by blast
    qed

    show ?thesis
    proof (cases "in_same_scc graph x c \<or> in_same_scc graph x d")
      case False
      (* x is not in either SCC: case 1 persists *)
      have "finish_order_1 graph (dfs_step graph state) c d"
        unfolding finish_order_1.simps new_visited using all_unvisited False by auto
      then show ?thesis by blast
    next
      case x_in_some_scc: True
      show ?thesis
      proof (cases "in_same_scc graph x c")
        case x_in_c: True
        (* x is in c's SCC: case 4 holds, with PostVisit x as the witness *)
        have "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<longrightarrow>
                   z \<in> will_finish_before_me graph (dfs_step graph state) (map PreVisit ?ns)"
        proof (intro allI impI)
          fix z
          assume z_hyp: "has_vertex graph z \<and> in_same_scc graph z d"

          (* Get a path from x to z, through c and d, that does not revisit x *)
          have x_reaches_c: "reachable graph x c"
            using x_in_c by simp
          have d_reaches_z: "reachable graph d z"
            using z_hyp by simp
          have d_z: "in_same_scc graph d z"
            using z_hyp in_same_scc_sym by blast
          obtain path_xz where path_xz_props:
            "valid_path graph path_xz"
            "path_start path_xz = x"
            "path_end path_xz = z"
            "\<forall>v. v \<in> set (tl path_xz) \<longrightarrow> v \<noteq> x"
            "\<forall>v. v \<in> set path_xz \<longrightarrow> in_same_scc graph v c \<or> in_same_scc graph v d"
            using path_through_edge_without_revisit[OF valid_g x_reaches_c edge_cd d_reaches_z
                    diff_scc x_in_c d_z]
            by blast

          (* The path has at least two vertices: x, then a successor w of x *)
          have "path_xz \<noteq> []"
            using path_xz_props(1) by (cases path_xz) auto
          obtain w path_xz_rest where path_xz_decomp: "path_xz = x # w # path_xz_rest"
            using path_xz_props
            by (metis \<open>path_xz \<noteq> []\<close> diff_scc in_same_scc_sym in_same_scc_trans neq_Nil_conv
                path_end.simps(2) path_start.simps(2) x_in_c z_hyp)
          have edge_xw: "has_edge graph x w"
            using path_xz_props(1) path_xz_decomp by auto

          (* The rest of the path, from w to z, is unvisited in the new state *)
          have combined_valid: "valid_path graph (w # path_xz_rest)"
            using path_xz_props(1) path_xz_decomp by auto
          have combined_end: "path_end (w # path_xz_rest) = z"
            using path_xz_props(3) path_xz_decomp by (metis path_end.simps(3))
          have "all_unvisited (finsert x (dfs_visited state)) (w # path_xz_rest)"
          proof -
            have neq_x: "\<forall>v. v \<in> set (w # path_xz_rest) \<longrightarrow> v \<noteq> x"
              using path_xz_props(4) path_xz_decomp by auto
            have "\<forall>v. v \<in> set (w # path_xz_rest) \<longrightarrow>
                      in_same_scc graph v c \<or> in_same_scc graph v d"
              using path_xz_props(5) path_xz_decomp by auto
            then have unvisited: "\<forall>v. v \<in> set (w # path_xz_rest) \<longrightarrow> v |\<notin>| dfs_visited state"
              using all_unvisited in_same_scc_vertices(1)[OF valid_g] by blast
            show ?thesis
              using neq_x unvisited
              by (meson all_unvisited.simps finsert_iff in_set_member)
          qed
          then have "unvisited_path graph (finsert x (dfs_visited state)) w z"
            by (rule valid_path_implies_unvisited_path[OF valid_g combined_valid path_start.simps(2)
                  combined_end])
          then show "z \<in> will_finish_before_me graph (dfs_step graph state) (map PreVisit ?ns)"
            by (rule wfbm_new[OF edge_xw])
        qed
        then have "finish_order_4 graph (dfs_step graph state) c d"
          unfolding finish_order_4.simps using x_vertex x_in_c new_stack by blast
        then show ?thesis by blast
      next
        case x_not_in_c: False
        (* x is in d's SCC: case 5 holds, with PostVisit x as the witness *)
        with x_in_some_scc have x_in_d: "in_same_scc graph x d"
          by blast

        (* Everything in d's SCC, apart from x, is in will_finish_before_me *)
        have "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<and> z \<noteq> x \<longrightarrow>
                   z \<in> will_finish_before_me graph (dfs_step graph state) (map PreVisit ?ns)"
        proof (intro allI impI)
          fix z
          assume z_hyp: "has_vertex graph z \<and> in_same_scc graph z d \<and> z \<noteq> x"
          have "in_same_scc graph x z"
            using x_in_d z_hyp by (meson in_same_scc_sym in_same_scc_trans)

          (* Get a successor p of x, and a path from p to z avoiding x *)
          obtain p where p_props:
            "has_edge graph x p"
            "in_same_scc graph p x"
            "\<exists>path. valid_path graph path \<and>
                    path_start path = p \<and>
                    path_end path = z \<and>
                    \<not>List.member path x"
            using scc_path_avoiding_vertex[OF valid_g \<open>in_same_scc graph x z\<close>] z_hyp by blast
          obtain path where path_props:
            "valid_path graph path"
            "path_start path = p"
            "path_end path = z"
            "\<not>List.member path x"
            using p_props(3) by blast

          (* All vertices on the path are in d's SCC (so were unvisited) and differ from x *)
          have p_in_d: "in_same_scc graph p d"
            using p_props(2) x_in_d by (meson in_same_scc_trans)
          have "all_unvisited (finsert x (dfs_visited state)) path"
          proof -
            have "\<forall>v. v \<in> set path \<longrightarrow> v \<noteq> x"
              using path_props(4) by (meson in_set_member)
            moreover have "\<forall>v. v \<in> set path \<longrightarrow> v |\<notin>| dfs_visited state"
            proof (intro allI impI)
              fix v
              assume "v \<in> set path"
              have "in_same_scc graph p z"
                using p_in_d z_hyp by (meson in_same_scc_sym in_same_scc_trans)
              then have "in_same_scc graph v p"
                using path_in_scc_all_in_scc[OF valid_g path_props(1)] path_props(2,3)
                  \<open>v \<in> set path\<close>
                by blast
              then have "in_same_scc graph v d"
                using p_in_d by (meson in_same_scc_trans)
              then show "v |\<notin>| dfs_visited state"
                using all_unvisited in_same_scc_vertices(1)[OF valid_g] by blast
            qed
            ultimately show ?thesis
              by (auto simp: in_set_member)
          qed
          then have "unvisited_path graph (finsert x (dfs_visited state)) p z"
            by (rule valid_path_implies_unvisited_path[OF valid_g path_props(1,2,3)])
          then show "z \<in> will_finish_before_me graph (dfs_step graph state) (map PreVisit ?ns)"
            by (rule wfbm_new[OF p_props(1)])
        qed

        (* c is unvisited, hence unfinished *)
        moreover have "\<exists>v. has_vertex graph v \<and> in_same_scc graph v c \<and>
                            \<not>List.member (dfs_finish_order (dfs_step graph state)) v"
        proof -
          have c_vertex: "has_vertex graph c"
            using edge_implies_vertices(1)[OF valid_g edge_cd] .
          have finish_visited: "\<forall>v. List.member (dfs_finish_order state) v \<longrightarrow> v |\<in>| dfs_visited state"
            using valid by simp
          have "c |\<notin>| dfs_visited state"
            using all_unvisited c_vertex in_same_scc_refl by blast
          then have "\<not>List.member (dfs_finish_order state) c"
            using finish_visited by blast
          then show ?thesis
            unfolding new_finish using c_vertex in_same_scc_refl by blast
        qed

        ultimately have "finish_order_5 graph (dfs_step graph state) c d"
          unfolding finish_order_5.simps using x_vertex x_in_d new_stack by blast
        then show ?thesis by blast
      qed
    qed
  qed
qed

(* Case 2: Previously, all vertices from d's SCC were finished,
   and at least one from c's SCC was unfinished *)
lemma dfs_step_preserves_finish_order_case2:
  assumes valid: "dfs_state_valid graph state"
    and non_empty: "dfs_stack state \<noteq> []"
    and case2_before: "finish_order_2 graph state c d"
  shows "finish_order_2 graph (dfs_step graph state) c d \<or>
         finish_order_3 graph (dfs_step graph state) c d"
proof (cases rule: dfs_step_cases[OF valid non_empty, case_names skip expand finish])
  case (skip u rest)
  (* The finish order is unchanged *)
  have new_finish: "dfs_finish_order (dfs_step graph state) = dfs_finish_order state"
    using skip(3) by simp
  have "finish_order_2 graph (dfs_step graph state) c d"
    using case2_before unfolding finish_order_2.simps new_finish .
  then show ?thesis by blast
next
  case (expand u rest)
  (* The finish order is unchanged *)
  have new_finish: "dfs_finish_order (dfs_step graph state) = dfs_finish_order state"
    using expand(4) by simp
  have "finish_order_2 graph (dfs_step graph state) c d"
    using case2_before unfolding finish_order_2.simps new_finish .
  then show ?thesis by blast
next
  case (finish v rest)
  (* v is added to the finish order *)
  have new_finish: "dfs_finish_order (dfs_step graph state) = v # dfs_finish_order state"
    using finish(2) by simp
  show ?thesis
    by (rule finish_order_2_after_finish[OF new_finish postvisit_top_props[OF valid finish(1)]
          case2_before])
qed

(* Case 3: Previously, all vertices in both SCCs were finished *)
lemma dfs_step_preserves_finish_order_case3:
  assumes valid: "dfs_state_valid graph state"
    and non_empty: "dfs_stack state \<noteq> []"
    and case3_before: "finish_order_3 graph state c d"
  shows "finish_order_3 graph (dfs_step graph state) c d"
proof (cases rule: dfs_step_cases[OF valid non_empty, case_names skip expand finish])
  case (skip u rest)
  (* The finish order is unchanged *)
  have new_finish: "dfs_finish_order (dfs_step graph state) = dfs_finish_order state"
    using skip(3) by simp
  show ?thesis
    using case3_before unfolding finish_order_3.simps new_finish .
next
  case (expand u rest)
  (* The finish order is unchanged *)
  have new_finish: "dfs_finish_order (dfs_step graph state) = dfs_finish_order state"
    using expand(4) by simp
  show ?thesis
    using case3_before unfolding finish_order_3.simps new_finish .
next
  case (finish v rest)
  (* v is added to the front of the finish order; v is not in either SCC
     (since those are already finished), so the relative order is preserved *)
  have new_finish: "dfs_finish_order (dfs_step graph state) = v # dfs_finish_order state"
    using finish(2) by simp
  have v_unfinished: "\<not> List.member (dfs_finish_order state) v"
    using postvisit_top_props(2)[OF valid finish(1)] .
  have all_finished: "\<forall>w. has_vertex graph w \<and> (in_same_scc graph w c \<or> in_same_scc graph w d) \<longrightarrow>
                           List.member (dfs_finish_order state) w"
    and "\<exists>v_c. has_vertex graph v_c \<and> in_same_scc graph v_c c \<and>
               (\<forall>v_d. has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
                  index_of v_c (dfs_finish_order state) < index_of v_d (dfs_finish_order state))"
    using case3_before unfolding finish_order_3.simps by blast+
  then obtain v_c where vc: "has_vertex graph v_c" "in_same_scc graph v_c c"
    and vc_first: "\<forall>v_d. has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
                     index_of v_c (dfs_finish_order state) < index_of v_d (dfs_finish_order state)"
    by blast
  show ?thesis
    unfolding finish_order_3.simps new_finish
  proof (intro conjI exI)
    show "\<forall>w. has_vertex graph w \<and> (in_same_scc graph w c \<or> in_same_scc graph w d) \<longrightarrow>
              List.member (v # dfs_finish_order state) w"
      using all_finished by (simp add: member_rec(1))
    show "has_vertex graph v_c"
      by (rule vc(1))
    show "in_same_scc graph v_c c"
      by (rule vc(2))
    show "\<forall>v_d. has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
                index_of v_c (v # dfs_finish_order state) < index_of v_d (v # dfs_finish_order state)"
    proof (intro allI impI)
      fix v_d
      assume vd: "has_vertex graph v_d \<and> in_same_scc graph v_d d"
      have "List.member (dfs_finish_order state) v_c" "List.member (dfs_finish_order state) v_d"
        using all_finished vc vd by blast+
      then have "v_c \<noteq> v" "v_d \<noteq> v"
        using v_unfinished by blast+
      then show "index_of v_c (v # dfs_finish_order state) < index_of v_d (v # dfs_finish_order state)"
        using vc_first vd by simp
    qed
  qed
qed

(* Case 4: Previously, at least one vertex in c's SCC was visited (not finished)
   and its WillFinishBeforeMe set contained everything in d's SCC *)
lemma dfs_step_preserves_finish_order_case4:
  assumes valid: "dfs_state_valid graph state"
    and non_empty: "dfs_stack state \<noteq> []"
    and case4_before: "finish_order_4 graph state c d"
  shows "finish_order_2 graph (dfs_step graph state) c d \<or>
         finish_order_3 graph (dfs_step graph state) c d \<or>
         finish_order_4 graph (dfs_step graph state) c d"
proof -
  (* From case4_before, get the witness vertex v in c's SCC *)
  obtain v prefix post where v_vertex: "has_vertex graph v"
    and v_in_c: "in_same_scc graph v c"
    and stack: "dfs_stack state = prefix @ PostVisit v # post"
    and d_in_wfbm: "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<longrightarrow>
                         z \<in> will_finish_before_me graph state prefix"
    using case4_before unfolding finish_order_4.simps by blast
  show ?thesis
  proof (cases "prefix = []")
    case True
    (* PostVisit v is on top of the stack, so all of d's SCC is already finished,
       and v is the next vertex to be finished *)
    have stack_v: "dfs_stack state = PostVisit v # post"
      using stack True by simp
    have new_finish: "dfs_finish_order (dfs_step graph state) = v # dfs_finish_order state"
      using stack_v by simp
    have v_unfinished: "\<not> List.member (dfs_finish_order state) v"
      using postvisit_top_props(2)[OF valid stack_v] .
    have "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<longrightarrow> List.member (dfs_finish_order state) z"
      using True d_in_wfbm by (simp add: member_def)
    then have "finish_order_2 graph state c d"
      unfolding finish_order_2.simps using v_vertex v_in_c v_unfinished by blast
    then show ?thesis
      using finish_order_2_after_finish[OF new_finish v_vertex v_unfinished] by blast
  next
    case False
    (* PostVisit v stays on the stack, and its will_finish_before_me set does not shrink *)
    obtain prefix' where new_stack: "dfs_stack (dfs_step graph state) = prefix' @ PostVisit v # post"
      and subset: "will_finish_before_me graph state prefix \<subseteq>
                   will_finish_before_me graph (dfs_step graph state) prefix'"
      using dfs_step_expands_will_finish[OF valid stack False] by blast
    have "finish_order_4 graph (dfs_step graph state) c d"
      unfolding finish_order_4.simps using v_vertex v_in_c new_stack subset d_in_wfbm by blast
    then show ?thesis by blast
  qed
qed

(* Case 5: Previously, at least one vertex x in d's SCC was visited (not finished)
   and its WillFinishBeforeMe set contained everything else in d's SCC *)
lemma dfs_step_preserves_finish_order_case5:
  assumes valid: "dfs_state_valid graph state"
    and postvisit_ordered: "dfs_postvisit_ordered graph state"
    and non_empty: "dfs_stack state \<noteq> []"
    and edge_cd: "has_edge graph c d"
    and diff_scc: "\<not>(in_same_scc graph c d)"
    and case5_before: "finish_order_5 graph state c d"
  shows "finish_order_2 graph (dfs_step graph state) c d \<or>
         finish_order_5 graph (dfs_step graph state) c d"
proof -
  have valid_g: "valid_graph graph"
    using valid by simp
  (* From case5_before, get an unfinished vertex v_c in c's SCC, and the witness x in d's SCC *)
  obtain v_c where v_c: "has_vertex graph v_c" "in_same_scc graph v_c c"
      "\<not>List.member (dfs_finish_order state) v_c"
    using case5_before unfolding finish_order_5.simps by blast
  obtain x prefix post where x_vertex: "has_vertex graph x"
    and x_in_d: "in_same_scc graph x d"
    and stack: "dfs_stack state = prefix @ PostVisit x # post"
    and d_in_wfbm: "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<and> z \<noteq> x \<longrightarrow>
                         z \<in> will_finish_before_me graph state prefix"
    using case5_before unfolding finish_order_5.simps by blast
  have v_c_neq_x: "v_c \<noteq> x"
    using v_c(2) x_in_d diff_scc by (metis in_same_scc_trans in_same_scc_sym)

  show ?thesis
  proof (cases "prefix = []")
    case True
    (* PostVisit x is on top of the stack: after finishing x, all of d's SCC is finished *)
    have stack_x: "dfs_stack state = PostVisit x # post"
      using stack True by simp
    have new_finish: "dfs_finish_order (dfs_step graph state) = x # dfs_finish_order state"
      using stack_x by simp
    have d_finished: "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<and> z \<noteq> x \<longrightarrow>
                          List.member (dfs_finish_order state) z"
      using True d_in_wfbm by (simp add: member_def)
    have "finish_order_2 graph (dfs_step graph state) c d"
      unfolding finish_order_2.simps new_finish
      using d_finished v_c v_c_neq_x by (auto simp: member_rec(1))
    then show ?thesis by blast
  next
    case False
    (* PostVisit x stays on the stack, and its will_finish_before_me set does not shrink *)
    obtain prefix' where new_stack: "dfs_stack (dfs_step graph state) = prefix' @ PostVisit x # post"
      and subset: "will_finish_before_me graph state prefix \<subseteq>
                   will_finish_before_me graph (dfs_step graph state) prefix'"
      using dfs_step_expands_will_finish[OF valid stack False] by blast

    (* v_c is still unfinished: if this step finishes some w, then w \<noteq> v_c *)
    have "\<not>List.member (dfs_finish_order (dfs_step graph state)) v_c"
    proof (cases rule: dfs_step_cases[OF valid non_empty, case_names skip expand finish])
      case (skip u rest)
      have new_finish: "dfs_finish_order (dfs_step graph state) = dfs_finish_order state"
        using skip(3) by simp
      show ?thesis
        unfolding new_finish by (rule v_c(3))
    next
      case (expand u rest)
      have new_finish: "dfs_finish_order (dfs_step graph state) = dfs_finish_order state"
        using expand(4) by simp
      show ?thesis
        unfolding new_finish by (rule v_c(3))
    next
      case (finish w rest)
      have new_finish: "dfs_finish_order (dfs_step graph state) = w # dfs_finish_order state"
        using finish(2) by simp
      (* PostVisit w is above PostVisit x on the stack, so x reaches w *)
      obtain prefix'' where "prefix = PostVisit w # prefix''"
        using stack finish(1) False by (cases prefix) auto
      then have "PostVisit w \<in> set prefix"
        by simp
      then have x_reaches_w: "reachable graph x w"
        using stack postvisit_ordered unfolding dfs_postvisit_ordered.simps by blast
      (* If w were in c's SCC, then d would reach c; but c reaches d, contradiction *)
      have "w \<noteq> v_c"
      proof
        assume "w = v_c"
        then have "reachable graph d c"
          using x_reaches_w x_in_d v_c(2) by (meson in_same_scc.simps reachable_trans)
        moreover have "reachable graph c d"
          using edge_cd edge_implies_vertices(1)[OF valid_g edge_cd]
            reachable.reachable_refl reachable.reachable_step
          by blast
        ultimately show False
          using diff_scc by simp
      qed
      then show ?thesis
        unfolding new_finish using v_c(3) by (simp add: member_rec(1))
    qed

    then have "finish_order_5 graph (dfs_step graph state) c d"
      unfolding finish_order_5.simps
      using v_c(1,2) x_vertex x_in_d new_stack subset d_in_wfbm by blast
    then show ?thesis by blast
  qed
qed

(* Main corollary: dfs_step preserves the finish order invariant *)
corollary dfs_step_preserves_finish_order:
  assumes valid: "dfs_state_valid graph state"
    and previsit_ordered: "dfs_previsit_ordered graph state"
    and postvisit_ordered: "dfs_postvisit_ordered graph state"
    and non_empty: "dfs_stack state \<noteq> []"
    and finish_order_inv: "dfs_finish_order_prop graph state"
  shows "dfs_finish_order_prop graph (dfs_step graph state)"
  unfolding dfs_finish_order_prop.simps
proof (intro allI impI, elim conjE)
  fix c d
  assume edge_cd: "has_edge graph c d" and diff_scc: "\<not>(in_same_scc graph c d)"
  then have "finish_order_1 graph state c d \<or> finish_order_2 graph state c d \<or>
             finish_order_3 graph state c d \<or> finish_order_4 graph state c d \<or>
             finish_order_5 graph state c d"
    using finish_order_inv unfolding dfs_finish_order_prop.simps by blast
  then show "finish_order_1 graph (dfs_step graph state) c d \<or>
             finish_order_2 graph (dfs_step graph state) c d \<or>
             finish_order_3 graph (dfs_step graph state) c d \<or>
             finish_order_4 graph (dfs_step graph state) c d \<or>
             finish_order_5 graph (dfs_step graph state) c d"
    using dfs_step_preserves_finish_order_case1[OF valid non_empty edge_cd diff_scc]
      dfs_step_preserves_finish_order_case2[OF valid non_empty]
      dfs_step_preserves_finish_order_case3[OF valid non_empty]
      dfs_step_preserves_finish_order_case4[OF valid non_empty]
      dfs_step_preserves_finish_order_case5[OF valid postvisit_ordered non_empty edge_cd diff_scc]
    by blast
qed

end
