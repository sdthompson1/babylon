theory Kosaraju2
  imports Kosaraju1
begin

(* Kosaraju's algorithm for finding strongly connected components: Part 2. *)

(*-----------------------------------------------------------------------------*)
(* DFS step preserves previsit_ordered and postvisit_ordered *)
(*-----------------------------------------------------------------------------*)

(* Lemma: dfs_step preserves the PreVisit ordering property *)
lemma dfs_step_preserves_previsit_ordered:
  assumes valid: "dfs_state_valid graph state"
    and previsit_ordered: "dfs_previsit_ordered graph state"
    and non_empty: "dfs_stack state \<noteq> []"
  shows "dfs_previsit_ordered graph (dfs_step graph state)"
proof -
  obtain frame rest where stack_split: "dfs_stack state = frame # rest"
    using non_empty by (cases "dfs_stack state") auto

  show ?thesis
  proof (cases frame)
    case (PreVisit u)
    show ?thesis
    proof (cases "u |\<in>| dfs_visited state")
      case True
      (* Case 1: u already visited, just pop the stack *)
      have step_result: "dfs_step graph state = state \<lparr> dfs_stack := rest \<rparr>"
        using stack_split PreVisit True by simp
      (* Stack gets smaller, so only removes pairs, preserving the property *)
      show ?thesis
        unfolding step_result dfs_previsit_ordered.simps dfs_state.simps
        using previsit_ordered stack_split PreVisit
        by (auto simp: member_rec)
    next
      case u_not_visited: False
      (* Case 2: u not visited, expand it - this is the interesting case *)
      define neighbors where "neighbors = the (fmlookup graph u)"

      have step_def: "dfs_step graph state =
            state \<lparr> dfs_visited := finsert u (dfs_visited state),
                   dfs_stack := map PreVisit neighbors @ [PostVisit u] @ rest \<rparr>"
        using dfs_step_previsit_expand valid stack_split neighbors_def PreVisit u_not_visited
        by blast

      have new_stack: "dfs_stack (dfs_step graph state) =
                       map PreVisit neighbors @ [PostVisit u] @ rest"
        using step_def by simp

      (* Need to show: for all pairs (PreVisit x, PostVisit y) on new stack
         with PreVisit x before PostVisit y, we have y reaches x *)
      show ?thesis
      proof (unfold dfs_previsit_ordered.simps, intro allI impI)
        fix x y
        assume pair_assumption: "List.member (dfs_stack (dfs_step graph state)) (PreVisit x) \<and>
                                 List.member (dfs_stack (dfs_step graph state)) (PostVisit y) \<and>
                                 index_of (PreVisit x) (dfs_stack (dfs_step graph state)) <
                                 index_of (PostVisit y) (dfs_stack (dfs_step graph state))"

        have px_in_new: "List.member (dfs_stack (dfs_step graph state)) (PreVisit x)"
          using pair_assumption by simp
        have py_in_new: "List.member (dfs_stack (dfs_step graph state)) (PostVisit y)"
          using pair_assumption by simp
        have idx_less: "index_of (PreVisit x) (dfs_stack (dfs_step graph state)) <
                        index_of (PostVisit y) (dfs_stack (dfs_step graph state))"
          using pair_assumption by simp

        (* PreVisit x is either in the new map PreVisit neighbors, or was in rest *)
        have "List.member (map PreVisit neighbors) (PreVisit x) \<or> List.member rest (PreVisit x)"
          using px_in_new new_stack
          by (metis append_Cons append_self_conv2 dfs_frame.distinct(1)
              list_membership_lemma member_rec(1)) 

        (* PostVisit y is either the new PostVisit u, or was in rest *)
        have py_cases: "PostVisit y = PostVisit u \<or> List.member rest (PostVisit y)"
        proof -
          have "List.member ([PostVisit u] @ rest) (PostVisit y)"
            using py_in_new new_stack map_PreVisit_no_PostVisit
            by (metis append_Cons list_membership_lemma)
          then show ?thesis
            by (auto simp: member_rec)
        qed

        show "reachable graph y x"
        proof (cases "PostVisit y = PostVisit u")
          (* First case: PostVisit y is the new PostVisit u *)
          case True
          then have "y = u" by simp

          (* Now we need to show u reaches x *)
          (* PreVisit x must be one of the new neighbors (since it comes before PostVisit u) *)
          have "List.member (map PreVisit neighbors) (PreVisit x)"
          proof (rule ccontr)
            (* Assume PreVisit x is *not* one of the new neighbors *)
            assume "\<not> List.member (map PreVisit neighbors) (PreVisit x)"
            then have "List.member rest (PreVisit x)"
              using \<open>List.member (map PreVisit neighbors) (PreVisit x) \<or> List.member rest (PreVisit x)\<close>
              by simp

            (* But then PreVisit x comes after PostVisit u in the new stack *)
            have "index_of (PostVisit u) (map PreVisit neighbors @ [PostVisit u] @ rest) =
                  length (map PreVisit neighbors)"
              by (induction neighbors) auto

            moreover have "index_of (PreVisit x) (map PreVisit neighbors @ [PostVisit u] @ rest) \<ge>
                          length (map PreVisit neighbors) + 1"
            proof -
              have "index_of (PreVisit x) (map PreVisit neighbors @ [PostVisit u] @ rest) =
                    length (map PreVisit neighbors) + 1 + index_of (PreVisit x) rest"
                using \<open>\<not> List.member (map PreVisit neighbors) (PreVisit x)\<close>
                by (induction neighbors) (auto simp: member_rec)
              then show ?thesis by simp
            qed

            ultimately have "index_of (PreVisit x) (dfs_stack (dfs_step graph state)) >
                            index_of (PostVisit y) (dfs_stack (dfs_step graph state))"
              using new_stack \<open>y = u\<close> by auto

            then show False using idx_less by simp
          qed

          (* So x is in neighbors, meaning u has edge to x *)
          then have "List.member neighbors x"
            by (induction neighbors) (auto simp: member_rec)

          (* u is a valid vertex *)
          have "has_vertex graph u"
            using valid stack_split PreVisit by (auto simp: member_rec)

          (* So there's an edge u -> x *)
          then have "has_edge graph u x"
            using \<open>List.member neighbors x\<close> neighbors_def has_edge_member_conv
            by blast 

          (* u reaches u (reflexive) *)
          have "reachable graph u u"
            using \<open>has_vertex graph u\<close> reachable.reachable_refl by simp

          (* Therefore u reaches x (one edge) *)
          then show ?thesis
            using \<open>has_edge graph u x\<close> \<open>y = u\<close> reachable.reachable_step by blast

        next
          case False
          (* Second case: PostVisit y was already in rest *)
          then have py_in_rest: "List.member rest (PostVisit y)"
            using py_cases by simp

          (* Case split on whether PreVisit x is in neighbors or rest *)
          show "reachable graph y x"
          proof (cases "List.member (map PreVisit neighbors) (PreVisit x)")
            case True
            (* x is a neighbor of u *)
            then have "List.member neighbors x"
              by (induction neighbors) (auto simp: member_rec)

            have "has_vertex graph u"
              using valid stack_split PreVisit by (auto simp: member_rec)

            then have "has_edge graph u x"
              using \<open>List.member neighbors x\<close> neighbors_def has_edge_member_conv by auto

            (* By old previsit_ordered, since PreVisit u was before PostVisit y, y reaches u *)
            have "reachable graph y u"
              using previsit_ordered stack_split PreVisit py_in_rest by (auto simp: member_rec)

            (* u reaches x (one edge) *)
            have "reachable graph u u"
              using \<open>has_vertex graph u\<close> reachable.reachable_refl by simp
            then have "reachable graph u x"
              using \<open>has_edge graph u x\<close> reachable.reachable_step by blast

            (* By transitivity, y reaches x *)
            then show ?thesis
              using \<open>reachable graph y u\<close> reachable_trans by blast

          next
            case px_not_in_neighbors: False
            (* PreVisit x is not in neighbors, so it must be in rest *)
            then have px_in_rest: "List.member rest (PreVisit x)"
              using \<open>List.member (map PreVisit neighbors) (PreVisit x) \<or> List.member rest (PreVisit x)\<close>
              by simp

            (* Both were in the old stack, so use old property *)
            have px_in_old: "List.member (dfs_stack state) (PreVisit x)"
              using px_in_rest stack_split by (auto simp: member_rec)
            have py_in_old: "List.member (dfs_stack state) (PostVisit y)"
              using py_in_rest stack_split by (auto simp: member_rec)

            (* Need to show that PreVisit x comes before PostVisit y in the old stack *)
            have idx_old: "index_of (PreVisit x) (dfs_stack state) < index_of (PostVisit y) (dfs_stack state)"
            proof -
              (* PostVisit y is not in the prefix *)
              have py_not_in_prefix: "\<not> List.member (map PreVisit neighbors @ [PostVisit u]) (PostVisit y)"
                using map_PreVisit_no_PostVisit
                by (metis False list.simps(8) list_membership_lemma
                    member_rec(1))
                
              (* PreVisit x is not in the prefix (from px_not_in_neighbors case) *)
              have px_not_in_prefix: "\<not> List.member (map PreVisit neighbors @ [PostVisit u]) (PreVisit x)"
                using px_not_in_neighbors
                by (meson dfs_frame.simps(4) list_membership_lemma
                    member_rec(1,2))

              (* Both are in rest and not in the prefix, so use index_of_append_shift *)
              have "index_of (PreVisit x) (map PreVisit neighbors @ [PostVisit u] @ rest) =
                    length (map PreVisit neighbors @ [PostVisit u]) + index_of (PreVisit x) rest"
                using px_in_rest px_not_in_prefix index_of_append_shift
                by fastforce 
              moreover have "index_of (PostVisit y) (map PreVisit neighbors @ [PostVisit u] @ rest) =
                             length (map PreVisit neighbors @ [PostVisit u]) + index_of (PostVisit y) rest"
                using py_in_rest py_not_in_prefix index_of_append_shift by fastforce
              ultimately have "index_of (PreVisit x) rest < index_of (PostVisit y) rest"
                using idx_less new_stack by simp

              (* In the old stack (PreVisit u # rest), use index_of_cons_shift *)
              then show ?thesis
                using stack_split PreVisit px_in_rest py_in_rest index_of_cons_shift
                by simp
            qed

            show ?thesis
              using previsit_ordered px_in_old py_in_old idx_old
              by auto
          qed
        qed
      qed
    qed
  next
    case (PostVisit v)
    (* Case 3: PostVisit removes v from stack *)
    have step_result: "dfs_step graph state = state \<lparr> dfs_stack := rest,
                                                        dfs_finish_order := v # dfs_finish_order state \<rparr>"
      using stack_split PostVisit by simp
    (* Stack gets smaller, so only removes pairs, preserving the property *)
    show ?thesis
    proof (unfold dfs_previsit_ordered.simps, intro allI impI)
      fix x y
      assume pair_in_new: "List.member (dfs_stack (dfs_step graph state)) (PreVisit x) \<and>
                           List.member (dfs_stack (dfs_step graph state)) (PostVisit y) \<and>
                           index_of (PreVisit x) (dfs_stack (dfs_step graph state)) <
                           index_of (PostVisit y) (dfs_stack (dfs_step graph state))"

      have "dfs_stack (dfs_step graph state) = rest"
        using step_result by simp

      then have "List.member rest (PreVisit x)" and "List.member rest (PostVisit y)"
                and "index_of (PreVisit x) rest < index_of (PostVisit y) rest"
        using pair_in_new by auto

      moreover have "List.member (dfs_stack state) (PreVisit x)"
        using \<open>List.member rest (PreVisit x)\<close> stack_split by (auto simp: member_rec)
      moreover have "List.member (dfs_stack state) (PostVisit y)"
        using \<open>List.member rest (PostVisit y)\<close> stack_split by (auto simp: member_rec)
      moreover have "index_of (PreVisit x) (dfs_stack state) < index_of (PostVisit y) (dfs_stack state)"
        using \<open>index_of (PreVisit x) rest < index_of (PostVisit y) rest\<close> stack_split
        using PostVisit pair_in_new valid by auto

      ultimately show "reachable graph y x"
        using previsit_ordered by auto
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
proof -
  obtain frame rest where stack_split: "dfs_stack state = frame # rest"
    using non_empty by (cases "dfs_stack state") auto

  show ?thesis
  proof (cases frame)
    case (PreVisit u)
    show ?thesis
    proof (cases "u |\<in>| dfs_visited state")
      case True
      (* Case 1: u already visited, just pop the stack *)
      have step_result: "dfs_step graph state = state \<lparr> dfs_stack := rest \<rparr>"
        using stack_split PreVisit True by simp
      (* Stack gets smaller, so only removes pairs, preserving the property *)
      show ?thesis
        unfolding step_result dfs_postvisit_ordered.simps dfs_state.simps
        using postvisit_ordered stack_split PreVisit
        by (auto simp: member_rec)
    next
      case u_not_visited: False
      (* Case 2: u not visited, expand it - this is the interesting case *)
      define neighbors where "neighbors = the (fmlookup graph u)"

      have step_def: "dfs_step graph state =
            state \<lparr> dfs_visited := finsert u (dfs_visited state),
                   dfs_stack := map PreVisit neighbors @ [PostVisit u] @ rest \<rparr>"
        using PreVisit dfs_step_previsit_expand neighbors_def stack_split valid
        using u_not_visited by blast 

      have new_stack: "dfs_stack (dfs_step graph state) =
                       map PreVisit neighbors @ [PostVisit u] @ rest"
        using step_def by simp

      (* Need to show: for all pairs (PostVisit x, PostVisit y) on new stack
         with PostVisit x before PostVisit y, we have y reaches x *)
      show ?thesis
      proof (unfold dfs_postvisit_ordered.simps, intro allI impI)
        fix x y
        assume pair_assumption: "List.member (dfs_stack (dfs_step graph state)) (PostVisit x) \<and>
                                 List.member (dfs_stack (dfs_step graph state)) (PostVisit y) \<and>
                                 index_of (PostVisit x) (dfs_stack (dfs_step graph state)) <
                                 index_of (PostVisit y) (dfs_stack (dfs_step graph state))"

        have px_in_new: "List.member (dfs_stack (dfs_step graph state)) (PostVisit x)"
          using pair_assumption by simp
        have py_in_new: "List.member (dfs_stack (dfs_step graph state)) (PostVisit y)"
          using pair_assumption by simp
        have idx_less: "index_of (PostVisit x) (dfs_stack (dfs_step graph state)) <
                        index_of (PostVisit y) (dfs_stack (dfs_step graph state))"
          using pair_assumption by simp

        (* PostVisit frames can only be PostVisit u or in rest (not in map PreVisit neighbors) *)
        have px_cases: "PostVisit x = PostVisit u \<or> List.member rest (PostVisit x)"
          using px_in_new new_stack map_PreVisit_no_PostVisit
          by (metis list_membership_lemma member_rec(1,2))
          
        have py_cases: "PostVisit y = PostVisit u \<or> List.member rest (PostVisit y)"
          using py_in_new new_stack map_PreVisit_no_PostVisit
          by (metis list_membership_lemma member_rec(1,2))

        show "reachable graph y x"
        proof (cases "PostVisit x = PostVisit u")
          case True
          then have "x = u" by simp
          (* PostVisit u is at index length neighbors in new stack *)
          have "index_of (PostVisit u) (map PreVisit neighbors @ [PostVisit u] @ rest) =
                length (map PreVisit neighbors)"
            by (induction neighbors) auto
          (* PostVisit y must come after, so it's in rest *)
          then have "PostVisit y \<noteq> PostVisit u"
            using idx_less new_stack True by auto
          then have py_in_rest: "List.member rest (PostVisit y)"
            using py_cases by simp

          (* By old previsit_ordered: PreVisit u before PostVisit y implies y reaches u *)
          have "reachable graph y u"
            using previsit_ordered stack_split PreVisit py_in_rest
            by (auto simp: member_rec)
          then show ?thesis
            using \<open>x = u\<close> by simp
        next
          case False
          (* PostVisit x is in rest *)
          then have px_in_rest: "List.member rest (PostVisit x)"
            using px_cases by simp

          show ?thesis
          proof (cases "PostVisit y = PostVisit u")
            case True
            (* This case is impossible: PostVisit x comes before PostVisit u,
               but PostVisit x is in rest which comes after PostVisit u *)
            have "index_of (PostVisit u) (map PreVisit neighbors @ [PostVisit u] @ rest) =
                  length (map PreVisit neighbors)"
              by (induction neighbors) auto
            then have False
              by (metis True index_of_append_shift less_add_Suc1
                  list_membership_lemma map_PreVisit_no_PostVisit new_stack not_less_eq
                  pair_assumption)
            thus ?thesis by simp
          next
            case False
            (* Both are in rest, use old postvisit_ordered *)
            then have py_in_rest: "List.member rest (PostVisit y)"
              using py_cases by simp

            have px_in_old: "List.member (dfs_stack state) (PostVisit x)"
              using px_in_rest stack_split by (auto simp: member_rec)
            have py_in_old: "List.member (dfs_stack state) (PostVisit y)"
              using py_in_rest stack_split by (auto simp: member_rec)

            (* Both are in rest, so their ordering is preserved *)
            have "index_of (PostVisit x) (dfs_stack state) < index_of (PostVisit y) (dfs_stack state)"
            proof -
              (* PostVisit frames are not in the prefix *)
              have px_not_in_prefix: "\<not> List.member (map PreVisit neighbors @ [PostVisit u]) (PostVisit x)"
                using map_PreVisit_no_PostVisit
                by (metis dfs_post_visit_visited.elims(1) dfs_state_valid.elims(2)
                    list_membership_lemma member_rec(1,2) px_in_old u_not_visited
                    valid)
              have py_not_in_prefix: "\<not> List.member (map PreVisit neighbors @ [PostVisit u]) (PostVisit y)"
                using map_PreVisit_no_PostVisit
                by (metis False list.simps(8) list_membership_lemma
                    member_rec(1))
                
              (* Apply index_of_append_shift *)
              have "index_of (PostVisit x) (map PreVisit neighbors @ [PostVisit u] @ rest) =
                    length (map PreVisit neighbors @ [PostVisit u]) + index_of (PostVisit x) rest"
                using px_in_rest px_not_in_prefix index_of_append_shift
                by fastforce 
              moreover have "index_of (PostVisit y) (map PreVisit neighbors @ [PostVisit u] @ rest) =
                             length (map PreVisit neighbors @ [PostVisit u]) + index_of (PostVisit y) rest"
                using py_in_rest py_not_in_prefix index_of_append_shift by fastforce
              ultimately have "index_of (PostVisit x) rest < index_of (PostVisit y) rest"
                using idx_less new_stack by simp

              (* In the old stack (PreVisit u # rest), use index_of_cons_shift *)
              then show ?thesis
                using stack_split PreVisit px_in_rest py_in_rest index_of_cons_shift
                by simp
            qed

            then show ?thesis
              using postvisit_ordered px_in_old py_in_old
              by auto
          qed
        qed
      qed
    qed
  next
    case (PostVisit v)
    (* Case 3: PostVisit removes v from stack *)
    have step_result: "dfs_step graph state = state \<lparr> dfs_stack := rest,
                                                        dfs_finish_order := v # dfs_finish_order state \<rparr>"
      using stack_split PostVisit by simp
    (* Stack gets smaller, so only removes pairs, preserving the property *)
    show ?thesis
    proof (unfold dfs_postvisit_ordered.simps, intro allI impI)
      fix x y
      assume pair_in_new: "List.member (dfs_stack (dfs_step graph state)) (PostVisit x) \<and>
                           List.member (dfs_stack (dfs_step graph state)) (PostVisit y) \<and>
                           index_of (PostVisit x) (dfs_stack (dfs_step graph state)) <
                           index_of (PostVisit y) (dfs_stack (dfs_step graph state))"

      have "dfs_stack (dfs_step graph state) = rest"
        using step_result by simp

      then have "List.member rest (PostVisit x)" and "List.member rest (PostVisit y)"
                and "index_of (PostVisit x) rest < index_of (PostVisit y) rest"
        using pair_in_new by auto

      moreover have "List.member (dfs_stack state) (PostVisit x)"
        using \<open>List.member rest (PostVisit x)\<close> stack_split by (auto simp: member_rec)
      moreover have "List.member (dfs_stack state) (PostVisit y)"
        using \<open>List.member rest (PostVisit y)\<close> stack_split by (auto simp: member_rec)
      moreover have "index_of (PostVisit x) (dfs_stack state) < index_of (PostVisit y) (dfs_stack state)"
        using \<open>index_of (PostVisit x) rest < index_of (PostVisit y) rest\<close> stack_split
        by (metis Suc_less_eq \<open>dfs_stack (dfs_step graph state) = rest\<close>
            dfs_post_visit_distinct.simps(3) dfs_state_valid.elims(2)
            index_of.simps(2) pair_in_new valid)

      ultimately show "reachable graph y x"
        using postvisit_ordered by auto
    qed
  qed
qed

(*-----------------------------------------------------------------------------*)
(* DFS step expands the WillFinishBeforeMe sets *)
(*-----------------------------------------------------------------------------*)

(* Lemma: dfs_step expands will_finish_before_me
   Case 1: visited PreVisit *)
lemma dfs_step_expands_will_finish_visited_previsit:
  assumes valid: "dfs_state_valid graph state"
    and stack_structure: "dfs_stack state = PreVisit v # rest"
    and v_visited: "v |\<in>| dfs_visited state"
    and post_in_old: "i < length (dfs_stack state) \<and> dfs_stack state ! i = PostVisit x"
    and post_in_new: "j < length (dfs_stack (dfs_step graph state)) \<and>
                      dfs_stack (dfs_step graph state) ! j = PostVisit x"
  shows "will_finish_before_me graph state i \<subseteq>
         will_finish_before_me graph (dfs_step graph state) j"
proof -
  have step_def: "dfs_step graph state = state \<lparr> dfs_stack := rest \<rparr>"
    using stack_structure v_visited by simp

  have distinct: "dfs_post_visit_distinct (dfs_stack state)"
    using valid by simp

  (* PostVisit x is in rest (not the head), so its index just shifts down by 1 *)
  have "PostVisit x \<noteq> PreVisit v" by simp
  then have x_in_rest: "List.member rest (PostVisit x)"
    using post_in_old stack_structure
    by (metis in_set_member nth_mem set_ConsD)

  (* The index in the new stack is i - 1 *)
  have "i > 0"
    using post_in_old stack_structure
    by (simp add: nth_non_equal_first_eq)
  then have old_index: "rest ! (i - 1) = PostVisit x"
    using post_in_old stack_structure by (metis Suc_diff_1 nth_Cons_Suc)

  have new_index: "j = i - 1"
  proof -
    have "dfs_post_visit_distinct rest"
      using distinct stack_structure dfs_post_visit_distinct_tail by auto
    moreover have "rest ! j = PostVisit x"
      using post_in_new step_def by simp
    moreover have "j < length rest"
      using post_in_new step_def by auto
    ultimately have "index_of (PostVisit x) rest = j"
      using index_of_postvisit_conv by blast
    moreover have "i - 1 < length rest"
      using post_in_old stack_structure \<open>i > 0\<close> by auto
    ultimately show "j = i - 1"
      using old_index \<open>dfs_post_visit_distinct rest\<close> index_of_postvisit_conv
      by blast
  qed

  define OldSet1 where "OldSet1 = set (dfs_finish_order state)"
  define OldSet2 where "OldSet2 =
    {z. \<exists>k. k < i \<and> List.member (dfs_stack state) (PostVisit z) \<and>
     index_of (PostVisit z) (dfs_stack state) = k}"
  define OldSet3 where "OldSet3 =
    {z. \<exists>k w. k < i \<and> List.member (dfs_stack state) (PreVisit w) \<and>
     index_of (PreVisit w) (dfs_stack state) = k \<and>
     unvisited_path graph (dfs_visited state) w z}"

  define NewSet1 where "NewSet1 = set (dfs_finish_order (dfs_step graph state))"
  define NewSet2 where "NewSet2 =
    {z. \<exists>k. k < j \<and> List.member (dfs_stack (dfs_step graph state)) (PostVisit z) \<and>
     index_of (PostVisit z) (dfs_stack (dfs_step graph state)) = k}"
  define NewSet3 where "NewSet3 =
    {z. \<exists>k w. k < j \<and> List.member (dfs_stack (dfs_step graph state)) (PreVisit w) \<and>
     index_of (PreVisit w) (dfs_stack (dfs_step graph state)) = k \<and>
     unvisited_path graph (dfs_visited (dfs_step graph state)) w z}"

  have "OldSet1 = NewSet1"
    using step_def OldSet1_def NewSet1_def by simp

  moreover have "OldSet2 \<subseteq> NewSet2"
  proof (rule subsetI)
    fix z
    assume "z \<in> OldSet2"
    then obtain k where
        "k < i"
        and "List.member (dfs_stack state) (PostVisit z)"
        and "index_of (PostVisit z) (dfs_stack state) = k"
      using OldSet2_def by blast

    (* PostVisit z cannot be PreVisit v, so must be in rest *)
    have "List.member rest (PostVisit z)"
      using \<open>List.member (dfs_stack state) (PostVisit z)\<close> stack_structure
      by (simp add: member_rec(1))
    moreover have "k > 0"
      using \<open>index_of (PostVisit z) (dfs_stack state) = k\<close> stack_structure
      by simp
    then have "index_of (PostVisit z) rest = k - 1"
      using \<open>index_of (PostVisit z) (dfs_stack state) = k\<close> stack_structure
      by force
    moreover have "k - 1 < j"
      using \<open>k < i\<close> \<open>k > 0\<close> new_index by simp
    ultimately show "z \<in> NewSet2"
      using NewSet2_def step_def by auto
  qed

  moreover have "OldSet3 \<subseteq> NewSet3"
  proof
    fix z
    assume "z \<in> OldSet3"
    then obtain k w where "k < i" and "List.member (dfs_stack state) (PreVisit w)"
                      and "index_of (PreVisit w) (dfs_stack state) = k"
                      and "unvisited_path graph (dfs_visited state) w z"
      using OldSet3_def by blast

    (* k cannot be 0: if k = 0 then w = v, but v is visited while unvisited_path requires w unvisited *)
    have "k \<noteq> 0"
    proof (rule notI)
      assume "k = 0"
      then have "PreVisit w = PreVisit v"
        using \<open>index_of (PreVisit w) (dfs_stack state) = k\<close> stack_structure
        by (metis index_of.simps(2) less_numeral_extra(3) zero_less_Suc)
      then have "w = v" by simp
      moreover have "w |\<notin>| dfs_visited state"
        using \<open>unvisited_path graph (dfs_visited state) w z\<close>
        by (metis unvisited_path.cases)
      ultimately show False
        using v_visited by simp
    qed
    then have "k > 0" by simp

    have "List.member rest (PreVisit w)"
      using \<open>List.member (dfs_stack state) (PreVisit w)\<close> stack_structure
      by (metis \<open>unvisited_path graph (dfs_visited state) w z\<close>
          dfs_frame.inject(1) member_rec(1) unvisited_path.cases v_visited)
    moreover have "index_of (PreVisit w) rest = k - 1"
      using \<open>index_of (PreVisit w) (dfs_stack state) = k\<close> \<open>k > 0\<close> stack_structure
      by force
    moreover have "k - 1 < j"
      using \<open>k < i\<close> \<open>k > 0\<close> new_index by simp
    moreover have "unvisited_path graph (dfs_visited (dfs_step graph state)) w z"
      using \<open>unvisited_path graph (dfs_visited state) w z\<close> step_def by simp
    ultimately show "z \<in> NewSet3"
      using NewSet3_def step_def by auto
  qed

  ultimately have "OldSet1 \<union> OldSet2 \<union> OldSet3 \<subseteq> NewSet1 \<union> NewSet2 \<union> NewSet3"
    by blast

  moreover have "will_finish_before_me graph state i = OldSet1 \<union> OldSet2 \<union> OldSet3"
    using OldSet1_def OldSet2_def OldSet3_def post_in_old by auto

  moreover have "will_finish_before_me graph (dfs_step graph state) j
        = NewSet1 \<union> NewSet2 \<union> NewSet3"
    using NewSet1_def NewSet2_def NewSet3_def post_in_new by auto

  ultimately show ?thesis
    by simp
qed

(* Lemma: dfs_step expands will_finish_before_me 
   Case 2: unvisited PreVisit *)
lemma dfs_step_expands_will_finish_unvisited_previsit:
  assumes valid: "dfs_state_valid graph state"
    and stack_structure: "dfs_stack state = PreVisit v # rest"
    and v_not_visited: "v |\<notin>| dfs_visited state"
    and post_in_old: "i < length (dfs_stack state) \<and> dfs_stack state ! i = PostVisit x"
    and post_in_new: "j < length (dfs_stack (dfs_step graph state)) \<and>
                      dfs_stack (dfs_step graph state) ! j = PostVisit x"
  shows "will_finish_before_me graph state i \<subseteq>
         will_finish_before_me graph (dfs_step graph state) j"
proof -
  define neighbors where "neighbors = the (fmlookup graph v)"
  define prefix where "prefix = map PreVisit neighbors @ [PostVisit v]"

  have step_def: "dfs_step graph state =
        state \<lparr> dfs_visited := finsert v (dfs_visited state),
               dfs_stack := prefix @ rest \<rparr>"
    using valid stack_structure v_not_visited neighbors_def prefix_def
    using dfs_step_previsit_expand append_assoc by metis

  have distinct: "dfs_post_visit_distinct (dfs_stack state)"
    using valid by simp

  (* PostVisit x is still in the stack, but its position has shifted *)
  have x_in_old_rest: "List.member rest (PostVisit x)"
    using post_in_old stack_structure
    by (metis dfs_frame.distinct(1) in_set_member nth_mem
        set_ConsD)

  have "i \<noteq> 0"
    using post_in_old stack_structure by (simp add: nth_non_equal_first_eq)

  have index_x_in_stack: "index_of (PostVisit x) (dfs_stack state) = i"
    using distinct post_in_old index_of_postvisit_conv
    by blast
  then have index_x_in_rest: "index_of (PostVisit x) rest = i - 1"
    using stack_structure index_of_cons_shift \<open>i \<noteq> 0\<close>
    by force

  have index_x_in_new: "index_of (PostVisit x) (dfs_stack (dfs_step graph state)) = j"
  proof -
    have "dfs_state_valid graph (dfs_step graph state)"
      using valid stack_structure dfs_step_preserves_validity
      by (metis list.distinct(1))
    then have "dfs_post_visit_distinct (dfs_stack (dfs_step graph state))"
      by simp
    thus ?thesis
      using index_of_postvisit_conv post_in_new
      by metis
  qed

  (* Show the subset relation using the structure from case 1 *)
  define OldSet1 where "OldSet1 = set (dfs_finish_order state)"
  define OldSet2 where "OldSet2 =
    {z. \<exists>k. k < i \<and> List.member (dfs_stack state) (PostVisit z) \<and>
     index_of (PostVisit z) (dfs_stack state) = k}"
  define OldSet3 where "OldSet3 =
    {z. \<exists>k w. k < i \<and> List.member (dfs_stack state) (PreVisit w) \<and>
     index_of (PreVisit w) (dfs_stack state) = k \<and>
     unvisited_path graph (dfs_visited state) w z}"

  define NewSet1 where "NewSet1 = set (dfs_finish_order (dfs_step graph state))"
  define NewSet2 where "NewSet2 =
    {z. \<exists>k. k < j \<and> List.member (dfs_stack (dfs_step graph state)) (PostVisit z) \<and>
     index_of (PostVisit z) (dfs_stack (dfs_step graph state)) = k}"
  define NewSet3 where "NewSet3 =
    {z. \<exists>k w. k < j \<and> List.member (dfs_stack (dfs_step graph state)) (PreVisit w) \<and>
     index_of (PreVisit w) (dfs_stack (dfs_step graph state)) = k \<and>
     unvisited_path graph (dfs_visited (dfs_step graph state)) w z}"

  (* Finish order is unchanged *)
  have "OldSet1 = NewSet1"
    using OldSet1_def NewSet1_def step_def by simp

  (* OldSet2 subset NewSet2 *)
  moreover have "OldSet2 \<subseteq> NewSet2"
  proof
    fix z
    assume "z \<in> OldSet2"
    then obtain k where
        "k < i"
        and "List.member (dfs_stack state) (PostVisit z)"
        and "index_of (PostVisit z) (dfs_stack state) = k"
      using OldSet2_def by blast

    have "k \<noteq> 0"
      using \<open>index_of (PostVisit z) (dfs_stack state) = k\<close> stack_structure
      by force

    have z_in_rest: "List.member rest (PostVisit z)"
      using \<open>List.member (dfs_stack state) (PostVisit z)\<close> stack_structure
      by (metis dfs_frame.distinct(1) member_rec(1))

    have index_z_in_rest: "index_of (PostVisit z) rest = k - 1"
      using \<open>index_of (PostVisit z) (dfs_stack state) = k\<close> \<open>k \<noteq> 0\<close>
        stack_structure by auto

    (* Apply index_of_append_preserves_order:
       We have index_of (PostVisit z) rest < index_of (PostVisit x) rest (by k < i),
       and neither PostVisit is in prefix (which only contains PreVisits and PostVisit v),
       so the ordering is preserved in prefix @ rest *)
    have index_less_in_rest:
      "index_of (PostVisit z) (prefix @ rest) < index_of (PostVisit x) (prefix @ rest)"
      by (metis \<open>List.member (dfs_stack state) (PostVisit z)\<close>
                \<open>index_of (PostVisit z) (dfs_stack state) = k\<close> \<open>k < i\<close>
                dfs_frame.simps(4) dfs_post_visit_visited.elims(2)
                dfs_state_valid.simps in_set_member index_of.simps(2)
                index_of_append_preserves_order index_x_in_stack
                list_membership_lemma map_PreVisit_no_PostVisit member_rec(1,2)
                not_less_eq nth_mem post_in_old prefix_def stack_structure v_not_visited
                valid)

    (* This means PostVisit z appears before PostVisit x in new stack *)
    then have "index_of (PostVisit z) (dfs_stack (dfs_step graph state)) < j"
      using step_def index_less_in_rest
      by (metis dfs_state_valid.simps dfs_step_preserves_validity
          index_of_postvisit_conv list.distinct(1) post_in_new select_convs(3)
          stack_structure surjective update_convs(3) valid) 

    moreover have "List.member (dfs_stack (dfs_step graph state)) (PostVisit z)"
    proof -
      have "List.member rest (PostVisit z)"
        using \<open>List.member (dfs_stack state) (PostVisit z)\<close> stack_structure
        by (metis dfs_frame.distinct(1) member_rec(1))
      then have "List.member (prefix @ rest) (PostVisit z)"
        by (induction prefix) (auto simp: member_rec)
      then show ?thesis
        using step_def by simp
    qed

    (* Therefore z is in NewSet2 *)
    ultimately show "z \<in> NewSet2"
      using NewSet2_def by blast
  qed

  (* OldSet3: This is the tricky part *)
  moreover have "OldSet3 \<subseteq> NewSet1 \<union> NewSet2 \<union> NewSet3"
  proof
    fix z
    assume "z \<in> OldSet3"
    then obtain k w where
        k_less: "k < i"
        and w_member: "List.member (dfs_stack state) (PreVisit w)"
        and w_index: "index_of (PreVisit w) (dfs_stack state) = k"
        and path_w_z: "unvisited_path graph (dfs_visited state) w z"
      using OldSet3_def by blast

    show "z \<in> NewSet1 \<union> NewSet2 \<union> NewSet3"
    proof (cases "z = v")
      case True
      (* If z = v, we prove that v is in NewSet2 *)
      then have "z \<in> NewSet2"
      proof -
        (* PostVisit v is in prefix *)
        have postvisit_v_in_prefix: "List.member prefix (PostVisit v)"
          using prefix_def by (meson in_set_conv_decomp in_set_member) 

        (* Therefore PostVisit v is in the new stack *)
        have "List.member (dfs_stack (dfs_step graph state)) (PostVisit v)"
          using postvisit_v_in_prefix step_def
          by (metis append_Cons append_assoc in_set_conv_decomp in_set_member
              select_convs(3) surjective update_convs(3))
          
        (* PostVisit v appears before PostVisit x in the new stack *)
        moreover have "index_of (PostVisit v) (dfs_stack (dfs_step graph state)) < j"
        proof -
          (* PostVisit v is in prefix, PostVisit x is in rest *)
          have "PostVisit v \<in> set prefix"
            using postvisit_v_in_prefix by (simp add: in_set_member)
          moreover have "PostVisit x \<in> set rest"
            using x_in_old_rest by (simp add: in_set_member)
          moreover have "\<not> List.member prefix (PostVisit x)"
          proof -
            (* PostVisit x cannot be in map PreVisit neighbors *)
            have "\<not> List.member (map PreVisit neighbors) (PostVisit x)"
              using map_PreVisit_no_PostVisit by auto
            (* PostVisit x \<noteq> PostVisit v by distinctness *)
            moreover have "PostVisit x \<noteq> PostVisit v"
            proof -
              have "\<not> List.member rest (PostVisit v)"
                using distinct stack_structure
                by (metis dfs_post_visit_visited.elims(2) dfs_state_valid.simps
                    member_rec(1) v_not_visited valid) 
              thus ?thesis
                using x_in_old_rest by auto
            qed
            ultimately show ?thesis
              using prefix_def
              by (metis list_membership_lemma member_rec(1,2)) 
          qed
          then have "index_of (PostVisit v) (prefix @ rest) < index_of (PostVisit x) (prefix @ rest)"
            using postvisit_v_in_prefix x_in_old_rest index_of_prefix_before_rest
            by metis 
          thus ?thesis
            using step_def index_x_in_new by simp
        qed

        ultimately show "z \<in> NewSet2"
          using NewSet2_def True by simp
      qed
      then show ?thesis by simp
    next
      case False
      (* z \<noteq> v, so we consider the path from w to z *)
      then have z_neq_v: "z \<noteq> v" by simp

      (* Get an explicit path from w to z *)
      obtain pth where
        pth_valid: "valid_path graph pth"
        and pth_start: "path_start pth = w"
        and pth_end: "path_end pth = z"
        and pth_unvisited: "all_unvisited (dfs_visited state) pth"
        using path_w_z valid unvisited_path_implies_valid_path
        using dfs_state_valid.simps by blast 

      (* Case split: does the path from w to z contain v or not? *)
      show ?thesis
      proof (cases "List.member pth v")
        case False
        (* Path doesn't contain v, so it's still unvisited in the new state *)
        have "z \<in> NewSet3"
        proof -
          (* w \<noteq> v because v is not on the path from w to z *)
          have "w \<noteq> v"
            using False pth_start pth_valid
            by (metis member_rec(1) path_start.elims valid_path.simps(1))

          (* Therefore PreVisit w is still in the new stack *)
          have "List.member (dfs_stack (dfs_step graph state)) (PreVisit w)"
            using w_member stack_structure step_def \<open>w \<noteq> v\<close>
          proof -
            have "List.member rest (PreVisit w)"
              by (metis \<open>w \<noteq> v\<close> dfs_frame.inject(1) member_rec(1) stack_structure
                  w_member)
            moreover have "dfs_stack (dfs_step graph state) = prefix @ rest"
              using step_def by simp
            ultimately show ?thesis
              by (metis append_assoc in_set_conv_decomp in_set_member) 
          qed

          (* The path is still unvisited in the new state *)
          moreover have "all_unvisited (dfs_visited (dfs_step graph state)) pth"
            using pth_unvisited False step_def all_unvisited_preserved_without_v
            by auto

          (* Therefore unvisited_path still holds in new state *)
          moreover have "unvisited_path graph (dfs_visited (dfs_step graph state)) w z"
            using pth_valid pth_start pth_end calculation(2) valid
            using valid_path_implies_unvisited_path
            using dfs_state_valid.simps by blast 

          (* Find the index of PreVisit w in the new stack *)
          moreover have "\<exists>k'. k' < j \<and>
                              List.member (dfs_stack (dfs_step graph state)) (PreVisit w) \<and>
                              index_of (PreVisit w) (dfs_stack (dfs_step graph state)) = k'"
          proof -
            have "PreVisit w \<in> set rest"
              using w_member stack_structure \<open>w \<noteq> v\<close>
              by (simp add: member_def)
            then have "List.member rest (PreVisit w)"
              by (simp add: in_set_member)
            then have "List.member (prefix @ rest) (PreVisit w)"
              by (induction prefix) (auto simp: member_rec)
            then have w_in_new: "List.member (dfs_stack (dfs_step graph state)) (PreVisit w)"
              using step_def by simp

            (* PostVisit x is not in prefix *)
            have "\<not> List.member prefix (PostVisit x)"
              using prefix_def map_PreVisit_no_PostVisit
              by (metis dfs_post_visit_visited.elims(2) dfs_state_valid.simps
                  list.simps(8) list_membership_lemma member_rec(1) stack_structure
                  v_not_visited valid x_in_old_rest)

            (* PreVisit w appears before PostVisit x in the new stack *)
            have "index_of (PreVisit w) (prefix @ rest) < index_of (PostVisit x) (prefix @ rest)"
            proof (cases "List.member prefix (PreVisit w)")
              case True
              (* w is in prefix, so it appears before all of rest, including PostVisit x *)
              then show ?thesis
                using x_in_old_rest \<open>\<not> List.member prefix (PostVisit x)\<close>
                      index_of_prefix_before_rest by metis
            next
              case w_not_in_prefix: False
              (* w is not in prefix, but we do know it is in rest *)

              (* In the old stack, PreVisit w was at index k and PostVisit x at index i, with k < i *)
              have w_index_in_rest: "index_of (PreVisit w) rest = k - 1"
                using w_index stack_structure
                using \<open>w \<noteq> v\<close> by fastforce

              have x_index_in_rest: "index_of (PostVisit x) rest = i - 1"
                using index_x_in_rest by simp

              (* Since k < i, we have k - 1 < i - 1 *)
              have "k > 0"
                using k_less post_in_old stack_structure w_index
                by (simp add: \<open>w \<noteq> v\<close>)
              then have "index_of (PreVisit w) rest < index_of (PostVisit x) rest"
                using w_index_in_rest x_index_in_rest k_less by simp

              (* Use index_of_append_preserves_order *)
              then show ?thesis
                using False \<open>List.member rest (PreVisit w)\<close> x_in_old_rest
                      \<open>\<not> List.member prefix (PostVisit x)\<close>
                      index_of_append_preserves_order
                by (metis w_not_in_prefix)
            qed

            then have "index_of (PreVisit w) (dfs_stack (dfs_step graph state)) < j"
              using step_def index_x_in_new by simp

            then show ?thesis
              using w_in_new by blast
          qed

          ultimately show ?thesis
            using NewSet3_def by blast
        qed
        then show ?thesis by simp
      next
        case path_contains_v: True
        (* Path contains v, so we use path_through_v_has_next *)
        have "z \<in> NewSet3"
        proof -
          (* Get the continuation after v *)
          obtain nxt suffix where
            edge_v_nxt: "has_edge graph v nxt"
            and suffix_valid: "valid_path graph (nxt # suffix)"
            and suffix_end: "path_end (nxt # suffix) = z"
            and suffix_no_v: "\<not>List.member (nxt # suffix) v"
            and suffix_in_pth: "(\<forall>u. List.member (nxt # suffix) u \<longrightarrow> List.member pth u)"
            using pth_valid pth_end path_contains_v z_neq_v path_through_v_has_next by blast

          (* nxt is a neighbor of v, so PreVisit nxt is in the new stack *)
          have "List.member neighbors nxt"
            using edge_v_nxt neighbors_def valid
            by (metis has_edge.elims(2) option.case_eq_if)

          then have "List.member (map PreVisit neighbors) (PreVisit nxt)"
            by (induction neighbors) (auto simp: member_rec)

          then have nxt_in_prefix: "List.member prefix (PreVisit nxt)"
            by (simp add: member_def prefix_def)

          then have "List.member (dfs_stack (dfs_step graph state)) (PreVisit nxt)"
            using step_def by (simp add: member_def) 

          (* The suffix is unvisited in the new state *)
          moreover have "all_unvisited (dfs_visited (dfs_step graph state)) (nxt # suffix)"
          proof -
            (* All vertices in pth were unvisited in old state *)
            have "\<forall>u. List.member pth u \<longrightarrow> u |\<notin>| dfs_visited state"
              using pth_unvisited by simp
            (* suffix vertices are in pth *)
            have "\<forall>u. List.member (nxt # suffix) u \<longrightarrow> List.member pth u"
              using suffix_in_pth by simp
            (* Only v was added to visited set *)
            have "dfs_visited (dfs_step graph state) = finsert v (dfs_visited state)"
              using step_def by simp
            (* suffix doesn't contain v *)
            have "\<forall>u. List.member (nxt # suffix) u \<longrightarrow> u \<noteq> v"
              using suffix_no_v by auto
            (* Therefore suffix is still unvisited *)
            then show ?thesis
              using \<open>\<forall>u. List.member (nxt # suffix) u \<longrightarrow> List.member pth u\<close>
                    \<open>\<forall>u. List.member pth u \<longrightarrow> u |\<notin>| dfs_visited state\<close>
                    \<open>dfs_visited (dfs_step graph state) = finsert v (dfs_visited state)\<close>
              by (simp add: member_rec)
          qed

          (* Therefore unvisited_path holds in new state *)
          moreover have "unvisited_path graph (dfs_visited (dfs_step graph state)) nxt z"
            using suffix_valid suffix_end calculation(2) valid
            using valid_path_implies_unvisited_path
            by (metis dfs_state_valid.simps path_start.simps(2))
            
          (* PreVisit nxt appears before position j *)
          moreover have "\<exists>k'. k' < j \<and>
                              List.member (dfs_stack (dfs_step graph state)) (PreVisit nxt) \<and>
                              index_of (PreVisit nxt) (dfs_stack (dfs_step graph state)) = k'"
          proof -
            have "\<not> List.member prefix (PostVisit x)"
              using prefix_def map_PreVisit_no_PostVisit
              by (metis dfs_post_visit_distinct.simps(1)
                  dfs_post_visit_visited.elims(2) dfs_state_valid.simps
                  index_of.simps(1) index_of_postvisit_conv less_numeral_extra(3)
                  list.size(3) list_membership_lemma member_rec(1) stack_structure
                  v_not_visited valid x_in_old_rest)

            then have "index_of (PreVisit nxt) (prefix @ rest) < index_of (PostVisit x) (prefix @ rest)"
              using nxt_in_prefix x_in_old_rest index_of_prefix_before_rest
              by metis 

            then have "index_of (PreVisit nxt) (dfs_stack (dfs_step graph state)) < j"
              using step_def index_x_in_new by simp

            then show ?thesis
              using \<open>List.member (dfs_stack (dfs_step graph state)) (PreVisit nxt)\<close> by blast
          qed

          ultimately show ?thesis
            using NewSet3_def by blast
        qed
        then show ?thesis by simp
      qed
    qed
  qed

  ultimately have "OldSet1 \<union> OldSet2 \<union> OldSet3 \<subseteq> NewSet1 \<union> NewSet2 \<union> NewSet3"
    by blast

  moreover have "will_finish_before_me graph state i = OldSet1 \<union> OldSet2 \<union> OldSet3"
    using OldSet1_def OldSet2_def OldSet3_def post_in_old by auto

  moreover have "will_finish_before_me graph (dfs_step graph state) j
        = NewSet1 \<union> NewSet2 \<union> NewSet3"
    using NewSet2_def NewSet3_def post_in_new NewSet1_def by auto

  ultimately show ?thesis by simp
qed

(* Lemma: dfs_step expands will_finish_before_me
   Case 3: PostVisit *)
lemma dfs_step_expands_will_finish_postvisit:
  assumes valid: "dfs_state_valid graph state"
    and stack_structure: "dfs_stack state = PostVisit v # rest"
    and post_in_old: "i < length (dfs_stack state) \<and> dfs_stack state ! i = PostVisit x"
    and post_in_new: "j < length (dfs_stack (dfs_step graph state)) \<and>
                      dfs_stack (dfs_step graph state) ! j = PostVisit x"
  shows "will_finish_before_me graph state i \<subseteq>
         will_finish_before_me graph (dfs_step graph state) j"
proof -
  have step_def: "dfs_step graph state =
        state \<lparr> dfs_finish_order := v # (dfs_finish_order state),
               dfs_stack := rest \<rparr>"
    using stack_structure by simp

  have distinct: "dfs_post_visit_distinct (dfs_stack state)"
    using valid by simp

  (* PostVisit x must be in rest (not the head being popped) since it appears in new state *)
  (* By distinctness, PostVisit v appears only once in the old stack *)
  have "\<not>List.member rest (PostVisit v)"
    using distinct stack_structure by auto

  (* But PostVisit x IS in the new stack, which is rest *)
  have x_in_new: "List.member (dfs_stack (dfs_step graph state)) (PostVisit x)"
    using post_in_new by (metis in_set_member nth_mem)
  then have "List.member rest (PostVisit x)"
    using step_def by simp

  (* Therefore x \<noteq> v *)
  have "PostVisit x \<noteq> PostVisit v"
    using \<open>\<not>List.member rest (PostVisit v)\<close> \<open>List.member rest (PostVisit x)\<close> by auto
  then have "x \<noteq> v" by simp

  have x_in_rest: "List.member rest (PostVisit x)"
    using post_in_old stack_structure \<open>PostVisit x \<noteq> PostVisit v\<close>
    by (metis in_set_member nth_mem set_ConsD)

  (* The index in the new stack is i - 1 *)
  have "i > 0"
    using post_in_old stack_structure \<open>PostVisit x \<noteq> PostVisit v\<close>
    by force

  then have old_index: "rest ! (i - 1) = PostVisit x"
    using post_in_old stack_structure by (metis Suc_diff_1 nth_Cons_Suc)

  have new_index: "j = i - 1"
  proof -
    have "dfs_stack (dfs_step graph state) ! j = PostVisit x"
      using post_in_new by simp
    then have "rest ! j = PostVisit x"
      using step_def by simp

    have "rest ! (i - 1) = PostVisit x"
      using old_index by simp

    have "dfs_post_visit_distinct rest"
      using distinct stack_structure dfs_post_visit_distinct_tail by auto

    have "j < length rest" and "i - 1 < length rest"
      using post_in_new step_def \<open>i > 0\<close> post_in_old stack_structure by auto

    then show "j = i - 1"
      using \<open>rest ! j = PostVisit x\<close> \<open>rest ! (i - 1) = PostVisit x\<close>
            \<open>dfs_post_visit_distinct rest\<close>
            dfs_post_visit_distinct_unique_index
      by blast
  qed

  define OldSet1 where "OldSet1 = set (dfs_finish_order state)"
  define OldSet2 where "OldSet2 =
    {z. \<exists>k. k < i \<and> List.member (dfs_stack state) (PostVisit z) \<and>
     index_of (PostVisit z) (dfs_stack state) = k}"
  define OldSet3 where "OldSet3 =
    {z. \<exists>k w. k < i \<and> List.member (dfs_stack state) (PreVisit w) \<and>
     index_of (PreVisit w) (dfs_stack state) = k \<and>
     unvisited_path graph (dfs_visited state) w z}"

  define NewSet1 where "NewSet1 = set (dfs_finish_order (dfs_step graph state))"
  define NewSet2 where "NewSet2 =
    {z. \<exists>k. k < j \<and> List.member (dfs_stack (dfs_step graph state)) (PostVisit z) \<and>
     index_of (PostVisit z) (dfs_stack (dfs_step graph state)) = k}"
  define NewSet3 where "NewSet3 =
    {z. \<exists>k w. k < j \<and> List.member (dfs_stack (dfs_step graph state)) (PreVisit w) \<and>
     index_of (PreVisit w) (dfs_stack (dfs_step graph state)) = k \<and>
     unvisited_path graph (dfs_visited (dfs_step graph state)) w z}"

  (* Finish order grows: v is added *)
  have "OldSet1 \<subseteq> NewSet1"
    using OldSet1_def NewSet1_def step_def by auto

  (* OldSet2 is NOT necessarily a subset of NewSet2, but it IS a subset of NewSet1 \<union> NewSet2 *)
  moreover have "OldSet2 \<subseteq> NewSet1 \<union> NewSet2"
  proof (rule subsetI)
    fix z
    assume "z \<in> OldSet2"
    then obtain k where "k < i" and "List.member (dfs_stack state) (PostVisit z)"
                    and "index_of (PostVisit z) (dfs_stack state) = k"
      using OldSet2_def by blast

    (* PostVisit z is either PostVisit v (at the head) or in rest *)
    show "z \<in> NewSet1 \<union> NewSet2"
    proof (cases "k = 0")
      case True
      (* k = 0 means PostVisit z is at the head, so z = v *)
      then have "PostVisit z = PostVisit v"
        using \<open>index_of (PostVisit z) (dfs_stack state) = k\<close> stack_structure
        by (metis index_of.simps(2) less_numeral_extra(3) zero_less_Suc)
      then have "z = v" by simp
      (* v is now in NewSet1 *)
      then have "z \<in> NewSet1"
        using NewSet1_def step_def by simp
      then show ?thesis by simp
    next
      case False
      then have "k > 0" by simp
      have "PostVisit z \<noteq> PostVisit v"
        using \<open>k > 0\<close> \<open>index_of (PostVisit z) (dfs_stack state) = k\<close> stack_structure
        by force
      then have "List.member rest (PostVisit z)"
        using \<open>List.member (dfs_stack state) (PostVisit z)\<close> stack_structure
        by (simp add: member_rec(1))
      moreover have "index_of (PostVisit z) rest = k - 1"
        using \<open>index_of (PostVisit z) (dfs_stack state) = k\<close> \<open>k > 0\<close>
              stack_structure \<open>PostVisit z \<noteq> PostVisit v\<close>
        by auto
      moreover have "k - 1 < j"
        using \<open>k < i\<close> \<open>k > 0\<close> new_index by simp
      ultimately have "z \<in> NewSet2"
        using NewSet2_def step_def by auto
      then show ?thesis by simp
    qed
  qed

  moreover have "OldSet3 \<subseteq> NewSet3"
  proof (rule subsetI)
    fix z
    assume "z \<in> OldSet3"
    then obtain k w where "k < i" and "List.member (dfs_stack state) (PreVisit w)"
                      and "index_of (PreVisit w) (dfs_stack state) = k"
                      and "unvisited_path graph (dfs_visited state) w z"
      using OldSet3_def by blast

    (* PreVisit w cannot be the first frame (which is PostVisit v) *)
    have "PreVisit w \<noteq> PostVisit v" by simp
    then have "List.member rest (PreVisit w)"
      using \<open>List.member (dfs_stack state) (PreVisit w)\<close> stack_structure
      by (simp add: member_rec(1))
    moreover have "k > 0"
      using \<open>index_of (PreVisit w) (dfs_stack state) = k\<close> stack_structure
            \<open>PreVisit w \<noteq> PostVisit v\<close>
      by force
    then have "index_of (PreVisit w) rest = k - 1"
      using \<open>index_of (PreVisit w) (dfs_stack state) = k\<close>
            stack_structure \<open>PreVisit w \<noteq> PostVisit v\<close>
      by auto
    moreover have "k - 1 < j"
      using \<open>k < i\<close> \<open>k > 0\<close> new_index by simp
    moreover have "unvisited_path graph (dfs_visited (dfs_step graph state)) w z"
      using \<open>unvisited_path graph (dfs_visited state) w z\<close> step_def by simp
    ultimately show "z \<in> NewSet3"
      using NewSet3_def step_def by auto
  qed

  ultimately have "OldSet1 \<union> OldSet2 \<union> OldSet3 \<subseteq> NewSet1 \<union> NewSet2 \<union> NewSet3"
    by blast

  moreover have "will_finish_before_me graph state i = OldSet1 \<union> OldSet2 \<union> OldSet3"
    using OldSet1_def OldSet2_def OldSet3_def post_in_old by auto

  moreover have "will_finish_before_me graph (dfs_step graph state) j
        = NewSet1 \<union> NewSet2 \<union> NewSet3"
    using NewSet1_def NewSet2_def NewSet3_def post_in_new by auto

  ultimately show ?thesis by simp
qed

(* Corollary: dfs_step expands the will_finish_before_me set *)
corollary dfs_step_expands_will_finish:
  assumes valid: "dfs_state_valid graph state"
    and non_empty: "dfs_stack state \<noteq> []"
    and post_in_old: "i < length (dfs_stack state) \<and> dfs_stack state ! i = PostVisit x"
    and post_in_new: "j < length (dfs_stack (dfs_step graph state)) \<and>
                      dfs_stack (dfs_step graph state) ! j = PostVisit x"
  shows "will_finish_before_me graph state i \<subseteq>
         will_finish_before_me graph (dfs_step graph state) j"
  by (metis dfs_post_visit_distinct.elims(1)
      dfs_step_expands_will_finish_postvisit
      dfs_step_expands_will_finish_unvisited_previsit
      dfs_step_expands_will_finish_visited_previsit
      non_empty post_in_new post_in_old valid)


(*-----------------------------------------------------------------------------*)
(* Helper lemmas for finish order invariant *)
(*-----------------------------------------------------------------------------*)

(* Lemma: If PostVisit x is at the top of the stack (index 0) and y is in
   WillFinishBeforeMe, then y is already finished *)
lemma will_finish_before_top_implies_finished:
  assumes valid: "dfs_state_valid graph state"
    and stack_head: "dfs_stack state = PostVisit x # rest"
    and y_in_set: "y \<in> will_finish_before_me graph state 0"
  shows "List.member (dfs_finish_order state) y"
proof -
  have "will_finish_before_me graph state 0 =
        set (dfs_finish_order state) \<union>
        {z. \<exists>j. j < 0 \<and>
                  List.member (dfs_stack state) (PostVisit z) \<and>
                  index_of (PostVisit z) (dfs_stack state) = j} \<union>
        {z. \<exists>j w. j < 0 \<and>
                  List.member (dfs_stack state) (PreVisit w) \<and>
                  index_of (PreVisit w) (dfs_stack state) = j \<and>
                  unvisited_path graph (dfs_visited state) w z}"
    using stack_head by auto

  (* The second and third sets are empty since j < 0 is impossible *)
  moreover have "{z. \<exists>j. j < 0 \<and>
                       List.member (dfs_stack state) (PostVisit z) \<and>
                       index_of (PostVisit z) (dfs_stack state) = j} = {}"
    by auto

  moreover have "{z. \<exists>j w. j < 0 \<and>
                       List.member (dfs_stack state) (PreVisit w) \<and>
                       index_of (PreVisit w) (dfs_stack state) = j \<and>
                       unvisited_path graph (dfs_visited state) w z} = {}"
    by auto

  ultimately have "will_finish_before_me graph state 0 = set (dfs_finish_order state)"
    by auto

  then show ?thesis
    using y_in_set by (simp add: in_set_member)
qed

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

(*-----------------------------------------------------------------------------*)
(* DFS step preserves dfs_finish_order_prop *)
(*-----------------------------------------------------------------------------*)

(* Case 1: Previously, all vertices in both SCCs were unvisited *)
lemma dfs_step_preserves_finish_order_case1:
  assumes valid: "dfs_state_valid graph state"
    and previsit_ordered: "dfs_previsit_ordered graph state"
    and postvisit_ordered: "dfs_postvisit_ordered graph state"
    and non_empty: "dfs_stack state \<noteq> []"
    and finish_order_inv: "dfs_finish_order_prop graph state"
    and edge_cd: "has_edge graph c d"
    and diff_scc: "\<not>(in_same_scc graph c d)"
    and case1_before: "finish_order_1 graph state c d"
  shows "finish_order_1 graph (dfs_step graph state) c d \<or>
         finish_order_4 graph (dfs_step graph state) c d \<or>
         finish_order_5 graph (dfs_step graph state) c d"
proof -
  (* From case1_before, all vertices in both SCCs are unvisited *)
  have all_unvisited: "\<forall>v. has_vertex graph v \<and> (in_same_scc graph v c \<or> in_same_scc graph v d) \<longrightarrow>
                            v |\<notin>| dfs_visited state"
    using case1_before by auto

  obtain frame rest where stack_split: "dfs_stack state = frame # rest"
    using non_empty by (cases "dfs_stack state") auto

  show ?thesis
  proof (cases frame)
    case (PreVisit x)
    show ?thesis
    proof (cases "x |\<in>| dfs_visited state")
      case x_already_visited: True
      (* Already visited - case 1 persists *)
      have step_result: "dfs_step graph state = state \<lparr> dfs_stack := rest \<rparr>"
        using stack_split PreVisit x_already_visited by simp
      then have "dfs_visited (dfs_step graph state) = dfs_visited state"
        by simp
      then have "finish_order_1 graph (dfs_step graph state) c d"
        using all_unvisited by auto
      then show ?thesis by simp
    next
      case x_not_visited: False
      (* x is unvisited - this is the interesting case *)
      then have x_not_visited: "x |\<notin>| dfs_visited state" by simp

      show ?thesis
      proof (cases "in_same_scc graph x c \<or> in_same_scc graph x d")
        case x_not_in_either_scc: False
        (* x is not in either SCC - case 1 persists *)
        define neighbors where "neighbors = the (fmlookup graph x)"
        have step_result: "dfs_step graph state =
                           state \<lparr> dfs_visited := finsert x (dfs_visited state),
                                  dfs_stack := map PreVisit neighbors @ [PostVisit x] @ rest \<rparr>"
          using stack_split PreVisit x_not_visited neighbors_def
            dfs_step_previsit_expand valid by blast

        have "\<forall>v. has_vertex graph v \<and> (in_same_scc graph v c \<or> in_same_scc graph v d) \<longrightarrow>
                   v |\<notin>| dfs_visited (dfs_step graph state)"
          using all_unvisited x_not_in_either_scc step_result by auto
        then have "finish_order_1 graph (dfs_step graph state) c d"
          by auto
        then show ?thesis by simp
      next
        case x_in_some_scc: True
        (* x is in c's SCC or d's SCC - the truly interesting case *)
        then show ?thesis
        proof (cases "in_same_scc graph x c")
          case x_in_c_scc: True
          (* x is in c's SCC - need to show case 4 holds *)
          then have x_in_c: "in_same_scc graph x c" by simp

          define neighbors where "neighbors = the (fmlookup graph x)"
          have step_result: "dfs_step graph state =
                             state \<lparr> dfs_visited := finsert x (dfs_visited state),
                                    dfs_stack := map PreVisit neighbors @ [PostVisit x] @ rest \<rparr>"
            using stack_split PreVisit x_not_visited neighbors_def valid dfs_step_previsit_expand 
            by blast

          (* PostVisit x is now at a specific index in the new stack *)
          have x_vertex: "has_vertex graph x"
            using valid stack_split PreVisit by (auto simp: member_rec)

          (* PostVisit x is at index length neighbors in the new stack *)
          define i where "i = length neighbors"
          have postvisit_x_index: "i < length (dfs_stack (dfs_step graph state)) \<and>
                                   dfs_stack (dfs_step graph state) ! i = PostVisit x"
            using step_result i_def by (simp add: nth_append)

          (* Show d's SCC is in WillFinishBeforeMe for PostVisit x *)
          have "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<longrightarrow>
                     z \<in> will_finish_before_me graph (dfs_step graph state) i"
          proof (intro allI impI)
            fix z
            assume z_hyp: "has_vertex graph z \<and> in_same_scc graph z d"

            (* Get paths from x to c, and d to z *)
            have x_reaches_c: "reachable graph x c"
              using x_in_c by simp
            have d_reaches_z: "reachable graph d z"
              using z_hyp by simp

            (* Use helper lemma to get path from x to z (without revisiting x) *)
            obtain path_xz where path_xz_props:
              "valid_path graph path_xz"
              "path_start path_xz = x"
              "path_end path_xz = z"
              "\<forall>v. v \<in> set (tl path_xz) \<longrightarrow> v \<noteq> x"
              "\<forall>v. v \<in> set path_xz \<longrightarrow> in_same_scc graph v c \<or> in_same_scc graph v d"
              by (metis d_reaches_z dfs_state_valid.elims(1) diff_scc edge_cd in_same_scc_sym
                  path_through_edge_without_revisit valid x_in_c x_reaches_c z_hyp)

            (* Extract w from path_xz: path_xz = x # w # ... *)
            (* We need to show path_xz has at least 2 elements *)
            have "path_xz \<noteq> []"
              using path_xz_props(1) by (cases path_xz) auto

            obtain w path_xz_rest where path_xz_decomp: "path_xz = x # w # path_xz_rest"
              using path_xz_props
              by (metis \<open>path_xz \<noteq> []\<close> diff_scc in_same_scc_sym in_same_scc_trans neq_Nil_conv
                  path_end.simps(2) path_start.simps(2) x_in_c z_hyp)
              
            (* w is a neighbor of x *)
            have "has_edge graph x w"
              using path_xz_props(1) path_xz_decomp by auto
            then have w_in_neighbors: "List.member neighbors w"
              using neighbors_def has_edge_member_conv x_vertex by blast

            have w_neq_x: "w \<noteq> x"
              using path_xz_props(4) path_xz_decomp by simp

            (* Build path from w to z *)
            define combined_path where "combined_path = w # path_xz_rest"

            (* This is a valid path from w to z *)
            have combined_valid: "valid_path graph combined_path"
              using path_xz_props(1) path_xz_decomp unfolding combined_path_def by auto
            have combined_start: "path_start combined_path = w"
              unfolding combined_path_def by simp
            have combined_end: "path_end combined_path = z"
              using path_xz_props(3) path_xz_decomp unfolding combined_path_def
              by (metis path_end.simps(3))

            (* All vertices on combined_path are unvisited in new state *)
            have "all_unvisited (dfs_visited (dfs_step graph state)) combined_path"
            proof -
              have visited_eq: "dfs_visited (dfs_step graph state) = finsert x (dfs_visited state)"
                using step_result by simp

              (* Every vertex on combined_path is different from x *)
              have all_neq_x: "\<forall>v. v \<in> set combined_path \<longrightarrow> v \<noteq> x"
              proof (intro allI impI)
                fix v
                assume "v \<in> set combined_path"
                then have "v \<in> set (w # path_xz_rest)"
                  using combined_path_def by auto
                then show "v \<noteq> x"
                  using path_xz_props(4) path_xz_decomp by auto
              qed

              (* Every vertex on the path is in either c's or d's SCC *)
              (* This follows directly from path_xz_props(5) *)
              have "\<forall>v. v \<in> set combined_path \<longrightarrow> in_same_scc graph v c \<or> in_same_scc graph v d"
                using path_xz_props(5) combined_path_def path_xz_decomp by auto

              (* Therefore every vertex was unvisited before *)
              then have "\<forall>v. v \<in> set combined_path \<longrightarrow> v |\<notin>| dfs_visited state"
                using all_unvisited
                using dfs_state_valid.simps valid by blast 

              then show ?thesis
                using visited_eq all_neq_x
                by (auto simp: in_set_member)
            qed

            (* Therefore unvisited_path from w to z *)
            then have "unvisited_path graph (dfs_visited (dfs_step graph state)) w z"
              using combined_valid combined_start combined_end
                    valid_path_implies_unvisited_path valid
              by (metis dfs_state_valid.simps)

            (* PreVisit w is on the stack at some index < i *)
            have w_in_map: "List.member (map PreVisit neighbors) (PreVisit w)"
              using \<open>List.member neighbors w\<close> by (induction neighbors) (auto simp: member_rec)
            then have w_in_stack: "List.member (dfs_stack (dfs_step graph state)) (PreVisit w)"
            proof -
              have "dfs_stack (dfs_step graph state) = 
                      map PreVisit neighbors @ [PostVisit x] @ rest"
                using step_result by simp
              thus ?thesis using w_in_map
                by (simp add: member_def)
            qed

            have w_index_bound: "index_of (PreVisit w) (dfs_stack (dfs_step graph state)) < i"
            proof -
              have stack_eq: "dfs_stack (dfs_step graph state) =
                             map PreVisit neighbors @ [PostVisit x] @ rest"
                using step_result by simp

              (* PreVisit w is at the same position as in the map *)
              have idx_eq: "index_of (PreVisit w) (map PreVisit neighbors @ [PostVisit x] @ rest) =
                           index_of (PreVisit w) (map PreVisit neighbors)"
                using w_in_map by (induction neighbors) (auto simp: member_rec)

              (* The index in map PreVisit neighbors is less than its length *)
              moreover have "index_of (PreVisit w) (map PreVisit neighbors) < length neighbors"
                using w_in_map by (induction neighbors) (auto simp: member_rec)

              ultimately show ?thesis
                using i_def stack_eq by simp
            qed

            (* Therefore z is in WillFinishBeforeMe *)
            then show "z \<in> will_finish_before_me graph (dfs_step graph state) i"
              using postvisit_x_index w_in_stack \<open>unvisited_path graph (dfs_visited (dfs_step graph state)) w z\<close>
              by auto
          qed

          then have "finish_order_4 graph (dfs_step graph state) c d"
            using x_in_c x_vertex postvisit_x_index
            by (meson finish_order_4.elims(3))
          then show ?thesis by simp
        next
          case x_in_d_scc: False
          (* x is in d's SCC - need to show case 5 holds *)
          then have x_in_d: "in_same_scc graph x d"
            using x_in_some_scc by blast

          define neighbors where "neighbors = the (fmlookup graph x)"
          have step_result: "dfs_step graph state =
                             state \<lparr> dfs_visited := finsert x (dfs_visited state),
                                    dfs_stack := map PreVisit neighbors @ [PostVisit x] @ rest \<rparr>"
            using stack_split PreVisit x_not_visited neighbors_def dfs_step_previsit_expand valid
            by blast

          (* PostVisit x is now at a specific index in the new stack *)
          have x_vertex: "has_vertex graph x"
            using valid stack_split PreVisit by (auto simp: member_rec)

          (* PostVisit x is at index length neighbors in the new stack *)
          define i where "i = length neighbors"
          have postvisit_x_index: "i < length (dfs_stack (dfs_step graph state)) \<and>
                                   dfs_stack (dfs_step graph state) ! i = PostVisit x"
            using step_result i_def by (simp add: nth_append)

          (* Show that all vertices in d's SCC except x are in WillFinishBeforeMe *)
          have "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<and> z \<noteq> x \<longrightarrow>
                     z \<in> will_finish_before_me graph (dfs_step graph state) i"
          proof (intro allI impI)
            fix z
            assume z_hyp: "has_vertex graph z \<and> in_same_scc graph z d \<and> z \<noteq> x"

            (* z is in same SCC as x (since both are in d's SCC) *)
            have "in_same_scc graph x z"
              using x_in_d z_hyp by (meson in_same_scc_sym in_same_scc_trans)

            (* Use scc_path_avoiding_vertex to get neighbor p and path from p to z *)
            obtain p where p_props:
              "has_edge graph x p"
              "in_same_scc graph p x"
              "\<exists>path. valid_path graph path \<and>
                      path_start path = p \<and>
                      path_end path = z \<and>
                      \<not>List.member path x"
              using scc_path_avoiding_vertex z_hyp
              using \<open>in_same_scc graph x z\<close> dfs_state_valid.simps valid by blast 

            (* p is a neighbor of x, so PreVisit p is on the stack *)
            have "List.member neighbors p"
              using p_props(1) neighbors_def has_edge_member_conv x_vertex by blast

            (* Extract the path from p to z *)
            obtain path where path_props:
              "valid_path graph path"
              "path_start path = p"
              "path_end path = z"
              "\<not>List.member path x"
              using p_props(3) by blast

            (* All vertices on path are unvisited in the new state *)
            have "all_unvisited (dfs_visited (dfs_step graph state)) path"
            proof -
              have visited_eq: "dfs_visited (dfs_step graph state) = finsert x (dfs_visited state)"
                using step_result by simp

              (* Every vertex on path is different from x *)
              have "\<forall>v. v \<in> set path \<longrightarrow> v \<noteq> x"
                using path_props(4)
                by (meson in_set_member) 

              (* Every vertex on path is in d's SCC, so unvisited before *)
              have "\<forall>v. v \<in> set path \<longrightarrow> in_same_scc graph v d"
              proof (intro allI impI)
                fix v
                assume "v \<in> set path"
                (* v is on path from p to z, and p and z are both in same SCC as d *)
                have "in_same_scc graph p d"
                  using p_props(2) x_in_d by (meson in_same_scc_sym in_same_scc_trans)
                have "in_same_scc graph z d"
                  using z_hyp by (simp add: in_same_scc_sym)
                then have "in_same_scc graph p z"
                  using \<open>in_same_scc graph p d\<close> by (meson in_same_scc_sym in_same_scc_trans)
                then have "in_same_scc graph v p"
                  using path_in_scc_all_in_scc
                  using path_props(2,3) \<open>v \<in> set path\<close>
                  using dfs_state_valid.simps path_in_scc_all_in_scc path_props(1) valid by blast 
                then show "in_same_scc graph v d"
                  using \<open>in_same_scc graph p d\<close> by (meson in_same_scc_sym in_same_scc_trans)
              qed

              (* Therefore all vertices were unvisited before *)
              then have "\<forall>v. v \<in> set path \<longrightarrow> v |\<notin>| dfs_visited state"
                using all_unvisited
                using dfs_state_valid.simps valid by blast 

              then show ?thesis
                using visited_eq \<open>\<forall>v. v \<in> set path \<longrightarrow> v \<noteq> x\<close>
                by (auto simp: in_set_member)
            qed

            (* Therefore there's an unvisited path from p to z *)
            then have "unvisited_path graph (dfs_visited (dfs_step graph state)) p z"
              by (metis dfs_state_valid.elims(2) path_props(1,2,3) valid
                  valid_path_implies_unvisited_path)

            (* PreVisit p is in the new stack, at an index less than i *)
            have "List.member (dfs_stack (dfs_step graph state)) (PreVisit p)"
            proof -
              have "dfs_stack (dfs_step graph state) = map PreVisit neighbors @ [PostVisit x] @ rest"
                using step_result by simp
              moreover have "List.member (map PreVisit neighbors) (PreVisit p)"
                by (metis \<open>List.member neighbors p\<close> in_set_conv_nth in_set_member length_map nth_map)
              ultimately show ?thesis
                using list_membership_lemma_2 by fastforce 
            qed

            moreover have "index_of (PreVisit p) (dfs_stack (dfs_step graph state)) < i"
            proof -
              have stack_eq: "dfs_stack (dfs_step graph state) =
                             map PreVisit neighbors @ [PostVisit x] @ rest"
                using step_result by simp

              have p_in_map: "List.member (map PreVisit neighbors) (PreVisit p)"
                by (metis \<open>List.member neighbors p\<close> in_set_conv_nth in_set_member length_map nth_map)

              have "index_of (PreVisit p) (dfs_stack (dfs_step graph state)) =
                    index_of (PreVisit p) (map PreVisit neighbors)"
                using p_in_map stack_eq index_of_prefix by simp

              moreover have "index_of (PreVisit p) (map PreVisit neighbors) < length neighbors"
                using \<open>List.member neighbors p\<close> by (induction neighbors) (auto simp: member_rec)

              ultimately show ?thesis
                using i_def by simp
            qed

            (* Therefore z is in WillFinishBeforeMe *)
            ultimately show "z \<in> will_finish_before_me graph (dfs_step graph state) i"
              using postvisit_x_index \<open>unvisited_path graph (dfs_visited (dfs_step graph state)) p z\<close>
              by auto
          qed

          (* We need to show there's a vertex in c's SCC that's unfinished *)
          have "\<exists>v. has_vertex graph v \<and> in_same_scc graph v c \<and>
                     \<not>List.member (dfs_finish_order (dfs_step graph state)) v"
          proof -
            (* c is unvisited, so it's unfinished *)
            have "has_vertex graph c"
              using edge_implies_vertices
              using dfs_state_valid.elims(1) edge_cd valid by blast
            moreover have "in_same_scc graph c c"
              by (meson calculation in_same_scc_refl)
            moreover have "\<not>List.member (dfs_finish_order (dfs_step graph state)) c"
              by (metis all_unvisited calculation(2) dfs_state_valid.elims(2) select_convs(2) step_result
                  surjective update_convs(1,3) valid)
            ultimately show ?thesis by blast
          qed

          then have "finish_order_5 graph (dfs_step graph state) c d"
            using x_in_d x_vertex postvisit_x_index \<open>\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<and> z \<noteq> x \<longrightarrow>
                     z \<in> will_finish_before_me graph (dfs_step graph state) i\<close>
            by (metis finish_order_5.elims(3))
          then show ?thesis by simp
        qed
      qed
    qed
  next
    case (PostVisit v)
    (* Popping PostVisit - case 1 persists *)
    have step_result: "dfs_step graph state =
                       state \<lparr> dfs_finish_order := v # dfs_finish_order state,
                              dfs_stack := rest \<rparr>"
      using stack_split PostVisit by simp
    then have "dfs_visited (dfs_step graph state) = dfs_visited state"
      by simp
    then have "finish_order_1 graph (dfs_step graph state) c d"
      using all_unvisited by auto
    then show ?thesis by simp
  qed
qed

(* Case 2: Previously, all vertices from d's SCC were finished,
   and at least one from c's SCC was unfinished *)
lemma dfs_step_preserves_finish_order_case2:
  assumes valid: "dfs_state_valid graph state"
    and previsit_ordered: "dfs_previsit_ordered graph state"
    and postvisit_ordered: "dfs_postvisit_ordered graph state"
    and non_empty: "dfs_stack state \<noteq> []"
    and finish_order_inv: "dfs_finish_order_prop graph state"
    and edge_cd: "has_edge graph c d"
    and diff_scc: "\<not>(in_same_scc graph c d)"
    and case2_before: "finish_order_2 graph state c d"
  shows "finish_order_2 graph (dfs_step graph state) c d \<or>
         finish_order_3 graph (dfs_step graph state) c d"
proof -
  (* From case2_before, all of d's SCC is finished, at least one in c's SCC is unfinished *)
  have all_d_finished: "\<forall>v. has_vertex graph v \<and> in_same_scc graph v d \<longrightarrow>
                             List.member (dfs_finish_order state) v"
    using case2_before by auto

  have c_has_unfinished: "\<exists>v. has_vertex graph v \<and> in_same_scc graph v c \<and>
                               \<not>List.member (dfs_finish_order state) v"
    using case2_before by auto

  obtain frame rest where stack_split: "dfs_stack state = frame # rest"
    using non_empty by (cases "dfs_stack state") auto

  show ?thesis
  proof (cases frame)
    case (PreVisit u)
    show ?thesis
    proof (cases "u |\<in>| dfs_visited state")
      case True
      (* Already visited - finish order unchanged *)
      have step_result: "dfs_step graph state = state \<lparr> dfs_stack := rest \<rparr>"
        using stack_split PreVisit True by simp
      then have "dfs_finish_order (dfs_step graph state) = dfs_finish_order state"
        by simp
      then have "finish_order_2 graph (dfs_step graph state) c d"
        using all_d_finished c_has_unfinished by auto
      then show ?thesis by simp
    next
      case False
      (* Not visited - finish order unchanged *)
      define neighbors where "neighbors = the (fmlookup graph u)"
      have step_result: "dfs_step graph state =
                         state \<lparr> dfs_visited := finsert u (dfs_visited state),
                                dfs_stack := map PreVisit neighbors @ [PostVisit u] @ rest \<rparr>"
        using stack_split PreVisit False neighbors_def valid dfs_step_previsit_expand by blast
      then have "dfs_finish_order (dfs_step graph state) = dfs_finish_order state"
        by simp
      then have "finish_order_2 graph (dfs_step graph state) c d"
        using all_d_finished c_has_unfinished by auto
      then show ?thesis by simp
    qed
  next
    case (PostVisit v)
    (* Popping PostVisit v - adding v to finish order *)
    have step_result: "dfs_step graph state =
                       state \<lparr> dfs_finish_order := v # dfs_finish_order state,
                              dfs_stack := rest \<rparr>"
      using stack_split PostVisit by simp

    (* All of d's SCC remains finished *)
    have "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<longrightarrow>
               List.member (dfs_finish_order (dfs_step graph state)) z"
      using all_d_finished step_result by (auto simp: member_rec)

    (* Check if v is the last unfinished vertex in c's SCC *)
    show ?thesis
    proof (cases "in_same_scc graph v c \<and> (\<forall>u. has_vertex graph u \<and> in_same_scc graph u c \<and> u \<noteq> v \<longrightarrow>
                                                 List.member (dfs_finish_order state) u)")
      case True
      (* v is the last unfinished in c's SCC - case 3 holds *)
      have all_c_finished: "\<forall>u. has_vertex graph u \<and> in_same_scc graph u c \<longrightarrow>
                                  List.member (dfs_finish_order (dfs_step graph state)) u"
        using True step_result by (auto simp: member_rec)

      (* v is now at the head, so some vertex from c's SCC comes before all of d's SCC *)
      have "\<exists>v_c. has_vertex graph v_c \<and> in_same_scc graph v_c c \<and>
                  (\<forall>v_d. has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
                    index_of v_c (dfs_finish_order (dfs_step graph state)) <
                    index_of v_d (dfs_finish_order (dfs_step graph state)))"
      proof -
        have "has_vertex graph v"
          using valid stack_split PostVisit by (auto simp: member_rec)
        have "\<forall>v_d. has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
                    index_of v (v # dfs_finish_order state) <
                    index_of v_d (v # dfs_finish_order state)"
        proof (intro allI impI)
          fix v_d
          assume "has_vertex graph v_d \<and> in_same_scc graph v_d d"
          then have "List.member (dfs_finish_order state) v_d"
            using all_d_finished by auto
          then show "index_of v (v # dfs_finish_order state) <
                    index_of v_d (v # dfs_finish_order state)"
            using True c_has_unfinished by auto
        qed
        then show ?thesis
          using True \<open>has_vertex graph v\<close> step_result by auto
      qed

      then have "finish_order_3 graph (dfs_step graph state) c d"
        using all_c_finished \<open>\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<longrightarrow>
                                     List.member (dfs_finish_order (dfs_step graph state)) z\<close>
        by auto
      then show ?thesis by simp
    next
      case False
      (* v is not the last unfinished in c's SCC, or v is not in c's SCC - case 2 holds *)
      have "\<exists>u. has_vertex graph u \<and> in_same_scc graph u c \<and>
                 \<not>List.member (dfs_finish_order (dfs_step graph state)) u"
      proof (cases "in_same_scc graph v c")
        case True
        (* v is in c's SCC but not the last - there exists another unfinished vertex *)
        then have "\<exists>w. has_vertex graph w \<and> in_same_scc graph w c \<and> w \<noteq> v \<and>
                       \<not>List.member (dfs_finish_order state) w"
          using False True by auto
        then obtain u where u_props: "has_vertex graph u" "in_same_scc graph u c" "u \<noteq> v"
                                  "\<not>List.member (dfs_finish_order state) u"
          by auto
        then have "\<not>List.member (dfs_finish_order (dfs_step graph state)) u"
          using step_result by (auto simp: member_rec)
        then show ?thesis
          using u_props by auto
      next
        case False
        (* v is not in c's SCC - any unfinished vertex in c's SCC will do *)
        obtain u where u_props: "has_vertex graph u" "in_same_scc graph u c"
                             "\<not>List.member (dfs_finish_order state) u"
          using c_has_unfinished by auto
        have "u \<noteq> v"
          using u_props False by (meson in_same_scc_sym)
        then have "\<not>List.member (dfs_finish_order (dfs_step graph state)) u"
          using u_props step_result by (auto simp: member_rec)
        then show ?thesis
          using u_props by auto
      qed

      then have "finish_order_2 graph (dfs_step graph state) c d"
        using \<open>\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<longrightarrow>
                   List.member (dfs_finish_order (dfs_step graph state)) z\<close>
        by auto
      then show ?thesis by simp
    qed
  qed
qed

(* Case 3: Previously, all vertices in both SCCs were finished *)
lemma dfs_step_preserves_finish_order_case3:
  assumes valid: "dfs_state_valid graph state"
    and previsit_ordered: "dfs_previsit_ordered graph state"
    and postvisit_ordered: "dfs_postvisit_ordered graph state"
    and non_empty: "dfs_stack state \<noteq> []"
    and finish_order_inv: "dfs_finish_order_prop graph state"
    and edge_cd: "has_edge graph c d"
    and diff_scc: "\<not>(in_same_scc graph c d)"
    and case3_before: "finish_order_3 graph state c d"
  shows "finish_order_3 graph (dfs_step graph state) c d"
proof -
  (* Unfold the definition of finish_order_3 *)
  have all_finished: "\<forall>v. has_vertex graph v \<and> (in_same_scc graph v c \<or> in_same_scc graph v d) \<longrightarrow>
                           List.member (dfs_finish_order state) v"
    using case3_before by auto

  have order_correct: "\<exists>v_c. has_vertex graph v_c \<and> in_same_scc graph v_c c \<and>
                              (\<forall>v_d. has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
                                index_of v_c (dfs_finish_order state) < index_of v_d (dfs_finish_order state))"
    using case3_before by auto

  (* After dfs_step, the finish order either stays the same or grows *)
  obtain frame rest where stack_split: "dfs_stack state = frame # rest"
    using non_empty by (cases "dfs_stack state") auto

  show ?thesis
  proof (cases frame)
    case (PreVisit u)
    show ?thesis
    proof (cases "u |\<in>| dfs_visited state")
      case True
      (* PreVisit u already visited: finish order unchanged *)
      have "dfs_step graph state = state \<lparr> dfs_stack := rest \<rparr>"
        using stack_split PreVisit True by simp
      then have "dfs_finish_order (dfs_step graph state) = dfs_finish_order state"
        by simp
      then show ?thesis
        using all_finished order_correct by auto
    next
      case False
      (* PreVisit u not visited: finish order unchanged *)
      define neighbors where "neighbors = the (fmlookup graph u)"
      have "dfs_step graph state =
            state \<lparr> dfs_visited := finsert u (dfs_visited state),
                   dfs_stack := map PreVisit neighbors @ [PostVisit u] @ rest \<rparr>"
        using stack_split PreVisit False neighbors_def valid dfs_step_previsit_expand by blast
      then have "dfs_finish_order (dfs_step graph state) = dfs_finish_order state"
        by simp
      then show ?thesis
        using all_finished order_correct by auto
    qed
  next
    case (PostVisit v)
    (* PostVisit v: finish order grows by prepending v *)
    have "dfs_step graph state = state \<lparr> dfs_finish_order := v # (dfs_finish_order state),
                                           dfs_stack := rest \<rparr>"
      using stack_split PostVisit by simp
    then have new_finish: "dfs_finish_order (dfs_step graph state) = v # dfs_finish_order state"
      by simp

    (* All vertices in both SCCs remain in the finish order *)
    have "\<forall>w. has_vertex graph w \<and> (in_same_scc graph w c \<or> in_same_scc graph w d) \<longrightarrow>
               List.member (dfs_finish_order (dfs_step graph state)) w"
      using all_finished new_finish by (auto simp: member_rec)

    (* The ordering is preserved: indices just shift by 1 using index_of_cons_shift *)
    moreover have "\<exists>v_c. has_vertex graph v_c \<and> in_same_scc graph v_c c \<and>
                          (\<forall>v_d. has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
                            index_of v_c (dfs_finish_order (dfs_step graph state)) <
                            index_of v_d (dfs_finish_order (dfs_step graph state)))"
    proof -
      obtain v_c where v_c_props: "has_vertex graph v_c" "in_same_scc graph v_c c"
                   and v_c_before_all: "\<forall>v_d. has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
                                             index_of v_c (dfs_finish_order state) <
                                             index_of v_d (dfs_finish_order state)"
        using order_correct by blast

      have v_c_in_old: "List.member (dfs_finish_order state) v_c"
        using all_finished v_c_props by auto

      have "\<forall>v_d. has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
                  index_of v_c (dfs_finish_order (dfs_step graph state)) <
                  index_of v_d (dfs_finish_order (dfs_step graph state))"
      proof (intro allI impI)
        fix v_d
        assume v_d_hyp: "has_vertex graph v_d \<and> in_same_scc graph v_d d"
        then have v_d_in_old: "List.member (dfs_finish_order state) v_d"
          using all_finished by auto

        (* Apply index_of_cons_shift to both since v \<noteq> v_c and v \<noteq> v_d *)
        have "index_of v_c (v # dfs_finish_order state) = Suc (index_of v_c (dfs_finish_order state))"
          using index_of_cons_shift v_c_in_old
          by (metis PostVisit dfs_state_valid.simps member_rec(1) stack_split
              valid) 
        moreover have "index_of v_d (v # dfs_finish_order state) = Suc (index_of v_d (dfs_finish_order state))"
          using index_of_cons_shift v_d_in_old 
          by (metis PostVisit dfs_state_valid.simps member_rec(1) stack_split
              valid)
        ultimately show "index_of v_c (dfs_finish_order (dfs_step graph state)) <
                        index_of v_d (dfs_finish_order (dfs_step graph state))"
          using v_c_before_all v_d_hyp new_finish by simp
      qed

      then show ?thesis
        using v_c_props by blast
    qed

    ultimately show ?thesis
      by auto
  qed
qed

(* Case 4: Previously, at least one vertex in c's SCC was visited (not finished)
   and its WillFinishBeforeMe set contained everything in d's SCC *)
lemma dfs_step_preserves_finish_order_case4:
  assumes valid: "dfs_state_valid graph state"
    and previsit_ordered: "dfs_previsit_ordered graph state"
    and postvisit_ordered: "dfs_postvisit_ordered graph state"
    and non_empty: "dfs_stack state \<noteq> []"
    and finish_order_inv: "dfs_finish_order_prop graph state"
    and edge_cd: "has_edge graph c d"
    and diff_scc: "\<not>(in_same_scc graph c d)"
    and case4_before: "finish_order_4 graph state c d"
  shows "finish_order_2 graph (dfs_step graph state) c d \<or>
         finish_order_3 graph (dfs_step graph state) c d \<or>
         finish_order_4 graph (dfs_step graph state) c d"
proof -
  (* From case4_before, get the witness vertex v in c's SCC *)
  obtain v i where
    v_in_c: "has_vertex graph v \<and> in_same_scc graph v c"
    and i_valid: "i < length (dfs_stack state)"
    and stack_at_i: "dfs_stack state ! i = PostVisit v"
    and d_scc_in_wfbm: "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<longrightarrow>
                             z \<in> will_finish_before_me graph state i"
    using case4_before by auto

  obtain frame rest where stack_split: "dfs_stack state = frame # rest"
    using non_empty by (cases "dfs_stack state") auto

  show ?thesis
  proof (cases "i = 0")
    case True
    (* PostVisit v is at the top of the stack - it will be popped *)
    then have "frame = PostVisit v"
      using stack_at_i stack_split by simp

    show ?thesis
    proof (cases frame)
      case (PostVisit x)
      then have "x = v"
        using \<open>frame = PostVisit v\<close> by simp

      (* All of d's SCC is in WillFinishBeforeMe at index 0, so all finished *)
      have "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<longrightarrow>
                 List.member (dfs_finish_order state) z"
        using d_scc_in_wfbm True will_finish_before_top_implies_finished
              valid stack_split \<open>frame = PostVisit v\<close>
        by blast

      (* dfs_step will add v to finish order *)
      have step_result: "dfs_step graph state =
                         state \<lparr> dfs_finish_order := v # dfs_finish_order state,
                                dfs_stack := rest \<rparr>"
        using stack_split PostVisit \<open>x = v\<close> by simp

      (* Check if v is the last unfinished vertex in c's SCC *)
      show ?thesis
      proof (cases "\<forall>u. has_vertex graph u \<and> in_same_scc graph u c \<and> u \<noteq> v \<longrightarrow>
                         List.member (dfs_finish_order state) u")
        case True
        (* v is the last - after step, all of c's SCC is finished, so case 3 holds *)
        have all_c_finished: "\<forall>u. has_vertex graph u \<and> in_same_scc graph u c \<longrightarrow>
                                    List.member (dfs_finish_order (dfs_step graph state)) u"
          using True step_result v_in_c by (auto simp: member_rec)

        have all_d_finished: "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<longrightarrow>
                                    List.member (dfs_finish_order (dfs_step graph state)) z"
          using \<open>\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<longrightarrow>
                     List.member (dfs_finish_order state) z\<close>
                step_result by (auto simp: member_rec)

        (* v is now at the head, so some vertex from c's SCC comes before all of d's SCC *)
        have "\<exists>v_c. has_vertex graph v_c \<and> in_same_scc graph v_c c \<and>
                    (\<forall>v_d. has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
                      index_of v_c (dfs_finish_order (dfs_step graph state)) <
                      index_of v_d (dfs_finish_order (dfs_step graph state)))"
        proof -
          have "\<forall>v_d. has_vertex graph v_d \<and> in_same_scc graph v_d d \<longrightarrow>
                      index_of v (v # dfs_finish_order state) <
                      index_of v_d (v # dfs_finish_order state)"
          proof (intro allI impI)
            fix v_d
            assume "has_vertex graph v_d \<and> in_same_scc graph v_d d"
            then have "List.member (dfs_finish_order state) v_d"
              using \<open>\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<longrightarrow>
                         List.member (dfs_finish_order state) z\<close> by auto
            then show "index_of v (v # dfs_finish_order state) <
                      index_of v_d (v # dfs_finish_order state)"
              by (metis \<open>has_vertex graph v_d \<and> in_same_scc graph v_d d\<close> diff_scc
                  gr_zeroI in_same_scc_sym in_same_scc_trans index_of.simps(2)
                  nat.simps(3) v_in_c)
          qed
          then show ?thesis
            using v_in_c step_result by auto
        qed

        then have "finish_order_3 graph (dfs_step graph state) c d"
          using all_c_finished all_d_finished by auto
        then show ?thesis by simp
      next
        case False
        (* v is not the last - some vertex in c's SCC is still unfinished, so case 2 holds *)
        have "finish_order_2 graph (dfs_step graph state) c d"
          using \<open>\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<longrightarrow>
                     List.member (dfs_finish_order state) z\<close>
                False step_result by (auto simp: member_rec)
        then show ?thesis by simp
      qed
    qed (use \<open>frame = PostVisit v\<close> in auto)
  next
    case False
    (* PostVisit v is not at the top - it remains on the stack or shifts position *)
    then have "i > 0" by simp

    show ?thesis
    proof (cases frame)
      case (PreVisit u)
      show ?thesis
      proof (cases "u |\<in>| dfs_visited state")
        case True
        (* Already visited - just pop, PostVisit v stays on stack *)
        have step_result: "dfs_step graph state = state \<lparr> dfs_stack := rest \<rparr>"
          using stack_split PreVisit True by simp

        (* PostVisit v is still on the stack at index i-1 *)
        have "i - 1 < length (dfs_stack (dfs_step graph state))"
          using i_valid step_result stack_split \<open>i > 0\<close> by simp
        moreover have "dfs_stack (dfs_step graph state) ! (i - 1) = PostVisit v"
          using stack_at_i stack_split \<open>i > 0\<close> step_result
          by simp
        moreover have "will_finish_before_me graph state i \<subseteq>
                      will_finish_before_me graph (dfs_step graph state) (i - 1)"
          using dfs_step_expands_will_finish valid non_empty stack_at_i i_valid
                calculation
          by blast

        ultimately have "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<longrightarrow>
                             z \<in> will_finish_before_me graph (dfs_step graph state) (i - 1)"
          using d_scc_in_wfbm by auto

        then have "finish_order_4 graph (dfs_step graph state) c d"
          using \<open>dfs_stack (dfs_step graph state) ! (i - 1) = PostVisit v\<close>
            \<open>i - 1 < length (dfs_stack (dfs_step graph state))\<close>
            finish_order_4.simps v_in_c by blast
          
        then show ?thesis by simp
      next
        case False
        (* Not visited - expand it, PostVisit v moves further down the stack *)
        define neighbors where "neighbors = the (fmlookup graph u)"
        have step_result: "dfs_step graph state =
                           state \<lparr> dfs_visited := finsert u (dfs_visited state),
                                  dfs_stack := map PreVisit neighbors @ [PostVisit u] @ rest \<rparr>"
          using stack_split PreVisit False neighbors_def
          using dfs_step_previsit_expand valid by blast 

        (* PostVisit v is still on the stack, at a new index *)
        have "PostVisit v \<in> set rest"
          using stack_at_i stack_split \<open>i > 0\<close>
          by (metis PreVisit dfs_frame.simps(4) i_valid nth_mem
              set_ConsD)
        then have v_in_new: "PostVisit v \<in> set (dfs_stack (dfs_step graph state))"
          using step_result by auto

        obtain j where j_props: "j < length (dfs_stack (dfs_step graph state))"
                              "dfs_stack (dfs_step graph state) ! j = PostVisit v"
          using v_in_new by (metis in_set_conv_nth)

        have "will_finish_before_me graph state i \<subseteq>
              will_finish_before_me graph (dfs_step graph state) j"
          using dfs_step_expands_will_finish valid non_empty stack_at_i i_valid j_props
          by blast

        then have "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<longrightarrow>
                       z \<in> will_finish_before_me graph (dfs_step graph state) j"
          using d_scc_in_wfbm by auto

        then have "finish_order_4 graph (dfs_step graph state) c d"
          using v_in_c j_props
          by (meson finish_order_4.elims(3)) 
        then show ?thesis by simp
      qed
    next
      case (PostVisit w)
      (* Popping PostVisit w - PostVisit v shifts up by 1 *)
      have step_result: "dfs_step graph state =
                         state \<lparr> dfs_finish_order := w # dfs_finish_order state,
                                dfs_stack := rest \<rparr>"
        using stack_split PostVisit by simp

      have "i - 1 < length (dfs_stack (dfs_step graph state))"
        using i_valid step_result stack_split \<open>i > 0\<close> by simp
      moreover have "dfs_stack (dfs_step graph state) ! (i - 1) = PostVisit v"
        using stack_at_i stack_split \<open>i > 0\<close> step_result
        by simp
      moreover have "will_finish_before_me graph state i \<subseteq>
                    will_finish_before_me graph (dfs_step graph state) (i - 1)"
        using dfs_step_expands_will_finish valid non_empty stack_at_i i_valid
              calculation
        by blast

      ultimately have "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<longrightarrow>
                           z \<in> will_finish_before_me graph (dfs_step graph state) (i - 1)"
        using d_scc_in_wfbm by auto

      then have "finish_order_4 graph (dfs_step graph state) c d"
        using \<open>dfs_stack (dfs_step graph state) ! (i - 1) = PostVisit v\<close>
          \<open>i - 1 < length (dfs_stack (dfs_step graph state))\<close>
          finish_order_4.simps v_in_c by blast
      then show ?thesis by simp
    qed
  qed
qed

(* Case 5: Previously, at least one vertex x in d's SCC was visited (not finished)
   and its WillFinishBeforeMe set contained everything else in d's SCC *)
lemma dfs_step_preserves_finish_order_case5:
  assumes valid: "dfs_state_valid graph state"
    and previsit_ordered: "dfs_previsit_ordered graph state"
    and postvisit_ordered: "dfs_postvisit_ordered graph state"
    and non_empty: "dfs_stack state \<noteq> []"
    and finish_order_inv: "dfs_finish_order_prop graph state"
    and edge_cd: "has_edge graph c d"
    and diff_scc: "\<not>(in_same_scc graph c d)"
    and case5_before: "finish_order_5 graph state c d"
  shows "finish_order_2 graph (dfs_step graph state) c d \<or>
         finish_order_5 graph (dfs_step graph state) c d"
proof -
  (* From case5_before, get the witness vertex x in d's SCC *)
  obtain v_c where v_c_unfinished: 
      "has_vertex graph v_c \<and> 
       in_same_scc graph v_c c \<and>
       \<not>List.member (dfs_finish_order state) v_c"
    using case5_before by auto

  obtain x i where
    x_in_d: "has_vertex graph x \<and> in_same_scc graph x d"
    and i_valid: "i < length (dfs_stack state)"
    and stack_at_i: "dfs_stack state ! i = PostVisit x"
    and d_scc_minus_x_in_wfbm: "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<and> z \<noteq> x \<longrightarrow>
                                     z \<in> will_finish_before_me graph state i"
    using case5_before by auto

  obtain frame rest where stack_split: "dfs_stack state = frame # rest"
    using non_empty by (cases "dfs_stack state") auto

  show ?thesis
  proof (cases "i = 0")
    case True
    (* PostVisit x is at the top of the stack - it will be popped *)
    then have "frame = PostVisit x"
      using stack_at_i stack_split by simp

    (* All of d's SCC except x is in WillFinishBeforeMe at index 0, so all finished *)
    have "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<and> z \<noteq> x \<longrightarrow>
               List.member (dfs_finish_order state) z"
      using d_scc_minus_x_in_wfbm True will_finish_before_top_implies_finished
            valid stack_split \<open>frame = PostVisit x\<close>
      by blast

    (* dfs_step will add x to finish order *)
    have step_result: "dfs_step graph state =
                       state \<lparr> dfs_finish_order := x # dfs_finish_order state,
                              dfs_stack := rest \<rparr>"
      using stack_split \<open>frame = PostVisit x\<close> by simp

    (* After this step, all of d's SCC is finished *)
    have all_d_finished: "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<longrightarrow>
                                List.member (dfs_finish_order (dfs_step graph state)) z"
      using \<open>\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<and> z \<noteq> x \<longrightarrow>
                 List.member (dfs_finish_order state) z\<close>
            step_result x_in_d by (auto simp: member_rec)

    (* Some vertex in c's SCC is still unfinished *)
    have c_not_all_finished:
        "\<exists>v. has_vertex graph v \<and> in_same_scc graph v c \<and>
             \<not>List.member (dfs_finish_order (dfs_step graph state)) v"
    proof -
      have "v_c \<noteq> x"
        using v_c_unfinished x_in_d diff_scc
        by (metis in_same_scc_trans in_same_scc_sym)
      then show ?thesis
        using v_c_unfinished step_result by (auto simp: member_rec)
    qed

    (* Therefore case 2 holds *)
    have "finish_order_2 graph (dfs_step graph state) c d"
      using all_d_finished c_not_all_finished by auto
    then show ?thesis by simp
  next
    case False
    (* PostVisit x is not at the top - it remains on the stack *)
    then have "i > 0" by simp

    show ?thesis
    proof (cases frame)
      case (PreVisit u)
      show ?thesis
      proof (cases "u |\<in>| dfs_visited state")
        case True
        (* Already visited - just pop, PostVisit x stays on stack *)
        have step_result: "dfs_step graph state = state \<lparr> dfs_stack := rest \<rparr>"
          using stack_split PreVisit True by simp

        (* PostVisit x is still on the stack at index i-1 *)
        have "i - 1 < length (dfs_stack (dfs_step graph state))"
          using i_valid step_result stack_split \<open>i > 0\<close> by simp
        moreover have "dfs_stack (dfs_step graph state) ! (i - 1) = PostVisit x"
          using stack_at_i stack_split \<open>i > 0\<close> step_result by simp
        moreover have "will_finish_before_me graph state i \<subseteq>
                      will_finish_before_me graph (dfs_step graph state) (i - 1)"
          using dfs_step_expands_will_finish valid non_empty stack_at_i i_valid
                calculation
          by blast

        ultimately have "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<and> z \<noteq> x \<longrightarrow>
                             z \<in> will_finish_before_me graph (dfs_step graph state) (i - 1)"
          using d_scc_minus_x_in_wfbm by auto

        moreover have "\<exists>v. has_vertex graph v \<and> in_same_scc graph v c \<and>
                            \<not>List.member (dfs_finish_order (dfs_step graph state)) v"
          using v_c_unfinished step_result
          by auto 
        ultimately have "finish_order_5 graph (dfs_step graph state) c d"
          using x_in_d
          by (metis \<open>dfs_stack (dfs_step graph state) ! (i - 1) = PostVisit x\<close>
              \<open>i - 1 < length (dfs_stack (dfs_step graph state))\<close>
              finish_order_5.elims(3)) 
        then show ?thesis by simp
      next
        case False
        (* Not visited - expand it, PostVisit x moves further down the stack *)
        define neighbors where "neighbors = the (fmlookup graph u)"
        have step_result: "dfs_step graph state =
                           state \<lparr> dfs_visited := finsert u (dfs_visited state),
                                  dfs_stack := map PreVisit neighbors @ [PostVisit u] @ rest \<rparr>"
          using stack_split PreVisit False neighbors_def valid dfs_step_previsit_expand by blast

        (* PostVisit x is still on the stack, at a new index *)
        have "PostVisit x \<in> set rest"
          using stack_at_i stack_split \<open>i > 0\<close>
          by (metis PreVisit dfs_frame.simps(4) i_valid nth_mem
              set_ConsD)
        then have x_in_new: "PostVisit x \<in> set (dfs_stack (dfs_step graph state))"
          using step_result by auto

        obtain j where j_props: "j < length (dfs_stack (dfs_step graph state))"
                              "dfs_stack (dfs_step graph state) ! j = PostVisit x"
          using x_in_new by (metis in_set_conv_nth)

        have "will_finish_before_me graph state i \<subseteq>
              will_finish_before_me graph (dfs_step graph state) j"
          using dfs_step_expands_will_finish valid non_empty stack_at_i i_valid j_props
          by blast

        then have "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<and> z \<noteq> x \<longrightarrow>
                       z \<in> will_finish_before_me graph (dfs_step graph state) j"
          using d_scc_minus_x_in_wfbm by auto

        moreover have "\<exists>v. has_vertex graph v \<and> in_same_scc graph v c \<and>
                            \<not>List.member (dfs_finish_order (dfs_step graph state)) v"
        proof -
          have "dfs_finish_order (dfs_step graph state) = dfs_finish_order state"
            using step_result by simp
          then show ?thesis
            using v_c_unfinished by auto
        qed

        ultimately have "finish_order_5 graph (dfs_step graph state) c d"
          using x_in_d j_props
          by (metis finish_order_5.elims(3)) 
        then show ?thesis by simp
      qed
    next
      case (PostVisit w)
      (* Popping PostVisit w - PostVisit x shifts up by 1 *)
      have step_result: "dfs_step graph state =
                         state \<lparr> dfs_finish_order := w # dfs_finish_order state,
                                dfs_stack := rest \<rparr>"
        using stack_split PostVisit by simp

      have "i - 1 < length (dfs_stack (dfs_step graph state))"
        using i_valid step_result stack_split \<open>i > 0\<close> by simp
      moreover have "dfs_stack (dfs_step graph state) ! (i - 1) = PostVisit x"
        using stack_at_i stack_split \<open>i > 0\<close> step_result by simp
      moreover have "will_finish_before_me graph state i \<subseteq>
                    will_finish_before_me graph (dfs_step graph state) (i - 1)"
        using dfs_step_expands_will_finish valid non_empty stack_at_i i_valid
              calculation
        by blast

      ultimately have "\<forall>z. has_vertex graph z \<and> in_same_scc graph z d \<and> z \<noteq> x \<longrightarrow>
                           z \<in> will_finish_before_me graph (dfs_step graph state) (i - 1)"
        using d_scc_minus_x_in_wfbm by auto

      moreover have "\<exists>v. has_vertex graph v \<and> in_same_scc graph v c \<and>
                          \<not>List.member (dfs_finish_order (dfs_step graph state)) v"
      proof -
        have "v_c \<noteq> w"
        proof (rule notI)
          assume "v_c = w"
          (* PostVisit w is at index 0 in old stack, PostVisit x is at index i > 0 *)
          have w_in_stack: "List.member (dfs_stack state) (PostVisit w)"
            using stack_split PostVisit by (simp add: member_rec)
          have x_in_stack: "List.member (dfs_stack state) (PostVisit x)"
            using stack_at_i i_valid by (metis in_set_member nth_mem)
          have w_before_x: "index_of (PostVisit w) (dfs_stack state) < index_of (PostVisit x) (dfs_stack state)"
            using stack_split PostVisit \<open>i > 0\<close> stack_at_i
            by (metis dfs_state_valid.simps i_valid index_of.simps(2)
                index_of_postvisit_conv valid) 
          (* By postvisit_ordered, x reaches w *)
          have "reachable graph x w"
            using postvisit_ordered w_in_stack x_in_stack w_before_x by auto
          (* x is in d's SCC, w is in c's SCC (via v_c) *)
          then have "reachable graph d c"
            using x_in_d v_c_unfinished \<open>v_c = w\<close>
            by (meson in_same_scc.simps reachable_trans)
          (* But we have edge c -> d, so c reaches d *)
          moreover have "reachable graph c d"
            by (meson edge_cd in_same_scc.simps reachable.simps reachable_trans
                v_c_unfinished)
          (* Therefore c and d are in same SCC *)
          ultimately have "in_same_scc graph c d"
            by simp
          (* Contradiction *)
          then show False
            using diff_scc by simp
        qed
        then show ?thesis
          using v_c_unfinished step_result by (auto simp: member_rec)
      qed

      ultimately have "finish_order_5 graph (dfs_step graph state) c d"
        by (meson \<open>dfs_stack (dfs_step graph state) ! (i - 1) = PostVisit x\<close>
            \<open>i - 1 < length (dfs_stack (dfs_step graph state))\<close>
            finish_order_5.elims(3) x_in_d)
        
      then show ?thesis by simp
    qed
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
  by (metis dfs_finish_order_prop.simps
      dfs_step_preserves_finish_order_case1
      dfs_step_preserves_finish_order_case2
      dfs_step_preserves_finish_order_case3
      dfs_step_preserves_finish_order_case4
      dfs_step_preserves_finish_order_case5 finish_order_inv non_empty
      postvisit_ordered previsit_ordered valid)
  
end
