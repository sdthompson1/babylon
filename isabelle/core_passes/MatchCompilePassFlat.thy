theory MatchCompilePassFlat
  imports MatchCompilePass MatchCompileTyping
begin

(* This file proves that the output of match_compile_module satisfies the
   predicates that the next stage (the code generator) needs:

    - core_module_flat (every pattern of every match is flat), for a
      ghost-free input module;
    - core_module_ghost_free and core_module_closed, if the input satisfies
      them.

   Proof notes:

   Besides flatness of the patterns (compile_matrix_flat, MatchCompileFlat.thy),
   flatness of the output needs two more facts about the trees that
   compile_matrix builds, proved here as compile_matrix_tests_ok:

    - the scrutinee of every test is obtained from the input scrutinees by
      record and variant projections, so it is flat if they are;
    - every test has at least one arm (needed later for the typing of a term
      match, which must not be empty). *)


section \<open>Test nodes of a tree\<close>

(* P holds of every test scrutinee of the tree, and every test has an arm. *)
fun match_tree_tests_ok :: "(CoreTerm \<Rightarrow> bool) \<Rightarrow> 'body MatchTree \<Rightarrow> bool" where
  "match_tree_tests_ok P (MT_Leaf _) = True"
| "match_tree_tests_ok P (MT_Test s arms) =
    (P s \<and> arms \<noteq> [] \<and> list_all (\<lambda>(_, t). match_tree_tests_ok P t) arms)"


subsection \<open>Elements and lengths under the column operations\<close>

lemma set_drop_at: "set (drop_at c xs) \<subseteq> set xs"
  by (induction c xs rule: drop_at.induct) auto

lemma set_replace_at: "set (replace_at c y xs) \<subseteq> insert y (set xs)"
  by (induction c y xs rule: replace_at.induct) auto

lemma set_splice_at: "set (splice_at c ys xs) \<subseteq> set ys \<union> set xs"
  by (induction c ys xs rule: splice_at.induct) auto

lemma list_all_drop_at: "list_all P xs \<Longrightarrow> list_all P (drop_at c xs)"
  using set_drop_at by (fastforce simp: list_all_iff)

lemma list_all_replace_at: "list_all P xs \<Longrightarrow> P y \<Longrightarrow> list_all P (replace_at c y xs)"
  using set_replace_at by (fastforce simp: list_all_iff)

lemma list_all_splice_at:
  "list_all P xs \<Longrightarrow> list_all P ys \<Longrightarrow> list_all P (splice_at c ys xs)"
  using set_splice_at by (fastforce simp: list_all_iff)

lemma default_row_length:
  "default_row c r = Some r' \<Longrightarrow> c < length (fst r) \<Longrightarrow> length (fst r') = length (fst r) - 1"
  by (cases r) (auto simp: length_drop_at split: CorePattern.splits)

lemma specialise_row_bool_length:
  "specialise_row_bool c h r = Some r' \<Longrightarrow> c < length (fst r)
   \<Longrightarrow> length (fst r') = length (fst r) - 1"
  by (cases r) (auto simp: length_drop_at split: CorePattern.splits if_splits)

lemma specialise_row_int_length:
  "specialise_row_int c h r = Some r' \<Longrightarrow> c < length (fst r)
   \<Longrightarrow> length (fst r') = length (fst r) - 1"
  by (cases r) (auto simp: length_drop_at split: CorePattern.splits if_splits)

lemma specialise_row_variant_length:
  "specialise_row_variant c h r = Some r' \<Longrightarrow> length (fst r') = length (fst r)"
  by (cases r) (auto simp: length_replace_at split: CorePattern.splits if_splits)

(* The rows of the matrix all have the length of the first row whenever
   first_non_wildcard_col finds a column. *)
lemma first_non_wildcard_col_same_length:
  assumes "first_non_wildcard_col rows = Some c"
  shows "\<forall>r \<in> set rows. length r = length (hd rows)"
  using assms unfolding first_non_wildcard_col_def
  by (auto simp: list_all_iff split: list.splits if_splits)

(* The first element of a map_filter comes from the list. *)
lemma hd_map_filter_member:
  assumes "List.map_filter f xs \<noteq> []"
  obtains x where "x \<in> set xs" "f x = Some (hd (List.map_filter f xs))"
  using assms map_filter_member[of "hd (List.map_filter f xs)" f xs] by auto


subsection \<open>The theorem\<close>

(* The hypothesis on the matrix (besides non-emptiness) is that its first row
   has as many columns as there are scrutinees. compile_matrix keeps this:
   the other rows have the same length as the first whenever a column is
   selected, and a record expansion is driven by the first row's pattern. *)
theorem compile_matrix_tests_ok:
  assumes P_rp: "\<And>s f. P s \<Longrightarrow> P (CoreTm_RecordProj s f)"
      and P_vp: "\<And>s h. P s \<Longrightarrow> P (CoreTm_VariantProj s h)"
  shows "snd m \<noteq> [] \<Longrightarrow> length (fst (hd (snd m))) = length (fst m)
         \<Longrightarrow> list_all P (fst m) \<Longrightarrow> match_tree_tests_ok P (compile_matrix m)"
proof (induction m rule: compile_matrix.induct)
  case (1 scruts rows)
  from "1.prems" have rows_ne: "rows \<noteq> []"
    and len_hd: "length (fst (hd rows)) = length scruts"
    and P_scruts: "list_all P scruts" by simp_all
  show ?case
  proof (cases "first_non_wildcard_col (map fst rows)")
    case None
    with rows_ne obtain r0 rs where rows_eq: "rows = r0 # rs" by (cases rows) auto
    obtain ps0 body0 where r0_eq: "r0 = (ps0, body0)" by (cases r0) auto
    from None rows_eq r0_eq show ?thesis by simp
  next
    case (Some c)
    note col_some = Some
    let ?col_pats = "map (\<lambda>(ps, _). ps ! c) rows"
    let ?nw_col_pats = "filter (\<lambda>p. \<not> is_wildcard_like p) ?col_pats"
    from col_some rows_ne have head_nw: "\<not> is_wildcard_like (fst (hd rows) ! c)"
      using first_non_wildcard_col_head_weight_pos is_wildcard_like_iff_weight_zero
      by auto
    obtain r0 rs where rows_eq: "rows = r0 # rs" using rows_ne by (cases rows) auto
    obtain ps0 body0 where r0_eq: "r0 = (ps0, body0)" by (cases r0) auto
    from rows_eq r0_eq head_nw have head_nw': "\<not> is_wildcard_like (ps0 ! c)" by simp
    hence nw_col_eq: "?nw_col_pats = (ps0 ! c) # filter (\<lambda>p. \<not> is_wildcard_like p)
                                                       (map (\<lambda>(ps, _). ps ! c) rs)"
      using rows_eq r0_eq by (simp add: case_prod_unfold)
    have col_pats_eq: "?col_pats = (ps0 ! c) # map (\<lambda>(ps, _). ps ! c) rs"
      using rows_eq r0_eq by simp
    \<comment> \<open>Lengths: every row has the length of the first row, which is the
       number of scrutinees, and c is a column of every row.\<close>
    from col_some have len_rows: "\<forall>r \<in> set rows. length (fst r) = length ps0"
      using first_non_wildcard_col_same_length[of "map fst rows" c] rows_eq r0_eq by auto
    from len_hd rows_eq r0_eq have len_ps0: "length ps0 = length scruts" by simp
    from col_some have c_lt_rows: "\<forall>r \<in> set rows. c < length (fst r)"
      by (rule first_non_wildcard_col_lengths)
    with rows_eq r0_eq have c_lt: "c < length ps0" by simp
    with len_ps0 have c_lt_s: "c < length scruts" by simp
    from P_scruts c_lt_s have P_c: "P (scruts ! c)" by (simp add: list_all_length)
    \<comment> \<open>The rows that survive a specialisation that drops column c.\<close>
    have dropped_ok:
      "match_tree_tests_ok P (compile_matrix (drop_at c scruts, rows'))"
      if ih: "rows' \<noteq> [] \<Longrightarrow> length (fst (hd rows')) = length (drop_at c scruts)
              \<Longrightarrow> list_all P (drop_at c scruts)
              \<Longrightarrow> match_tree_tests_ok P (compile_matrix (drop_at c scruts, rows'))"
      and ne: "rows' \<noteq> []"
      and len: "\<And>r'. r' \<in> set rows' \<Longrightarrow> length (fst r') = length ps0 - 1"
      for rows' :: "'body Row list"
    proof (rule ih[OF ne])
      from ne have "hd rows' \<in> set rows'" by simp
      from len[OF this] len_ps0 c_lt_s
      show "length (fst (hd rows')) = length (drop_at c scruts)"
        by (simp add: length_drop_at)
      show "list_all P (drop_at c scruts)" by (rule list_all_drop_at[OF P_scruts])
    qed
    show ?thesis
    proof (cases "head_kind_of (hd ?nw_col_pats)")
      case None
      from nw_col_eq have "hd ?nw_col_pats = ps0 ! c" by simp
      with None head_nw' head_kind_of_non_wildcard show ?thesis by (metis not_Some_eq)
    next
      case (Some hk)
      note head_kind_some = Some
      \<comment> \<open>The default arm, when present.\<close>
      have default_ok:
        "list_ex is_wildcard_like ?col_pats \<Longrightarrow>
           match_tree_tests_ok P (compile_matrix
             (drop_at c scruts, List.map_filter (default_row c) rows))"
      proof -
        assume hd: "list_ex is_wildcard_like ?col_pats"
        show ?thesis
        proof (rule dropped_ok)
          show "List.map_filter (default_row c) rows \<noteq> []"
            by (rule default_rows_nonempty[OF col_some hd])
          fix r' assume "r' \<in> set (List.map_filter (default_row c) rows)"
          then obtain r where r_in: "r \<in> set rows" and r_some: "default_row c r = Some r'"
            by (rule map_filter_member)
          from c_lt_rows r_in have "c < length (fst r)" by blast
          from default_row_length[OF r_some this] len_rows r_in
          show "length (fst r') = length ps0 - 1" by simp
        qed (rule "1.IH"(1)[OF col_some refl refl refl refl hd, simplified fst_conv snd_conv])
      qed
      have default_arm_ok:
        "list_all (\<lambda>(_, t). match_tree_tests_ok P t)
           (if list_ex is_wildcard_like ?col_pats
            then [(CorePat_Wildcard,
                   compile_matrix (drop_at c scruts, List.map_filter (default_row c) rows))]
            else [])"
        using default_ok by auto
      show ?thesis
      proof (cases hk)
        case HK_Bool
        with head_kind_some nw_col_eq obtain b where ps0_c: "ps0 ! c = CorePat_Bool b"
          by (cases "ps0 ! c") auto
        have heads_ne: "distinct_bool_heads ?col_pats \<noteq> []"
          using col_pats_eq ps0_c by simp
        have IH_heads:
          "\<And>h. h \<in> set (distinct_bool_heads ?col_pats) \<Longrightarrow>
             match_tree_tests_ok P (compile_matrix
               (drop_at c scruts, List.map_filter (specialise_row_bool c h) rows))"
        proof -
          fix h assume h_in: "h \<in> set (distinct_bool_heads ?col_pats)"
          show "match_tree_tests_ok P (compile_matrix
                  (drop_at c scruts, List.map_filter (specialise_row_bool c h) rows))"
          proof (rule dropped_ok)
            show "List.map_filter (specialise_row_bool c h) rows \<noteq> []"
              by (rule specialise_bool_rows_nonempty[OF h_in])
            fix r' assume "r' \<in> set (List.map_filter (specialise_row_bool c h) rows)"
            then obtain r where r_in: "r \<in> set rows"
              and r_some: "specialise_row_bool c h r = Some r'"
              by (rule map_filter_member)
            from c_lt_rows r_in have "c < length (fst r)" by blast
            from specialise_row_bool_length[OF r_some this] len_rows r_in
            show "length (fst r') = length ps0 - 1" by simp
          qed (rule "1.IH"(4)[OF col_some refl refl refl refl refl head_kind_some HK_Bool refl, simplified fst_conv snd_conv])
        qed
        have unfolded:
          "compile_matrix (scruts, rows) =
             MT_Test (scruts ! c)
               (map (\<lambda>h. (CorePat_Bool h,
                          compile_matrix (drop_at c scruts,
                            List.map_filter (specialise_row_bool c h) rows)))
                    (distinct_bool_heads ?col_pats)
                @ (if list_ex is_wildcard_like ?col_pats
                   then [(CorePat_Wildcard,
                          compile_matrix (drop_at c scruts,
                            List.map_filter (default_row c) rows))]
                   else []))"
          using col_some head_kind_some HK_Bool
          by (simp add: case_prod_unfold)
        have heads_ok:
          "list_all (\<lambda>(_, t). match_tree_tests_ok P t)
             (map (\<lambda>h. (CorePat_Bool h,
                        compile_matrix (drop_at c scruts,
                          List.map_filter (specialise_row_bool c h) rows)))
                  (distinct_bool_heads ?col_pats))"
          using IH_heads by (auto simp: list_all_iff)
        from unfolded heads_ok default_arm_ok heads_ne P_c show ?thesis by simp
      next
        case HK_Int
        with head_kind_some nw_col_eq obtain i where ps0_c: "ps0 ! c = CorePat_Int i"
          by (cases "ps0 ! c") auto
        have heads_ne: "distinct_int_heads ?col_pats \<noteq> []"
          using col_pats_eq ps0_c by simp
        have IH_heads:
          "\<And>h. h \<in> set (distinct_int_heads ?col_pats) \<Longrightarrow>
             match_tree_tests_ok P (compile_matrix
               (drop_at c scruts, List.map_filter (specialise_row_int c h) rows))"
        proof -
          fix h assume h_in: "h \<in> set (distinct_int_heads ?col_pats)"
          show "match_tree_tests_ok P (compile_matrix
                  (drop_at c scruts, List.map_filter (specialise_row_int c h) rows))"
          proof (rule dropped_ok)
            show "List.map_filter (specialise_row_int c h) rows \<noteq> []"
              by (rule specialise_int_rows_nonempty[OF h_in])
            fix r' assume "r' \<in> set (List.map_filter (specialise_row_int c h) rows)"
            then obtain r where r_in: "r \<in> set rows"
              and r_some: "specialise_row_int c h r = Some r'"
              by (rule map_filter_member)
            from c_lt_rows r_in have "c < length (fst r)" by blast
            from specialise_row_int_length[OF r_some this] len_rows r_in
            show "length (fst r') = length ps0 - 1" by simp
          qed (rule "1.IH"(5)[OF col_some refl refl refl refl refl head_kind_some HK_Int refl, simplified fst_conv snd_conv])
        qed
        have unfolded:
          "compile_matrix (scruts, rows) =
             MT_Test (scruts ! c)
               (map (\<lambda>h. (CorePat_Int h,
                          compile_matrix (drop_at c scruts,
                            List.map_filter (specialise_row_int c h) rows)))
                    (distinct_int_heads ?col_pats)
                @ (if list_ex is_wildcard_like ?col_pats
                   then [(CorePat_Wildcard,
                          compile_matrix (drop_at c scruts,
                            List.map_filter (default_row c) rows))]
                   else []))"
          using col_some head_kind_some HK_Int
          by (simp add: case_prod_unfold)
        have heads_ok:
          "list_all (\<lambda>(_, t). match_tree_tests_ok P t)
             (map (\<lambda>h. (CorePat_Int h,
                        compile_matrix (drop_at c scruts,
                          List.map_filter (specialise_row_int c h) rows)))
                  (distinct_int_heads ?col_pats))"
          using IH_heads by (auto simp: list_all_iff)
        from unfolded heads_ok default_arm_ok heads_ne P_c show ?thesis by simp
      next
        case HK_Variant
        with head_kind_some nw_col_eq obtain h0 p0 where ps0_c: "ps0 ! c = CorePat_Variant h0 p0"
          by (cases "ps0 ! c") auto
        have heads_ne: "distinct_variant_heads ?col_pats \<noteq> []"
          using col_pats_eq ps0_c by simp
        have IH_heads:
          "\<And>h. h \<in> set (distinct_variant_heads ?col_pats) \<Longrightarrow>
             match_tree_tests_ok P (compile_matrix
               (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                List.map_filter (specialise_row_variant c h) rows))"
        proof -
          fix h assume h_in: "h \<in> set (distinct_variant_heads ?col_pats)"
          let ?rows' = "List.map_filter (specialise_row_variant c h) rows"
          let ?scruts' = "replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts"
          have ne: "?rows' \<noteq> []" by (rule specialise_variant_rows_nonempty[OF h_in])
          have len: "length (fst (hd ?rows')) = length ?scruts'"
          proof -
            from ne obtain r where r_in: "r \<in> set rows"
              and r_some: "specialise_row_variant c h r = Some (hd ?rows')"
              by (rule hd_map_filter_member)
            from specialise_row_variant_length[OF r_some] r_in len_rows len_ps0
            show ?thesis by (simp add: length_replace_at)
          qed
          have P': "list_all P ?scruts'"
            by (rule list_all_replace_at[OF P_scruts P_vp[OF P_c]])
          show "match_tree_tests_ok P (compile_matrix (?scruts', ?rows'))"
            by (rule "1.IH"(3)[OF col_some refl refl refl refl refl head_kind_some HK_Variant
                               refl refl, simplified fst_conv snd_conv, OF ne len P'])
        qed
        have unfolded:
          "compile_matrix (scruts, rows) =
             MT_Test (scruts ! c)
               (map (\<lambda>h. (CorePat_Variant h CorePat_Wildcard,
                          compile_matrix
                            (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                             List.map_filter (specialise_row_variant c h) rows)))
                    (distinct_variant_heads ?col_pats)
                @ (if list_ex is_wildcard_like ?col_pats
                   then [(CorePat_Wildcard,
                          compile_matrix (drop_at c scruts,
                            List.map_filter (default_row c) rows))]
                   else []))"
          using col_some head_kind_some HK_Variant
          by (simp add: case_prod_unfold Let_def)
        have heads_ok:
          "list_all (\<lambda>(_, t). match_tree_tests_ok P t)
             (map (\<lambda>h. (CorePat_Variant h CorePat_Wildcard,
                        compile_matrix
                          (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                           List.map_filter (specialise_row_variant c h) rows)))
                  (distinct_variant_heads ?col_pats))"
          using IH_heads by (auto simp: list_all_iff)
        from unfolded heads_ok default_arm_ok heads_ne P_c show ?thesis by simp
      next
        case (HK_Record fld_names)
        with head_kind_some nw_col_eq obtain flds0 where ps0_c: "ps0 ! c = CorePat_Record flds0"
          and fld_names_eq: "fld_names = map fst flds0"
          by (cases "ps0 ! c") auto
        let ?scruts' = "expand_record_scruts c (scruts ! c) fld_names scruts"
        let ?rows' = "map (expand_record_row c fld_names) rows"
        have ne: "?rows' \<noteq> []" using rows_ne by simp
        have len: "length (fst (hd ?rows')) = length ?scruts'"
        proof -
          have "hd ?rows' = (splice_at c (map snd flds0) ps0, body0)"
            using rows_eq r0_eq ps0_c by simp
          thus ?thesis
            using c_lt c_lt_s len_ps0 fld_names_eq
            by (simp add: expand_record_scruts_def length_splice_at)
        qed
        have P': "list_all P ?scruts'"
          unfolding expand_record_scruts_def
          by (rule list_all_splice_at[OF P_scruts]) (auto simp: list_all_iff P_rp[OF P_c])
        have IH_record: "match_tree_tests_ok P (compile_matrix (?scruts', ?rows'))"
          by (rule "1.IH"(2)[OF col_some refl refl refl refl refl head_kind_some HK_Record,
                             simplified fst_conv snd_conv, OF ne len P'])
        have unfolded: "compile_matrix (scruts, rows) = compile_matrix (?scruts', ?rows')"
          using col_some head_kind_some HK_Record
          by (simp add: case_prod_unfold Let_def)
        from unfolded IH_record show ?thesis by simp
      qed
    qed
  qed
qed

theorem compile_match_tree_tests_ok:
  assumes "\<And>s f. P s \<Longrightarrow> P (CoreTm_RecordProj s f)"
      and "\<And>s h. P s \<Longrightarrow> P (CoreTm_VariantProj s h)"
      and "arms \<noteq> []"
      and "P scrut"
  shows "match_tree_tests_ok P (compile_match_tree scrut arms)"
  unfolding compile_match_tree_def
  by (rule compile_matrix_tests_ok[OF assms(1,2)])
     (use assms(3,4) in \<open>auto simp: neq_Nil_conv\<close>)

(* The facts about compile_match_tree that this file and the typing file use,
   restated for the type-free entry point. *)
lemma compile_match_tree_flat:
  "arms \<noteq> [] \<Longrightarrow> flat_match_tree (compile_match_tree scrut arms)"
  unfolding compile_match_tree_eq_compile_match[of scrut arms CoreTy_Bool]
  by (rule compile_match_flat)

lemma compile_match_tree_bodies_subset:
  "arms \<noteq> [] \<Longrightarrow> match_tree_bodies (compile_match_tree scrut arms) \<subseteq> set (map snd arms)"
  unfolding compile_match_tree_eq_compile_match[of scrut arms CoreTy_Bool]
  by (rule compile_match_bodies_subset)


section \<open>Flatness of the translated trees\<close>

lemma match_tree_to_term_flat:
  assumes "flat_match_tree t"
      and "match_tree_tests_ok core_term_flat t"
      and "\<And>body. body \<in> match_tree_bodies t \<Longrightarrow> core_term_flat body"
  shows "core_term_flat (match_tree_to_term t)"
  using assms
proof (induction t)
  case (MT_Leaf body)
  then show ?case by simp
next
  case (MT_Test s arms)
  have arm: "flat_pattern p \<and> core_term_flat (match_tree_to_term t)"
    if arm_in: "(p, t) \<in> set arms" for p t
  proof
    from MT_Test.prems(1) arm_in show "flat_pattern p" by (auto simp: list_all_iff)
    show "core_term_flat (match_tree_to_term t)"
    proof (rule MT_Test.IH)
      show "t \<in> Basic_BNFs.snds (p, t)" by simp
      show "(p, t) \<in> set arms" by (rule arm_in)
      from MT_Test.prems(1) arm_in show "flat_match_tree t" by (auto simp: list_all_iff)
      from MT_Test.prems(2) arm_in show "match_tree_tests_ok core_term_flat t"
        by (auto simp: list_all_iff)
      fix body assume "body \<in> match_tree_bodies t"
      with arm_in show "core_term_flat body" by (intro MT_Test.prems(3)) auto
    qed
  qed
  with MT_Test.prems(2) show ?case by (auto simp: list_all_iff)
qed

lemma match_tree_to_statements_flat:
  assumes "flat_match_tree t"
      and "match_tree_tests_ok core_term_flat t"
      and "\<And>body. body \<in> match_tree_bodies t \<Longrightarrow> core_statement_list_flat body"
  shows "core_statement_list_flat (match_tree_to_statements g t)"
  using assms
proof (induction t)
  case (MT_Leaf body)
  then show ?case by simp
next
  case (MT_Test s arms)
  have arm: "flat_pattern p \<and> core_statement_list_flat (match_tree_to_statements g t)"
    if arm_in: "(p, t) \<in> set arms" for p t
  proof
    from MT_Test.prems(1) arm_in show "flat_pattern p" by (auto simp: list_all_iff)
    show "core_statement_list_flat (match_tree_to_statements g t)"
    proof (rule MT_Test.IH)
      show "t \<in> Basic_BNFs.snds (p, t)" by simp
      show "(p, t) \<in> set arms" by (rule arm_in)
      from MT_Test.prems(1) arm_in show "flat_match_tree t" by (auto simp: list_all_iff)
      from MT_Test.prems(2) arm_in show "match_tree_tests_ok core_term_flat t"
        by (auto simp: list_all_iff)
      fix body assume "body \<in> match_tree_bodies t"
      with arm_in show "core_statement_list_flat body" by (intro MT_Test.prems(3)) auto
    qed
  qed
  with MT_Test.prems(2) show ?case by (auto simp: list_all_iff)
qed

lemma compile_match_term_flat:
  assumes "arms \<noteq> []"
      and "core_term_flat scrut"
      and "\<And>p body. (p, body) \<in> set arms \<Longrightarrow> core_term_flat body"
  shows "core_term_flat (compile_match_term scrut arms)"
  unfolding compile_match_term_def
proof (rule match_tree_to_term_flat)
  show "flat_match_tree (compile_match_tree scrut arms)"
    by (rule compile_match_tree_flat[OF assms(1)])
  show "match_tree_tests_ok core_term_flat (compile_match_tree scrut arms)"
    by (rule compile_match_tree_tests_ok[where P = core_term_flat]) (simp_all add: assms(1,2))
  fix body assume "body \<in> match_tree_bodies (compile_match_tree scrut arms)"
  with compile_match_tree_bodies_subset[OF assms(1)] have "body \<in> set (map snd arms)" by blast
  thus "core_term_flat body" using assms(3) by auto
qed

lemma compile_match_statement_flat:
  assumes "arms \<noteq> []"
      and "core_term_flat scrut"
      and "\<And>p body. (p, body) \<in> set arms \<Longrightarrow> core_statement_list_flat body"
  shows "core_statement_list_flat (compile_match_statement g scrut arms)"
proof -
  have flat: "flat_match_tree (compile_match_tree scrut arms)"
    by (rule compile_match_tree_flat[OF assms(1)])
  have tests: "match_tree_tests_ok core_term_flat (compile_match_tree scrut arms)"
    by (rule compile_match_tree_tests_ok[where P = core_term_flat]) (simp_all add: assms(1,2))
  have bodies: "core_statement_list_flat body"
    if "body \<in> match_tree_bodies (compile_match_tree scrut arms)" for body
  proof -
    from that compile_match_tree_bodies_subset[OF assms(1)]
    have "body \<in> set (map snd arms)" by blast
    thus ?thesis using assms(3) by auto
  qed
  show ?thesis
  proof (cases "compile_match_tree scrut arms")
    case (MT_Leaf body)
    with bodies[of body] assms(2) show ?thesis
      by (simp add: compile_match_statement_def)
  next
    case (MT_Test s arms')
    have "core_statement_list_flat
            (match_tree_to_statements g (compile_match_tree scrut arms))"
      by (rule match_tree_to_statements_flat[OF flat tests]) (rule bodies)
    thus ?thesis unfolding compile_match_statement_def MT_Test by simp
  qed
qed


section \<open>Flatness of the pass\<close>

(* Every term is compiled to a flat term. *)
theorem match_compile_term_flat:
  "core_term_flat (match_compile_term tm)"
proof (induction tm)
  case (CoreTm_Match scrut arms)
  let ?arms' = "map (\<lambda>(p, b). (p, match_compile_term b)) arms"
  have bodies: "core_term_flat (match_compile_term b)" if "(p, b) \<in> set arms" for p b
    using CoreTm_Match.IH(2)[OF that, of b] by simp
  show ?case
  proof (cases "arms_flat arms")
    case True
    with CoreTm_Match.IH(1) bodies show ?thesis
      by (auto simp: arms_flat_def list_all_iff)
  next
    case False
    hence ne: "?arms' \<noteq> []" by (auto simp: arms_flat_def)
    have "core_term_flat (compile_match_term (match_compile_term scrut) ?arms')"
      by (rule compile_match_term_flat[OF ne CoreTm_Match.IH(1)]) (use bodies in auto)
    with False show ?thesis by simp
  qed
qed (auto simp: list_all_iff)

(* Lifting a per-statement fact to statement lists. *)
lemma match_compile_statement_list_flat_aux:
  assumes "\<And>stmt. stmt \<in> set stmts \<Longrightarrow> core_statement_ghost_free stmt
             \<Longrightarrow> core_statement_list_flat (match_compile_statement stmt)"
      and "core_statement_list_ghost_free stmts"
  shows "core_statement_list_flat (match_compile_statement_list stmts)"
  using assms by (induction stmts) simp_all

(* A ghost-free statement is compiled to flat statements. *)
theorem match_compile_statement_flat:
  "core_statement_ghost_free stmt \<Longrightarrow> core_statement_list_flat (match_compile_statement stmt)"
proof (induction stmt)
  case (CoreStmt_While g condTm invars decrTm body)
  have b: "core_statement_list_flat (match_compile_statement_list body)"
  proof (rule match_compile_statement_list_flat_aux)
    fix s assume s_in: "s \<in> set body"
    show "core_statement_ghost_free s \<Longrightarrow> core_statement_list_flat (match_compile_statement s)"
      by (rule CoreStmt_While.IH[OF s_in])
  next
    from CoreStmt_While.prems show "core_statement_list_ghost_free body" by simp
  qed
  show ?case using b by (auto simp: list_all_iff match_compile_term_flat split: option.splits)
next
  case (CoreStmt_Match g scrut arms)
  let ?arms' = "map (\<lambda>(p, body). (p, match_compile_statement_list body)) arms"
  have bodies: "core_statement_list_flat (match_compile_statement_list body)"
    if arm_in: "(p, body) \<in> set arms" for p body
  proof (rule match_compile_statement_list_flat_aux)
    fix s assume s_in: "s \<in> set body"
    have sn: "body \<in> Basic_BNFs.snds (p, body)" by simp
    show "core_statement_ghost_free s \<Longrightarrow> core_statement_list_flat (match_compile_statement s)"
      by (rule CoreStmt_Match.IH[OF arm_in sn s_in])
  next
    from CoreStmt_Match.prems arm_in show "core_statement_list_ghost_free body"
      by (auto simp: list_all_iff)
  qed
  show ?case
  proof (cases "arms_flat arms")
    case True
    with bodies show ?thesis
      by (auto simp: arms_flat_def list_all_iff match_compile_term_flat)
  next
    case False
    hence ne: "?arms' \<noteq> []" by (auto simp: arms_flat_def)
    have "core_statement_list_flat
            (compile_match_statement g (match_compile_term scrut) ?arms')"
      by (rule compile_match_statement_flat[OF ne match_compile_term_flat])
         (use bodies in auto)
    with False show ?thesis by simp
  qed
next
  case (CoreStmt_Block body)
  have b: "core_statement_list_flat (match_compile_statement_list body)"
  proof (rule match_compile_statement_list_flat_aux)
    fix s assume s_in: "s \<in> set body"
    show "core_statement_ghost_free s \<Longrightarrow> core_statement_list_flat (match_compile_statement s)"
      by (rule CoreStmt_Block.IH[OF s_in])
  next
    from CoreStmt_Block.prems show "core_statement_list_ghost_free body" by simp
  qed
  show ?case using b by simp
qed (auto simp: list_all_iff match_compile_term_flat)

theorem match_compile_statement_list_flat:
  "core_statement_list_ghost_free stmts
   \<Longrightarrow> core_statement_list_flat (match_compile_statement_list stmts)"
  by (rule match_compile_statement_list_flat_aux) (rule match_compile_statement_flat)

(* A ghost-free module is compiled to a flat module. *)
theorem match_compile_module_flat:
  assumes "core_module_ghost_free m"
  shows "core_module_flat (match_compile_module m)"
  unfolding core_module_flat_iff
proof (intro allI impI, elim conjE)
  fix name f body
  assume lk: "fmlookup (CM_Functions (match_compile_module m)) name = Some f"
    and b: "CF_Body f = Some body"
  from lk obtain f0 where lk0: "fmlookup (CM_Functions m) name = Some f0"
    and f: "f = match_compile_function f0"
    by (auto simp: match_compile_module_fun_lookup)
  from b f obtain body0 where b0: "CF_Body f0 = Some body0"
    and body: "body = match_compile_statement_list body0"
    by auto
  from assms lk0 b0 have "core_statement_list_ghost_free body0"
    unfolding core_module_ghost_free_def by blast
  thus "core_statement_list_flat body"
    unfolding body by (rule match_compile_statement_list_flat)
qed


section \<open>Ghost-freeness and closedness are preserved\<close>

lemma match_tree_to_statements_ghost_free:
  assumes "\<And>body. body \<in> match_tree_bodies t \<Longrightarrow> core_statement_list_ghost_free body"
  shows "core_statement_list_ghost_free (match_tree_to_statements NotGhost t)"
  using assms
proof (induction t)
  case (MT_Leaf body)
  then show ?case by simp
next
  case (MT_Test s arms)
  have "core_statement_list_ghost_free (match_tree_to_statements NotGhost t)"
    if arm_in: "(p, t) \<in> set arms" for p t
  proof (rule MT_Test.IH)
    show "t \<in> Basic_BNFs.snds (p, t)" by simp
    show "(p, t) \<in> set arms" by (rule arm_in)
    fix body assume "body \<in> match_tree_bodies t"
    with arm_in show "core_statement_list_ghost_free body" by (intro MT_Test.prems) auto
  qed
  then show ?case by (auto simp: list_all_iff)
qed

lemma compile_match_statement_ghost_free:
  assumes "arms \<noteq> []"
      and "\<And>p body. (p, body) \<in> set arms \<Longrightarrow> core_statement_list_ghost_free body"
  shows "core_statement_list_ghost_free (compile_match_statement NotGhost scrut arms)"
proof -
  have bodies: "core_statement_list_ghost_free body"
    if "body \<in> match_tree_bodies (compile_match_tree scrut arms)" for body
  proof -
    from that compile_match_tree_bodies_subset[OF assms(1)]
    have "body \<in> set (map snd arms)" by blast
    thus ?thesis using assms(2) by auto
  qed
  show ?thesis
  proof (cases "compile_match_tree scrut arms")
    case (MT_Leaf body)
    with bodies[of body] show ?thesis by (simp add: compile_match_statement_def)
  next
    case (MT_Test s arms')
    have "core_statement_list_ghost_free
            (match_tree_to_statements NotGhost (compile_match_tree scrut arms))"
      by (rule match_tree_to_statements_ghost_free) (rule bodies)
    thus ?thesis unfolding compile_match_statement_def MT_Test by simp
  qed
qed

lemma match_compile_statement_list_ghost_free_aux:
  assumes "\<And>stmt. stmt \<in> set stmts \<Longrightarrow> core_statement_ghost_free stmt
             \<Longrightarrow> core_statement_list_ghost_free (match_compile_statement stmt)"
      and "core_statement_list_ghost_free stmts"
  shows "core_statement_list_ghost_free (match_compile_statement_list stmts)"
  using assms by (induction stmts) (simp_all add: core_statement_list_ghost_free_append)

theorem match_compile_statement_ghost_free:
  "core_statement_ghost_free stmt
   \<Longrightarrow> core_statement_list_ghost_free (match_compile_statement stmt)"
proof (induction stmt)
  case (CoreStmt_While g condTm invars decrTm body)
  have b: "core_statement_list_ghost_free (match_compile_statement_list body)"
  proof (rule match_compile_statement_list_ghost_free_aux)
    fix s assume s_in: "s \<in> set body"
    show "core_statement_ghost_free s
          \<Longrightarrow> core_statement_list_ghost_free (match_compile_statement s)"
      by (rule CoreStmt_While.IH[OF s_in])
  next
    from CoreStmt_While.prems show "core_statement_list_ghost_free body" by simp
  qed
  show ?case using CoreStmt_While.prems b by simp
next
  case (CoreStmt_Match g scrut arms)
  let ?arms' = "map (\<lambda>(p, body). (p, match_compile_statement_list body)) arms"
  from CoreStmt_Match.prems have g: "g = NotGhost" by simp
  have bodies: "core_statement_list_ghost_free (match_compile_statement_list body)"
    if arm_in: "(p, body) \<in> set arms" for p body
  proof (rule match_compile_statement_list_ghost_free_aux)
    fix s assume s_in: "s \<in> set body"
    have sn: "body \<in> Basic_BNFs.snds (p, body)" by simp
    show "core_statement_ghost_free s
          \<Longrightarrow> core_statement_list_ghost_free (match_compile_statement s)"
      by (rule CoreStmt_Match.IH[OF arm_in sn s_in])
  next
    from CoreStmt_Match.prems arm_in show "core_statement_list_ghost_free body"
      by (auto simp: list_all_iff)
  qed
  show ?case
  proof (cases "arms_flat arms")
    case True
    with bodies g show ?thesis by (auto simp: list_all_iff)
  next
    case False
    hence ne: "?arms' \<noteq> []" by (auto simp: arms_flat_def)
    have "core_statement_list_ghost_free
            (compile_match_statement NotGhost (match_compile_term scrut) ?arms')"
      by (rule compile_match_statement_ghost_free[OF ne]) (use bodies in auto)
    with False g show ?thesis by simp
  qed
next
  case (CoreStmt_Block body)
  have b: "core_statement_list_ghost_free (match_compile_statement_list body)"
  proof (rule match_compile_statement_list_ghost_free_aux)
    fix s assume s_in: "s \<in> set body"
    show "core_statement_ghost_free s
          \<Longrightarrow> core_statement_list_ghost_free (match_compile_statement s)"
      by (rule CoreStmt_Block.IH[OF s_in])
  next
    from CoreStmt_Block.prems show "core_statement_list_ghost_free body" by simp
  qed
  show ?case using b by simp
qed simp_all

theorem match_compile_statement_list_ghost_free:
  "core_statement_list_ghost_free stmts
   \<Longrightarrow> core_statement_list_ghost_free (match_compile_statement_list stmts)"
  by (rule match_compile_statement_list_ghost_free_aux)
     (rule match_compile_statement_ghost_free)

theorem match_compile_module_ghost_free:
  assumes "core_module_ghost_free m"
  shows "core_module_ghost_free (match_compile_module m)"
proof -
  have bodies: "core_statement_list_ghost_free body"
    if lk: "fmlookup (CM_Functions (match_compile_module m)) name = Some f"
      and b: "CF_Body f = Some body" for name f body
  proof -
    from lk obtain f0 where lk0: "fmlookup (CM_Functions m) name = Some f0"
      and f: "f = match_compile_function f0"
      by (auto simp: match_compile_module_fun_lookup)
    from b f obtain body0 where b0: "CF_Body f0 = Some body0"
      and body: "body = match_compile_statement_list body0"
      by auto
    from assms lk0 b0 have "core_statement_list_ghost_free body0"
      unfolding core_module_ghost_free_def by blast
    thus ?thesis unfolding body by (rule match_compile_statement_list_ghost_free)
  qed
  from assms show ?thesis
    unfolding core_module_ghost_free_def match_compile_module_simps(1)
    using bodies by blast
qed

theorem match_compile_module_closed:
  "core_module_closed (match_compile_module m) = core_module_closed m"
  by (simp add: core_module_closed_def)

end
