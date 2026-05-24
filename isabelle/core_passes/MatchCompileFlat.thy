theory MatchCompileFlat
  imports MatchCompile
begin

(* Flat-pattern guarantee for the match-compilation pass.

   The pass eliminates nested patterns: in its output, every pattern
   inside an MT_Test arm satisfies `flat_pattern` (see CoreSyntax).
   Downstream consumers (code generation, the type-preservation proof
   in MatchCompileTyping) may rely on this property. *)


section \<open>Flatness predicate on MatchTree\<close>

(* A MatchTree is "flat" if every pattern appearing in an MT_Test arm
   satisfies `flat_pattern`. MT_Leaf is flat trivially. *)
fun flat_match_tree :: "'body MatchTree \<Rightarrow> bool" where
  "flat_match_tree (MT_Leaf _) = True"
| "flat_match_tree (MT_Test _ arms) =
    list_all (\<lambda>(p, t). flat_pattern p \<and> flat_match_tree t) arms"


section \<open>Distinct heads come from the source list\<close>

(* The distinct_*_heads functions extract head values that actually
   appear in the input column. We need this to know that some row
   matches each enumerated head, hence survives specialisation. *)

lemma distinct_bool_heads_subset:
  "h \<in> set (distinct_bool_heads xs) \<Longrightarrow> CorePat_Bool h \<in> set xs"
proof (induction xs rule: distinct_bool_heads.induct)
  case (2 b rest)
  show ?case
  proof (cases "h = b")
    case True thus ?thesis by simp
  next
    case False
    with "2.prems" have "h \<in> set (distinct_bool_heads (filter (\<lambda>p. p \<noteq> CorePat_Bool b) rest))"
      by simp
    with "2.IH" have "CorePat_Bool h \<in> set (filter (\<lambda>p. p \<noteq> CorePat_Bool b) rest)" by auto
    thus ?thesis by auto
  qed
qed (auto split: CorePattern.splits)

lemma distinct_int_heads_subset:
  "h \<in> set (distinct_int_heads xs) \<Longrightarrow> CorePat_Int h \<in> set xs"
proof (induction xs rule: distinct_int_heads.induct)
  case (2 i rest)
  show ?case
  proof (cases "h = i")
    case True thus ?thesis by simp
  next
    case False
    with "2.prems" have "h \<in> set (distinct_int_heads (filter (\<lambda>p. p \<noteq> CorePat_Int i) rest))"
      by simp
    with "2.IH" have "CorePat_Int h \<in> set (filter (\<lambda>p. p \<noteq> CorePat_Int i) rest)" by simp
    thus ?thesis by auto
  qed
qed (auto split: CorePattern.splits)

lemma distinct_variant_heads_subset:
  "h \<in> set (distinct_variant_heads xs) \<Longrightarrow> \<exists>p. CorePat_Variant h p \<in> set xs"
proof (induction xs rule: distinct_variant_heads.induct)
  case (2 h' pl rest)
  show ?case
  proof (cases "h = h'")
    case True thus ?thesis by auto
  next
    case False
    with "2.prems" have
      "h \<in> set (distinct_variant_heads
                  (filter (\<lambda>p. case p of CorePat_Variant h'' _ \<Rightarrow> h'' \<noteq> h' | _ \<Rightarrow> True) rest))"
      by simp
    with "2.IH" have
      "\<exists>p. CorePat_Variant h p \<in> set (filter (\<lambda>p. case p of CorePat_Variant h'' _ \<Rightarrow> h'' \<noteq> h' | _ \<Rightarrow> True) rest)"
      by simp
    thus ?thesis by auto
  qed
qed (auto split: CorePattern.splits)


section \<open>Non-emptiness preserved by recursive calls\<close>

(* compile_matrix only recurses on non-empty matrices when called from
   a non-empty matrix. Each helper shows that the matrix passed to a
   recursive call is non-empty, given the preconditions that hold at
   the call site. *)

(* A row that maps to Some under f contributes a value to the
   List.map_filter result, so the result is non-empty. *)
lemma map_filter_nonempty:
  assumes "r \<in> set xs" and "f r = Some y"
  shows "List.map_filter f xs \<noteq> []"
  using assms
  by (induction xs) (auto simp: List.map_filter_simps split: option.splits)

lemma default_rows_nonempty:
  assumes col_some: "first_non_wildcard_col (map fst rows) = Some c"
      and has_default: "list_ex is_wildcard_like
                          (map (\<lambda>(ps, _). ps ! c) rows)"
  shows "List.map_filter (default_row c) rows \<noteq> []"
proof -
  from has_default obtain r where r_in: "r \<in> set rows"
      and wc: "is_wildcard_like ((\<lambda>(ps, _). ps ! c) r)"
    by (auto simp: list_ex_iff)
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  with wc have wc': "is_wildcard_like (ps ! c)" by simp
  hence "ps ! c = CorePat_Wildcard" by (cases "ps ! c") auto
  hence "default_row c r = Some (drop_at c ps, body)" using r_eq by simp
  with r_in show ?thesis by (rule map_filter_nonempty)
qed

lemma specialise_bool_rows_nonempty:
  assumes h_in: "h \<in> set (distinct_bool_heads
                             (map (\<lambda>(ps, _). ps ! c) rows))"
  shows "List.map_filter (specialise_row_bool c h) rows \<noteq> []"
proof -
  from h_in distinct_bool_heads_subset have
    "CorePat_Bool h \<in> set (map (\<lambda>(ps, _). ps ! c) rows)" by blast
  then obtain r where r_in: "r \<in> set rows"
                  and r_eq: "(\<lambda>(ps, _). ps ! c) r = CorePat_Bool h"
    by auto
  obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
  with r_eq have "ps ! c = CorePat_Bool h" by simp
  hence "specialise_row_bool c h r = Some (drop_at c ps, body)"
    using r_split by simp
  with r_in show ?thesis by (rule map_filter_nonempty)
qed

lemma specialise_int_rows_nonempty:
  assumes h_in: "h \<in> set (distinct_int_heads
                             (map (\<lambda>(ps, _). ps ! c) rows))"
  shows "List.map_filter (specialise_row_int c h) rows \<noteq> []"
proof -
  from h_in distinct_int_heads_subset have
    "CorePat_Int h \<in> set (map (\<lambda>(ps, _). ps ! c) rows)" by blast
  then obtain r where r_in: "r \<in> set rows"
                  and r_eq: "(\<lambda>(ps, _). ps ! c) r = CorePat_Int h"
    by auto
  obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
  with r_eq have "ps ! c = CorePat_Int h" by simp
  hence "specialise_row_int c h r = Some (drop_at c ps, body)"
    using r_split by simp
  with r_in show ?thesis by (rule map_filter_nonempty)
qed

lemma specialise_variant_rows_nonempty:
  assumes h_in: "h \<in> set (distinct_variant_heads
                             (map (\<lambda>(ps, _). ps ! c) rows))"
  shows "List.map_filter (specialise_row_variant c h) rows \<noteq> []"
proof -
  from h_in distinct_variant_heads_subset obtain p where
    "CorePat_Variant h p \<in> set (map (\<lambda>(ps, _). ps ! c) rows)" by blast
  then obtain r where r_in: "r \<in> set rows"
                  and r_eq: "(\<lambda>(ps, _). ps ! c) r = CorePat_Variant h p"
    by auto
  obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
  with r_eq have "ps ! c = CorePat_Variant h p" by simp
  hence "specialise_row_variant c h r = Some (replace_at c p ps, body)"
    using r_split by simp
  with r_in show ?thesis by (rule map_filter_nonempty)
qed

lemma expand_record_rows_nonempty:
  "rows \<noteq> [] \<Longrightarrow> map (expand_record_row c fld_names) rows \<noteq> []"
  by simp

lemma head_kind_of_non_wildcard:
  "\<not> is_wildcard_like p \<Longrightarrow> \<exists>k. head_kind_of p = Some k"
  by (cases p) auto


section \<open>compile_matrix produces a flat tree\<close>

theorem compile_matrix_flat:
  "snd m \<noteq> [] \<Longrightarrow> flat_match_tree (compile_matrix m)"
proof (induction m rule: compile_matrix.induct)
  case (1 scruts rows)
  from "1.prems" have rows_ne: "rows \<noteq> []" by simp
  show ?case
  proof (cases "first_non_wildcard_col (map fst rows)")
    case None
    with rows_ne obtain r0 rs where rows_eq: "rows = r0 # rs" by (cases rows) auto
    obtain ps0 body0 where r0_eq: "r0 = (ps0, body0)" by (cases r0) auto
    from None rows_eq r0_eq show ?thesis by simp
  next
    case (Some c)
    let ?col_pats = "map (\<lambda>(ps, _). ps ! c) rows"
    let ?nw_col_pats = "filter (\<lambda>p. \<not> is_wildcard_like p) ?col_pats"
    (* Head row contributes a non-wildcard to ?nw_col_pats, so it is
       non-empty and its head is a non-wildcard pattern. *)
    from Some rows_ne have head_nw: "\<not> is_wildcard_like (fst (hd rows) ! c)"
      using first_non_wildcard_col_head_weight_pos
            is_wildcard_like_iff_weight_zero
      by auto
    obtain r0 rs where rows_eq: "rows = r0 # rs" using rows_ne by (cases rows) auto
    obtain ps0 body0 where r0_eq: "r0 = (ps0, body0)" by (cases r0) auto
    from rows_eq r0_eq head_nw have head_nw': "\<not> is_wildcard_like (ps0 ! c)" by simp
    hence nw_col_eq: "?nw_col_pats = (ps0 ! c) # filter (\<lambda>p. \<not> is_wildcard_like p)
                                                       (map (\<lambda>(ps, _). ps ! c) rs)"
      using rows_eq r0_eq by (simp add: case_prod_unfold)
    show ?thesis
    proof (cases "head_kind_of (hd ?nw_col_pats)")
      case None
      from nw_col_eq have "hd ?nw_col_pats = ps0 ! c" by simp
      with None head_nw' head_kind_of_non_wildcard show ?thesis by (metis not_Some_eq)
    next
      case (Some hk)
      have col_some: "first_non_wildcard_col (map fst rows) = Some c"
        using \<open>first_non_wildcard_col (map fst rows) = Some c\<close> .
      from Some have head_kind_some:
        "head_kind_of (hd ?nw_col_pats) = Some hk" .
      show ?thesis
      proof (cases hk)
        case HK_Bool
        have IH_default:
          "list_ex is_wildcard_like ?col_pats \<Longrightarrow>
             flat_match_tree (compile_matrix
               (drop_at c scruts, List.map_filter (default_row c) rows))"
          using "1.IH"(1)[OF col_some]
                default_rows_nonempty[OF col_some]
          by auto
        have IH_heads:
          "\<And>h. h \<in> set (distinct_bool_heads ?col_pats) \<Longrightarrow>
             flat_match_tree (compile_matrix
               (drop_at c scruts,
                List.map_filter (specialise_row_bool c h) rows))"
          using "1.IH"(2)[OF col_some] head_kind_some HK_Bool
                specialise_bool_rows_nonempty
          by (metis "1.IH"(4) col_some snd_conv)
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
        have heads_flat:
          "list_all (\<lambda>(p, t). flat_pattern p \<and> flat_match_tree t)
             (map (\<lambda>h. (CorePat_Bool h,
                        compile_matrix (drop_at c scruts,
                          List.map_filter (specialise_row_bool c h) rows)))
                  (distinct_bool_heads ?col_pats))"
          using IH_heads by (auto simp: list_all_iff)
        have default_flat:
          "list_all (\<lambda>(p, t). flat_pattern p \<and> flat_match_tree t)
             (if list_ex is_wildcard_like ?col_pats
              then [(CorePat_Wildcard,
                     compile_matrix (drop_at c scruts,
                       List.map_filter (default_row c) rows))]
              else [])"
          using IH_default by auto
        from unfolded heads_flat default_flat show ?thesis by simp
      next
        case HK_Int
        have IH_default:
          "list_ex is_wildcard_like ?col_pats \<Longrightarrow>
             flat_match_tree (compile_matrix
               (drop_at c scruts, List.map_filter (default_row c) rows))"
          using "1.IH"(1)[OF col_some]
                default_rows_nonempty[OF col_some]
          by auto
        have IH_heads:
          "\<And>h. h \<in> set (distinct_int_heads ?col_pats) \<Longrightarrow>
             flat_match_tree (compile_matrix
               (drop_at c scruts,
                List.map_filter (specialise_row_int c h) rows))"
          using "1.IH"(3)[OF col_some] head_kind_some HK_Int
                specialise_int_rows_nonempty
          by (metis "1.IH"(5) col_some snd_conv)
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
        have heads_flat:
          "list_all (\<lambda>(p, t). flat_pattern p \<and> flat_match_tree t)
             (map (\<lambda>h. (CorePat_Int h,
                        compile_matrix (drop_at c scruts,
                          List.map_filter (specialise_row_int c h) rows)))
                  (distinct_int_heads ?col_pats))"
          using IH_heads by (auto simp: list_all_iff)
        have default_flat:
          "list_all (\<lambda>(p, t). flat_pattern p \<and> flat_match_tree t)
             (if list_ex is_wildcard_like ?col_pats
              then [(CorePat_Wildcard,
                     compile_matrix (drop_at c scruts,
                       List.map_filter (default_row c) rows))]
              else [])"
          using IH_default by auto
        from unfolded heads_flat default_flat show ?thesis by simp
      next
        case HK_Variant
        have IH_default:
          "list_ex is_wildcard_like ?col_pats \<Longrightarrow>
             flat_match_tree (compile_matrix
               (drop_at c scruts, List.map_filter (default_row c) rows))"
          using "1.IH"(1)[OF col_some]
                default_rows_nonempty[OF col_some]
          by auto
        have IH_heads:
          "\<And>h. h \<in> set (distinct_variant_heads ?col_pats) \<Longrightarrow>
             flat_match_tree (compile_matrix
               (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                List.map_filter (specialise_row_variant c h) rows))"
          using "1.IH"(4)[OF col_some] head_kind_some HK_Variant
                specialise_variant_rows_nonempty
          by (metis "1.IH"(3) col_some snd_conv)
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
        have heads_flat:
          "list_all (\<lambda>(p, t). flat_pattern p \<and> flat_match_tree t)
             (map (\<lambda>h. (CorePat_Variant h CorePat_Wildcard,
                        compile_matrix
                          (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                           List.map_filter (specialise_row_variant c h) rows)))
                  (distinct_variant_heads ?col_pats))"
          using IH_heads by (auto simp: list_all_iff)
        have default_flat:
          "list_all (\<lambda>(p, t). flat_pattern p \<and> flat_match_tree t)
             (if list_ex is_wildcard_like ?col_pats
              then [(CorePat_Wildcard,
                     compile_matrix (drop_at c scruts,
                       List.map_filter (default_row c) rows))]
              else [])"
          using IH_default by auto
        from unfolded heads_flat default_flat show ?thesis by simp
      next
        case (HK_Record fld_names)
        have IH_record:
          "flat_match_tree (compile_matrix
              (expand_record_scruts c (scruts ! c) fld_names scruts,
               map (expand_record_row c fld_names) rows))"
          using "1.IH"(5)[OF col_some] head_kind_some HK_Record rows_ne
          by (metis "1.IH"(2) col_some expand_record_rows_nonempty snd_conv)
        have unfolded:
          "compile_matrix (scruts, rows) =
             compile_matrix
               (expand_record_scruts c (scruts ! c) fld_names scruts,
                map (expand_record_row c fld_names) rows)"
          using col_some head_kind_some HK_Record
          by (simp add: case_prod_unfold Let_def)
        from unfolded IH_record show ?thesis by simp
      qed
    qed
  qed
qed


section \<open>compile_match produces a flat tree\<close>

theorem compile_match_flat:
  assumes "arms \<noteq> []"
  shows "flat_match_tree (compile_match scrut scrutTy arms)"
proof -
  let ?m = "([scrut], map (\<lambda>(p, b). ([p], b)) arms)"
  from assms have "snd ?m \<noteq> []" by simp
  hence "flat_match_tree (compile_matrix ?m)" by (rule compile_matrix_flat)
  thus ?thesis by (simp add: compile_match_def)
qed

end
