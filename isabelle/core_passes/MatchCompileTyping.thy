theory MatchCompileTyping
  imports MatchCompileFlat "../core/CoreTypecheck"
begin

(* Type-preservation results for the Core-to-Core match-compilation pass.

   The pass is polymorphic in the arm body type 'body, so we factor the
   typing guarantee into two body-type-independent properties:

   (1) bodies_subset: every body that appears in the output MatchTree
       was present in the input arm list. A downstream consumer that
       wants "every output body is well-typed at type ty" instantiates
       this with the input well-typedness.

   (2) arm_patterns_compatible: every internal MT_Test scrutinee
       type-checks in the ambient env, and every test pattern is
       pattern_compatible with its scrutinee's type.

   Together these are enough for a consumer to reconstruct
   well-typedness of the lowered match without this file needing to
   know anything about how 'body is typed. *)


section \<open>Bodies appearing in a MatchTree\<close>

fun match_tree_bodies :: "'body MatchTree \<Rightarrow> 'body set" where
  "match_tree_bodies (MT_Leaf b) = {b}"
| "match_tree_bodies (MT_Test _ arms) =
     (\<Union>(_, t) \<in> set arms. match_tree_bodies t)"


section \<open>Arm pattern compatibility\<close>

fun arm_patterns_compatible ::
  "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> 'body MatchTree \<Rightarrow> bool"
where
  "arm_patterns_compatible env g (MT_Leaf _) = True"
| "arm_patterns_compatible env g (MT_Test s arms) =
     (case core_term_type env g s of
        None \<Rightarrow> False
      | Some sTy \<Rightarrow>
          list_all (\<lambda>(p, t).
                pattern_compatible env p sTy
              \<and> arm_patterns_compatible env g t)
            arms)"


section \<open>Matrix typing invariant\<close>

(* Each column has a CoreType; the scrutinee at that column types as
   that CoreType; every row's pattern at that column is compatible
   with that CoreType; and every column type is well-kinded.
   Well-kindedness is needed to discharge the record-column case in
   the type-preservation proof, because pattern_compatible looks up
   field types via map_of, which only agrees with positional lookup
   under distinct field names — and is_well_kinded enforces that for
   CoreTy_Record. The matrix may have any number of rows. *)
definition matrix_inv ::
  "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> CoreType list \<Rightarrow> 'body MatchMatrix \<Rightarrow> bool"
where
  "matrix_inv env g colTys m \<longleftrightarrow>
     length (fst m) = length colTys
   \<and> list_all2 (\<lambda>s ty. core_term_type env g s = Some ty) (fst m) colTys
   \<and> list_all (is_well_kinded env) colTys
   \<and> list_all (\<lambda>(ps, _).
         length ps = length colTys
       \<and> list_all2 (pattern_compatible env) ps colTys)
       (snd m)"


subsection \<open>Well-kindedness propagation through column plumbing\<close>

lemma list_all_drop_at:
  "list_all P xs \<Longrightarrow> list_all P (drop_at c xs)"
  by (induction c xs rule: drop_at.induct) auto

lemma list_all_replace_at:
  "list_all P xs \<Longrightarrow> (c < length xs \<Longrightarrow> P y) \<Longrightarrow> list_all P (replace_at c y xs)"
  by (induction c y xs rule: replace_at.induct) auto

lemma list_all_splice_at:
  "list_all P xs \<Longrightarrow> list_all P ys \<Longrightarrow> list_all P (splice_at c ys xs)"
  by (induction c ys xs rule: splice_at.induct) auto


section \<open>List arithmetic for column plumbing\<close>

lemma list_all2_drop_at:
  assumes "list_all2 P xs ys"
  shows   "list_all2 P (drop_at c xs) (drop_at c ys)"
  using assms
proof (induction c xs arbitrary: ys rule: drop_at.induct)
  case (1 c) thus ?case by simp
next
  case (2 x xs)
  then obtain y ys' where ys_eq: "ys = y # ys'" "P x y" "list_all2 P xs ys'"
    by (metis list_all2_Cons1)
  thus ?case by simp
next
  case (3 c x xs)
  then obtain y ys' where ys_eq: "ys = y # ys'" "P x y" "list_all2 P xs ys'"
    by (metis list_all2_Cons1)
  thus ?case using 3 by simp
qed

lemma length_drop_at:
  "length (drop_at c xs) = (if c < length xs then length xs - 1 else length xs)"
  by (induction c xs rule: drop_at.induct) auto

lemma length_replace_at:
  "length (replace_at c y xs) = length xs"
  by (induction c y xs rule: replace_at.induct) auto

lemma length_splice_at:
  "length (splice_at c ys xs) =
     (if c < length xs then length xs - 1 + length ys else length xs)"
  by (induction c ys xs rule: splice_at.induct) auto

lemma list_all2_replace_at:
  assumes "list_all2 P xs ys"
  assumes "c < length xs \<Longrightarrow> P x' (ys ! c)"
  shows   "list_all2 P (replace_at c x' xs) ys"
  using assms
proof (induction c x' xs arbitrary: ys rule: replace_at.induct)
  case (1 c y) thus ?case by simp
next
  case (2 y x xs)
  then obtain z ys' where ys_eq: "ys = z # ys'" "P x z" "list_all2 P xs ys'"
    by (metis list_all2_Cons1)
  have "P y z" using "2.prems"(2) ys_eq(1) by auto
  with ys_eq show ?case by simp
next
  case (3 c y x xs)
  then obtain z ys' where ys_eq: "ys = z # ys'" "P x z" "list_all2 P xs ys'"
    by (metis list_all2_Cons1)
  have "list_all2 P (replace_at c y xs) ys'"
    using "3.IH" "3.prems"(2) ys_eq(1,3) by auto
  with ys_eq show ?case by simp
qed

lemma list_all2_replace_at_sym:
  assumes "list_all2 P xs ys"
  assumes "c < length xs \<Longrightarrow> P x' y'"
  shows   "list_all2 P (replace_at c x' xs) (replace_at c y' ys)"
  using assms
proof (induction c x' xs arbitrary: ys rule: replace_at.induct)
  case (1 c y) thus ?case by simp
next
  case (2 y x xs)
  then obtain z ys' where ys_eq: "ys = z # ys'" "P x z" "list_all2 P xs ys'"
    by (metis list_all2_Cons1)
  have "P y y'" using "2.prems"(2) ys_eq(1) by auto
  with ys_eq show ?case by simp
next
  case (3 c y x xs)
  then obtain z ys' where ys_eq: "ys = z # ys'" "P x z" "list_all2 P xs ys'"
    by (metis list_all2_Cons1)
  have "list_all2 P (replace_at c y xs) (replace_at c y' ys')"
    using "3.IH" "3.prems"(2) ys_eq(1,3) by auto
  with ys_eq show ?case by simp
qed

lemma list_all2_replace_at_both:
  assumes "list_all2 P xs ys"
  assumes "list_all2 P xs' ys'"
  assumes "length xs' = length ys'"
  shows   "list_all2 P (splice_at c xs' xs) (splice_at c ys' ys)"
  using assms
proof (induction c xs' xs arbitrary: ys ys' rule: splice_at.induct)
  case (1 c xs') thus ?case by simp
next
  case (2 ys'' x xs)
  then obtain z zs where ys_eq: "ys = z # zs" "P x z" "list_all2 P xs zs"
    by (metis list_all2_Cons1)
  from 2 ys_eq show ?case
    by (simp add: list_all2_appendI)
next
  case (3 c ys'' x xs)
  then obtain z zs where ys_eq: "ys = z # zs" "P x z" "list_all2 P xs zs"
    by (metis list_all2_Cons1)
  from 3(1)[OF ys_eq(3) 3(3) 3(4)] 3(2) ys_eq
  show ?case by simp
qed

(* drop_at and ! commute when stepping past unrelated indices. We don't
   need this in full generality, but a couple of nth-after-drop lemmas
   make the proofs lighter. *)
lemma nth_drop_at_lt:
  "i < c \<Longrightarrow> i < length xs - 1 \<Longrightarrow> c < length xs \<Longrightarrow>
   drop_at c xs ! i = xs ! i"
  by (induction c xs arbitrary: i rule: drop_at.induct)
     (auto simp: nth_Cons split: nat.split)


section \<open>Inversion lemmas for pattern_compatible\<close>

lemma pattern_compatible_variant_inv:
  assumes "pattern_compatible env (CorePat_Variant ctor payload) ty"
  obtains dtName tyArgs tyvars payloadTy where
    "ty = CoreTy_Datatype dtName tyArgs"
    "fmlookup (TE_DataCtors env) ctor = Some (dtName, tyvars, payloadTy)"
    "length tyArgs = length tyvars"
    "pattern_compatible env payload
        (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
  using assms
  by (cases "fmlookup (TE_DataCtors env) ctor"; cases ty)
     (auto split: option.splits prod.splits)

lemma pattern_compatible_record_inv:
  assumes "pattern_compatible env (CorePat_Record pflds) ty"
  obtains fldTys where
    "ty = CoreTy_Record fldTys"
    "list_all2 (\<lambda>(pn, p) (fn, fty). pn = fn \<and> pattern_compatible env p fty)
               pflds fldTys"
  using assms by (cases ty) auto


section \<open>Bodies subset: every output body is an input body\<close>

(* Helper for List.map_filter: every element of the filtered output
   comes from the input. *)
lemma map_filter_member:
  assumes "y \<in> set (List.map_filter f xs)"
  obtains x where "x \<in> set xs" "f x = Some y"
  using assms by (induction xs) (auto simp: List.map_filter_simps split: option.splits)

lemma specialise_row_bool_body:
  "specialise_row_bool c h r = Some r' \<Longrightarrow> snd r' = snd r"
  by (cases r) (auto split: CorePattern.splits if_splits)

lemma specialise_row_int_body:
  "specialise_row_int c h r = Some r' \<Longrightarrow> snd r' = snd r"
  by (cases r) (auto split: CorePattern.splits if_splits)

lemma specialise_row_variant_body:
  "specialise_row_variant c h r = Some r' \<Longrightarrow> snd r' = snd r"
  by (cases r) (auto split: CorePattern.splits if_splits)

lemma default_row_body:
  "default_row c r = Some r' \<Longrightarrow> snd r' = snd r"
  by (cases r) (auto split: CorePattern.splits)

lemma expand_record_row_body:
  "snd (expand_record_row c fns r) = snd r"
  by (cases r) (auto split: CorePattern.splits)

(* The output bodies of compile_matrix are all drawn from the input
   rows' bodies. *)
(* set inclusion under List.map_filter when the filter preserves snd. *)
lemma map_filter_snd_subset:
  assumes "\<And>r r'. f r = Some r' \<Longrightarrow> snd r' = snd r"
  shows "set (map snd (List.map_filter f xs)) \<subseteq> set (map snd xs)"
proof
  fix b assume "b \<in> set (map snd (List.map_filter f xs))"
  then obtain r' where r'_in: "r' \<in> set (List.map_filter f xs)" and b_eq: "b = snd r'"
    by auto
  from r'_in obtain r where r_in: "r \<in> set xs" and fr: "f r = Some r'"
    by (rule map_filter_member)
  from fr assms have "snd r' = snd r" by blast
  with r_in b_eq show "b \<in> set (map snd xs)" by force
qed

lemma compile_matrix_bodies_subset:
  "snd m \<noteq> [] \<Longrightarrow> match_tree_bodies (compile_matrix m) \<subseteq> set (map snd (snd m))"
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
    obtain r0 rs where rows_eq: "rows = r0 # rs" using rows_ne by (cases rows) auto
    obtain ps0 body0 where r0_eq: "r0 = (ps0, body0)" by (cases r0) auto
    from Some rows_ne have head_nw: "\<not> is_wildcard_like (fst (hd rows) ! c)"
      using first_non_wildcard_col_head_weight_pos
            is_wildcard_like_iff_weight_zero
      by auto
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

      have default_subset:
        "list_ex is_wildcard_like ?col_pats \<Longrightarrow>
           match_tree_bodies (compile_matrix (drop_at c scruts,
             List.map_filter (default_row c) rows))
             \<subseteq> set (map snd rows)"
      proof -
        assume has_default: "list_ex is_wildcard_like ?col_pats"
        have IH:
          "match_tree_bodies (compile_matrix (drop_at c scruts,
             List.map_filter (default_row c) rows))
           \<subseteq> set (map snd (List.map_filter (default_row c) rows))"
          using "1.IH"(1)[OF col_some]
                default_rows_nonempty[OF col_some has_default]
          by (simp add: has_default)
        have "set (map snd (List.map_filter (default_row c) rows))
                \<subseteq> set (map snd rows)"
          by (rule map_filter_snd_subset) (rule default_row_body)
        with IH show "match_tree_bodies (compile_matrix (drop_at c scruts,
             List.map_filter (default_row c) rows))
             \<subseteq> set (map snd rows)" by blast
      qed

      show ?thesis
      proof (cases hk)
        case HK_Bool
        have IH_heads:
          "\<And>h. h \<in> set (distinct_bool_heads ?col_pats) \<Longrightarrow>
             match_tree_bodies (compile_matrix
               (drop_at c scruts,
                List.map_filter (specialise_row_bool c h) rows))
             \<subseteq> set (map snd rows)"
        proof -
          fix h assume h_in: "h \<in> set (distinct_bool_heads ?col_pats)"
          have IH: "match_tree_bodies (compile_matrix
                      (drop_at c scruts,
                       List.map_filter (specialise_row_bool c h) rows))
                    \<subseteq> set (map snd (List.map_filter (specialise_row_bool c h) rows))"
            using "1.IH"(2)[OF col_some] head_kind_some HK_Bool
                  specialise_bool_rows_nonempty[OF h_in]
            by (metis "1.IH"(4) col_some snd_conv)
          have "set (map snd (List.map_filter (specialise_row_bool c h) rows))
                  \<subseteq> set (map snd rows)"
            by (rule map_filter_snd_subset) (rule specialise_row_bool_body)
          with IH show "match_tree_bodies (compile_matrix
                      (drop_at c scruts,
                       List.map_filter (specialise_row_bool c h) rows))
                    \<subseteq> set (map snd rows)" by blast
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
        show ?thesis
          unfolding unfolded match_tree_bodies.simps
          using IH_heads default_subset by (auto split: if_splits)
      next
        case HK_Int
        have IH_heads:
          "\<And>h. h \<in> set (distinct_int_heads ?col_pats) \<Longrightarrow>
             match_tree_bodies (compile_matrix
               (drop_at c scruts,
                List.map_filter (specialise_row_int c h) rows))
             \<subseteq> set (map snd rows)"
        proof -
          fix h assume h_in: "h \<in> set (distinct_int_heads ?col_pats)"
          have IH: "match_tree_bodies (compile_matrix
                      (drop_at c scruts,
                       List.map_filter (specialise_row_int c h) rows))
                    \<subseteq> set (map snd (List.map_filter (specialise_row_int c h) rows))"
            using "1.IH"(3)[OF col_some] head_kind_some HK_Int
                  specialise_int_rows_nonempty[OF h_in]
            by (metis "1.IH"(5) col_some snd_conv)
          have "set (map snd (List.map_filter (specialise_row_int c h) rows))
                  \<subseteq> set (map snd rows)"
            by (rule map_filter_snd_subset) (rule specialise_row_int_body)
          with IH show "match_tree_bodies (compile_matrix
                      (drop_at c scruts,
                       List.map_filter (specialise_row_int c h) rows))
                    \<subseteq> set (map snd rows)" by blast
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
        show ?thesis
          unfolding unfolded match_tree_bodies.simps
          using IH_heads default_subset by (auto split: if_splits)
      next
        case HK_Variant
        have IH_heads:
          "\<And>h. h \<in> set (distinct_variant_heads ?col_pats) \<Longrightarrow>
             match_tree_bodies (compile_matrix
               (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                List.map_filter (specialise_row_variant c h) rows))
             \<subseteq> set (map snd rows)"
        proof -
          fix h assume h_in: "h \<in> set (distinct_variant_heads ?col_pats)"
          have IH: "match_tree_bodies (compile_matrix
                      (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                       List.map_filter (specialise_row_variant c h) rows))
                    \<subseteq> set (map snd (List.map_filter (specialise_row_variant c h) rows))"
            using "1.IH"(4)[OF col_some] head_kind_some HK_Variant
                  specialise_variant_rows_nonempty[OF h_in]
            by (metis "1.IH"(3) col_some snd_conv)
          have "set (map snd (List.map_filter (specialise_row_variant c h) rows))
                  \<subseteq> set (map snd rows)"
            by (rule map_filter_snd_subset) (rule specialise_row_variant_body)
          with IH show "match_tree_bodies (compile_matrix
                      (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                       List.map_filter (specialise_row_variant c h) rows))
                    \<subseteq> set (map snd rows)" by blast
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
        show ?thesis
          unfolding unfolded match_tree_bodies.simps
          using IH_heads default_subset by (auto split: if_splits)
      next
        case (HK_Record fld_names)
        have IH_record:
          "match_tree_bodies (compile_matrix
              (expand_record_scruts c (scruts ! c) fld_names scruts,
               map (expand_record_row c fld_names) rows))
           \<subseteq> set (map snd (map (expand_record_row c fld_names) rows))"
          using "1.IH"(5)[OF col_some] head_kind_some HK_Record rows_ne
          by (metis "1.IH"(2) col_some expand_record_rows_nonempty snd_conv)
        have rec_subset:
          "match_tree_bodies (compile_matrix
              (expand_record_scruts c (scruts ! c) fld_names scruts,
               map (expand_record_row c fld_names) rows))
           \<subseteq> set (map snd rows)"
        proof -
          have "map snd (map (expand_record_row c fld_names) rows) = map snd rows"
            by (simp add: expand_record_row_body)
          with IH_record show ?thesis by simp
        qed
        have unfolded:
          "compile_matrix (scruts, rows) =
             compile_matrix
               (expand_record_scruts c (scruts ! c) fld_names scruts,
                map (expand_record_row c fld_names) rows)"
          using col_some head_kind_some HK_Record
          by (simp add: case_prod_unfold Let_def)
        from unfolded rec_subset show ?thesis by simp
      qed
    qed
  qed
qed


section \<open>Arm patterns compatible: the main type-preservation lemma\<close>

lemma list_all2_nth:
  "list_all2 P xs ys \<Longrightarrow> c < length xs \<Longrightarrow> P (xs ! c) (ys ! c)"
  by (simp add: list_all2_conv_all_nth)

lemma list_all2_length:
  "list_all2 P xs ys \<Longrightarrow> length xs = length ys"
  by (simp add: list_all2_conv_all_nth)


subsection \<open>Column-type lookup\<close>

(* If some row has a non-wildcard pattern at column c, the column's
   type is determined by that pattern via pattern_compatible. We
   instantiate this for each head kind to derive the column type. *)

lemma col_type_bool:
  assumes "list_all (\<lambda>(ps, _).
              length ps = length colTys
            \<and> list_all2 (pattern_compatible env) ps colTys) rows"
  assumes "h \<in> set (distinct_bool_heads (map (\<lambda>(ps, _). ps ! c) rows))"
  assumes "c < length colTys"
  shows   "colTys ! c = CoreTy_Bool"
proof -
  from assms(2) distinct_bool_heads_subset
    have "CorePat_Bool h \<in> set (map (\<lambda>(ps, _). ps ! c) rows)" by blast
  then obtain r where r_in: "r \<in> set rows"
                  and r_eq: "(\<lambda>(ps, _). ps ! c) r = CorePat_Bool h"
    by auto
  obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
  with r_eq have pc: "ps ! c = CorePat_Bool h" by simp
  from assms(1) r_in r_split have
    len: "length ps = length colTys" and
    pcs: "list_all2 (pattern_compatible env) ps colTys"
    by (auto simp: list_all_iff)
  from list_all2_nth[OF pcs] assms(3) len
    have "pattern_compatible env (ps ! c) (colTys ! c)" by simp
  with pc show ?thesis by simp
qed

lemma col_type_int:
  assumes "list_all (\<lambda>(ps, _).
              length ps = length colTys
            \<and> list_all2 (pattern_compatible env) ps colTys) rows"
  assumes "h \<in> set (distinct_int_heads (map (\<lambda>(ps, _). ps ! c) rows))"
  assumes "c < length colTys"
  shows   "is_integer_type (colTys ! c)"
proof -
  from assms(2) distinct_int_heads_subset
    have "CorePat_Int h \<in> set (map (\<lambda>(ps, _). ps ! c) rows)" by blast
  then obtain r where r_in: "r \<in> set rows"
                  and r_eq: "(\<lambda>(ps, _). ps ! c) r = CorePat_Int h"
    by auto
  obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
  with r_eq have pc: "ps ! c = CorePat_Int h" by simp
  from assms(1) r_in r_split have
    len: "length ps = length colTys" and
    pcs: "list_all2 (pattern_compatible env) ps colTys"
    by (auto simp: list_all_iff)
  from list_all2_nth[OF pcs] assms(3) len
    have "pattern_compatible env (ps ! c) (colTys ! c)" by simp
  with pc show ?thesis by simp
qed

lemma col_type_variant:
  assumes "list_all (\<lambda>(ps, _).
              length ps = length colTys
            \<and> list_all2 (pattern_compatible env) ps colTys) rows"
  assumes "h \<in> set (distinct_variant_heads (map (\<lambda>(ps, _). ps ! c) rows))"
  assumes "c < length colTys"
  obtains dtName tyArgs tyvars payloadTy where
    "colTys ! c = CoreTy_Datatype dtName tyArgs"
    "fmlookup (TE_DataCtors env) h = Some (dtName, tyvars, payloadTy)"
    "length tyArgs = length tyvars"
proof -
  from assms(2) distinct_variant_heads_subset obtain p where
    "CorePat_Variant h p \<in> set (map (\<lambda>(ps, _). ps ! c) rows)" by blast
  then obtain r where r_in: "r \<in> set rows"
                  and r_eq: "(\<lambda>(ps, _). ps ! c) r = CorePat_Variant h p"
    by auto
  obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
  with r_eq have pc_eq: "ps ! c = CorePat_Variant h p" by simp
  from assms(1) r_in r_split have
    len: "length ps = length colTys" and
    pcs: "list_all2 (pattern_compatible env) ps colTys"
    by (auto simp: list_all_iff)
  from list_all2_nth[OF pcs] assms(3) len
    have pc: "pattern_compatible env (ps ! c) (colTys ! c)" by simp
  from pc pc_eq have
    "pattern_compatible env (CorePat_Variant h p) (colTys ! c)" by simp
  from pattern_compatible_variant_inv[OF this]
  obtain dtName tyArgs tyvars payloadTy where
    "colTys ! c = CoreTy_Datatype dtName tyArgs"
    "fmlookup (TE_DataCtors env) h = Some (dtName, tyvars, payloadTy)"
    "length tyArgs = length tyvars"
    "pattern_compatible env p
        (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
    by metis
  thus ?thesis using that by blast
qed

(* For a record column, every row's pattern at column c is either
   wildcard or CorePat_Record. If a row's head is a CorePat_Record,
   pattern_compatible forces the column type to be a record type with
   matching field names. The field-names list driving expansion comes
   from the column-head record pattern, so we need that the column
   type itself is a CoreTy_Record fldTys with map fst fldTys = fld_names. *)
lemma col_type_record:
  assumes pcs_all: "list_all (\<lambda>(ps, _).
              length ps = length colTys
            \<and> list_all2 (pattern_compatible env) ps colTys) rows"
  assumes head_eq: "(ps0, body0) \<in> set rows"
  assumes head_rec: "ps0 ! c = CorePat_Record pflds"
  assumes c_lt: "c < length colTys"
  obtains fldTys where
    "colTys ! c = CoreTy_Record fldTys"
    "map fst pflds = map fst fldTys"
proof -
  from pcs_all head_eq have
    len: "length ps0 = length colTys" and
    pcs: "list_all2 (pattern_compatible env) ps0 colTys"
    by (auto simp: list_all_iff)
  from list_all2_nth[OF pcs] c_lt len
    have "pattern_compatible env (ps0 ! c) (colTys ! c)" by simp
  with head_rec have
    "pattern_compatible env (CorePat_Record pflds) (colTys ! c)" by simp
  from pattern_compatible_record_inv[OF this]
  obtain fldTys where
    col_eq: "colTys ! c = CoreTy_Record fldTys" and
    la2: "list_all2 (\<lambda>(pn, p) (fn, fty). pn = fn \<and> pattern_compatible env p fty)
                    pflds fldTys"
    by metis
  have "map fst pflds = map fst fldTys"
    using la2 by (induction pflds fldTys rule: list_all2_induct) auto
  with col_eq show ?thesis using that by blast
qed


subsection \<open>Row-specialisation preserves column-pattern compatibility\<close>

(* A surviving row in specialise_row_bool has the same length and
   same per-column compatibility as the original, modulo the dropped
   column. *)
lemma specialise_row_bool_inv:
  assumes "specialise_row_bool c h r = Some r'"
  assumes "length (fst r) = length colTys"
  assumes "list_all2 (pattern_compatible env) (fst r) colTys"
  assumes "c < length colTys"
  shows   "length (fst r') = length (drop_at c colTys)
         \<and> list_all2 (pattern_compatible env) (fst r') (drop_at c colTys)"
proof -
  obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
  from assms(1) r_split obtain ps' where
    r'_eq: "r' = (ps', body)"
    and ps'_eq: "ps' = drop_at c ps"
    by (cases "ps ! c") (auto split: if_splits)
  show ?thesis
  proof
    show "length (fst r') = length (drop_at c colTys)"
      using r'_eq ps'_eq assms(2,4) r_split
      by (simp add: length_drop_at)
  next
    show "list_all2 (pattern_compatible env) (fst r') (drop_at c colTys)"
      using r'_eq ps'_eq assms(3) r_split
      by (simp add: list_all2_drop_at)
  qed
qed

lemma specialise_row_int_inv:
  assumes "specialise_row_int c h r = Some r'"
  assumes "length (fst r) = length colTys"
  assumes "list_all2 (pattern_compatible env) (fst r) colTys"
  assumes "c < length colTys"
  shows   "length (fst r') = length (drop_at c colTys)
         \<and> list_all2 (pattern_compatible env) (fst r') (drop_at c colTys)"
proof -
  obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
  from assms(1) r_split obtain ps' where
    r'_eq: "r' = (ps', body)"
    and ps'_eq: "ps' = drop_at c ps"
    by (cases "ps ! c") (auto split: if_splits)
  show ?thesis
  proof
    show "length (fst r') = length (drop_at c colTys)"
      using r'_eq ps'_eq assms(2,4) r_split
      by (simp add: length_drop_at)
  next
    show "list_all2 (pattern_compatible env) (fst r') (drop_at c colTys)"
      using r'_eq ps'_eq assms(3) r_split
      by (simp add: list_all2_drop_at)
  qed
qed

(* default rows: same shape as bool/int. *)
lemma default_row_inv:
  assumes "default_row c r = Some r'"
  assumes "length (fst r) = length colTys"
  assumes "list_all2 (pattern_compatible env) (fst r) colTys"
  assumes "c < length colTys"
  shows   "length (fst r') = length (drop_at c colTys)
         \<and> list_all2 (pattern_compatible env) (fst r') (drop_at c colTys)"
proof -
  obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
  from assms(1) r_split obtain ps' where
    r'_eq: "r' = (ps', body)"
    and ps'_eq: "ps' = drop_at c ps"
    by (cases "ps ! c") auto
  show ?thesis
  proof
    show "length (fst r') = length (drop_at c colTys)"
      using r'_eq ps'_eq assms(2,4) r_split
      by (simp add: length_drop_at)
  next
    show "list_all2 (pattern_compatible env) (fst r') (drop_at c colTys)"
      using r'_eq ps'_eq assms(3) r_split
      by (simp add: list_all2_drop_at)
  qed
qed

(* Variant: column c's type changes to the substituted payload type;
   surviving rows have their column c replaced with the inner payload
   pattern (or wildcard for wildcard rows). The new column pattern is
   compatible with the new column type. *)
lemma specialise_row_variant_inv:
  assumes "specialise_row_variant c h r = Some r'"
  assumes "length (fst r) = length colTys"
  assumes "list_all2 (pattern_compatible env) (fst r) colTys"
  assumes "c < length colTys"
  assumes "colTys ! c = CoreTy_Datatype dtName tyArgs"
  assumes "fmlookup (TE_DataCtors env) h = Some (dtName, tyvars, payloadTy)"
  assumes "length tyArgs = length tyvars"
  defines "payloadTy' \<equiv> apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy"
  defines "colTys' \<equiv> replace_at c payloadTy' colTys"
  shows   "length (fst r') = length colTys'
         \<and> list_all2 (pattern_compatible env) (fst r') colTys'"
proof -
  obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
  from list_all2_nth[OF assms(3)] assms(4) assms(2) r_split
    have pc_at_c: "pattern_compatible env (ps ! c) (colTys ! c)" by simp
  from assms(1) r_split
  consider
      (Match) payload where "ps ! c = CorePat_Variant h payload"
                          "r' = (replace_at c payload ps, body)"
    | (Wild) "ps ! c = CorePat_Wildcard"
             "r' = (replace_at c CorePat_Wildcard ps, body)"
    by (cases "ps ! c") (auto split: if_splits)
  thus ?thesis
  proof cases
    case (Match payload)
    from pc_at_c Match(1) have
      "pattern_compatible env (CorePat_Variant h payload) (colTys ! c)" by simp
    from pattern_compatible_variant_inv[OF this] assms(5,6,7) payloadTy'_def
    have payload_pc: "pattern_compatible env payload payloadTy'"
      by (auto split: if_splits)
    show ?thesis
    proof
      show "length (fst r') = length colTys'"
        using Match(2) assms(2) r_split colTys'_def
        by (simp add: length_replace_at)
    next
      show "list_all2 (pattern_compatible env) (fst r') colTys'"
        unfolding colTys'_def using Match(2) assms(3) r_split payload_pc
        by (auto intro!: list_all2_replace_at_sym)
    qed
  next
    case Wild
    have pc_wild: "pattern_compatible env CorePat_Wildcard payloadTy'" by simp
    show ?thesis
    proof
      show "length (fst r') = length colTys'"
        using Wild(2) assms(2) r_split colTys'_def
        by (simp add: length_replace_at)
    next
      show "list_all2 (pattern_compatible env) (fst r') colTys'"
        unfolding colTys'_def using Wild(2) assms(3) r_split pc_wild
        by (auto intro!: list_all2_replace_at_sym)
    qed
  qed
qed

(* Record expansion: column c's type list splices in the field types;
   each row's column c splices in its field sub-patterns (or wildcards
   if the row is wildcard at c). *)
lemma expand_record_row_inv:
  assumes "length (fst r) = length colTys"
  assumes "list_all2 (pattern_compatible env) (fst r) colTys"
  assumes "c < length colTys"
  assumes "colTys ! c = CoreTy_Record fldTys"
  assumes "fld_names = map fst fldTys"
  defines "r' \<equiv> expand_record_row c fld_names r"
  defines "colTys' \<equiv> splice_at c (map snd fldTys) colTys"
  shows   "length (fst r') = length colTys'
         \<and> list_all2 (pattern_compatible env) (fst r') colTys'"
proof -
  obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
  from list_all2_nth[OF assms(2)] assms(3) assms(1) r_split
    have pc_at_c: "pattern_compatible env (ps ! c) (colTys ! c)" by simp
  show ?thesis
  proof (cases "ps ! c")
    case (CorePat_Record row_flds)
    from pc_at_c CorePat_Record assms(4) have
      la2: "list_all2 (\<lambda>(pn, p) (fn, fty). pn = fn \<and> pattern_compatible env p fty)
                      row_flds fldTys"
      by simp
    have sub_pc_zip:
      "list_all2 (pattern_compatible env) (map snd row_flds) (map snd fldTys)"
      using la2
      by (induction row_flds fldTys rule: list_all2_induct) auto
    have len_eq: "length row_flds = length fldTys"
      using la2 by (rule list_all2_lengthD)
    from CorePat_Record have
      ps'_eq: "fst r' = splice_at c (map snd row_flds) ps"
      using r'_def r_split by simp
    have len_subs: "length (map snd row_flds) = length (map snd fldTys)"
      using len_eq by simp
    show ?thesis
    proof
      show "length (fst r') = length colTys'"
        unfolding ps'_eq colTys'_def
        using assms(1,3) r_split len_subs
        by (simp add: length_splice_at)
    next
      show "list_all2 (pattern_compatible env) (fst r') colTys'"
        unfolding ps'_eq colTys'_def
        using assms(2) sub_pc_zip len_subs r_split
        by (auto intro!: list_all2_replace_at_both)
    qed
  next
    case CorePat_Wildcard
    from CorePat_Wildcard have
      ps'_eq: "fst r' = splice_at c (replicate (length fld_names) CorePat_Wildcard) ps"
      using r'_def r_split by simp
    have len_subs:
      "length (replicate (length fld_names) CorePat_Wildcard) = length (map snd fldTys)"
      using assms(5) by simp
    have wild_pc:
      "list_all2 (pattern_compatible env)
                 (replicate (length fld_names) CorePat_Wildcard)
                 (map snd fldTys)"
      using len_subs by (simp add: list_all2_conv_all_nth)
    show ?thesis
    proof
      show "length (fst r') = length colTys'"
        unfolding ps'_eq colTys'_def
        using assms(1,3) r_split assms(5)
        by (simp add: length_splice_at)
    next
      show "list_all2 (pattern_compatible env) (fst r') colTys'"
        unfolding ps'_eq colTys'_def
        using assms(2) wild_pc len_subs r_split
        by (auto intro!: list_all2_replace_at_both)
    qed
  next
    case (CorePat_Bool b)
    with pc_at_c assms(4) show ?thesis by simp
  next
    case (CorePat_Int i)
    with pc_at_c assms(4) show ?thesis by simp
  next
    case (CorePat_Variant nm p)
    with pc_at_c assms(4) show ?thesis
      by (auto split: option.splits prod.splits CoreType.splits)
  qed
qed


section \<open>Main theorem: compile_matrix preserves pattern compatibility\<close>

(* Lift row-level preservation to matrix-level. *)

lemma map_filter_list_all:
  assumes "list_all P xs"
  assumes "\<And>x y. P x \<Longrightarrow> f x = Some y \<Longrightarrow> Q y"
  shows   "list_all Q (List.map_filter f xs)"
  using assms
  by (induction xs) (auto simp: List.map_filter_simps split: option.splits)

lemma matrix_inv_default:
  assumes "matrix_inv env g colTys (scruts, rows)"
  assumes "c < length colTys"
  shows   "matrix_inv env g (drop_at c colTys)
             (drop_at c scruts, List.map_filter (default_row c) rows)"
proof -
  from assms(1) have
    len: "length scruts = length colTys" and
    sc_pc: "list_all2 (\<lambda>s ty. core_term_type env g s = Some ty) scruts colTys" and
    cols_wk: "list_all (is_well_kinded env) colTys" and
    rows_inv: "list_all (\<lambda>(ps, _).
       length ps = length colTys
     \<and> list_all2 (pattern_compatible env) ps colTys) rows"
    unfolding matrix_inv_def by auto
  have new_len:
    "length (drop_at c scruts) = length (drop_at c colTys)"
    using len assms(2) by (simp add: length_drop_at)
  have new_sc_pc:
    "list_all2 (\<lambda>s ty. core_term_type env g s = Some ty)
       (drop_at c scruts) (drop_at c colTys)"
    using list_all2_drop_at[OF sc_pc] .
  have new_cols_wk:
    "list_all (is_well_kinded env) (drop_at c colTys)"
    by (rule list_all_drop_at[OF cols_wk])
  have new_rows_inv:
    "list_all (\<lambda>(ps, _).
       length ps = length (drop_at c colTys)
     \<and> list_all2 (pattern_compatible env) ps (drop_at c colTys))
       (List.map_filter (default_row c) rows)"
  proof (rule map_filter_list_all[OF rows_inv])
    fix r r' :: "'body Row"
    assume r_pc: "(case r of (ps, _) \<Rightarrow>
                            length ps = length colTys
                          \<and> list_all2 (pattern_compatible env) ps colTys)"
      and dr: "default_row c r = Some r'"
    obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
    from r_pc r_split have
      len_ps: "length (fst r) = length colTys" and
      pcs: "list_all2 (pattern_compatible env) (fst r) colTys" by auto
    from default_row_inv[OF dr len_ps pcs assms(2)]
    show "case r' of (ps, _) \<Rightarrow>
             length ps = length (drop_at c colTys)
           \<and> list_all2 (pattern_compatible env) ps (drop_at c colTys)"
      by (cases r') simp
  qed
  show ?thesis
    unfolding matrix_inv_def
    using new_len new_sc_pc new_cols_wk new_rows_inv by simp
qed

lemma matrix_inv_specialise_bool:
  assumes "matrix_inv env g colTys (scruts, rows)"
  assumes "c < length colTys"
  shows   "matrix_inv env g (drop_at c colTys)
             (drop_at c scruts, List.map_filter (specialise_row_bool c h) rows)"
proof -
  from assms(1) have
    len: "length scruts = length colTys" and
    sc_pc: "list_all2 (\<lambda>s ty. core_term_type env g s = Some ty) scruts colTys" and
    cols_wk: "list_all (is_well_kinded env) colTys" and
    rows_inv: "list_all (\<lambda>(ps, _).
       length ps = length colTys
     \<and> list_all2 (pattern_compatible env) ps colTys) rows"
    unfolding matrix_inv_def by auto
  have new_len: "length (drop_at c scruts) = length (drop_at c colTys)"
    using len assms(2) by (simp add: length_drop_at)
  have new_sc_pc:
    "list_all2 (\<lambda>s ty. core_term_type env g s = Some ty)
       (drop_at c scruts) (drop_at c colTys)"
    using list_all2_drop_at[OF sc_pc] .
  have new_cols_wk: "list_all (is_well_kinded env) (drop_at c colTys)"
    by (rule list_all_drop_at[OF cols_wk])
  have new_rows_inv:
    "list_all (\<lambda>(ps, _).
       length ps = length (drop_at c colTys)
     \<and> list_all2 (pattern_compatible env) ps (drop_at c colTys))
       (List.map_filter (specialise_row_bool c h) rows)"
  proof (rule map_filter_list_all[OF rows_inv])
    fix r r' :: "'body Row"
    assume r_pc: "(case r of (ps, _) \<Rightarrow>
                            length ps = length colTys
                          \<and> list_all2 (pattern_compatible env) ps colTys)"
      and sp: "specialise_row_bool c h r = Some r'"
    obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
    from r_pc r_split have
      len_ps: "length (fst r) = length colTys" and
      pcs: "list_all2 (pattern_compatible env) (fst r) colTys" by auto
    from specialise_row_bool_inv[OF sp len_ps pcs assms(2)]
    show "case r' of (ps, _) \<Rightarrow>
             length ps = length (drop_at c colTys)
           \<and> list_all2 (pattern_compatible env) ps (drop_at c colTys)"
      by (cases r') simp
  qed
  show ?thesis
    unfolding matrix_inv_def
    using new_len new_sc_pc new_cols_wk new_rows_inv by simp
qed

lemma matrix_inv_specialise_int:
  assumes "matrix_inv env g colTys (scruts, rows)"
  assumes "c < length colTys"
  shows   "matrix_inv env g (drop_at c colTys)
             (drop_at c scruts, List.map_filter (specialise_row_int c h) rows)"
proof -
  from assms(1) have
    len: "length scruts = length colTys" and
    sc_pc: "list_all2 (\<lambda>s ty. core_term_type env g s = Some ty) scruts colTys" and
    cols_wk: "list_all (is_well_kinded env) colTys" and
    rows_inv: "list_all (\<lambda>(ps, _).
       length ps = length colTys
     \<and> list_all2 (pattern_compatible env) ps colTys) rows"
    unfolding matrix_inv_def by auto
  have new_len: "length (drop_at c scruts) = length (drop_at c colTys)"
    using len assms(2) by (simp add: length_drop_at)
  have new_sc_pc:
    "list_all2 (\<lambda>s ty. core_term_type env g s = Some ty)
       (drop_at c scruts) (drop_at c colTys)"
    using list_all2_drop_at[OF sc_pc] .
  have new_cols_wk: "list_all (is_well_kinded env) (drop_at c colTys)"
    by (rule list_all_drop_at[OF cols_wk])
  have new_rows_inv:
    "list_all (\<lambda>(ps, _).
       length ps = length (drop_at c colTys)
     \<and> list_all2 (pattern_compatible env) ps (drop_at c colTys))
       (List.map_filter (specialise_row_int c h) rows)"
  proof (rule map_filter_list_all[OF rows_inv])
    fix r r' :: "'body Row"
    assume r_pc: "(case r of (ps, _) \<Rightarrow>
                            length ps = length colTys
                          \<and> list_all2 (pattern_compatible env) ps colTys)"
      and sp: "specialise_row_int c h r = Some r'"
    obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
    from r_pc r_split have
      len_ps: "length (fst r) = length colTys" and
      pcs: "list_all2 (pattern_compatible env) (fst r) colTys" by auto
    from specialise_row_int_inv[OF sp len_ps pcs assms(2)]
    show "case r' of (ps, _) \<Rightarrow>
             length ps = length (drop_at c colTys)
           \<and> list_all2 (pattern_compatible env) ps (drop_at c colTys)"
      by (cases r') simp
  qed
  show ?thesis
    unfolding matrix_inv_def
    using new_len new_sc_pc new_cols_wk new_rows_inv by simp
qed

(* Variant case: column type at c changes from CoreTy_Datatype dt args
   to the substituted payload type. The substituted payload type is
   well-kinded by apply_subst_specializes_well_kinded, using
   tyenv_well_formed to extract the relevant well-formedness
   conditions. *)
lemma matrix_inv_specialise_variant:
  assumes "matrix_inv env g colTys (scruts, rows)"
  assumes "c < length colTys"
  assumes "colTys ! c = CoreTy_Datatype dtName tyArgs"
  assumes "fmlookup (TE_DataCtors env) h = Some (dtName, tyvars, payloadTy)"
  assumes "length tyArgs = length tyvars"
  assumes "tyenv_well_formed env"
  defines "payloadTy' \<equiv> apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy"
  shows   "matrix_inv env g (replace_at c payloadTy' colTys)
             (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
              List.map_filter (specialise_row_variant c h) rows)"
proof -
  from assms(1) have
    len: "length scruts = length colTys" and
    sc_pc: "list_all2 (\<lambda>s ty. core_term_type env g s = Some ty) scruts colTys" and
    cols_wk: "list_all (is_well_kinded env) colTys" and
    rows_inv: "list_all (\<lambda>(ps, _).
       length ps = length colTys
     \<and> list_all2 (pattern_compatible env) ps colTys) rows"
    unfolding matrix_inv_def by auto
  from list_all2_nth[OF sc_pc] assms(2) len
    have sc_at_c: "core_term_type env g (scruts ! c) = Some (colTys ! c)" by simp
  with assms(3) have sc_at_c': "core_term_type env g (scruts ! c) = Some (CoreTy_Datatype dtName tyArgs)"
    by simp
  have new_sc_at_c: "core_term_type env g (CoreTm_VariantProj (scruts ! c) h) = Some payloadTy'"
    using sc_at_c' assms(4,5)
    by (simp add: payloadTy'_def)
  have new_len:
    "length (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts)
       = length (replace_at c payloadTy' colTys)"
    using len by (simp add: length_replace_at)
  have new_sc_pc:
    "list_all2 (\<lambda>s ty. core_term_type env g s = Some ty)
       (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts)
       (replace_at c payloadTy' colTys)"
    by (rule list_all2_replace_at_sym[OF sc_pc]) (rule new_sc_at_c)
  (* Well-kindedness of the substituted payload type. *)
  from assms(6) have payloads_wk:
    "is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list tyvars \<rparr>) payloadTy"
    using assms(4)
    unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def
    by blast
  have col_c_wk: "is_well_kinded env (CoreTy_Datatype dtName tyArgs)"
    using cols_wk assms(2,3)
    by (auto simp: list_all_iff dest!: nth_mem)
  have args_wk: "list_all (is_well_kinded env) tyArgs"
    using col_c_wk
    by (auto split: option.splits)
  have payload'_wk: "is_well_kinded env payloadTy'"
    unfolding payloadTy'_def
    using apply_subst_specializes_well_kinded[OF payloads_wk args_wk] assms(5)
    by simp
  have new_cols_wk:
    "list_all (is_well_kinded env) (replace_at c payloadTy' colTys)"
    using list_all_replace_at[OF cols_wk] payload'_wk by blast
  have new_rows_inv:
    "list_all (\<lambda>(ps, _).
       length ps = length (replace_at c payloadTy' colTys)
     \<and> list_all2 (pattern_compatible env) ps (replace_at c payloadTy' colTys))
       (List.map_filter (specialise_row_variant c h) rows)"
  proof (rule map_filter_list_all[OF rows_inv])
    fix r r' :: "'body Row"
    assume r_pc: "(case r of (ps, _) \<Rightarrow>
                            length ps = length colTys
                          \<and> list_all2 (pattern_compatible env) ps colTys)"
      and sp: "specialise_row_variant c h r = Some r'"
    obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
    from r_pc r_split have
      len_ps: "length (fst r) = length colTys" and
      pcs: "list_all2 (pattern_compatible env) (fst r) colTys" by auto
    from specialise_row_variant_inv[OF sp len_ps pcs assms(2) assms(3) assms(4) assms(5)]
    show "case r' of (ps, _) \<Rightarrow>
             length ps = length (replace_at c payloadTy' colTys)
           \<and> list_all2 (pattern_compatible env) ps (replace_at c payloadTy' colTys)"
      by (cases r') (simp add: payloadTy'_def)
  qed
  show ?thesis
    unfolding matrix_inv_def
    using new_len new_sc_pc new_cols_wk new_rows_inv by simp
qed

(* Record case: column type at c is CoreTy_Record fldTys; new columns
   splice in (map snd fldTys) at position c; new scruts splice in one
   CoreTm_RecordProj per field. *)
lemma matrix_inv_expand_record:
  assumes "matrix_inv env g colTys (scruts, rows)"
  assumes "c < length colTys"
  assumes "colTys ! c = CoreTy_Record fldTys"
  assumes "fld_names = map fst fldTys"
  shows   "matrix_inv env g (splice_at c (map snd fldTys) colTys)
             (expand_record_scruts c (scruts ! c) fld_names scruts,
              map (expand_record_row c fld_names) rows)"
proof -
  from assms(1) have
    len: "length scruts = length colTys" and
    sc_pc: "list_all2 (\<lambda>s ty. core_term_type env g s = Some ty) scruts colTys" and
    cols_wk: "list_all (is_well_kinded env) colTys" and
    rows_inv: "list_all (\<lambda>(ps, _).
       length ps = length colTys
     \<and> list_all2 (pattern_compatible env) ps colTys) rows"
    unfolding matrix_inv_def by auto
  from list_all2_nth[OF sc_pc] assms(2) len
    have sc_at_c: "core_term_type env g (scruts ! c) = Some (colTys ! c)" by simp
  with assms(3) have sc_at_c': "core_term_type env g (scruts ! c) = Some (CoreTy_Record fldTys)"
    by simp
  (* Distinctness of fldTys field names (needed for expand_record_row_inv) *)
  have col_c_in: "colTys ! c \<in> set colTys" using assms(2) by (rule nth_mem)
  with assms(3) cols_wk
  have col_c_wk: "is_well_kinded env (CoreTy_Record fldTys)"
    by (metis assms(2) list_all_length)
  hence distinct_flds: "distinct (map fst fldTys)" by simp
  from col_c_wk have sub_wk: "list_all (is_well_kinded env) (map snd fldTys)"
    by simp
  (* New scrutinees splice in one RecordProj per field. *)
  have proj_typed:
    "list_all2 (\<lambda>s ty. core_term_type env g s = Some ty)
       (map (\<lambda>f. CoreTm_RecordProj (scruts ! c) f) fld_names)
       (map snd fldTys)"
  proof (rule list_all2_all_nthI)
    show "length (map (\<lambda>f. CoreTm_RecordProj (scruts ! c) f) fld_names)
          = length (map snd fldTys)"
      using assms(4) by simp
  next
    fix i assume i_lt: "i < length (map (\<lambda>f. CoreTm_RecordProj (scruts ! c) f) fld_names)"
    from i_lt assms(4) have i_lt': "i < length fldTys" by simp
    obtain f fty where fld_i: "fldTys ! i = (f, fty)" by (cases "fldTys ! i") auto
    from assms(4) i_lt' have fld_names_i: "fld_names ! i = f"
      using fld_i by (metis fst_conv nth_map)
    have mo: "map_of fldTys f = Some fty"
      using distinct_flds fld_i i_lt'
      by (metis Some_eq_map_of_iff nth_mem)
    show "core_term_type env g
            (map (\<lambda>f. CoreTm_RecordProj (scruts ! c) f) fld_names ! i)
          = Some (map snd fldTys ! i)"
      using sc_at_c' mo fld_i fld_names_i i_lt i_lt'
      by simp
  qed
  have new_len:
    "length (expand_record_scruts c (scruts ! c) fld_names scruts)
       = length (splice_at c (map snd fldTys) colTys)"
    unfolding expand_record_scruts_def
    using len assms(2,4)
    by (simp add: length_splice_at)
  have new_sc_pc:
    "list_all2 (\<lambda>s ty. core_term_type env g s = Some ty)
       (expand_record_scruts c (scruts ! c) fld_names scruts)
       (splice_at c (map snd fldTys) colTys)"
    unfolding expand_record_scruts_def
    using sc_pc proj_typed assms(4)
    by (auto intro!: list_all2_replace_at_both)
  have new_cols_wk:
    "list_all (is_well_kinded env) (splice_at c (map snd fldTys) colTys)"
    by (rule list_all_splice_at[OF cols_wk sub_wk])
  have new_rows_inv:
    "list_all (\<lambda>(ps, _).
       length ps = length (splice_at c (map snd fldTys) colTys)
     \<and> list_all2 (pattern_compatible env) ps (splice_at c (map snd fldTys) colTys))
       (map (expand_record_row c fld_names) rows)"
  proof -
    have "\<forall>r \<in> set rows.
            case expand_record_row c fld_names r of (ps, _) \<Rightarrow>
              length ps = length (splice_at c (map snd fldTys) colTys)
            \<and> list_all2 (pattern_compatible env) ps (splice_at c (map snd fldTys) colTys)"
    proof
      fix r
      assume r_in: "r \<in> set rows"
      obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
      from rows_inv r_in r_split have
        len_ps: "length (fst r) = length colTys" and
        pcs: "list_all2 (pattern_compatible env) (fst r) colTys"
        by (auto simp: list_all_iff)
      from expand_record_row_inv[OF len_ps pcs assms(2) assms(3) assms(4)]
      show "case expand_record_row c fld_names r of (ps, _) \<Rightarrow>
              length ps = length (splice_at c (map snd fldTys) colTys)
            \<and> list_all2 (pattern_compatible env) ps (splice_at c (map snd fldTys) colTys)"
        by (cases "expand_record_row c fld_names r") simp
    qed
    thus ?thesis by (simp add: list_all_iff)
  qed
  show ?thesis
    unfolding matrix_inv_def
    using new_len new_sc_pc new_cols_wk new_rows_inv by simp
qed


(* Headline lemma: compile_matrix produces a tree whose every test
   pattern is compatible with its scrutinee's type. *)
theorem compile_matrix_arm_patterns_compatible:
  assumes "matrix_inv env g colTys m"
  assumes "snd m \<noteq> []"
  assumes "tyenv_well_formed env"
  shows   "arm_patterns_compatible env g (compile_matrix m)"
  using assms
proof (induction m arbitrary: colTys rule: compile_matrix.induct)
  case (1 scruts rows)
  from "1.prems"(2) have rows_ne: "rows \<noteq> []" by simp
  note inv = "1.prems"(1)
  note wf = "1.prems"(3)
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
    obtain r0 rs where rows_eq: "rows = r0 # rs" using rows_ne by (cases rows) auto
    obtain ps0 body0 where r0_eq: "r0 = (ps0, body0)" by (cases r0) auto
    from Some rows_ne have head_nw: "\<not> is_wildcard_like (fst (hd rows) ! c)"
      using first_non_wildcard_col_head_weight_pos
            is_wildcard_like_iff_weight_zero by auto
    from rows_eq r0_eq head_nw have head_nw': "\<not> is_wildcard_like (ps0 ! c)" by simp
    hence nw_col_eq:
      "?nw_col_pats = (ps0 ! c) # filter (\<lambda>p. \<not> is_wildcard_like p)
                                         (map (\<lambda>(ps, _). ps ! c) rs)"
      using rows_eq r0_eq by (simp add: case_prod_unfold)
    from inv have c_lt: "c < length colTys"
      using Some
      unfolding matrix_inv_def first_non_wildcard_col_def
      using rows_eq r0_eq
      by (auto split: list.splits if_splits dest!: find_Some_iff[THEN iffD1])
    from inv have len_scruts: "length scruts = length colTys"
      unfolding matrix_inv_def by simp
    from inv have sc_pc:
      "list_all2 (\<lambda>s ty. core_term_type env g s = Some ty) scruts colTys"
      unfolding matrix_inv_def by simp
    from inv have rows_inv:
      "list_all (\<lambda>(ps, _).
         length ps = length colTys
       \<and> list_all2 (pattern_compatible env) ps colTys) rows"
      unfolding matrix_inv_def by simp
    from list_all2_nth[OF sc_pc] c_lt len_scruts
      have sc_at_c: "core_term_type env g (scruts ! c) = Some (colTys ! c)" by simp
    show ?thesis
    proof (cases "head_kind_of (hd ?nw_col_pats)")
      case None
      from nw_col_eq have "hd ?nw_col_pats = ps0 ! c" by simp
      with None head_nw' head_kind_of_non_wildcard show ?thesis by (metis not_Some_eq)
    next
      case (Some hk)
      have col_some: "first_non_wildcard_col (map fst rows) = Some c"
        using \<open>first_non_wildcard_col (map fst rows) = Some c\<close> .
      from Some have head_kind_some: "head_kind_of (hd ?nw_col_pats) = Some hk" .

      (* Default arm typing: applies in every head-kind case. *)
      have IH_default:
        "list_ex is_wildcard_like ?col_pats \<Longrightarrow>
           arm_patterns_compatible env g
             (compile_matrix (drop_at c scruts, List.map_filter (default_row c) rows))"
      proof -
        assume has_default: "list_ex is_wildcard_like ?col_pats"
        from matrix_inv_default[OF inv c_lt]
        have inv': "matrix_inv env g (drop_at c colTys)
                     (drop_at c scruts, List.map_filter (default_row c) rows)" .
        have ne: "snd (drop_at c scruts, List.map_filter (default_row c) rows) \<noteq> []"
          using default_rows_nonempty[OF col_some has_default] by simp
        from "1.IH"(1)[OF col_some _ _ _ _ has_default inv' ne wf]
        show ?thesis by auto
      qed

      show ?thesis
      proof (cases hk)
        case HK_Bool
        from col_type_bool[OF rows_inv _ c_lt]
        have col_c_bool: "\<And>h. h \<in> set (distinct_bool_heads ?col_pats) \<Longrightarrow> colTys ! c = CoreTy_Bool"
          by blast
        have IH_heads:
          "\<And>h. h \<in> set (distinct_bool_heads ?col_pats) \<Longrightarrow>
             arm_patterns_compatible env g (compile_matrix
               (drop_at c scruts, List.map_filter (specialise_row_bool c h) rows))"
        proof -
          fix h assume h_in: "h \<in> set (distinct_bool_heads ?col_pats)"
          from matrix_inv_specialise_bool[OF inv c_lt, of h]
          have inv': "matrix_inv env g (drop_at c colTys)
                       (drop_at c scruts, List.map_filter (specialise_row_bool c h) rows)" .
          have ne: "snd (drop_at c scruts, List.map_filter (specialise_row_bool c h) rows) \<noteq> []"
            using specialise_bool_rows_nonempty[OF h_in] by simp
          from "1.IH"(4)[OF col_some _ _ _ _ _ head_kind_some HK_Bool _ inv' ne wf]
          show "arm_patterns_compatible env g (compile_matrix
                  (drop_at c scruts, List.map_filter (specialise_row_bool c h) rows))"
            by auto
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
        show ?thesis
          unfolding unfolded arm_patterns_compatible.simps
          using sc_at_c col_c_bool IH_heads IH_default
          by (auto simp: list_all_iff split: option.splits if_splits)
      next
        case HK_Int
        from col_type_int[OF rows_inv _ c_lt]
        have col_c_int: "\<And>h. h \<in> set (distinct_int_heads ?col_pats) \<Longrightarrow> is_integer_type (colTys ! c)"
          by blast
        have IH_heads:
          "\<And>h. h \<in> set (distinct_int_heads ?col_pats) \<Longrightarrow>
             arm_patterns_compatible env g (compile_matrix
               (drop_at c scruts, List.map_filter (specialise_row_int c h) rows))"
        proof -
          fix h assume h_in: "h \<in> set (distinct_int_heads ?col_pats)"
          from matrix_inv_specialise_int[OF inv c_lt, of h]
          have inv': "matrix_inv env g (drop_at c colTys)
                       (drop_at c scruts, List.map_filter (specialise_row_int c h) rows)" .
          have ne: "snd (drop_at c scruts, List.map_filter (specialise_row_int c h) rows) \<noteq> []"
            using specialise_int_rows_nonempty[OF h_in] by simp
          from "1.IH"(5)[OF col_some _ _ _ _ _ head_kind_some HK_Int _ inv' ne wf]
          show "arm_patterns_compatible env g (compile_matrix
                  (drop_at c scruts, List.map_filter (specialise_row_int c h) rows))"
            by auto
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
        show ?thesis
          unfolding unfolded arm_patterns_compatible.simps
          using sc_at_c col_c_int IH_heads IH_default
          by (auto simp: list_all_iff split: option.splits if_splits)
      next
        case HK_Variant
        have IH_heads:
          "\<And>h. h \<in> set (distinct_variant_heads ?col_pats) \<Longrightarrow>
             pattern_compatible env (CorePat_Variant h CorePat_Wildcard) (colTys ! c)
           \<and> arm_patterns_compatible env g (compile_matrix
                (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                 List.map_filter (specialise_row_variant c h) rows))"
        proof -
          fix h assume h_in: "h \<in> set (distinct_variant_heads ?col_pats)"
          from col_type_variant[OF rows_inv h_in c_lt]
          obtain dtName tyArgs tyvars payloadTy where
            col_c: "colTys ! c = CoreTy_Datatype dtName tyArgs" and
            lookup: "fmlookup (TE_DataCtors env) h = Some (dtName, tyvars, payloadTy)" and
            len_ty: "length tyArgs = length tyvars"
            by metis
          have pat_compat:
            "pattern_compatible env (CorePat_Variant h CorePat_Wildcard) (colTys ! c)"
            using col_c lookup len_ty by simp
          from matrix_inv_specialise_variant[OF inv c_lt col_c lookup len_ty wf]
          have inv': "matrix_inv env g
                       (replace_at c (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy) colTys)
                       (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                        List.map_filter (specialise_row_variant c h) rows)" .
          have ne:
            "snd (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                  List.map_filter (specialise_row_variant c h) rows) \<noteq> []"
            using specialise_variant_rows_nonempty[OF h_in] by simp
          from "1.IH"(3)[OF col_some _ _ _ _ _ head_kind_some HK_Variant _ _ inv' ne wf]
          show "pattern_compatible env (CorePat_Variant h CorePat_Wildcard) (colTys ! c)
              \<and> arm_patterns_compatible env g (compile_matrix
                   (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                    List.map_filter (specialise_row_variant c h) rows))"
            using pat_compat by auto
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
        show ?thesis
          unfolding unfolded arm_patterns_compatible.simps
          using sc_at_c IH_heads IH_default
          by (auto simp: list_all_iff split: option.splits if_splits)
      next
        case (HK_Record fld_names)
        from head_kind_some HK_Record nw_col_eq
        have head_record:
          "head_kind_of (ps0 ! c) = Some (HK_Record fld_names)" by simp
        then obtain pflds where
          ps0_c_eq: "ps0 ! c = CorePat_Record pflds" and
          fld_names_eq: "fld_names = map fst pflds"
          by (cases "ps0 ! c") auto
        from rows_eq r0_eq have r0_in: "r0 \<in> set rows" by simp
        from rows_inv r0_in r0_eq have
          ps0_pcs: "list_all2 (pattern_compatible env) ps0 colTys"
          by (auto simp: list_all_iff)
        from list_all2_nth[OF ps0_pcs] c_lt
        have ps0_at_c_pc: "pattern_compatible env (ps0 ! c) (colTys ! c)"
          using rows_inv r0_in r0_eq by (auto simp: list_all_iff)
        with ps0_c_eq have
          "pattern_compatible env (CorePat_Record pflds) (colTys ! c)" by simp
        from pattern_compatible_record_inv[OF this]
        obtain fldTys where
          col_c_rec: "colTys ! c = CoreTy_Record fldTys" and
          la2: "list_all2 (\<lambda>(pn, p) (fn, fty). pn = fn \<and> pattern_compatible env p fty)
                          pflds fldTys"
          by metis
        have names_eq: "map fst pflds = map fst fldTys"
          using la2 by (induction pflds fldTys rule: list_all2_induct) auto
        have fld_names_eq': "fld_names = map fst fldTys"
          using fld_names_eq names_eq by simp
        from matrix_inv_expand_record[OF inv c_lt col_c_rec fld_names_eq']
        have inv': "matrix_inv env g (splice_at c (map snd fldTys) colTys)
                     (expand_record_scruts c (scruts ! c) fld_names scruts,
                      map (expand_record_row c fld_names) rows)" .
        have ne:
          "snd (expand_record_scruts c (scruts ! c) fld_names scruts,
                map (expand_record_row c fld_names) rows) \<noteq> []"
          using rows_ne by simp
        from "1.IH"(2)[OF col_some _ _ _ _ _ head_kind_some HK_Record inv' ne wf]
        have rec_compat: "arm_patterns_compatible env g (compile_matrix
                            (expand_record_scruts c (scruts ! c) fld_names scruts,
                             map (expand_record_row c fld_names) rows))"
          by auto
        have unfolded:
          "compile_matrix (scruts, rows) =
             compile_matrix (expand_record_scruts c (scruts ! c) fld_names scruts,
                             map (expand_record_row c fld_names) rows)"
          using col_some head_kind_some HK_Record
          by (simp add: case_prod_unfold Let_def)
        from unfolded rec_compat show ?thesis by simp
      qed
    qed
  qed
qed


section \<open>Headline theorems for compile_match\<close>

(* The two deliverables of the type-preservation layer, stated for the
   compile_match entry point. *)

theorem compile_match_arm_patterns_compatible:
  assumes "core_term_type env g scrut = Some scrutTy"
  assumes "is_well_kinded env scrutTy"
  assumes "arms \<noteq> []"
  assumes "list_all (\<lambda>(p, _). pattern_compatible env p scrutTy) arms"
  assumes "tyenv_well_formed env"
  shows   "arm_patterns_compatible env g (compile_match scrut scrutTy arms)"
proof -
  let ?m = "([scrut], map (\<lambda>(p, b). ([p], b)) arms)"
  have inv: "matrix_inv env g [scrutTy] ?m"
    unfolding matrix_inv_def
    using assms(1,2,4) by (auto simp: list_all_iff)
  have ne: "snd ?m \<noteq> []" using assms(3) by simp
  from compile_matrix_arm_patterns_compatible[OF inv ne assms(5)]
  show ?thesis unfolding compile_match_def by simp
qed

theorem compile_match_bodies_subset:
  assumes "arms \<noteq> []"
  shows   "match_tree_bodies (compile_match scrut scrutTy arms) \<subseteq> set (map snd arms)"
proof -
  let ?m = "([scrut], map (\<lambda>(p, b). ([p], b)) arms)"
  have ne: "snd ?m \<noteq> []" using assms by simp
  have "match_tree_bodies (compile_matrix ?m) \<subseteq> set (map snd (snd ?m))"
    using compile_matrix_bodies_subset[OF ne] .
  also have "set (map snd (snd ?m)) = set (map snd arms)"
    by (induction arms) auto
  finally show ?thesis unfolding compile_match_def .
qed

end
