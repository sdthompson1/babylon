theory Unify
  imports "../core/CoreSyntax" "../core/MetaSubst" "../core/CoreTypeProps"
begin

(* ========================================================================== *)
(* Type unification algorithm *)
(* ========================================================================== *)

(* Unifies two CoreTypes, returning a most general unifier if one exists, or None if
   unification fails (incompatible types or occurs check). *)

function (domintros) unify :: "CoreType \<Rightarrow> CoreType \<Rightarrow> MetaSubst option"
and unify_list :: "CoreType list \<Rightarrow> CoreType list \<Rightarrow> MetaSubst option" where
  "unify (CoreTy_Name name1 tyArgs1) ty2 =
    (case ty2 of
      CoreTy_Meta n \<Rightarrow>
        if occurs n (CoreTy_Name name1 tyArgs1) then None
        else Some (singleton_subst n (CoreTy_Name name1 tyArgs1))
    | CoreTy_Name name2 tyArgs2 \<Rightarrow>
        if name1 = name2 then unify_list tyArgs1 tyArgs2 else None
    | _ \<Rightarrow> None)"

| "unify CoreTy_Bool ty2 =
    (case ty2 of
      CoreTy_Meta n \<Rightarrow> Some (singleton_subst n CoreTy_Bool)
    | CoreTy_Bool \<Rightarrow> Some fmempty
    | _ \<Rightarrow> None)"

| "unify (CoreTy_FiniteInt sign bits) ty2 =
    (case ty2 of
      CoreTy_Meta n \<Rightarrow> Some (singleton_subst n (CoreTy_FiniteInt sign bits))
    | CoreTy_FiniteInt sign' bits' \<Rightarrow>
        if sign = sign' \<and> bits = bits' then Some fmempty else None
    | _ \<Rightarrow> None)"

| "unify CoreTy_MathInt ty2 =
    (case ty2 of
      CoreTy_Meta n \<Rightarrow> Some (singleton_subst n CoreTy_MathInt)
    | CoreTy_MathInt \<Rightarrow> Some fmempty
    | _ \<Rightarrow> None)"

| "unify CoreTy_MathReal ty2 =
    (case ty2 of
      CoreTy_Meta n \<Rightarrow> Some (singleton_subst n CoreTy_MathReal)
    | CoreTy_MathReal \<Rightarrow> Some fmempty
    | _ \<Rightarrow> None)"

| "unify (CoreTy_Record flds1) ty2 =
    (case ty2 of
      CoreTy_Meta n \<Rightarrow>
        if occurs n (CoreTy_Record flds1) then None
        else Some (singleton_subst n (CoreTy_Record flds1))
    | CoreTy_Record flds2 \<Rightarrow>
        if map fst flds1 = map fst flds2
        then unify_list (map snd flds1) (map snd flds2)
        else None
    | _ \<Rightarrow> None)"

| "unify (CoreTy_Array elemTy1 dims1) ty2 =
    (case ty2 of
      CoreTy_Meta n \<Rightarrow>
        if occurs n (CoreTy_Array elemTy1 dims1) then None
        else Some (singleton_subst n (CoreTy_Array elemTy1 dims1))
    | CoreTy_Array elemTy2 dims2 \<Rightarrow>
        if dims1 = dims2 then unify elemTy1 elemTy2 else None
    | _ \<Rightarrow> None)"

| "unify (CoreTy_Meta n) ty2 =
    (if occurs n ty2 \<and> ty2 \<noteq> CoreTy_Meta n then None
     else if ty2 = CoreTy_Meta n then Some fmempty
     else Some (singleton_subst n ty2))"

| "unify_list [] [] = Some fmempty"

| "unify_list [] (ty # tys) = None"

| "unify_list (ty # tys) [] = None"

| "unify_list (ty1 # tys1) (ty2 # tys2) =
    (case unify ty1 ty2 of
      None \<Rightarrow> None
    | Some subst1 \<Rightarrow>
        (case unify_list (map (apply_subst subst1) tys1)
                         (map (apply_subst subst1) tys2) of
          None \<Rightarrow> None
        | Some subst2 \<Rightarrow> Some (compose_subst subst2 subst1)))"

by pat_completeness auto


(* ========================================================================== *)
(* Termination proof                                                          *)
(* ========================================================================== *)

(* Custom size function for CoreType that returns at least 1 for every type *)
fun core_type_size :: "CoreType \<Rightarrow> nat" where
  "core_type_size (CoreTy_Name _ tyargs) = 1 + sum_list (map core_type_size tyargs)"
| "core_type_size CoreTy_Bool = 1"
| "core_type_size (CoreTy_FiniteInt _ _) = 1"
| "core_type_size CoreTy_MathInt = 1"
| "core_type_size CoreTy_MathReal = 1"
| "core_type_size (CoreTy_Record flds) = 1 + sum_list (map (core_type_size \<circ> snd) flds)"
| "core_type_size (CoreTy_Array elemTy _) = 1 + core_type_size elemTy"
| "core_type_size (CoreTy_Meta _) = 1"

(* Size of a list of types *)
definition list_type_size :: "CoreType list \<Rightarrow> nat" where
  "list_type_size tys = sum_list (map core_type_size tys)"

(* Basic size lemmas *)
lemma core_type_size_pos: "0 < core_type_size ty"
  by (cases ty) auto

lemma list_type_size_cons:
  "list_type_size (ty # tys) = core_type_size ty + list_type_size tys"
  by (simp add: list_type_size_def)

lemma type_args_size_smaller:
  "list_type_size args < core_type_size (CoreTy_Name name args)"
  by (simp add: list_type_size_def)

lemma record_size_smaller:
  "list_type_size (map snd flds) < core_type_size (CoreTy_Record flds)"
  by (simp add: list_type_size_def comp_def)

lemma array_elem_size_smaller:
  "core_type_size elem < core_type_size (CoreTy_Array elem dims)"
  by simp

lemma list_metavars_cons:
  "list_metavars (ty # tys) = type_metavars ty \<union> list_metavars tys"
  by (simp add: list_metavars_def)

(* The termination relation: lexicographic on (card of metavars, size, tag)
   where tag is 0 for Inl (unify) and 1 for Inr (unify_list). *)
definition unify_rel :: "((CoreType \<times> CoreType) + (CoreType list \<times> CoreType list)) rel" where
  "unify_rel = inv_image (less_than <*lex*> less_than <*lex*> less_than)
    (\<lambda>x. case x of
      Inl (ty1, ty2) \<Rightarrow> (card (type_metavars ty1 \<union> type_metavars ty2),
                         core_type_size ty1 + core_type_size ty2,
                         0::nat)
    | Inr (tys1, tys2) \<Rightarrow> (card (list_metavars tys1 \<union> list_metavars tys2),
                           list_type_size tys1 + list_type_size tys2,
                           1::nat))"

lemma wf_unify_rel: "wf unify_rel"
  unfolding unify_rel_def by auto

(* Lemmas about when recursive calls are in unify_rel *)

(* Calling unify_list args1 args2 from unify (Name n1 args1) (Name n2 args2) is smaller *)
lemma unify_rel_name_to_list:
  "(Inr (args1, args2), Inl (CoreTy_Name n1 args1, CoreTy_Name n2 args2)) \<in> unify_rel"
proof -
  have "list_type_size args1 + list_type_size args2 <
        core_type_size (CoreTy_Name n1 args1) + core_type_size (CoreTy_Name n2 args2)"
    by (meson add_less_mono type_args_size_smaller)
  moreover have "list_metavars args1 \<union> list_metavars args2 =
                 type_metavars (CoreTy_Name n1 args1) \<union> type_metavars (CoreTy_Name n2 args2)"
    by (auto simp: list_metavars_def)
  ultimately show ?thesis
    unfolding unify_rel_def by auto
qed

(* Calling unify_list (map snd flds1) (map snd flds2) from unify (Record flds1) (Record flds2) is smaller *)
lemma unify_rel_record_to_list:
  "(Inr (map snd flds1, map snd flds2), Inl (CoreTy_Record flds1, CoreTy_Record flds2)) \<in> unify_rel"
proof -
  have "list_type_size (map snd flds1) + list_type_size (map snd flds2) <
        core_type_size (CoreTy_Record flds1) + core_type_size (CoreTy_Record flds2)"
    by (meson add_less_mono record_size_smaller)
  moreover have "list_metavars (map snd flds1) \<union> list_metavars (map snd flds2) =
                 type_metavars (CoreTy_Record flds1) \<union> type_metavars (CoreTy_Record flds2)"
    by (auto simp: list_metavars_def comp_def)
  ultimately show ?thesis
    unfolding unify_rel_def by auto
qed

(* Calling unify elem1 elem2 from unify (Array elem1 dims1) (Array elem2 dims2) is smaller *)
lemma unify_rel_array_to_elem:
  "(Inl (elem1, elem2), Inl (CoreTy_Array elem1 dims1, CoreTy_Array elem2 dims2)) \<in> unify_rel"
proof -
  have "core_type_size elem1 + core_type_size elem2 <
        core_type_size (CoreTy_Array elem1 dims1) + core_type_size (CoreTy_Array elem2 dims2)"
    by (meson add_less_mono array_elem_size_smaller)
  moreover have "type_metavars elem1 \<union> type_metavars elem2 =
                 type_metavars (CoreTy_Array elem1 dims1) \<union> type_metavars (CoreTy_Array elem2 dims2)"
    by auto
  ultimately show ?thesis
    unfolding unify_rel_def by auto
qed

(* Calling unify head1 head2 from unify_list (head1 # rest1) (head2 # rest2) is smaller *)
lemma unify_rel_list_to_head:
  "(Inl (head1, head2), Inr (head1 # rest1, head2 # rest2)) \<in> unify_rel"
proof -
  have mv_subset: "type_metavars head1 \<union> type_metavars head2 \<subseteq>
        list_metavars (head1 # rest1) \<union> list_metavars (head2 # rest2)"
    by (auto simp: list_metavars_def)
  hence mv_card: "card (type_metavars head1 \<union> type_metavars head2) \<le>
            card (list_metavars (head1 # rest1) \<union> list_metavars (head2 # rest2))"
    by (simp add: card_mono finite_list_metavars)
  have size_le: "core_type_size head1 + core_type_size head2 \<le>
                 list_type_size (head1 # rest1) + list_type_size (head2 # rest2)"
    by (simp add: list_type_size_cons)
  show ?thesis
    unfolding unify_rel_def
    using mv_card size_le by auto
qed

(* Properties that a substitution from unify/unify_list must satisfy *)
definition subst_props :: "nat set \<Rightarrow> MetaSubst \<Rightarrow> bool" where
  "subst_props mvs subst \<equiv>
    fset (fmdom subst) \<subseteq> mvs \<and>
    (\<forall>n ty. fmlookup subst n = Some ty \<longrightarrow> type_metavars ty \<subseteq> mvs) \<and>
    fset (fmdom subst) \<inter> subst_range_mvs subst = {}"

definition unify_input_mvs :: "CoreType \<Rightarrow> CoreType \<Rightarrow> nat set" where
  "unify_input_mvs ty1 ty2 = type_metavars ty1 \<union> type_metavars ty2"

definition unify_list_input_mvs :: "CoreType list \<Rightarrow> CoreType list \<Rightarrow> nat set" where
  "unify_list_input_mvs tys1 tys2 = list_metavars tys1 \<union> list_metavars tys2"

(* Empty substitution trivially satisfies the properties *)
lemma subst_props_empty [simp]: "subst_props mvs fmempty"
  by (simp add: subst_props_def)

(* Singleton substitution satisfies properties when constructed correctly *)
lemma subst_props_singleton:
  assumes "n \<in> mvs"
      and "type_metavars ty \<subseteq> mvs"
      and "\<not> occurs n ty"
  shows "subst_props mvs (singleton_subst n ty)"
  using assms
  by (auto simp: subst_props_def singleton_subst_def subst_range_mvs_def occurs_def fmran'_def)

(* If subst satisfies props for mvs, applying it to types with metavars in mvs
   results in types whose metavars are still in mvs *)
lemma apply_subst_metavars_subset:
  assumes "subst_props mvs subst"
      and "type_metavars ty \<subseteq> mvs"
  shows "type_metavars (apply_subst subst ty) \<subseteq> mvs"
proof -
  from assms(1) have dom_sub: "fset (fmdom subst) \<subseteq> mvs"
    by (simp add: subst_props_def)
  from assms(1) have range_sub: "subst_range_mvs subst \<subseteq> mvs"
    by (auto simp: subst_props_def subst_range_mvs_def fmran'_def)
  have "type_metavars (apply_subst subst ty) \<subseteq>
        (type_metavars ty - fset (fmdom subst)) \<union> subst_range_mvs subst"
    by (rule apply_subst_metavars_result)
  also have "... \<subseteq> mvs"
    using assms(2) range_sub by auto
  finally show ?thesis .
qed

(* Composition preserves properties *)
lemma subst_props_compose:
  assumes props1: "subst_props mvs subst1"
      and props2: "subst_props mvs subst2"
      and dom_disj: "fset (fmdom subst2) \<inter> fset (fmdom subst1) = {}"
      and range2_disj: "subst_range_mvs subst2 \<inter> fset (fmdom subst1) = {}"
  shows "subst_props mvs (compose_subst subst2 subst1)"
  unfolding subst_props_def
proof (intro conjI)
  (* Domain of composition is union of domains, both subsets of mvs *)
  show "fset (fmdom (compose_subst subst2 subst1)) \<subseteq> mvs"
  proof -
    have "fmdom (compose_subst subst2 subst1) = fmdom subst2 |\<union>| fmdom subst1"
      by (simp add: compose_subst_def)
    moreover have "fset (fmdom subst1) \<subseteq> mvs" and "fset (fmdom subst2) \<subseteq> mvs"
      using props1 props2 by (auto simp: subst_props_def)
    ultimately show ?thesis by auto
  qed
next
  (* For each binding in the composition, range metavars are in mvs *)
  show "\<forall>n ty. fmlookup (compose_subst subst2 subst1) n = Some ty \<longrightarrow>
               type_metavars ty \<subseteq> mvs"
  proof (intro allI impI)
    fix n ty
    assume lookup: "fmlookup (compose_subst subst2 subst1) n = Some ty"

    show "type_metavars ty \<subseteq> mvs"
    proof (cases "fmlookup subst1 n")
      case None
      hence "fmlookup subst2 n = Some ty"
        using lookup by (simp add: fmlookup_compose_subst_None1)
      thus ?thesis
        using props2 by (auto simp: subst_props_def)
    next
      case (Some ty1)
      hence ty_eq: "ty = apply_subst subst2 ty1"
        using lookup by (simp add: fmlookup_compose_subst_Some1)
      from Some props1 have ty1_mvs: "type_metavars ty1 \<subseteq> mvs"
        by (auto simp: subst_props_def)
      show ?thesis
        using ty_eq ty1_mvs props2 by (simp add: apply_subst_metavars_subset)
    qed
  qed
next
  (* Domain and range of composition are disjoint *)
  show "fset (fmdom (compose_subst subst2 subst1)) \<inter> subst_range_mvs (compose_subst subst2 subst1) = {}"
  proof -
    have dom_eq: "fmdom (compose_subst subst2 subst1) = fmdom subst2 |\<union>| fmdom subst1"
      by (simp add: compose_subst_def)
    (* Range of compose_subst subst2 subst1:
       For n in dom(subst1): apply_subst subst2 (subst1 n)
       For n in dom(subst2) \ dom(subst1): subst2 n *)
    have range_sub: "subst_range_mvs (compose_subst subst2 subst1) \<subseteq>
                     subst_range_mvs subst2 \<union> subst_range_mvs subst1"
    proof
      fix x assume "x \<in> subst_range_mvs (compose_subst subst2 subst1)"
      then obtain ty where ty_in: "ty \<in> fmran' (compose_subst subst2 subst1)"
                       and x_in: "x \<in> type_metavars ty"
        by (auto simp: subst_range_mvs_def)
      from ty_in obtain n where lookup: "fmlookup (compose_subst subst2 subst1) n = Some ty"
        by (auto simp: fmran'_def)
      show "x \<in> subst_range_mvs subst2 \<union> subst_range_mvs subst1"
      proof (cases "fmlookup subst1 n")
        case None
        hence "fmlookup subst2 n = Some ty"
          using lookup by (simp add: fmlookup_compose_subst_None1)
        hence "ty \<in> fmran' subst2" by (auto simp: fmran'_def)
        thus ?thesis using x_in by (auto simp: subst_range_mvs_def)
      next
        case (Some ty1)
        hence ty_eq: "ty = apply_subst subst2 ty1"
          using lookup by (simp add: fmlookup_compose_subst_Some1)
        have ty1_in: "ty1 \<in> fmran' subst1" using Some by (auto simp: fmran'_def)
        from x_in[unfolded ty_eq] have "x \<in> type_metavars (apply_subst subst2 ty1)" .
        hence "x \<in> (type_metavars ty1 - fset (fmdom subst2)) \<union> subst_range_mvs subst2"
          using apply_subst_metavars_result by auto
        thus ?thesis
        proof
          assume "x \<in> type_metavars ty1 - fset (fmdom subst2)"
          hence "x \<in> type_metavars ty1" by auto
          thus ?thesis using ty1_in by (auto simp: subst_range_mvs_def)
        next
          assume "x \<in> subst_range_mvs subst2"
          thus ?thesis by auto
        qed
      qed
    qed
    (* Show disjointness directly *)
    have no_overlap: "\<And>n. n \<in> fset (fmdom (compose_subst subst2 subst1)) \<Longrightarrow>
                          n \<notin> subst_range_mvs (compose_subst subst2 subst1)"
    proof -
      fix n
      assume n_in_dom: "n \<in> fset (fmdom (compose_subst subst2 subst1))"
      from n_in_dom have n_cases: "n \<in> fset (fmdom subst1) \<or> n \<in> fset (fmdom subst2)"
        using dom_eq by auto
      show "n \<notin> subst_range_mvs (compose_subst subst2 subst1)"
      proof (cases "n \<in> fset (fmdom subst1)")
        case True
        (* n is in dom(subst1), so n \<notin> range(subst1) and n \<notin> range(subst2) by range2_disj *)
        have n_not_in_range1: "n \<notin> subst_range_mvs subst1"
          using props1 True by (auto simp: subst_props_def)
        have n_not_in_range2: "n \<notin> subst_range_mvs subst2"
          using range2_disj True by auto
        from range_sub n_not_in_range1 n_not_in_range2
        show ?thesis by auto
      next
        case False
        (* n \<in> dom(subst2) but n \<notin> dom(subst1) *)
        with n_cases have n_in_dom2: "n \<in> fset (fmdom subst2)" by auto
        have n_not_in_range2: "n \<notin> subst_range_mvs subst2"
          using props2 n_in_dom2 by (auto simp: subst_props_def)
        (* Show n is not in range of composition *)
        show ?thesis
        proof
          assume n_in_range: "n \<in> subst_range_mvs (compose_subst subst2 subst1)"
          from n_in_range obtain ty where ty_in: "ty \<in> fmran' (compose_subst subst2 subst1)"
                                      and n_in_ty: "n \<in> type_metavars ty"
            by (auto simp: subst_range_mvs_def)
          from ty_in obtain m where lookup: "fmlookup (compose_subst subst2 subst1) m = Some ty"
            by (auto simp: fmran'_def)
          show False
          proof (cases "fmlookup subst1 m")
            case None
            hence "fmlookup subst2 m = Some ty"
              using lookup by (simp add: fmlookup_compose_subst_None1)
            hence "ty \<in> fmran' subst2" by (auto simp: fmran'_def)
            hence "n \<in> subst_range_mvs subst2" using n_in_ty by (auto simp: subst_range_mvs_def)
            thus False using n_not_in_range2 by simp
          next
            case (Some ty1)
            hence ty_eq: "ty = apply_subst subst2 ty1"
              using lookup by (simp add: fmlookup_compose_subst_Some1)
            from n_in_ty[unfolded ty_eq]
            have "n \<in> (type_metavars ty1 - fset (fmdom subst2)) \<union> subst_range_mvs subst2"
              using apply_subst_metavars_result by auto
            thus False
            proof
              assume "n \<in> type_metavars ty1 - fset (fmdom subst2)"
              thus False using n_in_dom2 by auto
            next
              assume "n \<in> subst_range_mvs subst2"
              thus False using n_not_in_range2 by simp
            qed
          qed
        qed
      qed
    qed
    show ?thesis using no_overlap by auto
  qed
qed

(* The recursive unify_list call after unifying heads is smaller *)
lemma unify_rel_list_recursive:
  assumes "subst_props (type_metavars ty1 \<union> type_metavars ty2) subst"
  shows "(Inr (map (apply_subst subst) rest1, map (apply_subst subst) rest2),
          Inr (ty1 # rest1, ty2 # rest2)) \<in> unify_rel"
proof (cases "subst = fmempty")
  case True
  (* With empty subst, size decreases since we remove heads *)
  have size_lt: "list_type_size (map (apply_subst subst) rest1) +
                 list_type_size (map (apply_subst subst) rest2)
              <  list_type_size (ty1 # rest1) + list_type_size (ty2 # rest2)"
    using True core_type_size_pos by (simp add: list_type_size_cons)
  moreover have "list_metavars (map (apply_subst subst) rest1) \<union> list_metavars (map (apply_subst subst) rest2)
                 \<subseteq> list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
    using True by (auto simp: list_metavars_def)
  hence "card (list_metavars (map (apply_subst subst) rest1) \<union> list_metavars (map (apply_subst subst) rest2))
         \<le> card (list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2))"
    by (simp add: card_mono finite_list_metavars)
  ultimately show ?thesis
    unfolding unify_rel_def by auto
next
  case False
  (* Non-empty subst: metavar count decreases *)
  from False obtain n ty where binding: "fmlookup subst n = Some ty"
    by (metis fmap_ext fmempty_lookup option.exhaust)
  have n_in_heads: "n \<in> type_metavars ty1 \<union> type_metavars ty2"
    using assms binding unfolding subst_props_def
    by (meson fmdomI in_mono)
  have n_in_dom: "n \<in> fset (fmdom subst)"
    using binding by (simp add: fmlookup_dom_iff)
  have n_not_in_range: "n \<notin> subst_range_mvs subst"
    using assms n_in_dom unfolding subst_props_def by auto
  have n_not_in_result: "n \<notin> list_metavars (map (apply_subst subst) rest1) \<union>
                              list_metavars (map (apply_subst subst) rest2)"
    using apply_subst_eliminates_dom[OF n_in_dom n_not_in_range]
    by (auto simp: list_metavars_def)
  have result_subset: "list_metavars (map (apply_subst subst) rest1) \<union>
                       list_metavars (map (apply_subst subst) rest2)
                       \<subseteq> list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
  proof -
    have dom_sub: "fset (fmdom subst) \<subseteq> type_metavars ty1 \<union> type_metavars ty2"
      using assms unfolding subst_props_def by auto
    have range_sub: "subst_range_mvs subst \<subseteq> type_metavars ty1 \<union> type_metavars ty2"
      using assms unfolding subst_props_def subst_range_mvs_def
      by fastforce
    have "\<And>t. t \<in> set rest1 \<Longrightarrow> type_metavars (apply_subst subst t) \<subseteq>
              list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
    proof -
      fix t assume "t \<in> set rest1"
      have "type_metavars (apply_subst subst t) \<subseteq>
            (type_metavars t - fset (fmdom subst)) \<union> subst_range_mvs subst"
        by (rule apply_subst_metavars_result)
      also have "... \<subseteq> type_metavars t \<union> subst_range_mvs subst" by auto
      also have "... \<subseteq> list_metavars rest1 \<union> (type_metavars ty1 \<union> type_metavars ty2)"
        using \<open>t \<in> set rest1\<close> range_sub by (auto simp: list_metavars_def)
      also have "... \<subseteq> list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
        by (auto simp: list_metavars_def)
      finally show "type_metavars (apply_subst subst t) \<subseteq>
                    list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)" .
    qed
    moreover have "\<And>t. t \<in> set rest2 \<Longrightarrow> type_metavars (apply_subst subst t) \<subseteq>
              list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
    proof -
      fix t assume "t \<in> set rest2"
      have "type_metavars (apply_subst subst t) \<subseteq>
            (type_metavars t - fset (fmdom subst)) \<union> subst_range_mvs subst"
        by (rule apply_subst_metavars_result)
      also have "... \<subseteq> type_metavars t \<union> subst_range_mvs subst" by auto
      also have "... \<subseteq> list_metavars rest2 \<union> (type_metavars ty1 \<union> type_metavars ty2)"
        using \<open>t \<in> set rest2\<close> range_sub by (auto simp: list_metavars_def)
      also have "... \<subseteq> list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
        by (auto simp: list_metavars_def)
      finally show "type_metavars (apply_subst subst t) \<subseteq>
                    list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)" .
    qed
    ultimately show ?thesis by (auto simp: list_metavars_def)
  qed
  have n_in_orig: "n \<in> list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
    using n_in_heads by (auto simp: list_metavars_def)
  have strict_subset: "list_metavars (map (apply_subst subst) rest1) \<union>
                       list_metavars (map (apply_subst subst) rest2)
                       \<subset> list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
    using result_subset n_not_in_result n_in_orig by auto
  hence "card (list_metavars (map (apply_subst subst) rest1) \<union>
               list_metavars (map (apply_subst subst) rest2))
         < card (list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2))"
    using finite_list_metavars psubset_card_mono
    by (metis finite_Un)
  thus ?thesis
    unfolding unify_rel_def by auto
qed

(* The main inductive property: termination and props *)
definition unify_terminates_with_props ::
    "((CoreType \<times> CoreType) + (CoreType list \<times> CoreType list)) \<Rightarrow> bool" where
  "unify_terminates_with_props x \<equiv>
    unify_unify_list_dom x \<and>
    (case x of
      Inl (ty1, ty2) \<Rightarrow>
        (\<forall>subst. unify ty1 ty2 = Some subst \<longrightarrow>
                 subst_props (unify_input_mvs ty1 ty2) subst)
    | Inr (tys1, tys2) \<Rightarrow>
        (\<forall>subst. unify_list tys1 tys2 = Some subst \<longrightarrow>
                 subst_props (unify_list_input_mvs tys1 tys2) subst))"

(* The main theorem: all inputs terminate with props. *)
lemma unify_terminates_with_props_all:
  "unify_terminates_with_props x"
proof (induction x rule: wf_induct_rule[OF wf_unify_rel])
  case (1 x)
  (* IH: for all y with (y, x) \<in> unify_rel, unify_terminates_with_props y *)
  show ?case
  proof (cases x)
    case (Inl pair)
    obtain ty1 ty2 where pair_eq: "pair = (ty1, ty2)" by (cases pair)

    (* Need to show domain holds and props hold for unify ty1 ty2 *)
    show ?thesis
    proof (cases ty1)
      case (CoreTy_Meta n)
      (* When ty1 is a metavar, result depends on ty2 *)
      show ?thesis
        using Inl pair_eq CoreTy_Meta
      proof (cases ty2)
        case (CoreTy_Meta m)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Meta n, CoreTy_Meta m))"
          by (rule unify_unify_list.domintros)
        show ?thesis
        proof (cases "n = m")
          case True
          have result: "unify (CoreTy_Meta n) (CoreTy_Meta m) = Some fmempty"
            using dom True by (simp add: unify.psimps occurs_def)
          show ?thesis
            using Inl pair_eq \<open>ty1 = CoreTy_Meta n\<close> CoreTy_Meta dom result True
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have result: "unify (CoreTy_Meta n) (CoreTy_Meta m) = Some (singleton_subst n (CoreTy_Meta m))"
            using dom False by (simp add: unify.psimps occurs_def)
          have props: "subst_props (unify_input_mvs (CoreTy_Meta n) (CoreTy_Meta m)) (singleton_subst n (CoreTy_Meta m))"
            using False by (auto simp: unify_input_mvs_def intro: subst_props_singleton simp: occurs_def)
          show ?thesis
            using Inl pair_eq \<open>ty1 = CoreTy_Meta n\<close> CoreTy_Meta dom result props
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case (CoreTy_Name name2 args2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Meta n, CoreTy_Name name2 args2))"
          by (rule unify_unify_list.domintros)
        show ?thesis
        proof (cases "occurs n (CoreTy_Name name2 args2)")
          case True
          have result: "unify (CoreTy_Meta n) (CoreTy_Name name2 args2) = None"
            using dom True by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq \<open>ty1 = CoreTy_Meta n\<close> CoreTy_Name dom result
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have result: "unify (CoreTy_Meta n) (CoreTy_Name name2 args2) = Some (singleton_subst n (CoreTy_Name name2 args2))"
            using dom False by (simp add: unify.psimps)
          have props: "subst_props (unify_input_mvs (CoreTy_Meta n) (CoreTy_Name name2 args2)) (singleton_subst n (CoreTy_Name name2 args2))"
            using False by (auto simp: unify_input_mvs_def intro: subst_props_singleton)
          show ?thesis
            using Inl pair_eq \<open>ty1 = CoreTy_Meta n\<close> CoreTy_Name dom result props
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case CoreTy_Bool
        have dom: "unify_unify_list_dom (Inl (CoreTy_Meta n, CoreTy_Bool))"
          by (rule unify_unify_list.domintros)
        have result: "unify (CoreTy_Meta n) CoreTy_Bool = Some (singleton_subst n CoreTy_Bool)"
          using dom by (simp add: unify.psimps occurs_def)
        have props: "subst_props (unify_input_mvs (CoreTy_Meta n) CoreTy_Bool) (singleton_subst n CoreTy_Bool)"
          by (auto simp: unify_input_mvs_def intro: subst_props_singleton simp: occurs_def)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_Meta n\<close> CoreTy_Bool dom result props
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_FiniteInt sign2 bits2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Meta n, CoreTy_FiniteInt sign2 bits2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (CoreTy_Meta n) (CoreTy_FiniteInt sign2 bits2) = Some (singleton_subst n (CoreTy_FiniteInt sign2 bits2))"
          using dom by (simp add: unify.psimps occurs_def)
        have props: "subst_props (unify_input_mvs (CoreTy_Meta n) (CoreTy_FiniteInt sign2 bits2)) (singleton_subst n (CoreTy_FiniteInt sign2 bits2))"
          by (auto simp: unify_input_mvs_def intro: subst_props_singleton simp: occurs_def)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_Meta n\<close> CoreTy_FiniteInt dom result props
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_MathInt
        have dom: "unify_unify_list_dom (Inl (CoreTy_Meta n, CoreTy_MathInt))"
          by (rule unify_unify_list.domintros)
        have result: "unify (CoreTy_Meta n) CoreTy_MathInt = Some (singleton_subst n CoreTy_MathInt)"
          using dom by (simp add: unify.psimps occurs_def)
        have props: "subst_props (unify_input_mvs (CoreTy_Meta n) CoreTy_MathInt) (singleton_subst n CoreTy_MathInt)"
          by (auto simp: unify_input_mvs_def intro: subst_props_singleton simp: occurs_def)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_Meta n\<close> CoreTy_MathInt dom result props
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_MathReal
        have dom: "unify_unify_list_dom (Inl (CoreTy_Meta n, CoreTy_MathReal))"
          by (rule unify_unify_list.domintros)
        have result: "unify (CoreTy_Meta n) CoreTy_MathReal = Some (singleton_subst n CoreTy_MathReal)"
          using dom by (simp add: unify.psimps occurs_def)
        have props: "subst_props (unify_input_mvs (CoreTy_Meta n) CoreTy_MathReal) (singleton_subst n CoreTy_MathReal)"
          by (auto simp: unify_input_mvs_def intro: subst_props_singleton simp: occurs_def)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_Meta n\<close> CoreTy_MathReal dom result props
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_Record flds2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Meta n, CoreTy_Record flds2))"
          by (rule unify_unify_list.domintros)
        show ?thesis
        proof (cases "occurs n (CoreTy_Record flds2)")
          case True
          have result: "unify (CoreTy_Meta n) (CoreTy_Record flds2) = None"
            using dom True by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq \<open>ty1 = CoreTy_Meta n\<close> CoreTy_Record dom result
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have result: "unify (CoreTy_Meta n) (CoreTy_Record flds2) = Some (singleton_subst n (CoreTy_Record flds2))"
            using dom False by (simp add: unify.psimps)
          have props: "subst_props (unify_input_mvs (CoreTy_Meta n) (CoreTy_Record flds2)) (singleton_subst n (CoreTy_Record flds2))"
            using False by (auto simp: unify_input_mvs_def intro: subst_props_singleton)
          show ?thesis
            using Inl pair_eq \<open>ty1 = CoreTy_Meta n\<close> CoreTy_Record dom result props
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case (CoreTy_Array elem2 dims2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Meta n, CoreTy_Array elem2 dims2))"
          by (rule unify_unify_list.domintros)
        show ?thesis
        proof (cases "occurs n (CoreTy_Array elem2 dims2)")
          case True
          have result: "unify (CoreTy_Meta n) (CoreTy_Array elem2 dims2) = None"
            using dom True by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq \<open>ty1 = CoreTy_Meta n\<close> CoreTy_Array dom result
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have result: "unify (CoreTy_Meta n) (CoreTy_Array elem2 dims2) = Some (singleton_subst n (CoreTy_Array elem2 dims2))"
            using dom False by (simp add: unify.psimps)
          have props: "subst_props (unify_input_mvs (CoreTy_Meta n) (CoreTy_Array elem2 dims2)) (singleton_subst n (CoreTy_Array elem2 dims2))"
            using False by (auto simp: unify_input_mvs_def intro: subst_props_singleton)
          show ?thesis
            using Inl pair_eq \<open>ty1 = CoreTy_Meta n\<close> CoreTy_Array dom result props
            by (auto simp: unify_terminates_with_props_def)
        qed
      qed
    next
      case CoreTy_Name1: (CoreTy_Name name1 args1)
      show ?thesis
        using Inl pair_eq CoreTy_Name1
      proof (cases ty2)
        case (CoreTy_Meta m)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Name name1 args1, CoreTy_Meta m))"
          using unify_unify_list.domintros(1) by auto
        show ?thesis
        proof (cases "occurs m (CoreTy_Name name1 args1)")
          case True
          have result: "unify (CoreTy_Name name1 args1) (CoreTy_Meta m) = None"
            using dom True by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq \<open>ty1 = CoreTy_Name name1 args1\<close> CoreTy_Meta dom result
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have result: "unify (CoreTy_Name name1 args1) (CoreTy_Meta m) = Some (singleton_subst m (CoreTy_Name name1 args1))"
            using dom False by (simp add: unify.psimps)
          have props: "subst_props (unify_input_mvs (CoreTy_Name name1 args1) (CoreTy_Meta m)) (singleton_subst m (CoreTy_Name name1 args1))"
            using False by (auto simp: unify_input_mvs_def intro: subst_props_singleton)
          show ?thesis
            using Inl pair_eq \<open>ty1 = CoreTy_Name name1 args1\<close> CoreTy_Meta dom result props
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case (CoreTy_Name name2 args2)
        show ?thesis
        proof (cases "name1 = name2")
          case False
          have dom: "unify_unify_list_dom (Inl (CoreTy_Name name1 args1, CoreTy_Name name2 args2))"
            using False unify_unify_list.domintros(1) by force
          have result: "unify (CoreTy_Name name1 args1) (CoreTy_Name name2 args2) = None"
            using dom False by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq CoreTy_Name1 CoreTy_Name dom result
            by (auto simp: unify_terminates_with_props_def)
        next
          case True
          (* Recursive call to unify_list args1 args2 *)
          have in_rel: "(Inr (args1, args2), Inl (CoreTy_Name name1 args1, CoreTy_Name name2 args2)) \<in> unify_rel"
            using True by (simp add: unify_rel_name_to_list)
          have ih: "unify_terminates_with_props (Inr (args1, args2))"
            by (simp add: "1" CoreTy_Name CoreTy_Name1 Inl in_rel pair_eq)
          hence list_dom: "unify_unify_list_dom (Inr (args1, args2))"
            and list_props: "\<And>subst. unify_list args1 args2 = Some subst \<Longrightarrow>
                                      subst_props (unify_list_input_mvs args1 args2) subst"
            by (auto simp: unify_terminates_with_props_def)
          have dom: "unify_unify_list_dom (Inl (CoreTy_Name name1 args1, CoreTy_Name name2 args2))"
            using list_dom True by (auto intro: unify_unify_list.domintros)
          have result_eq: "unify (CoreTy_Name name1 args1) (CoreTy_Name name2 args2) = unify_list args1 args2"
            using dom True by (simp add: unify.psimps)
          have mvs_eq: "unify_list_input_mvs args1 args2 = unify_input_mvs (CoreTy_Name name1 args1) (CoreTy_Name name2 args2)"
            by (auto simp: unify_list_input_mvs_def unify_input_mvs_def list_metavars_def)
          show ?thesis
            using Inl pair_eq CoreTy_Name1 CoreTy_Name dom result_eq list_props mvs_eq
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case CoreTy_Bool
        have dom: "unify_unify_list_dom (Inl (CoreTy_Name name1 args1, CoreTy_Bool))"
          using unify_unify_list.domintros(1) by auto
        have result: "unify (CoreTy_Name name1 args1) CoreTy_Bool = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_Name1 CoreTy_Bool dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_FiniteInt sign2 bits2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Name name1 args1, CoreTy_FiniteInt sign2 bits2))"
          using unify_unify_list.domintros(1) by auto
        have result: "unify (CoreTy_Name name1 args1) (CoreTy_FiniteInt sign2 bits2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_Name1 CoreTy_FiniteInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_MathInt
        have dom: "unify_unify_list_dom (Inl (CoreTy_Name name1 args1, CoreTy_MathInt))"
          using unify_unify_list.domintros(1) by auto
        have result: "unify (CoreTy_Name name1 args1) CoreTy_MathInt = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_Name1 CoreTy_MathInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_MathReal
        have dom: "unify_unify_list_dom (Inl (CoreTy_Name name1 args1, CoreTy_MathReal))"
          using unify_unify_list.domintros(1) by auto
        have result: "unify (CoreTy_Name name1 args1) CoreTy_MathReal = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_Name1 CoreTy_MathReal dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_Record flds2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Name name1 args1, CoreTy_Record flds2))"
          using unify_unify_list.domintros(1) by auto
        have result: "unify (CoreTy_Name name1 args1) (CoreTy_Record flds2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_Name1 CoreTy_Record dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_Array elem2 dims2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Name name1 args1, CoreTy_Array elem2 dims2))"
          using unify_unify_list.domintros(1) by auto
        have result: "unify (CoreTy_Name name1 args1) (CoreTy_Array elem2 dims2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_Name1 CoreTy_Array dom result
          by (auto simp: unify_terminates_with_props_def)
      qed
    next
      case CoreTy_Bool
      show ?thesis
        using Inl pair_eq CoreTy_Bool
      proof (cases ty2)
        case (CoreTy_Meta m)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Bool, CoreTy_Meta m))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_Bool (CoreTy_Meta m) = Some (singleton_subst m CoreTy_Bool)"
          using dom by (simp add: unify.psimps)
        have props: "subst_props (unify_input_mvs CoreTy_Bool (CoreTy_Meta m)) (singleton_subst m CoreTy_Bool)"
          by (auto simp: unify_input_mvs_def intro: subst_props_singleton simp: occurs_def)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_Bool\<close> CoreTy_Meta dom result props
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_Bool
        have dom: "unify_unify_list_dom (Inl (CoreTy_Bool, CoreTy_Bool))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_Bool CoreTy_Bool = Some fmempty"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_Bool\<close> CoreTy_Bool dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_Name name2 args2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Bool, CoreTy_Name name2 args2))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_Bool (CoreTy_Name name2 args2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_Bool\<close> CoreTy_Name dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_FiniteInt sign2 bits2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Bool, CoreTy_FiniteInt sign2 bits2))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_Bool (CoreTy_FiniteInt sign2 bits2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_Bool\<close> CoreTy_FiniteInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_MathInt
        have dom: "unify_unify_list_dom (Inl (CoreTy_Bool, CoreTy_MathInt))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_Bool CoreTy_MathInt = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_Bool\<close> CoreTy_MathInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_MathReal
        have dom: "unify_unify_list_dom (Inl (CoreTy_Bool, CoreTy_MathReal))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_Bool CoreTy_MathReal = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_Bool\<close> CoreTy_MathReal dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_Record flds2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Bool, CoreTy_Record flds2))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_Bool (CoreTy_Record flds2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_Bool\<close> CoreTy_Record dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_Array elem2 dims2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Bool, CoreTy_Array elem2 dims2))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_Bool (CoreTy_Array elem2 dims2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_Bool\<close> CoreTy_Array dom result
          by (auto simp: unify_terminates_with_props_def)
      qed
    next
      case CoreTy_FiniteInt1: (CoreTy_FiniteInt sign1 bits1)
      show ?thesis
        using Inl pair_eq CoreTy_FiniteInt1
      proof (cases ty2)
        case (CoreTy_Meta m)
        have dom: "unify_unify_list_dom (Inl (CoreTy_FiniteInt sign1 bits1, CoreTy_Meta m))"
          by (rule unify_unify_list.domintros)
        have result: "unify (CoreTy_FiniteInt sign1 bits1) (CoreTy_Meta m) = Some (singleton_subst m (CoreTy_FiniteInt sign1 bits1))"
          using dom by (simp add: unify.psimps)
        have props: "subst_props (unify_input_mvs (CoreTy_FiniteInt sign1 bits1) (CoreTy_Meta m)) (singleton_subst m (CoreTy_FiniteInt sign1 bits1))"
          by (auto simp: unify_input_mvs_def intro: subst_props_singleton simp: occurs_def)
        show ?thesis
          using Inl pair_eq CoreTy_FiniteInt1 CoreTy_Meta dom result props
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_FiniteInt sign2 bits2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_FiniteInt sign1 bits1, CoreTy_FiniteInt sign2 bits2))"
          by (rule unify_unify_list.domintros)
        show ?thesis
        proof (cases "sign1 = sign2 \<and> bits1 = bits2")
          case True
          have result: "unify (CoreTy_FiniteInt sign1 bits1) (CoreTy_FiniteInt sign2 bits2) = Some fmempty"
            using dom True by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq CoreTy_FiniteInt1 CoreTy_FiniteInt dom result
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have result: "unify (CoreTy_FiniteInt sign1 bits1) (CoreTy_FiniteInt sign2 bits2) = None"
            using dom False by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq CoreTy_FiniteInt1 CoreTy_FiniteInt dom result
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case (CoreTy_Name name2 args2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_FiniteInt sign1 bits1, CoreTy_Name name2 args2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (CoreTy_FiniteInt sign1 bits1) (CoreTy_Name name2 args2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_FiniteInt1 CoreTy_Name dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_Bool
        have dom: "unify_unify_list_dom (Inl (CoreTy_FiniteInt sign1 bits1, CoreTy_Bool))"
          by (rule unify_unify_list.domintros)
        have result: "unify (CoreTy_FiniteInt sign1 bits1) CoreTy_Bool = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_FiniteInt1 CoreTy_Bool dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_MathInt
        have dom: "unify_unify_list_dom (Inl (CoreTy_FiniteInt sign1 bits1, CoreTy_MathInt))"
          by (rule unify_unify_list.domintros)
        have result: "unify (CoreTy_FiniteInt sign1 bits1) CoreTy_MathInt = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_FiniteInt1 CoreTy_MathInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_MathReal
        have dom: "unify_unify_list_dom (Inl (CoreTy_FiniteInt sign1 bits1, CoreTy_MathReal))"
          by (rule unify_unify_list.domintros)
        have result: "unify (CoreTy_FiniteInt sign1 bits1) CoreTy_MathReal = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_FiniteInt1 CoreTy_MathReal dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_Record flds2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_FiniteInt sign1 bits1, CoreTy_Record flds2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (CoreTy_FiniteInt sign1 bits1) (CoreTy_Record flds2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_FiniteInt1 CoreTy_Record dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_Array elem2 dims2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_FiniteInt sign1 bits1, CoreTy_Array elem2 dims2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (CoreTy_FiniteInt sign1 bits1) (CoreTy_Array elem2 dims2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_FiniteInt1 CoreTy_Array dom result
          by (auto simp: unify_terminates_with_props_def)
      qed
    next
      case CoreTy_MathInt
      show ?thesis
        using Inl pair_eq CoreTy_MathInt
      proof (cases ty2)
        case (CoreTy_Meta m)
        have dom: "unify_unify_list_dom (Inl (CoreTy_MathInt, CoreTy_Meta m))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_MathInt (CoreTy_Meta m) = Some (singleton_subst m CoreTy_MathInt)"
          using dom by (simp add: unify.psimps)
        have props: "subst_props (unify_input_mvs CoreTy_MathInt (CoreTy_Meta m)) (singleton_subst m CoreTy_MathInt)"
          by (auto simp: unify_input_mvs_def intro: subst_props_singleton simp: occurs_def)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_MathInt\<close> CoreTy_Meta dom result props
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_MathInt
        have dom: "unify_unify_list_dom (Inl (CoreTy_MathInt, CoreTy_MathInt))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_MathInt CoreTy_MathInt = Some fmempty"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_MathInt\<close> CoreTy_MathInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_Name name2 args2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_MathInt, CoreTy_Name name2 args2))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_MathInt (CoreTy_Name name2 args2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_MathInt\<close> CoreTy_Name dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_Bool
        have dom: "unify_unify_list_dom (Inl (CoreTy_MathInt, CoreTy_Bool))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_MathInt CoreTy_Bool = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_MathInt\<close> CoreTy_Bool dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_FiniteInt sign2 bits2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_MathInt, CoreTy_FiniteInt sign2 bits2))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_MathInt (CoreTy_FiniteInt sign2 bits2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_MathInt\<close> CoreTy_FiniteInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_MathReal
        have dom: "unify_unify_list_dom (Inl (CoreTy_MathInt, CoreTy_MathReal))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_MathInt CoreTy_MathReal = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_MathInt\<close> CoreTy_MathReal dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_Record flds2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_MathInt, CoreTy_Record flds2))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_MathInt (CoreTy_Record flds2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_MathInt\<close> CoreTy_Record dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_Array elem2 dims2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_MathInt, CoreTy_Array elem2 dims2))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_MathInt (CoreTy_Array elem2 dims2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_MathInt\<close> CoreTy_Array dom result
          by (auto simp: unify_terminates_with_props_def)
      qed
    next
      case CoreTy_MathReal
      show ?thesis
        using Inl pair_eq CoreTy_MathReal
      proof (cases ty2)
        case (CoreTy_Meta m)
        have dom: "unify_unify_list_dom (Inl (CoreTy_MathReal, CoreTy_Meta m))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_MathReal (CoreTy_Meta m) = Some (singleton_subst m CoreTy_MathReal)"
          using dom by (simp add: unify.psimps)
        have props: "subst_props (unify_input_mvs CoreTy_MathReal (CoreTy_Meta m)) (singleton_subst m CoreTy_MathReal)"
          by (auto simp: unify_input_mvs_def intro: subst_props_singleton simp: occurs_def)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_MathReal\<close> CoreTy_Meta dom result props
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_MathReal
        have dom: "unify_unify_list_dom (Inl (CoreTy_MathReal, CoreTy_MathReal))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_MathReal CoreTy_MathReal = Some fmempty"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_MathReal\<close> CoreTy_MathReal dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_Name name2 args2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_MathReal, CoreTy_Name name2 args2))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_MathReal (CoreTy_Name name2 args2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_MathReal\<close> CoreTy_Name dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_Bool
        have dom: "unify_unify_list_dom (Inl (CoreTy_MathReal, CoreTy_Bool))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_MathReal CoreTy_Bool = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_MathReal\<close> CoreTy_Bool dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_FiniteInt sign2 bits2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_MathReal, CoreTy_FiniteInt sign2 bits2))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_MathReal (CoreTy_FiniteInt sign2 bits2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_MathReal\<close> CoreTy_FiniteInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_MathInt
        have dom: "unify_unify_list_dom (Inl (CoreTy_MathReal, CoreTy_MathInt))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_MathReal CoreTy_MathInt = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_MathReal\<close> CoreTy_MathInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_Record flds2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_MathReal, CoreTy_Record flds2))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_MathReal (CoreTy_Record flds2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_MathReal\<close> CoreTy_Record dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_Array elem2 dims2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_MathReal, CoreTy_Array elem2 dims2))"
          by (rule unify_unify_list.domintros)
        have result: "unify CoreTy_MathReal (CoreTy_Array elem2 dims2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = CoreTy_MathReal\<close> CoreTy_Array dom result
          by (auto simp: unify_terminates_with_props_def)
      qed
    next
      case CoreTy_Record1: (CoreTy_Record flds1)
      show ?thesis
        using Inl pair_eq CoreTy_Record1
      proof (cases ty2)
        case (CoreTy_Meta m)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Record flds1, CoreTy_Meta m))"
          using unify_unify_list.domintros(6) by auto
        show ?thesis
        proof (cases "occurs m (CoreTy_Record flds1)")
          case True
          have result: "unify (CoreTy_Record flds1) (CoreTy_Meta m) = None"
            using dom True by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq CoreTy_Record1 CoreTy_Meta dom result
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have result: "unify (CoreTy_Record flds1) (CoreTy_Meta m) = Some (singleton_subst m (CoreTy_Record flds1))"
            using dom False by (simp add: unify.psimps)
          have props: "subst_props (unify_input_mvs (CoreTy_Record flds1) (CoreTy_Meta m)) (singleton_subst m (CoreTy_Record flds1))"
            using False by (auto simp: unify_input_mvs_def intro: subst_props_singleton)
          show ?thesis
            using Inl pair_eq CoreTy_Record1 CoreTy_Meta dom result props
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case (CoreTy_Record flds2)
        show ?thesis
        proof (cases "map fst flds1 = map fst flds2")
          case False
          (* Field names don't match - unification fails immediately *)
          have dom: "unify_unify_list_dom (Inl (CoreTy_Record flds1, CoreTy_Record flds2))"
            using False unify_unify_list.domintros(6) by force
          have result: "unify (CoreTy_Record flds1) (CoreTy_Record flds2) = None"
            using dom False by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq CoreTy_Record1 CoreTy_Record dom result
            by (auto simp: unify_terminates_with_props_def)
        next
          case True
          (* Field names match - recursive call to unify_list on field types *)
          have in_rel: "(Inr (map snd flds1, map snd flds2), Inl (CoreTy_Record flds1, CoreTy_Record flds2)) \<in> unify_rel"
            by (simp add: unify_rel_record_to_list)
          have ih: "unify_terminates_with_props (Inr (map snd flds1, map snd flds2))"
            by (simp add: "1" CoreTy_Record CoreTy_Record1 Inl in_rel pair_eq)
          hence list_dom: "unify_unify_list_dom (Inr (map snd flds1, map snd flds2))"
            by (simp add: unify_terminates_with_props_def)
          have list_props: "\<And>subst. unify_list (map snd flds1) (map snd flds2) = Some subst \<Longrightarrow>
                                      subst_props (unify_list_input_mvs (map snd flds1) (map snd flds2)) subst"
            using ih unify_terminates_with_props_def by auto
          have dom: "unify_unify_list_dom (Inl (CoreTy_Record flds1, CoreTy_Record flds2))"
            using list_dom True by (auto intro: unify_unify_list.domintros)
          have result_eq: "unify (CoreTy_Record flds1) (CoreTy_Record flds2) = unify_list (map snd flds1) (map snd flds2)"
            using dom True by (simp add: unify.psimps)
          have mvs_eq: "unify_list_input_mvs (map snd flds1) (map snd flds2) = unify_input_mvs (CoreTy_Record flds1) (CoreTy_Record flds2)"
            by (auto simp: unify_list_input_mvs_def unify_input_mvs_def list_metavars_def comp_def)
          show ?thesis
            using Inl pair_eq CoreTy_Record1 CoreTy_Record dom result_eq list_props mvs_eq
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case (CoreTy_Name name2 args2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Record flds1, CoreTy_Name name2 args2))"
          using unify_unify_list.domintros(6) by auto
        have result: "unify (CoreTy_Record flds1) (CoreTy_Name name2 args2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_Record1 CoreTy_Name dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_Bool
        have dom: "unify_unify_list_dom (Inl (CoreTy_Record flds1, CoreTy_Bool))"
          using unify_unify_list.domintros(6) by auto
        have result: "unify (CoreTy_Record flds1) CoreTy_Bool = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_Record1 CoreTy_Bool dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_FiniteInt sign2 bits2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Record flds1, CoreTy_FiniteInt sign2 bits2))"
          using unify_unify_list.domintros(6) by auto
        have result: "unify (CoreTy_Record flds1) (CoreTy_FiniteInt sign2 bits2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_Record1 CoreTy_FiniteInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_MathInt
        have dom: "unify_unify_list_dom (Inl (CoreTy_Record flds1, CoreTy_MathInt))"
          using unify_unify_list.domintros(6) by auto
        have result: "unify (CoreTy_Record flds1) CoreTy_MathInt = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_Record1 CoreTy_MathInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_MathReal
        have dom: "unify_unify_list_dom (Inl (CoreTy_Record flds1, CoreTy_MathReal))"
          using unify_unify_list.domintros(6) by auto
        have result: "unify (CoreTy_Record flds1) CoreTy_MathReal = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_Record1 CoreTy_MathReal dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_Array elem2 dims2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Record flds1, CoreTy_Array elem2 dims2))"
          using unify_unify_list.domintros(6) by auto
        have result: "unify (CoreTy_Record flds1) (CoreTy_Array elem2 dims2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_Record1 CoreTy_Array dom result
          by (auto simp: unify_terminates_with_props_def)
      qed
    next
      case CoreTy_Array1: (CoreTy_Array elem1 dims1)
      show ?thesis
        using Inl pair_eq CoreTy_Array1
      proof (cases ty2)
        case (CoreTy_Meta m)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Array elem1 dims1, CoreTy_Meta m))"
          using unify_unify_list.domintros(7) by auto
        show ?thesis
        proof (cases "occurs m (CoreTy_Array elem1 dims1)")
          case True
          have result: "unify (CoreTy_Array elem1 dims1) (CoreTy_Meta m) = None"
            using dom True by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq CoreTy_Array1 CoreTy_Meta dom result
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have result: "unify (CoreTy_Array elem1 dims1) (CoreTy_Meta m) = Some (singleton_subst m (CoreTy_Array elem1 dims1))"
            using dom False by (simp add: unify.psimps)
          have props: "subst_props (unify_input_mvs (CoreTy_Array elem1 dims1) (CoreTy_Meta m)) (singleton_subst m (CoreTy_Array elem1 dims1))"
            using False by (auto simp: unify_input_mvs_def intro: subst_props_singleton)
          show ?thesis
            using Inl pair_eq CoreTy_Array1 CoreTy_Meta dom result props
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case (CoreTy_Array elem2 dims2)
        show ?thesis
        proof (cases "dims1 = dims2")
          case False
          have dom: "unify_unify_list_dom (Inl (CoreTy_Array elem1 dims1, CoreTy_Array elem2 dims2))"
            using False unify_unify_list.domintros(7) by force
          have result: "unify (CoreTy_Array elem1 dims1) (CoreTy_Array elem2 dims2) = None"
            using dom False by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq CoreTy_Array1 CoreTy_Array dom result
            by (auto simp: unify_terminates_with_props_def)
        next
          case True
          (* Recursive call to unify elem1 elem2 *)
          have in_rel: "(Inl (elem1, elem2), Inl (CoreTy_Array elem1 dims1, CoreTy_Array elem2 dims2)) \<in> unify_rel"
            by (simp add: unify_rel_array_to_elem)
          have ih: "unify_terminates_with_props (Inl (elem1, elem2))"
            by (simp add: "1" CoreTy_Array CoreTy_Array1 Inl in_rel pair_eq)
          hence elem_dom: "unify_unify_list_dom (Inl (elem1, elem2))"
            and elem_props: "\<And>subst. unify elem1 elem2 = Some subst \<Longrightarrow>
                                      subst_props (unify_input_mvs elem1 elem2) subst"
            by (auto simp: unify_terminates_with_props_def)
          have dom: "unify_unify_list_dom (Inl (CoreTy_Array elem1 dims1, CoreTy_Array elem2 dims2))"
            using elem_dom True by (auto intro: unify_unify_list.domintros)
          have result_eq: "unify (CoreTy_Array elem1 dims1) (CoreTy_Array elem2 dims2) = unify elem1 elem2"
            using dom True by (simp add: unify.psimps)
          have mvs_eq: "unify_input_mvs elem1 elem2 = unify_input_mvs (CoreTy_Array elem1 dims1) (CoreTy_Array elem2 dims2)"
            by (auto simp: unify_input_mvs_def)
          show ?thesis
            using Inl pair_eq CoreTy_Array1 CoreTy_Array dom result_eq elem_props mvs_eq
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case (CoreTy_Name name2 args2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Array elem1 dims1, CoreTy_Name name2 args2))"
          using unify_unify_list.domintros(7) by auto
        have result: "unify (CoreTy_Array elem1 dims1) (CoreTy_Name name2 args2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_Array1 CoreTy_Name dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_Bool
        have dom: "unify_unify_list_dom (Inl (CoreTy_Array elem1 dims1, CoreTy_Bool))"
          using unify_unify_list.domintros(7) by auto
        have result: "unify (CoreTy_Array elem1 dims1) CoreTy_Bool = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_Array1 CoreTy_Bool dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_FiniteInt sign2 bits2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Array elem1 dims1, CoreTy_FiniteInt sign2 bits2))"
          using unify_unify_list.domintros(7) by auto
        have result: "unify (CoreTy_Array elem1 dims1) (CoreTy_FiniteInt sign2 bits2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_Array1 CoreTy_FiniteInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_MathInt
        have dom: "unify_unify_list_dom (Inl (CoreTy_Array elem1 dims1, CoreTy_MathInt))"
          using unify_unify_list.domintros(7) by auto
        have result: "unify (CoreTy_Array elem1 dims1) CoreTy_MathInt = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_Array1 CoreTy_MathInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case CoreTy_MathReal
        have dom: "unify_unify_list_dom (Inl (CoreTy_Array elem1 dims1, CoreTy_MathReal))"
          using unify_unify_list.domintros(7) by auto
        have result: "unify (CoreTy_Array elem1 dims1) CoreTy_MathReal = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_Array1 CoreTy_MathReal dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (CoreTy_Record flds2)
        have dom: "unify_unify_list_dom (Inl (CoreTy_Array elem1 dims1, CoreTy_Record flds2))"
          using unify_unify_list.domintros(7) by auto
        have result: "unify (CoreTy_Array elem1 dims1) (CoreTy_Record flds2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq CoreTy_Array1 CoreTy_Record dom result
          by (auto simp: unify_terminates_with_props_def)
      qed
    qed
  next
    case (Inr pair)
    obtain tys1 tys2 where pair_eq: "pair = (tys1, tys2)" by (cases pair)
    show ?thesis
    proof (cases tys1)
      case Nil
      show ?thesis
      proof (cases tys2)
        case Nil
        have dom: "unify_unify_list_dom (Inr ([], []))"
          by (rule unify_unify_list.domintros)
        have result: "unify_list [] [] = Some fmempty"
          by (simp add: dom unify_list.psimps(1))
        show ?thesis
          using Inr pair_eq \<open>tys1 = []\<close> Nil dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (Cons ty2 rest2)
        have dom: "unify_unify_list_dom (Inr ([], ty2 # rest2))"
          by (rule unify_unify_list.domintros)
        have result: "unify_list [] (ty2 # rest2) = None"
          by (simp add: dom unify_list.psimps(2))
        show ?thesis
          using Inr pair_eq \<open>tys1 = []\<close> Cons dom result
          by (auto simp: unify_terminates_with_props_def)
      qed
    next
      case (Cons ty1 rest1)
      show ?thesis
      proof (cases tys2)
        case Nil
        have dom: "unify_unify_list_dom (Inr (ty1 # rest1, []))"
          by (rule unify_unify_list.domintros)
        have result: "unify_list (ty1 # rest1) [] = None"
          by (simp add: dom unify_list.psimps(3))
        show ?thesis
          using Inr pair_eq Cons Nil dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case Cons2: (Cons ty2 rest2)
        (* This is the interesting case: unify_list (ty1 # rest1) (ty2 # rest2) *)
        (* First unify ty1 ty2, then recursively unify the tails with substitution applied *)

        (* IH for unify ty1 ty2 *)
        have head_in_rel: "(Inl (ty1, ty2), Inr (ty1 # rest1, ty2 # rest2)) \<in> unify_rel"
          by (simp add: unify_rel_list_to_head)
        have head_ih: "unify_terminates_with_props (Inl (ty1, ty2))"
          by (simp add: "1" Cons2 Inr head_in_rel local.Cons pair_eq) 
        hence head_dom: "unify_unify_list_dom (Inl (ty1, ty2))"
          and head_props: "\<And>subst. unify ty1 ty2 = Some subst \<Longrightarrow>
                                    subst_props (unify_input_mvs ty1 ty2) subst"
          by (auto simp: unify_terminates_with_props_def)

        show ?thesis
        proof (cases "unify ty1 ty2")
          case None
          have dom: "unify_unify_list_dom (Inr (ty1 # rest1, ty2 # rest2))"
            using head_dom
            using None unify_unify_list.domintros(12) by force
          have result: "unify_list (ty1 # rest1) (ty2 # rest2) = None"
            using dom head_dom None
            by (simp add: unify_list.psimps(4))
          show ?thesis
            using Inr pair_eq \<open>tys1 = ty1 # rest1\<close> Cons dom result
            by (simp add: Cons2 unify_terminates_with_props_def)
        next
          case (Some subst1)
          hence subst1_props: "subst_props (unify_input_mvs ty1 ty2) subst1"
            using head_props by auto

          (* IH for unify_list on tails with subst applied *)
          have tail_in_rel: "(Inr (map (apply_subst subst1) rest1, map (apply_subst subst1) rest2),
                              Inr (ty1 # rest1, ty2 # rest2)) \<in> unify_rel"
            using subst1_props
            by (metis unify_input_mvs_def unify_rel_list_recursive)
          have tail_ih: "unify_terminates_with_props (Inr (map (apply_subst subst1) rest1, map (apply_subst subst1) rest2))"
            by (simp add: "1" Cons2 Inr local.Cons pair_eq tail_in_rel)
          hence tail_dom: "unify_unify_list_dom (Inr (map (apply_subst subst1) rest1, map (apply_subst subst1) rest2))"
            and tail_props: "\<And>subst. unify_list (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2) = Some subst \<Longrightarrow>
                                      subst_props (unify_list_input_mvs (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2)) subst"
            by (auto simp: unify_terminates_with_props_def)

          have dom: "unify_unify_list_dom (Inr (ty1 # rest1, ty2 # rest2))"
            using head_dom tail_dom Some by (auto intro: unify_unify_list.domintros)

          show ?thesis
          proof (cases "unify_list (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2)")
            case None
            have result: "unify_list (ty1 # rest1) (ty2 # rest2) = None"
              using dom head_dom Some None
              by (simp add: unify_list.psimps(4))
            show ?thesis
              using Inr pair_eq Cons Cons2 dom result
              by (auto simp: unify_terminates_with_props_def)
          next
            case (Some subst2)
            have result: "unify_list (ty1 # rest1) (ty2 # rest2) = Some (compose_subst subst2 subst1)"
              using dom head_dom \<open>unify ty1 ty2 = Some subst1\<close> Some
              by (simp add: unify_list.psimps(4))

            (* Need to show subst_props for composed substitution *)
            have subst2_props: "subst_props (unify_list_input_mvs (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2)) subst2"
              using tail_props Some by auto

            (* Key definitions for the proof *)
            define head_mvs where "head_mvs = type_metavars ty1 \<union> type_metavars ty2"
            define full_mvs where "full_mvs = list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"

            have head_sub: "head_mvs \<subseteq> full_mvs"
              by (auto simp: head_mvs_def full_mvs_def list_metavars_def)

            have head_props': "subst_props head_mvs subst1"
              using subst1_props by (simp add: head_mvs_def unify_input_mvs_def)

            (* After applying subst1, metavars of the result are contained in full_mvs *)
            have rec_mvs: "unify_list_input_mvs (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2) \<subseteq> full_mvs"
            proof -
              have rest1_mvs: "list_metavars rest1 \<subseteq> full_mvs"
                by (auto simp: full_mvs_def list_metavars_def)
              have rest2_mvs: "list_metavars rest2 \<subseteq> full_mvs"
                by (auto simp: full_mvs_def list_metavars_def)
              have range1_mvs: "subst_range_mvs subst1 \<subseteq> head_mvs"
              proof -
                have "\<And>ty. ty \<in> fmran' subst1 \<Longrightarrow> type_metavars ty \<subseteq> head_mvs"
                proof -
                  fix ty assume "ty \<in> fmran' subst1"
                  then obtain n where "fmlookup subst1 n = Some ty" by (auto simp: fmran'_def)
                  thus "type_metavars ty \<subseteq> head_mvs"
                    using head_props' by (auto simp: subst_props_def head_mvs_def)
                qed
                thus ?thesis by (auto simp: subst_range_mvs_def)
              qed
              have applied1: "list_metavars (map (apply_subst subst1) rest1) \<subseteq> full_mvs"
              proof
                fix x assume "x \<in> list_metavars (map (apply_subst subst1) rest1)"
                then obtain t where t_in: "t \<in> set rest1" and x_in: "x \<in> type_metavars (apply_subst subst1 t)"
                  by (auto simp: list_metavars_def)
                from x_in have "x \<in> (type_metavars t - fset (fmdom subst1)) \<union> subst_range_mvs subst1"
                  using apply_subst_metavars_result by auto
                thus "x \<in> full_mvs"
                  using t_in rest1_mvs range1_mvs head_sub by (auto simp: list_metavars_def)
              qed
              moreover have applied2: "list_metavars (map (apply_subst subst1) rest2) \<subseteq> full_mvs"
              proof
                fix x assume "x \<in> list_metavars (map (apply_subst subst1) rest2)"
                then obtain t where t_in: "t \<in> set rest2" and x_in: "x \<in> type_metavars (apply_subst subst1 t)"
                  by (auto simp: list_metavars_def)
                from x_in have "x \<in> (type_metavars t - fset (fmdom subst1)) \<union> subst_range_mvs subst1"
                  using apply_subst_metavars_result by auto
                thus "x \<in> full_mvs"
                  using t_in rest2_mvs range1_mvs head_sub by (auto simp: list_metavars_def)
              qed
              ultimately show ?thesis by (auto simp: unify_list_input_mvs_def)
            qed

            (* Lift subst1 props to full mvs *)
            have props1: "subst_props full_mvs subst1"
              using head_props' head_sub unfolding subst_props_def subst_range_mvs_def by blast

            (* Lift subst2 props to full mvs *)
            have rec_props: "subst_props (unify_list_input_mvs (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2)) subst2"
              using subst2_props by simp
            have props2: "subst_props full_mvs subst2"
              using rec_props rec_mvs unfolding subst_props_def subst_range_mvs_def by blast

            (* Domain disjointness *)
            have dom_disj: "fset (fmdom subst2) \<inter> fset (fmdom subst1) = {}"
            proof -
              have dom1_sub: "fset (fmdom subst1) \<subseteq> head_mvs"
                using head_props' by (auto simp: subst_props_def)
              have dom2_sub: "fset (fmdom subst2) \<subseteq> list_metavars (map (apply_subst subst1) rest1) \<union>
                                                     list_metavars (map (apply_subst subst1) rest2)"
                using rec_props by (auto simp: subst_props_def unify_list_input_mvs_def)
              have "\<And>n. n \<in> fset (fmdom subst1) \<Longrightarrow>
                        n \<notin> list_metavars (map (apply_subst subst1) rest1) \<union>
                             list_metavars (map (apply_subst subst1) rest2)"
              proof -
                fix n assume n_in: "n \<in> fset (fmdom subst1)"
                have "n \<notin> subst_range_mvs subst1"
                  using head_props' n_in by (auto simp: subst_props_def)
                thus "n \<notin> list_metavars (map (apply_subst subst1) rest1) \<union>
                           list_metavars (map (apply_subst subst1) rest2)"
                  using apply_subst_eliminates_dom[OF n_in] by (auto simp: list_metavars_def)
              qed
              thus ?thesis using dom2_sub by auto
            qed

            (* Range disjointness *)
            have range2_disj: "subst_range_mvs subst2 \<inter> fset (fmdom subst1) = {}"
            proof -
              have range2_sub: "subst_range_mvs subst2 \<subseteq> list_metavars (map (apply_subst subst1) rest1) \<union>
                                                         list_metavars (map (apply_subst subst1) rest2)"
              proof -
                have "\<And>ty. ty \<in> fmran' subst2 \<Longrightarrow> type_metavars ty \<subseteq>
                      list_metavars (map (apply_subst subst1) rest1) \<union>
                      list_metavars (map (apply_subst subst1) rest2)"
                proof -
                  fix ty assume "ty \<in> fmran' subst2"
                  then obtain n where "fmlookup subst2 n = Some ty"
                    by (auto simp: fmran'_def)
                  thus "type_metavars ty \<subseteq> list_metavars (map (apply_subst subst1) rest1) \<union>
                        list_metavars (map (apply_subst subst1) rest2)"
                    using rec_props by (auto simp: subst_props_def unify_list_input_mvs_def)
                qed
                thus ?thesis by (auto simp: subst_range_mvs_def)
              qed
              have "\<And>n. n \<in> fset (fmdom subst1) \<Longrightarrow>
                        n \<notin> list_metavars (map (apply_subst subst1) rest1) \<union>
                             list_metavars (map (apply_subst subst1) rest2)"
              proof -
                fix n assume n_in: "n \<in> fset (fmdom subst1)"
                have "n \<notin> subst_range_mvs subst1"
                  using head_props' n_in by (auto simp: subst_props_def)
                thus "n \<notin> list_metavars (map (apply_subst subst1) rest1) \<union>
                           list_metavars (map (apply_subst subst1) rest2)"
                  using apply_subst_eliminates_dom[OF n_in] by (auto simp: list_metavars_def)
              qed
              thus ?thesis using range2_sub by auto
            qed

            have composed_props: "subst_props (unify_list_input_mvs (ty1 # rest1) (ty2 # rest2)) (compose_subst subst2 subst1)"
              using subst_props_compose[OF props1 props2 dom_disj range2_disj]
              by (simp add: full_mvs_def unify_list_input_mvs_def)

            show ?thesis
              using Inr pair_eq Cons Cons2 dom result composed_props
              by (auto simp: unify_terminates_with_props_def)
          qed
        qed
      qed
    qed
  qed
qed

(* Extract termination *)
lemma unify_dom: "unify_unify_list_dom x"
  using unify_terminates_with_props_all unfolding unify_terminates_with_props_def by auto

termination unify
  using unify_dom by auto

end

