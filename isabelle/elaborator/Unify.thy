theory Unify
  imports "../core/CoreSyntax" "../core/TypeSubst" "../core/CoreTypeProps"
begin

(* ========================================================================== *)
(* Type unification algorithm *)
(* ========================================================================== *)

(* Unifies two CoreTypes, returning a most general unifier if one exists, or None if
   unification fails (incompatible types or occurs check).
   The is_flex predicate determines which metavariables are flexible (unifiable).
   Rigid metavariables (where is_flex returns False) behave like opaque type constants
   and only unify with themselves. *)

function (domintros) unify :: "(string \<Rightarrow> bool) \<Rightarrow> CoreType \<Rightarrow> CoreType \<Rightarrow> TypeSubst option"
and unify_list :: "(string \<Rightarrow> bool) \<Rightarrow> CoreType list \<Rightarrow> CoreType list \<Rightarrow> TypeSubst option" where
  "unify is_flex (CoreTy_Datatype name1 tyArgs1) ty2 =
    (case ty2 of
      CoreTy_Var n \<Rightarrow>
        if is_flex n then
          (if occurs n (CoreTy_Datatype name1 tyArgs1) then None
           else Some (singleton_subst n (CoreTy_Datatype name1 tyArgs1)))
        else None
    | CoreTy_Datatype name2 tyArgs2 \<Rightarrow>
        if name1 = name2 then unify_list is_flex tyArgs1 tyArgs2 else None
    | _ \<Rightarrow> None)"

| "unify is_flex CoreTy_Bool ty2 =
    (case ty2 of
      CoreTy_Var n \<Rightarrow>
        if is_flex n then Some (singleton_subst n CoreTy_Bool) else None
    | CoreTy_Bool \<Rightarrow> Some fmempty
    | _ \<Rightarrow> None)"

| "unify is_flex (CoreTy_FiniteInt sign bits) ty2 =
    (case ty2 of
      CoreTy_Var n \<Rightarrow>
        if is_flex n then Some (singleton_subst n (CoreTy_FiniteInt sign bits)) else None
    | CoreTy_FiniteInt sign' bits' \<Rightarrow>
        if sign = sign' \<and> bits = bits' then Some fmempty else None
    | _ \<Rightarrow> None)"

| "unify is_flex CoreTy_MathInt ty2 =
    (case ty2 of
      CoreTy_Var n \<Rightarrow>
        if is_flex n then Some (singleton_subst n CoreTy_MathInt) else None
    | CoreTy_MathInt \<Rightarrow> Some fmempty
    | _ \<Rightarrow> None)"

| "unify is_flex CoreTy_MathReal ty2 =
    (case ty2 of
      CoreTy_Var n \<Rightarrow>
        if is_flex n then Some (singleton_subst n CoreTy_MathReal) else None
    | CoreTy_MathReal \<Rightarrow> Some fmempty
    | _ \<Rightarrow> None)"

| "unify is_flex (CoreTy_Record flds1) ty2 =
    (case ty2 of
      CoreTy_Var n \<Rightarrow>
        if is_flex n then
          (if occurs n (CoreTy_Record flds1) then None
           else Some (singleton_subst n (CoreTy_Record flds1)))
        else None
    | CoreTy_Record flds2 \<Rightarrow>
        if map fst flds1 = map fst flds2
        then unify_list is_flex (map snd flds1) (map snd flds2)
        else None
    | _ \<Rightarrow> None)"

| "unify is_flex (CoreTy_Array elemTy1 dims1) ty2 =
    (case ty2 of
      CoreTy_Var n \<Rightarrow>
        if is_flex n then
          (if occurs n (CoreTy_Array elemTy1 dims1) then None
           else Some (singleton_subst n (CoreTy_Array elemTy1 dims1)))
        else None
    | CoreTy_Array elemTy2 dims2 \<Rightarrow>
        if dims1 = dims2 then unify is_flex elemTy1 elemTy2 else None
    | _ \<Rightarrow> None)"

| "unify is_flex (CoreTy_Var n) ty2 =
    (if is_flex n then
       (if occurs n ty2 \<and> ty2 \<noteq> CoreTy_Var n then None
        else if ty2 = CoreTy_Var n then Some fmempty
        else Some (singleton_subst n ty2))
     else \<comment> \<open>Rigid metavar: only matches itself, or can be bound by a flexible var on the right\<close>
       (case ty2 of
         CoreTy_Var m \<Rightarrow>
           if m = n then Some fmempty
           else if is_flex m then Some (singleton_subst m (CoreTy_Var n))
           else None
       | _ \<Rightarrow> None))"

| "unify_list _ [] [] = Some fmempty"

| "unify_list _ [] (ty # tys) = None"

| "unify_list _ (ty # tys) [] = None"

| "unify_list is_flex (ty1 # tys1) (ty2 # tys2) =
    (case unify is_flex ty1 ty2 of
      None \<Rightarrow> None
    | Some subst1 \<Rightarrow>
        (case unify_list is_flex (map (apply_subst subst1) tys1)
                                (map (apply_subst subst1) tys2) of
          None \<Rightarrow> None
        | Some subst2 \<Rightarrow> Some (compose_subst subst2 subst1)))"

(* An extern type unifies with itself and with a flexible metavariable, and with nothing
   else. (Appended after the unify_list clauses so that the numbering of the earlier
   clauses is unchanged.) *)
| "unify is_flex (CoreTy_Extern n l) ty2 =
    (case ty2 of
      CoreTy_Var m \<Rightarrow>
        if is_flex m then Some (singleton_subst m (CoreTy_Extern n l)) else None
    | CoreTy_Extern n' l' \<Rightarrow> if n = n' \<and> l = l' then Some fmempty else None
    | _ \<Rightarrow> None)"

by pat_completeness auto


(* ========================================================================== *)
(* Termination proof                                                          *)
(* ========================================================================== *)

(* Custom size function for CoreType that returns at least 1 for every type *)
fun core_type_size :: "CoreType \<Rightarrow> nat" where
  "core_type_size (CoreTy_Datatype _ tyargs) = 1 + sum_list (map core_type_size tyargs)"
| "core_type_size CoreTy_Bool = 1"
| "core_type_size (CoreTy_FiniteInt _ _) = 1"
| "core_type_size CoreTy_MathInt = 1"
| "core_type_size CoreTy_MathReal = 1"
| "core_type_size (CoreTy_Record flds) = 1 + sum_list (map (core_type_size \<circ> snd) flds)"
| "core_type_size (CoreTy_Array elemTy _) = 1 + core_type_size elemTy"
| "core_type_size (CoreTy_Var _) = 1"
| "core_type_size (CoreTy_Extern _ _) = 1"

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
  "list_type_size args < core_type_size (CoreTy_Datatype name args)"
  by (simp add: list_type_size_def)

lemma record_size_smaller:
  "list_type_size (map snd flds) < core_type_size (CoreTy_Record flds)"
  by (simp add: list_type_size_def comp_def)

lemma array_elem_size_smaller:
  "core_type_size elem < core_type_size (CoreTy_Array elem dims)"
  by simp

lemma list_tyvars_cons:
  "list_tyvars (ty # tys) = type_tyvars ty \<union> list_tyvars tys"
  by (simp add: list_tyvars_def)

(* The termination relation: lexicographic on (card of metavars, size, tag)
   where tag is 0 for Inl (unify) and 1 for Inr (unify_list).
   The is_flex predicate is passed unchanged to every recursive call so it
   does not affect termination — we project it out. *)
definition unify_rel :: "(((string \<Rightarrow> bool) \<times> CoreType \<times> CoreType) + ((string \<Rightarrow> bool) \<times> CoreType list \<times> CoreType list)) rel" where
  "unify_rel = inv_image (less_than <*lex*> less_than <*lex*> less_than)
    (\<lambda>x. case x of
      Inl (_, ty1, ty2) \<Rightarrow> (card (type_tyvars ty1 \<union> type_tyvars ty2),
                            core_type_size ty1 + core_type_size ty2,
                            0::nat)
    | Inr (_, tys1, tys2) \<Rightarrow> (card (list_tyvars tys1 \<union> list_tyvars tys2),
                              list_type_size tys1 + list_type_size tys2,
                              1::nat))"

lemma wf_unify_rel: "wf unify_rel"
  unfolding unify_rel_def by auto

(* Lemmas about when recursive calls are in unify_rel *)

(* Calling unify_list args1 args2 from unify (Name n1 args1) (Name n2 args2) is smaller *)
lemma unify_rel_name_to_list:
  "(Inr (f, args1, args2), Inl (f, CoreTy_Datatype n1 args1, CoreTy_Datatype n2 args2)) \<in> unify_rel"
proof -
  have "list_type_size args1 + list_type_size args2 <
        core_type_size (CoreTy_Datatype n1 args1) + core_type_size (CoreTy_Datatype n2 args2)"
    by (meson add_less_mono type_args_size_smaller)
  moreover have "list_tyvars args1 \<union> list_tyvars args2 =
                 type_tyvars (CoreTy_Datatype n1 args1) \<union> type_tyvars (CoreTy_Datatype n2 args2)"
    by (auto simp: list_tyvars_def)
  ultimately show ?thesis
    unfolding unify_rel_def by auto
qed

(* Calling unify_list (map snd flds1) (map snd flds2) from unify (Record flds1) (Record flds2) is smaller *)
lemma unify_rel_record_to_list:
  "(Inr (f, map snd flds1, map snd flds2), Inl (f, CoreTy_Record flds1, CoreTy_Record flds2)) \<in> unify_rel"
proof -
  have "list_type_size (map snd flds1) + list_type_size (map snd flds2) <
        core_type_size (CoreTy_Record flds1) + core_type_size (CoreTy_Record flds2)"
    by (meson add_less_mono record_size_smaller)
  moreover have "list_tyvars (map snd flds1) \<union> list_tyvars (map snd flds2) =
                 type_tyvars (CoreTy_Record flds1) \<union> type_tyvars (CoreTy_Record flds2)"
    by (auto simp: list_tyvars_def comp_def)
  ultimately show ?thesis
    unfolding unify_rel_def by auto
qed

(* Calling unify elem1 elem2 from unify (Array elem1 dims1) (Array elem2 dims2) is smaller *)
lemma unify_rel_array_to_elem:
  "(Inl (f, elem1, elem2), Inl (f, CoreTy_Array elem1 dims1, CoreTy_Array elem2 dims2)) \<in> unify_rel"
proof -
  have "core_type_size elem1 + core_type_size elem2 <
        core_type_size (CoreTy_Array elem1 dims1) + core_type_size (CoreTy_Array elem2 dims2)"
    by (meson add_less_mono array_elem_size_smaller)
  moreover have "type_tyvars elem1 \<union> type_tyvars elem2 =
                 type_tyvars (CoreTy_Array elem1 dims1) \<union> type_tyvars (CoreTy_Array elem2 dims2)"
    by auto
  ultimately show ?thesis
    unfolding unify_rel_def by auto
qed

(* Calling unify head1 head2 from unify_list (head1 # rest1) (head2 # rest2) is smaller *)
lemma unify_rel_list_to_head:
  "(Inl (f, head1, head2), Inr (f, head1 # rest1, head2 # rest2)) \<in> unify_rel"
proof -
  have mv_subset: "type_tyvars head1 \<union> type_tyvars head2 \<subseteq>
        list_tyvars (head1 # rest1) \<union> list_tyvars (head2 # rest2)"
    by (auto simp: list_tyvars_def)
  hence mv_card: "card (type_tyvars head1 \<union> type_tyvars head2) \<le>
            card (list_tyvars (head1 # rest1) \<union> list_tyvars (head2 # rest2))"
    by (simp add: card_mono finite_list_tyvars)
  have size_le: "core_type_size head1 + core_type_size head2 \<le>
                 list_type_size (head1 # rest1) + list_type_size (head2 # rest2)"
    by (simp add: list_type_size_cons)
  show ?thesis
    unfolding unify_rel_def
    using mv_card size_le by auto
qed

(* Properties that a substitution from unify/unify_list must satisfy *)
definition subst_props :: "string set \<Rightarrow> TypeSubst \<Rightarrow> bool" where
  "subst_props mvs subst \<equiv>
    fset (fmdom subst) \<subseteq> mvs \<and>
    (\<forall>n ty. fmlookup subst n = Some ty \<longrightarrow> type_tyvars ty \<subseteq> mvs) \<and>
    fset (fmdom subst) \<inter> subst_range_tyvars subst = {}"

definition unify_input_mvs :: "CoreType \<Rightarrow> CoreType \<Rightarrow> string set" where
  "unify_input_mvs ty1 ty2 = type_tyvars ty1 \<union> type_tyvars ty2"

definition unify_list_input_mvs :: "CoreType list \<Rightarrow> CoreType list \<Rightarrow> string set" where
  "unify_list_input_mvs tys1 tys2 = list_tyvars tys1 \<union> list_tyvars tys2"

(* Empty substitution trivially satisfies the properties *)
lemma subst_props_empty [simp]: "subst_props mvs fmempty"
  by (simp add: subst_props_def)

(* Singleton substitution satisfies properties when constructed correctly *)
lemma subst_props_singleton:
  assumes "n \<in> mvs"
      and "type_tyvars ty \<subseteq> mvs"
      and "\<not> occurs n ty"
  shows "subst_props mvs (singleton_subst n ty)"
  using assms
  by (auto simp: subst_props_def singleton_subst_def subst_range_tyvars_def occurs_def fmran'_def)

(* If subst satisfies props for mvs, applying it to types with metavars in mvs
   results in types whose metavars are still in mvs *)
lemma apply_subst_tyvars_subset:
  assumes "subst_props mvs subst"
      and "type_tyvars ty \<subseteq> mvs"
  shows "type_tyvars (apply_subst subst ty) \<subseteq> mvs"
proof -
  from assms(1) have dom_sub: "fset (fmdom subst) \<subseteq> mvs"
    by (simp add: subst_props_def)
  from assms(1) have range_sub: "subst_range_tyvars subst \<subseteq> mvs"
    by (auto simp: subst_props_def subst_range_tyvars_def fmran'_def)
  have "type_tyvars (apply_subst subst ty) \<subseteq>
        (type_tyvars ty - fset (fmdom subst)) \<union> subst_range_tyvars subst"
    by (rule apply_subst_tyvars_result)
  also have "... \<subseteq> mvs"
    using assms(2) range_sub by auto
  finally show ?thesis .
qed

(* Composition preserves properties *)
lemma subst_props_compose:
  assumes props1: "subst_props mvs subst1"
      and props2: "subst_props mvs subst2"
      and dom_disj: "fset (fmdom subst2) \<inter> fset (fmdom subst1) = {}"
      and range2_disj: "subst_range_tyvars subst2 \<inter> fset (fmdom subst1) = {}"
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
               type_tyvars ty \<subseteq> mvs"
  proof (intro allI impI)
    fix n ty
    assume lookup: "fmlookup (compose_subst subst2 subst1) n = Some ty"

    show "type_tyvars ty \<subseteq> mvs"
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
      from Some props1 have ty1_mvs: "type_tyvars ty1 \<subseteq> mvs"
        by (auto simp: subst_props_def)
      show ?thesis
        using ty_eq ty1_mvs props2 by (simp add: apply_subst_tyvars_subset)
    qed
  qed
next
  (* Domain and range of composition are disjoint *)
  show "fset (fmdom (compose_subst subst2 subst1)) \<inter> subst_range_tyvars (compose_subst subst2 subst1) = {}"
  proof -
    have dom_eq: "fmdom (compose_subst subst2 subst1) = fmdom subst2 |\<union>| fmdom subst1"
      by (simp add: compose_subst_def)
    (* Range of compose_subst subst2 subst1:
       For n in dom(subst1): apply_subst subst2 (subst1 n)
       For n in dom(subst2) \ dom(subst1): subst2 n *)
    have range_sub: "subst_range_tyvars (compose_subst subst2 subst1) \<subseteq>
                     subst_range_tyvars subst2 \<union> subst_range_tyvars subst1"
    proof
      fix x assume "x \<in> subst_range_tyvars (compose_subst subst2 subst1)"
      then obtain ty where ty_in: "ty \<in> fmran' (compose_subst subst2 subst1)"
                       and x_in: "x \<in> type_tyvars ty"
        by (auto simp: subst_range_tyvars_def)
      from ty_in obtain n where lookup: "fmlookup (compose_subst subst2 subst1) n = Some ty"
        by (auto simp: fmran'_def)
      show "x \<in> subst_range_tyvars subst2 \<union> subst_range_tyvars subst1"
      proof (cases "fmlookup subst1 n")
        case None
        hence "fmlookup subst2 n = Some ty"
          using lookup by (simp add: fmlookup_compose_subst_None1)
        hence "ty \<in> fmran' subst2" by (auto simp: fmran'_def)
        thus ?thesis using x_in by (auto simp: subst_range_tyvars_def)
      next
        case (Some ty1)
        hence ty_eq: "ty = apply_subst subst2 ty1"
          using lookup by (simp add: fmlookup_compose_subst_Some1)
        have ty1_in: "ty1 \<in> fmran' subst1" using Some by (auto simp: fmran'_def)
        from x_in[unfolded ty_eq] have "x \<in> type_tyvars (apply_subst subst2 ty1)" .
        hence "x \<in> (type_tyvars ty1 - fset (fmdom subst2)) \<union> subst_range_tyvars subst2"
          using apply_subst_tyvars_result by auto
        thus ?thesis
        proof
          assume "x \<in> type_tyvars ty1 - fset (fmdom subst2)"
          hence "x \<in> type_tyvars ty1" by auto
          thus ?thesis using ty1_in by (auto simp: subst_range_tyvars_def)
        next
          assume "x \<in> subst_range_tyvars subst2"
          thus ?thesis by auto
        qed
      qed
    qed
    (* Show disjointness directly *)
    have no_overlap: "\<And>n. n \<in> fset (fmdom (compose_subst subst2 subst1)) \<Longrightarrow>
                          n \<notin> subst_range_tyvars (compose_subst subst2 subst1)"
    proof -
      fix n
      assume n_in_dom: "n \<in> fset (fmdom (compose_subst subst2 subst1))"
      from n_in_dom have n_cases: "n \<in> fset (fmdom subst1) \<or> n \<in> fset (fmdom subst2)"
        using dom_eq by auto
      show "n \<notin> subst_range_tyvars (compose_subst subst2 subst1)"
      proof (cases "n \<in> fset (fmdom subst1)")
        case True
        (* n is in dom(subst1), so n \<notin> range(subst1) and n \<notin> range(subst2) by range2_disj *)
        have n_not_in_range1: "n \<notin> subst_range_tyvars subst1"
          using props1 True by (auto simp: subst_props_def)
        have n_not_in_range2: "n \<notin> subst_range_tyvars subst2"
          using range2_disj True by auto
        from range_sub n_not_in_range1 n_not_in_range2
        show ?thesis by auto
      next
        case False
        (* n \<in> dom(subst2) but n \<notin> dom(subst1) *)
        with n_cases have n_in_dom2: "n \<in> fset (fmdom subst2)" by auto
        have n_not_in_range2: "n \<notin> subst_range_tyvars subst2"
          using props2 n_in_dom2 by (auto simp: subst_props_def)
        (* Show n is not in range of composition *)
        show ?thesis
        proof
          assume n_in_range: "n \<in> subst_range_tyvars (compose_subst subst2 subst1)"
          from n_in_range obtain ty where ty_in: "ty \<in> fmran' (compose_subst subst2 subst1)"
                                      and n_in_ty: "n \<in> type_tyvars ty"
            by (auto simp: subst_range_tyvars_def)
          from ty_in obtain m where lookup: "fmlookup (compose_subst subst2 subst1) m = Some ty"
            by (auto simp: fmran'_def)
          show False
          proof (cases "fmlookup subst1 m")
            case None
            hence "fmlookup subst2 m = Some ty"
              using lookup by (simp add: fmlookup_compose_subst_None1)
            hence "ty \<in> fmran' subst2" by (auto simp: fmran'_def)
            hence "n \<in> subst_range_tyvars subst2" using n_in_ty by (auto simp: subst_range_tyvars_def)
            thus False using n_not_in_range2 by simp
          next
            case (Some ty1)
            hence ty_eq: "ty = apply_subst subst2 ty1"
              using lookup by (simp add: fmlookup_compose_subst_Some1)
            from n_in_ty[unfolded ty_eq]
            have "n \<in> (type_tyvars ty1 - fset (fmdom subst2)) \<union> subst_range_tyvars subst2"
              using apply_subst_tyvars_result by auto
            thus False
            proof
              assume "n \<in> type_tyvars ty1 - fset (fmdom subst2)"
              thus False using n_in_dom2 by auto
            next
              assume "n \<in> subst_range_tyvars subst2"
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
  assumes "subst_props (type_tyvars ty1 \<union> type_tyvars ty2) subst"
  shows "(Inr (f, map (apply_subst subst) rest1, map (apply_subst subst) rest2),
          Inr (f, ty1 # rest1, ty2 # rest2)) \<in> unify_rel"
proof (cases "subst = fmempty")
  case True
  (* With empty subst, size decreases since we remove heads *)
  have size_lt: "list_type_size (map (apply_subst subst) rest1) +
                 list_type_size (map (apply_subst subst) rest2)
              <  list_type_size (ty1 # rest1) + list_type_size (ty2 # rest2)"
    using True core_type_size_pos by (simp add: list_type_size_cons)
  moreover have "list_tyvars (map (apply_subst subst) rest1) \<union> list_tyvars (map (apply_subst subst) rest2)
                 \<subseteq> list_tyvars (ty1 # rest1) \<union> list_tyvars (ty2 # rest2)"
    using True by (auto simp: list_tyvars_def)
  hence "card (list_tyvars (map (apply_subst subst) rest1) \<union> list_tyvars (map (apply_subst subst) rest2))
         \<le> card (list_tyvars (ty1 # rest1) \<union> list_tyvars (ty2 # rest2))"
    by (simp add: card_mono finite_list_tyvars)
  ultimately show ?thesis
    unfolding unify_rel_def by auto
next
  case False
  (* Non-empty subst: metavar count decreases *)
  from False obtain n ty where binding: "fmlookup subst n = Some ty"
    by (metis fmap_ext fmempty_lookup option.exhaust)
  have n_in_heads: "n \<in> type_tyvars ty1 \<union> type_tyvars ty2"
    using assms binding unfolding subst_props_def
    by (meson fmdomI in_mono)
  have n_in_dom: "n \<in> fset (fmdom subst)"
    using binding by (simp add: fmlookup_dom_iff)
  have n_not_in_range: "n \<notin> subst_range_tyvars subst"
    using assms n_in_dom unfolding subst_props_def by auto
  have n_not_in_result: "n \<notin> list_tyvars (map (apply_subst subst) rest1) \<union>
                              list_tyvars (map (apply_subst subst) rest2)"
    using apply_subst_eliminates_dom[OF n_in_dom n_not_in_range]
    by (auto simp: list_tyvars_def)
  have result_subset: "list_tyvars (map (apply_subst subst) rest1) \<union>
                       list_tyvars (map (apply_subst subst) rest2)
                       \<subseteq> list_tyvars (ty1 # rest1) \<union> list_tyvars (ty2 # rest2)"
  proof -
    have dom_sub: "fset (fmdom subst) \<subseteq> type_tyvars ty1 \<union> type_tyvars ty2"
      using assms unfolding subst_props_def by auto
    have range_sub: "subst_range_tyvars subst \<subseteq> type_tyvars ty1 \<union> type_tyvars ty2"
      using assms unfolding subst_props_def subst_range_tyvars_def
      by fastforce
    have "\<And>t. t \<in> set rest1 \<Longrightarrow> type_tyvars (apply_subst subst t) \<subseteq>
              list_tyvars (ty1 # rest1) \<union> list_tyvars (ty2 # rest2)"
    proof -
      fix t assume "t \<in> set rest1"
      have "type_tyvars (apply_subst subst t) \<subseteq>
            (type_tyvars t - fset (fmdom subst)) \<union> subst_range_tyvars subst"
        by (rule apply_subst_tyvars_result)
      also have "... \<subseteq> type_tyvars t \<union> subst_range_tyvars subst" by auto
      also have "... \<subseteq> list_tyvars rest1 \<union> (type_tyvars ty1 \<union> type_tyvars ty2)"
        using \<open>t \<in> set rest1\<close> range_sub by (auto simp: list_tyvars_def)
      also have "... \<subseteq> list_tyvars (ty1 # rest1) \<union> list_tyvars (ty2 # rest2)"
        by (auto simp: list_tyvars_def)
      finally show "type_tyvars (apply_subst subst t) \<subseteq>
                    list_tyvars (ty1 # rest1) \<union> list_tyvars (ty2 # rest2)" .
    qed
    moreover have "\<And>t. t \<in> set rest2 \<Longrightarrow> type_tyvars (apply_subst subst t) \<subseteq>
              list_tyvars (ty1 # rest1) \<union> list_tyvars (ty2 # rest2)"
    proof -
      fix t assume "t \<in> set rest2"
      have "type_tyvars (apply_subst subst t) \<subseteq>
            (type_tyvars t - fset (fmdom subst)) \<union> subst_range_tyvars subst"
        by (rule apply_subst_tyvars_result)
      also have "... \<subseteq> type_tyvars t \<union> subst_range_tyvars subst" by auto
      also have "... \<subseteq> list_tyvars rest2 \<union> (type_tyvars ty1 \<union> type_tyvars ty2)"
        using \<open>t \<in> set rest2\<close> range_sub by (auto simp: list_tyvars_def)
      also have "... \<subseteq> list_tyvars (ty1 # rest1) \<union> list_tyvars (ty2 # rest2)"
        by (auto simp: list_tyvars_def)
      finally show "type_tyvars (apply_subst subst t) \<subseteq>
                    list_tyvars (ty1 # rest1) \<union> list_tyvars (ty2 # rest2)" .
    qed
    ultimately show ?thesis by (auto simp: list_tyvars_def)
  qed
  have n_in_orig: "n \<in> list_tyvars (ty1 # rest1) \<union> list_tyvars (ty2 # rest2)"
    using n_in_heads by (auto simp: list_tyvars_def)
  have strict_subset: "list_tyvars (map (apply_subst subst) rest1) \<union>
                       list_tyvars (map (apply_subst subst) rest2)
                       \<subset> list_tyvars (ty1 # rest1) \<union> list_tyvars (ty2 # rest2)"
    using result_subset n_not_in_result n_in_orig by auto
  hence "card (list_tyvars (map (apply_subst subst) rest1) \<union>
               list_tyvars (map (apply_subst subst) rest2))
         < card (list_tyvars (ty1 # rest1) \<union> list_tyvars (ty2 # rest2))"
    using finite_list_tyvars psubset_card_mono
    by (metis finite_Un)
  thus ?thesis
    unfolding unify_rel_def by auto
qed

(* The main inductive property: termination and props *)
definition unify_terminates_with_props ::
    "(((string \<Rightarrow> bool) \<times> CoreType \<times> CoreType) + ((string \<Rightarrow> bool) \<times> CoreType list \<times> CoreType list)) \<Rightarrow> bool" where
  "unify_terminates_with_props x \<equiv>
    unify_unify_list_dom x \<and>
    (case x of
      Inl (is_flex, ty1, ty2) \<Rightarrow>
        (\<forall>subst. unify is_flex ty1 ty2 = Some subst \<longrightarrow>
                 subst_props (unify_input_mvs ty1 ty2) subst)
    | Inr (is_flex, tys1, tys2) \<Rightarrow>
        (\<forall>subst. unify_list is_flex tys1 tys2 = Some subst \<longrightarrow>
                 subst_props (unify_list_input_mvs tys1 tys2) subst))"

(* Binding a variable to a type it does not occur in satisfies the properties,
   over the input variables of unifying that variable (on either side) with
   that type. *)
lemma subst_props_singleton_left:
  "\<not> occurs n ty \<Longrightarrow> subst_props (unify_input_mvs (CoreTy_Var n) ty) (singleton_subst n ty)"
  by (auto simp: unify_input_mvs_def intro: subst_props_singleton)

lemma subst_props_singleton_right:
  "\<not> occurs n ty \<Longrightarrow> subst_props (unify_input_mvs ty (CoreTy_Var n)) (singleton_subst n ty)"
  by (auto simp: unify_input_mvs_def intro: subst_props_singleton)

(* The argument pairs on which unify may make a recursive call. *)
fun unify_may_recurse :: "CoreType \<Rightarrow> CoreType \<Rightarrow> bool" where
  "unify_may_recurse (CoreTy_Datatype _ _) (CoreTy_Datatype _ _) = True"
| "unify_may_recurse (CoreTy_Record _) (CoreTy_Record _) = True"
| "unify_may_recurse (CoreTy_Array _ _) (CoreTy_Array _ _) = True"
| "unify_may_recurse _ _ = False"

(* On every other pair of arguments unify answers directly: None, the empty
   substitution, or a binding of one side's variable to the other side. *)
lemma unify_base_terminates:
  assumes base: "\<not> unify_may_recurse ty1 ty2"
  shows "unify_terminates_with_props (Inl (is_flex, ty1, ty2))"
proof -
  have dom: "unify_unify_list_dom (Inl (is_flex, ty1, ty2))"
    using base by (cases ty1; cases ty2) (auto intro: unify_unify_list.domintros)
  have "subst_props (unify_input_mvs ty1 ty2) s"
    if "unify is_flex ty1 ty2 = Some s" for s
    using base dom that
    by (cases ty1; cases ty2)
       (auto simp: unify.psimps occurs_def split: if_splits
             intro: subst_props_singleton_left subst_props_singleton_right)
  with dom show ?thesis
    unfolding unify_terminates_with_props_def by auto
qed

(* unify_list's cons step preserves the properties: the heads unify to subst1,
   then the tails, with subst1 applied, unify to subst2. *)
lemma unify_list_cons_props:
  assumes p1: "subst_props (unify_input_mvs ty1 ty2) subst1"
      and p2: "subst_props (unify_list_input_mvs (map (apply_subst subst1) rest1)
                                                  (map (apply_subst subst1) rest2)) subst2"
  shows "subst_props (unify_list_input_mvs (ty1 # rest1) (ty2 # rest2))
                     (compose_subst subst2 subst1)"
proof -
  define head_mvs where "head_mvs = type_tyvars ty1 \<union> type_tyvars ty2"
  define full_mvs where "full_mvs = list_tyvars (ty1 # rest1) \<union> list_tyvars (ty2 # rest2)"
  let ?rec_mvs = "list_tyvars (map (apply_subst subst1) rest1)
                  \<union> list_tyvars (map (apply_subst subst1) rest2)"
  have head_sub: "head_mvs \<subseteq> full_mvs"
    by (auto simp: head_mvs_def full_mvs_def list_tyvars_def)
  have props1_head: "subst_props head_mvs subst1"
    using p1 by (simp add: head_mvs_def unify_input_mvs_def)
  have props2_rec: "subst_props ?rec_mvs subst2"
    using p2 by (simp add: unify_list_input_mvs_def)
  have range1: "subst_range_tyvars subst1 \<subseteq> head_mvs"
    using props1_head unfolding subst_props_def subst_range_tyvars_def by fastforce

  \<comment> \<open>The tails, with subst1 applied, stay within full_mvs.\<close>
  have applied: "list_tyvars (map (apply_subst subst1) rs) \<subseteq> full_mvs"
    if rs_sub: "list_tyvars rs \<subseteq> full_mvs" for rs
  proof
    fix x assume "x \<in> list_tyvars (map (apply_subst subst1) rs)"
    then obtain t where t_in: "t \<in> set rs" and x_in: "x \<in> type_tyvars (apply_subst subst1 t)"
      by (auto simp: list_tyvars_def)
    from x_in have "x \<in> (type_tyvars t - fset (fmdom subst1)) \<union> subst_range_tyvars subst1"
      using apply_subst_tyvars_result by auto
    thus "x \<in> full_mvs"
      using t_in rs_sub range1 head_sub by (auto simp: list_tyvars_def)
  qed
  have rest1_sub: "list_tyvars rest1 \<subseteq> full_mvs"
    and rest2_sub: "list_tyvars rest2 \<subseteq> full_mvs"
    by (auto simp: full_mvs_def list_tyvars_def)
  have rec_sub: "?rec_mvs \<subseteq> full_mvs"
    using applied[OF rest1_sub] applied[OF rest2_sub] by blast

  have props1: "subst_props full_mvs subst1"
    using props1_head head_sub unfolding subst_props_def subst_range_tyvars_def by blast
  have props2: "subst_props full_mvs subst2"
    using props2_rec rec_sub unfolding subst_props_def subst_range_tyvars_def by blast

  \<comment> \<open>subst1's domain is eliminated from the tails, and subst2 lives there.\<close>
  have elim: "n \<notin> ?rec_mvs" if n_in: "n \<in> fset (fmdom subst1)" for n
  proof -
    have "n \<notin> subst_range_tyvars subst1"
      using props1_head n_in by (auto simp: subst_props_def)
    thus ?thesis
      using apply_subst_eliminates_dom[OF n_in] by (auto simp: list_tyvars_def)
  qed
  have dom_disj: "fset (fmdom subst2) \<inter> fset (fmdom subst1) = {}"
  proof -
    have "fset (fmdom subst2) \<subseteq> ?rec_mvs"
      using props2_rec by (auto simp: subst_props_def)
    thus ?thesis using elim by blast
  qed
  have range2_disj: "subst_range_tyvars subst2 \<inter> fset (fmdom subst1) = {}"
  proof -
    have "subst_range_tyvars subst2 \<subseteq> ?rec_mvs"
      using props2_rec unfolding subst_props_def subst_range_tyvars_def by fastforce
    thus ?thesis using elim by blast
  qed

  show ?thesis
    using subst_props_compose[OF props1 props2 dom_disj range2_disj]
    by (simp add: full_mvs_def unify_list_input_mvs_def)
qed

(* The main theorem: all inputs terminate with props. The base cases are
   unify_base_terminates; the structural recursions of unify, and unify_list's
   cons step, use the IH on the recursive calls. *)
lemma unify_terminates_with_props_all:
  "unify_terminates_with_props x"
proof (induction x rule: wf_induct_rule[OF wf_unify_rel])
  case (1 x)
  show ?case
  proof (cases x)
    case (Inl triple)
    then obtain is_flex ty1 ty2 where x_eq: "x = Inl (is_flex, ty1, ty2)"
      by (cases triple) auto
    show ?thesis
    proof (cases "unify_may_recurse ty1 ty2")
      case False
      thus ?thesis unfolding x_eq by (rule unify_base_terminates)
    next
      case True
      then consider
          (Datatype) name1 args1 name2 args2 where
            "ty1 = CoreTy_Datatype name1 args1" "ty2 = CoreTy_Datatype name2 args2"
        | (Record) flds1 flds2 where
            "ty1 = CoreTy_Record flds1" "ty2 = CoreTy_Record flds2"
        | (Array) elem1 dims1 elem2 dims2 where
            "ty1 = CoreTy_Array elem1 dims1" "ty2 = CoreTy_Array elem2 dims2"
        by (cases ty1; cases ty2) auto
      then show ?thesis
      proof cases
        case Datatype
        \<comment> \<open>unify_list on the type arguments (if the names agree).\<close>
        have "(Inr (is_flex, args1, args2), x) \<in> unify_rel"
          unfolding x_eq Datatype by (rule unify_rel_name_to_list)
        hence "unify_terminates_with_props (Inr (is_flex, args1, args2))"
          using "1" by blast
        hence list_dom: "unify_unify_list_dom (Inr (is_flex, args1, args2))"
          and list_props: "\<And>s. unify_list is_flex args1 args2 = Some s \<Longrightarrow>
                                  subst_props (unify_list_input_mvs args1 args2) s"
          by (auto simp: unify_terminates_with_props_def)
        have dom: "unify_unify_list_dom (Inl (is_flex, ty1, ty2))"
          unfolding Datatype using list_dom by (auto intro: unify_unify_list.domintros)
        have result: "unify is_flex ty1 ty2
                        = (if name1 = name2 then unify_list is_flex args1 args2 else None)"
          using dom unfolding Datatype by (simp add: unify.psimps)
        have mvs_eq: "unify_list_input_mvs args1 args2 = unify_input_mvs ty1 ty2"
          unfolding Datatype
          by (auto simp: unify_list_input_mvs_def unify_input_mvs_def list_tyvars_def)
        show ?thesis
          unfolding x_eq unify_terminates_with_props_def
          using dom result list_props mvs_eq by (auto split: if_splits)
      next
        case Record
        \<comment> \<open>unify_list on the field types (if the field names agree).\<close>
        have "(Inr (is_flex, map snd flds1, map snd flds2), x) \<in> unify_rel"
          unfolding x_eq Record by (rule unify_rel_record_to_list)
        hence "unify_terminates_with_props (Inr (is_flex, map snd flds1, map snd flds2))"
          using "1" by blast
        hence list_dom: "unify_unify_list_dom (Inr (is_flex, map snd flds1, map snd flds2))"
          and list_props: "\<And>s. unify_list is_flex (map snd flds1) (map snd flds2) = Some s \<Longrightarrow>
                                  subst_props (unify_list_input_mvs (map snd flds1)
                                                                    (map snd flds2)) s"
          by (auto simp: unify_terminates_with_props_def)
        have dom: "unify_unify_list_dom (Inl (is_flex, ty1, ty2))"
          unfolding Record using list_dom by (auto intro: unify_unify_list.domintros)
        have result: "unify is_flex ty1 ty2
                        = (if map fst flds1 = map fst flds2
                           then unify_list is_flex (map snd flds1) (map snd flds2) else None)"
          using dom unfolding Record by (simp add: unify.psimps)
        have mvs_eq: "unify_list_input_mvs (map snd flds1) (map snd flds2)
                        = unify_input_mvs ty1 ty2"
          unfolding Record
          by (auto simp: unify_list_input_mvs_def unify_input_mvs_def list_tyvars_def comp_def)
        show ?thesis
          unfolding x_eq unify_terminates_with_props_def
          using dom result list_props mvs_eq by (auto split: if_splits)
      next
        case Array
        \<comment> \<open>unify on the element types (if the dimensions agree).\<close>
        have "(Inl (is_flex, elem1, elem2), x) \<in> unify_rel"
          unfolding x_eq Array by (rule unify_rel_array_to_elem)
        hence "unify_terminates_with_props (Inl (is_flex, elem1, elem2))"
          using "1" by blast
        hence elem_dom: "unify_unify_list_dom (Inl (is_flex, elem1, elem2))"
          and elem_props: "\<And>s. unify is_flex elem1 elem2 = Some s \<Longrightarrow>
                                  subst_props (unify_input_mvs elem1 elem2) s"
          by (auto simp: unify_terminates_with_props_def)
        have dom: "unify_unify_list_dom (Inl (is_flex, ty1, ty2))"
          unfolding Array using elem_dom by (auto intro: unify_unify_list.domintros)
        have result: "unify is_flex ty1 ty2
                        = (if dims1 = dims2 then unify is_flex elem1 elem2 else None)"
          using dom unfolding Array by (simp add: unify.psimps)
        have mvs_eq: "unify_input_mvs elem1 elem2 = unify_input_mvs ty1 ty2"
          unfolding Array by (auto simp: unify_input_mvs_def)
        show ?thesis
          unfolding x_eq unify_terminates_with_props_def
          using dom result elem_props mvs_eq by (auto split: if_splits)
      qed
    qed
  next
    case (Inr triple)
    then obtain is_flex tys1 tys2 where x_eq: "x = Inr (is_flex, tys1, tys2)"
      by (cases triple) auto
    show ?thesis
    proof (cases "\<exists>ty1 rest1 ty2 rest2. tys1 = ty1 # rest1 \<and> tys2 = ty2 # rest2")
      case False
      \<comment> \<open>At least one list is empty: unify_list answers directly.\<close>
      hence dom: "unify_unify_list_dom (Inr (is_flex, tys1, tys2))"
        by (cases tys1; cases tys2) (auto intro: unify_unify_list.domintros)
      show ?thesis
        unfolding x_eq unify_terminates_with_props_def
        using False dom by (cases tys1; cases tys2) (auto simp: unify_list.psimps)
    next
      case True
      then obtain ty1 rest1 ty2 rest2 where
        tys1_eq: "tys1 = ty1 # rest1" and tys2_eq: "tys2 = ty2 # rest2"
        by blast
      \<comment> \<open>IH on the heads.\<close>
      have "(Inl (is_flex, ty1, ty2), x) \<in> unify_rel"
        unfolding x_eq tys1_eq tys2_eq by (rule unify_rel_list_to_head)
      hence "unify_terminates_with_props (Inl (is_flex, ty1, ty2))"
        using "1" by blast
      hence head_dom: "unify_unify_list_dom (Inl (is_flex, ty1, ty2))"
        and head_props: "\<And>s. unify is_flex ty1 ty2 = Some s \<Longrightarrow>
                                subst_props (unify_input_mvs ty1 ty2) s"
        by (auto simp: unify_terminates_with_props_def)
      show ?thesis
      proof (cases "unify is_flex ty1 ty2")
        case None
        have dom: "unify_unify_list_dom (Inr (is_flex, tys1, tys2))"
          unfolding tys1_eq tys2_eq using head_dom None
          by (auto intro: unify_unify_list.domintros)
        show ?thesis
          unfolding x_eq unify_terminates_with_props_def
          using dom head_dom None by (auto simp: tys1_eq tys2_eq unify_list.psimps)
      next
        case (Some subst1)
        \<comment> \<open>IH on the tails, with subst1 applied.\<close>
        let ?rest1' = "map (apply_subst subst1) rest1"
        let ?rest2' = "map (apply_subst subst1) rest2"
        have "(Inr (is_flex, ?rest1', ?rest2'), x) \<in> unify_rel"
          unfolding x_eq tys1_eq tys2_eq
          using head_props[OF Some] by (metis unify_input_mvs_def unify_rel_list_recursive)
        hence "unify_terminates_with_props (Inr (is_flex, ?rest1', ?rest2'))"
          using "1" by blast
        hence tail_dom: "unify_unify_list_dom (Inr (is_flex, ?rest1', ?rest2'))"
          and tail_props: "\<And>s. unify_list is_flex ?rest1' ?rest2' = Some s \<Longrightarrow>
                                  subst_props (unify_list_input_mvs ?rest1' ?rest2') s"
          by (auto simp: unify_terminates_with_props_def)
        have dom: "unify_unify_list_dom (Inr (is_flex, tys1, tys2))"
          unfolding tys1_eq tys2_eq using head_dom tail_dom Some
          by (auto intro: unify_unify_list.domintros)
        show ?thesis
          unfolding x_eq unify_terminates_with_props_def
          using dom head_dom Some tail_props head_props[OF Some]
          by (auto simp: tys1_eq tys2_eq unify_list.psimps split: option.splits
                   intro: unify_list_cons_props)
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

