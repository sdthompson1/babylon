theory Unify2
  imports Unify
begin

(* This file proves some properties of unify and unify_list. *)


(* ========================================================================== *)
(* unify_list succeeds only on equal length lists                             *)
(* ========================================================================== *)

lemma unify_list_length:
  "unify_list tys1 tys2 = Some subst \<Longrightarrow> length tys1 = length tys2"
proof (induction "length tys1 + length tys2" arbitrary: tys1 tys2 subst rule: less_induct)
  case less
  then show ?case
  proof (cases tys1)
    case Nil
    then show ?thesis using less.prems by (cases tys2; simp)
  next
    case (Cons ty1 rest1)
    then show ?thesis
    proof (cases tys2)
      case Nil
      then show ?thesis using Cons less.prems by simp
    next
      case (Cons ty2 rest2)
      from less.prems Cons \<open>tys1 = ty1 # rest1\<close> obtain s1 s2 where
        "unify ty1 ty2 = Some s1" and
        rest: "unify_list (map (apply_subst s1) rest1) (map (apply_subst s1) rest2) = Some s2"
        by (auto split: option.splits)
      have "length (map (apply_subst s1) rest1) + length (map (apply_subst s1) rest2) < length tys1 + length tys2"
        using \<open>tys1 = ty1 # rest1\<close> Cons by simp
      from less.hyps[OF this rest]
      have "length (map (apply_subst s1) rest1) = length (map (apply_subst s1) rest2)" .
      thus ?thesis using \<open>tys1 = ty1 # rest1\<close> Cons by simp
    qed
  qed
qed


(* ========================================================================== *)
(* Soundness of unification                                                    *)
(* ========================================================================== *)

(* Helper lemma for soundness proof: if field names match and field types unify,
   then the transformed field lists satisfy the types_equal_Record predicate *)
lemma record_fields_types_equal:
  assumes len_eq: "length flds1 = length flds2"
      and names_eq: "map fst flds1 = map fst flds2"
      and types_eq: "list_all (\<lambda>(t1, t2). types_equal (apply_subst subst t1) (apply_subst subst t2))
                    (zip (map snd flds1) (map snd flds2))"
    shows "list_all (\<lambda>(f1, f2). fst f1 = fst f2 \<and> types_equal (snd f1) (snd f2))
                    (zip (map (\<lambda>(name, ty). (name, apply_subst subst ty)) flds1)
                         (map (\<lambda>(name, ty). (name, apply_subst subst ty)) flds2))"
proof -
  let ?flds1' = "map (\<lambda>(name, ty). (name, apply_subst subst ty)) flds1"
  let ?flds2' = "map (\<lambda>(name, ty). (name, apply_subst subst ty)) flds2"
  have len_eq': "length ?flds1' = length ?flds2'" using len_eq by simp
  have "\<forall>i < length ?flds1'. fst (?flds1' ! i) = fst (?flds2' ! i) \<and>
                              types_equal (snd (?flds1' ! i)) (snd (?flds2' ! i))"
  proof (intro allI impI)
    fix i assume "i < length ?flds1'"
    hence i_bound: "i < length flds1" by simp
    hence i_bound2: "i < length flds2" using len_eq by simp
    (* fst part *)
    have "fst (?flds1' ! i) = fst (flds1 ! i)"
      using i_bound by (simp add: case_prod_beta)
    also have "... = fst (flds2 ! i)"
      using names_eq i_bound i_bound2 by (metis nth_map)
    also have "... = fst (?flds2' ! i)"
      using i_bound2 by (simp add: case_prod_beta)
    finally have fst_eq: "fst (?flds1' ! i) = fst (?flds2' ! i)" .
    (* snd part *)
    have "snd (?flds1' ! i) = apply_subst subst (snd (flds1 ! i))"
      using i_bound by (simp add: case_prod_beta)
    moreover have "snd (?flds2' ! i) = apply_subst subst (snd (flds2 ! i))"
      using i_bound2 by (simp add: case_prod_beta)
    moreover have "types_equal (apply_subst subst (snd (flds1 ! i)))
                               (apply_subst subst (snd (flds2 ! i)))"
      using types_eq i_bound len_eq by (simp add: list_all_length)
    ultimately have snd_eq: "types_equal (snd (?flds1' ! i)) (snd (?flds2' ! i))" by simp
    show "fst (?flds1' ! i) = fst (?flds2' ! i) \<and> types_equal (snd (?flds1' ! i)) (snd (?flds2' ! i))"
      using fst_eq snd_eq by simp
  qed
  thus ?thesis using len_eq' by (simp add: list_all_length del: types_equal.simps)
qed

(* Soundness theorem: If unify succeeds, the substitution makes the types equal. *)

theorem unify_sound:
  "unify ty1 ty2 = Some subst \<Longrightarrow>
     types_equal (apply_subst subst ty1) (apply_subst subst ty2)"
and unify_list_sound:
  "unify_list tys1 tys2 = Some subst \<Longrightarrow>
      list_all (\<lambda>(t1, t2). types_equal (apply_subst subst t1) (apply_subst subst t2)) (zip tys1 tys2)"
proof (induction ty1 ty2 and tys1 tys2 arbitrary: subst and subst rule: unify_unify_list.induct)
  case (1 n m)
  then show ?case
    by (metis apply_subst_singleton apply_subst_singleton_other option.inject types_equal_reflexive
        unify.simps(1))
next
  case (2 n loc name tyargs)
  then show ?case
    by (metis apply_subst_singleton apply_subst_singleton_no_occurs option.distinct(1)
        option.inject types_equal_reflexive unify.simps(2))
next
  case (3 n loc)
  then show ?case
    by (metis apply_subst.simps(3) apply_subst_singleton
        option.inject types_equal_reflexive unify.simps(3))
next
  case (4 n loc sign bits)
  then show ?case
    by (metis apply_subst.simps(4) apply_subst_singleton option.inject
        types_equal_reflexive unify.simps(4))
next
  case (5 n loc)
  then show ?case
    by (metis apply_subst.simps(5) apply_subst_singleton option.inject
        types_equal_reflexive unify.simps(5))
next
  case (6 n loc)
  then show ?case
    by (metis apply_subst.simps(6) apply_subst_singleton option.inject
        types_equal_reflexive unify.simps(6))
next
  case (7 n loc tys)
  then show ?case
    by (metis apply_subst_singleton apply_subst_singleton_no_occurs option.distinct(1)
        option.inject types_equal_reflexive unify.simps(7))
next
  case (8 n loc flds)
  then show ?case
    by (metis apply_subst_singleton apply_subst_singleton_no_occurs option.distinct(1)
        option.inject types_equal_reflexive unify.simps(8))
next
  case (9 n loc elem dims)
  then show ?case
    by (metis apply_subst_singleton apply_subst_singleton_no_occurs option.distinct(1)
        option.inject types_equal_reflexive unify.simps(9))
next
  case (10 loc name tyargs n)
  then show ?case
    by (metis apply_subst_singleton apply_subst_singleton_no_occurs option.distinct(1)
        option.inject types_equal_reflexive unify.simps(10))
next
  case (11 loc n)
  then show ?case
    by (metis apply_subst.simps(3) apply_subst_singleton option.inject
        types_equal_reflexive unify.simps(11))
next
  case (12 loc sign bits n)
  then show ?case
    by (metis apply_subst.simps(4) apply_subst_singleton option.inject
        types_equal_reflexive unify.simps(12))
next
  case (13 loc n)
  then show ?case
    by (metis apply_subst.simps(5) apply_subst_singleton option.inject
        types_equal_reflexive unify.simps(13))
next
  case (14 loc n)
  then show ?case
    by (metis apply_subst.simps(6) apply_subst_singleton option.inject
        types_equal_reflexive unify.simps(14))
next
  case (15 loc tys n)
  then show ?case
    by (metis apply_subst_singleton apply_subst_singleton_no_occurs option.distinct(1)
        option.inject types_equal_reflexive unify.simps(15))
next
  case (16 loc flds n)
  then show ?case
    by (metis apply_subst_singleton apply_subst_singleton_no_occurs option.distinct(1)
        option.inject types_equal_reflexive unify.simps(16))
next
  case (17 loc elem dims n)
  then show ?case
    by (metis apply_subst_singleton apply_subst_singleton_no_occurs option.distinct(1)
        option.inject types_equal_reflexive unify.simps(17))
next
  case (18 uu uv)
  then show ?case by (simp add: types_equal_reflexive)
next
  case (19 uw s1 b1 ux s2 b2)
  then show ?case by (auto simp: types_equal_reflexive split: if_splits)
next
  case (20 uy uz)
  then show ?case by (simp add: types_equal_reflexive)
next
  case (21 va vb)
  then show ?case by (simp add: types_equal_reflexive)
next
  case (22 vc n1 args1 vd n2 args2)
  then show ?case
  proof (cases "n1 = n2 \<and> length args1 = length args2")
    case True
    with 22 have "unify_list args1 args2 = Some subst" by simp
    with 22 True have "list_all (\<lambda>(t1, t2). types_equal (apply_subst subst t1) (apply_subst subst t2))
                                (zip args1 args2)" by simp
    then have "list_all (\<lambda>(t1, t2). types_equal t1 t2)
                        (zip (map (apply_subst subst) args1) (map (apply_subst subst) args2))"
      by (simp add: list_all_length)
    then show ?thesis using True by (simp add: types_equal_Name del: types_equal.simps)
  next
    case False
    then show ?thesis using 22 by auto
  qed
next
  case (23 ve tys1 vf tys2)
  then show ?case
  proof (cases "length tys1 = length tys2")
    case True
    with 23 have "unify_list tys1 tys2 = Some subst" by simp
    with 23 True have "list_all (\<lambda>(t1, t2). types_equal (apply_subst subst t1) (apply_subst subst t2))
                                (zip tys1 tys2)" by simp
    then have "list_all (\<lambda>(t1, t2). types_equal t1 t2)
                        (zip (map (apply_subst subst) tys1) (map (apply_subst subst) tys2))"
      by (simp add: list_all_length)
    then show ?thesis using True by (simp add: types_equal_Tuple del: types_equal.simps)
  next
    case False
    then show ?thesis using 23 by simp
  qed
next
  case (24 vg flds1 vh flds2)
  then show ?case
  proof (cases "length flds1 = length flds2 \<and> map fst flds1 = map fst flds2")
    case True
    with 24 have "unify_list (map snd flds1) (map snd flds2) = Some subst" by simp
    with 24 True have types_eq: "list_all (\<lambda>(t1, t2). types_equal (apply_subst subst t1) (apply_subst subst t2))
                                          (zip (map snd flds1) (map snd flds2))" by simp
    from True have len_eq: "length flds1 = length flds2" and fld_names_eq: "map fst flds1 = map fst flds2"
      by simp_all
    let ?flds1' = "map (\<lambda>(name, ty). (name, apply_subst subst ty)) flds1"
    let ?flds2' = "map (\<lambda>(name, ty). (name, apply_subst subst ty)) flds2"
    have len_eq': "length ?flds1' = length ?flds2'" using len_eq by simp
    from record_fields_types_equal[OF len_eq fld_names_eq types_eq]
    have "list_all (\<lambda>(f1, f2). fst f1 = fst f2 \<and> types_equal (snd f1) (snd f2)) (zip ?flds1' ?flds2')" .
    then show ?thesis using len_eq' by (simp add: types_equal_Record del: types_equal.simps)
  next
    case False
    then show ?thesis using 24 by auto
  qed
next
  case (25 vi elem1 dims1 vj elem2 dims2)
  then show ?case
  proof (cases "dims1 = dims2")
    case True
    with 25 have "unify elem1 elem2 = Some subst" by simp
    with 25 True have "types_equal (apply_subst subst elem1) (apply_subst subst elem2)" by simp
    then show ?thesis using True by simp
  next
    case False
    then show ?thesis using 25 by simp
  qed
next
  (* unify_list cases *)
  case 82
  then show ?case by simp
next
  case (83 ty1 rest1 ty2 rest2)
  from 83(3) obtain subst1 subst2 where
    unify_head: "unify ty1 ty2 = Some subst1" and
    unify_rest: "unify_list (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2) = Some subst2" and
    subst_compose: "subst = compose_subst subst2 subst1"
    by (auto split: option.splits)
  from 83(1)[OF unify_head]
  have head_eq: "types_equal (apply_subst subst1 ty1) (apply_subst subst1 ty2)" .
  from 83(2)[OF unify_head unify_rest]
  have "list_all (\<lambda>(t1, t2). types_equal (apply_subst subst2 t1) (apply_subst subst2 t2))
                 (zip (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2))" .
  then have rest_eq: "list_all (\<lambda>(t1, t2). types_equal (apply_subst subst t1) (apply_subst subst t2))
                               (zip rest1 rest2)"
    using subst_compose by (simp add: list_all_length compose_subst_correct)
  from types_equal_apply_subst[OF head_eq, of subst2]
  have "types_equal (apply_subst subst2 (apply_subst subst1 ty1))
                    (apply_subst subst2 (apply_subst subst1 ty2))" .
  hence "types_equal (apply_subst subst ty1) (apply_subst subst ty2)"
    using subst_compose compose_subst_correct by simp
  then show ?case using rest_eq by simp
qed (simp_all)


(* ========================================================================== *)
(* Most General Unifier (MGU) property                                        *)
(* ========================================================================== *)

(* The MGU property states that the unifier returned by unify is "most general":
   any other unifier can be expressed by composing some substitution with the MGU.

   More precisely: if unify returns subst1, and subst2 also unifies ty1 and ty2,
   then there exists subst' such that subst2 = subst' \<circ> subst1
   (subst2 factors through subst1).
*)

(* Helper: if subst' unifies Meta n with ty (via types_equal), then applying subst' to the result
   of singleton_subst n ty gives a types_equal result to applying subst' directly *)
lemma unifier_factors_singleton:
  assumes unifies: "types_equal (apply_subst subst' (BabTy_Meta n)) (apply_subst subst' ty)"
      and no_occurs: "\<not> occurs n ty"
    shows "\<forall>ty'. types_equal (apply_subst subst' ty') (apply_subst subst' (apply_subst (singleton_subst n ty) ty'))"
proof (intro allI)
  fix ty'
  show "types_equal (apply_subst subst' ty') (apply_subst subst' (apply_subst (singleton_subst n ty) ty'))"
  proof (induction "singleton_subst n ty" ty' rule: apply_subst.induct)
    case (1 m)
    show ?case
    proof (cases "n = m")
      case True
      then have "apply_subst (singleton_subst n ty) (BabTy_Meta m) = ty"
        by (simp add: singleton_subst_def)
      moreover have "types_equal (apply_subst subst' (BabTy_Meta m)) (apply_subst subst' ty)"
        using unifies True by simp
      ultimately show ?thesis by simp
    next
      case False
      then show ?thesis by (simp add: singleton_subst_def types_equal_reflexive del: types_equal.simps)
    qed
  next
    case (2 loc name tyargs)
    then show ?case
      by (simp add: types_equal_Name list_all_length del: types_equal.simps)
  next
    case (3 loc)
    then show ?case by (simp add: types_equal_reflexive)
  next
    case (4 loc sign bits)
    then show ?case by (simp add: types_equal_reflexive)
  next
    case (5 loc)
    then show ?case by (simp add: types_equal_reflexive)
  next
    case (6 loc)
    then show ?case by (simp add: types_equal_reflexive)
  next
    case (7 loc types)
    then show ?case
      by (simp add: types_equal_Tuple list_all_length del: types_equal.simps)
  next
    case (8 loc flds)
    have "\<forall>x\<in>set flds. types_equal (apply_subst subst' (snd x)) (apply_subst subst' (apply_subst (singleton_subst n ty) (snd x)))"
    proof
      fix x assume "x \<in> set flds"
      then show "types_equal (apply_subst subst' (snd x)) (apply_subst subst' (apply_subst (singleton_subst n ty) (snd x)))"
        using "8" prod.collapse by blast
    qed
    then show ?case by (simp add: types_equal_Record list_all_length case_prod_beta del: types_equal.simps)
  next
    case (9 loc elem dims)
    then show ?case by simp
  qed
qed

(* Main MGU theorem, proved by mutual induction *)
(* See also corollary below for a more standard "textbook" form of this *)
lemma unify_mgu:
  "unify ty1 ty2 = Some subst \<Longrightarrow>
     types_equal (apply_subst subst' ty1) (apply_subst subst' ty2) \<Longrightarrow>
     types_equal (apply_subst subst' ty) (apply_subst subst' (apply_subst subst ty))"
  and unify_list_mgu:
  "unify_list tys1 tys2 = Some subst \<Longrightarrow>
     list_all (\<lambda>(t1, t2). types_equal (apply_subst subst' t1) (apply_subst subst' t2)) (zip tys1 tys2) \<Longrightarrow>
     types_equal (apply_subst subst' ty) (apply_subst subst' (apply_subst subst ty))"
proof (induction ty1 ty2 and tys1 tys2 arbitrary: subst subst' ty and subst subst' ty rule: unify_unify_list.induct)
  (* Case 1: Meta/Meta *)
  case (1 n m)
  show ?case
  proof (cases "n = m")
    case True
    then have "subst = fmempty" using 1 by simp
    then show ?thesis by (simp add: types_equal_reflexive del: types_equal.simps)
  next
    case False
    then have subst_eq: "subst = singleton_subst n (BabTy_Meta m)" using 1 by simp
    from 1(2) have unifies': "types_equal (apply_subst subst' (BabTy_Meta n)) (apply_subst subst' (BabTy_Meta m))" by simp
    have no_occurs: "\<not> occurs n (BabTy_Meta m)" using False by (simp add: occurs_def)
    show ?thesis using unifier_factors_singleton[OF unifies' no_occurs] subst_eq by blast
  qed
next
  (* Cases 2-9: Meta on left, non-meta on right *)
  case (2 n loc name tyargs)
  then have "subst = singleton_subst n (BabTy_Name loc name tyargs)" and "\<not> occurs n (BabTy_Name loc name tyargs)"
    by (auto split: if_splits)
  moreover have "types_equal (apply_subst subst' (BabTy_Meta n)) (apply_subst subst' (BabTy_Name loc name tyargs))"
    using 2(2) by simp
  ultimately show ?case using unifier_factors_singleton by blast
next
  case (3 n loc)
  then have "subst = singleton_subst n (BabTy_Bool loc)" and "\<not> occurs n (BabTy_Bool loc)"
    by (auto simp: occurs_def)
  moreover have "types_equal (apply_subst subst' (BabTy_Meta n)) (apply_subst subst' (BabTy_Bool loc))"
    using 3(2) by simp
  ultimately show ?case using unifier_factors_singleton by blast
next
  case (4 n loc sign bits)
  then have "subst = singleton_subst n (BabTy_FiniteInt loc sign bits)" and "\<not> occurs n (BabTy_FiniteInt loc sign bits)"
    by (auto simp: occurs_def)
  moreover have "types_equal (apply_subst subst' (BabTy_Meta n)) (apply_subst subst' (BabTy_FiniteInt loc sign bits))"
    using 4(2) by simp
  ultimately show ?case using unifier_factors_singleton by blast
next
  case (5 n loc)
  then have "subst = singleton_subst n (BabTy_MathInt loc)" and "\<not> occurs n (BabTy_MathInt loc)"
    by (auto simp: occurs_def)
  moreover have "types_equal (apply_subst subst' (BabTy_Meta n)) (apply_subst subst' (BabTy_MathInt loc))"
    using 5(2) by simp
  ultimately show ?case using unifier_factors_singleton by blast
next
  case (6 n loc)
  then have "subst = singleton_subst n (BabTy_MathReal loc)" and "\<not> occurs n (BabTy_MathReal loc)"
    by (auto simp: occurs_def)
  moreover have "types_equal (apply_subst subst' (BabTy_Meta n)) (apply_subst subst' (BabTy_MathReal loc))"
    using 6(2) by simp
  ultimately show ?case using unifier_factors_singleton by blast
next
  case (7 n loc tys)
  then have "subst = singleton_subst n (BabTy_Tuple loc tys)" and "\<not> occurs n (BabTy_Tuple loc tys)"
    by (auto split: if_splits)
  moreover have "types_equal (apply_subst subst' (BabTy_Meta n)) (apply_subst subst' (BabTy_Tuple loc tys))"
    using 7(2) by simp
  ultimately show ?case using unifier_factors_singleton by blast
next
  case (8 n loc flds)
  then have "subst = singleton_subst n (BabTy_Record loc flds)" and "\<not> occurs n (BabTy_Record loc flds)"
    by (auto split: if_splits)
  moreover have "types_equal (apply_subst subst' (BabTy_Meta n)) (apply_subst subst' (BabTy_Record loc flds))"
    using 8(2) by simp
  ultimately show ?case using unifier_factors_singleton by blast
next
  case (9 n loc elem dims)
  then have "subst = singleton_subst n (BabTy_Array loc elem dims)" and "\<not> occurs n (BabTy_Array loc elem dims)"
    by (auto split: if_splits)
  moreover have "types_equal (apply_subst subst' (BabTy_Meta n)) (apply_subst subst' (BabTy_Array loc elem dims))"
    using 9(2) by simp
  ultimately show ?case using unifier_factors_singleton by blast
next
  (* Cases 10-17: Non-meta on left, meta on right *)
  case (10 loc name tyargs n)
  then have "subst = singleton_subst n (BabTy_Name loc name tyargs)" and "\<not> occurs n (BabTy_Name loc name tyargs)"
    by (auto split: if_splits)
  moreover have "types_equal (apply_subst subst' (BabTy_Name loc name tyargs)) (apply_subst subst' (BabTy_Meta n))"
    using 10(2) types_equal_symmetric by (simp del: types_equal.simps)
  ultimately show ?case using unifier_factors_singleton types_equal_symmetric by blast
next
  case (11 loc n)
  then have "subst = singleton_subst n (BabTy_Bool loc)" and "\<not> occurs n (BabTy_Bool loc)"
    by (auto simp: occurs_def)
  moreover have "types_equal (apply_subst subst' (BabTy_Bool loc)) (apply_subst subst' (BabTy_Meta n))"
    using 11(2) types_equal_symmetric by auto
  ultimately show ?case using unifier_factors_singleton types_equal_symmetric by blast
next
  case (12 loc sign bits n)
  then have "subst = singleton_subst n (BabTy_FiniteInt loc sign bits)" and "\<not> occurs n (BabTy_FiniteInt loc sign bits)"
    by (auto simp: occurs_def)
  moreover have "types_equal (apply_subst subst' (BabTy_FiniteInt loc sign bits)) (apply_subst subst' (BabTy_Meta n))"
    using 12(2) types_equal_symmetric by (simp del: types_equal.simps)
  ultimately show ?case using unifier_factors_singleton types_equal_symmetric by blast
next
  case (13 loc n)
  then have "subst = singleton_subst n (BabTy_MathInt loc)" and "\<not> occurs n (BabTy_MathInt loc)"
    by (auto simp: occurs_def)
  moreover have "types_equal (apply_subst subst' (BabTy_MathInt loc)) (apply_subst subst' (BabTy_Meta n))"
    using 13(2) types_equal_symmetric by auto
  ultimately show ?case using unifier_factors_singleton types_equal_symmetric by blast
next
  case (14 loc n)
  then have "subst = singleton_subst n (BabTy_MathReal loc)" and "\<not> occurs n (BabTy_MathReal loc)"
    by (auto simp: occurs_def)
  moreover have "types_equal (apply_subst subst' (BabTy_MathReal loc)) (apply_subst subst' (BabTy_Meta n))"
    using 14(2) types_equal_symmetric by auto
  ultimately show ?case using unifier_factors_singleton types_equal_symmetric by blast
next
  case (15 loc tys n)
  then have "subst = singleton_subst n (BabTy_Tuple loc tys)" and "\<not> occurs n (BabTy_Tuple loc tys)"
    by (auto split: if_splits)
  moreover have "types_equal (apply_subst subst' (BabTy_Tuple loc tys)) (apply_subst subst' (BabTy_Meta n))"
    using 15(2) types_equal_symmetric by (simp del: types_equal.simps)
  ultimately show ?case using unifier_factors_singleton types_equal_symmetric by blast
next
  case (16 loc flds n)
  then have "subst = singleton_subst n (BabTy_Record loc flds)" and "\<not> occurs n (BabTy_Record loc flds)"
    by (auto split: if_splits)
  moreover have "types_equal (apply_subst subst' (BabTy_Record loc flds)) (apply_subst subst' (BabTy_Meta n))"
    using 16(2) types_equal_symmetric by (simp del: types_equal.simps)
  ultimately show ?case using unifier_factors_singleton types_equal_symmetric by blast
next
  case (17 loc elem dims n)
  then have "subst = singleton_subst n (BabTy_Array loc elem dims)" and "\<not> occurs n (BabTy_Array loc elem dims)"
    by (auto split: if_splits)
  moreover have "types_equal (apply_subst subst' (BabTy_Array loc elem dims)) (apply_subst subst' (BabTy_Meta n))"
    using 17(2) types_equal_symmetric by (simp del: types_equal.simps)
  ultimately show ?case using unifier_factors_singleton types_equal_symmetric by blast
next
  (* Cases 18-21: Base type matching *)
  case 18 then show ?case by (simp add: types_equal_reflexive del: types_equal.simps)
next
  case 19 then show ?case by (auto simp: types_equal_reflexive split: if_splits simp del: types_equal.simps)
next
  case 20 then show ?case by (simp add: types_equal_reflexive del: types_equal.simps)
next
  case 21 then show ?case by (simp add: types_equal_reflexive del: types_equal.simps)
next
  (* Case 22: Name/Name *)
  case (22 loc1 n1 args1 loc2 n2 args2)
  show ?case
  proof (cases "n1 = n2 \<and> length args1 = length args2")
    case True
    with 22(2) have unify_args: "unify_list args1 args2 = Some subst" by simp
    from 22(3) have "list_all (\<lambda>(t1, t2). types_equal (apply_subst subst' t1) (apply_subst subst' t2)) (zip args1 args2)"
      by (simp add: types_equal_Name list_all_length del: types_equal.simps)
    from 22(1)[OF True unify_args this] show ?thesis .
  next
    case False then show ?thesis using 22(2) by auto
  qed
next
  (* Case 23: Tuple/Tuple *)
  case (23 loc1 tys1 loc2 tys2)
  show ?case
  proof (cases "length tys1 = length tys2")
    case True
    with 23(2) have unify_tys: "unify_list tys1 tys2 = Some subst" by simp
    from 23(3) have "list_all (\<lambda>(t1, t2). types_equal (apply_subst subst' t1) (apply_subst subst' t2)) (zip tys1 tys2)"
      by (simp add: types_equal_Tuple list_all_length del: types_equal.simps)
    from 23(1)[OF True unify_tys this] show ?thesis .
  next
    case False then show ?thesis using 23(2) by simp
  qed
next
  (* Case 24: Record/Record *)
  case (24 loc1 flds1 loc2 flds2)
  show ?case
  proof (cases "length flds1 = length flds2 \<and> map fst flds1 = map fst flds2")
    case True
    with 24(2) have unify_flds: "unify_list (map snd flds1) (map snd flds2) = Some subst" by simp
    (* Extract the types_equal assumption about applied records *)
    let ?flds1' = "map (\<lambda>(name, ty). (name, apply_subst subst' ty)) flds1"
    let ?flds2' = "map (\<lambda>(name, ty). (name, apply_subst subst' ty)) flds2"
    from 24(3) have rec_eq: "types_equal (BabTy_Record loc1 ?flds1') (BabTy_Record loc2 ?flds2')" by simp
    hence flds_eq: "list_all (\<lambda>(f1, f2). fst f1 = fst f2 \<and> types_equal (snd f1) (snd f2)) (zip ?flds1' ?flds2')"
      by (simp add: types_equal_Record del: types_equal.simps)
    (* Convert to the form expected by IH *)
    from True have len_eq: "length flds1 = length flds2" by simp
    have "list_all (\<lambda>(t1, t2). types_equal (apply_subst subst' t1) (apply_subst subst' t2)) (zip (map snd flds1) (map snd flds2))"
    proof (simp del: types_equal.simps add: list_all_length)
      show "\<forall>n. n < length flds1 \<and> n < length flds2 \<longrightarrow>
              types_equal (apply_subst subst' (snd (flds1 ! n))) (apply_subst subst' (snd (flds2 ! n)))"
      proof (intro allI impI)
        fix n
        assume n_bound: "n < length flds1 \<and> n < length flds2"
        hence n_bound1: "n < length flds1" and n_bound2: "n < length flds2" by simp_all
        from flds_eq n_bound1 len_eq have eq1: "types_equal (snd (?flds1' ! n)) (snd (?flds2' ! n))"
          by (simp add: list_all_length)
        have "snd (?flds1' ! n) = apply_subst subst' (snd (flds1 ! n))"
          using n_bound1 by (simp add: case_prod_beta)
        moreover have "snd (?flds2' ! n) = apply_subst subst' (snd (flds2 ! n))"
          using n_bound2 by (simp add: case_prod_beta)
        ultimately show "types_equal (apply_subst subst' (snd (flds1 ! n))) (apply_subst subst' (snd (flds2 ! n)))"
          using eq1 by simp
      qed
    qed
    from 24(1)[OF True unify_flds this] show ?thesis .
  next
    case False then show ?thesis using 24(2) by auto
  qed
next
  (* Case 25: Array/Array *)
  case (25 loc1 elem1 dims1 loc2 elem2 dims2)
  show ?case
  proof (cases "dims1 = dims2")
    case True
    with 25(2) have unify_elem: "unify elem1 elem2 = Some subst" by simp
    from 25(3) have "types_equal (apply_subst subst' elem1) (apply_subst subst' elem2)" by simp
    from 25(1)[OF True unify_elem this] show ?thesis .
  next
    case False then show ?thesis using 25(2) by simp
  qed
next
  (* Case 82: unify_list base case *)
  case 82
  then show ?case by (simp add: types_equal_reflexive del: types_equal.simps)
next
  (* Case 83: unify_list Cons/Cons *)
  case (83 ty1 rest1 ty2 rest2)
  from 83(3) obtain subst1 subst2 where
    unify_head: "unify ty1 ty2 = Some subst1" and
    unify_rest: "unify_list (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2) = Some subst2" and
    subst_compose: "subst = compose_subst subst2 subst1"
    by (auto split: option.splits simp del: types_equal.simps)
  from 83(4) have head_unifies: "types_equal (apply_subst subst' ty1) (apply_subst subst' ty2)"
    and rest_unifies: "list_all (\<lambda>(t1, t2). types_equal (apply_subst subst' t1) (apply_subst subst' t2)) (zip rest1 rest2)"
    by simp_all
  (* From the head unification, subst' factors through subst1 *)
  from 83(1)[OF unify_head head_unifies]
  have factor1: "\<And>ty. types_equal (apply_subst subst' ty) (apply_subst subst' (apply_subst subst1 ty))" .
  (* Therefore rest_unifies also holds after applying subst1 *)
  have len_eq: "length rest1 = length rest2"
    using unify_list_length[OF unify_rest] by simp
  have rest_unifies': "list_all (\<lambda>(t1, t2). types_equal (apply_subst subst' t1) (apply_subst subst' t2))
                                (zip (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2))"
  proof -
    have orig: "\<forall>i < length rest1. types_equal (apply_subst subst' (rest1 ! i)) (apply_subst subst' (rest2 ! i))"
      using rest_unifies len_eq by (simp add: list_all_length del: types_equal.simps)
    have "\<forall>i < length rest1. types_equal (apply_subst subst' (apply_subst subst1 (rest1 ! i)))
                                           (apply_subst subst' (apply_subst subst1 (rest2 ! i)))"
    proof (intro allI impI)
      fix i assume "i < length rest1"
      hence eq_i: "types_equal (apply_subst subst' (rest1 ! i)) (apply_subst subst' (rest2 ! i))"
        using orig by blast
      have "types_equal (apply_subst subst' (apply_subst subst1 (rest1 ! i)))
                        (apply_subst subst' (rest1 ! i))"
        using factor1 types_equal_symmetric by blast
      also have "types_equal (apply_subst subst' (rest1 ! i)) (apply_subst subst' (rest2 ! i))"
        using eq_i by blast
      also have "types_equal (apply_subst subst' (rest2 ! i))
                             (apply_subst subst' (apply_subst subst1 (rest2 ! i)))"
        using factor1 by blast
      finally show "types_equal (apply_subst subst' (apply_subst subst1 (rest1 ! i)))
                                (apply_subst subst' (apply_subst subst1 (rest2 ! i)))" .
    qed
    thus ?thesis by (simp add: list_all_length del: types_equal.simps)
  qed
  (* From the rest unification, subst' factors through subst2 as well *)
  from 83(2)[OF unify_head unify_rest rest_unifies']
  have factor2: "\<And>ty. types_equal (apply_subst subst' ty) (apply_subst subst' (apply_subst subst2 ty))" .
  (* Combine: subst' factors through compose_subst subst2 subst1 *)
  have "types_equal (apply_subst subst' ty) (apply_subst subst' (apply_subst subst1 ty))"
    using factor1 by blast
  also have "types_equal ... (apply_subst subst' (apply_subst subst2 (apply_subst subst1 ty)))"
    using factor2 by blast
  also have "apply_subst subst' (apply_subst subst2 (apply_subst subst1 ty)) =
             apply_subst subst' (apply_subst (compose_subst subst2 subst1) ty)"
    by (simp add: compose_subst_correct)
  finally show ?case using subst_compose by simp
qed (simp_all)

(* Standard form of MGU theorem: any unifier factors through the MGU *)
theorem unify_mgu_standard:
  assumes "unify ty1 ty2 = Some \<sigma>"
      and "types_equal (apply_subst \<sigma>' ty1) (apply_subst \<sigma>' ty2)"
    shows "\<exists>\<tau>. subst_equal \<sigma>' (compose_subst \<tau> \<sigma>)"
proof -
  have "\<And>ty. types_equal (apply_subst \<sigma>' ty) (apply_subst \<sigma>' (apply_subst \<sigma> ty))"
    using unify_mgu[OF assms] .
  hence "\<And>ty. types_equal (apply_subst \<sigma>' ty) (apply_subst (compose_subst \<sigma>' \<sigma>) ty)"
    by (simp add: compose_subst_correct)
  hence "subst_equal \<sigma>' (compose_subst \<sigma>' \<sigma>)"
    by (simp add: subst_equal_def)
  thus ?thesis by blast
qed


(* ========================================================================== *)
(* Completeness of unification                                                  *)
(* ========================================================================== *)

(* Helper: if n occurs in ty, then apply_subst \<sigma> ty contains apply_subst \<sigma> (BabTy_Meta n)
   as a subterm, making the size of the former strictly larger (when ty \<noteq> BabTy_Meta n) *)
lemma occurs_implies_larger_size:
  assumes "occurs n ty"
      and "ty \<noteq> BabTy_Meta n"
    shows "bab_type_size (apply_subst \<sigma> (BabTy_Meta n)) < bab_type_size (apply_subst \<sigma> ty)"
  using assms
proof (induction ty rule: measure_induct_rule[where f=bab_type_size])
  case (less ty)
  show ?case
  proof (cases ty)
    case (BabTy_Meta m)
    (* ty = BabTy_Meta m, and n occurs in it, so n = m, but ty \<noteq> BabTy_Meta n - contradiction *)
    from less.prems BabTy_Meta have "n = m" by (simp add: occurs_def)
    hence "ty = BabTy_Meta n" using BabTy_Meta by simp
    with less.prems show ?thesis by simp
  next
    case (BabTy_Name loc name tyargs)
    from less.prems BabTy_Name have "n \<in> type_metavars (BabTy_Name loc name tyargs)"
      by (simp add: occurs_def)
    hence "\<exists>arg \<in> set tyargs. n \<in> type_metavars arg" by auto
    then obtain arg where "arg \<in> set tyargs" and "n \<in> type_metavars arg" by auto
    hence "occurs n arg" by (simp add: occurs_def)
    show ?thesis
    proof (cases "arg = BabTy_Meta n")
      case True
      (* arg = BabTy_Meta n, so apply_subst \<sigma> arg = apply_subst \<sigma> (BabTy_Meta n) *)
      have "bab_type_size (apply_subst \<sigma> arg) \<le> sum_list (map (bab_type_size \<circ> apply_subst \<sigma>) tyargs)"
        using \<open>arg \<in> set tyargs\<close> by (simp add: member_le_sum_list)
      hence "bab_type_size (apply_subst \<sigma> (BabTy_Meta n)) < 1 + sum_list (map (bab_type_size \<circ> apply_subst \<sigma>) tyargs)"
        using True by simp
      thus ?thesis using BabTy_Name by simp
    next
      case False
      have "bab_type_size arg < bab_type_size ty"
        using BabTy_Name \<open>arg \<in> set tyargs\<close> bab_type_smaller_than_list by fastforce
      from less.IH[OF this \<open>occurs n arg\<close> False]
      have "bab_type_size (apply_subst \<sigma> (BabTy_Meta n)) < bab_type_size (apply_subst \<sigma> arg)" .
      also have "bab_type_size (apply_subst \<sigma> arg) \<le> sum_list (map (bab_type_size \<circ> apply_subst \<sigma>) tyargs)"
        using \<open>arg \<in> set tyargs\<close> by (simp add: member_le_sum_list)
      also have "... < 1 + sum_list (map (bab_type_size \<circ> apply_subst \<sigma>) tyargs)" by simp
      finally show ?thesis using BabTy_Name by simp
    qed
  next
    case (BabTy_Bool loc)
    from less.prems BabTy_Bool show ?thesis by (simp add: occurs_def)
  next
    case (BabTy_FiniteInt loc s b)
    from less.prems BabTy_FiniteInt show ?thesis by (simp add: occurs_def)
  next
    case (BabTy_MathInt loc)
    from less.prems BabTy_MathInt show ?thesis by (simp add: occurs_def)
  next
    case (BabTy_MathReal loc)
    from less.prems BabTy_MathReal show ?thesis by (simp add: occurs_def)
  next
    case (BabTy_Tuple loc tys)
    from less.prems BabTy_Tuple have "n \<in> type_metavars (BabTy_Tuple loc tys)"
      by (simp add: occurs_def)
    hence "\<exists>t \<in> set tys. n \<in> type_metavars t" by auto
    then obtain t where "t \<in> set tys" and "n \<in> type_metavars t" by auto
    hence "occurs n t" by (simp add: occurs_def)
    show ?thesis
    proof (cases "t = BabTy_Meta n")
      case True
      have "bab_type_size (apply_subst \<sigma> t) \<le> sum_list (map (bab_type_size \<circ> apply_subst \<sigma>) tys)"
        using \<open>t \<in> set tys\<close> by (simp add: member_le_sum_list)
      hence "bab_type_size (apply_subst \<sigma> (BabTy_Meta n)) < 1 + sum_list (map (bab_type_size \<circ> apply_subst \<sigma>) tys)"
        using True by simp
      thus ?thesis using BabTy_Tuple by simp
    next
      case False
      have "bab_type_size t < bab_type_size ty"
        using BabTy_Tuple \<open>t \<in> set tys\<close> bab_type_smaller_than_list by fastforce
      from less.IH[OF this \<open>occurs n t\<close> False]
      have "bab_type_size (apply_subst \<sigma> (BabTy_Meta n)) < bab_type_size (apply_subst \<sigma> t)" .
      also have "bab_type_size (apply_subst \<sigma> t) \<le> sum_list (map (bab_type_size \<circ> apply_subst \<sigma>) tys)"
        using \<open>t \<in> set tys\<close> by (simp add: member_le_sum_list)
      also have "... < 1 + sum_list (map (bab_type_size \<circ> apply_subst \<sigma>) tys)" by simp
      finally show ?thesis using BabTy_Tuple by simp
    qed
  next
    case (BabTy_Record loc flds)
    from less.prems BabTy_Record have "n \<in> type_metavars (BabTy_Record loc flds)"
      by (simp add: occurs_def)
    hence "\<exists>f \<in> set flds. n \<in> type_metavars (snd f)" by auto
    then obtain f where "f \<in> set flds" and "n \<in> type_metavars (snd f)" by auto
    hence "occurs n (snd f)" by (simp add: occurs_def)
    show ?thesis
    proof (cases "snd f = BabTy_Meta n")
      case True
      have "bab_type_size (apply_subst \<sigma> (snd f)) \<le> sum_list (map (bab_type_size \<circ> apply_subst \<sigma> \<circ> snd) flds)"
        using \<open>f \<in> set flds\<close> by (auto intro: member_le_sum_list)
      hence "bab_type_size (apply_subst \<sigma> (BabTy_Meta n)) < 1 + sum_list (map (bab_type_size \<circ> apply_subst \<sigma> \<circ> snd) flds)"
        using True by simp
      moreover have "sum_list (map (bab_type_size \<circ> apply_subst \<sigma> \<circ> snd) flds) =
                     sum_list (map (bab_type_size \<circ> snd) (map (\<lambda>(name, ty). (name, apply_subst \<sigma> ty)) flds))"
        by (simp add: case_prod_beta comp_def)
      ultimately show ?thesis using BabTy_Record by simp
    next
      case False
      have "snd f \<in> snd ` set flds" using \<open>f \<in> set flds\<close> by force
      have "bab_type_size (snd f) < bab_type_size ty"
        using BabTy_Record \<open>f \<in> set flds\<close> bab_type_smaller_than_fieldlist[of "fst f" "snd f" flds]
        by simp
      from less.IH[OF this \<open>occurs n (snd f)\<close> False]
      have "bab_type_size (apply_subst \<sigma> (BabTy_Meta n)) < bab_type_size (apply_subst \<sigma> (snd f))" .
      also have "bab_type_size (apply_subst \<sigma> (snd f)) \<le> sum_list (map (bab_type_size \<circ> apply_subst \<sigma> \<circ> snd) flds)"
        using \<open>f \<in> set flds\<close> by (auto intro: member_le_sum_list)
      also have "... < 1 + sum_list (map (bab_type_size \<circ> apply_subst \<sigma> \<circ> snd) flds)" by simp
      finally have "bab_type_size (apply_subst \<sigma> (BabTy_Meta n)) < 1 + sum_list (map (bab_type_size \<circ> apply_subst \<sigma> \<circ> snd) flds)" .
      moreover have "sum_list (map (bab_type_size \<circ> apply_subst \<sigma> \<circ> snd) flds) =
                     sum_list (map (bab_type_size \<circ> snd) (map (\<lambda>(name, ty). (name, apply_subst \<sigma> ty)) flds))"
        by (simp add: case_prod_beta comp_def)
      ultimately show ?thesis using BabTy_Record by simp
    qed
  next
    case (BabTy_Array loc elem dims)
    from less.prems BabTy_Array have "n \<in> type_metavars elem" by (simp add: occurs_def)
    hence "occurs n elem" by (simp add: occurs_def)
    show ?thesis
    proof (cases "elem = BabTy_Meta n")
      case True
      have "bab_type_size (apply_subst \<sigma> elem) < 1 + bab_type_size (apply_subst \<sigma> elem) + sum_list (map bab_dimension_size dims)"
        by simp
      thus ?thesis using True BabTy_Array by simp
    next
      case False
      have "bab_type_size elem < bab_type_size ty"
        using BabTy_Array by simp
      from less.IH[OF this \<open>occurs n elem\<close> False]
      have "bab_type_size (apply_subst \<sigma> (BabTy_Meta n)) < bab_type_size (apply_subst \<sigma> elem)" .
      also have "... < 1 + bab_type_size (apply_subst \<sigma> elem) + sum_list (map bab_dimension_size dims)"
        by simp
      finally show ?thesis using BabTy_Array by simp
    qed
  qed
qed

(* The occurs check prevents infinite types: if metavariable n occurs in ty
   (and ty is not just BabTy_Meta n), then no substitution can make
   BabTy_Meta n equal to ty. This is because applying any substitution
   would result in an infinite expansion. *)
lemma occurs_check_no_unifier:
  assumes "occurs n ty"
      and "ty \<noteq> BabTy_Meta n"
    shows "\<not> types_equal (apply_subst \<sigma> (BabTy_Meta n)) (apply_subst \<sigma> ty)"
proof
  assume "types_equal (apply_subst \<sigma> (BabTy_Meta n)) (apply_subst \<sigma> ty)"
  hence "bab_type_size (apply_subst \<sigma> (BabTy_Meta n)) = bab_type_size (apply_subst \<sigma> ty)"
    by (rule types_equal_same_size)
  moreover from occurs_implies_larger_size[OF assms]
  have "bab_type_size (apply_subst \<sigma> (BabTy_Meta n)) < bab_type_size (apply_subst \<sigma> ty)" .
  ultimately show False by simp
qed

(* Completeness of unification: if a unifier exists, then unify will find one. *)
theorem unify_complete:
  "types_equal (apply_subst \<sigma> ty1) (apply_subst \<sigma> ty2) \<Longrightarrow>
   \<exists>\<theta>. unify ty1 ty2 = Some \<theta>"
  and unify_list_complete:
  "list_all (\<lambda>(t1, t2). types_equal (apply_subst \<sigma> t1) (apply_subst \<sigma> t2)) (zip tys1 tys2) \<Longrightarrow>
   length tys1 = length tys2 \<Longrightarrow>
   \<exists>\<theta>. unify_list tys1 tys2 = Some \<theta>"
proof (induction ty1 ty2 and tys1 tys2 arbitrary: \<sigma> and \<sigma> rule: unify_unify_list.induct)
  (* Case 1: Meta/Meta *)
  case (1 n m)
  then show ?case by auto
next
  (* Case 2: Meta/Name - check occurs *)
  case (2 n loc name tyargs)
  show ?case
  proof (cases "occurs n (BabTy_Name loc name tyargs)")
    case True
    from occurs_check_no_unifier[OF True] "2.prems"
    show ?thesis by simp
  next
    case False
    then show ?thesis by auto
  qed
next
  (* Case 3: Meta/Bool *)
  case (3 n loc)
  then show ?case by (auto simp: occurs_def)
next
  (* Case 4: Meta/FiniteInt *)
  case (4 n loc s b)
  then show ?case by (auto simp: occurs_def)
next
  (* Case 5: Meta/MathInt *)
  case (5 n loc)
  then show ?case by (auto simp: occurs_def)
next
  (* Case 6: Meta/MathReal *)
  case (6 n loc)
  then show ?case by (auto simp: occurs_def)
next
  (* Case 7: Meta/Tuple - check occurs *)
  case (7 n loc tys)
  show ?case
  proof (cases "occurs n (BabTy_Tuple loc tys)")
    case True
    from occurs_check_no_unifier[OF True] "7.prems"
    show ?thesis by simp
  next
    case False
    then show ?thesis by auto
  qed
next
  (* Case 8: Meta/Record - check occurs *)
  case (8 n loc flds)
  show ?case
  proof (cases "occurs n (BabTy_Record loc flds)")
    case True
    from occurs_check_no_unifier[OF True] "8.prems"
    show ?thesis by simp
  next
    case False
    then show ?thesis by auto
  qed
next
  (* Case 9: Meta/Array - check occurs *)
  case (9 n loc elem dims)
  show ?case
  proof (cases "occurs n (BabTy_Array loc elem dims)")
    case True
    from occurs_check_no_unifier[OF True] "9.prems"
    show ?thesis by simp
  next
    case False
    then show ?thesis by auto
  qed
next
  (* Case 10: Name/Meta - check occurs *)
  case (10 loc name tyargs n)
  show ?case
  proof (cases "occurs n (BabTy_Name loc name tyargs)")
    case True
    from occurs_check_no_unifier[OF True] "10.prems"
    show ?thesis using types_equal_symmetric by (simp del: types_equal.simps)
  next
    case False
    then show ?thesis by auto
  qed
next
  (* Case 11: Bool/Meta *)
  case (11 loc n)
  then show ?case by (auto simp: occurs_def)
next
  (* Case 12: FiniteInt/Meta *)
  case (12 loc s b n)
  then show ?case by (auto simp: occurs_def)
next
  (* Case 13: MathInt/Meta *)
  case (13 loc n)
  then show ?case by (auto simp: occurs_def)
next
  (* Case 14: MathReal/Meta *)
  case (14 loc n)
  then show ?case by (auto simp: occurs_def)
next
  (* Case 15: Tuple/Meta - check occurs *)
  case (15 loc tys n)
  show ?case
  proof (cases "occurs n (BabTy_Tuple loc tys)")
    case True
    from occurs_check_no_unifier[OF True] "15.prems"
    show ?thesis using types_equal_symmetric by (simp del: types_equal.simps)
  next
    case False
    then show ?thesis by auto
  qed
next
  (* Case 16: Record/Meta - check occurs *)
  case (16 loc flds n)
  show ?case
  proof (cases "occurs n (BabTy_Record loc flds)")
    case True
    from occurs_check_no_unifier[OF True] "16.prems"
    show ?thesis using types_equal_symmetric by (simp del: types_equal.simps)
  next
    case False
    then show ?thesis by auto
  qed
next
  (* Case 17: Array/Meta - check occurs *)
  case (17 loc elem dims n)
  show ?case
  proof (cases "occurs n (BabTy_Array loc elem dims)")
    case True
    from occurs_check_no_unifier[OF True] "17.prems"
    show ?thesis using types_equal_symmetric by (simp del: types_equal.simps)
  next
    case False
    then show ?thesis by auto
  qed
next
  (* Case 18: Bool/Bool *)
  case (18 loc1 loc2)
  then show ?case by auto
next
  (* Case 19: FiniteInt/FiniteInt *)
  case (19 loc1 s1 b1 loc2 s2 b2)
  from "19.prems" have "s1 = s2" "b1 = b2" by simp_all
  then show ?case by auto
next
  (* Case 20: MathInt/MathInt *)
  case (20 loc1 loc2)
  then show ?case by auto
next
  (* Case 21: MathReal/MathReal *)
  case (21 loc1 loc2)
  then show ?case by auto
next
  (* Case 22: Name/Name - unify type arguments *)
  case (22 loc1 name1 tyargs1 loc2 name2 tyargs2)
  from "22.prems" have cond: "name1 = name2 \<and> length tyargs1 = length tyargs2"
    by (simp add: types_equal_Name)
  from "22.prems" cond have "list_all (\<lambda>(t1, t2). types_equal (apply_subst \<sigma> t1) (apply_subst \<sigma> t2)) (zip tyargs1 tyargs2)"
    by (simp add: types_equal_Name list_all_length del: types_equal.simps)
  from "22.IH"[OF cond this] cond obtain \<theta> where "unify_list tyargs1 tyargs2 = Some \<theta>" by auto
  with cond show ?case by auto
next
  (* Case 23: Tuple/Tuple - unify element types *)
  case (23 loc1 tys1 loc2 tys2)
  from "23.prems" have len_eq: "length tys1 = length tys2"
    by (simp add: types_equal_Tuple)
  from "23.prems" len_eq have "list_all (\<lambda>(t1, t2). types_equal (apply_subst \<sigma> t1) (apply_subst \<sigma> t2)) (zip tys1 tys2)"
    by (simp add: types_equal_Tuple list_all_length del: types_equal.simps)
  from "23.IH"[OF len_eq this] len_eq obtain \<theta> where "unify_list tys1 tys2 = Some \<theta>" by auto
  with len_eq show ?case by auto
next
  (* Case 24: Record/Record - unify field types *)
  case (24 loc1 flds1 loc2 flds2)
  (* Extract the types_equal assumption about applied records *)
  let ?flds1' = "map (\<lambda>(name, ty). (name, apply_subst \<sigma> ty)) flds1"
  let ?flds2' = "map (\<lambda>(name, ty). (name, apply_subst \<sigma> ty)) flds2"
  from "24.prems" have rec_eq: "types_equal (BabTy_Record loc1 ?flds1') (BabTy_Record loc2 ?flds2')" by simp
  hence len_eq: "length ?flds1' = length ?flds2'"
    and flds_eq: "list_all (\<lambda>(f1, f2). fst f1 = fst f2 \<and> types_equal (snd f1) (snd f2)) (zip ?flds1' ?flds2')"
    by (simp_all add: types_equal_Record del: types_equal.simps)
  from len_eq have len_eq_orig: "length flds1 = length flds2" by simp
  have names_eq: "map fst flds1 = map fst flds2"
  proof -
    have "map fst ?flds1' = map fst flds1" by (simp add: case_prod_beta)
    moreover have "map fst ?flds2' = map fst flds2" by (simp add: case_prod_beta)
    moreover have "map fst ?flds1' = map fst ?flds2'"
      using flds_eq len_eq by (simp add: list_all_length list_eq_iff_nth_eq)
    ultimately show ?thesis by metis
  qed
  have cond: "length flds1 = length flds2 \<and> map fst flds1 = map fst flds2"
    using len_eq_orig names_eq by simp
  (* Convert flds_eq to the form expected by IH *)
  have types_eq: "list_all (\<lambda>(t1, t2). types_equal (apply_subst \<sigma> t1) (apply_subst \<sigma> t2)) (zip (map snd flds1) (map snd flds2))"
  proof (simp del: types_equal.simps add: list_all_length)
    show "\<forall>n. n < length flds1 \<and> n < length flds2 \<longrightarrow>
            types_equal (apply_subst \<sigma> (snd (flds1 ! n))) (apply_subst \<sigma> (snd (flds2 ! n)))"
    proof (intro allI impI)
      fix n
      assume n_bound: "n < length flds1 \<and> n < length flds2"
      hence n_bound1: "n < length flds1" and n_bound2: "n < length flds2" by simp_all
      from flds_eq n_bound1 len_eq have eq1: "types_equal (snd (?flds1' ! n)) (snd (?flds2' ! n))"
        by (simp add: list_all_length)
      have "snd (?flds1' ! n) = apply_subst \<sigma> (snd (flds1 ! n))"
        using n_bound1 by (simp add: case_prod_beta)
      moreover have "snd (?flds2' ! n) = apply_subst \<sigma> (snd (flds2 ! n))"
        using n_bound2 by (simp add: case_prod_beta)
      ultimately show "types_equal (apply_subst \<sigma> (snd (flds1 ! n))) (apply_subst \<sigma> (snd (flds2 ! n)))"
        using eq1 by simp
    qed
  qed
  from len_eq_orig have "length (map snd flds1) = length (map snd flds2)" by simp
  with types_eq obtain \<theta> where "unify_list (map snd flds1) (map snd flds2) = Some \<theta>"
    using "24.IH"[OF cond] by auto
  with cond show ?case by auto
next
  (* Case 25: Array/Array - unify element types *)
  case (25 loc1 elem1 dims1 loc2 elem2 dims2)
  from "25.prems" have dims_eq: "dims1 = dims2" by simp
  from "25.prems" have "types_equal (apply_subst \<sigma> elem1) (apply_subst \<sigma> elem2)" by simp
  from "25.IH"[OF dims_eq this] obtain \<theta> where "unify elem1 elem2 = Some \<theta>" by auto
  with dims_eq show ?case by auto
next
  (* Case 82: unify_list [] [] *)
  case 82
  then show ?case by simp
next
  (* Case 83: unify_list (ty1 # tys1) (ty2 # tys2) - the key case *)
  case (83 ty1 tys1 ty2 tys2)
  (* Extract hypotheses *)
  from "83.prems" have head_unifies: "types_equal (apply_subst \<sigma> ty1) (apply_subst \<sigma> ty2)"
    and rest_unifies: "list_all (\<lambda>(t1, t2). types_equal (apply_subst \<sigma> t1) (apply_subst \<sigma> t2)) (zip tys1 tys2)"
    and len_eq: "length tys1 = length tys2"
    by simp_all
  (* Use IH to unify heads *)
  from "83.IH"(1)[OF head_unifies] obtain \<theta>1 where unify_head: "unify ty1 ty2 = Some \<theta>1" by auto
  (* The MGU property tells us that \<sigma> factors through \<theta>1 *)
  from unify_mgu[OF unify_head head_unifies]
  have mgu: "\<And>ty. types_equal (apply_subst \<sigma> ty) (apply_subst \<sigma> (apply_subst \<theta>1 ty))" .
  (* Therefore the rest still unifies after applying \<theta>1 *)
  have rest_unifies': "list_all (\<lambda>(t1, t2). types_equal (apply_subst \<sigma> t1) (apply_subst \<sigma> t2))
                                (zip (map (apply_subst \<theta>1) tys1) (map (apply_subst \<theta>1) tys2))"
  proof -
    have "\<forall>i < length tys1. types_equal (apply_subst \<sigma> (apply_subst \<theta>1 (tys1 ! i)))
                                          (apply_subst \<sigma> (apply_subst \<theta>1 (tys2 ! i)))"
    proof (intro allI impI)
      fix i assume "i < length tys1"
      hence orig: "types_equal (apply_subst \<sigma> (tys1 ! i)) (apply_subst \<sigma> (tys2 ! i))"
        using rest_unifies len_eq by (simp add: list_all_length del: types_equal.simps)
      have "types_equal (apply_subst \<sigma> (apply_subst \<theta>1 (tys1 ! i)))
                        (apply_subst \<sigma> (tys1 ! i))"
        using mgu types_equal_symmetric by blast
      also have "types_equal ... (apply_subst \<sigma> (tys2 ! i))" using orig .
      also have "types_equal ... (apply_subst \<sigma> (apply_subst \<theta>1 (tys2 ! i)))"
        using mgu by blast
      finally show "types_equal (apply_subst \<sigma> (apply_subst \<theta>1 (tys1 ! i)))
                                (apply_subst \<sigma> (apply_subst \<theta>1 (tys2 ! i)))" .
    qed
    thus ?thesis by (simp add: list_all_length del: types_equal.simps)
  qed
  have len_eq': "length (map (apply_subst \<theta>1) tys1) = length (map (apply_subst \<theta>1) tys2)"
    using len_eq by simp
  (* Use IH for unify_list on the substituted lists - this is the key! *)
  from "83.IH"(2)[OF unify_head rest_unifies' len_eq']
  obtain \<theta>2 where unify_rest: "unify_list (map (apply_subst \<theta>1) tys1) (map (apply_subst \<theta>1) tys2) = Some \<theta>2"
    by auto
  (* Combine results *)
  have "unify_list (ty1 # tys1) (ty2 # tys2) = Some (compose_subst \<theta>2 \<theta>1)"
    using unify_head unify_rest by simp
  then show ?case by blast
qed (simp_all)


end
