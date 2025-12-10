theory Unify2
  imports Unify
begin

(* Correctness properties for our unification algorithm *)


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

(* If unify succeeds, the substitution makes the types equal. *)

theorem unify_sound:
  "unify ty1 ty2 = Some subst \<Longrightarrow>
     apply_subst subst ty1 = apply_subst subst ty2"
and unify_list_sound:
  "unify_list tys1 tys2 = Some subst \<Longrightarrow>
      list_all (\<lambda>(t1, t2). apply_subst subst t1 = apply_subst subst t2) (zip tys1 tys2)"
proof (induction ty1 ty2 and tys1 tys2 arbitrary: subst and subst rule: unify_unify_list.induct)
  (* CoreTy_Name / ty2 *)
  case (1 name1 tyArgs1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    (* unify returns singleton_subst n (CoreTy_Name name1 tyArgs1) when occurs check passes *)
    from 1 CoreTy_Meta have no_occurs: "\<not> occurs n (CoreTy_Name name1 tyArgs1)"
      by (auto split: if_splits)
    from 1 CoreTy_Meta no_occurs have subst_eq: "subst = singleton_subst n (CoreTy_Name name1 tyArgs1)"
      by simp
    have "apply_subst subst (CoreTy_Name name1 tyArgs1) = CoreTy_Name name1 tyArgs1"
      using no_occurs subst_eq
      using apply_subst_singleton_no_occurs by blast
    also have "... = apply_subst subst (CoreTy_Meta n)"
      using subst_eq apply_subst_singleton by auto
    finally show ?thesis using CoreTy_Meta by simp
  next
    case (CoreTy_Name name2 tyArgs2)
    show ?thesis
    proof (cases "name1 = name2")
      case True
      with 1 CoreTy_Name have "unify_list tyArgs1 tyArgs2 = Some subst" by simp
      with 1 True CoreTy_Name have "list_all (\<lambda>(t1, t2). apply_subst subst t1 = apply_subst subst t2)
                                  (zip tyArgs1 tyArgs2)" by simp
      then have "map (apply_subst subst) tyArgs1 = map (apply_subst subst) tyArgs2"
        using unify_list_length[of tyArgs1 tyArgs2 subst] \<open>unify_list tyArgs1 tyArgs2 = Some subst\<close>
        by (simp add: list_all_length list_eq_iff_nth_eq)
      then show ?thesis using True CoreTy_Name by simp
    next
      case False
      then show ?thesis using 1 CoreTy_Name by simp
    qed
  qed auto
next
  (* CoreTy_Bool / ty2 *)
  case (2 ty2)
  then show ?case by (cases ty2; auto simp: apply_subst_singleton singleton_subst_def)
next
  (* CoreTy_FiniteInt / ty2 *)
  case (3 sign bits ty2)
  then show ?case by (cases ty2; auto simp: apply_subst_singleton singleton_subst_def split: if_splits)
next
  (* CoreTy_MathInt / ty2 *)
  case (4 ty2)
  then show ?case by (cases ty2; auto simp: apply_subst_singleton singleton_subst_def)
next
  (* CoreTy_MathReal / ty2 *)
  case (5 ty2)
  then show ?case by (cases ty2; auto simp: apply_subst_singleton singleton_subst_def)
next
  (* CoreTy_Record / ty2 *)
  case (6 flds1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    from 6 CoreTy_Meta have no_occurs: "\<not> occurs n (CoreTy_Record flds1)"
      by (auto split: if_splits)
    from 6 CoreTy_Meta no_occurs have subst_eq: "subst = singleton_subst n (CoreTy_Record flds1)"
      by simp
    have "apply_subst subst (CoreTy_Record flds1) = CoreTy_Record flds1"
      using no_occurs subst_eq apply_subst_singleton_no_occurs by blast
    also have "... = apply_subst subst (CoreTy_Meta n)"
      using apply_subst_singleton subst_eq by auto
    finally show ?thesis using CoreTy_Meta by simp
  next
    case (CoreTy_Record flds2)
    (* Field names must match for unification to succeed *)
    from 6 CoreTy_Record have names_eq: "map fst flds1 = map fst flds2"
      by (auto split: if_splits)
    from 6 CoreTy_Record names_eq have "unify_list (map snd flds1) (map snd flds2) = Some subst"
      by simp
    with 6 CoreTy_Record names_eq
    have "list_all (\<lambda>(t1, t2). apply_subst subst t1 = apply_subst subst t2)
                   (zip (map snd flds1) (map snd flds2))" by simp
    then have types_eq: "map (apply_subst subst) (map snd flds1) = map (apply_subst subst) (map snd flds2)"
      using unify_list_length[of "map snd flds1" "map snd flds2" subst]
            \<open>unify_list (map snd flds1) (map snd flds2) = Some subst\<close>
      by (simp add: list_all_length list_eq_iff_nth_eq)
    (* Now show that applying subst to both records gives equal results *)
    have "apply_subst subst (CoreTy_Record flds1) =
          CoreTy_Record (map (\<lambda>(name, ty). (name, apply_subst subst ty)) flds1)"
      by simp
    also have "... = CoreTy_Record (zip (map fst flds1) (map (apply_subst subst) (map snd flds1)))"
      by (metis zip_map2 zip_map_fst_snd)
    also have "... = CoreTy_Record (zip (map fst flds2) (map (apply_subst subst) (map snd flds2)))"
      using names_eq types_eq by simp
    also have "... = CoreTy_Record (map (\<lambda>(name, ty). (name, apply_subst subst ty)) flds2)"
      by (metis zip_map2 zip_map_fst_snd)
    also have "... = apply_subst subst (CoreTy_Record flds2)"
      by simp
    finally show ?thesis using CoreTy_Record by simp
  qed auto
next
  (* CoreTy_Array / ty2 *)
  case (7 elemTy1 dims1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    from 7 CoreTy_Meta have no_occurs: "\<not> occurs n (CoreTy_Array elemTy1 dims1)"
      by (auto split: if_splits)
    from 7 CoreTy_Meta no_occurs have subst_eq: "subst = singleton_subst n (CoreTy_Array elemTy1 dims1)"
      by simp
    have "apply_subst subst (CoreTy_Array elemTy1 dims1) = CoreTy_Array elemTy1 dims1"
      using apply_subst_singleton_no_occurs no_occurs subst_eq by blast
    also have "... = apply_subst subst (CoreTy_Meta n)"
      using apply_subst_singleton subst_eq by auto
    finally show ?thesis using CoreTy_Meta by simp
  next
    case (CoreTy_Array elemTy2 dims2)
    show ?thesis
    proof (cases "dims1 = dims2")
      case True
      with 7 CoreTy_Array have "unify elemTy1 elemTy2 = Some subst" by simp
      with 7 True CoreTy_Array have "apply_subst subst elemTy1 = apply_subst subst elemTy2" by simp
      then show ?thesis using True CoreTy_Array by simp
    next
      case False
      then show ?thesis using 7 CoreTy_Array by simp
    qed
  qed auto
next
  (* CoreTy_Meta / ty2 *)
  case (8 n ty2)
  then show ?case
  proof (cases "occurs n ty2 \<and> ty2 \<noteq> CoreTy_Meta n")
    case True
    then show ?thesis using 8 by simp
  next
    case False
    show ?thesis
    proof (cases "ty2 = CoreTy_Meta n")
      case True
      then show ?thesis using 8 by simp
    next
      case neq: False
      with False have no_occurs: "\<not> occurs n ty2" by simp
      from 8 False neq have subst_eq: "subst = singleton_subst n ty2" by simp
      have "apply_subst subst (CoreTy_Meta n) = ty2"
        using apply_subst_singleton subst_eq by blast
      also have "... = apply_subst subst ty2"
        by (simp add: apply_subst_singleton_no_occurs no_occurs subst_eq)
      finally show ?thesis by simp
    qed
  qed
next
  (* unify_list [] [] *)
  case 9
  then show ?case by simp
next
  (* unify_list [] (ty # tys) *)
  case (10 ty tys)
  then show ?case by simp
next
  (* unify_list (ty # tys) [] *)
  case (11 ty tys)
  then show ?case by simp
next
  (* unify_list (ty1 # tys1) (ty2 # tys2) *)
  case (12 ty1 rest1 ty2 rest2)
  from 12(3) obtain subst1 subst2 where
    unify_head: "unify ty1 ty2 = Some subst1" and
    unify_rest: "unify_list (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2) = Some subst2" and
    subst_compose: "subst = compose_subst subst2 subst1"
    by (auto split: option.splits)
  from 12(1)[OF unify_head]
  have head_eq: "apply_subst subst1 ty1 = apply_subst subst1 ty2" .
  from 12(2)[OF unify_head unify_rest]
  have "list_all (\<lambda>(t1, t2). apply_subst subst2 t1 = apply_subst subst2 t2)
                 (zip (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2))" .
  then have rest_eq: "list_all (\<lambda>(t1, t2). apply_subst subst t1 = apply_subst subst t2)
                               (zip rest1 rest2)"
    using subst_compose by (simp add: list_all_length compose_subst_correct)
  have "apply_subst subst2 (apply_subst subst1 ty1) = apply_subst subst2 (apply_subst subst1 ty2)"
    using head_eq by simp
  hence "apply_subst subst ty1 = apply_subst subst ty2"
    using subst_compose compose_subst_correct by simp
  then show ?case using rest_eq by simp
qed


(* ========================================================================== *)
(* Most General Unifier (MGU) property                                        *)
(* ========================================================================== *)

(* The MGU property states that the unifier returned by unify is "most general":
   any other unifier can be expressed by composing some substitution with the MGU.

   More precisely: if unify returns subst1, and subst2 also unifies ty1 and ty2,
   then there exists subst' such that subst2 is equivalent to subst' \<circ> subst1
   (subst2 factors through subst1).
*)

(* Helper: if subst' unifies Meta n with ty, then applying subst' to the result
   of singleton_subst n ty gives the same result as applying subst' directly *)
(* See below for main MGU theorem *)
lemma unifier_factors_singleton:
  assumes unifies: "apply_subst subst' (CoreTy_Meta n) = apply_subst subst' ty"
      and no_occurs: "\<not> occurs n ty"
    shows "\<forall>ty'. apply_subst subst' ty' = apply_subst subst' (apply_subst (singleton_subst n ty) ty')"
proof (intro allI)
  fix ty'
  show "apply_subst subst' ty' = apply_subst subst' (apply_subst (singleton_subst n ty) ty')"
  proof (induction ty')
    case (CoreTy_Meta m)
    show ?case
    proof (cases "n = m")
      case True
      then have "apply_subst (singleton_subst n ty) (CoreTy_Meta m) = ty"
        by (simp add: singleton_subst_def)
      moreover have "apply_subst subst' (CoreTy_Meta m) = apply_subst subst' ty"
        using unifies True by simp
      ultimately show ?thesis by simp
    next
      case False
      then show ?thesis by (simp add: singleton_subst_def)
    qed
  next
    case (CoreTy_Name name tyArgs)
    then show ?case by simp
  next
    case CoreTy_Bool
    then show ?case by simp
  next
    case (CoreTy_FiniteInt sign bits)
    then show ?case by simp
  next
    case CoreTy_MathInt
    then show ?case by simp
  next
    case CoreTy_MathReal
    then show ?case by simp
  next
    case (CoreTy_Record flds)
    have "\<And>nm t. (nm, t) \<in> set flds \<Longrightarrow>
          apply_subst subst' t = apply_subst subst' (apply_subst (singleton_subst n ty) t)"
      using CoreTy_Record.IH by auto
    hence "map (\<lambda>(nm, t). (nm, apply_subst subst' t)) flds =
           map (\<lambda>(nm, t). (nm, apply_subst subst' (apply_subst (singleton_subst n ty) t))) flds"
      by (induction flds) auto
    then show ?case by auto
  next
    case (CoreTy_Array elemTy dims)
    then show ?case by simp
  qed
qed

(* Main MGU theorem, proved by mutual induction *)
(* See also corollary below for a more standard "textbook" form of this *)
theorem unify_mgu:
  "unify ty1 ty2 = Some subst \<Longrightarrow>
     apply_subst subst' ty1 = apply_subst subst' ty2 \<Longrightarrow>
     apply_subst subst' ty = apply_subst subst' (apply_subst subst ty)"
  and unify_list_mgu:
  "unify_list tys1 tys2 = Some subst \<Longrightarrow>
     list_all (\<lambda>(t1, t2). apply_subst subst' t1 = apply_subst subst' t2) (zip tys1 tys2) \<Longrightarrow>
     apply_subst subst' ty = apply_subst subst' (apply_subst subst ty)"
proof (induction ty1 ty2 and tys1 tys2 arbitrary: subst subst' ty and subst subst' ty rule: unify_unify_list.induct)
  (* CoreTy_Name / ty2 *)
  case (1 name1 tyArgs1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    then have subst_eq: "subst = singleton_subst n (CoreTy_Name name1 tyArgs1)"
          and no_occurs: "\<not> occurs n (CoreTy_Name name1 tyArgs1)"
      using 1(2) by (auto split: if_splits)
    have "apply_subst subst' (CoreTy_Name name1 tyArgs1) = apply_subst subst' (CoreTy_Meta n)"
      using 1(3) CoreTy_Meta by simp
    from unifier_factors_singleton[OF this[symmetric] no_occurs] subst_eq
    show ?thesis by blast
  next
    case (CoreTy_Name name2 tyArgs2)
    show ?thesis
    proof (cases "name1 = name2")
      case True
      with 1(2) CoreTy_Name have unify_args: "unify_list tyArgs1 tyArgs2 = Some subst" by simp
      from 1(3) CoreTy_Name True have "map (apply_subst subst') tyArgs1 = map (apply_subst subst') tyArgs2"
        by simp
      hence "list_all (\<lambda>(t1, t2). apply_subst subst' t1 = apply_subst subst' t2) (zip tyArgs1 tyArgs2)"
        using unify_list_length[OF unify_args] by (simp add: list_all_length list_eq_iff_nth_eq)
      from 1(1)[OF CoreTy_Name True unify_args this] show ?thesis .
    next
      case False then show ?thesis using 1(2) CoreTy_Name by auto
    qed
  qed auto
next
  (* CoreTy_Bool / ty2 *)
  case (2 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    then have subst_eq: "subst = singleton_subst n CoreTy_Bool"
      using 2(1) by simp
    have no_occurs: "\<not> occurs n CoreTy_Bool" by (simp add: occurs_def)
    have "apply_subst subst' CoreTy_Bool = apply_subst subst' (CoreTy_Meta n)"
      using 2(2) CoreTy_Meta by simp
    from unifier_factors_singleton[OF this[symmetric] no_occurs] subst_eq
    show ?thesis by blast
  qed auto
next
  (* CoreTy_FiniteInt / ty2 *)
  case (3 sign bits ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    then have subst_eq: "subst = singleton_subst n (CoreTy_FiniteInt sign bits)"
      using 3(1) by simp
    have no_occurs: "\<not> occurs n (CoreTy_FiniteInt sign bits)" by (simp add: occurs_def)
    have "apply_subst subst' (CoreTy_FiniteInt sign bits) = apply_subst subst' (CoreTy_Meta n)"
      using 3(2) CoreTy_Meta by blast
    from unifier_factors_singleton[OF this[symmetric] no_occurs] subst_eq
    show ?thesis by blast
  qed (auto split: if_splits)
next
  (* CoreTy_MathInt / ty2 *)
  case (4 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    then have subst_eq: "subst = singleton_subst n CoreTy_MathInt"
      using 4(1) by simp
    have no_occurs: "\<not> occurs n CoreTy_MathInt" by (simp add: occurs_def)
    have "apply_subst subst' CoreTy_MathInt = apply_subst subst' (CoreTy_Meta n)"
      using 4(2) CoreTy_Meta by simp
    from unifier_factors_singleton[OF this[symmetric] no_occurs] subst_eq
    show ?thesis by blast
  qed auto
next
  (* CoreTy_MathReal / ty2 *)
  case (5 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    then have subst_eq: "subst = singleton_subst n CoreTy_MathReal"
      using 5(1) by simp
    have no_occurs: "\<not> occurs n CoreTy_MathReal" by (simp add: occurs_def)
    have "apply_subst subst' CoreTy_MathReal = apply_subst subst' (CoreTy_Meta n)"
      using 5(2) CoreTy_Meta by simp
    from unifier_factors_singleton[OF this[symmetric] no_occurs] subst_eq
    show ?thesis by blast
  qed auto
next
  (* CoreTy_Record / ty2 *)
  case (6 flds1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    then have subst_eq: "subst = singleton_subst n (CoreTy_Record flds1)"
          and no_occurs: "\<not> occurs n (CoreTy_Record flds1)"
      using 6(2) by (auto split: if_splits)
    have "apply_subst subst' (CoreTy_Record flds1) = apply_subst subst' (CoreTy_Meta n)"
      using 6(3) CoreTy_Meta by simp
    from unifier_factors_singleton[OF this[symmetric] no_occurs] subst_eq
    show ?thesis by blast
  next
    case (CoreTy_Record flds2)
    (* Field names must match for unification to succeed *)
    from 6(2) CoreTy_Record have names_eq: "map fst flds1 = map fst flds2"
      by (auto split: if_splits)
    with 6(2) CoreTy_Record have unify_tys: "unify_list (map snd flds1) (map snd flds2) = Some subst"
      by simp
    (* Extract that applying subst' to both records gives equal results *)
    from 6(3) CoreTy_Record
    have "CoreTy_Record (map (\<lambda>(n,t). (n, apply_subst subst' t)) flds1) =
          CoreTy_Record (map (\<lambda>(n,t). (n, apply_subst subst' t)) flds2)"
      by simp
    hence eq_flds: "map (\<lambda>(n,t). (n, apply_subst subst' t)) flds1 =
                    map (\<lambda>(n,t). (n, apply_subst subst' t)) flds2"
      by simp
    (* This means the types are equal *)
    have "map (apply_subst subst') (map snd flds1) = map (apply_subst subst') (map snd flds2)"
    proof -
      have "map (apply_subst subst' \<circ> snd) flds1 = map (apply_subst subst' \<circ> snd) flds2"
        using eq_flds
        by (metis (no_types, lifting) ext apsnd_conv case_prod_Pair_iden list.map_comp snd_comp_apsnd
            split_beta)
      thus ?thesis by (simp add: comp_def)
    qed
    hence "list_all (\<lambda>(t1, t2). apply_subst subst' t1 = apply_subst subst' t2)
                    (zip (map snd flds1) (map snd flds2))"
      using unify_list_length[OF unify_tys] by (simp add: list_all_length list_eq_iff_nth_eq)
    from 6(1)[OF CoreTy_Record names_eq unify_tys this] show ?thesis .
  qed auto
next
  (* CoreTy_Array / ty2 *)
  case (7 elemTy1 dims1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    then have subst_eq: "subst = singleton_subst n (CoreTy_Array elemTy1 dims1)"
          and no_occurs: "\<not> occurs n (CoreTy_Array elemTy1 dims1)"
      using 7(2) by (auto split: if_splits)
    have "apply_subst subst' (CoreTy_Array elemTy1 dims1) = apply_subst subst' (CoreTy_Meta n)"
      using 7(3) CoreTy_Meta by simp
    from unifier_factors_singleton[OF this[symmetric] no_occurs] subst_eq
    show ?thesis by blast
  next
    case (CoreTy_Array elemTy2 dims2)
    show ?thesis
    proof (cases "dims1 = dims2")
      case True
      with 7(2) CoreTy_Array have unify_elem: "unify elemTy1 elemTy2 = Some subst" by simp
      from 7(3) CoreTy_Array have "apply_subst subst' elemTy1 = apply_subst subst' elemTy2" by simp
      from 7(1)[OF CoreTy_Array True unify_elem this] show ?thesis .
    next
      case False then show ?thesis using 7(2) CoreTy_Array by simp
    qed
  qed auto
next
  (* CoreTy_Meta / ty2 *)
  case (8 n ty2)
  show ?case
  proof (cases "occurs n ty2 \<and> ty2 \<noteq> CoreTy_Meta n")
    case True then show ?thesis using 8(1) by simp
  next
    case False
    show ?thesis
    proof (cases "ty2 = CoreTy_Meta n")
      case True
      then have "subst = fmempty" using 8(1) by simp
      then show ?thesis by simp
    next
      case neq: False
      with False have no_occurs: "\<not> occurs n ty2" by simp
      have subst_eq: "subst = singleton_subst n ty2"
        using 8(1) False neq by simp
      from 8(2) have unifies': "apply_subst subst' (CoreTy_Meta n) = apply_subst subst' ty2" by simp
      show ?thesis using unifier_factors_singleton[OF unifies' no_occurs] subst_eq by blast
    qed
  qed
next
  (* unify_list [] [] *)
  case 9
  then show ?case by simp
next
  (* unify_list [] (ty # tys) - impossible *)
  case (10 ty2 tys2)
  then show ?case by simp
next
  (* unify_list (ty # tys) [] - impossible *)
  case (11 ty1 tys1)
  then show ?case by simp
next
  (* unify_list (ty1 # tys1) (ty2 # tys2) *)
  case (12 ty1 rest1 ty2 rest2)
  from 12(3) obtain subst1 subst2 where
    unify_head: "unify ty1 ty2 = Some subst1" and
    unify_rest: "unify_list (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2) = Some subst2" and
    subst_compose: "subst = compose_subst subst2 subst1"
    by (auto split: option.splits)
  from 12(4) have head_unifies: "apply_subst subst' ty1 = apply_subst subst' ty2"
    and rest_unifies: "list_all (\<lambda>(t1, t2). apply_subst subst' t1 = apply_subst subst' t2) (zip rest1 rest2)"
    by simp_all
  (* From the head unification, subst' factors through subst1 *)
  from 12(1)[OF unify_head head_unifies]
  have factor1: "\<And>ty. apply_subst subst' ty = apply_subst subst' (apply_subst subst1 ty)" .
  (* Therefore rest_unifies also holds after applying subst1 *)
  have len_eq: "length rest1 = length rest2"
    using unify_list_length[OF unify_rest] by simp
  have rest_unifies': "list_all (\<lambda>(t1, t2). apply_subst subst' t1 = apply_subst subst' t2)
                                (zip (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2))"
  proof -
    have orig: "\<forall>i < length rest1. apply_subst subst' (rest1 ! i) = apply_subst subst' (rest2 ! i)"
      using rest_unifies len_eq by (simp add: list_all_length)
    have "\<forall>i < length rest1. apply_subst subst' (apply_subst subst1 (rest1 ! i)) =
                             apply_subst subst' (apply_subst subst1 (rest2 ! i))"
    proof (intro allI impI)
      fix i assume "i < length rest1"
      hence eq_i: "apply_subst subst' (rest1 ! i) = apply_subst subst' (rest2 ! i)"
        using orig by blast
      have "apply_subst subst' (apply_subst subst1 (rest1 ! i)) = apply_subst subst' (rest1 ! i)"
        using factor1 by simp
      also have "... = apply_subst subst' (rest2 ! i)" using eq_i .
      also have "... = apply_subst subst' (apply_subst subst1 (rest2 ! i))"
        using factor1 by simp
      finally show "apply_subst subst' (apply_subst subst1 (rest1 ! i)) =
                    apply_subst subst' (apply_subst subst1 (rest2 ! i))" .
    qed
    thus ?thesis by (simp add: list_all_length)
  qed
  (* From the rest unification, subst' factors through subst2 as well *)
  from 12(2)[OF unify_head unify_rest rest_unifies']
  have factor2: "\<And>ty. apply_subst subst' ty = apply_subst subst' (apply_subst subst2 ty)" .
  (* Combine: subst' factors through compose_subst subst2 subst1 *)
  have "apply_subst subst' ty = apply_subst subst' (apply_subst subst1 ty)"
    using factor1 by blast
  also have "... = apply_subst subst' (apply_subst subst2 (apply_subst subst1 ty))"
    using factor2 by simp
  also have "... = apply_subst subst' (apply_subst (compose_subst subst2 subst1) ty)"
    by (simp add: compose_subst_correct)
  finally show ?case using subst_compose by simp
qed

(* Standard form of MGU theorem: any unifier factors through the MGU. *)
(* Note: the standard definition of MGU is: 
     \<sigma> is an MGU if:
       for all other unifiers \<tau>, there exists \<sigma>' such that \<tau> = \<sigma>' \<circ> \<sigma>
   Here we prove something stronger, namely that the unifier \<sigma> returned from "unify"
   satisfies the following:
       for all other unifiers \<tau>, we have \<tau> = \<tau> \<circ> \<sigma>
   In other words, in our case, \<tau> itself can function as \<sigma>' in the MGU definition. *)
(* Also note: when we talk about two substitutions being equal (in the above), we really
   mean they have the same effect on all types (i.e. they are equal as functions on types); 
   they do not strictly speaking need to be equal as fmaps. (For example the fmap could
   contain a redundant entry 0 \<mapsto> 0.) 
*)
theorem unify_mgu_standard:
  assumes "unify ty1 ty2 = Some \<sigma>"
      and "apply_subst \<tau> ty1 = apply_subst \<tau> ty2"
    shows "\<forall>ty. apply_subst \<tau> ty = apply_subst (compose_subst \<tau> \<sigma>) ty"
proof -
  have "\<And>ty. apply_subst \<tau> ty = apply_subst \<tau> (apply_subst \<sigma> ty)"
    using unify_mgu[OF assms] .
  thus ?thesis
    by (simp add: compose_subst_correct)
qed


(* ========================================================================== *)
(* Completeness of unification *)
(* ========================================================================== *)

(* Helper: if n occurs in ty, then apply_subst \<sigma> ty contains apply_subst \<sigma> (CoreTy_Meta n)
   as a subterm, making the size of the former strictly larger (when ty \<noteq> CoreTy_Meta n) *)
lemma occurs_implies_larger_size:
  assumes "occurs n ty"
      and "ty \<noteq> CoreTy_Meta n"
    shows "core_type_size (apply_subst \<sigma> (CoreTy_Meta n)) < core_type_size (apply_subst \<sigma> ty)"
  using assms
proof (induction ty rule: measure_induct_rule[where f=core_type_size])
  case (less ty)
  show ?case
  proof (cases ty)
    case (CoreTy_Meta m)
    (* ty = CoreTy_Meta m, and n occurs in it, so n = m, but ty \<noteq> CoreTy_Meta n - contradiction *)
    from less.prems CoreTy_Meta have "n = m" by (simp add: occurs_def)
    hence "ty = CoreTy_Meta n" using CoreTy_Meta by simp
    with less.prems show ?thesis by simp
  next
    case (CoreTy_Name name tyargs)
    from less.prems CoreTy_Name have "n \<in> type_metavars (CoreTy_Name name tyargs)"
      by (simp add: occurs_def)
    hence "\<exists>arg \<in> set tyargs. n \<in> type_metavars arg" by auto
    then obtain arg where "arg \<in> set tyargs" and "n \<in> type_metavars arg" by auto
    hence "occurs n arg" by (simp add: occurs_def)
    show ?thesis
    proof (cases "arg = CoreTy_Meta n")
      case True
      have "core_type_size (apply_subst \<sigma> arg) \<le> sum_list (map (core_type_size \<circ> apply_subst \<sigma>) tyargs)"
        using \<open>arg \<in> set tyargs\<close> by (simp add: member_le_sum_list)
      hence "core_type_size (apply_subst \<sigma> (CoreTy_Meta n)) < 1 + sum_list (map (core_type_size \<circ> apply_subst \<sigma>) tyargs)"
        using True by simp
      thus ?thesis using CoreTy_Name by simp
    next
      case False
      have "core_type_size arg \<le> sum_list (map core_type_size tyargs)"
        using \<open>arg \<in> set tyargs\<close> by (simp add: member_le_sum_list)
      hence "core_type_size arg < core_type_size ty"
        using CoreTy_Name by simp
      from less.IH[OF this \<open>occurs n arg\<close> False]
      have "core_type_size (apply_subst \<sigma> (CoreTy_Meta n)) < core_type_size (apply_subst \<sigma> arg)" .
      also have "core_type_size (apply_subst \<sigma> arg) \<le> sum_list (map (core_type_size \<circ> apply_subst \<sigma>) tyargs)"
        using \<open>arg \<in> set tyargs\<close> by (simp add: member_le_sum_list)
      also have "... < 1 + sum_list (map (core_type_size \<circ> apply_subst \<sigma>) tyargs)" by simp
      finally show ?thesis using CoreTy_Name by simp
    qed
  next
    case CoreTy_Bool
    from less.prems CoreTy_Bool show ?thesis by (simp add: occurs_def)
  next
    case (CoreTy_FiniteInt s b)
    from less.prems CoreTy_FiniteInt show ?thesis by (simp add: occurs_def)
  next
    case CoreTy_MathInt
    from less.prems CoreTy_MathInt show ?thesis by (simp add: occurs_def)
  next
    case CoreTy_MathReal
    from less.prems CoreTy_MathReal show ?thesis by (simp add: occurs_def)
  next
    case (CoreTy_Record flds)
    from less.prems CoreTy_Record have "n \<in> type_metavars (CoreTy_Record flds)"
      by (simp add: occurs_def)
    hence "\<exists>t \<in> set (map snd flds). n \<in> type_metavars t" by (auto simp: comp_def)
    then obtain t where t_in: "t \<in> set (map snd flds)" and "n \<in> type_metavars t" by auto
    hence "occurs n t" by (simp add: occurs_def)
    (* Helper: rewrite sum_list for apply_subst composition *)
    have sum_eq: "sum_list (map (core_type_size \<circ> apply_subst \<sigma>) (map snd flds)) =
                  sum_list (map (\<lambda>t. core_type_size (apply_subst \<sigma> t)) (map snd flds))"
      by (simp add: comp_def)
    show ?thesis
    proof (cases "t = CoreTy_Meta n")
      case True
      have "core_type_size (apply_subst \<sigma> t) \<le> sum_list (map (\<lambda>t. core_type_size (apply_subst \<sigma> t)) (map snd flds))"
        using canonically_ordered_monoid_add_class.member_le_sum_list t_in by force
      hence "core_type_size (apply_subst \<sigma> (CoreTy_Meta n)) < 1 + sum_list (map (core_type_size \<circ> apply_subst \<sigma>) (map snd flds))"
        using True sum_eq by simp
      thus ?thesis using CoreTy_Record by (simp add: comp_def case_prod_beta)
    next
      case False
      have "core_type_size t \<le> sum_list (map core_type_size (map snd flds))"
        using canonically_ordered_monoid_add_class.member_le_sum_list t_in by force
      hence "core_type_size t < core_type_size ty"
        using CoreTy_Record by (simp add: comp_def)
      from less.IH[OF this \<open>occurs n t\<close> False]
      have "core_type_size (apply_subst \<sigma> (CoreTy_Meta n)) < core_type_size (apply_subst \<sigma> t)" .
      also have "core_type_size (apply_subst \<sigma> t) \<le> sum_list (map (\<lambda>t. core_type_size (apply_subst \<sigma> t)) (map snd flds))"
        using canonically_ordered_monoid_add_class.member_le_sum_list t_in by force
      also have "... = sum_list (map (core_type_size \<circ> apply_subst \<sigma>) (map snd flds))"
        by (simp add: comp_def)
      also have "... < 1 + sum_list (map (core_type_size \<circ> apply_subst \<sigma>) (map snd flds))" by simp
      finally show ?thesis using CoreTy_Record by (simp add: comp_def case_prod_beta)
    qed
  next
    case (CoreTy_Array elem dims)
    from less.prems CoreTy_Array have "n \<in> type_metavars elem" by (simp add: occurs_def)
    hence "occurs n elem" by (simp add: occurs_def)
    show ?thesis
    proof (cases "elem = CoreTy_Meta n")
      case True
      have "core_type_size (apply_subst \<sigma> elem) < 1 + core_type_size (apply_subst \<sigma> elem)"
        by simp
      thus ?thesis using True CoreTy_Array by simp
    next
      case False
      have "core_type_size elem < core_type_size ty"
        using CoreTy_Array by simp
      from less.IH[OF this \<open>occurs n elem\<close> False]
      have "core_type_size (apply_subst \<sigma> (CoreTy_Meta n)) < core_type_size (apply_subst \<sigma> elem)" .
      also have "... < 1 + core_type_size (apply_subst \<sigma> elem)" by simp
      finally show ?thesis using CoreTy_Array by simp
    qed
  qed
qed

(* The occurs check prevents infinite types: if metavariable n occurs in ty
   (and ty is not just CoreTy_Meta n), then no substitution can make
   CoreTy_Meta n equal to ty. *)
lemma occurs_check_no_unifier:
  assumes "occurs n ty"
      and "ty \<noteq> CoreTy_Meta n"
    shows "apply_subst \<sigma> (CoreTy_Meta n) \<noteq> apply_subst \<sigma> ty"
proof
  assume "apply_subst \<sigma> (CoreTy_Meta n) = apply_subst \<sigma> ty"
  hence "core_type_size (apply_subst \<sigma> (CoreTy_Meta n)) = core_type_size (apply_subst \<sigma> ty)"
    by simp
  moreover from occurs_implies_larger_size[OF assms]
  have "core_type_size (apply_subst \<sigma> (CoreTy_Meta n)) < core_type_size (apply_subst \<sigma> ty)" .
  ultimately show False by simp
qed

(* Completeness of unification: if a unifier exists, then unify will find one. *)
theorem unify_complete:
  "apply_subst \<sigma> ty1 = apply_subst \<sigma> ty2 \<Longrightarrow>
   \<exists>\<theta>. unify ty1 ty2 = Some \<theta>"
  and unify_list_complete:
  "list_all (\<lambda>(t1, t2). apply_subst \<sigma> t1 = apply_subst \<sigma> t2) (zip tys1 tys2) \<Longrightarrow>
   length tys1 = length tys2 \<Longrightarrow>
   \<exists>\<theta>. unify_list tys1 tys2 = Some \<theta>"
proof (induction ty1 ty2 and tys1 tys2 arbitrary: \<sigma> and \<sigma> rule: unify_unify_list.induct)
  (* CoreTy_Name / ty2 *)
  case (1 name1 tyArgs1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    show ?thesis
    proof (cases "occurs n (CoreTy_Name name1 tyArgs1)")
      case True
      from occurs_check_no_unifier[OF True] "1.prems" CoreTy_Meta
      show ?thesis
        by (metis unify.simps(8)) 
    next
      case False
      then show ?thesis using CoreTy_Meta by auto
    qed
  next
    case (CoreTy_Name name2 tyArgs2)
    from "1.prems" CoreTy_Name have cond: "name1 = name2 \<and> length tyArgs1 = length tyArgs2"
      using map_eq_imp_length_eq by auto
    from "1.prems" CoreTy_Name cond have
      "list_all (\<lambda>(t1, t2). apply_subst \<sigma> t1 = apply_subst \<sigma> t2) (zip tyArgs1 tyArgs2)"
      by (simp add: list_all_length list_eq_iff_nth_eq)
    from "1.IH"[OF CoreTy_Name _ this] cond obtain \<theta> where "unify_list tyArgs1 tyArgs2 = Some \<theta>"
      by auto
    with cond CoreTy_Name show ?thesis by auto
  qed auto
next
  (* CoreTy_Bool / ty2 *)
  case (2 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    (* occurs check always passes for Bool *)
    have "\<not> occurs n CoreTy_Bool" by (simp add: occurs_def)
    then show ?thesis using CoreTy_Meta by auto
  qed auto
next
  (* CoreTy_FiniteInt / ty2 *)
  case (3 sign bits ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    (* occurs check always passes for FiniteInt *)
    have "\<not> occurs n (CoreTy_FiniteInt sign bits)" by (simp add: occurs_def)
    then show ?thesis using CoreTy_Meta by auto
  qed auto
next
  (* CoreTy_MathInt / ty2 *)
  case (4 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    (* occurs check always passes for MathInt *)
    have "\<not> occurs n CoreTy_MathInt" by (simp add: occurs_def)
    then show ?thesis using CoreTy_Meta by auto
  qed auto
next
  (* CoreTy_MathReal / ty2 *)
  case (5 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    (* occurs check always passes for MathReal *)
    have "\<not> occurs n CoreTy_MathReal" by (simp add: occurs_def)
    then show ?thesis using CoreTy_Meta by auto
  qed auto
next
  (* CoreTy_Record / ty2 *)
  case (6 flds1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    show ?thesis
    proof (cases "occurs n (CoreTy_Record flds1)")
      case True
      from occurs_check_no_unifier[OF True] "6.prems" CoreTy_Meta
      show ?thesis
        by (metis CoreType.distinct(53))
    next
      case False
      then show ?thesis using CoreTy_Meta by auto
    qed
  next
    case (CoreTy_Record flds2)
    (* From hypothesis: apply_subst \<sigma> (Record flds1) = apply_subst \<sigma> (Record flds2) *)
    from "6.prems" CoreTy_Record
    have eq_result: "CoreTy_Record (map (\<lambda>(n,t). (n, apply_subst \<sigma> t)) flds1) =
                     CoreTy_Record (map (\<lambda>(n,t). (n, apply_subst \<sigma> t)) flds2)"
      by simp
    hence eq_flds: "map (\<lambda>(n,t). (n, apply_subst \<sigma> t)) flds1 =
                    map (\<lambda>(n,t). (n, apply_subst \<sigma> t)) flds2"
      by simp
    (* This implies field names are equal *)
    have names_eq: "map fst flds1 = map fst flds2"
    proof -
      have "map fst (map (\<lambda>(n,t). (n, apply_subst \<sigma> t)) flds1) =
            map fst (map (\<lambda>(n,t). (n, apply_subst \<sigma> t)) flds2)"
        using eq_flds by simp
      thus ?thesis by (simp add: case_prod_beta comp_def)
    qed
    (* And types are pairwise equal under substitution *)
    have types_eq: "map (apply_subst \<sigma>) (map snd flds1) = map (apply_subst \<sigma>) (map snd flds2)"
    proof -
      have "map snd (map (\<lambda>(n,t). (n, apply_subst \<sigma> t)) flds1) =
            map snd (map (\<lambda>(n,t). (n, apply_subst \<sigma> t)) flds2)"
        using eq_flds by simp
      thus ?thesis by (simp add: case_prod_beta comp_def)
    qed
    hence len_eq: "length (map snd flds1) = length (map snd flds2)" using length_map by metis
    from types_eq len_eq have
      "list_all (\<lambda>(t1, t2). apply_subst \<sigma> t1 = apply_subst \<sigma> t2) (zip (map snd flds1) (map snd flds2))"
      by (simp add: list_all_length list_eq_iff_nth_eq)
    from "6.IH"[OF CoreTy_Record names_eq this len_eq] obtain \<theta> where
      "unify_list (map snd flds1) (map snd flds2) = Some \<theta>" by auto
    with names_eq CoreTy_Record show ?thesis by auto
  qed auto
next
  (* CoreTy_Array / ty2 *)
  case (7 elemTy1 dims1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    show ?thesis
    proof (cases "occurs n (CoreTy_Array elemTy1 dims1)")
      case True
      from occurs_check_no_unifier[OF True] "7.prems" CoreTy_Meta
      show ?thesis
        by (metis CoreType.distinct(55))
    next
      case False
      then show ?thesis using CoreTy_Meta by auto
    qed
  next
    case (CoreTy_Array elemTy2 dims2)
    from "7.prems" CoreTy_Array have dims_eq: "dims1 = dims2" by simp
    from "7.prems" CoreTy_Array have "apply_subst \<sigma> elemTy1 = apply_subst \<sigma> elemTy2" by simp
    from "7.IH"[OF CoreTy_Array dims_eq this] obtain \<theta> where "unify elemTy1 elemTy2 = Some \<theta>" by auto
    with dims_eq CoreTy_Array show ?thesis by auto
  qed auto
next
  (* CoreTy_Meta / ty2 *)
  case (8 n ty2)
  show ?case
  proof (cases "occurs n ty2 \<and> ty2 \<noteq> CoreTy_Meta n")
    case True
    from occurs_check_no_unifier[of n ty2] True "8.prems"
    show ?thesis by simp
  next
    case False
    then show ?thesis by auto
  qed
next
  (* unify_list [] [] *)
  case 9
  then show ?case by simp
next
  (* unify_list [] (ty # tys) - impossible due to length constraint *)
  case (10 ty tys)
  then show ?case by simp
next
  (* unify_list (ty # tys) [] - impossible due to length constraint *)
  case (11 ty tys)
  then show ?case by simp
next
  (* unify_list (ty1 # tys1) (ty2 # tys2) *)
  case (12 ty1 tys1 ty2 tys2)
  (* Extract hypotheses *)
  from "12.prems" have head_unifies: "apply_subst \<sigma> ty1 = apply_subst \<sigma> ty2"
    and rest_unifies: "list_all (\<lambda>(t1, t2). apply_subst \<sigma> t1 = apply_subst \<sigma> t2) (zip tys1 tys2)"
    and len_eq: "length tys1 = length tys2"
    by simp_all
  (* Use IH to unify heads *)
  from "12.IH"(1)[OF head_unifies] obtain \<theta>1 where unify_head: "unify ty1 ty2 = Some \<theta>1" by auto
  (* The MGU property tells us that \<sigma> factors through \<theta>1 *)
  from unify_mgu[OF unify_head head_unifies]
  have mgu: "\<And>ty. apply_subst \<sigma> ty = apply_subst \<sigma> (apply_subst \<theta>1 ty)" .
  (* Therefore the rest still unifies after applying \<theta>1 *)
  have rest_unifies': "list_all (\<lambda>(t1, t2). apply_subst \<sigma> t1 = apply_subst \<sigma> t2)
                                (zip (map (apply_subst \<theta>1) tys1) (map (apply_subst \<theta>1) tys2))"
  proof -
    have "\<forall>i < length tys1. apply_subst \<sigma> (apply_subst \<theta>1 (tys1 ! i)) =
                            apply_subst \<sigma> (apply_subst \<theta>1 (tys2 ! i))"
    proof (intro allI impI)
      fix i assume "i < length tys1"
      hence orig: "apply_subst \<sigma> (tys1 ! i) = apply_subst \<sigma> (tys2 ! i)"
        using rest_unifies len_eq by (simp add: list_all_length)
      have "apply_subst \<sigma> (apply_subst \<theta>1 (tys1 ! i)) = apply_subst \<sigma> (tys1 ! i)"
        using mgu by simp
      also have "... = apply_subst \<sigma> (tys2 ! i)" using orig .
      also have "... = apply_subst \<sigma> (apply_subst \<theta>1 (tys2 ! i))"
        using mgu by simp
      finally show "apply_subst \<sigma> (apply_subst \<theta>1 (tys1 ! i)) =
                    apply_subst \<sigma> (apply_subst \<theta>1 (tys2 ! i))" .
    qed
    thus ?thesis by (simp add: list_all_length)
  qed
  have len_eq': "length (map (apply_subst \<theta>1) tys1) = length (map (apply_subst \<theta>1) tys2)"
    using len_eq by simp
  (* Use IH for unify_list on the substituted lists *)
  from "12.IH"(2)[OF unify_head rest_unifies' len_eq']
  obtain \<theta>2 where unify_rest: "unify_list (map (apply_subst \<theta>1) tys1) (map (apply_subst \<theta>1) tys2) = Some \<theta>2"
    by auto
  (* Combine results *)
  have "unify_list (ty1 # tys1) (ty2 # tys2) = Some (compose_subst \<theta>2 \<theta>1)"
    using unify_head unify_rest by simp
  then show ?case by blast
qed


end
