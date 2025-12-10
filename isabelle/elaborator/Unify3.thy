theory Unify3
  imports Unify2 "../core/CoreKindcheck"
begin

(* This file proves that unification preserves runtime types and well-kindedness:
   if both input types are runtime types (resp. well-kinded), then the range of
   the substitution produced by unify includes only runtime (resp. well-kinded) types.
*)


(* ========================================================================== *)
(* Unification preserves runtime types                                        *)
(* ========================================================================== *)

theorem unify_preserves_runtime:
  "unify ty1 ty2 = Some subst \<Longrightarrow>
   is_runtime_type ty1 \<Longrightarrow>
   is_runtime_type ty2 \<Longrightarrow>
   \<forall>ty \<in> fmran' subst. is_runtime_type ty"
  and unify_list_preserves_runtime:
  "unify_list tys1 tys2 = Some subst \<Longrightarrow>
   list_all is_runtime_type tys1 \<Longrightarrow>
   list_all is_runtime_type tys2 \<Longrightarrow>
   \<forall>ty \<in> fmran' subst. is_runtime_type ty"
proof (induction ty1 ty2 and tys1 tys2 arbitrary: subst and subst rule: unify_unify_list.induct)
  (* CoreTy_Name / ty2 *)
  case (1 name1 tyArgs1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    hence "\<not> occurs n (CoreTy_Name name1 tyArgs1)"
      using "1.prems"(1) by auto
    hence "subst = singleton_subst n (CoreTy_Name name1 tyArgs1)"
      using "1.prems"(1) CoreTy_Meta by force
    thus ?thesis using "1.prems"(1)
      by (metis "1.prems"(2) apply_subst.simps(8) apply_subst_singleton apply_subst_singleton_other
          fmlookup_ran'_iff is_runtime_type.simps(8) option.simps(5))
  next
    case (CoreTy_Name name2 tyArgs2)
    show ?thesis
    proof (cases "name1 = name2")
      case False then show ?thesis using "1.prems"(1) CoreTy_Name by auto
    next
      case True
      with "1.prems"(1) CoreTy_Name have unify_ok: "unify_list tyArgs1 tyArgs2 = Some subst" by simp
      from "1.prems"(2) have "list_all is_runtime_type tyArgs1" by auto
      from "1.prems"(3) CoreTy_Name have "list_all is_runtime_type tyArgs2"
        using is_runtime_type.simps(1) by blast 
      from "1.IH"[OF CoreTy_Name True unify_ok
                    \<open>list_all is_runtime_type tyArgs1\<close>
                    \<open>list_all is_runtime_type tyArgs2\<close>]
      show ?thesis .
    qed
  qed auto
next
  (* CoreTy_Bool / ty2 *)
  case (2 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    then have "subst = singleton_subst n CoreTy_Bool" using 2(1) by simp
    then show ?thesis by (auto simp: fmran'_singleton_subst)
  qed (auto simp: fmran'_def)
next
  (* CoreTy_FiniteInt / ty2 *)
  case (3 sign bits ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    then have "subst = singleton_subst n (CoreTy_FiniteInt sign bits)" using 3(1) by simp
    then show ?thesis by (auto simp: fmran'_singleton_subst)
  qed (auto simp: fmran'_def split: if_splits)
next
  (* CoreTy_MathInt / ty2 - MathInt is not runtime, so premise is false *)
  case (4 ty2)
  then show ?case by simp
next
  (* CoreTy_MathReal / ty2 - MathReal is not runtime, so premise is false *)
  case (5 ty2)
  then show ?case by simp
next
  (* CoreTy_Record / ty2 *)
  case (6 flds1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    hence "\<not> occurs n (CoreTy_Record flds1)"
      using "6.prems"(1) by auto
    hence "subst = singleton_subst n (CoreTy_Record flds1)"
      using "6.prems"(1) CoreTy_Meta by force
    thus ?thesis using "6.prems"(1)
      by (metis "6.prems"(2) apply_subst.simps(8) apply_subst_singleton apply_subst_singleton_other
          fmlookup_ran'_iff is_runtime_type.simps(8) option.simps(5))
  next
    case (CoreTy_Record flds2)
    from "6.prems"(1) CoreTy_Record have names_eq: "map fst flds1 = map fst flds2"
      by (auto split: if_splits)
    from "6.prems"(1) CoreTy_Record names_eq
    have unify_ok: "unify_list (map snd flds1) (map snd flds2) = Some subst" by simp
    from "6.prems"(2) have "list_all is_runtime_type (map snd flds1)" by simp
    from "6.prems"(3) CoreTy_Record have "list_all is_runtime_type (map snd flds2)" by simp
    from "6.IH"[OF CoreTy_Record names_eq unify_ok
                  \<open>list_all is_runtime_type (map snd flds1)\<close>
                  \<open>list_all is_runtime_type (map snd flds2)\<close>]
    show ?thesis .
  qed auto
next
  (* CoreTy_Array / ty2 *)
  case (7 elemTy1 dims1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    hence "\<not> occurs n (CoreTy_Array elemTy1 dims1)"
      using "7.prems"(1) by auto
    hence "subst = singleton_subst n (CoreTy_Array elemTy1 dims1)"
      using "7.prems"(1) CoreTy_Meta by force
    thus ?thesis using "7.prems"(1)
      by (metis "7.prems"(2) apply_subst.simps(8) apply_subst_singleton apply_subst_singleton_other
          fmlookup_ran'_iff is_runtime_type.simps(8) option.simps(5))
  next
    case (CoreTy_Array elemTy2 dims2)
    show ?thesis
    proof (cases "dims1 = dims2")
      case False then show ?thesis using 7(2) CoreTy_Array by simp
    next
      case True
      with 7(2) CoreTy_Array have unify_ok: "unify elemTy1 elemTy2 = Some subst" by simp
      from "7.prems"(2) have "is_runtime_type elemTy1" by simp
      from "7.prems"(3) CoreTy_Array have "is_runtime_type elemTy2" by simp
      from "7.IH"[OF CoreTy_Array True unify_ok
                    \<open>is_runtime_type elemTy1\<close>
                    \<open>is_runtime_type elemTy2\<close>]
      show ?thesis .
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
      then show ?thesis by (simp add: fmran'_def)
    next
      case neq: False
      with False have "subst = singleton_subst n ty2" using 8(1) by simp
      then show ?thesis using "8.prems"(3)
        by (auto simp: fmran'_singleton_subst)
    qed
  qed
next
  (* unify_list [] [] *)
  case 9
  then show ?case by (simp add: fmran'_def)
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
  from 12(4) have ty1_runtime: "is_runtime_type ty1" and rest1_runtime: "list_all is_runtime_type rest1"
    by simp_all
  from 12(5) have ty2_runtime: "is_runtime_type ty2" and rest2_runtime: "list_all is_runtime_type rest2"
    by simp_all
  (* From IH on head: subst1 range is runtime *)
  from "12.IH"(1)[OF unify_head ty1_runtime ty2_runtime]
  have subst1_runtime: "\<forall>ty \<in> fmran' subst1. is_runtime_type ty" .
  (* Show that applying subst1 to runtime types gives runtime types *)
  have rest1_subst_runtime: "list_all is_runtime_type (map (apply_subst subst1) rest1)"
  proof (simp add: list_all_iff)
    show "\<forall>x\<in>set rest1. is_runtime_type (apply_subst subst1 x)"
    proof
      fix x assume "x \<in> set rest1"
      hence "is_runtime_type x" using rest1_runtime by (simp add: list_all_iff)
      thus "is_runtime_type (apply_subst subst1 x)"
        using subst1_runtime apply_subst_preserves_runtime by blast
    qed
  qed
  have rest2_subst_runtime: "list_all is_runtime_type (map (apply_subst subst1) rest2)"
  proof (simp add: list_all_iff)
    show "\<forall>x\<in>set rest2. is_runtime_type (apply_subst subst1 x)"
    proof
      fix x assume "x \<in> set rest2"
      hence "is_runtime_type x" using rest2_runtime by (simp add: list_all_iff)
      thus "is_runtime_type (apply_subst subst1 x)"
        using subst1_runtime apply_subst_preserves_runtime by blast
    qed
  qed
  (* From IH on rest: subst2 range is runtime *)
  from "12.IH"(2)[OF unify_head unify_rest rest1_subst_runtime rest2_subst_runtime]
  have subst2_runtime: "\<forall>ty \<in> fmran' subst2. is_runtime_type ty" .
  (* Now show composed substitution range is runtime *)
  from compose_subst_preserves_runtime[OF subst1_runtime subst2_runtime]
  show ?case using subst_compose by simp
qed


(* ========================================================================== *)
(* Unification preserves well-kindedness                                      *)
(* ========================================================================== *)

theorem unify_preserves_well_kinded:
  "unify ty1 ty2 = Some subst \<Longrightarrow>
   is_well_kinded env ty1 \<Longrightarrow>
   is_well_kinded env ty2 \<Longrightarrow>
   \<forall>ty \<in> fmran' subst. is_well_kinded env ty"
  and unify_list_preserves_well_kinded:
  "unify_list tys1 tys2 = Some subst \<Longrightarrow>
   list_all (is_well_kinded env) tys1 \<Longrightarrow>
   list_all (is_well_kinded env) tys2 \<Longrightarrow>
   \<forall>ty \<in> fmran' subst. is_well_kinded env ty"
proof (induction ty1 ty2 and tys1 tys2 arbitrary: subst and subst rule: unify_unify_list.induct)
  (* CoreTy_Name / ty2 *)
  case (1 name1 tyArgs1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    then have subst_eq: "subst = singleton_subst n (CoreTy_Name name1 tyArgs1)"
      using 1(2) by (auto split: if_splits)
    have ty1_wk: "is_well_kinded env (CoreTy_Name name1 tyArgs1)" using "1.prems"(2) by simp
    show ?thesis using subst_eq ty1_wk by (auto simp: fmran'_singleton_subst)
  next
    case (CoreTy_Name name2 tyArgs2)
    show ?thesis
    proof (cases "name1 = name2")
      case False then show ?thesis using "1.prems"(1) CoreTy_Name by auto
    next
      case True
      with "1.prems"(1) CoreTy_Name have unify_ok: "unify_list tyArgs1 tyArgs2 = Some subst" by simp
      (* Extract well-kindedness of args from premises *)
      have args1_wk: "list_all (is_well_kinded env) tyArgs1"
      proof (cases "name1 |\<in>| TE_TypeVars env")
        case True
        with "1.prems"(2) have "tyArgs1 = []" by simp
        thus ?thesis by simp
      next
        case False
        with "1.prems"(2) show ?thesis by (auto split: option.splits)
      qed
      have args2_wk: "list_all (is_well_kinded env) tyArgs2"
      proof (cases "name2 |\<in>| TE_TypeVars env")
        case True
        with "1.prems"(3) CoreTy_Name have "tyArgs2 = []" by simp
        thus ?thesis by simp
      next
        case False
        with "1.prems"(3) CoreTy_Name show ?thesis by (auto split: option.splits)
      qed
      from "1.IH"[OF CoreTy_Name True unify_ok args1_wk args2_wk]
      show ?thesis .
    qed
  qed auto
next
  (* CoreTy_Bool / ty2 *)
  case (2 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    then have "subst = singleton_subst n CoreTy_Bool" using 2(1) by simp
    then show ?thesis by (auto simp: fmran'_singleton_subst)
  qed (auto simp: fmran'_def)
next
  (* CoreTy_FiniteInt / ty2 *)
  case (3 sign bits ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    then have "subst = singleton_subst n (CoreTy_FiniteInt sign bits)" using 3(1) by simp
    then show ?thesis by (auto simp: fmran'_singleton_subst)
  qed (auto simp: fmran'_def split: if_splits)
next
  (* CoreTy_MathInt / ty2 *)
  case (4 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    then have "subst = singleton_subst n CoreTy_MathInt" using 4(1) by simp
    then show ?thesis by (auto simp: fmran'_singleton_subst)
  qed (auto simp: fmran'_def)
next
  (* CoreTy_MathReal / ty2 *)
  case (5 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    then have "subst = singleton_subst n CoreTy_MathReal" using 5(1) by simp
    then show ?thesis by (auto simp: fmran'_singleton_subst)
  qed (auto simp: fmran'_def)
next
  (* CoreTy_Record / ty2 *)
  case (6 flds1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    then have subst_eq: "subst = singleton_subst n (CoreTy_Record flds1)"
      using 6(2) by (auto split: if_splits)
    have ty1_wk: "is_well_kinded env (CoreTy_Record flds1)" using "6.prems"(2) by simp
    show ?thesis using subst_eq ty1_wk by (auto simp: fmran'_singleton_subst)
  next
    case (CoreTy_Record flds2)
    from "6.prems"(1) CoreTy_Record have names_eq: "map fst flds1 = map fst flds2"
      by (auto split: if_splits)
    from "6.prems"(1) CoreTy_Record names_eq
    have unify_ok: "unify_list (map snd flds1) (map snd flds2) = Some subst" by simp
    from "6.prems"(2) have flds1_wk: "list_all (is_well_kinded env) (map snd flds1)" by simp
    from "6.prems"(3) CoreTy_Record have flds2_wk: "list_all (is_well_kinded env) (map snd flds2)" by simp
    from "6.IH"[OF CoreTy_Record names_eq unify_ok flds1_wk flds2_wk]
    show ?thesis .
  qed auto
next
  (* CoreTy_Array / ty2 *)
  case (7 elemTy1 dims1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Meta n)
    then have subst_eq: "subst = singleton_subst n (CoreTy_Array elemTy1 dims1)"
      using 7(2) by (auto split: if_splits)
    have ty1_wk: "is_well_kinded env (CoreTy_Array elemTy1 dims1)" using "7.prems"(2) by simp
    show ?thesis using subst_eq ty1_wk by (auto simp: fmran'_singleton_subst)
  next
    case (CoreTy_Array elemTy2 dims2)
    show ?thesis
    proof (cases "dims1 = dims2")
      case False then show ?thesis using 7(2) CoreTy_Array by simp
    next
      case True
      with 7(2) CoreTy_Array have unify_ok: "unify elemTy1 elemTy2 = Some subst" by simp
      from "7.prems"(2) have elem1_wk: "is_well_kinded env elemTy1" by simp
      from "7.prems"(3) CoreTy_Array have elem2_wk: "is_well_kinded env elemTy2" by simp
      from "7.IH"[OF CoreTy_Array True unify_ok elem1_wk elem2_wk]
      show ?thesis .
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
      then show ?thesis by (simp add: fmran'_def)
    next
      case neq: False
      with False have subst_eq: "subst = singleton_subst n ty2" using 8(1) by simp
      have ty2_wk: "is_well_kinded env ty2" using "8.prems"(3) by simp
      show ?thesis using subst_eq ty2_wk by (auto simp: fmran'_singleton_subst)
    qed
  qed
next
  (* unify_list [] [] *)
  case 9
  then show ?case by (simp add: fmran'_def)
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
  from 12(4) have ty1_wk: "is_well_kinded env ty1" and rest1_wk: "list_all (is_well_kinded env) rest1"
    by simp_all
  from 12(5) have ty2_wk: "is_well_kinded env ty2" and rest2_wk: "list_all (is_well_kinded env) rest2"
    by simp_all
  (* From IH on head: subst1 range is well-kinded *)
  from "12.IH"(1)[OF unify_head ty1_wk ty2_wk]
  have subst1_wk: "\<forall>ty \<in> fmran' subst1. is_well_kinded env ty" .
  (* Show that applying subst1 to well-kinded types gives well-kinded types *)
  have rest1_subst_wk: "list_all (is_well_kinded env) (map (apply_subst subst1) rest1)"
  proof (simp add: list_all_iff)
    show "\<forall>x\<in>set rest1. is_well_kinded env (apply_subst subst1 x)"
    proof
      fix x assume "x \<in> set rest1"
      hence "is_well_kinded env x" using rest1_wk by (simp add: list_all_iff)
      thus "is_well_kinded env (apply_subst subst1 x)"
        by (simp add: apply_subst_preserves_well_kinded fmran'I metasubst_well_kinded_def
            subst1_wk)
    qed
  qed
  have rest2_subst_wk: "list_all (is_well_kinded env) (map (apply_subst subst1) rest2)"
  proof (simp add: list_all_iff)
    show "\<forall>x\<in>set rest2. is_well_kinded env (apply_subst subst1 x)"
    proof
      fix x assume "x \<in> set rest2"
      hence "is_well_kinded env x" using rest2_wk by (simp add: list_all_iff)
      thus "is_well_kinded env (apply_subst subst1 x)"
        by (simp add: apply_subst_preserves_well_kinded fmran'I metasubst_well_kinded_def
            subst1_wk)
    qed
  qed
  (* From IH on rest: subst2 range is well-kinded *)
  from "12.IH"(2)[OF unify_head unify_rest rest1_subst_wk rest2_subst_wk]
  have subst2_wk: "\<forall>ty \<in> fmran' subst2. is_well_kinded env ty" .
  (* Now show composed substitution range is well-kinded *)
  from compose_subst_preserves_well_kinded[OF subst1_wk subst2_wk]
  show ?case using subst_compose by simp
qed

end
