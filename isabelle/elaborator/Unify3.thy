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
  "unify is_flex ty1 ty2 = Some subst \<Longrightarrow>
   is_runtime_type env ty1 \<Longrightarrow>
   is_runtime_type env ty2 \<Longrightarrow>
   \<forall>ty \<in> fmran' subst. is_runtime_type env ty"
  and unify_list_preserves_runtime:
  "unify_list is_flex tys1 tys2 = Some subst \<Longrightarrow>
   list_all (is_runtime_type env) tys1 \<Longrightarrow>
   list_all (is_runtime_type env) tys2 \<Longrightarrow>
   \<forall>ty \<in> fmran' subst. is_runtime_type env ty"
proof (induction is_flex ty1 ty2 and is_flex tys1 tys2 arbitrary: subst and subst rule: unify_unify_list.induct)
  (* CoreTy_Datatype / ty2 *)
  case (1 is_flex name1 tyArgs1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    then have subst_eq: "subst = singleton_subst n (CoreTy_Datatype name1 tyArgs1)"
      using "1.prems"(1) by (auto split: if_splits)
    have ty1_rt: "is_runtime_type env (CoreTy_Datatype name1 tyArgs1)" using "1.prems"(2) by simp
    show ?thesis using subst_eq ty1_rt by (auto simp: fmran'_singleton_subst)
  next
    case (CoreTy_Datatype name2 tyArgs2)
    show ?thesis
    proof (cases "name1 = name2")
      case False then show ?thesis using "1.prems"(1) CoreTy_Datatype by auto
    next
      case True
      with "1.prems"(1) CoreTy_Datatype have unify_ok: "unify_list is_flex tyArgs1 tyArgs2 = Some subst" by simp
      from "1.prems"(2) have "list_all (is_runtime_type env) tyArgs1" by auto
      from "1.prems"(3) CoreTy_Datatype have "list_all (is_runtime_type env) tyArgs2"
        using is_runtime_type.simps(1) by blast
      from "1.IH"[OF CoreTy_Datatype True unify_ok
                    \<open>list_all (is_runtime_type env) tyArgs1\<close>
                    \<open>list_all (is_runtime_type env) tyArgs2\<close>]
      show ?thesis .
    qed
  qed auto
next
  (* CoreTy_Bool / ty2 *)
  case (2 is_flex ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    then have "subst = singleton_subst n CoreTy_Bool" using 2(1) by (simp split: if_splits)
    then show ?thesis by (auto simp: fmran'_singleton_subst)
  qed (auto simp: fmran'_def)
next
  (* CoreTy_FiniteInt / ty2 *)
  case (3 is_flex sign bits ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    then have "subst = singleton_subst n (CoreTy_FiniteInt sign bits)" using 3(1) by (simp split: if_splits)
    then show ?thesis by (auto simp: fmran'_singleton_subst)
  qed (auto simp: fmran'_def split: if_splits)
next
  (* CoreTy_MathInt / ty2 - MathInt is not runtime, so premise is false *)
  case (4 is_flex ty2)
  then show ?case by simp
next
  (* CoreTy_MathReal / ty2 - MathReal is not runtime, so premise is false *)
  case (5 is_flex ty2)
  then show ?case by simp
next
  (* CoreTy_Record / ty2 *)
  case (6 is_flex flds1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    then have subst_eq: "subst = singleton_subst n (CoreTy_Record flds1)"
      using "6.prems"(1) by (auto split: if_splits)
    have ty1_rt: "is_runtime_type env (CoreTy_Record flds1)" using "6.prems"(2) by simp
    show ?thesis using subst_eq ty1_rt by (auto simp: fmran'_singleton_subst)
  next
    case (CoreTy_Record flds2)
    from "6.prems"(1) CoreTy_Record have names_eq: "map fst flds1 = map fst flds2"
      by (auto split: if_splits)
    from "6.prems"(1) CoreTy_Record names_eq
    have unify_ok: "unify_list is_flex (map snd flds1) (map snd flds2) = Some subst" by simp
    from "6.prems"(2) have "list_all (is_runtime_type env) (map snd flds1)" by simp
    from "6.prems"(3) CoreTy_Record have "list_all (is_runtime_type env) (map snd flds2)" by simp
    from "6.IH"[OF CoreTy_Record names_eq unify_ok
                  \<open>list_all (is_runtime_type env) (map snd flds1)\<close>
                  \<open>list_all (is_runtime_type env) (map snd flds2)\<close>]
    show ?thesis .
  qed auto
next
  (* CoreTy_Array / ty2 *)
  case (7 is_flex elemTy1 dims1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    then have subst_eq: "subst = singleton_subst n (CoreTy_Array elemTy1 dims1)"
      using "7.prems"(1) by (auto split: if_splits)
    have ty1_rt: "is_runtime_type env (CoreTy_Array elemTy1 dims1)" using "7.prems"(2) by simp
    show ?thesis using subst_eq ty1_rt by (auto simp: fmran'_singleton_subst)
  next
    case (CoreTy_Array elemTy2 dims2)
    show ?thesis
    proof (cases "dims1 = dims2")
      case False then show ?thesis using 7(2) CoreTy_Array by simp
    next
      case True
      with 7(2) CoreTy_Array have unify_ok: "unify is_flex elemTy1 elemTy2 = Some subst" by simp
      from "7.prems"(2) have "is_runtime_type env elemTy1" by simp
      from "7.prems"(3) CoreTy_Array have "is_runtime_type env elemTy2" by simp
      from "7.IH"[OF CoreTy_Array True unify_ok
                    \<open>is_runtime_type env elemTy1\<close>
                    \<open>is_runtime_type env elemTy2\<close>]
      show ?thesis .
    qed
  qed auto
next
  (* CoreTy_Var / ty2 *)
  case (8 is_flex n ty2)
  show ?case
  proof (cases "is_flex n")
    case True
    show ?thesis
    proof (cases "occurs n ty2 \<and> ty2 \<noteq> CoreTy_Var n")
      case True then show ?thesis using 8(1) \<open>is_flex n\<close> by simp
    next
      case False
      show ?thesis
      proof (cases "ty2 = CoreTy_Var n")
        case True
        then have "subst = fmempty" using 8(1) \<open>is_flex n\<close> by simp
        then show ?thesis by (simp add: fmran'_def)
      next
        case neq: False
        with False have "subst = singleton_subst n ty2" using 8(1) \<open>is_flex n\<close> by simp
        then show ?thesis using "8.prems"(3)
          by (auto simp: fmran'_singleton_subst)
      qed
    qed
  next
    case flex_n_false: False
    show ?thesis
    proof (cases ty2)
      case (CoreTy_Var m)
      show ?thesis
      proof (cases "m = n")
        case True
        then have "subst = fmempty" using 8(1) flex_n_false CoreTy_Var by simp
        then show ?thesis by (simp add: fmran'_def)
      next
        case neq: False
        show ?thesis
        proof (cases "is_flex m")
          case True
          from 8(1) flex_n_false CoreTy_Var neq True
          have "subst = singleton_subst m (CoreTy_Var n)" by simp
          then show ?thesis using "8.prems"(2)
            by (auto simp: fmran'_singleton_subst)
        next
          case False
          then show ?thesis using 8(1) flex_n_false CoreTy_Var neq by simp
        qed
      qed
    next
      case (CoreTy_Datatype name args)
      then show ?thesis using 8(1) flex_n_false by simp
    next
      case CoreTy_Bool
      then show ?thesis using 8(1) flex_n_false by simp
    next
      case (CoreTy_FiniteInt sign bits)
      then show ?thesis using 8(1) flex_n_false by simp
    next
      case CoreTy_MathInt
      then show ?thesis using 8(1) flex_n_false by simp
    next
      case CoreTy_MathReal
      then show ?thesis using 8(1) flex_n_false by simp
    next
      case (CoreTy_Record flds)
      then show ?thesis using 8(1) flex_n_false by simp
    next
      case (CoreTy_Array elem dims)
      then show ?thesis using 8(1) flex_n_false by simp
    qed
  qed
next
  (* unify_list [] [] *)
  case (9 is_flex)
  then show ?case by (simp add: fmran'_def)
next
  (* unify_list [] (ty # tys) *)
  case (10 is_flex ty tys)
  then show ?case by simp
next
  (* unify_list (ty # tys) [] *)
  case (11 is_flex ty tys)
  then show ?case by simp
next
  (* unify_list (ty1 # tys1) (ty2 # tys2) *)
  case (12 is_flex ty1 rest1 ty2 rest2)
  from 12(3) obtain subst1 subst2 where
    unify_head: "unify is_flex ty1 ty2 = Some subst1" and
    unify_rest: "unify_list is_flex (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2) = Some subst2" and
    subst_compose: "subst = compose_subst subst2 subst1"
    by (auto split: option.splits)
  from 12(4) have ty1_runtime: "is_runtime_type env ty1" and rest1_runtime: "list_all (is_runtime_type env) rest1"
    by simp_all
  from 12(5) have ty2_runtime: "is_runtime_type env ty2" and rest2_runtime: "list_all (is_runtime_type env) rest2"
    by simp_all
  (* From IH on head: subst1 range is runtime *)
  from "12.IH"(1)[OF unify_head ty1_runtime ty2_runtime]
  have subst1_runtime: "\<forall>ty \<in> fmran' subst1. is_runtime_type env ty" .
  (* Show that applying subst1 to runtime types gives runtime types *)
  have rest1_subst_runtime: "list_all (is_runtime_type env) (map (apply_subst subst1) rest1)"
  proof (simp add: list_all_iff)
    show "\<forall>x\<in>set rest1. is_runtime_type env (apply_subst subst1 x)"
    proof
      fix x assume "x \<in> set rest1"
      hence "is_runtime_type env x" using rest1_runtime by (simp add: list_all_iff)
      thus "is_runtime_type env (apply_subst subst1 x)"
        by (rule apply_subst_preserves_runtime[where src=env and tgt=env])
           (auto simp: subst1_runtime fmran'I split: option.splits)
    qed
  qed
  have rest2_subst_runtime: "list_all (is_runtime_type env) (map (apply_subst subst1) rest2)"
  proof (simp add: list_all_iff)
    show "\<forall>x\<in>set rest2. is_runtime_type env (apply_subst subst1 x)"
    proof
      fix x assume "x \<in> set rest2"
      hence "is_runtime_type env x" using rest2_runtime by (simp add: list_all_iff)
      thus "is_runtime_type env (apply_subst subst1 x)"
        by (rule apply_subst_preserves_runtime[where src=env and tgt=env])
           (auto simp: subst1_runtime fmran'I split: option.splits)
    qed
  qed
  (* From IH on rest: subst2 range is runtime *)
  from "12.IH"(2)[OF unify_head unify_rest rest1_subst_runtime rest2_subst_runtime]
  have subst2_runtime: "\<forall>ty \<in> fmran' subst2. is_runtime_type env ty" .
  (* Now show composed substitution range is runtime *)
  from compose_subst_preserves_runtime[OF subst1_runtime subst2_runtime]
  show ?case using subst_compose by simp
qed


(* ========================================================================== *)
(* Unification preserves well-kindedness                                      *)
(* ========================================================================== *)

theorem unify_preserves_well_kinded:
  "unify is_flex ty1 ty2 = Some subst \<Longrightarrow>
   is_well_kinded env ty1 \<Longrightarrow>
   is_well_kinded env ty2 \<Longrightarrow>
   \<forall>ty \<in> fmran' subst. is_well_kinded env ty"
  and unify_list_preserves_well_kinded:
  "unify_list is_flex tys1 tys2 = Some subst \<Longrightarrow>
   list_all (is_well_kinded env) tys1 \<Longrightarrow>
   list_all (is_well_kinded env) tys2 \<Longrightarrow>
   \<forall>ty \<in> fmran' subst. is_well_kinded env ty"
proof (induction is_flex ty1 ty2 and is_flex tys1 tys2 arbitrary: subst and subst rule: unify_unify_list.induct)
  (* CoreTy_Datatype / ty2 *)
  case (1 is_flex name1 tyArgs1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    then have subst_eq: "subst = singleton_subst n (CoreTy_Datatype name1 tyArgs1)"
      using 1(2) by (auto split: if_splits)
    have ty1_wk: "is_well_kinded env (CoreTy_Datatype name1 tyArgs1)" using "1.prems"(2) by simp
    show ?thesis using subst_eq ty1_wk by (auto simp: fmran'_singleton_subst)
  next
    case (CoreTy_Datatype name2 tyArgs2)
    show ?thesis
    proof (cases "name1 = name2")
      case False then show ?thesis using "1.prems"(1) CoreTy_Datatype by auto
    next
      case True
      with "1.prems"(1) CoreTy_Datatype have unify_ok: "unify_list is_flex tyArgs1 tyArgs2 = Some subst" by simp
      have args1_wk: "list_all (is_well_kinded env) tyArgs1"
        using "1.prems"(2) by (auto split: option.splits)
      have args2_wk: "list_all (is_well_kinded env) tyArgs2"
        using "1.prems"(3) CoreTy_Datatype by (auto split: option.splits)
      from "1.IH"[OF CoreTy_Datatype True unify_ok args1_wk args2_wk]
      show ?thesis .
    qed
  qed auto
next
  (* CoreTy_Bool / ty2 *)
  case (2 is_flex ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    then have "subst = singleton_subst n CoreTy_Bool" using 2(1) by (simp split: if_splits)
    then show ?thesis by (auto simp: fmran'_singleton_subst)
  qed (auto simp: fmran'_def)
next
  (* CoreTy_FiniteInt / ty2 *)
  case (3 is_flex sign bits ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    then have "subst = singleton_subst n (CoreTy_FiniteInt sign bits)" using 3(1) by (simp split: if_splits)
    then show ?thesis by (auto simp: fmran'_singleton_subst)
  qed (auto simp: fmran'_def split: if_splits)
next
  (* CoreTy_MathInt / ty2 *)
  case (4 is_flex ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    then have "subst = singleton_subst n CoreTy_MathInt" using 4(1) by (simp split: if_splits)
    then show ?thesis by (auto simp: fmran'_singleton_subst)
  qed (auto simp: fmran'_def)
next
  (* CoreTy_MathReal / ty2 *)
  case (5 is_flex ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    then have "subst = singleton_subst n CoreTy_MathReal" using 5(1) by (simp split: if_splits)
    then show ?thesis by (auto simp: fmran'_singleton_subst)
  qed (auto simp: fmran'_def)
next
  (* CoreTy_Record / ty2 *)
  case (6 is_flex flds1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    then have subst_eq: "subst = singleton_subst n (CoreTy_Record flds1)"
      using 6(2) by (auto split: if_splits)
    have ty1_wk: "is_well_kinded env (CoreTy_Record flds1)" using "6.prems"(2) by simp
    show ?thesis using subst_eq ty1_wk by (auto simp: fmran'_singleton_subst)
  next
    case (CoreTy_Record flds2)
    from "6.prems"(1) CoreTy_Record have names_eq: "map fst flds1 = map fst flds2"
      by (auto split: if_splits)
    from "6.prems"(1) CoreTy_Record names_eq
    have unify_ok: "unify_list is_flex (map snd flds1) (map snd flds2) = Some subst" by simp
    from "6.prems"(2) have flds1_wk: "list_all (is_well_kinded env) (map snd flds1)" by simp
    from "6.prems"(3) CoreTy_Record have flds2_wk: "list_all (is_well_kinded env) (map snd flds2)" by simp
    from "6.IH"[OF CoreTy_Record names_eq unify_ok flds1_wk flds2_wk]
    show ?thesis .
  qed auto
next
  (* CoreTy_Array / ty2 *)
  case (7 is_flex elemTy1 dims1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
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
      with 7(2) CoreTy_Array have unify_ok: "unify is_flex elemTy1 elemTy2 = Some subst" by simp
      from "7.prems"(2) have elem1_wk: "is_well_kinded env elemTy1" by simp
      from "7.prems"(3) CoreTy_Array have elem2_wk: "is_well_kinded env elemTy2" by simp
      from "7.IH"[OF CoreTy_Array True unify_ok elem1_wk elem2_wk]
      show ?thesis .
    qed
  qed auto
next
  (* CoreTy_Var / ty2 *)
  case (8 is_flex n ty2)
  show ?case
  proof (cases "is_flex n")
    case True
    show ?thesis
    proof (cases "occurs n ty2 \<and> ty2 \<noteq> CoreTy_Var n")
      case True then show ?thesis using 8(1) \<open>is_flex n\<close> by simp
    next
      case False
      show ?thesis
      proof (cases "ty2 = CoreTy_Var n")
        case True
        then have "subst = fmempty" using 8(1) \<open>is_flex n\<close> by simp
        then show ?thesis by (simp add: fmran'_def)
      next
        case neq: False
        with False have subst_eq: "subst = singleton_subst n ty2" using 8(1) \<open>is_flex n\<close> by simp
        have ty2_wk: "is_well_kinded env ty2" using "8.prems"(3) by simp
        show ?thesis using subst_eq ty2_wk by (auto simp: fmran'_singleton_subst)
      qed
    qed
  next
    case flex_n_false: False
    show ?thesis
    proof (cases ty2)
      case (CoreTy_Var m)
      show ?thesis
      proof (cases "m = n")
        case True
        then have "subst = fmempty" using 8(1) flex_n_false CoreTy_Var by simp
        then show ?thesis by (simp add: fmran'_def)
      next
        case neq: False
        show ?thesis
        proof (cases "is_flex m")
          case True
          from 8(1) flex_n_false CoreTy_Var neq True
          have "subst = singleton_subst m (CoreTy_Var n)" by simp
          then show ?thesis using "8.prems"(2)
            by (auto simp: fmran'_singleton_subst)
        next
          case False
          then show ?thesis using 8(1) flex_n_false CoreTy_Var neq by simp
        qed
      qed
    next
      case (CoreTy_Datatype name args)
      then show ?thesis using 8(1) flex_n_false by simp
    next
      case CoreTy_Bool
      then show ?thesis using 8(1) flex_n_false by simp
    next
      case (CoreTy_FiniteInt sign bits)
      then show ?thesis using 8(1) flex_n_false by simp
    next
      case CoreTy_MathInt
      then show ?thesis using 8(1) flex_n_false by simp
    next
      case CoreTy_MathReal
      then show ?thesis using 8(1) flex_n_false by simp
    next
      case (CoreTy_Record flds)
      then show ?thesis using 8(1) flex_n_false by simp
    next
      case (CoreTy_Array elem dims)
      then show ?thesis using 8(1) flex_n_false by simp
    qed
  qed
next
  (* unify_list [] [] *)
  case (9 is_flex)
  then show ?case by (simp add: fmran'_def)
next
  (* unify_list [] (ty # tys) *)
  case (10 is_flex ty tys)
  then show ?case by simp
next
  (* unify_list (ty # tys) [] *)
  case (11 is_flex ty tys)
  then show ?case by simp
next
  (* unify_list (ty1 # tys1) (ty2 # tys2) *)
  case (12 is_flex ty1 rest1 ty2 rest2)
  from 12(3) obtain subst1 subst2 where
    unify_head: "unify is_flex ty1 ty2 = Some subst1" and
    unify_rest: "unify_list is_flex (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2) = Some subst2" and
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
        by (rule apply_subst_preserves_well_kinded[where src=env and tgt=env])
           (auto simp: subst1_wk fmran'I split: option.splits)
    qed
  qed
  have rest2_subst_wk: "list_all (is_well_kinded env) (map (apply_subst subst1) rest2)"
  proof (simp add: list_all_iff)
    show "\<forall>x\<in>set rest2. is_well_kinded env (apply_subst subst1 x)"
    proof
      fix x assume "x \<in> set rest2"
      hence "is_well_kinded env x" using rest2_wk by (simp add: list_all_iff)
      thus "is_well_kinded env (apply_subst subst1 x)"
        by (rule apply_subst_preserves_well_kinded[where src=env and tgt=env])
           (auto simp: subst1_wk fmran'I split: option.splits)
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
