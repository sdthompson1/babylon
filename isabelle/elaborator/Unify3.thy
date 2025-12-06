theory Unify3
  imports "Unify2" "SubstituteTypes"
begin

(* This file proves that unification preserves runtime types and well-kindedness:
   if both input types are runtime types (resp. well-kinded), then the substitution
   produced by unify maps metavariables only to runtime types (resp. well-kinded types). *)


(* The range of the composed substitution *)
lemma compose_subst_range:
  "ty \<in> fmran' (compose_subst s2 s1) \<Longrightarrow>
   ty \<in> fmran' s2 \<or> (\<exists>ty1 \<in> fmran' s1. ty = apply_subst s2 ty1)"
proof -
  assume "ty \<in> fmran' (compose_subst s2 s1)"
  then obtain n where lookup: "fmlookup (compose_subst s2 s1) n = Some ty"
    by (auto simp: fmran'_def)
  show ?thesis
  proof (cases "fmlookup s1 n")
    case None
    hence "fmlookup s2 n = Some ty"
      using lookup by (simp add: fmlookup_compose_subst_None1)
    thus ?thesis by (auto simp: fmran'_def)
  next
    case (Some ty1)
    hence "ty = apply_subst s2 ty1"
      using lookup by (simp add: fmlookup_compose_subst_Some1)
    moreover have "ty1 \<in> fmran' s1" using Some by (auto simp: fmran'_def)
    ultimately show ?thesis by auto
  qed
qed


(* Main theorem: unify preserves runtime types in the substitution range *)
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
  (* Case 1: Meta/Meta *)
  case (1 n m)
  show ?case
  proof (cases "n = m")
    case True
    then have "subst = fmempty" using 1 by simp
    then show ?thesis by (simp add: fmran'_def)
  next
    case False
    then have "subst = singleton_subst n (BabTy_Meta m)" using 1 by simp
    then show ?thesis by (auto simp: fmran'_singleton_subst)
  qed
next
  (* Cases 2-9: Meta on left, ground type on right *)
  case (2 n loc name tyargs)
  then have "subst = singleton_subst n (BabTy_Name loc name tyargs)"
    by (auto split: if_splits)
  then show ?case using "2.prems"(2)
    by (metis "2.prems"(3) apply_subst.simps(1) apply_subst_singleton apply_subst_singleton_other
        fmran'E is_runtime_type.simps(9) option.simps(5))
next
  case (3 n loc)
  then have "subst = singleton_subst n (BabTy_Bool loc)" by simp
  then show ?case by (auto simp: fmran'_singleton_subst)
next
  case (4 n loc sign bits)
  then have "subst = singleton_subst n (BabTy_FiniteInt loc sign bits)" by simp
  then show ?case by (auto simp: fmran'_singleton_subst)
next
  case (5 n loc)
  (* MathInt - but MathInt is not runtime, so premise is false *)
  then show ?case by simp
next
  case (6 n loc)
  (* MathReal - but MathReal is not runtime, so premise is false *)
  then show ?case by simp
next
  case (7 n loc tys)
  then have "subst = singleton_subst n (BabTy_Tuple loc tys)"
    by (auto split: if_splits)
  then show ?case using "7.prems"(2)
    by (metis "7.prems"(3) apply_subst.simps(1) apply_subst_singleton apply_subst_singleton_other
        fmlookup_ran'_iff is_runtime_type.simps(9) option.simps(5)) 
next
  case (8 n loc flds)
  then have "subst = singleton_subst n (BabTy_Record loc flds)"
    by (auto split: if_splits)
  then show ?case using "8.prems"(2)
    by (metis "8.prems"(3) apply_subst.simps(1) apply_subst_singleton apply_subst_singleton_other
        fmlookup_ran'_iff is_runtime_type.simps(9) option.simps(5)) 
next
  case (9 n loc elem dims)
  then have "subst = singleton_subst n (BabTy_Array loc elem dims)"
    by (auto split: if_splits)
  then show ?case using "9.prems"(2)
    by (metis "9.prems"(3) apply_subst.simps(1) apply_subst_singleton apply_subst_singleton_other
        fmlookup_ran'_iff is_runtime_type.simps(9) option.simps(5))
next
  (* Cases 10-17: Ground type on left, meta on right *)
  case (10 loc name tyargs n)
  then have "subst = singleton_subst n (BabTy_Name loc name tyargs)"
    by (auto split: if_splits)
  then show ?case using "10.prems"(1)
    by (metis "10.prems"(2) apply_subst.simps(1) apply_subst_singleton apply_subst_singleton_other
        fmlookup_ran'_iff is_runtime_type.simps(9) option.simps(5))
next
  case (11 loc n)
  then have "subst = singleton_subst n (BabTy_Bool loc)" by simp
  then show ?case by (auto simp: fmran'_singleton_subst)
next
  case (12 loc sign bits n)
  then have "subst = singleton_subst n (BabTy_FiniteInt loc sign bits)" by simp
  then show ?case by (auto simp: fmran'_singleton_subst)
next
  case (13 loc n)
  (* MathInt - but MathInt is not runtime, so premise is false *)
  then show ?case by simp
next
  case (14 loc n)
  (* MathReal - but MathReal is not runtime, so premise is false *)
  then show ?case by simp
next
  case (15 loc tys n)
  then have "subst = singleton_subst n (BabTy_Tuple loc tys)"
    by (auto split: if_splits)
  then show ?case using "15.prems"(1) 
    by (metis "15.prems"(2) apply_subst.simps(1) apply_subst_singleton apply_subst_singleton_other
        fmlookup_ran'_iff is_runtime_type.simps(9) option.simps(5))
next
  case (16 loc flds n)
  then have "subst = singleton_subst n (BabTy_Record loc flds)"
    by (auto split: if_splits)
  then show ?case using "16.prems"(1)
    by (metis "16.prems"(2) apply_subst.simps(1) apply_subst_singleton apply_subst_singleton_other
        fmlookup_ran'_iff is_runtime_type.simps(9) option.simps(5))
next
  case (17 loc elem dims n)
  then have "subst = singleton_subst n (BabTy_Array loc elem dims)"
    by (auto split: if_splits)
  then show ?case using "17.prems"(1)
    by (metis "17.prems"(2) apply_subst.simps(1) apply_subst_singleton apply_subst_singleton_other
        fmlookup_ran'_iff is_runtime_type.simps(9) option.simps(5))
next
  (* Cases 18-21: Base type matching - empty substitution *)
  case 18 then show ?case by (simp add: fmran'_def)
next
  case 19 then show ?case by (auto simp: fmran'_def split: if_splits)
next
  case 20 then show ?case by simp
next
  case 21 then show ?case by simp
next
  (* Case 22: Name/Name *)
  case (22 loc1 n1 args1 loc2 n2 args2)
  show ?case
  proof (cases "n1 = n2 \<and> length args1 = length args2")
    case False
    then show ?thesis using 22 by auto
  next
    case True
    with 22(2) have "unify_list args1 args2 = Some subst" by simp
    from "22.prems"(1) have "list_all is_runtime_type args1"
      using "22.prems"(2) by auto 
    from "22.prems"(2) have "list_all is_runtime_type args2"
      by (meson "22.prems"(3) is_runtime_type.simps(3)) 
    from "22.IH"[OF True \<open>unify_list args1 args2 = Some subst\<close>
                    \<open>list_all is_runtime_type args1\<close>
                    \<open>list_all is_runtime_type args2\<close>]
    show ?thesis .
  qed
next
  (* Case 23: Tuple/Tuple *)
  case (23 loc1 tys1 loc2 tys2)
  show ?case
  proof (cases "length tys1 = length tys2")
    case False
    then show ?thesis using 23 by simp
  next
    case True
    with 23(2) have "unify_list tys1 tys2 = Some subst" by simp
    from "23.prems"(1) have "list_all is_runtime_type tys1"
      using "23.prems"(2) by auto 
    from "23.prems"(2) have "list_all is_runtime_type tys2"
      using "23.prems"(3) by auto 
    from "23.IH"[OF True \<open>unify_list tys1 tys2 = Some subst\<close>
                    \<open>list_all is_runtime_type tys1\<close>
                    \<open>list_all is_runtime_type tys2\<close>]
    show ?thesis .
  qed
next
  (* Case 24: Record/Record *)
  case (24 loc1 flds1 loc2 flds2)
  show ?case
  proof (cases "length flds1 = length flds2 \<and> map fst flds1 = map fst flds2")
    case False
    then show ?thesis using 24 by auto
  next
    case True
    with 24(2) have "unify_list (map snd flds1) (map snd flds2) = Some subst" by simp
    from "24.prems"(1) have "list_all (is_runtime_type \<circ> snd) flds1"
      using "24.prems"(2) by auto 
    hence "list_all is_runtime_type (map snd flds1)" by (simp add: list_all_iff)
    from "24.prems"(2) have "list_all (is_runtime_type \<circ> snd) flds2"
      using "24.prems"(3) by auto 
    hence "list_all is_runtime_type (map snd flds2)" by (simp add: list_all_iff)
    from "24.IH"[OF True \<open>unify_list (map snd flds1) (map snd flds2) = Some subst\<close>
                    \<open>list_all is_runtime_type (map snd flds1)\<close>
                    \<open>list_all is_runtime_type (map snd flds2)\<close>]
    show ?thesis .
  qed
next
  (* Case 25: Array/Array *)
  case (25 loc1 elem1 dims1 loc2 elem2 dims2)
  show ?case
  proof (cases "dims1 = dims2")
    case False
    then show ?thesis using 25 by simp
  next
    case True
    with 25(2) have "unify elem1 elem2 = Some subst" by simp
    from "25.prems"(1) have "is_runtime_type elem1"
      using "25.prems"(2) by auto 
    from "25.prems"(2) have "is_runtime_type elem2"
      using "25.prems"(3) by auto 
    from "25.IH"[OF True \<open>unify elem1 elem2 = Some subst\<close>
                    \<open>is_runtime_type elem1\<close>
                    \<open>is_runtime_type elem2\<close>]
    show ?thesis .
  qed
next
  (* Case 82: unify_list base case *)
  case 82
  then show ?case by (simp add: fmran'_def)
next
  (* Case 83: unify_list Cons/Cons *)
  case (83 ty1 rest1 ty2 rest2)
  from 83(3) obtain subst1 subst2 where
    unify_head: "unify ty1 ty2 = Some subst1" and
    unify_rest: "unify_list (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2) = Some subst2" and
    subst_compose: "subst = compose_subst subst2 subst1"
    by (auto split: option.splits)
  from 83(4) have ty1_runtime: "is_runtime_type ty1" and rest1_runtime: "list_all is_runtime_type rest1"
    by simp_all
  from 83(5) have ty2_runtime: "is_runtime_type ty2" and rest2_runtime: "list_all is_runtime_type rest2"
    by simp_all
  (* From IH on head: subst1 range is runtime *)
  from "83.IH"(1)[OF unify_head ty1_runtime ty2_runtime]
  have subst1_runtime: "\<forall>ty \<in> fmran' subst1. is_runtime_type ty" .
  (* Show that applying subst1 to runtime types gives runtime types *)
  have rest1_subst_runtime: "list_all is_runtime_type (map (apply_subst subst1) rest1)"
  proof (simp add: list_all_iff)
    show "\<forall>x\<in>set rest1. is_runtime_type (apply_subst subst1 x)"
    proof
      fix x assume "x \<in> set rest1"
      hence "is_runtime_type x" using rest1_runtime by (simp add: list_all_iff)
      thus "is_runtime_type (apply_subst subst1 x)"
        using subst1_runtime is_runtime_type_apply_subst by blast
    qed
  qed
  have rest2_subst_runtime: "list_all is_runtime_type (map (apply_subst subst1) rest2)"
  proof (simp add: list_all_iff)
    show "\<forall>x\<in>set rest2. is_runtime_type (apply_subst subst1 x)"
    proof
      fix x assume "x \<in> set rest2"
      hence "is_runtime_type x" using rest2_runtime by (simp add: list_all_iff)
      thus "is_runtime_type (apply_subst subst1 x)"
        using subst1_runtime is_runtime_type_apply_subst by blast
    qed
  qed
  (* From IH on rest: subst2 range is runtime *)
  from "83.IH"(2)[OF unify_head unify_rest rest1_subst_runtime rest2_subst_runtime]
  have subst2_runtime: "\<forall>ty \<in> fmran' subst2. is_runtime_type ty" .
  (* Now show composed substitution range is runtime *)
  show ?case
  proof
    fix ty assume "ty \<in> fmran' subst"
    hence "ty \<in> fmran' (compose_subst subst2 subst1)" using subst_compose by simp
    from compose_subst_range[OF this]
    show "is_runtime_type ty"
    proof
      assume "ty \<in> fmran' subst2"
      thus ?thesis using subst2_runtime by blast
    next
      assume "\<exists>ty1 \<in> fmran' subst1. ty = apply_subst subst2 ty1"
      then obtain ty1 where "ty1 \<in> fmran' subst1" and "ty = apply_subst subst2 ty1" by auto
      from \<open>ty1 \<in> fmran' subst1\<close> subst1_runtime have "is_runtime_type ty1" by blast
      thus ?thesis using \<open>ty = apply_subst subst2 ty1\<close> subst2_runtime is_runtime_type_apply_subst
        by blast
    qed
  qed
qed (simp_all)


(* Unify also preserves well-kindedness in the substitution range *)
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
  \<comment> \<open>Case 1: Meta/Meta - substitution contains only metavariables, which are always well-kinded\<close>
  case (1 n m)
  show ?case
  proof (cases "n = m")
    case True
    then have "subst = fmempty" using 1 by simp
    then show ?thesis by (simp add: fmran'_def)
  next
    case False
    then have "subst = singleton_subst n (BabTy_Meta m)" using 1 by simp
    then show ?thesis by (auto simp: fmran'_singleton_subst)
  qed
next
  \<comment> \<open>Cases 2-9: Meta on left, ground type on right - substitution maps to ty2\<close>
  case (2 n loc name tyargs)
  then have subst_eq: "subst = singleton_subst n (BabTy_Name loc name tyargs)" by (auto split: if_splits)
  have ty2_wk: "is_well_kinded env (BabTy_Name loc name tyargs)" using "2.prems"(3) by simp
  show ?case using subst_eq ty2_wk by (auto simp: fmran'_singleton_subst)
next
  case (3 n loc)
  then have "subst = singleton_subst n (BabTy_Bool loc)" by simp
  then show ?case by (auto simp: fmran'_singleton_subst)
next
  case (4 n loc sign bits)
  then have "subst = singleton_subst n (BabTy_FiniteInt loc sign bits)" by simp
  then show ?case by (auto simp: fmran'_singleton_subst)
next
  case (5 n loc)
  then have "subst = singleton_subst n (BabTy_MathInt loc)" by simp
  then show ?case by (auto simp: fmran'_singleton_subst)
next
  case (6 n loc)
  then have "subst = singleton_subst n (BabTy_MathReal loc)" by simp
  then show ?case by (auto simp: fmran'_singleton_subst)
next
  case (7 n loc tys)
  then have subst_eq: "subst = singleton_subst n (BabTy_Tuple loc tys)" by (auto split: if_splits)
  have ty2_wk: "is_well_kinded env (BabTy_Tuple loc tys)" using "7.prems"(3) by simp
  show ?case using subst_eq ty2_wk by (auto simp: fmran'_singleton_subst)
next
  case (8 n loc flds)
  then have subst_eq: "subst = singleton_subst n (BabTy_Record loc flds)" by (auto split: if_splits)
  have ty2_wk: "is_well_kinded env (BabTy_Record loc flds)" using "8.prems"(3) by simp
  show ?case using subst_eq ty2_wk by (auto simp: fmran'_singleton_subst)
next
  case (9 n loc elem dims)
  then have subst_eq: "subst = singleton_subst n (BabTy_Array loc elem dims)" by (auto split: if_splits)
  have ty2_wk: "is_well_kinded env (BabTy_Array loc elem dims)" using "9.prems"(3) by simp
  show ?case using subst_eq ty2_wk by (auto simp: fmran'_singleton_subst)
next
  \<comment> \<open>Cases 10-17: Ground type on left, meta on right - substitution maps to ty1\<close>
  case (10 loc name tyargs n)
  then have subst_eq: "subst = singleton_subst n (BabTy_Name loc name tyargs)" by (auto split: if_splits)
  have ty1_wk: "is_well_kinded env (BabTy_Name loc name tyargs)" using "10.prems"(2) by simp
  show ?case using subst_eq ty1_wk by (auto simp: fmran'_singleton_subst)
next
  case (11 loc n)
  then have "subst = singleton_subst n (BabTy_Bool loc)" by simp
  then show ?case by (auto simp: fmran'_singleton_subst)
next
  case (12 loc sign bits n)
  then have "subst = singleton_subst n (BabTy_FiniteInt loc sign bits)" by simp
  then show ?case by (auto simp: fmran'_singleton_subst)
next
  case (13 loc n)
  then have "subst = singleton_subst n (BabTy_MathInt loc)" by simp
  then show ?case by (auto simp: fmran'_singleton_subst)
next
  case (14 loc n)
  then have "subst = singleton_subst n (BabTy_MathReal loc)" by simp
  then show ?case by (auto simp: fmran'_singleton_subst)
next
  case (15 loc tys n)
  then have subst_eq: "subst = singleton_subst n (BabTy_Tuple loc tys)" by (auto split: if_splits)
  have ty1_wk: "is_well_kinded env (BabTy_Tuple loc tys)" using "15.prems"(2) by simp
  show ?case using subst_eq ty1_wk by (auto simp: fmran'_singleton_subst)
next
  case (16 loc flds n)
  then have subst_eq: "subst = singleton_subst n (BabTy_Record loc flds)" by (auto split: if_splits)
  have ty1_wk: "is_well_kinded env (BabTy_Record loc flds)" using "16.prems"(2) by simp
  show ?case using subst_eq ty1_wk by (auto simp: fmran'_singleton_subst)
next
  case (17 loc elem dims n)
  then have subst_eq: "subst = singleton_subst n (BabTy_Array loc elem dims)" by (auto split: if_splits)
  have ty1_wk: "is_well_kinded env (BabTy_Array loc elem dims)" using "17.prems"(2) by simp
  show ?case using subst_eq ty1_wk by (auto simp: fmran'_singleton_subst)
next
  \<comment> \<open>Cases 18-21: Base type matching - empty substitution\<close>
  case 18 then show ?case by (simp add: fmran'_def)
next
  case 19 then show ?case by (auto simp: fmran'_def split: if_splits)
next
  case 20 then show ?case by auto
next
  case 21 then show ?case by auto
next
  \<comment> \<open>Case 22: Name/Name\<close>
  case (22 loc1 n1 args1 loc2 n2 args2)
  show ?case
  proof (cases "n1 = n2 \<and> length args1 = length args2")
    case False
    then show ?thesis using 22 by auto
  next
    case True
    with 22(2) have unify_ok: "unify_list args1 args2 = Some subst" by simp
    \<comment> \<open>Extract well-kindedness of args from premises\<close>
    have args1_wk: "list_all (is_well_kinded env) args1"
    proof (cases "n1 |\<in>| TE_TypeVars env")
      case True
      with "22.prems"(2) have "args1 = []" by simp
      thus ?thesis by simp
    next
      case False
      with "22.prems"(2) show ?thesis by (auto split: option.splits)
    qed
    have args2_wk: "list_all (is_well_kinded env) args2"
    proof (cases "n2 |\<in>| TE_TypeVars env")
      case True
      with "22.prems"(3) have "args2 = []" by simp
      thus ?thesis by simp
    next
      case False
      with "22.prems"(3) show ?thesis by (auto split: option.splits)
    qed
    from "22.IH"[OF True unify_ok args1_wk args2_wk]
    show ?thesis .
  qed
next
  \<comment> \<open>Case 23: Tuple/Tuple\<close>
  case (23 loc1 tys1 loc2 tys2)
  show ?case
  proof (cases "length tys1 = length tys2")
    case False
    then show ?thesis using 23 by simp
  next
    case True
    with 23(2) have unify_ok: "unify_list tys1 tys2 = Some subst" by simp
    from "23.prems"(2) have tys1_wk: "list_all (is_well_kinded env) tys1" by simp
    from "23.prems"(3) have tys2_wk: "list_all (is_well_kinded env) tys2" by simp
    from "23.IH"[OF True unify_ok tys1_wk tys2_wk]
    show ?thesis .
  qed
next
  \<comment> \<open>Case 24: Record/Record\<close>
  case (24 loc1 flds1 loc2 flds2)
  show ?case
  proof (cases "length flds1 = length flds2 \<and> map fst flds1 = map fst flds2")
    case False
    then show ?thesis using 24 by auto
  next
    case True
    with 24(2) have unify_ok: "unify_list (map snd flds1) (map snd flds2) = Some subst" by simp
    from "24.prems"(2) have "list_all (is_well_kinded env \<circ> snd) flds1" by simp
    hence flds1_wk: "list_all (is_well_kinded env) (map snd flds1)" by (simp add: list_all_iff)
    from "24.prems"(3) have "list_all (is_well_kinded env \<circ> snd) flds2" by simp
    hence flds2_wk: "list_all (is_well_kinded env) (map snd flds2)" by (simp add: list_all_iff)
    from "24.IH"[OF True unify_ok flds1_wk flds2_wk]
    show ?thesis .
  qed
next
  \<comment> \<open>Case 25: Array/Array\<close>
  case (25 loc1 elem1 dims1 loc2 elem2 dims2)
  show ?case
  proof (cases "dims1 = dims2")
    case False
    then show ?thesis using 25 by simp
  next
    case True
    with 25(2) have unify_ok: "unify elem1 elem2 = Some subst" by simp
    from "25.prems"(2) have elem1_wk: "is_well_kinded env elem1" by simp
    from "25.prems"(3) have elem2_wk: "is_well_kinded env elem2" by simp
    from "25.IH"[OF True unify_ok elem1_wk elem2_wk]
    show ?thesis .
  qed
next
  \<comment> \<open>Case 82: unify_list base case\<close>
  case 82
  then show ?case by (simp add: fmran'_def)
next
  \<comment> \<open>Case 83: unify_list Cons/Cons\<close>
  case (83 ty1 rest1 ty2 rest2)
  from 83(3) obtain subst1 subst2 where
    unify_head: "unify ty1 ty2 = Some subst1" and
    unify_rest: "unify_list (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2) = Some subst2" and
    subst_compose: "subst = compose_subst subst2 subst1"
    by (auto split: option.splits)
  from 83(4) have ty1_wk: "is_well_kinded env ty1" and rest1_wk: "list_all (is_well_kinded env) rest1"
    by simp_all
  from 83(5) have ty2_wk: "is_well_kinded env ty2" and rest2_wk: "list_all (is_well_kinded env) rest2"
    by simp_all
  \<comment> \<open>From IH on head: subst1 range is well-kinded\<close>
  from "83.IH"(1)[OF unify_head ty1_wk ty2_wk]
  have subst1_wk: "\<forall>ty \<in> fmran' subst1. is_well_kinded env ty" .
  \<comment> \<open>Show that applying subst1 to well-kinded types gives well-kinded types\<close>
  have rest1_subst_wk: "list_all (is_well_kinded env) (map (apply_subst subst1) rest1)"
  proof (simp add: list_all_iff)
    show "\<forall>x\<in>set rest1. is_well_kinded env (apply_subst subst1 x)"
    proof
      fix x assume "x \<in> set rest1"
      hence "is_well_kinded env x" using rest1_wk by (simp add: list_all_iff)
      thus "is_well_kinded env (apply_subst subst1 x)"
        using subst1_wk is_well_kinded_apply_subst by blast
    qed
  qed
  have rest2_subst_wk: "list_all (is_well_kinded env) (map (apply_subst subst1) rest2)"
  proof (simp add: list_all_iff)
    show "\<forall>x\<in>set rest2. is_well_kinded env (apply_subst subst1 x)"
    proof
      fix x assume "x \<in> set rest2"
      hence "is_well_kinded env x" using rest2_wk by (simp add: list_all_iff)
      thus "is_well_kinded env (apply_subst subst1 x)"
        using subst1_wk is_well_kinded_apply_subst by blast
    qed
  qed
  \<comment> \<open>From IH on rest: subst2 range is well-kinded\<close>
  from "83.IH"(2)[OF unify_head unify_rest rest1_subst_wk rest2_subst_wk]
  have subst2_wk: "\<forall>ty \<in> fmran' subst2. is_well_kinded env ty" .
  \<comment> \<open>Now show composed substitution range is well-kinded\<close>
  show ?case
  proof
    fix ty assume "ty \<in> fmran' subst"
    hence "ty \<in> fmran' (compose_subst subst2 subst1)" using subst_compose by simp
    from compose_subst_range[OF this]
    show "is_well_kinded env ty"
    proof
      assume "ty \<in> fmran' subst2"
      thus ?thesis using subst2_wk by blast
    next
      assume "\<exists>ty1 \<in> fmran' subst1. ty = apply_subst subst2 ty1"
      then obtain ty1 where "ty1 \<in> fmran' subst1" and "ty = apply_subst subst2 ty1" by auto
      from \<open>ty1 \<in> fmran' subst1\<close> subst1_wk have "is_well_kinded env ty1" by blast
      thus ?thesis using \<open>ty = apply_subst subst2 ty1\<close> subst2_wk is_well_kinded_apply_subst
        by blast
    qed
  qed
qed (simp_all)


(* Composition of substitutions preserves well-kindedness:
   If both substitutions map metavariables to well-kinded types,
   then the composed substitution also maps to well-kinded types. *)
(* See also: is_well_kinded_apply_subst in SubstituteTypes.thy *)
lemma compose_subst_preserves_well_kinded:
  assumes "\<forall>ty \<in> fmran' s1. is_well_kinded env ty"
      and "\<forall>ty \<in> fmran' s2. is_well_kinded env ty"
    shows "\<forall>ty \<in> fmran' (compose_subst s2 s1). is_well_kinded env ty"
proof
  fix ty assume "ty \<in> fmran' (compose_subst s2 s1)"
  from compose_subst_range[OF this] show "is_well_kinded env ty"
  proof
    assume "ty \<in> fmran' s2"
    thus ?thesis using assms(2) by blast
  next
    assume "\<exists>ty1 \<in> fmran' s1. ty = apply_subst s2 ty1"
    then obtain ty1 where "ty1 \<in> fmran' s1" and "ty = apply_subst s2 ty1" by auto
    from \<open>ty1 \<in> fmran' s1\<close> assms(1) have "is_well_kinded env ty1" by blast
    thus ?thesis using \<open>ty = apply_subst s2 ty1\<close> assms(2) is_well_kinded_apply_subst by blast
  qed
qed

(* Composition of substitutions preserves runtime types:
   If both substitutions map metavariables to runtime types,
   then the composed substitution also maps to runtime types. *)
(* See also: is_runtime_type_apply_subst in SubstituteTypes.thy *)
lemma compose_subst_preserves_runtime:
  assumes "\<forall>ty \<in> fmran' s1. is_runtime_type ty"
      and "\<forall>ty \<in> fmran' s2. is_runtime_type ty"
    shows "\<forall>ty \<in> fmran' (compose_subst s2 s1). is_runtime_type ty"
proof
  fix ty assume "ty \<in> fmran' (compose_subst s2 s1)"
  from compose_subst_range[OF this] show "is_runtime_type ty"
  proof
    assume "ty \<in> fmran' s2"
    thus ?thesis using assms(2) by blast
  next
    assume "\<exists>ty1 \<in> fmran' s1. ty = apply_subst s2 ty1"
    then obtain ty1 where "ty1 \<in> fmran' s1" and "ty = apply_subst s2 ty1" by auto
    from \<open>ty1 \<in> fmran' s1\<close> assms(1) have "is_runtime_type ty1" by blast
    thus ?thesis using \<open>ty = apply_subst s2 ty1\<close> assms(2) is_runtime_type_apply_subst by blast
  qed
qed


end
