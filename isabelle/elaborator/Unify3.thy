theory Unify3
  imports Unify2 "../core/CoreKindcheck"
begin

(* This file proves that unification preserves runtime types and well-kindedness:
   if both input types are runtime types (resp. well-kinded), then the range of
   the substitution produced by unify includes only runtime (resp. well-kinded) types.
   Both are instances of one generic result, for any property of types that
   passes to the components that unify recurses into and is preserved by
   substitution.
*)


(* ========================================================================== *)
(* Generic range preservation                                                 *)
(* ========================================================================== *)

(* Where unify answers directly, every type in the range of its result is one of
   the two inputs (it binds one side's variable to the other side). *)
lemma unify_base_range:
  "unify is_flex ty1 ty2 = Some s \<Longrightarrow> \<not> unify_may_recurse ty1 ty2
   \<Longrightarrow> fmran' s \<subseteq> {ty1, ty2}"
  by (cases ty1; cases ty2) (auto simp: fmran'_def singleton_subst_def split: if_splits)

theorem unify_range_preserves:
  fixes P :: "CoreType \<Rightarrow> bool"
  assumes P_args: "\<And>name args. P (CoreTy_Datatype name args) \<Longrightarrow> list_all P args"
      and P_flds: "\<And>flds. P (CoreTy_Record flds) \<Longrightarrow> list_all P (map snd flds)"
      and P_elem: "\<And>elem dims. P (CoreTy_Array elem dims) \<Longrightarrow> P elem"
      and P_subst: "\<And>s ty. \<forall>t \<in> fmran' s. P t \<Longrightarrow> P ty \<Longrightarrow> P (apply_subst s ty)"
  shows "unify is_flex ty1 ty2 = Some subst \<Longrightarrow> P ty1 \<Longrightarrow> P ty2
           \<Longrightarrow> \<forall>t \<in> fmran' subst. P t"
    and "unify_list is_flex tys1 tys2 = Some subst \<Longrightarrow> list_all P tys1 \<Longrightarrow> list_all P tys2
           \<Longrightarrow> \<forall>t \<in> fmran' subst. P t"
proof (induction is_flex ty1 ty2 and is_flex tys1 tys2 arbitrary: subst and subst
       rule: unify_unify_list.induct)
  (* CoreTy_Datatype / ty2 *)
  case (1 is_flex name1 tyArgs1 ty2)
  show ?case
  proof (cases ty2)
    case (CoreTy_Datatype name2 tyArgs2)
    with "1.prems"(1) have eq: "name1 = name2"
      and ok: "unify_list is_flex tyArgs1 tyArgs2 = Some subst"
      by (auto split: if_splits)
    have "list_all P tyArgs2"
      using P_args "1.prems"(3) CoreTy_Datatype by blast
    then show ?thesis
      by (rule "1.IH"[OF CoreTy_Datatype eq ok P_args[OF "1.prems"(2)]])
  qed (use unify_base_range[OF "1.prems"(1)] "1.prems"(2,3) in auto)
next
  (* CoreTy_Bool / ty2 *)
  case (2 is_flex ty2)
  show ?case using unify_base_range[OF "2.prems"(1)] "2.prems"(2,3) by auto
next
  (* CoreTy_FiniteInt / ty2 *)
  case (3 is_flex sign bits ty2)
  show ?case using unify_base_range[OF "3.prems"(1)] "3.prems"(2,3) by auto
next
  (* CoreTy_MathInt / ty2 *)
  case (4 is_flex ty2)
  show ?case using unify_base_range[OF "4.prems"(1)] "4.prems"(2,3) by auto
next
  (* CoreTy_MathReal / ty2 *)
  case (5 is_flex ty2)
  show ?case using unify_base_range[OF "5.prems"(1)] "5.prems"(2,3) by auto
next
  (* CoreTy_Record / ty2 *)
  case (6 is_flex flds1 ty2)
  show ?case
  proof (cases ty2)
    case (CoreTy_Record flds2)
    with "6.prems"(1) have eq: "map fst flds1 = map fst flds2"
      and ok: "unify_list is_flex (map snd flds1) (map snd flds2) = Some subst"
      by (auto split: if_splits)
    have "list_all P (map snd flds2)"
      using P_flds "6.prems"(3) CoreTy_Record by blast
    then show ?thesis
      by (rule "6.IH"[OF CoreTy_Record eq ok P_flds[OF "6.prems"(2)]])
  qed (use unify_base_range[OF "6.prems"(1)] "6.prems"(2,3) in auto)
next
  (* CoreTy_Array / ty2 *)
  case (7 is_flex elemTy1 dims1 ty2)
  show ?case
  proof (cases ty2)
    case (CoreTy_Array elemTy2 dims2)
    with "7.prems"(1) have eq: "dims1 = dims2"
      and ok: "unify is_flex elemTy1 elemTy2 = Some subst"
      by (auto split: if_splits)
    have "P elemTy2"
      using P_elem "7.prems"(3) CoreTy_Array by blast
    then show ?thesis
      by (rule "7.IH"[OF CoreTy_Array eq ok P_elem[OF "7.prems"(2)]])
  qed (use unify_base_range[OF "7.prems"(1)] "7.prems"(2,3) in auto)
next
  (* CoreTy_Var / ty2 *)
  case (8 is_flex n ty2)
  show ?case using unify_base_range[OF "8.prems"(1)] "8.prems"(2,3) by auto
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
  from "12.prems"(1) obtain subst1 subst2 where
    head: "unify is_flex ty1 ty2 = Some subst1" and
    tail: "unify_list is_flex (map (apply_subst subst1) rest1)
                              (map (apply_subst subst1) rest2) = Some subst2" and
    subst_eq: "subst = compose_subst subst2 subst1"
    by (auto split: option.splits)
  from "12.prems"(2,3) have ty1_P: "P ty1" and rest1_P: "list_all P rest1"
    and ty2_P: "P ty2" and rest2_P: "list_all P rest2"
    by simp_all
  have s1: "\<forall>t \<in> fmran' subst1. P t"
    by (rule "12.IH"(1)[OF head ty1_P ty2_P])
  have rest1_P': "list_all P (map (apply_subst subst1) rest1)"
    using rest1_P P_subst[OF s1] by (auto simp: list_all_iff)
  have rest2_P': "list_all P (map (apply_subst subst1) rest2)"
    using rest2_P P_subst[OF s1] by (auto simp: list_all_iff)
  have s2: "\<forall>t \<in> fmran' subst2. P t"
    by (rule "12.IH"(2)[OF head tail rest1_P' rest2_P'])
  show ?case
    unfolding subst_eq
  proof
    fix t assume "t \<in> fmran' (compose_subst subst2 subst1)"
    from compose_subst_range[OF this] show "P t"
      using s1 s2 P_subst by blast
  qed
next
  (* CoreTy_Extern / ty2 *)
  case (13 is_flex n l ty2)
  show ?case using unify_base_range[OF "13.prems"(1)] "13.prems"(2,3) by auto
qed


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
proof -
  have args: "\<And>name args. is_runtime_type env (CoreTy_Datatype name args)
                \<Longrightarrow> list_all (is_runtime_type env) args"
    by auto
  have flds: "\<And>flds. is_runtime_type env (CoreTy_Record flds)
                \<Longrightarrow> list_all (is_runtime_type env) (map snd flds)"
    by simp
  have elem: "\<And>elem dims. is_runtime_type env (CoreTy_Array elem dims)
                \<Longrightarrow> is_runtime_type env elem"
    by simp
  have subst: "is_runtime_type env (apply_subst s ty)"
    if "\<forall>t \<in> fmran' s. is_runtime_type env t" and "is_runtime_type env ty" for s ty
    by (rule apply_subst_preserves_runtime[where src=env and tgt=env, OF that(2)])
       (use that(1) in \<open>auto simp: fmran'I split: option.splits\<close>)
  note gen = unify_range_preserves[where P = "is_runtime_type env", OF args flds elem subst]
  show "unify is_flex ty1 ty2 = Some subst \<Longrightarrow>
        is_runtime_type env ty1 \<Longrightarrow>
        is_runtime_type env ty2 \<Longrightarrow>
        \<forall>ty \<in> fmran' subst. is_runtime_type env ty"
    by (rule gen(1))
  show "unify_list is_flex tys1 tys2 = Some subst \<Longrightarrow>
        list_all (is_runtime_type env) tys1 \<Longrightarrow>
        list_all (is_runtime_type env) tys2 \<Longrightarrow>
        \<forall>ty \<in> fmran' subst. is_runtime_type env ty"
    by (rule gen(2))
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
proof -
  have args: "\<And>name args. is_well_kinded env (CoreTy_Datatype name args)
                \<Longrightarrow> list_all (is_well_kinded env) args"
    by (auto split: option.splits)
  have flds: "\<And>flds. is_well_kinded env (CoreTy_Record flds)
                \<Longrightarrow> list_all (is_well_kinded env) (map snd flds)"
    by simp
  have elem: "\<And>elem dims. is_well_kinded env (CoreTy_Array elem dims)
                \<Longrightarrow> is_well_kinded env elem"
    by simp
  have subst: "is_well_kinded env (apply_subst s ty)"
    if "\<forall>t \<in> fmran' s. is_well_kinded env t" and "is_well_kinded env ty" for s ty
    by (rule apply_subst_preserves_well_kinded[where src=env and tgt=env, OF that(2)])
       (use that(1) in \<open>auto simp: fmran'I split: option.splits\<close>)
  note gen = unify_range_preserves[where P = "is_well_kinded env", OF args flds elem subst]
  show "unify is_flex ty1 ty2 = Some subst \<Longrightarrow>
        is_well_kinded env ty1 \<Longrightarrow>
        is_well_kinded env ty2 \<Longrightarrow>
        \<forall>ty \<in> fmran' subst. is_well_kinded env ty"
    by (rule gen(1))
  show "unify_list is_flex tys1 tys2 = Some subst \<Longrightarrow>
        list_all (is_well_kinded env) tys1 \<Longrightarrow>
        list_all (is_well_kinded env) tys2 \<Longrightarrow>
        \<forall>ty \<in> fmran' subst. is_well_kinded env ty"
    by (rule gen(2))
qed

end
