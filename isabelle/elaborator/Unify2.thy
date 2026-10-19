theory Unify2
  imports Unify
begin

(* Correctness properties for our unification algorithm *)


(* ========================================================================== *)
(* The base cases of unify                                                    *)
(* ========================================================================== *)

(* Where unify answers directly (no recursive call), a successful result is
   either the empty substitution on equal inputs, or binds a flexible variable
   on one side to the other side, which it does not occur in. The correctness
   proofs below handle all base cases through this one lemma. *)
lemma unify_base_casesE:
  assumes "unify is_flex ty1 ty2 = Some s" and "\<not> unify_may_recurse ty1 ty2"
  obtains (refl) "s = fmempty" "ty1 = ty2"
    | (left) v where "ty1 = CoreTy_Var v" "is_flex v" "\<not> occurs v ty2"
                     "s = singleton_subst v ty2"
    | (right) v where "ty2 = CoreTy_Var v" "is_flex v" "\<not> occurs v ty1"
                      "s = singleton_subst v ty1"
  using assms by (cases ty1; cases ty2) (auto simp: occurs_def split: if_splits)


(* ========================================================================== *)
(* Only "flexible" variables are unified                                      *)
(* ========================================================================== *)

lemma unify_base_dom_flex:
  assumes "unify is_flex ty1 ty2 = Some s" and "\<not> unify_may_recurse ty1 ty2"
  shows "\<forall>n. n |\<in>| fmdom s \<longrightarrow> is_flex n"
  using assms by (rule unify_base_casesE) (auto simp: singleton_subst_def)

(* The unifier only ever binds metavariables for which is_flex returns True.
   Every binding in the algorithm is gated by an `if is_flex n` check. *)
lemma unify_unify_list_dom_flex:
  "unify is_flex ty1 ty2 = Some subst \<Longrightarrow> \<forall>n. n |\<in>| fmdom subst \<longrightarrow> is_flex n"
  "unify_list is_flex tys1 tys2 = Some subst \<Longrightarrow> \<forall>n. n |\<in>| fmdom subst \<longrightarrow> is_flex n"
proof (induction is_flex ty1 ty2 and is_flex tys1 tys2 arbitrary: subst and subst
       rule: unify_unify_list.induct)
  case (1 is_flex name1 tyArgs1 ty2)
  show ?case
  proof (cases "unify_may_recurse (CoreTy_Datatype name1 tyArgs1) ty2")
    case True
    then obtain name2 tyArgs2 where ty2_eq: "ty2 = CoreTy_Datatype name2 tyArgs2"
      by (cases ty2) auto
    with "1.prems" have name_eq: "name1 = name2"
      and ul_eq: "unify_list is_flex tyArgs1 tyArgs2 = Some subst"
      by (auto split: if_splits)
    from "1.IH"[OF ty2_eq name_eq ul_eq] show ?thesis .
  next
    case False
    with "1.prems" show ?thesis by (rule unify_base_dom_flex)
  qed
next
  case (2 is_flex ty2)
  from "2.prems" show ?case by (rule unify_base_dom_flex) simp
next
  case (3 is_flex sign bits ty2)
  from "3.prems" show ?case by (rule unify_base_dom_flex) simp
next
  case (4 is_flex ty2)
  from "4.prems" show ?case by (rule unify_base_dom_flex) simp
next
  case (5 is_flex ty2)
  from "5.prems" show ?case by (rule unify_base_dom_flex) simp
next
  case (6 is_flex flds1 ty2)
  show ?case
  proof (cases "unify_may_recurse (CoreTy_Record flds1) ty2")
    case True
    then obtain flds2 where ty2_eq: "ty2 = CoreTy_Record flds2"
      by (cases ty2) auto
    with "6.prems" have fst_eq: "map fst flds1 = map fst flds2"
      and ul_eq: "unify_list is_flex (map snd flds1) (map snd flds2) = Some subst"
      by (auto split: if_splits)
    from "6.IH"[OF ty2_eq fst_eq ul_eq] show ?thesis .
  next
    case False
    with "6.prems" show ?thesis by (rule unify_base_dom_flex)
  qed
next
  case (7 is_flex elemTy1 dims1 ty2)
  show ?case
  proof (cases "unify_may_recurse (CoreTy_Array elemTy1 dims1) ty2")
    case True
    then obtain elemTy2 dims2 where ty2_eq: "ty2 = CoreTy_Array elemTy2 dims2"
      by (cases ty2) auto
    with "7.prems" have dims_eq: "dims1 = dims2"
      and u_eq: "unify is_flex elemTy1 elemTy2 = Some subst"
      by (auto split: if_splits)
    from "7.IH"[OF ty2_eq dims_eq u_eq] show ?thesis .
  next
    case False
    with "7.prems" show ?thesis by (rule unify_base_dom_flex)
  qed
next
  case (8 is_flex n ty2)
  from "8.prems" show ?case by (rule unify_base_dom_flex) simp
next
  case (9 uu)
  \<comment> \<open>unify_list [] [] = Some fmempty: empty domain. \<close>
  then show ?case by simp
next
  case (10 uv ty tys)
  \<comment> \<open>unify_list [] (ty # tys) fails. \<close>
  then show ?case by simp
next
  case (11 uw ty tys)
  \<comment> \<open>unify_list (ty # tys) [] fails. \<close>
  then show ?case by simp
next
  case (12 is_flex ty1 tys1 ty2 tys2)
  \<comment> \<open>unify_list (ty1 # tys1) (ty2 # tys2): unify head, recurse on substituted tail,
      compose substitutions. Both head and tail substitutions have flex domain
      by their respective IHs; composition's domain is their union, hence flex. \<close>
  from "12.prems" obtain subst1 subst2 where
    head_eq: "unify is_flex ty1 ty2 = Some subst1" and
    tail_eq: "unify_list is_flex (map (apply_subst subst1) tys1)
                                  (map (apply_subst subst1) tys2) = Some subst2" and
    subst_eq: "subst = compose_subst subst2 subst1"
    by (auto split: option.splits)
  from "12.IH"(1)[OF head_eq] have head_flex: "\<forall>n. n |\<in>| fmdom subst1 \<longrightarrow> is_flex n" .
  from "12.IH"(2)[OF head_eq tail_eq] have tail_flex: "\<forall>n. n |\<in>| fmdom subst2 \<longrightarrow> is_flex n" .
  have dom_union: "fmdom (compose_subst subst2 subst1) = fmdom subst2 |\<union>| fmdom subst1"
    by (simp add: compose_subst_def)
  show ?case
    using subst_eq dom_union head_flex tail_flex by auto
next
  case (13 is_flex n l ty2)
  from "13.prems" show ?case by (rule unify_base_dom_flex) simp
qed

lemma unify_dom_flex:
  "unify is_flex ty1 ty2 = Some subst \<Longrightarrow> \<forall>n. n |\<in>| fmdom subst \<longrightarrow> is_flex n"
  by (rule unify_unify_list_dom_flex(1))


(* ========================================================================== *)
(* unify_list succeeds only on equal length lists                             *)
(* ========================================================================== *)

lemma unify_list_length:
  "unify_list is_flex tys1 tys2 = Some subst \<Longrightarrow> length tys1 = length tys2"
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
        "unify is_flex ty1 ty2 = Some s1" and
        rest: "unify_list is_flex (map (apply_subst s1) rest1) (map (apply_subst s1) rest2) = Some s2"
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

lemma unify_base_sound:
  assumes "unify is_flex ty1 ty2 = Some s" and "\<not> unify_may_recurse ty1 ty2"
  shows "apply_subst s ty1 = apply_subst s ty2"
  using assms
proof (cases rule: unify_base_casesE)
  case refl
  then show ?thesis by simp
next
  case (left v)
  have "apply_subst s (CoreTy_Var v) = ty2"
    by (simp only: left(4) apply_subst_singleton)
  moreover have "apply_subst s ty2 = ty2"
    by (simp only: left(4) apply_subst_singleton_no_occurs[OF left(3)])
  ultimately show ?thesis by (simp only: left(1))
next
  case (right v)
  have "apply_subst s (CoreTy_Var v) = ty1"
    by (simp only: right(4) apply_subst_singleton)
  moreover have "apply_subst s ty1 = ty1"
    by (simp only: right(4) apply_subst_singleton_no_occurs[OF right(3)])
  ultimately show ?thesis by (simp only: right(1))
qed

(* If unify succeeds, the substitution makes the types equal. *)
theorem unify_sound:
  "unify is_flex ty1 ty2 = Some subst \<Longrightarrow>
     apply_subst subst ty1 = apply_subst subst ty2"
and unify_list_sound:
  "unify_list is_flex tys1 tys2 = Some subst \<Longrightarrow>
      list_all (\<lambda>(t1, t2). apply_subst subst t1 = apply_subst subst t2) (zip tys1 tys2)"
proof (induction is_flex ty1 ty2 and is_flex tys1 tys2 arbitrary: subst and subst rule: unify_unify_list.induct)
  (* CoreTy_Datatype / ty2 *)
  case (1 is_flex name1 tyArgs1 ty2)
  show ?case
  proof (cases "unify_may_recurse (CoreTy_Datatype name1 tyArgs1) ty2")
    case True
    then obtain name2 tyArgs2 where ty2_eq: "ty2 = CoreTy_Datatype name2 tyArgs2"
      by (cases ty2) auto
    with "1.prems" have name_eq: "name1 = name2"
      and unify_args: "unify_list is_flex tyArgs1 tyArgs2 = Some subst"
      by (auto split: if_splits)
    from "1.IH"[OF ty2_eq name_eq unify_args]
    have "list_all (\<lambda>(t1, t2). apply_subst subst t1 = apply_subst subst t2)
                   (zip tyArgs1 tyArgs2)" .
    then have "map (apply_subst subst) tyArgs1 = map (apply_subst subst) tyArgs2"
      using unify_list_length[OF unify_args]
      by (simp add: list_all_length list_eq_iff_nth_eq)
    then show ?thesis using ty2_eq name_eq by simp
  next
    case False
    with "1.prems" show ?thesis by (rule unify_base_sound)
  qed
next
  (* CoreTy_Bool / ty2 *)
  case (2 is_flex ty2)
  from "2.prems" show ?case by (rule unify_base_sound) simp
next
  (* CoreTy_FiniteInt / ty2 *)
  case (3 is_flex sign bits ty2)
  from "3.prems" show ?case by (rule unify_base_sound) simp
next
  (* CoreTy_MathInt / ty2 *)
  case (4 is_flex ty2)
  from "4.prems" show ?case by (rule unify_base_sound) simp
next
  (* CoreTy_MathReal / ty2 *)
  case (5 is_flex ty2)
  from "5.prems" show ?case by (rule unify_base_sound) simp
next
  (* CoreTy_Record / ty2 *)
  case (6 is_flex flds1 ty2)
  show ?case
  proof (cases "unify_may_recurse (CoreTy_Record flds1) ty2")
    case True
    then obtain flds2 where ty2_eq: "ty2 = CoreTy_Record flds2"
      by (cases ty2) auto
    with "6.prems" have names_eq: "map fst flds1 = map fst flds2"
      and unify_tys: "unify_list is_flex (map snd flds1) (map snd flds2) = Some subst"
      by (auto split: if_splits)
    from "6.IH"[OF ty2_eq names_eq unify_tys]
    have "list_all (\<lambda>(t1, t2). apply_subst subst t1 = apply_subst subst t2)
                   (zip (map snd flds1) (map snd flds2))" .
    then have types_eq: "map (apply_subst subst) (map snd flds1) = map (apply_subst subst) (map snd flds2)"
      using unify_list_length[OF unify_tys]
      by (simp add: list_all_length list_eq_iff_nth_eq)
    \<comment> \<open>Now show that applying subst to both records gives equal results\<close>
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
    finally show ?thesis using ty2_eq by simp
  next
    case False
    with "6.prems" show ?thesis by (rule unify_base_sound)
  qed
next
  (* CoreTy_Array / ty2 *)
  case (7 is_flex elemTy1 dims1 ty2)
  show ?case
  proof (cases "unify_may_recurse (CoreTy_Array elemTy1 dims1) ty2")
    case True
    then obtain elemTy2 dims2 where ty2_eq: "ty2 = CoreTy_Array elemTy2 dims2"
      by (cases ty2) auto
    with "7.prems" have dims_eq: "dims1 = dims2"
      and unify_elem: "unify is_flex elemTy1 elemTy2 = Some subst"
      by (auto split: if_splits)
    from "7.IH"[OF ty2_eq dims_eq unify_elem]
    have "apply_subst subst elemTy1 = apply_subst subst elemTy2" .
    then show ?thesis using ty2_eq dims_eq by simp
  next
    case False
    with "7.prems" show ?thesis by (rule unify_base_sound)
  qed
next
  (* CoreTy_Var / ty2 *)
  case (8 is_flex n ty2)
  from "8.prems" show ?case by (rule unify_base_sound) simp
next
  (* unify_list [] [] *)
  case (9 is_flex)
  then show ?case by simp
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
  from "12.prems" obtain subst1 subst2 where
    unify_head: "unify is_flex ty1 ty2 = Some subst1" and
    unify_rest: "unify_list is_flex (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2) = Some subst2" and
    subst_compose: "subst = compose_subst subst2 subst1"
    by (auto split: option.splits)
  from "12.IH"(1)[OF unify_head]
  have head_eq: "apply_subst subst1 ty1 = apply_subst subst1 ty2" .
  from "12.IH"(2)[OF unify_head unify_rest]
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
next
  (* CoreTy_Extern / ty2 *)
  case (13 is_flex n l ty2)
  from "13.prems" show ?case by (rule unify_base_sound) simp
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
  assumes unifies: "apply_subst subst' (CoreTy_Var n) = apply_subst subst' ty"
      and no_occurs: "\<not> occurs n ty"
    shows "\<forall>ty'. apply_subst subst' ty' = apply_subst subst' (apply_subst (singleton_subst n ty) ty')"
proof (intro allI)
  fix ty'
  show "apply_subst subst' ty' = apply_subst subst' (apply_subst (singleton_subst n ty) ty')"
  proof (induction ty')
    case (CoreTy_Var m)
    show ?case
    proof (cases "n = m")
      case True
      then have "apply_subst (singleton_subst n ty) (CoreTy_Var m) = ty"
        by (simp add: singleton_subst_def)
      moreover have "apply_subst subst' (CoreTy_Var m) = apply_subst subst' ty"
        using unifies True by simp
      ultimately show ?thesis by simp
    next
      case False
      then show ?thesis by (simp add: singleton_subst_def)
    qed
  next
    case (CoreTy_Datatype name tyArgs)
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
  next
    case (CoreTy_Extern n' l')
    then show ?case by simp
  qed
qed

lemma unify_base_mgu:
  assumes "unify is_flex ty1 ty2 = Some s"
      and unifies: "apply_subst subst' ty1 = apply_subst subst' ty2"
      and "\<not> unify_may_recurse ty1 ty2"
  shows "apply_subst subst' ty = apply_subst subst' (apply_subst s ty)"
  using assms(1,3)
proof (cases rule: unify_base_casesE)
  case refl
  then show ?thesis by simp
next
  case (left v)
  have "apply_subst subst' (CoreTy_Var v) = apply_subst subst' ty2"
    using unifies left(1) by simp
  from unifier_factors_singleton[OF this left(3)] show ?thesis
    unfolding left(4) by blast
next
  case (right v)
  have "apply_subst subst' (CoreTy_Var v) = apply_subst subst' ty1"
    using unifies right(1) by simp
  from unifier_factors_singleton[OF this right(3)] show ?thesis
    unfolding right(4) by blast
qed

(* Main MGU theorem, proved by mutual induction *)
(* See also corollary below for a more standard "textbook" form of this *)
theorem unify_mgu:
  "unify is_flex ty1 ty2 = Some subst \<Longrightarrow>
     apply_subst subst' ty1 = apply_subst subst' ty2 \<Longrightarrow>
     apply_subst subst' ty = apply_subst subst' (apply_subst subst ty)"
  and unify_list_mgu:
  "unify_list is_flex tys1 tys2 = Some subst \<Longrightarrow>
     list_all (\<lambda>(t1, t2). apply_subst subst' t1 = apply_subst subst' t2) (zip tys1 tys2) \<Longrightarrow>
     apply_subst subst' ty = apply_subst subst' (apply_subst subst ty)"
proof (induction is_flex ty1 ty2 and is_flex tys1 tys2 arbitrary: subst subst' ty and subst subst' ty rule: unify_unify_list.induct)
  (* CoreTy_Datatype / ty2 *)
  case (1 is_flex name1 tyArgs1 ty2)
  show ?case
  proof (cases "unify_may_recurse (CoreTy_Datatype name1 tyArgs1) ty2")
    case True
    then obtain name2 tyArgs2 where ty2_eq: "ty2 = CoreTy_Datatype name2 tyArgs2"
      by (cases ty2) auto
    with "1.prems"(1) have name_eq: "name1 = name2"
      and unify_args: "unify_list is_flex tyArgs1 tyArgs2 = Some subst"
      by (auto split: if_splits)
    from "1.prems"(2) ty2_eq
    have "map (apply_subst subst') tyArgs1 = map (apply_subst subst') tyArgs2"
      by simp
    hence "list_all (\<lambda>(t1, t2). apply_subst subst' t1 = apply_subst subst' t2) (zip tyArgs1 tyArgs2)"
      using unify_list_length[OF unify_args] by (simp add: list_all_length list_eq_iff_nth_eq)
    from "1.IH"[OF ty2_eq name_eq unify_args this] show ?thesis .
  next
    case False
    with "1.prems" show ?thesis by (rule unify_base_mgu)
  qed
next
  (* CoreTy_Bool / ty2 *)
  case (2 is_flex ty2)
  from "2.prems" show ?case by (rule unify_base_mgu) simp
next
  (* CoreTy_FiniteInt / ty2 *)
  case (3 is_flex sign bits ty2)
  from "3.prems" show ?case by (rule unify_base_mgu) simp
next
  (* CoreTy_MathInt / ty2 *)
  case (4 is_flex ty2)
  from "4.prems" show ?case by (rule unify_base_mgu) simp
next
  (* CoreTy_MathReal / ty2 *)
  case (5 is_flex ty2)
  from "5.prems" show ?case by (rule unify_base_mgu) simp
next
  (* CoreTy_Record / ty2 *)
  case (6 is_flex flds1 ty2)
  show ?case
  proof (cases "unify_may_recurse (CoreTy_Record flds1) ty2")
    case True
    then obtain flds2 where ty2_eq: "ty2 = CoreTy_Record flds2"
      by (cases ty2) auto
    with "6.prems"(1) have names_eq: "map fst flds1 = map fst flds2"
      and unify_tys: "unify_list is_flex (map snd flds1) (map snd flds2) = Some subst"
      by (auto split: if_splits)
    from "6.prems"(2) ty2_eq
    have eq_flds: "map (\<lambda>(n,t). (n, apply_subst subst' t)) flds1 =
                   map (\<lambda>(n,t). (n, apply_subst subst' t)) flds2"
      by simp
    have "map snd (map (\<lambda>(n,t). (n, apply_subst subst' t)) flds1) =
          map snd (map (\<lambda>(n,t). (n, apply_subst subst' t)) flds2)"
      using eq_flds by simp
    hence "map (apply_subst subst') (map snd flds1) = map (apply_subst subst') (map snd flds2)"
      by (simp add: case_prod_beta comp_def)
    hence "list_all (\<lambda>(t1, t2). apply_subst subst' t1 = apply_subst subst' t2)
                    (zip (map snd flds1) (map snd flds2))"
      using unify_list_length[OF unify_tys] by (simp add: list_all_length list_eq_iff_nth_eq)
    from "6.IH"[OF ty2_eq names_eq unify_tys this] show ?thesis .
  next
    case False
    with "6.prems" show ?thesis by (rule unify_base_mgu)
  qed
next
  (* CoreTy_Array / ty2 *)
  case (7 is_flex elemTy1 dims1 ty2)
  show ?case
  proof (cases "unify_may_recurse (CoreTy_Array elemTy1 dims1) ty2")
    case True
    then obtain elemTy2 dims2 where ty2_eq: "ty2 = CoreTy_Array elemTy2 dims2"
      by (cases ty2) auto
    with "7.prems"(1) have dims_eq: "dims1 = dims2"
      and unify_elem: "unify is_flex elemTy1 elemTy2 = Some subst"
      by (auto split: if_splits)
    from "7.prems"(2) ty2_eq have "apply_subst subst' elemTy1 = apply_subst subst' elemTy2"
      by simp
    from "7.IH"[OF ty2_eq dims_eq unify_elem this] show ?thesis .
  next
    case False
    with "7.prems" show ?thesis by (rule unify_base_mgu)
  qed
next
  (* CoreTy_Var / ty2 *)
  case (8 is_flex n ty2)
  from "8.prems" show ?case by (rule unify_base_mgu) simp
next
  (* unify_list [] [] *)
  case (9 is_flex)
  then show ?case by simp
next
  (* unify_list [] (ty # tys) - impossible *)
  case (10 is_flex ty2 tys2)
  then show ?case by simp
next
  (* unify_list (ty # tys) [] - impossible *)
  case (11 is_flex ty1 tys1)
  then show ?case by simp
next
  (* unify_list (ty1 # tys1) (ty2 # tys2) *)
  case (12 is_flex ty1 rest1 ty2 rest2)
  from "12.prems"(1) obtain subst1 subst2 where
    unify_head: "unify is_flex ty1 ty2 = Some subst1" and
    unify_rest: "unify_list is_flex (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2) = Some subst2" and
    subst_compose: "subst = compose_subst subst2 subst1"
    by (auto split: option.splits)
  from "12.prems"(2) have head_unifies: "apply_subst subst' ty1 = apply_subst subst' ty2"
    and rest_unifies: "list_all (\<lambda>(t1, t2). apply_subst subst' t1 = apply_subst subst' t2) (zip rest1 rest2)"
    by simp_all
  (* From the head unification, subst' factors through subst1 *)
  from "12.IH"(1)[OF unify_head head_unifies]
  have factor1: "\<And>ty. apply_subst subst' ty = apply_subst subst' (apply_subst subst1 ty)" .
  (* Therefore rest_unifies also holds after applying subst1 *)
  have rest_unifies': "list_all (\<lambda>(t1, t2). apply_subst subst' t1 = apply_subst subst' t2)
                                (zip (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2))"
    using rest_unifies factor1[symmetric] by (simp add: list_all_length)
  (* From the rest unification, subst' factors through subst2 as well *)
  from "12.IH"(2)[OF unify_head unify_rest rest_unifies']
  have factor2: "\<And>ty. apply_subst subst' ty = apply_subst subst' (apply_subst subst2 ty)" .
  (* Combine: subst' factors through compose_subst subst2 subst1 *)
  have "apply_subst subst' ty = apply_subst subst' (apply_subst subst1 ty)"
    using factor1 by blast
  also have "... = apply_subst subst' (apply_subst subst2 (apply_subst subst1 ty))"
    using factor2 by simp
  also have "... = apply_subst subst' (apply_subst (compose_subst subst2 subst1) ty)"
    by (simp add: compose_subst_correct)
  finally show ?case using subst_compose by simp
next
  (* CoreTy_Extern / ty2 *)
  case (13 is_flex n l ty2)
  from "13.prems" show ?case by (rule unify_base_mgu) simp
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
  assumes "unify is_flex ty1 ty2 = Some \<sigma>"
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

(* If n occurs in a type other than CoreTy_Var n, it occurs in an immediate
   component of that type, which stays strictly smaller under any substitution. *)
lemma occurs_in_child:
  assumes occ: "occurs n ty" and ne: "ty \<noteq> CoreTy_Var n"
  obtains c where "occurs n c"
    and "\<And>\<sigma>. core_type_size (apply_subst \<sigma> c) < core_type_size (apply_subst \<sigma> ty)"
proof (cases ty)
  case (CoreTy_Datatype name args)
  with occ obtain arg where arg_in: "arg \<in> set args" and arg_occ: "occurs n arg"
    by (auto simp: occurs_def)
  have "core_type_size (apply_subst \<sigma> arg) < core_type_size (apply_subst \<sigma> ty)" for \<sigma>
  proof -
    have "core_type_size (apply_subst \<sigma> arg)
            \<le> sum_list (map core_type_size (map (apply_subst \<sigma>) args))"
      using arg_in by (intro member_le_sum_list) auto
    thus ?thesis using CoreTy_Datatype by simp
  qed
  with arg_occ show ?thesis by (rule that)
next
  case (CoreTy_Record flds)
  with occ obtain t where t_in: "t \<in> snd ` set flds" and t_occ: "occurs n t"
    by (auto simp: occurs_def)
  have "core_type_size (apply_subst \<sigma> t) < core_type_size (apply_subst \<sigma> ty)" for \<sigma>
  proof -
    have "core_type_size (apply_subst \<sigma> t)
            \<le> sum_list (map (core_type_size \<circ> snd)
                            (map (\<lambda>(nm, t). (nm, apply_subst \<sigma> t)) flds))"
      using t_in by (intro member_le_sum_list) force+
    thus ?thesis using CoreTy_Record by simp
  qed
  with t_occ show ?thesis by (rule that)
next
  case (CoreTy_Array elem dims)
  with occ have "occurs n elem" by (simp add: occurs_def)
  moreover have "core_type_size (apply_subst \<sigma> elem) < core_type_size (apply_subst \<sigma> ty)" for \<sigma>
    using CoreTy_Array by simp
  ultimately show ?thesis by (rule that)
qed (use occ ne in \<open>auto simp: occurs_def\<close>)

(* Hence if n occurs in ty, then apply_subst \<sigma> ty contains apply_subst \<sigma> (CoreTy_Var n)
   as a subterm, making the size of the former strictly larger (when ty \<noteq> CoreTy_Var n) *)
lemma occurs_implies_larger_size:
  assumes "occurs n ty"
      and "ty \<noteq> CoreTy_Var n"
    shows "core_type_size (apply_subst \<sigma> (CoreTy_Var n)) < core_type_size (apply_subst \<sigma> ty)"
  using assms
proof (induction ty rule: measure_induct_rule[where f=core_type_size])
  case (less ty)
  from less.prems obtain c where c_occ: "occurs n c"
    and c_size: "\<And>\<sigma>. core_type_size (apply_subst \<sigma> c) < core_type_size (apply_subst \<sigma> ty)"
    by (rule occurs_in_child) blast
  show ?case
  proof (cases "c = CoreTy_Var n")
    case True
    then show ?thesis using c_size[of \<sigma>] by simp
  next
    case False
    have "core_type_size c < core_type_size ty"
      using c_size[of fmempty] by simp
    from less.IH[OF this c_occ False]
    have "core_type_size (apply_subst \<sigma> (CoreTy_Var n)) < core_type_size (apply_subst \<sigma> c)" .
    from this c_size[of \<sigma>] show ?thesis by (rule less_trans)
  qed
qed

(* The occurs check prevents infinite types: if metavariable n occurs in ty
   (and ty is not just CoreTy_Var n), then no substitution can make
   CoreTy_Var n equal to ty. *)
lemma occurs_check_no_unifier:
  assumes "occurs n ty"
      and "ty \<noteq> CoreTy_Var n"
    shows "apply_subst \<sigma> (CoreTy_Var n) \<noteq> apply_subst \<sigma> ty"
proof
  assume "apply_subst \<sigma> (CoreTy_Var n) = apply_subst \<sigma> ty"
  hence "core_type_size (apply_subst \<sigma> (CoreTy_Var n)) = core_type_size (apply_subst \<sigma> ty)"
    by simp
  moreover from occurs_implies_larger_size[OF assms]
  have "core_type_size (apply_subst \<sigma> (CoreTy_Var n)) < core_type_size (apply_subst \<sigma> ty)" .
  ultimately show False by simp
qed

(* Helper: if \<sigma> unifies a non-Meta type with CoreTy_Var n, then n must be in fmdom \<sigma> *)
lemma unifier_binds_meta:
  assumes "apply_subst \<sigma> ty1 = apply_subst \<sigma> (CoreTy_Var n)"
      and "\<not> (\<exists>m. ty1 = CoreTy_Var m)"
    shows "n \<in> fset (fmdom \<sigma>)"
proof (rule ccontr)
  assume "n \<notin> fset (fmdom \<sigma>)"
  hence "fmlookup \<sigma> n = None" by (simp add: fmdom_notD)
  hence "apply_subst \<sigma> (CoreTy_Var n) = CoreTy_Var n" by simp
  with assms(1) have "apply_subst \<sigma> ty1 = CoreTy_Var n" by simp
  with assms(2) show False by (cases ty1; simp)
qed

(* Completeness of unification: if a unifier exists whose domain consists entirely of
   flexible variables, then unify will find one. *)
theorem unify_complete:
  "apply_subst \<sigma> ty1 = apply_subst \<sigma> ty2 \<Longrightarrow>
   fset (fmdom \<sigma>) \<subseteq> {n. is_flex n} \<Longrightarrow>
   \<exists>\<theta>. unify is_flex ty1 ty2 = Some \<theta>"
  and unify_list_complete:
  "list_all (\<lambda>(t1, t2). apply_subst \<sigma> t1 = apply_subst \<sigma> t2) (zip tys1 tys2) \<Longrightarrow>
   length tys1 = length tys2 \<Longrightarrow>
   fset (fmdom \<sigma>) \<subseteq> {n. is_flex n} \<Longrightarrow>
   \<exists>\<theta>. unify_list is_flex tys1 tys2 = Some \<theta>"
proof (induction is_flex ty1 ty2 and is_flex tys1 tys2 arbitrary: \<sigma> and \<sigma> rule: unify_unify_list.induct)
  (* CoreTy_Datatype / ty2 *)
  case (1 is_flex name1 tyArgs1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    from unifier_binds_meta[of \<sigma> "CoreTy_Datatype name1 tyArgs1" n] "1.prems" CoreTy_Var
    have "n \<in> fset (fmdom \<sigma>)" by auto
    with "1.prems"(2) have "is_flex n" by auto
    show ?thesis
    proof (cases "occurs n (CoreTy_Datatype name1 tyArgs1)")
      case True
      from occurs_check_no_unifier[OF True] "1.prems"(1) CoreTy_Var
      show ?thesis by (metis CoreType.distinct(13))
    next
      case False
      then show ?thesis using CoreTy_Var \<open>is_flex n\<close> by auto
    qed
  next
    case (CoreTy_Datatype name2 tyArgs2)
    from "1.prems"(1) CoreTy_Datatype have cond: "name1 = name2 \<and> length tyArgs1 = length tyArgs2"
      using map_eq_imp_length_eq by auto
    from "1.prems"(1) CoreTy_Datatype cond have
      "list_all (\<lambda>(t1, t2). apply_subst \<sigma> t1 = apply_subst \<sigma> t2) (zip tyArgs1 tyArgs2)"
      by (simp add: list_all_length list_eq_iff_nth_eq)
    from "1.IH"[OF CoreTy_Datatype _ this] cond "1.prems"(2) obtain \<theta> where "unify_list is_flex tyArgs1 tyArgs2 = Some \<theta>"
      by auto
    with cond CoreTy_Datatype show ?thesis by auto
  qed auto
next
  (* CoreTy_Bool / ty2 *)
  case (2 is_flex ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    from unifier_binds_meta[of \<sigma> CoreTy_Bool n] "2.prems" CoreTy_Var
    have "is_flex n" by auto
    have "\<not> occurs n CoreTy_Bool" by (simp add: occurs_def)
    then show ?thesis using CoreTy_Var \<open>is_flex n\<close> by auto
  qed auto
next
  (* CoreTy_FiniteInt / ty2 *)
  case (3 is_flex sign bits ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    from unifier_binds_meta[of \<sigma> "CoreTy_FiniteInt sign bits" n] "3.prems" CoreTy_Var
    have "is_flex n" by blast
    have "\<not> occurs n (CoreTy_FiniteInt sign bits)" by (simp add: occurs_def)
    then show ?thesis using CoreTy_Var \<open>is_flex n\<close> by auto
  qed auto
next
  (* CoreTy_MathInt / ty2 *)
  case (4 is_flex ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    from unifier_binds_meta[of \<sigma> CoreTy_MathInt n] "4.prems" CoreTy_Var
    have "is_flex n" by auto
    have "\<not> occurs n CoreTy_MathInt" by (simp add: occurs_def)
    then show ?thesis using CoreTy_Var \<open>is_flex n\<close> by auto
  qed auto
next
  (* CoreTy_MathReal / ty2 *)
  case (5 is_flex ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    from unifier_binds_meta[of \<sigma> CoreTy_MathReal n] "5.prems" CoreTy_Var
    have "is_flex n" by auto
    have "\<not> occurs n CoreTy_MathReal" by (simp add: occurs_def)
    then show ?thesis using CoreTy_Var \<open>is_flex n\<close> by auto
  qed auto
next
  (* CoreTy_Record / ty2 *)
  case (6 is_flex flds1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    from unifier_binds_meta[of \<sigma> "CoreTy_Record flds1" n] "6.prems" CoreTy_Var
    have "is_flex n" by auto
    show ?thesis
    proof (cases "occurs n (CoreTy_Record flds1)")
      case True
      from occurs_check_no_unifier[OF True] "6.prems"(1) CoreTy_Var
      show ?thesis by (metis CoreType.distinct(63))
    next
      case False
      then show ?thesis using CoreTy_Var \<open>is_flex n\<close> by auto
    qed
  next
    case (CoreTy_Record flds2)
    (* From hypothesis: apply_subst \<sigma> (Record flds1) = apply_subst \<sigma> (Record flds2) *)
    from "6.prems"(1) CoreTy_Record
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
    from "6.IH"[OF CoreTy_Record names_eq this len_eq "6.prems"(2)] obtain \<theta> where
      "unify_list is_flex (map snd flds1) (map snd flds2) = Some \<theta>" by auto
    with names_eq CoreTy_Record show ?thesis by auto
  qed auto
next
  (* CoreTy_Array / ty2 *)
  case (7 is_flex elemTy1 dims1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    from unifier_binds_meta[of \<sigma> "CoreTy_Array elemTy1 dims1" n] "7.prems" CoreTy_Var
    have "is_flex n" by auto
    show ?thesis
    proof (cases "occurs n (CoreTy_Array elemTy1 dims1)")
      case True
      from occurs_check_no_unifier[OF True] "7.prems"(1) CoreTy_Var
      show ?thesis by (metis CoreType.distinct(67))
    next
      case False
      then show ?thesis using CoreTy_Var \<open>is_flex n\<close> by auto
    qed
  next
    case (CoreTy_Array elemTy2 dims2)
    from "7.prems"(1) CoreTy_Array have dims_eq: "dims1 = dims2" by simp
    from "7.prems"(1) CoreTy_Array have "apply_subst \<sigma> elemTy1 = apply_subst \<sigma> elemTy2" by simp
    from "7.IH"[OF CoreTy_Array dims_eq this "7.prems"(2)] obtain \<theta> where "unify is_flex elemTy1 elemTy2 = Some \<theta>" by auto
    with dims_eq CoreTy_Array show ?thesis by auto
  qed auto
next
  (* CoreTy_Var / ty2 *)
  case (8 is_flex n ty2)
  show ?case
  proof (cases "is_flex n")
    case True
    (* n is flexible: old logic applies *)
    show ?thesis
    proof (cases "occurs n ty2 \<and> ty2 \<noteq> CoreTy_Var n")
      case True
      from occurs_check_no_unifier[of n ty2] True "8.prems"(1)
      show ?thesis by simp
    next
      case False
      then show ?thesis using \<open>is_flex n\<close> by auto
    qed
  next
    case flex_n_false: False
    (* n is rigid, so n \<notin> fmdom \<sigma> *)
    from flex_n_false "8.prems"(2) have "n \<notin> fset (fmdom \<sigma>)" by auto
    hence lookup_n: "fmlookup \<sigma> n = None" by (simp add: fmdom_notD)
    hence subst_n: "apply_subst \<sigma> (CoreTy_Var n) = CoreTy_Var n" by simp
    with "8.prems"(1) have ty2_eq: "apply_subst \<sigma> ty2 = CoreTy_Var n" by simp
    show ?thesis
    proof (cases ty2)
      case (CoreTy_Var m)
      show ?thesis
      proof (cases "m = n")
        case True
        (* ty2 = CoreTy_Var n, unify returns fmempty *)
        then show ?thesis using CoreTy_Var flex_n_false by auto
      next
        case neq: False
        (* m \<noteq> n, so \<sigma> maps m to CoreTy_Var n, meaning m \<in> fmdom \<sigma>, so is_flex m *)
        from ty2_eq CoreTy_Var have "apply_subst \<sigma> (CoreTy_Var m) = CoreTy_Var n" by simp
        with neq have "fmlookup \<sigma> m \<noteq> None" by (auto split: option.splits)
        hence "m \<in> fset (fmdom \<sigma>)" by (meson fmdom_notD)
        with "8.prems"(2) have "is_flex m" by auto
        then show ?thesis using CoreTy_Var flex_n_false neq by auto
      qed
      (* For all non-Meta ty2: apply_subst \<sigma> ty2 preserves the constructor, so it can't equal CoreTy_Var n *)
    qed (use ty2_eq in simp_all)
  qed
next
  (* unify_list [] [] *)
  case (9 is_flex)
  then show ?case by simp
next
  (* unify_list [] (ty # tys) - impossible due to length constraint *)
  case (10 is_flex ty tys)
  then show ?case by simp
next
  (* unify_list (ty # tys) [] - impossible due to length constraint *)
  case (11 is_flex ty tys)
  then show ?case by simp
next
  (* unify_list (ty1 # tys1) (ty2 # tys2) *)
  case (12 is_flex ty1 tys1 ty2 tys2)
  (* Extract hypotheses *)
  from "12.prems" have head_unifies: "apply_subst \<sigma> ty1 = apply_subst \<sigma> ty2"
    and rest_unifies: "list_all (\<lambda>(t1, t2). apply_subst \<sigma> t1 = apply_subst \<sigma> t2) (zip tys1 tys2)"
    and len_eq: "length tys1 = length tys2"
    and flex_dom: "fset (fmdom \<sigma>) \<subseteq> {n. is_flex n}"
    by simp_all
  (* Use IH to unify heads *)
  from "12.IH"(1)[OF head_unifies flex_dom] obtain \<theta>1 where unify_head: "unify is_flex ty1 ty2 = Some \<theta>1" by auto
  (* The MGU property tells us that \<sigma> factors through \<theta>1 *)
  from unify_mgu[OF unify_head head_unifies]
  have mgu: "\<And>ty. apply_subst \<sigma> ty = apply_subst \<sigma> (apply_subst \<theta>1 ty)" .
  (* Therefore the rest still unifies after applying \<theta>1 *)
  have rest_unifies': "list_all (\<lambda>(t1, t2). apply_subst \<sigma> t1 = apply_subst \<sigma> t2)
                                (zip (map (apply_subst \<theta>1) tys1) (map (apply_subst \<theta>1) tys2))"
    using rest_unifies mgu[symmetric] by (simp add: list_all_length)
  have len_eq': "length (map (apply_subst \<theta>1) tys1) = length (map (apply_subst \<theta>1) tys2)"
    using len_eq by simp
  (* Use IH for unify_list on the substituted lists — \<sigma> is still the witness, domain unchanged *)
  from "12.IH"(2)[OF unify_head rest_unifies' len_eq' flex_dom]
  obtain \<theta>2 where unify_rest: "unify_list is_flex (map (apply_subst \<theta>1) tys1) (map (apply_subst \<theta>1) tys2) = Some \<theta>2"
    by auto
  (* Combine results *)
  have "unify_list is_flex (ty1 # tys1) (ty2 # tys2) = Some (compose_subst \<theta>2 \<theta>1)"
    using unify_head unify_rest by simp
  then show ?case by blast
next
  (* CoreTy_Extern / ty2 *)
  case (13 is_flex n l ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var m)
    from unifier_binds_meta[of \<sigma> "CoreTy_Extern n l" m] "13.prems" CoreTy_Var
    have "is_flex m" by blast
    have "\<not> occurs m (CoreTy_Extern n l)" by (simp add: occurs_def)
    then show ?thesis using CoreTy_Var \<open>is_flex m\<close> by auto
  qed auto
qed


end
