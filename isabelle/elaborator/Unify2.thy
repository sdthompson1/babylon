theory Unify2
  imports Unify
begin

(* Correctness properties for our unification algorithm *)


(* ========================================================================== *)
(* Only "flexible" variables are unified                                      *)
(* ========================================================================== *)

(* The unifier only ever binds metavariables for which is_flex returns True.
   Every binding in the algorithm is gated by an `if is_flex n` check. *)
lemma unify_unify_list_dom_flex:
  "unify is_flex ty1 ty2 = Some subst \<Longrightarrow> \<forall>n. n |\<in>| fmdom subst \<longrightarrow> is_flex n"
  "unify_list is_flex tys1 tys2 = Some subst \<Longrightarrow> \<forall>n. n |\<in>| fmdom subst \<longrightarrow> is_flex n"
proof (induction is_flex ty1 ty2 and is_flex tys1 tys2 arbitrary: subst and subst
       rule: unify_unify_list.induct)
  case (1 is_flex name1 tyArgs1 ty2)
  \<comment> \<open>Datatype on left: only succeeds when ty2 is also a Datatype with the same name
      (recursing into unify_list) or a flex meta n (binding n). \<close>
  from "1.prems" show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    with "1.prems" have flex_n: "is_flex n" and
      subst_eq: "subst = singleton_subst n (CoreTy_Datatype name1 tyArgs1)"
      by (auto split: if_splits)
    show ?thesis using flex_n subst_eq by (simp add: singleton_subst_def)
  next
    case (CoreTy_Datatype name2 tyArgs2)
    with "1.prems" have name_eq: "name1 = name2" and
      ul_eq: "unify_list is_flex tyArgs1 tyArgs2 = Some subst"
      by (auto split: if_splits)
    from "1.IH"[OF CoreTy_Datatype name_eq ul_eq]
    show ?thesis .
  qed (use "1.prems" in auto)
next
  case (2 is_flex ty2)
  \<comment> \<open>Bool on left: only succeeds when ty2 is Bool (empty subst) or a flex meta. \<close>
  from "2.prems" show ?case
    by (cases ty2) (auto split: if_splits simp: singleton_subst_def)
next
  case (3 is_flex sign bits ty2)
  \<comment> \<open>FiniteInt on left. \<close>
  from "3.prems" show ?case
    by (cases ty2) (auto split: if_splits simp: singleton_subst_def)
next
  case (4 is_flex ty2)
  \<comment> \<open>MathInt on left. \<close>
  from "4.prems" show ?case
    by (cases ty2) (auto split: if_splits simp: singleton_subst_def)
next
  case (5 is_flex ty2)
  \<comment> \<open>MathReal on left. \<close>
  from "5.prems" show ?case
    by (cases ty2) (auto split: if_splits simp: singleton_subst_def)
next
  case (6 is_flex flds1 ty2)
  \<comment> \<open>Record on left: meta-bind or recurse via unify_list on field types. \<close>
  from "6.prems" show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    with "6.prems" have flex_n: "is_flex n" and
      subst_eq: "subst = singleton_subst n (CoreTy_Record flds1)"
      by (auto split: if_splits)
    show ?thesis using flex_n subst_eq by (simp add: singleton_subst_def)
  next
    case (CoreTy_Record flds2)
    with "6.prems" have fst_eq: "map fst flds1 = map fst flds2" and
      ul_eq: "unify_list is_flex (map snd flds1) (map snd flds2) = Some subst"
      by (auto split: if_splits)
    from "6.IH"[OF CoreTy_Record fst_eq ul_eq]
    show ?thesis .
  qed (use "6.prems" in auto)
next
  case (7 is_flex elemTy1 dims1 ty2)
  \<comment> \<open>Array on left: meta-bind or recurse via unify on the element type. \<close>
  from "7.prems" show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    with "7.prems" have flex_n: "is_flex n" and
      subst_eq: "subst = singleton_subst n (CoreTy_Array elemTy1 dims1)"
      by (auto split: if_splits)
    show ?thesis using flex_n subst_eq by (simp add: singleton_subst_def)
  next
    case (CoreTy_Array elemTy2 dims2)
    with "7.prems" have dims_eq: "dims1 = dims2" and
      u_eq: "unify is_flex elemTy1 elemTy2 = Some subst"
      by (auto split: if_splits)
    from "7.IH"[OF CoreTy_Array dims_eq u_eq]
    show ?thesis .
  qed (use "7.prems" in auto)
next
  case (8 is_flex n ty2)
  \<comment> \<open>Meta on left. If is_flex n, we may bind n. Otherwise we may bind a flex meta
      m on the right. Either way, every binding requires the bound variable to
      be flex. \<close>
  from "8.prems" show ?case
  proof (cases "is_flex n")
    case True
    \<comment> \<open>n is flex: result is empty (if ty2 = Meta n), None (if occurs), or
        singleton_subst n ty2 (otherwise). \<close>
    show ?thesis
    proof (cases "ty2 = CoreTy_Var n")
      case True
      with \<open>is_flex n\<close> "8.prems" have "subst = fmempty" by simp
      thus ?thesis by simp
    next
      case False
      with \<open>is_flex n\<close> "8.prems" have
        not_occurs: "\<not> occurs n ty2" and
        subst_eq: "subst = singleton_subst n ty2"
        by (auto split: if_splits)
      show ?thesis using \<open>is_flex n\<close> subst_eq by (simp add: singleton_subst_def)
    qed
  next
    case False
    \<comment> \<open>n is rigid: only succeeds if ty2 is Meta m where m = n (empty subst) or
        m is flex (binding m). \<close>
    from \<open>\<not> is_flex n\<close> "8.prems" obtain m where
      ty2_eq: "ty2 = CoreTy_Var m"
      by (cases ty2) (auto split: if_splits)
    show ?thesis
    proof (cases "m = n")
      case True
      with ty2_eq \<open>\<not> is_flex n\<close> "8.prems" have "subst = fmempty" by simp
      thus ?thesis by simp
    next
      case False
      with ty2_eq \<open>\<not> is_flex n\<close> "8.prems" have
        flex_m: "is_flex m" and
        subst_eq: "subst = singleton_subst m (CoreTy_Var n)"
        by (auto split: if_splits)
      show ?thesis using flex_m subst_eq by (simp add: singleton_subst_def)
    qed
  qed
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
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    (* unify returns singleton_subst n (CoreTy_Datatype name1 tyArgs1) when occurs check passes *)
    from 1 CoreTy_Var have no_occurs: "\<not> occurs n (CoreTy_Datatype name1 tyArgs1)"
      by (auto split: if_splits)
    from 1 CoreTy_Var no_occurs have subst_eq: "subst = singleton_subst n (CoreTy_Datatype name1 tyArgs1)"
      by (simp split: if_splits)
    have "apply_subst subst (CoreTy_Datatype name1 tyArgs1) = CoreTy_Datatype name1 tyArgs1"
      using no_occurs subst_eq
      using apply_subst_singleton_no_occurs by blast
    also have "... = apply_subst subst (CoreTy_Var n)"
      using subst_eq apply_subst_singleton by auto
    finally show ?thesis using CoreTy_Var by simp
  next
    case (CoreTy_Datatype name2 tyArgs2)
    show ?thesis
    proof (cases "name1 = name2")
      case True
      with 1 CoreTy_Datatype have "unify_list is_flex tyArgs1 tyArgs2 = Some subst" by simp
      with 1 True CoreTy_Datatype have "list_all (\<lambda>(t1, t2). apply_subst subst t1 = apply_subst subst t2)
                                  (zip tyArgs1 tyArgs2)" by simp
      then have "map (apply_subst subst) tyArgs1 = map (apply_subst subst) tyArgs2"
        using unify_list_length[of is_flex tyArgs1 tyArgs2 subst] \<open>unify_list is_flex tyArgs1 tyArgs2 = Some subst\<close>
        by (simp add: list_all_length list_eq_iff_nth_eq)
      then show ?thesis using True CoreTy_Datatype by simp
    next
      case False
      then show ?thesis using 1 CoreTy_Datatype by simp
    qed
  qed auto
next
  (* CoreTy_Bool / ty2 *)
  case (2 is_flex ty2)
  then show ?case by (cases ty2; auto simp: apply_subst_singleton singleton_subst_def split: if_splits)
next
  (* CoreTy_FiniteInt / ty2 *)
  case (3 is_flex sign bits ty2)
  then show ?case by (cases ty2; auto simp: apply_subst_singleton singleton_subst_def split: if_splits)
next
  (* CoreTy_MathInt / ty2 *)
  case (4 is_flex ty2)
  then show ?case by (cases ty2; auto simp: apply_subst_singleton singleton_subst_def split: if_splits)
next
  (* CoreTy_MathReal / ty2 *)
  case (5 is_flex ty2)
  then show ?case by (cases ty2; auto simp: apply_subst_singleton singleton_subst_def split: if_splits)
next
  (* CoreTy_Record / ty2 *)
  case (6 is_flex flds1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    from 6 CoreTy_Var have no_occurs: "\<not> occurs n (CoreTy_Record flds1)"
      by (auto split: if_splits)
    from 6 CoreTy_Var no_occurs have subst_eq: "subst = singleton_subst n (CoreTy_Record flds1)"
      by (simp split: if_splits)
    have "apply_subst subst (CoreTy_Record flds1) = CoreTy_Record flds1"
      using no_occurs subst_eq apply_subst_singleton_no_occurs by blast
    also have "... = apply_subst subst (CoreTy_Var n)"
      using apply_subst_singleton subst_eq by auto
    finally show ?thesis using CoreTy_Var by simp
  next
    case (CoreTy_Record flds2)
    (* Field names must match for unification to succeed *)
    from 6 CoreTy_Record have names_eq: "map fst flds1 = map fst flds2"
      by (auto split: if_splits)
    from 6 CoreTy_Record names_eq have "unify_list is_flex (map snd flds1) (map snd flds2) = Some subst"
      by simp
    with 6 CoreTy_Record names_eq
    have "list_all (\<lambda>(t1, t2). apply_subst subst t1 = apply_subst subst t2)
                   (zip (map snd flds1) (map snd flds2))" by simp
    then have types_eq: "map (apply_subst subst) (map snd flds1) = map (apply_subst subst) (map snd flds2)"
      using unify_list_length[of is_flex "map snd flds1" "map snd flds2" subst]
            \<open>unify_list is_flex (map snd flds1) (map snd flds2) = Some subst\<close>
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
  case (7 is_flex elemTy1 dims1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    from 7 CoreTy_Var have no_occurs: "\<not> occurs n (CoreTy_Array elemTy1 dims1)"
      by (auto split: if_splits)
    from 7 CoreTy_Var no_occurs have subst_eq: "subst = singleton_subst n (CoreTy_Array elemTy1 dims1)"
      by (simp split: if_splits)
    have "apply_subst subst (CoreTy_Array elemTy1 dims1) = CoreTy_Array elemTy1 dims1"
      using apply_subst_singleton_no_occurs no_occurs subst_eq by blast
    also have "... = apply_subst subst (CoreTy_Var n)"
      using apply_subst_singleton subst_eq by auto
    finally show ?thesis using CoreTy_Var by simp
  next
    case (CoreTy_Array elemTy2 dims2)
    show ?thesis
    proof (cases "dims1 = dims2")
      case True
      with 7 CoreTy_Array have "unify is_flex elemTy1 elemTy2 = Some subst" by simp
      with 7 True CoreTy_Array have "apply_subst subst elemTy1 = apply_subst subst elemTy2" by simp
      then show ?thesis using True CoreTy_Array by simp
    next
      case False
      then show ?thesis using 7 CoreTy_Array by simp
    qed
  qed auto
next
  (* CoreTy_Var / ty2 *)
  case (8 is_flex n ty2)
  then show ?case
  proof (cases "is_flex n")
    case True
    (* n is flexible: old logic applies *)
    show ?thesis
    proof (cases "occurs n ty2 \<and> ty2 \<noteq> CoreTy_Var n")
      case True
      then show ?thesis using 8 \<open>is_flex n\<close> by simp
    next
      case False
      show ?thesis
      proof (cases "ty2 = CoreTy_Var n")
        case True
        then show ?thesis using 8 \<open>is_flex n\<close> by simp
      next
        case neq: False
        with False have no_occurs: "\<not> occurs n ty2" by simp
        from 8 \<open>is_flex n\<close> False neq have subst_eq: "subst = singleton_subst n ty2" by simp
        have "apply_subst subst (CoreTy_Var n) = ty2"
          using apply_subst_singleton subst_eq by blast
        also have "... = apply_subst subst ty2"
          by (simp add: apply_subst_singleton_no_occurs no_occurs subst_eq)
        finally show ?thesis by simp
      qed
    qed
  next
    case flex_n_false: False
    (* n is rigid: can only match itself or be bound by a flexible var on the right *)
    show ?thesis
    proof (cases ty2)
      case (CoreTy_Var m)
      show ?thesis
      proof (cases "m = n")
        case True
        then show ?thesis using 8 flex_n_false CoreTy_Var by simp
      next
        case neq: False
        show ?thesis
        proof (cases "is_flex m")
          case True
          (* m is flexible, binds to CoreTy_Var n *)
          from 8 flex_n_false CoreTy_Var neq True
          have subst_eq: "subst = singleton_subst m (CoreTy_Var n)" by simp
          have "apply_subst subst (CoreTy_Var n) = CoreTy_Var n"
            using subst_eq neq by (simp add: singleton_subst_def)
          also have "... = apply_subst subst (CoreTy_Var m)"
            using apply_subst_singleton subst_eq by auto
          finally show ?thesis using CoreTy_Var by simp
        next
          case False
          then show ?thesis using 8 flex_n_false CoreTy_Var neq by simp
        qed
      qed
    next
      case (CoreTy_Datatype name args)
      then show ?thesis using 8 flex_n_false by simp
    next
      case CoreTy_Bool
      then show ?thesis using 8 flex_n_false by simp
    next
      case (CoreTy_FiniteInt sign bits)
      then show ?thesis using 8 flex_n_false by simp
    next
      case CoreTy_MathInt
      then show ?thesis using 8 flex_n_false by simp
    next
      case CoreTy_MathReal
      then show ?thesis using 8 flex_n_false by simp
    next
      case (CoreTy_Record flds)
      then show ?thesis using 8 flex_n_false by simp
    next
      case (CoreTy_Array elem dims)
      then show ?thesis using 8 flex_n_false by simp
    qed
  qed
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
  from 12(3) obtain subst1 subst2 where
    unify_head: "unify is_flex ty1 ty2 = Some subst1" and
    unify_rest: "unify_list is_flex (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2) = Some subst2" and
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
  qed
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
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    then have subst_eq: "subst = singleton_subst n (CoreTy_Datatype name1 tyArgs1)"
          and no_occurs: "\<not> occurs n (CoreTy_Datatype name1 tyArgs1)"
      using 1(2) by (auto split: if_splits)
    have "apply_subst subst' (CoreTy_Datatype name1 tyArgs1) = apply_subst subst' (CoreTy_Var n)"
      using 1(3) CoreTy_Var by simp
    from unifier_factors_singleton[OF this[symmetric] no_occurs] subst_eq
    show ?thesis by blast
  next
    case (CoreTy_Datatype name2 tyArgs2)
    show ?thesis
    proof (cases "name1 = name2")
      case True
      with 1(2) CoreTy_Datatype have unify_args: "unify_list is_flex tyArgs1 tyArgs2 = Some subst" by simp
      from 1(3) CoreTy_Datatype True have "map (apply_subst subst') tyArgs1 = map (apply_subst subst') tyArgs2"
        by simp
      hence "list_all (\<lambda>(t1, t2). apply_subst subst' t1 = apply_subst subst' t2) (zip tyArgs1 tyArgs2)"
        using unify_list_length[OF unify_args] by (simp add: list_all_length list_eq_iff_nth_eq)
      from 1(1)[OF CoreTy_Datatype True unify_args this] show ?thesis .
    next
      case False then show ?thesis using 1(2) CoreTy_Datatype by auto
    qed
  qed auto
next
  (* CoreTy_Bool / ty2 *)
  case (2 is_flex ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    then have subst_eq: "subst = singleton_subst n CoreTy_Bool"
      using 2(1) by (simp split: if_splits)
    have no_occurs: "\<not> occurs n CoreTy_Bool" by (simp add: occurs_def)
    have "apply_subst subst' CoreTy_Bool = apply_subst subst' (CoreTy_Var n)"
      using 2(2) CoreTy_Var by simp
    from unifier_factors_singleton[OF this[symmetric] no_occurs] subst_eq
    show ?thesis by blast
  qed auto
next
  (* CoreTy_FiniteInt / ty2 *)
  case (3 is_flex sign bits ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    then have subst_eq: "subst = singleton_subst n (CoreTy_FiniteInt sign bits)"
      using 3(1) by (simp split: if_splits)
    have no_occurs: "\<not> occurs n (CoreTy_FiniteInt sign bits)" by (simp add: occurs_def)
    have "apply_subst subst' (CoreTy_FiniteInt sign bits) = apply_subst subst' (CoreTy_Var n)"
      using 3(2) CoreTy_Var by blast
    from unifier_factors_singleton[OF this[symmetric] no_occurs] subst_eq
    show ?thesis by blast
  qed (auto split: if_splits)
next
  (* CoreTy_MathInt / ty2 *)
  case (4 is_flex ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    then have subst_eq: "subst = singleton_subst n CoreTy_MathInt"
      using 4(1) by (simp split: if_splits)
    have no_occurs: "\<not> occurs n CoreTy_MathInt" by (simp add: occurs_def)
    have "apply_subst subst' CoreTy_MathInt = apply_subst subst' (CoreTy_Var n)"
      using 4(2) CoreTy_Var by simp
    from unifier_factors_singleton[OF this[symmetric] no_occurs] subst_eq
    show ?thesis by blast
  qed auto
next
  (* CoreTy_MathReal / ty2 *)
  case (5 is_flex ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    then have subst_eq: "subst = singleton_subst n CoreTy_MathReal"
      using 5(1) by (simp split: if_splits)
    have no_occurs: "\<not> occurs n CoreTy_MathReal" by (simp add: occurs_def)
    have "apply_subst subst' CoreTy_MathReal = apply_subst subst' (CoreTy_Var n)"
      using 5(2) CoreTy_Var by simp
    from unifier_factors_singleton[OF this[symmetric] no_occurs] subst_eq
    show ?thesis by blast
  qed auto
next
  (* CoreTy_Record / ty2 *)
  case (6 is_flex flds1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    then have subst_eq: "subst = singleton_subst n (CoreTy_Record flds1)"
          and no_occurs: "\<not> occurs n (CoreTy_Record flds1)"
      using 6(2) by (auto split: if_splits)
    have "apply_subst subst' (CoreTy_Record flds1) = apply_subst subst' (CoreTy_Var n)"
      using 6(3) CoreTy_Var by simp
    from unifier_factors_singleton[OF this[symmetric] no_occurs] subst_eq
    show ?thesis by blast
  next
    case (CoreTy_Record flds2)
    (* Field names must match for unification to succeed *)
    from 6(2) CoreTy_Record have names_eq: "map fst flds1 = map fst flds2"
      by (auto split: if_splits)
    with 6(2) CoreTy_Record have unify_tys: "unify_list is_flex (map snd flds1) (map snd flds2) = Some subst"
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
  case (7 is_flex elemTy1 dims1 ty2)
  then show ?case
  proof (cases ty2)
    case (CoreTy_Var n)
    then have subst_eq: "subst = singleton_subst n (CoreTy_Array elemTy1 dims1)"
          and no_occurs: "\<not> occurs n (CoreTy_Array elemTy1 dims1)"
      using 7(2) by (auto split: if_splits)
    have "apply_subst subst' (CoreTy_Array elemTy1 dims1) = apply_subst subst' (CoreTy_Var n)"
      using 7(3) CoreTy_Var by simp
    from unifier_factors_singleton[OF this[symmetric] no_occurs] subst_eq
    show ?thesis by blast
  next
    case (CoreTy_Array elemTy2 dims2)
    show ?thesis
    proof (cases "dims1 = dims2")
      case True
      with 7(2) CoreTy_Array have unify_elem: "unify is_flex elemTy1 elemTy2 = Some subst" by simp
      from 7(3) CoreTy_Array have "apply_subst subst' elemTy1 = apply_subst subst' elemTy2" by simp
      from 7(1)[OF CoreTy_Array True unify_elem this] show ?thesis .
    next
      case False then show ?thesis using 7(2) CoreTy_Array by simp
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
        then show ?thesis by simp
      next
        case neq: False
        with False have no_occurs: "\<not> occurs n ty2" by simp
        have subst_eq: "subst = singleton_subst n ty2"
          using 8(1) \<open>is_flex n\<close> False neq by simp
        from 8(2) have unifies': "apply_subst subst' (CoreTy_Var n) = apply_subst subst' ty2" by simp
        show ?thesis using unifier_factors_singleton[OF unifies' no_occurs] subst_eq by blast
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
        then show ?thesis by simp
      next
        case neq: False
        show ?thesis
        proof (cases "is_flex m")
          case True
          (* m is flexible, binds to CoreTy_Var n *)
          from 8(1) flex_n_false CoreTy_Var neq True
          have subst_eq: "subst = singleton_subst m (CoreTy_Var n)" by simp
          from 8(2) CoreTy_Var have unifies': "apply_subst subst' (CoreTy_Var m) = apply_subst subst' (CoreTy_Var n)"
            by simp
          have no_occurs: "\<not> occurs m (CoreTy_Var n)"
            using neq by (simp add: occurs_def)
          show ?thesis using unifier_factors_singleton[OF unifies' no_occurs] subst_eq by blast
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
  from 12(3) obtain subst1 subst2 where
    unify_head: "unify is_flex ty1 ty2 = Some subst1" and
    unify_rest: "unify_list is_flex (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2) = Some subst2" and
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

(* Helper: if n occurs in ty, then apply_subst \<sigma> ty contains apply_subst \<sigma> (CoreTy_Var n)
   as a subterm, making the size of the former strictly larger (when ty \<noteq> CoreTy_Var n) *)
lemma occurs_implies_larger_size:
  assumes "occurs n ty"
      and "ty \<noteq> CoreTy_Var n"
    shows "core_type_size (apply_subst \<sigma> (CoreTy_Var n)) < core_type_size (apply_subst \<sigma> ty)"
  using assms
proof (induction ty rule: measure_induct_rule[where f=core_type_size])
  case (less ty)
  show ?case
  proof (cases ty)
    case (CoreTy_Var m)
    (* ty = CoreTy_Var m, and n occurs in it, so n = m, but ty \<noteq> CoreTy_Var n - contradiction *)
    from less.prems CoreTy_Var have "n = m" by (simp add: occurs_def)
    hence "ty = CoreTy_Var n" using CoreTy_Var by simp
    with less.prems show ?thesis by simp
  next
    case (CoreTy_Datatype name tyargs)
    from less.prems CoreTy_Datatype have "n \<in> type_tyvars (CoreTy_Datatype name tyargs)"
      by (simp add: occurs_def)
    hence "\<exists>arg \<in> set tyargs. n \<in> type_tyvars arg" by auto
    then obtain arg where "arg \<in> set tyargs" and "n \<in> type_tyvars arg" by auto
    hence "occurs n arg" by (simp add: occurs_def)
    show ?thesis
    proof (cases "arg = CoreTy_Var n")
      case True
      have "core_type_size (apply_subst \<sigma> arg) \<le> sum_list (map (core_type_size \<circ> apply_subst \<sigma>) tyargs)"
        using \<open>arg \<in> set tyargs\<close> by (simp add: member_le_sum_list)
      hence "core_type_size (apply_subst \<sigma> (CoreTy_Var n)) < 1 + sum_list (map (core_type_size \<circ> apply_subst \<sigma>) tyargs)"
        using True by simp
      thus ?thesis using CoreTy_Datatype by simp
    next
      case False
      have "core_type_size arg \<le> sum_list (map core_type_size tyargs)"
        using \<open>arg \<in> set tyargs\<close> by (simp add: member_le_sum_list)
      hence "core_type_size arg < core_type_size ty"
        using CoreTy_Datatype by simp
      from less.IH[OF this \<open>occurs n arg\<close> False]
      have "core_type_size (apply_subst \<sigma> (CoreTy_Var n)) < core_type_size (apply_subst \<sigma> arg)" .
      also have "core_type_size (apply_subst \<sigma> arg) \<le> sum_list (map (core_type_size \<circ> apply_subst \<sigma>) tyargs)"
        using \<open>arg \<in> set tyargs\<close> by (simp add: member_le_sum_list)
      also have "... < 1 + sum_list (map (core_type_size \<circ> apply_subst \<sigma>) tyargs)" by simp
      finally show ?thesis using CoreTy_Datatype by simp
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
    from less.prems CoreTy_Record have "n \<in> type_tyvars (CoreTy_Record flds)"
      by (simp add: occurs_def)
    hence "\<exists>t \<in> set (map snd flds). n \<in> type_tyvars t" by (auto simp: comp_def)
    then obtain t where t_in: "t \<in> set (map snd flds)" and "n \<in> type_tyvars t" by auto
    hence "occurs n t" by (simp add: occurs_def)
    (* Helper: rewrite sum_list for apply_subst composition *)
    have sum_eq: "sum_list (map (core_type_size \<circ> apply_subst \<sigma>) (map snd flds)) =
                  sum_list (map (\<lambda>t. core_type_size (apply_subst \<sigma> t)) (map snd flds))"
      by (simp add: comp_def)
    show ?thesis
    proof (cases "t = CoreTy_Var n")
      case True
      have "core_type_size (apply_subst \<sigma> t) \<le> sum_list (map (\<lambda>t. core_type_size (apply_subst \<sigma> t)) (map snd flds))"
        using canonically_ordered_monoid_add_class.member_le_sum_list t_in by force
      hence "core_type_size (apply_subst \<sigma> (CoreTy_Var n)) < 1 + sum_list (map (core_type_size \<circ> apply_subst \<sigma>) (map snd flds))"
        using True sum_eq by simp
      thus ?thesis using CoreTy_Record by (simp add: comp_def case_prod_beta)
    next
      case False
      have "core_type_size t \<le> sum_list (map core_type_size (map snd flds))"
        using canonically_ordered_monoid_add_class.member_le_sum_list t_in by force
      hence "core_type_size t < core_type_size ty"
        using CoreTy_Record by (simp add: comp_def)
      from less.IH[OF this \<open>occurs n t\<close> False]
      have "core_type_size (apply_subst \<sigma> (CoreTy_Var n)) < core_type_size (apply_subst \<sigma> t)" .
      also have "core_type_size (apply_subst \<sigma> t) \<le> sum_list (map (\<lambda>t. core_type_size (apply_subst \<sigma> t)) (map snd flds))"
        using canonically_ordered_monoid_add_class.member_le_sum_list t_in by force
      also have "... = sum_list (map (core_type_size \<circ> apply_subst \<sigma>) (map snd flds))"
        by (simp add: comp_def)
      also have "... < 1 + sum_list (map (core_type_size \<circ> apply_subst \<sigma>) (map snd flds))" by simp
      finally show ?thesis using CoreTy_Record by (simp add: comp_def case_prod_beta)
    qed
  next
    case (CoreTy_Array elem dims)
    from less.prems CoreTy_Array have "n \<in> type_tyvars elem" by (simp add: occurs_def)
    hence "occurs n elem" by (simp add: occurs_def)
    show ?thesis
    proof (cases "elem = CoreTy_Var n")
      case True
      have "core_type_size (apply_subst \<sigma> elem) < 1 + core_type_size (apply_subst \<sigma> elem)"
        by simp
      thus ?thesis using True CoreTy_Array by simp
    next
      case False
      have "core_type_size elem < core_type_size ty"
        using CoreTy_Array by simp
      from less.IH[OF this \<open>occurs n elem\<close> False]
      have "core_type_size (apply_subst \<sigma> (CoreTy_Var n)) < core_type_size (apply_subst \<sigma> elem)" .
      also have "... < 1 + core_type_size (apply_subst \<sigma> elem)" by simp
      finally show ?thesis using CoreTy_Array by simp
    qed
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
      show ?thesis
        by (metis CoreType.distinct(13))
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
      show ?thesis
        by (metis CoreType.distinct(53))
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
      show ?thesis
        by (metis CoreType.distinct(55))
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
    next
      (* For all non-Meta ty2: apply_subst \<sigma> ty2 preserves the constructor, so it can't equal CoreTy_Var n *)
      case (CoreTy_Datatype name args)
      with ty2_eq show ?thesis by simp
    next
      case CoreTy_Bool
      with ty2_eq show ?thesis by simp
    next
      case (CoreTy_FiniteInt sign bits)
      with ty2_eq show ?thesis by simp
    next
      case CoreTy_MathInt
      with ty2_eq show ?thesis by simp
    next
      case CoreTy_MathReal
      with ty2_eq show ?thesis by simp
    next
      case (CoreTy_Record flds)
      with ty2_eq show ?thesis by simp
    next
      case (CoreTy_Array elem dims)
      with ty2_eq show ?thesis by simp
    qed
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
  (* Use IH for unify_list on the substituted lists — \<sigma> is still the witness, domain unchanged *)
  from "12.IH"(2)[OF unify_head rest_unifies' len_eq' flex_dom]
  obtain \<theta>2 where unify_rest: "unify_list is_flex (map (apply_subst \<theta>1) tys1) (map (apply_subst \<theta>1) tys2) = Some \<theta>2"
    by auto
  (* Combine results *)
  have "unify_list is_flex (ty1 # tys1) (ty2 # tys2) = Some (compose_subst \<theta>2 \<theta>1)"
    using unify_head unify_rest by simp
  then show ?case by blast
qed


end
