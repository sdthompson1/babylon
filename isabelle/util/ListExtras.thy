theory ListExtras
  imports Main "HOL-Library.AList"
begin

(* Small general-purpose facts about lists that the HOL library does not
   provide directly. *)


(* ========================================================================== *)
(* those *)
(* ========================================================================== *)

lemma those_eq_Some:
  "those xs = Some ys \<longleftrightarrow> list_all2 (\<lambda>x y. x = Some y) xs ys"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then show ?case by (cases x) (auto simp: list_all2_Cons1)
qed

(* Unpacking those by index. *)
lemma those_some_nth:
  assumes "those xs = Some ys"
  shows "length ys = length xs \<and> (\<forall>i < length xs. xs ! i = Some (ys ! i))"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  from Cons.prems obtain y ys' where
    x_eq: "x = Some y" and rest: "those xs = Some ys'" and ys_eq: "ys = y # ys'"
    by (auto split: option.splits)
  from Cons.IH[OF rest] show ?case
    by (auto simp: x_eq ys_eq nth_Cons split: nat.splits)
qed

(* If those succeeds, every element of the list is defined. *)
lemma those_Some_all_Some:
  "those xs = Some ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<exists>y. x = Some y"
  by (induction xs arbitrary: ys) (auto split: option.splits)

lemma those_map_Some_all:
  "those (map f xs) = Some ys \<Longrightarrow> \<forall>x \<in> set xs. f x \<noteq> None"
  by (induction xs arbitrary: ys) (auto split: option.splits)

(* If those succeeds on the f-images of xs, and g agrees with f wherever f
   succeeds, then those succeeds on the g-images with the same result. *)
lemma those_map_mono:
  assumes "those (map f xs) = Some ys"
      and "\<And>x y. x \<in> set xs \<Longrightarrow> f x = Some y \<Longrightarrow> g x = Some y"
  shows "those (map g xs) = Some ys"
  using assms by (induction xs arbitrary: ys) (auto split: option.splits)


(* ========================================================================== *)
(* list_all2 *)
(* ========================================================================== *)

(* list_all2 against a list of pairs, with the pair split in the relation. *)

lemma list_all2_case_prod_conv_all_nth:
  "list_all2 (\<lambda>x (a, b). P x a b) xs ys \<longleftrightarrow>
     length xs = length ys
     \<and> (\<forall>i < length xs. P (xs ! i) (fst (ys ! i)) (snd (ys ! i)))"
  by (simp add: list_all2_conv_all_nth case_prod_unfold)

lemma list_all2_case_prod_nthD:
  assumes "list_all2 (\<lambda>x (a, b). P x a b) xs ys" and "i < length xs"
  shows "P (xs ! i) (fst (ys ! i)) (snd (ys ! i))"
  using assms unfolding list_all2_conv_all_nth case_prod_unfold by blast

lemma list_all2_case_prod_mono:
  assumes "list_all2 (\<lambda>x (a, b). P x a b) xs ys"
    and "\<And>x a b. x \<in> set xs \<Longrightarrow> P x a b \<Longrightarrow> Q x a b"
  shows "list_all2 (\<lambda>x (a, b). Q x a b) xs ys"
  using assms unfolding list_all2_conv_all_nth case_prod_unfold by (metis nth_mem)

(* If flds and fieldTypes are related by list_all2 with name equality,
   then map_of lookups agree and predicates transfer. *)
lemma list_all2_map_of_transfer:
  assumes "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t) flds fieldTypes"
    and "map_of flds k = Some v"
  shows "\<exists>t. map_of fieldTypes k = Some t \<and> P v t"
using assms proof (induction flds arbitrary: fieldTypes)
  case Nil
  then show ?case by simp
next
  case (Cons entry flds)
  obtain k1 v1 where entry_eq: "entry = (k1, v1)" by (cases entry) auto
  from Cons.prems(1) obtain ft fieldTypes' where
    ft_eq: "fieldTypes = ft # fieldTypes'" and
    head_rel: "(\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t) entry ft" and
    tail_rel: "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t) flds fieldTypes'"
    by (cases fieldTypes) auto
  obtain k2 t2 where ft_pair: "ft = (k2, t2)" by (cases ft) auto
  from head_rel entry_eq ft_pair have k_eq: "k1 = k2" and pred: "P v1 t2" by auto
  show ?case
  proof (cases "k1 = k")
    case True
    with entry_eq Cons.prems(2) have "v = v1" by simp
    with True k_eq ft_eq ft_pair pred show ?thesis by simp
  next
    case False
    with entry_eq Cons.prems(2) have "map_of flds k = Some v" by simp
    from Cons.IH[OF tail_rel this] obtain t where
      "map_of fieldTypes' k = Some t" and "P v t" by auto
    with False k_eq ft_eq ft_pair show ?thesis by simp
  qed
qed

(* Reverse direction of list_all2_map_of_transfer: given a key present in the
   second list (fieldTypes), conclude it is also present in the first list (flds). *)
lemma list_all2_map_of_transfer_rev:
  assumes "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t) flds fieldTypes"
    and "map_of fieldTypes k = Some t"
  shows "\<exists>v. map_of flds k = Some v \<and> P v t"
using assms proof (induction flds arbitrary: fieldTypes)
  case Nil
  then show ?case by simp
next
  case (Cons entry flds)
  obtain k1 v1 where entry_eq: "entry = (k1, v1)" by (cases entry) auto
  from Cons.prems(1) obtain ft fieldTypes' where
    ft_eq: "fieldTypes = ft # fieldTypes'" and
    head_rel: "(\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t) entry ft" and
    tail_rel: "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t) flds fieldTypes'"
    by (cases fieldTypes) auto
  obtain k2 t2 where ft_pair: "ft = (k2, t2)" by (cases ft) auto
  from head_rel entry_eq ft_pair have k_eq: "k1 = k2" and pred: "P v1 t2" by auto
  show ?case
  proof (cases "k2 = k")
    case True
    with ft_eq ft_pair Cons.prems(2) have "t = t2" by simp
    with True k_eq entry_eq pred show ?thesis by simp
  next
    case False
    with ft_eq ft_pair Cons.prems(2) have "map_of fieldTypes' k = Some t" by simp
    from Cons.IH[OF tail_rel this] obtain v where
      "map_of flds k = Some v" and "P v t" by auto
    with False k_eq entry_eq show ?thesis by simp
  qed
qed

(* AList.update preserves list_all2 when the replacement value satisfies the
   same predicate as the original value at that key. *)
lemma alist_update_preserves_list_all2:
  assumes all2: "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t) flds fieldTypes"
    and lookup: "map_of flds field = Some oldVal"
    and new_pred: "\<And>t. map_of fieldTypes field = Some t \<Longrightarrow> P newVal t"
  shows "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t)
           (AList.update field newVal flds) fieldTypes"
using all2 lookup new_pred proof (induction flds arbitrary: fieldTypes)
  case Nil
  then show ?case by simp
next
  case (Cons entry flds)
  obtain k v where entry_eq: "entry = (k, v)" by (cases entry) auto
  from Cons.prems(1) obtain ft fieldTypes' where
    ft_eq: "fieldTypes = ft # fieldTypes'" and
    head_rel: "(\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t) entry ft" and
    tail_rel: "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t) flds fieldTypes'"
    by (cases fieldTypes) auto
  obtain kft tft where ft_pair: "ft = (kft, tft)" by (cases ft) auto
  from head_rel entry_eq ft_pair have k_eq: "k = kft" and old_P: "P v tft" by auto
  show ?case
  proof (cases "k = field")
    case True
    then have "AList.update field newVal (entry # flds) = (field, newVal) # flds"
      using entry_eq by simp
    moreover from True k_eq ft_pair have "map_of fieldTypes field = Some tft"
      using ft_eq by simp
    hence "P newVal tft" using Cons.prems(3) by simp
    ultimately show ?thesis using ft_eq ft_pair k_eq True tail_rel by force
  next
    case False
    then have "AList.update field newVal (entry # flds) =
               entry # AList.update field newVal flds"
      using entry_eq by simp
    moreover from False have lookup_tail: "map_of flds field = Some oldVal"
      using Cons.prems(2) entry_eq by simp
    have new_pred_tail: "\<And>t. map_of fieldTypes' field = Some t \<Longrightarrow> P newVal t"
      using Cons.prems(3) ft_eq False k_eq entry_eq ft_pair by simp
    from Cons.IH[OF tail_rel lookup_tail new_pred_tail] have
      "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t)
         (AList.update field newVal flds) fieldTypes'" .
    ultimately show ?thesis using ft_eq head_rel by simp
  qed
qed

end
