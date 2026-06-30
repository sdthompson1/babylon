theory DistinctCheck
  imports Main "HOL-Library.Char_ord" "HOL-Library.List_Lexorder"
begin

(* Efficient duplicate checking.

   The standard `distinct` operation is O(n^2). These functions detect duplicate
   names in O(n log n) by sorting first and then scanning for adjacent equal
   elements. *)

(* Helper: Scan a sorted list for the first adjacent-equal element. *)
fun first_adjacent_dup :: "string list \<Rightarrow> string option" where
  "first_adjacent_dup [] = None"
| "first_adjacent_dup [_] = None"
| "first_adjacent_dup (x # y # rest) =
    (if x = y then Some x else first_adjacent_dup (y # rest))"

(* Check for duplicate "names" in a list. Takes a list of items and a function that
   extracts the name from each item. Returns `Some name` if a name appears more than
   once, or None if all names are unique. *)
definition first_duplicate_name :: "('a \<Rightarrow> string) \<Rightarrow> 'a list \<Rightarrow> string option" where
  "first_duplicate_name getName items = first_adjacent_dup (sort (map getName items))"

(* If first_adjacent_dup returns None, on sorted input, then the input was distinct *)
lemma first_adjacent_dup_None_implies_distinct:
  assumes "first_adjacent_dup xs = None"
    and "sorted xs"
  shows "distinct xs"
  using assms
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases xs)
    case Nil thus ?thesis by simp
  next
    case (Cons b ys)
    with Cons.prems(1) have a_neq_b: "a \<noteq> b" by auto
    have rec_eq: "first_adjacent_dup (a # b # ys) = first_adjacent_dup (b # ys)"
      by (simp add: a_neq_b)
    thus ?thesis
      using Cons.IH Cons.prems(1,2) \<open>xs = b # ys\<close> a_neq_b by force
  qed
qed

(* Converse: If the input is distinct, then first_adjacent_dup returns None *)
lemma first_adjacent_dup_None_if_distinct:
  assumes "distinct xs"
  shows "first_adjacent_dup xs = None"
  using assms
proof (induction xs rule: first_adjacent_dup.induct)
  case (3 x y rest)
  then show ?case by auto
qed simp_all

(* If first_duplicate_name returns None, then the input was distinct *)
lemma first_duplicate_name_None_implies_distinct:
  assumes "first_duplicate_name getName items = None"
  shows "distinct (map getName items)"
proof -
  let ?sorted = "sort (map getName items)"
  from assms have "first_adjacent_dup ?sorted = None"
    unfolding first_duplicate_name_def by simp
  moreover have "sorted ?sorted" by simp
  ultimately have "distinct ?sorted"
    by (rule first_adjacent_dup_None_implies_distinct)
  thus ?thesis by simp
qed

(* Converse: if the input is distinct, then first_duplicate_name returns None *)
lemma first_duplicate_name_None_if_distinct:
  assumes "distinct (map getName items)"
  shows "first_duplicate_name getName items = None"
proof -
  have "distinct (sort (map getName items))" using assms by simp
  thus ?thesis
    unfolding first_duplicate_name_def
    by (rule first_adjacent_dup_None_if_distinct)
qed

end
