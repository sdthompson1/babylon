theory DistinctCheck
  imports Main "HOL-Library.Char_ord" "HOL-Library.List_Lexorder"
begin

(* Efficient duplicate checking.

   The standard `distinct` operation is O(n^2). These functions detect duplicate
   names in O(n log n) by sorting first and then scanning for adjacent equal
   elements.

   `first_duplicate_name` takes a key function and a list of items; it returns
   `Some name` if some pair of items share a name, or `None` if all keys are
   distinct. *)

(* Scan a sorted list for the first adjacent-equal element *)
fun first_adjacent_dup :: "string list \<Rightarrow> string option" where
  "first_adjacent_dup [] = None"
| "first_adjacent_dup [_] = None"
| "first_adjacent_dup (x # y # rest) =
    (if x = y then Some x else first_adjacent_dup (y # rest))"

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

(* Check for duplicate names in a list. Returns Some name if `name` appears
   more than once (as a key), or None if all keys are distinct. *)
definition first_duplicate_name :: "('a \<Rightarrow> string) \<Rightarrow> 'a list \<Rightarrow> string option" where
  "first_duplicate_name getName items = first_adjacent_dup (sort (map getName items))"

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

end
