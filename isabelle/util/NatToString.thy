theory NatToString
  imports Main
begin

(* Convert a nat to a string in decimal notation *)
fun nat_to_string :: "nat \<Rightarrow> string" where
  "nat_to_string n = (if n < 10 then [char_of (48 + n)]
                      else nat_to_string (n div 10) @ [char_of (48 + n mod 10)])"

(* Generate synthetic field names "0", "1", "2", ... for tuple types *)
definition tuple_field_names :: "nat \<Rightarrow> string list" where
  "tuple_field_names n = map nat_to_string [0..<n]"


(* nat_to_string always produces a non-empty string *)
lemma nat_to_string_nonempty: "nat_to_string n \<noteq> []"
  by (induction n rule: nat_to_string.induct) auto

(* The last character of nat_to_string encodes n mod 10 *)
lemma nat_to_string_last: "last (nat_to_string n) = char_of (48 + n mod 10)"
proof (induction n rule: nat_to_string.induct)
  case (1 n)
  show ?case
  proof (cases "n < 10")
    case True
    hence "n mod 10 = n" by simp
    thus ?thesis using True by simp
  next
    case False
    thus ?thesis using nat_to_string_nonempty by simp
  qed
qed

(* The butlast of nat_to_string for n >= 10 is nat_to_string (n div 10) *)
lemma nat_to_string_butlast:
  assumes "\<not> n < 10"
  shows "butlast (nat_to_string n) = nat_to_string (n div 10)"
  using assms nat_to_string_nonempty by (simp add: butlast_append)

(* char_of is injective on the range 0..9 offset by 48 *)
lemma char_of_digit_injective:
  assumes "a < 10" "b < 10" "char_of (48 + a) = char_of (48 + (b::nat))"
  shows "a = b"
  using assms by auto

(* nat_to_string is injective *)
lemma nat_to_string_injective: "nat_to_string m = nat_to_string n \<Longrightarrow> m = n"
proof (induction m arbitrary: n rule: less_induct)
  case (less m)
  show ?case
  proof (cases "m < 10")
    case m_small: True
    show ?thesis
    proof (cases "n < 10")
      case True
      from less.prems m_small True have "char_of (48 + m) = char_of (48 + n)"
        by simp
      thus ?thesis using char_of_digit_injective m_small True by blast
    next
      case False
      \<comment> \<open>m < 10 gives length 1, n >= 10 gives length >= 2 - contradiction\<close>
      from m_small have "length (nat_to_string m) = 1" by simp
      moreover from False nat_to_string_nonempty
      have "length (nat_to_string n) \<ge> 2"
        by simp
      ultimately show ?thesis using less.prems by simp
    qed
  next
    case m_big: False
    show ?thesis
    proof (cases "n < 10")
      case True
      from True have "length (nat_to_string n) = 1" by simp
      moreover from m_big nat_to_string_nonempty
      have "length (nat_to_string m) \<ge> 2"
        by simp
      ultimately show ?thesis using less.prems by simp
    next
      case n_big: False
      \<comment> \<open>Both >= 10: last characters match, so m mod 10 = n mod 10;
         butlast matches, so nat_to_string (m div 10) = nat_to_string (n div 10),
         and by IH, m div 10 = n div 10. Together: m = n.\<close>
      from less.prems have last_eq: "last (nat_to_string m) = last (nat_to_string n)" by simp
      hence mod_eq: "m mod 10 = n mod 10"
        using nat_to_string_last char_of_digit_injective[of "m mod 10" "n mod 10"]
        by simp
      from less.prems have "butlast (nat_to_string m) = butlast (nat_to_string n)" by simp
      hence "nat_to_string (m div 10) = nat_to_string (n div 10)"
        using nat_to_string_butlast m_big n_big by simp
      hence "m div 10 = n div 10"
        using less.IH m_big by simp
      thus ?thesis using mod_eq by (metis div_mod_decomp)
    qed
  qed
qed


lemma length_tuple_field_names [simp]: "length (tuple_field_names n) = n"
  by (simp add: tuple_field_names_def)

lemma distinct_tuple_field_names: "distinct (tuple_field_names n)"
proof -
  have "inj_on nat_to_string (set [0..<n])"
    using inj_on_def nat_to_string_injective by blast
  thus ?thesis unfolding tuple_field_names_def
    by (simp add: distinct_map)
qed

end
