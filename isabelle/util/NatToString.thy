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

end
