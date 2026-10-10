theory ContractNames
  imports "../util/NatToString"
begin

(* A function's contract (FI_Requires, FI_Ensures) cannot refer to the
   parameters by their declared names, because FunInfo carries no parameter
   names. Instead it uses positional names:
     - arg@@i is the i-th parameter (by value or by reference, as declared);
     - old@@i is the value the i-th parameter had on entry to the function
       (postconditions only);
     - return is the return value (postconditions only).
   None of these can be written in Babylon source.

   These names are used both by the typechecker (ModuleBodyEnv.thy,
   CoreContractTypecheck.thy) and by the interpreter (CoreInterp.thy), so they
   live in a theory of their own, low in the import graph. *)

definition contract_arg_names :: "nat \<Rightarrow> string list" where
  "contract_arg_names n = map (\<lambda>i. ''arg@@'' @ nat_to_string i) [0..<n]"

definition contract_old_names :: "nat \<Rightarrow> string list" where
  "contract_old_names n = map (\<lambda>i. ''old@@'' @ nat_to_string i) [0..<n]"

(* The names in scope in a postcondition, in the order of post_funinfo's
   parameters (ModuleBodyEnv.thy). *)
definition contract_post_names :: "nat \<Rightarrow> string list" where
  "contract_post_names n = contract_arg_names n @ contract_old_names n @ [''return'']"

(* Note: nat_to_string.simps must be kept out of the simp set in the following
   proofs, since it unfolds forever on a variable argument. *)

lemma length_contract_arg_names [simp]: "length (contract_arg_names n) = n"
  by (simp add: contract_arg_names_def del: nat_to_string.simps)

lemma length_contract_old_names [simp]: "length (contract_old_names n) = n"
  by (simp add: contract_old_names_def del: nat_to_string.simps)

lemma length_contract_post_names [simp]: "length (contract_post_names n) = n + n + 1"
  by (simp add: contract_post_names_def)

lemma distinct_contract_arg_names: "distinct (contract_arg_names n)"
  unfolding contract_arg_names_def distinct_map
  by (auto intro!: inj_onI dest: nat_to_string_injective simp del: nat_to_string.simps)

lemma distinct_contract_old_names: "distinct (contract_old_names n)"
  unfolding contract_old_names_def distinct_map
  by (auto intro!: inj_onI dest: nat_to_string_injective simp del: nat_to_string.simps)

lemma distinct_contract_post_names: "distinct (contract_post_names n)"
  using distinct_contract_arg_names[of n] distinct_contract_old_names[of n]
  unfolding contract_post_names_def
  by (auto simp: contract_arg_names_def contract_old_names_def simp del: nat_to_string.simps)

end
