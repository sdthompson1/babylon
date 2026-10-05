theory TrivialDecreases
  imports "../core/CoreSyntax"
begin

(* The decreases-term of an erased While loop. *)
abbreviation (input) trivial_decreases :: CoreTerm where
  "trivial_decreases \<equiv> CoreTm_LitBool False"

end
