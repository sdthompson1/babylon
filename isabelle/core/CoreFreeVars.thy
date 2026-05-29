theory CoreFreeVars
  imports CoreSyntax "HOL-Library.FSet"
begin

(* Free variables of a core term *)
fun core_term_free_vars :: "CoreTerm \<Rightarrow> string fset" where
  "core_term_free_vars (CoreTm_LitBool _) = {||}"
| "core_term_free_vars (CoreTm_LitInt _) = {||}"
| "core_term_free_vars (CoreTm_LitArray _ tms) = ffUnion (fset_of_list (map core_term_free_vars tms))"
| "core_term_free_vars (CoreTm_Var name) = {|name|}"
| "core_term_free_vars (CoreTm_Cast _ tm) = core_term_free_vars tm"
| "core_term_free_vars (CoreTm_Unop _ tm) = core_term_free_vars tm"
| "core_term_free_vars (CoreTm_Binop _ lhs rhs) =
    core_term_free_vars lhs |\<union>| core_term_free_vars rhs"
| "core_term_free_vars (CoreTm_Let var rhs body) =
    core_term_free_vars rhs |\<union>| (core_term_free_vars body |-| {|var|})"
| "core_term_free_vars (CoreTm_Quantifier _ var _ body) =
    core_term_free_vars body |-| {|var|}"
| "core_term_free_vars (CoreTm_FunctionCall _ _ tmArgs) =
    ffUnion (fset_of_list (map core_term_free_vars tmArgs))"
| "core_term_free_vars (CoreTm_VariantCtor _ _ payload) = core_term_free_vars payload"
| "core_term_free_vars (CoreTm_Record flds) =
    ffUnion (fset_of_list (map (core_term_free_vars \<circ> snd) flds))"
| "core_term_free_vars (CoreTm_RecordProj tm _) = core_term_free_vars tm"
| "core_term_free_vars (CoreTm_VariantProj tm _) = core_term_free_vars tm"
| "core_term_free_vars (CoreTm_ArrayProj arr idxs) =
    core_term_free_vars arr |\<union>| ffUnion (fset_of_list (map core_term_free_vars idxs))"
| "core_term_free_vars (CoreTm_Match scrut arms) =
    core_term_free_vars scrut |\<union>| ffUnion (fset_of_list (map (core_term_free_vars \<circ> snd) arms))"
| "core_term_free_vars (CoreTm_Sizeof tm) = core_term_free_vars tm"
| "core_term_free_vars (CoreTm_Allocated tm) = core_term_free_vars tm"
| "core_term_free_vars (CoreTm_Old tm) = core_term_free_vars tm"
| "core_term_free_vars (CoreTm_Default _) = {||}"

(* Membership in ffUnion (f |`| fset_of_list xs) reduces to a list quantifier
   over the underlying list. Useful for case-splits on the recursive shapes
   used by core_term_free_vars (CoreTm_LitArray, CoreTm_FunctionCall,
   CoreTm_Record, CoreTm_ArrayProj, CoreTm_Match). The simp set normalises
   fset_of_list (map f xs) to f |`| fset_of_list xs, so we state the lemma
   in the normalised form. *)
lemma fmember_ffUnion_fimage_fset_of_list_iff:
  "x |\<in>| ffUnion (f |`| fset_of_list xs) \<longleftrightarrow> (\<exists>y \<in> set xs. x |\<in>| f y)"
  by (induction xs) auto

end
