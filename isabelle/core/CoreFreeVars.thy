theory CoreFreeVars
  imports CoreSyntax
begin

(* Free variables of a core term *)
fun core_term_free_vars :: "CoreTerm \<Rightarrow> string set" where
  "core_term_free_vars (CoreTm_LitBool _) = {}"
| "core_term_free_vars (CoreTm_LitInt _) = {}"
| "core_term_free_vars (CoreTm_LitArray tms) = \<Union>(set (map core_term_free_vars tms))"
| "core_term_free_vars (CoreTm_Var name) = {name}"
| "core_term_free_vars (CoreTm_Cast _ tm) = core_term_free_vars tm"
| "core_term_free_vars (CoreTm_Unop _ tm) = core_term_free_vars tm"
| "core_term_free_vars (CoreTm_Binop _ lhs rhs) =
    core_term_free_vars lhs \<union> core_term_free_vars rhs"
| "core_term_free_vars (CoreTm_Let var rhs body) =
    core_term_free_vars rhs \<union> (core_term_free_vars body - {var})"
| "core_term_free_vars (CoreTm_Quantifier _ var _ body) =
    core_term_free_vars body - {var}"
| "core_term_free_vars (CoreTm_FunctionCall _ _ tmArgs) =
    \<Union>(set (map core_term_free_vars tmArgs))"
| "core_term_free_vars (CoreTm_VariantCtor _ _ payload) = core_term_free_vars payload"
| "core_term_free_vars (CoreTm_Record flds) =
    \<Union>(set (map (core_term_free_vars \<circ> snd) flds))"
| "core_term_free_vars (CoreTm_RecordProj tm _) = core_term_free_vars tm"
| "core_term_free_vars (CoreTm_VariantProj tm _) = core_term_free_vars tm"
| "core_term_free_vars (CoreTm_ArrayProj arr idxs) =
    core_term_free_vars arr \<union> \<Union>(set (map core_term_free_vars idxs))"
| "core_term_free_vars (CoreTm_Match scrut arms) =
    core_term_free_vars scrut \<union> \<Union>(set (map (core_term_free_vars \<circ> snd) arms))"
| "core_term_free_vars (CoreTm_Sizeof tm) = core_term_free_vars tm"
| "core_term_free_vars (CoreTm_Allocated tm) = core_term_free_vars tm"
| "core_term_free_vars (CoreTm_Old tm) = core_term_free_vars tm"

end
