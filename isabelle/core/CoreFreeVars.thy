theory CoreFreeVars
  imports CoreSyntax "HOL-Library.FSet"
begin

(* ========================================================================== *)
(* Type variables of a type                                                   *)
(* ========================================================================== *)

(* Type variables in a type *)
fun type_tyvars :: "CoreType \<Rightarrow> nat set" where
  "type_tyvars (CoreTy_Datatype _ tyargs) = \<Union>(set (map type_tyvars tyargs))"
| "type_tyvars CoreTy_Bool = {}"
| "type_tyvars (CoreTy_FiniteInt _ _) = {}"
| "type_tyvars CoreTy_MathInt = {}"
| "type_tyvars CoreTy_MathReal = {}"
| "type_tyvars (CoreTy_Record flds) = \<Union>(set (map (type_tyvars \<circ> snd) flds))"
| "type_tyvars (CoreTy_Array elemTy dims) = type_tyvars elemTy"
| "type_tyvars (CoreTy_Var n) = {n}"

(* Collect all type variables in a type as a list (executable) *)
fun type_tyvars_list :: "CoreType \<Rightarrow> nat list" where
  "type_tyvars_list (CoreTy_Datatype _ args) = concat (map type_tyvars_list args)"
| "type_tyvars_list CoreTy_Bool = []"
| "type_tyvars_list (CoreTy_FiniteInt _ _) = []"
| "type_tyvars_list CoreTy_MathInt = []"
| "type_tyvars_list CoreTy_MathReal = []"
| "type_tyvars_list (CoreTy_Record flds) = concat (map (type_tyvars_list \<circ> snd) flds)"
| "type_tyvars_list (CoreTy_Array elemTy _) = type_tyvars_list elemTy"
| "type_tyvars_list (CoreTy_Var n) = [n]"

(* Collect all type variables in a list of types *)
definition list_tyvars :: "CoreType list \<Rightarrow> nat set" where
  "list_tyvars tys = \<Union>(set (map type_tyvars tys))"

(* Check if type variable n occurs in type ty *)
definition occurs :: "nat \<Rightarrow> CoreType \<Rightarrow> bool" where
  "occurs n ty = (n \<in> type_tyvars ty)"

(* Type variables in a type are finite *)
lemma finite_type_tyvars: "finite (type_tyvars ty)"
  by (induct ty) auto

(* Type variables in a list of types are finite *)
lemma finite_list_tyvars: "finite (list_tyvars tys)"
  using list_tyvars_def finite_type_tyvars by auto

(* type_tyvars_list collects the same set as type_tyvars *)
lemma set_type_tyvars_list: "set (type_tyvars_list ty) = type_tyvars ty"
  by (induct ty) auto


(* ========================================================================== *)
(* Free (term) variables of a core term                                       *)
(* ========================================================================== *)

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


(* ========================================================================== *)
(* Free type variables of a core term                                         *)
(* ========================================================================== *)

(* Type variables appearing in the types syntactically embedded in a term.
   Only six constructors carry an embedded type (the ones on which
   core_term_type runs is_well_kinded / is_runtime_type); the rest just
   recurse into subterms. *)
fun core_term_free_tyvars :: "CoreTerm \<Rightarrow> nat set" where
  "core_term_free_tyvars (CoreTm_LitBool _) = {}"
| "core_term_free_tyvars (CoreTm_LitInt _) = {}"
| "core_term_free_tyvars (CoreTm_LitArray elemTy tms) =
    type_tyvars elemTy \<union> \<Union>(set (map core_term_free_tyvars tms))"
| "core_term_free_tyvars (CoreTm_Var _) = {}"
| "core_term_free_tyvars (CoreTm_Cast targetTy tm) =
    type_tyvars targetTy \<union> core_term_free_tyvars tm"
| "core_term_free_tyvars (CoreTm_Unop _ tm) = core_term_free_tyvars tm"
| "core_term_free_tyvars (CoreTm_Binop _ lhs rhs) =
    core_term_free_tyvars lhs \<union> core_term_free_tyvars rhs"
| "core_term_free_tyvars (CoreTm_Let _ rhs body) =
    core_term_free_tyvars rhs \<union> core_term_free_tyvars body"
| "core_term_free_tyvars (CoreTm_Quantifier _ _ varTy body) =
    type_tyvars varTy \<union> core_term_free_tyvars body"
| "core_term_free_tyvars (CoreTm_FunctionCall _ tyArgs tmArgs) =
    \<Union>(set (map type_tyvars tyArgs)) \<union> \<Union>(set (map core_term_free_tyvars tmArgs))"
| "core_term_free_tyvars (CoreTm_VariantCtor _ tyArgs payload) =
    \<Union>(set (map type_tyvars tyArgs)) \<union> core_term_free_tyvars payload"
| "core_term_free_tyvars (CoreTm_Record flds) =
    \<Union>(set (map (core_term_free_tyvars \<circ> snd) flds))"
| "core_term_free_tyvars (CoreTm_RecordProj tm _) = core_term_free_tyvars tm"
| "core_term_free_tyvars (CoreTm_VariantProj tm _) = core_term_free_tyvars tm"
| "core_term_free_tyvars (CoreTm_ArrayProj arr idxs) =
    core_term_free_tyvars arr \<union> \<Union>(set (map core_term_free_tyvars idxs))"
| "core_term_free_tyvars (CoreTm_Match scrut arms) =
    core_term_free_tyvars scrut \<union> \<Union>(set (map (core_term_free_tyvars \<circ> snd) arms))"
| "core_term_free_tyvars (CoreTm_Sizeof tm) = core_term_free_tyvars tm"
| "core_term_free_tyvars (CoreTm_Allocated tm) = core_term_free_tyvars tm"
| "core_term_free_tyvars (CoreTm_Old tm) = core_term_free_tyvars tm"
| "core_term_free_tyvars (CoreTm_Default ty) = type_tyvars ty"

end
