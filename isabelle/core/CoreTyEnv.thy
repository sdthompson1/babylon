theory CoreTyEnv
  imports CoreSyntax "HOL-Library.Finite_Map"
begin

record FunInfo =
  (* Number of type arguments, and corresponding metavariables *)
  (* (The metavariables are present in FI_TmArgs and FI_ReturnType and must be
     substituted before using those types) *)
  FI_TyArgs :: "nat list"

  (* Term arguments: type and whether passed by value (Var) or reference (Ref) *)
  FI_TmArgs :: "(CoreType \<times> VarOrRef) list"

  (* Return type *)
  FI_ReturnType :: CoreType

  (* Ghost flag - Ghost functions can only be used in ghost contexts *)
  FI_Ghost :: GhostOrNot

  (* Impure flag - impure functions may modify the world state *)
  FI_Impure :: bool


record CoreTyEnv =
  (* Term-level bindings: variables and constants *)
  TE_TermVars :: "(string, CoreType) fmap"

  (* Ghost variables - subset of TE_TermVars keys *)
  TE_GhostVars :: "string fset"

  (* Constant names - subset of TE_TermVars keys; these are not assignable *)
  TE_ConstNames :: "string fset"

  (* Type variable bindings: for polymorphic contexts *)
  TE_TypeVars :: "string fset"

  (* Expected return type of the enclosing function *)
  TE_ReturnType :: CoreType

  (* Function signatures *)
  TE_Functions :: "(string, FunInfo) fmap"

  (* Datatypes: maps datatype name to number of type arguments *)
  TE_Datatypes :: "(string, nat) fmap"

  (* Data constructors: maps constructor name to (datatype name, metavars, payload type) *)
  (* The number of metavars should be consistent with TE_Datatypes *)
  TE_DataCtors :: "(string, string \<times> nat list \<times> CoreType) fmap"

  (* Reverse mapping: datatype name to list of its constructor names *)
  (* Should be consistent with TE_DataCtors *)
  TE_DataCtorsByType :: "(string, string list) fmap"

  (* Ghost datatypes: datatypes whose constructors have non-runtime payload types.
     These cannot be represented in memory (e.g. as tagged unions) because the payload
     sizes are not known. A datatype is ghost if any of its constructor payloads
     contains MathInt, MathReal, or another ghost datatype. *)
  TE_GhostDatatypes :: "string fset"

(* tyenv_subset env1 env2: env1 is a "sub-environment" of env2.
   This means env2 has all the same variables (with the same types) plus possibly more.
   The "fixed" fields (functions, datatypes, return type, type vars) must be identical. *)
definition tyenv_subset :: "CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "tyenv_subset env1 env2 \<equiv>
    (\<forall>name ty. fmlookup (TE_TermVars env1) name = Some ty \<longrightarrow>
               fmlookup (TE_TermVars env2) name = Some ty) \<and>
    TE_GhostVars env1 |\<subseteq>| TE_GhostVars env2 \<and>
    TE_ConstNames env1 |\<subseteq>| TE_ConstNames env2 \<and>
    TE_ReturnType env1 = TE_ReturnType env2 \<and>
    TE_Functions env1 = TE_Functions env2 \<and>
    TE_Datatypes env1 = TE_Datatypes env2 \<and>
    TE_DataCtors env1 = TE_DataCtors env2 \<and>
    TE_DataCtorsByType env1 = TE_DataCtorsByType env2 \<and>
    TE_GhostDatatypes env1 = TE_GhostDatatypes env2 \<and>
    TE_TypeVars env1 = TE_TypeVars env2"

lemma tyenv_subset_refl: "tyenv_subset env env"
  unfolding tyenv_subset_def by simp

lemma tyenv_subset_trans:
  assumes "tyenv_subset env1 env2" and "tyenv_subset env2 env3"
  shows "tyenv_subset env1 env3"
  using assms unfolding tyenv_subset_def by (auto dest: fsubset_trans)

end
