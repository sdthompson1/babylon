theory CoreTyEnv
  imports CoreSyntax "HOL-Library.Finite_Map"
begin

record FunInfo =
  (* Type arguments: type variable numbers *)
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
  (* Local variable bindings (mutable or const-local, e.g. let-bindings, function params).
     These correspond to IS_Locals and IS_Refs in the interpreter state. *)
  TE_LocalVars :: "(string, CoreType) fmap"

  (* Global variable bindings (always constant / read-only).
     These correspond to IS_Globals in the interpreter state.
     Globals are implicitly constant and do not appear in TE_ConstNames. *)
  TE_GlobalVars :: "(string, CoreType) fmap"

  (* Ghost variables - subset of TE_LocalVars and TE_GlobalVars keys *)
  TE_GhostVars :: "string fset"

  (* Constant local names - subset of TE_LocalVars keys; these are not assignable.
     Globals are implicitly constant and do not need to appear here. *)
  TE_ConstNames :: "string fset"

  (* In-scope type variables (for polymorphic functions) *)
  TE_TypeVars :: "nat fset"

  (* Type variables that are known to be bound to runtime types - subset of TE_TypeVars *)
  TE_RuntimeTypeVars :: "nat fset"

  (* Expected return type of the enclosing function *)
  TE_ReturnType :: CoreType

  (* Ghost-ness of the enclosing function. *)
  TE_FunctionGhost :: GhostOrNot

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

(* Look up a term variable: locals shadow globals *)
definition tyenv_lookup_var :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> CoreType option" where
  "tyenv_lookup_var env name =
    (case fmlookup (TE_LocalVars env) name of
      Some ty \<Rightarrow> Some ty
    | None \<Rightarrow> fmlookup (TE_GlobalVars env) name)"

(* A term variable is writable if it is a non-const local.
   Globals are implicitly constant and never writable. *)
definition tyenv_var_writable :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> bool" where
  "tyenv_var_writable env name =
    (fmlookup (TE_LocalVars env) name \<noteq> None \<and> name |\<notin>| TE_ConstNames env)"

(* tyenv_subset env1 env2: env1 is a "sub-environment" of env2.
   This means env2 has all the same variables (with the same types) plus possibly more.
   Only locals may grow; globals and "fixed" fields must be identical. *)
definition tyenv_subset :: "CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "tyenv_subset env1 env2 \<equiv>
    (\<forall>name ty. fmlookup (TE_LocalVars env1) name = Some ty \<longrightarrow>
               fmlookup (TE_LocalVars env2) name = Some ty) \<and>
    TE_GlobalVars env1 = TE_GlobalVars env2 \<and>
    TE_GhostVars env1 |\<subseteq>| TE_GhostVars env2 \<and>
    TE_ConstNames env1 |\<subseteq>| TE_ConstNames env2 \<and>
    TE_ReturnType env1 = TE_ReturnType env2 \<and>
    TE_FunctionGhost env1 = TE_FunctionGhost env2 \<and>
    TE_Functions env1 = TE_Functions env2 \<and>
    TE_Datatypes env1 = TE_Datatypes env2 \<and>
    TE_DataCtors env1 = TE_DataCtors env2 \<and>
    TE_DataCtorsByType env1 = TE_DataCtorsByType env2 \<and>
    TE_GhostDatatypes env1 = TE_GhostDatatypes env2 \<and>
    TE_TypeVars env1 = TE_TypeVars env2 \<and>
    TE_RuntimeTypeVars env1 = TE_RuntimeTypeVars env2"

lemma tyenv_subset_refl: "tyenv_subset env env"
  unfolding tyenv_subset_def by simp

lemma tyenv_subset_trans:
  assumes "tyenv_subset env1 env2" and "tyenv_subset env2 env3"
  shows "tyenv_subset env1 env3"
  using assms unfolding tyenv_subset_def by (auto dest: fsubset_trans)

lemma tyenv_lookup_var_local [simp]:
  "fmlookup (TE_LocalVars env) name = Some ty \<Longrightarrow> tyenv_lookup_var env name = Some ty"
  unfolding tyenv_lookup_var_def by simp

lemma tyenv_lookup_var_global:
  "fmlookup (TE_LocalVars env) name = None \<Longrightarrow>
   tyenv_lookup_var env name = fmlookup (TE_GlobalVars env) name"
  unfolding tyenv_lookup_var_def by simp

lemma tyenv_lookup_var_TE_ConstNames_irrelevant [simp]:
  "tyenv_lookup_var (env \<lparr> TE_ConstNames := c \<rparr>) name = tyenv_lookup_var env name"
  unfolding tyenv_lookup_var_def by (simp split: option.splits)


end
