theory CoreTyEnv
  imports CoreSyntax "HOL-Library.Finite_Map"
begin

record FunInfo =
  (* Number of type arguments, and corresponding metavariables *)
  (* (The metavariables are present in FI_TmArgs and FI_ReturnType and must be
     substituted before using those types) *)
  FI_TyArgs :: "nat list"

  (* Number and type of term arguments *)
  FI_TmArgs :: "CoreType list"

  (* Return type *)
  FI_ReturnType :: CoreType

  (* Ghost flag - Ghost functions can only be used in ghost contexts *)
  FI_Ghost :: GhostOrNot

  (* TODO: Impure and Ref information will be needed to elaborate call stmts properly *)
  (* TODO: We also need to know if the return type was absent in the Bab FunDecl
     (as opposed to present and elaborated to {}) *)


record CoreTyEnv =
  (* Term-level bindings: variables and constants *)
  TE_TermVars :: "(string, CoreType) fmap"

  (* Ghost variables - subset of TE_TermVars keys *)
  TE_GhostVars :: "string fset"

  (* Type variable bindings: for polymorphic contexts *)
  TE_TypeVars :: "string fset"

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


end
