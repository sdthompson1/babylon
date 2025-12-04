theory TypeEnv
  imports "../base/BabSyntax" "TypesEqual"
begin

record BabTyEnv =
  (* Term-level bindings: variables and constants *)
  (* Types are kind-correct and all typedefs are resolved *)
  TE_TermVars :: "(string, BabType) fmap"

  (* Ghost variables - subset of TE_TermVars keys *)
  TE_GhostVars :: "string fset"

  (* Type variable bindings: for polymorphic contexts *)
  TE_TypeVars :: "string fset"

  (* Function signatures *)
  (* DeclFuns are valid and have all typedefs resolved *)
  TE_Functions :: "(string, DeclFun) fmap"

  (* Datatype definitions *)
  (* DeclDatatypes are valid and have all typedefs resolved *)
  TE_Datatypes :: "(string, DeclDatatype) fmap"

  (* Data constructors: maps constructor name to (datatype name, num type args, payload type) *)
  (* This should be consistent with TE_Datatypes *)
  TE_DataCtors :: "(string, string \<times> nat \<times> BabType option) fmap"


(* Helper functions for BabTyEnv *)

(* Add a variable to the environment *)
(*
fun add_var :: "string \<Rightarrow> BabType \<Rightarrow> GhostOrNot \<Rightarrow> BabTyEnv \<Rightarrow> BabTyEnv" where
  "add_var name ty Ghost env =
    env \<lparr> TE_TermVars := fmupd name ty (TE_TermVars env),
          TE_GhostVars := finsert name (TE_GhostVars env) \<rparr>"
| "add_var name ty NotGhost env =
    env \<lparr> TE_TermVars := fmupd name ty (TE_TermVars env) \<rparr>"
*)

(* Add a type variable to the environment *)
(*
fun add_type_var :: "string \<Rightarrow> BabTyEnv \<Rightarrow> BabTyEnv" where
  "add_type_var name env = env \<lparr> TE_TypeVars := finsert name (TE_TypeVars env) \<rparr>"
*)

(* Clear local variables (for entering a new function scope) *)
(*
fun clear_locals :: "BabTyEnv \<Rightarrow> BabTyEnv" where
  "clear_locals env = env \<lparr> TE_TermVars := fmempty, TE_GhostVars := {||}, TE_TypeVars := {||} \<rparr>"
*)

(* Check if a type is an integer type *)
fun is_integer_type :: "BabType \<Rightarrow> bool" where
  "is_integer_type (BabTy_FiniteInt _ _ _) = True"
| "is_integer_type (BabTy_MathInt _) = True"
| "is_integer_type _ = False"

(* Check if a type is a signed integer type (signed finite int or MathInt) *)
fun is_signed_integer_type :: "BabType \<Rightarrow> bool" where
  "is_signed_integer_type (BabTy_FiniteInt _ Signed _) = True"
| "is_signed_integer_type (BabTy_MathInt _) = True"
| "is_signed_integer_type _ = False"

(* Check if a type is a finite integer type *)
fun is_finite_integer_type :: "BabType \<Rightarrow> bool" where
  "is_finite_integer_type (BabTy_FiniteInt _ _ _) = True"
| "is_finite_integer_type _ = False"

(* Check if an array dimension is resolved (not BabDim_Fixed) *)
fun is_resolved_dimension :: "BabDimension \<Rightarrow> bool" where
  "is_resolved_dimension (BabDim_Fixed _) = False"
| "is_resolved_dimension _ = True"

(* Check if a type is a runtime-compatible type (no MathInt/MathReal) *)
(* Note: Metavariables are considered runtime types, but metavariables should theoretically
   be removed anyway, post type inference. *)
fun is_runtime_type :: "BabType \<Rightarrow> bool" where
  "is_runtime_type (BabTy_MathInt _) = False"
| "is_runtime_type (BabTy_MathReal _) = False"
| "is_runtime_type (BabTy_Name _ _ tyArgs) = list_all is_runtime_type tyArgs"
| "is_runtime_type (BabTy_Tuple _ tys) = list_all is_runtime_type tys"
| "is_runtime_type (BabTy_Record _ flds) = list_all (is_runtime_type \<circ> snd) flds"
| "is_runtime_type (BabTy_Array _ ty _) = is_runtime_type ty"
| "is_runtime_type _ = True"


end
