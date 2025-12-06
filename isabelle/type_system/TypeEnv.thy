theory TypeEnv
  imports "../base/BabSyntax" "TypesEqual"
begin

(* Note: all types contained in the BabTyEnv are fully elaborated *)

record BabTyEnv =
  (* Term-level bindings: variables and constants *)
  TE_TermVars :: "(string, BabType) fmap"

  (* Ghost variables - subset of TE_TermVars keys *)
  TE_GhostVars :: "string fset"

  (* Type variable bindings: for polymorphic contexts *)
  TE_TypeVars :: "string fset"

  (* Function signatures *)
  TE_Functions :: "(string, DeclFun) fmap"

  (* Datatype type parameters: maps datatype name to list of type variable names *)
  TE_Datatypes :: "(string, string list) fmap"

  (* Data constructors: maps constructor name to (datatype name, num type args, payload type) *)
  (* The num type args should be consistent with TE_Datatypes *)
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

end
