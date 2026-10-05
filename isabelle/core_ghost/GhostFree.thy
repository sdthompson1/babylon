theory GhostFree
  imports "../core/CoreSyntax" "../core/CoreModule" TrivialDecreases
begin

(* Ghost-free code.

   Code is considered "ghost-free" if it contains no ghost markers or other
   ghost-only constructs.

   Code that is both ghost-free, and well-typed in NotGhost mode, can (in principle at
   least) be executed by the interpreter without needing to do anything non-computable.
*)


(* Note: There is no separate ghost-free predicate for terms.
   Terms are already fully executable, so long as they are well-typed in
   NotGhost mode. *)

(* A statement is ghost-free if:
    - it is not marked Ghost;
    - it is not an Obtain, Assert, Assume, ShowHide, Fix or Use;
    - if it is a While, it has no invariants, and its decreases-term is the
      trivial one;
    - the statements nested in it are ghost-free. *)
fun core_statement_ghost_free :: "CoreStatement \<Rightarrow> bool"
and core_statement_list_ghost_free :: "CoreStatement list \<Rightarrow> bool" where

  "core_statement_ghost_free (CoreStmt_VarDecl declGhost _ _ _ _) = (declGhost = NotGhost)"
| "core_statement_ghost_free (CoreStmt_VarDeclCall declGhost _ _ _ _ _ _) =
    (declGhost = NotGhost)"
| "core_statement_ghost_free (CoreStmt_Assign assignGhost _ _) = (assignGhost = NotGhost)"
| "core_statement_ghost_free (CoreStmt_AssignCall assignGhost _ _ _ _ _) =
    (assignGhost = NotGhost)"
| "core_statement_ghost_free (CoreStmt_Swap swapGhost _ _) = (swapGhost = NotGhost)"
| "core_statement_ghost_free (CoreStmt_Return _) = True"

| "core_statement_ghost_free (CoreStmt_While whileGhost _ invars decrTm body) =
    (whileGhost = NotGhost
     \<and> invars = []
     \<and> decrTm = trivial_decreases
     \<and> core_statement_list_ghost_free body)"

| "core_statement_ghost_free (CoreStmt_Match matchGhost _ arms) =
    (matchGhost = NotGhost
     \<and> list_all (\<lambda>(_, body). core_statement_list_ghost_free body) arms)"

| "core_statement_ghost_free (CoreStmt_Block body) = core_statement_list_ghost_free body"

| "core_statement_ghost_free (CoreStmt_Obtain _ _ _) = False"
| "core_statement_ghost_free (CoreStmt_Assert _ _) = False"
| "core_statement_ghost_free (CoreStmt_Assume _) = False"
| "core_statement_ghost_free (CoreStmt_ShowHide _ _) = False"
| "core_statement_ghost_free (CoreStmt_Fix _ _) = False"
| "core_statement_ghost_free (CoreStmt_Use _) = False"

| "core_statement_list_ghost_free [] = True"
| "core_statement_list_ghost_free (stmt # stmts) =
    (core_statement_ghost_free stmt \<and> core_statement_list_ghost_free stmts)"

(* A module is ghost-free if:
    - no function is ghost;
    - no datatype is ghost;
    - every abstract type is a runtime type;
    - every function body is ghost-free. 
*)
definition core_module_ghost_free :: "CoreModule \<Rightarrow> bool" where
  "core_module_ghost_free m =
    ((\<forall>name info. fmlookup (TE_Functions (CM_TyEnv m)) name = Some info
                    \<longrightarrow> FI_Ghost info = NotGhost)
     \<and> TE_GhostDatatypes (CM_TyEnv m) = {||}
     \<and> TE_TypeVars (CM_TyEnv m) |\<subseteq>| TE_RuntimeTypeVars (CM_TyEnv m)
     \<and> (\<forall>name f body. fmlookup (CM_Functions m) name = Some f \<and> CF_Body f = Some body
                       \<longrightarrow> core_statement_list_ghost_free body))"


(* Properties of the definitions. *)

lemma core_statement_list_ghost_free_append:
  "core_statement_list_ghost_free (stmts1 @ stmts2)
     = (core_statement_list_ghost_free stmts1 \<and> core_statement_list_ghost_free stmts2)"
  by (induction stmts1) simp_all


end
