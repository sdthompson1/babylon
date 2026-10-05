theory EraseGhost
  imports TrivialDecreases "../core/CoreSyntax" "../core/CoreModule"
begin

(* This file contains functions to "ghost-erase" a piece of Core code, i.e.,
   remove all "ghost" constructs from it.

   The result is ghost-free (ErasedIsGhostFree.thy), well-typed (EraseGhostTyping.thy,
   EraseGhostStmtTyping.thy, EraseGhostModuleTyping.thy), and its semantics is related
   to the original code by a simulation theorem (EraseGhostSimulation.thy).

   Some further properties are proved in EraseGhostLemmas.thy.
*)

(* ========================================================================== *)
(* Ghost-erasing a statement list *)
(* ========================================================================== *)

(* Ghost-erase a single statement, or an entire statement list:
    - A statement marked Ghost is removed.
    - Obtain, Assert, Assume, ShowHide, Fix and Use are removed.
    - A NotGhost While loses its invariants, and its decreases-term is
      replaced by a trivial one; its body is ghost-erased.
    - The bodies of a NotGhost Match, and of a Block, are ghost-erased.
    - Every other statement is kept as it is.

   Note that each statement ghost-erases to either no statements or one statement. 
*)
fun erase_ghost_statement :: "CoreStatement \<Rightarrow> CoreStatement list"
and erase_ghost_statement_list :: "CoreStatement list \<Rightarrow> CoreStatement list" where
  "erase_ghost_statement (CoreStmt_VarDecl Ghost _ _ _ _) = []"
| "erase_ghost_statement (CoreStmt_VarDecl NotGhost varName vr ty initTm) =
    [CoreStmt_VarDecl NotGhost varName vr ty initTm]"

| "erase_ghost_statement (CoreStmt_VarDeclCall Ghost _ _ _ _ _ _) = []"
| "erase_ghost_statement (CoreStmt_VarDeclCall NotGhost varName ty castOpt fnName tyArgs argTms) =
    [CoreStmt_VarDeclCall NotGhost varName ty castOpt fnName tyArgs argTms]"

| "erase_ghost_statement (CoreStmt_Assign Ghost _ _) = []"
| "erase_ghost_statement (CoreStmt_Assign NotGhost lhsTm rhsTm) =
    [CoreStmt_Assign NotGhost lhsTm rhsTm]"

| "erase_ghost_statement (CoreStmt_AssignCall Ghost _ _ _ _ _) = []"
| "erase_ghost_statement (CoreStmt_AssignCall NotGhost lhsTm castOpt fnName tyArgs argTms) =
    [CoreStmt_AssignCall NotGhost lhsTm castOpt fnName tyArgs argTms]"

| "erase_ghost_statement (CoreStmt_Swap Ghost _ _) = []"
| "erase_ghost_statement (CoreStmt_Swap NotGhost lhsTm rhsTm) =
    [CoreStmt_Swap NotGhost lhsTm rhsTm]"

| "erase_ghost_statement (CoreStmt_Return tm) = [CoreStmt_Return tm]"

| "erase_ghost_statement (CoreStmt_While Ghost _ _ _ _) = []"
| "erase_ghost_statement (CoreStmt_While NotGhost condTm invars decrTm body) =
    [CoreStmt_While NotGhost condTm [] trivial_decreases (erase_ghost_statement_list body)]"

| "erase_ghost_statement (CoreStmt_Match Ghost _ _) = []"
| "erase_ghost_statement (CoreStmt_Match NotGhost scrut arms) =
    [CoreStmt_Match NotGhost scrut
       (map (\<lambda>(pat, body). (pat, erase_ghost_statement_list body)) arms)]"

| "erase_ghost_statement (CoreStmt_Block body) =
    [CoreStmt_Block (erase_ghost_statement_list body)]"

| "erase_ghost_statement (CoreStmt_Obtain _ _ _) = []"
| "erase_ghost_statement (CoreStmt_Assert _ _) = []"
| "erase_ghost_statement (CoreStmt_Assume _) = []"
| "erase_ghost_statement (CoreStmt_ShowHide _ _) = []"
| "erase_ghost_statement (CoreStmt_Fix _ _) = []"
| "erase_ghost_statement (CoreStmt_Use _) = []"

| "erase_ghost_statement_list [] = []"
| "erase_ghost_statement_list (stmt # stmts) =
    erase_ghost_statement stmt @ erase_ghost_statement_list stmts"


(* ========================================================================== *)
(* Ghost-erasing function bodies *)
(* ========================================================================== *)

(* Ghost-erase all the statements in a function body. *)
definition erase_ghost_function :: "CoreFunction \<Rightarrow> CoreFunction" where
  "erase_ghost_function f =
    f \<lparr> CF_Body := map_option erase_ghost_statement_list (CF_Body f) \<rparr>"

(* Ghost-erase all the statements in all function bodies of a module.
   Note this doesn't actually remove the ghost functions from the module. *)
definition erase_ghost_module_bodies :: "CoreModule \<Rightarrow> CoreModule" where
  "erase_ghost_module_bodies m =
    m \<lparr> CM_Functions := fmmap erase_ghost_function (CM_Functions m) \<rparr>"

(* Simp lemmas. *)
lemma erase_ghost_function_simps [simp]:
  "CF_Args (erase_ghost_function f) = CF_Args f"
  "CF_Body (erase_ghost_function f) = map_option erase_ghost_statement_list (CF_Body f)"
  by (simp_all add: erase_ghost_function_def)

lemma erase_ghost_module_bodies_simps [simp]:
  "CM_TyEnv (erase_ghost_module_bodies m) = CM_TyEnv m"
  "CM_TypeSubst (erase_ghost_module_bodies m) = CM_TypeSubst m"
  "CM_GlobalVars (erase_ghost_module_bodies m) = CM_GlobalVars m"
  "CM_Functions (erase_ghost_module_bodies m) = fmmap erase_ghost_function (CM_Functions m)"
  by (simp_all add: erase_ghost_module_bodies_def)


(* ========================================================================== *)
(* Ghost-erasing a type environment *)
(* ========================================================================== *)

(* Helper: The function is declared, and is not ghost. *)
definition tyenv_nonghost_fun :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> bool" where
  "tyenv_nonghost_fun env name =
    (case fmlookup (TE_Functions env) name of
       None \<Rightarrow> False
     | Some info \<Rightarrow> FI_Ghost info = NotGhost)"

(* Helper: The data constructor is declared, and its datatype is not ghost. *)
definition tyenv_nonghost_ctor :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> bool" where
  "tyenv_nonghost_ctor env ctorName =
    (case fmlookup (TE_DataCtors env) ctorName of
       None \<Rightarrow> False
     | Some (dtName, _, _) \<Rightarrow> dtName |\<notin>| TE_GhostDatatypes env)"

(* Erase all ghost functions, ghost datatypes, and non-runtime type variables
   from a type environment. Global variables are never ghost, so they all stay.
   The fields for the current scope are not changed. *)
definition erase_ghost_tyenv :: "CoreTyEnv \<Rightarrow> CoreTyEnv" where
  "erase_ghost_tyenv env =
    env \<lparr>
      TE_TypeVars := TE_TypeVars env |\<inter>| TE_RuntimeTypeVars env,
      TE_AbstractTypes := TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env,
      TE_Functions := fmfilter (tyenv_nonghost_fun env) (TE_Functions env),
      TE_Datatypes := fmfilter (\<lambda>dtName. dtName |\<notin>| TE_GhostDatatypes env) (TE_Datatypes env),
      TE_DataCtors := fmfilter (tyenv_nonghost_ctor env) (TE_DataCtors env),
      TE_DataCtorsByType :=
        fmfilter (\<lambda>dtName. dtName |\<notin>| TE_GhostDatatypes env) (TE_DataCtorsByType env),
      TE_GhostDatatypes := {||}
    \<rparr>"

(* Simp lemmas *)
lemma erase_ghost_tyenv_simps [simp]:
  "TE_LocalVars (erase_ghost_tyenv env) = TE_LocalVars env"
  "TE_GlobalVars (erase_ghost_tyenv env) = TE_GlobalVars env"
  "TE_GhostLocals (erase_ghost_tyenv env) = TE_GhostLocals env"
  "TE_ConstLocals (erase_ghost_tyenv env) = TE_ConstLocals env"
  "TE_TypeVars (erase_ghost_tyenv env) = TE_TypeVars env |\<inter>| TE_RuntimeTypeVars env"
  "TE_RuntimeTypeVars (erase_ghost_tyenv env) = TE_RuntimeTypeVars env"
  "TE_AbstractTypes (erase_ghost_tyenv env) = TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env"
  "TE_ReturnType (erase_ghost_tyenv env) = TE_ReturnType env"
  "TE_FunctionGhost (erase_ghost_tyenv env) = TE_FunctionGhost env"
  "TE_ProofGoal (erase_ghost_tyenv env) = TE_ProofGoal env"
  "TE_ProofTopLevel (erase_ghost_tyenv env) = TE_ProofTopLevel env"
  "TE_Functions (erase_ghost_tyenv env) = fmfilter (tyenv_nonghost_fun env) (TE_Functions env)"
  "TE_Datatypes (erase_ghost_tyenv env)
     = fmfilter (\<lambda>dtName. dtName |\<notin>| TE_GhostDatatypes env) (TE_Datatypes env)"
  "TE_DataCtors (erase_ghost_tyenv env) = fmfilter (tyenv_nonghost_ctor env) (TE_DataCtors env)"
  "TE_DataCtorsByType (erase_ghost_tyenv env)
     = fmfilter (\<lambda>dtName. dtName |\<notin>| TE_GhostDatatypes env) (TE_DataCtorsByType env)"
  "TE_GhostDatatypes (erase_ghost_tyenv env) = {||}"
  by (simp_all add: erase_ghost_tyenv_def)

(* What is in the erased environment. *)

lemma erase_ghost_tyenv_fun_lookup:
  "fmlookup (TE_Functions (erase_ghost_tyenv env)) name = Some info
     \<longleftrightarrow> fmlookup (TE_Functions env) name = Some info \<and> FI_Ghost info = NotGhost"
  by (auto simp: tyenv_nonghost_fun_def split: option.splits)

lemma erase_ghost_tyenv_datatype_lookup:
  "fmlookup (TE_Datatypes (erase_ghost_tyenv env)) dtName = Some n
     \<longleftrightarrow> fmlookup (TE_Datatypes env) dtName = Some n \<and> dtName |\<notin>| TE_GhostDatatypes env"
  by auto

lemma erase_ghost_tyenv_ctor_lookup:
  "fmlookup (TE_DataCtors (erase_ghost_tyenv env)) ctorName = Some (dtName, tyVars, payload)
     \<longleftrightarrow> fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload)
         \<and> dtName |\<notin>| TE_GhostDatatypes env"
  by (auto simp: tyenv_nonghost_ctor_def split: option.splits)

lemma erase_ghost_tyenv_ctors_by_type_lookup:
  "fmlookup (TE_DataCtorsByType (erase_ghost_tyenv env)) dtName = Some ctors
     \<longleftrightarrow> fmlookup (TE_DataCtorsByType env) dtName = Some ctors
         \<and> dtName |\<notin>| TE_GhostDatatypes env"
  by auto


(* ========================================================================== *)
(* Ghost-erasing an entire module *)
(* ========================================================================== *)

(* erase_ghost_module removes everything that is ghost from a module:
    - the ghost functions (from the type environment and from CM_Functions);
    - the ghost datatypes, with their constructors;
    - the abstract types that are not runtime types;
    - the ghost code in the remaining function bodies.
*)
definition erase_ghost_module :: "CoreModule \<Rightarrow> CoreModule" where
  "erase_ghost_module m =
    m \<lparr>
      CM_TyEnv := erase_ghost_tyenv (CM_TyEnv m),
      CM_Functions :=
        fmmap erase_ghost_function
              (fmfilter (tyenv_nonghost_fun (CM_TyEnv m)) (CM_Functions m))
    \<rparr>"

(* Simp lemmas *)
lemma erase_ghost_module_simps [simp]:
  "CM_TyEnv (erase_ghost_module m) = erase_ghost_tyenv (CM_TyEnv m)"
  "CM_TypeSubst (erase_ghost_module m) = CM_TypeSubst m"
  "CM_GlobalVars (erase_ghost_module m) = CM_GlobalVars m"
  by (simp_all add: erase_ghost_module_def)

(* What is in the erased module *)
lemma erase_ghost_module_fun_lookup:
  "fmlookup (CM_Functions (erase_ghost_module m)) name = Some f
     \<longleftrightarrow> (\<exists>f0. fmlookup (CM_Functions m) name = Some f0
               \<and> tyenv_nonghost_fun (CM_TyEnv m) name
               \<and> f = erase_ghost_function f0)"
  by (auto simp: erase_ghost_module_def)


end
