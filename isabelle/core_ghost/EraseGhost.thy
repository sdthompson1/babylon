theory EraseGhost
  imports TrivialDecreases "../core/CoreSyntax" "../core/CoreModule"
begin

(* This file contains functions to "ghost-erase" a piece of Core code, i.e.,
   remove all "ghost" constructs from it.

   The result is ghost-free (ErasedIsGhostFree.thy), well-typed (EraseGhostTyping.thy,
   EraseGhostStmtTyping.thy, EraseGhostModuleTyping.thy), and its semantics is related
   to the original code by a simulation theorem (EraseGhostSimulation.thy).

   Which arguments of a call are ghost is recorded only in the signature of
   the function that is called. So the functions below take a table of
   function signatures, "funs". For a module, it is the module's TE_Functions.
*)


(* ========================================================================== *)
(* Ghost-erasing the arguments of a call *)
(* ========================================================================== *)

(* The ghost flags of a function's parameters, in order. *)
definition param_ghost_flags :: "FunInfo \<Rightarrow> GhostOrNot list" where
  "param_ghost_flags info = map (\<lambda>(_, _, gh). gh) (FI_TmArgs info)"

(* Keep the elements of a list whose flag is NotGhost. *)
definition drop_ghost :: "GhostOrNot list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "drop_ghost flags xs = map snd (filter (\<lambda>(gh, _). gh = NotGhost) (zip flags xs))"

(* Remove, from a list with one element for each parameter of the function
   fnName, the elements that belong to ghost parameters. A function that is not
   in the table keeps the whole list. *)
definition erase_ghost_args :: "(string, FunInfo) fmap \<Rightarrow> string \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "erase_ghost_args funs fnName xs =
    (case fmlookup funs fnName of
       None \<Rightarrow> xs
     | Some info \<Rightarrow> drop_ghost (param_ghost_flags info) xs)"

lemma drop_ghost_Nil [simp]:
  "drop_ghost [] xs = []"
  "drop_ghost flags [] = []"
  by (simp_all add: drop_ghost_def)

lemma drop_ghost_Cons [simp]:
  "drop_ghost (NotGhost # flags) (x # xs) = x # drop_ghost flags xs"
  "drop_ghost (Ghost # flags) (x # xs) = drop_ghost flags xs"
  by (simp_all add: drop_ghost_def)

lemma drop_ghost_map:
  "drop_ghost flags (map f xs) = map f (drop_ghost flags xs)"
proof (induction flags arbitrary: xs)
  case Nil
  show ?case by simp
next
  case (Cons gh flags)
  show ?case by (cases xs; cases gh) (simp_all add: Cons.IH)
qed

lemma set_drop_ghost_subset:
  "set (drop_ghost flags xs) \<subseteq> set xs"
  unfolding drop_ghost_def by (auto dest: set_zip_rightD)

lemma distinct_drop_ghost:
  "distinct xs \<Longrightarrow> distinct (drop_ghost flags xs)"
proof (induction flags arbitrary: xs)
  case Nil
  show ?case by simp
next
  case (Cons gh flags)
  note IH = Cons.IH and dist = Cons.prems
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons x xs')
    have d: "distinct xs'" and nin: "x \<notin> set xs'"
      using dist Cons by simp_all
    have tl: "distinct (drop_ghost flags xs')" by (rule IH[OF d])
    have "x \<notin> set (drop_ghost flags xs')"
      using nin set_drop_ghost_subset[of flags xs'] by blast
    with tl show ?thesis by (cases gh) (simp_all add: Cons)
  qed
qed

(* The number of elements kept is the number of NotGhost parameters. *)
lemma length_drop_ghost_params:
  assumes "length xs = length params"
  shows "length (drop_ghost (map (\<lambda>(_, _, gh). gh) params) xs)
           = length (filter (\<lambda>(_, _, gh). gh = NotGhost) params)"
  using assms
proof (induction xs params rule: list_induct2)
  case Nil
  show ?case by simp
next
  case (Cons x xs p params)
  obtain ty vor gh where p: "p = (ty, vor, gh)" by (cases p)
  show ?case using Cons.IH by (cases gh) (simp_all add: p)
qed

(* Dropping the ghost parameters from the parameter list itself is filtering
   it by the flag. *)
lemma drop_ghost_params:
  "drop_ghost (map (\<lambda>(_, _, gh). gh) params) params
     = filter (\<lambda>(_, _, gh). gh = NotGhost) params"
proof (induction params)
  case Nil
  show ?case by simp
next
  case (Cons p params)
  obtain ty vor gh where p: "p = (ty, vor, gh)" by (cases p)
  show ?case by (cases gh) (simp_all add: p Cons.IH)
qed


(* ========================================================================== *)
(* Ghost-erasing a term *)
(* ========================================================================== *)

(* Ghost-erase a term that is in an executable position (one that is typed in
   NotGhost mode): each function call in it loses the actuals of the callee's
   ghost parameters. Nothing else changes.

   A quantifier, "allocated" and "old" do not occur in an executable position,
   and they are left as they are. *)
fun erase_ghost_term :: "(string, FunInfo) fmap \<Rightarrow> CoreTerm \<Rightarrow> CoreTerm" where
  "erase_ghost_term funs (CoreTm_LitBool b) = CoreTm_LitBool b"
| "erase_ghost_term funs (CoreTm_LitInt i) = CoreTm_LitInt i"
| "erase_ghost_term funs (CoreTm_LitArray elemTy tms) =
    CoreTm_LitArray elemTy (map (erase_ghost_term funs) tms)"
| "erase_ghost_term funs (CoreTm_Var name) = CoreTm_Var name"
| "erase_ghost_term funs (CoreTm_Cast ty tm) = CoreTm_Cast ty (erase_ghost_term funs tm)"
| "erase_ghost_term funs (CoreTm_Unop op tm) = CoreTm_Unop op (erase_ghost_term funs tm)"
| "erase_ghost_term funs (CoreTm_Binop op tm1 tm2) =
    CoreTm_Binop op (erase_ghost_term funs tm1) (erase_ghost_term funs tm2)"
| "erase_ghost_term funs (CoreTm_Let name rhs body) =
    CoreTm_Let name (erase_ghost_term funs rhs) (erase_ghost_term funs body)"
| "erase_ghost_term funs (CoreTm_Quantifier q var ty body) = CoreTm_Quantifier q var ty body"
| "erase_ghost_term funs (CoreTm_FunctionCall fnName tyArgs args) =
    CoreTm_FunctionCall fnName tyArgs
      (erase_ghost_args funs fnName (map (erase_ghost_term funs) args))"
| "erase_ghost_term funs (CoreTm_VariantCtor ctorName tyArgs arg) =
    CoreTm_VariantCtor ctorName tyArgs (erase_ghost_term funs arg)"
| "erase_ghost_term funs (CoreTm_Record flds) =
    CoreTm_Record (map (\<lambda>(name, tm). (name, erase_ghost_term funs tm)) flds)"
| "erase_ghost_term funs (CoreTm_RecordProj tm fldName) =
    CoreTm_RecordProj (erase_ghost_term funs tm) fldName"
| "erase_ghost_term funs (CoreTm_ArrayProj tm idxs) =
    CoreTm_ArrayProj (erase_ghost_term funs tm) (map (erase_ghost_term funs) idxs)"
| "erase_ghost_term funs (CoreTm_VariantProj tm ctorName) =
    CoreTm_VariantProj (erase_ghost_term funs tm) ctorName"
| "erase_ghost_term funs (CoreTm_Match tm cases) =
    CoreTm_Match (erase_ghost_term funs tm)
                 (map (\<lambda>(pat, tm). (pat, erase_ghost_term funs tm)) cases)"
| "erase_ghost_term funs (CoreTm_Sizeof tm) = CoreTm_Sizeof (erase_ghost_term funs tm)"
| "erase_ghost_term funs (CoreTm_Allocated tm) = CoreTm_Allocated tm"
| "erase_ghost_term funs (CoreTm_Old tm) = CoreTm_Old tm"
| "erase_ghost_term funs (CoreTm_Default ty) = CoreTm_Default ty"

(* Erasure keeps the shape of an lvalue. *)
lemma lvalue_base_name_erase_ghost_term [simp]:
  "lvalue_base_name (erase_ghost_term funs tm) = lvalue_base_name tm"
  by (induction tm) simp_all

lemma is_lvalue_erase_ghost_term [simp]:
  "is_lvalue (erase_ghost_term funs tm) = is_lvalue tm"
  by (simp add: is_lvalue_def)


(* ========================================================================== *)
(* Ghost-erasing a statement list *)
(* ========================================================================== *)

(* Ghost-erase a single statement, or an entire statement list:
    - A statement marked Ghost is removed.
    - Obtain, Assert, Assume, ShowHide, Fix and Use are removed.
    - A NotGhost While loses its invariants, and its decreases-term is
      replaced by a trivial one; its body is ghost-erased.
    - The bodies of a NotGhost Match, and of a Block, are ghost-erased.
    - Every other statement is kept.
    - The terms of a statement that is kept are ghost-erased, so a call
      statement loses any ghost arguments.

   Note that each statement ghost-erases to either no statements or one statement.
*)
fun erase_ghost_statement ::
    "(string, FunInfo) fmap \<Rightarrow> CoreStatement \<Rightarrow> CoreStatement list"
and erase_ghost_statement_list ::
    "(string, FunInfo) fmap \<Rightarrow> CoreStatement list \<Rightarrow> CoreStatement list" where
  "erase_ghost_statement funs (CoreStmt_VarDecl Ghost _ _ _ _) = []"
| "erase_ghost_statement funs (CoreStmt_VarDecl NotGhost varName vr ty initTm) =
    [CoreStmt_VarDecl NotGhost varName vr ty (erase_ghost_term funs initTm)]"

| "erase_ghost_statement funs (CoreStmt_VarDeclCall Ghost _ _ _ _ _ _) = []"
| "erase_ghost_statement funs
      (CoreStmt_VarDeclCall NotGhost varName ty castOpt fnName tyArgs argTms) =
    [CoreStmt_VarDeclCall NotGhost varName ty castOpt fnName tyArgs
       (erase_ghost_args funs fnName (map (erase_ghost_term funs) argTms))]"

| "erase_ghost_statement funs (CoreStmt_Assign Ghost _ _) = []"
| "erase_ghost_statement funs (CoreStmt_Assign NotGhost lhsTm rhsTm) =
    [CoreStmt_Assign NotGhost (erase_ghost_term funs lhsTm) (erase_ghost_term funs rhsTm)]"

| "erase_ghost_statement funs (CoreStmt_AssignCall Ghost _ _ _ _ _) = []"
| "erase_ghost_statement funs
      (CoreStmt_AssignCall NotGhost lhsTm castOpt fnName tyArgs argTms) =
    [CoreStmt_AssignCall NotGhost (erase_ghost_term funs lhsTm) castOpt fnName tyArgs
       (erase_ghost_args funs fnName (map (erase_ghost_term funs) argTms))]"

| "erase_ghost_statement funs (CoreStmt_Swap Ghost _ _) = []"
| "erase_ghost_statement funs (CoreStmt_Swap NotGhost lhsTm rhsTm) =
    [CoreStmt_Swap NotGhost (erase_ghost_term funs lhsTm) (erase_ghost_term funs rhsTm)]"

| "erase_ghost_statement funs (CoreStmt_Return tm) =
    [CoreStmt_Return (erase_ghost_term funs tm)]"

| "erase_ghost_statement funs (CoreStmt_While Ghost _ _ _ _) = []"
| "erase_ghost_statement funs (CoreStmt_While NotGhost condTm invars decrTm body) =
    [CoreStmt_While NotGhost (erase_ghost_term funs condTm) [] trivial_decreases
       (erase_ghost_statement_list funs body)]"

| "erase_ghost_statement funs (CoreStmt_Match Ghost _ _) = []"
| "erase_ghost_statement funs (CoreStmt_Match NotGhost scrut arms) =
    [CoreStmt_Match NotGhost (erase_ghost_term funs scrut)
       (map (\<lambda>(pat, body). (pat, erase_ghost_statement_list funs body)) arms)]"

| "erase_ghost_statement funs (CoreStmt_Block body) =
    [CoreStmt_Block (erase_ghost_statement_list funs body)]"

| "erase_ghost_statement funs (CoreStmt_Obtain _ _ _) = []"
| "erase_ghost_statement funs (CoreStmt_Assert _ _) = []"
| "erase_ghost_statement funs (CoreStmt_Assume _) = []"
| "erase_ghost_statement funs (CoreStmt_ShowHide _ _) = []"
| "erase_ghost_statement funs (CoreStmt_Fix _ _) = []"
| "erase_ghost_statement funs (CoreStmt_Use _) = []"

| "erase_ghost_statement_list funs [] = []"
| "erase_ghost_statement_list funs (stmt # stmts) =
    erase_ghost_statement funs stmt @ erase_ghost_statement_list funs stmts"


(* ========================================================================== *)
(* Ghost-erasing function signatures and definitions *)
(* ========================================================================== *)

(* Remove the ghost parameters from a function signature. *)
definition erase_ghost_funinfo :: "FunInfo \<Rightarrow> FunInfo" where
  "erase_ghost_funinfo info =
    info \<lparr> FI_TmArgs := filter (\<lambda>(_, _, gh). gh = NotGhost) (FI_TmArgs info) \<rparr>"

(* Ghost-erase the definition of the function `name`: remove the names of
   its ghost parameters, and ghost-erase its body. *)
definition erase_ghost_function ::
    "(string, FunInfo) fmap \<Rightarrow> string \<Rightarrow> CoreFunction \<Rightarrow> CoreFunction" where
  "erase_ghost_function funs name f =
    f \<lparr> CF_Args := erase_ghost_args funs name (CF_Args f),
        CF_Body := map_option (erase_ghost_statement_list funs) (CF_Body f) \<rparr>"

lemma erase_ghost_funinfo_simps [simp]:
  "FI_TyArgs (erase_ghost_funinfo info) = FI_TyArgs info"
  "FI_TmArgs (erase_ghost_funinfo info)
     = filter (\<lambda>(_, _, gh). gh = NotGhost) (FI_TmArgs info)"
  "FI_ReturnType (erase_ghost_funinfo info) = FI_ReturnType info"
  "FI_Ghost (erase_ghost_funinfo info) = FI_Ghost info"
  "FI_Impure (erase_ghost_funinfo info) = FI_Impure info"
  by (simp_all add: erase_ghost_funinfo_def)

lemma no_ghost_params_erase_ghost_funinfo [simp]:
  "no_ghost_params (erase_ghost_funinfo info)"
  by (auto simp: no_ghost_params_def list_all_iff)

lemma erase_ghost_function_simps [simp]:
  "CF_Args (erase_ghost_function funs name f) = erase_ghost_args funs name (CF_Args f)"
  "CF_Body (erase_ghost_function funs name f)
     = map_option (erase_ghost_statement_list funs) (CF_Body f)"
  by (simp_all add: erase_ghost_function_def)


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
   from a type environment, and the ghost parameters from the signatures of the
   functions that stay. Global variables are never ghost, so they all stay.
   The fields for the current scope are not changed. *)
definition erase_ghost_tyenv :: "CoreTyEnv \<Rightarrow> CoreTyEnv" where
  "erase_ghost_tyenv env =
    env \<lparr>
      TE_TypeVars := TE_TypeVars env |\<inter>| TE_RuntimeTypeVars env,
      TE_AbstractTypes := TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env,
      TE_Functions := fmmap erase_ghost_funinfo
                        (fmfilter (tyenv_nonghost_fun env) (TE_Functions env)),
      TE_Datatypes := fmfilter (\<lambda>dtName. dtName |\<notin>| TE_GhostDatatypes env) (TE_Datatypes env),
      TE_DataCtors := fmfilter (tyenv_nonghost_ctor env) (TE_DataCtors env),
      TE_DataCtorsByType :=
        fmfilter (\<lambda>dtName. dtName |\<notin>| TE_GhostDatatypes env) (TE_DataCtorsByType env),
      TE_GhostDatatypes := {||}
    \<rparr>"

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
  "TE_FunctionImpure (erase_ghost_tyenv env) = TE_FunctionImpure env"
  "TE_ProofGoal (erase_ghost_tyenv env) = TE_ProofGoal env"
  "TE_ProofTopLevel (erase_ghost_tyenv env) = TE_ProofTopLevel env"
  "TE_Functions (erase_ghost_tyenv env)
     = fmmap erase_ghost_funinfo (fmfilter (tyenv_nonghost_fun env) (TE_Functions env))"
  "TE_Datatypes (erase_ghost_tyenv env)
     = fmfilter (\<lambda>dtName. dtName |\<notin>| TE_GhostDatatypes env) (TE_Datatypes env)"
  "TE_DataCtors (erase_ghost_tyenv env) = fmfilter (tyenv_nonghost_ctor env) (TE_DataCtors env)"
  "TE_DataCtorsByType (erase_ghost_tyenv env)
     = fmfilter (\<lambda>dtName. dtName |\<notin>| TE_GhostDatatypes env) (TE_DataCtorsByType env)"
  "TE_GhostDatatypes (erase_ghost_tyenv env) = {||}"
  by (simp_all add: erase_ghost_tyenv_def)

(* What is in the erased environment. *)

lemma erase_ghost_tyenv_fun_lookup:
  "fmlookup (TE_Functions (erase_ghost_tyenv env)) name = Some infoE
     \<longleftrightarrow> (\<exists>info. fmlookup (TE_Functions env) name = Some info
                 \<and> FI_Ghost info = NotGhost
                 \<and> infoE = erase_ghost_funinfo info)"
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
    - the ghost parameters of the remaining functions (from their signatures
      and from their parameter lists), and the actuals for them in every call;
    - the ghost datatypes, with their constructors;
    - the abstract types that are not runtime types;
    - the ghost code in the remaining function bodies.

   The table of function signatures is the module's own TE_Functions, before
   erasure. The module must, therefore, not call any function outside of its
   own TE_Functions; this requirement will be satisfied by any well-typed
   module.
*)
definition erase_ghost_module :: "CoreModule \<Rightarrow> CoreModule" where
  "erase_ghost_module m =
    m \<lparr>
      CM_TyEnv := erase_ghost_tyenv (CM_TyEnv m),
      CM_Functions :=
        fmmap_keys (erase_ghost_function (TE_Functions (CM_TyEnv m)))
                   (fmfilter (tyenv_nonghost_fun (CM_TyEnv m)) (CM_Functions m))
    \<rparr>"

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
               \<and> f = erase_ghost_function (TE_Functions (CM_TyEnv m)) name f0)"
  by (auto simp: erase_ghost_module_def)


end
