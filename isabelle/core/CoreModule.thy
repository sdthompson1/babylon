theory CoreModule
  imports TypeSubstStmt TypeSubstEnv
begin

(* A CoreModule is a self-contained, separately-typecheckable fragment of a
   program. It consists of a type environment (declarations), constant and
   function definitions, and concrete definitions for previously-declared
   abstract types. *)


(* ========================================================================== *)
(* Modules                                                                    *)
(* ========================================================================== *)

(* CoreFunction: the record, inside a CoreModule, that holds the *definition* of
   a function (term-parameter names and body). Everything else (type parameters,
   argument types and VarOrRef tags, return type, ghost/impure flags) is considered
   part of the *declaration* and lives in the FunInfo in the module's type
   environment. *)

(* Note: CF_Body = None marks an *extern* function, which is declared (it has a FunInfo)
   but has no Core body; its implementation is supplied at InterpState-creation time
   as an ExternFunc. *)

record CoreFunction =
  CF_Args :: "string list"                   (* term parameter names *)
  CF_Body :: "CoreStatement list option"     (* None for extern functions *)


(* CoreModule: the main record representing a Core program fragment. It contains:
    - CM_TyEnv: The types of everything this module either declares or defines.
        Note that TE_TypeVars represents the set of abstract types that are
        declared, but not defined by this module.
        TE_GlobalVars and TE_Functions represent global vars and functions
        declared by this module; these may (or may not) also be defined in
        CM_GlobalVars and CM_Functions.
    - CM_TypeSubst: Provides definitions for abstract types which were declared
        in some previous module. Required to be idempotent. Types defined here
        are *not* listed in TE_TypeVars.
    - CM_GlobalVars: Global constants defined by this module, along with their
        initializer terms.
    - CM_Functions: Functions defined by this module.

   A module may *declare* more than it *defines* (that is exactly what an
   interface is); the reverse never holds in a well-typed module. *)

record CoreModule =
  CM_TyEnv      :: CoreTyEnv
  CM_TypeSubst  :: TypeSubst
  CM_GlobalVars :: "(string, CoreTerm) fmap"
  CM_Functions  :: "(string, CoreFunction) fmap"


(* ========================================================================== *)
(* normalize_module                                                           *)
(* ========================================================================== *)

(* This resolves all abstract types into their concrete definitions. Specifically,
   it applies CM_TypeSubst to every type and term in the module, then clears the
   substitution. *)

definition normalize_module :: "CoreModule \<Rightarrow> CoreModule" where
  "normalize_module m =
    m \<lparr>
      CM_TyEnv      := apply_subst_to_tyenv (CM_TypeSubst m) (CM_TyEnv m),
      CM_GlobalVars := fmmap (apply_subst_to_term (CM_TypeSubst m)) (CM_GlobalVars m),
      CM_Functions  := fmmap
                         (\<lambda>f. f \<lparr> CF_Body :=
                                  map_option (apply_subst_to_statement_list (CM_TypeSubst m))
                                             (CF_Body f) \<rparr>)
                         (CM_Functions m),
      CM_TypeSubst  := fmempty
    \<rparr>"

(* Applying the empty substitution to the CF_Body of a CoreFunction leaves that
   CoreFunction unchanged. *)
lemma cf_body_subst_empty [simp]:
  "f \<lparr> CF_Body := map_option (apply_subst_to_statement_list fmempty) (CF_Body f) \<rparr> = f"
  by (simp add: option.map_ident_strong)

(* When CM_TypeSubst is empty, normalize_module is the identity. *)
lemma normalize_module_id_when_empty:
  assumes "CM_TypeSubst m = fmempty"
  shows   "normalize_module m = m"
  unfolding normalize_module_def
  using assms
  by (simp add: fmap.map_ident_strong)

(* normalize_module always clears the substitution. *)
lemma normalized_module_has_empty_subst:
  shows "CM_TypeSubst (normalize_module m) = fmempty"
  unfolding normalize_module_def by simp

(* normalize_module is idempotent. *)
lemma normalize_module_idempotent:
  shows "normalize_module (normalize_module m) = normalize_module m"
  by (simp add: normalize_module_id_when_empty normalized_module_has_empty_subst)


(* ========================================================================== *)
(* core_module_closed                                                         *)
(* ========================================================================== *)

(* A module is closed (fully linked) when everything declared is also defined, and
   there are no unresolved abstract types.

   Extern functions, with CF_Body = None, are allowed; these are presumed to be
   available in the external environment, and therefore do not prevent the module
   from being considered "closed".

   Note CM_TypeSubst may be non-empty in a closed module - it records the
   resolutions of abstract types that have been removed from TE_TypeVars;
   normalize_module clears it.
*)

definition core_module_closed :: "CoreModule \<Rightarrow> bool" where
  "core_module_closed m =
    (fmdom (TE_GlobalVars (CM_TyEnv m)) = fmdom (CM_GlobalVars m)
     \<and> fmdom (TE_Functions (CM_TyEnv m)) = fmdom (CM_Functions m)
     \<and> TE_TypeVars (CM_TyEnv m) = {||})"

(* Closedness only looks at map domains and TE_TypeVars, none of which are
   changed by substitution, so it is invariant under normalize_module. *)
lemma core_module_closed_normalize_module [simp]:
  "core_module_closed (normalize_module m) = core_module_closed m"
  unfolding core_module_closed_def normalize_module_def apply_subst_to_tyenv_def
  by simp


(* ========================================================================== *)
(* Capture-avoidance                                                          *)
(* ========================================================================== *)

(* The type variable names mentioned in the CM_TypeSubst (in both domain and
   range) must be distinct from the names used for type parameters of generic
   functions or datatypes.

   This property is automatically true for Babylon programs (after renaming)
   because entries in CM_TypeSubst are global names and hence contain a dot;
   type parameters are local names and hence undotted. At the CoreModule level, we
   do not capture this dotted/undotted discipline, but we do maintain the
   invariant that the two sets of names are distinct; this is the purpose
   of the `capture_avoiding` predicate. *)

definition capture_avoiding :: "CoreModule \<Rightarrow> bool" where
  "capture_avoiding m =
    ((\<forall>funName info.
        fmlookup (TE_Functions (CM_TyEnv m)) funName = Some info \<longrightarrow>
        subst_names (CM_TypeSubst m) |\<inter>| fset_of_list (FI_TyArgs info) = {||})
     \<and> (\<forall>ctorName dtName tyVars payload.
          fmlookup (TE_DataCtors (CM_TyEnv m)) ctorName = Some (dtName, tyVars, payload) \<longrightarrow>
          subst_names (CM_TypeSubst m) |\<inter>| fset_of_list tyVars = {||}))"

(* A module with an empty substitution is trivially capture-avoiding. *)
lemma capture_avoiding_empty_subst:
  assumes "CM_TypeSubst m = fmempty"
  shows "capture_avoiding m"
  unfolding capture_avoiding_def using assms by simp


(* ========================================================================== *)
(* Ghost-marker sanity                                                        *)
(* ========================================================================== *)

(* A module may only mark ghost what it itself declares: TE_GhostGlobals
   names its own global declarations, TE_GhostDatatypes its own datatypes. *)

definition module_ghost_subsets_ok :: "CoreModule \<Rightarrow> bool" where
  "module_ghost_subsets_ok m =
    (TE_GhostGlobals (CM_TyEnv m) |\<subseteq>| fmdom (TE_GlobalVars (CM_TyEnv m))
     \<and> TE_GhostDatatypes (CM_TyEnv m) |\<subseteq>| fmdom (TE_Datatypes (CM_TyEnv m)))"


(* ========================================================================== *)
(* Module-scope type environments                                             *)
(* ========================================================================== *)

(* This predicate says that a type environment is at *module scope*, i.e. not
   inside any function or proof. Specifically: there are no local variables
   (TE_LocalVars, TE_GhostLocals and TE_ConstLocals all empty); no enclosing function
   (TE_ReturnType = CoreTy_Record [] and TE_FunctionGhost = NotGhost by convention);
   no enclosing proof (TE_ProofGoal = None, TE_ProofTopLevel = False); and no
   function-level type parameters (every in-scope type variable is a module-level
   abstract type, i.e. TE_AbstractTypes = TE_TypeVars). *)
definition tyenv_module_scope :: "CoreTyEnv \<Rightarrow> bool" where
  "tyenv_module_scope env =
    (TE_LocalVars env = fmempty
     \<and> TE_GhostLocals env = {||}
     \<and> TE_ConstLocals env = {||}
     \<and> TE_ReturnType env = CoreTy_Record []
     \<and> TE_FunctionGhost env = NotGhost
     \<and> TE_ProofGoal env = None
     \<and> TE_ProofTopLevel env = False
     \<and> TE_AbstractTypes env = TE_TypeVars env)"

(* Applying a substitution to a CoreTyEnv preserves tyenv_module_scope. *)
lemma subst_preserves_tyenv_module_scope:
  assumes "tyenv_module_scope env"
  shows "tyenv_module_scope (apply_subst_to_tyenv subst env)"
  using assms tyenv_module_scope_def apply_subst_to_tyenv_def by fastforce


(* ========================================================================== *)
(* core_module_invariant                                                      *)
(* ========================================================================== *)

(* All CoreModules (even non-well-typed ones) are expected to satisfy the
   following predicate. This is true of all modules created by the elaborator,
   and is preserved by the linker.

   The conjuncts:
   - CM_TypeSubst is idempotent and capture-avoiding;
   - ghost markers only on the module's own declarations;
   - a resolved abstract type is recorded in the substitution and removed
     from TE_TypeVars, so the two are disjoint;
   - the runtime type variables are a subset of the in-scope type variables;
   - the type environment is at module scope. *)

definition core_module_invariant :: "CoreModule \<Rightarrow> bool" where
  "core_module_invariant m =
    (idempotent_subst (CM_TypeSubst m)
     \<and> capture_avoiding m
     \<and> module_ghost_subsets_ok m
     \<and> fmdom (CM_TypeSubst m) |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}
     \<and> TE_RuntimeTypeVars (CM_TyEnv m) |\<subseteq>| TE_TypeVars (CM_TyEnv m)
     \<and> tyenv_module_scope (CM_TyEnv m))"

(* Destructor for the conjunct that theorems most often take per input. *)
lemma core_module_invariant_ghost_subsets_ok:
  "core_module_invariant m \<Longrightarrow> module_ghost_subsets_ok m"
  unfolding core_module_invariant_def by blast

end
