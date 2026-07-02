theory CoreModule
  imports TypeSubstStmt TypeSubstEnv
begin

(* ========================================================================== *)
(* Modules                                                                    *)
(*                                                                            *)
(* A CoreModule is a self-contained, separately-typecheckable fragment of a   *)
(* program. It consists of a type environment (declarations), constant and    *)
(* function definitions, and concrete definitions for previously-declared     *)
(* abstract types.                                                            *)
(* ========================================================================== *)


(* A CoreFunction holds the parts of a function *definition* that are not      *)
(* already present in its FunInfo (CoreTyEnv.thy): the term-parameter names    *)
(* and the body. Everything type-level (type parameters, argument types and    *)
(* VarOrRef tags, return type, ghost/impure flags) is read from the            *)
(* counterpart FunInfo.                                                        *)
(*                                                                             *)
(* CF_Body = None marks an *extern* function: declared (it has a FunInfo) but  *)
(* with no Core body; its implementation is supplied at InterpState-creation   *)
(* time as an ExternFunc.                                                      *)
record CoreFunction =
  CF_Args :: "string list"                   (* term parameter names *)
  CF_Body :: "CoreStatement list option"     (* None for extern functions *)


(* A CoreModule contains:                                                        *)
(*  - CM_TyEnv: The types of everything this module either declares or defines.  *)
(*      Note that TE_TypeVars represents the set of abstract types that are      *)
(*      declared, but not defined by this module.                                *)
(*      TE_GlobalVars and TE_Functions represent global vars and functions       *)
(*      declared by this module; these may (or may not) also be defined in       *)
(*      CM_GlobalVars and CM_Functions.                                          *)
(*  - CM_TypeSubst: Provides definitions for abstract types which were declared  *)
(*      in some previous module. Required to be idempotent. Types defined here   *)
(*      are *not* listed in TE_TypeVars.                                         *)
(*  - CM_GlobalVars: Global constants defined by this module, along with their   *)
(*      initializer terms.                                                       *)
(*  - CM_Functions: Functions defined by this module.                            *)
(*                                                                               *)
(* A module may *declare* more than it *defines* (that is exactly what an        *)
(* interface is); the reverse never holds in a well-typed module.                *)
record CoreModule =
  CM_TyEnv      :: CoreTyEnv
  CM_TypeSubst  :: TypeSubst
  CM_GlobalVars :: "(string, CoreTerm) fmap"
  CM_Functions  :: "(string, CoreFunction) fmap"


(* ========================================================================== *)
(* normalize_module                                                           *)
(*                                                                            *)
(* Resolve all abstract types into their concrete definitions: apply          *)
(* CM_TypeSubst to every type and term in the module, then clear the          *)
(* substitution.                                                              *)
(* ========================================================================== *)

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


(* ========================================================================== *)
(* Properties of normalize_module                                             *)
(* ========================================================================== *)

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
(*                                                                            *)
(* A module is closed (fully linked) when everything declared is also         *)
(* defined, and there are no unresolved abstract types. Extern functions      *)
(* appear in CM_Functions with CF_Body = None, so they satisfy the function   *)
(* clause. Note CM_TypeSubst may be non-empty in a closed module - it records *)
(* the resolutions of abstract types that have been removed from TE_TypeVars; *)
(* normalize_module clears it.                                                *)
(* ========================================================================== *)

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

end
