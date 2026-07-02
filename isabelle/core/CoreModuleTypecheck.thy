theory CoreModuleTypecheck
  imports CoreModule CoreStmtTypecheck CoreTyEnvWellFormed
begin

(* ========================================================================== *)
(* Module-level well-typedness                                                *)
(*                                                                            *)
(* core_module_well_typed m holds when:                                       *)
(*   - CM_TypeSubst m is idempotent and capture-avoiding, and                 *)
(*   - the *normalized* module (all abstract types resolved) satisfies        *)
(*     normalized_module_well_typed: its env is well-formed, its scope        *)
(*     fields are inert, every defined global/function is declared with a     *)
(*     consistent type, and every definition typechecks.                      *)
(*                                                                            *)
(* Well-typedness is stated about normalize_module m, so clauses connecting   *)
(* a term to an abstract-typed declaration are checked *after* substitution:  *)
(* an implementation initializer 100 for a global declared x: T is checked    *)
(* against i32 once T has been resolved, never against the abstract T.        *)
(* ========================================================================== *)


(* ========================================================================== *)
(* Compile-time constant terms                                                *)
(*                                                                            *)
(* Global-variable initializers must be computable at InterpState-creation    *)
(* time without evaluating function calls, so we require them to contain no   *)
(* CoreTm_FunctionCall anywhere. References to *other* globals are allowed    *)
(* (cyclic constant dependencies are ruled out by a topological-order check   *)
(* at InterpState construction, not here). Everything else the initializer    *)
(* may not contain (e.g. quantifiers in non-ghost code) is already rejected   *)
(* by the term typechecker.                                                   *)
(* ========================================================================== *)

fun is_constant_term :: "CoreTerm \<Rightarrow> bool" where
  "is_constant_term (CoreTm_LitBool _) = True"
| "is_constant_term (CoreTm_LitInt _) = True"
| "is_constant_term (CoreTm_LitArray _ tms) = list_all is_constant_term tms"
| "is_constant_term (CoreTm_Var _) = True"
| "is_constant_term (CoreTm_Cast _ tm) = is_constant_term tm"
| "is_constant_term (CoreTm_Unop _ tm) = is_constant_term tm"
| "is_constant_term (CoreTm_Binop _ lhs rhs) =
    (is_constant_term lhs \<and> is_constant_term rhs)"
| "is_constant_term (CoreTm_Let _ rhs body) =
    (is_constant_term rhs \<and> is_constant_term body)"
| "is_constant_term (CoreTm_Quantifier _ _ _ body) = is_constant_term body"
| "is_constant_term (CoreTm_FunctionCall _ _ _) = False"
| "is_constant_term (CoreTm_VariantCtor _ _ payload) = is_constant_term payload"
| "is_constant_term (CoreTm_Record flds) =
    list_all (is_constant_term \<circ> snd) flds"
| "is_constant_term (CoreTm_RecordProj tm _) = is_constant_term tm"
| "is_constant_term (CoreTm_VariantProj tm _) = is_constant_term tm"
| "is_constant_term (CoreTm_ArrayProj arr idxs) =
    (is_constant_term arr \<and> list_all is_constant_term idxs)"
| "is_constant_term (CoreTm_Match scrut arms) =
    (is_constant_term scrut \<and> list_all (is_constant_term \<circ> snd) arms)"
| "is_constant_term (CoreTm_Sizeof tm) = is_constant_term tm"
| "is_constant_term (CoreTm_Allocated tm) = is_constant_term tm"
| "is_constant_term (CoreTm_Old tm) = is_constant_term tm"
| "is_constant_term (CoreTm_Default _) = True"


(* ========================================================================== *)
(* The body environment for checking a function definition                    *)
(*                                                                            *)
(* The module-level analogue of body_env_for (interpreter/StateMatchesEnv.thy)*)
(* generalized in two ways:                                                   *)
(*   - the module env may have unresolved abstract types, so TE_TypeVars is   *)
(*     TE_AbstractTypes env plus the function's own type parameters (rather   *)
(*     than the type parameters alone); and                                   *)
(*   - ghost functions are covered (body_env_for hard-wires NotGhost because  *)
(*     the interpreter skips ghost calls): a ghost function's parameters are  *)
(*     ghost locals and its type parameters are not runtime type variables.   *)
(*                                                                            *)
(* In the NotGhost case, the TE_RuntimeTypeVars formula is the same one used  *)
(* by tyenv_fun_ghost_constraint (CoreTyEnvWellFormed.thy) when it checks a   *)
(* non-ghost function's argument/return types for being runtime types, so     *)
(* runtime-type facts about the signature transfer directly to the body env.  *)
(*                                                                            *)
(* On a *closed* module (TE_AbstractTypes env = {||}) with a NotGhost         *)
(* function, this definition coincides field-for-field with body_env_for -    *)
(* which is why state_matches_env's body-typecheck obligation will match the  *)
(* module-level check when an InterpState is built.                           *)
(* ========================================================================== *)

definition module_body_env_for :: "CoreTyEnv \<Rightarrow> string list \<Rightarrow> FunInfo \<Rightarrow> CoreTyEnv" where
  "module_body_env_for env names info =
    env \<lparr>
      TE_LocalVars := fmap_of_list (zip names (map fst (FI_TmArgs info))),
      TE_GhostLocals := (if FI_Ghost info = Ghost then fset_of_list names else {||}),
      TE_ConstLocals := fset_of_list
        (map fst
             (filter (\<lambda>(_, vor). vor = Var) (zip names (map snd (FI_TmArgs info))))),
      TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list (FI_TyArgs info),
      TE_RuntimeTypeVars := (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                             |\<union>| (if FI_Ghost info = NotGhost
                                   then fset_of_list (FI_TyArgs info)
                                   else {||}),
      TE_ReturnType := FI_ReturnType info,
      TE_FunctionGhost := FI_Ghost info,
      TE_ProofGoal := None,
      TE_ProofTopLevel := False
    \<rparr>"


(* ========================================================================== *)
(* Clauses of normalized_module_well_typed                                    *)
(* ========================================================================== *)

(* The "current scope" fields of a module-level env hold inert,               *)
(* module-appropriate values: there are no local variables, no proof goal,    *)
(* and no enclosing function (TE_ReturnType is CoreTy_Record [] and           *)
(* TE_FunctionGhost is NotGhost by convention). These are exactly the values  *)
(* link_result (LinkModules.thy) installs. *)
definition module_scope_fields_inert :: "CoreTyEnv \<Rightarrow> bool" where
  "module_scope_fields_inert env =
    (TE_LocalVars env = fmempty
     \<and> TE_GhostLocals env = {||}
     \<and> TE_ConstLocals env = {||}
     \<and> TE_ReturnType env = CoreTy_Record []
     \<and> TE_FunctionGhost env = NotGhost
     \<and> TE_ProofGoal env = None
     \<and> TE_ProofTopLevel env = False)"

(* Every defined global is declared in TE_GlobalVars, and its initializer
   typechecks at the declared type. A non-ghost global's initializer must
   additionally be a compile-time constant (it is evaluated at
   InterpState-creation time); a ghost global's initializer is never
   evaluated, so it may be an arbitrary ghost term.
   (The converse need not hold: a global may be declared but not defined -
   that is exactly what an interface is.) *)
definition module_globals_well_typed :: "CoreTyEnv \<Rightarrow> (string, CoreTerm) fmap \<Rightarrow> bool" where
  "module_globals_well_typed env globals =
    (\<forall>name tm. fmlookup globals name = Some tm \<longrightarrow>
       (\<exists>declTy. fmlookup (TE_GlobalVars env) name = Some declTy \<and>
          (if name |\<in>| TE_GhostGlobals env
           then core_term_type env Ghost tm = Some declTy
           else is_constant_term tm \<and>
                core_term_type env NotGhost tm = Some declTy)))"

(* Every defined function is declared in TE_Functions, and the CoreFunction
   is consistent with its FunInfo: the parameter names are distinct and line
   up one-for-one with the types and Var/Ref tags in FI_TmArgs, and the body
   (if any - extern functions have CF_Body = None) typechecks in the body
   environment. (Distinctness of parameter names is required by
   fun_info_matches_interp_fun, so it must be established here for the
   InterpState-construction theorem to go through.) *)
definition module_functions_well_typed :: "CoreTyEnv \<Rightarrow> (string, CoreFunction) fmap \<Rightarrow> bool" where
  "module_functions_well_typed env funs =
    (\<forall>name f. fmlookup funs name = Some f \<longrightarrow>
       (\<exists>info. fmlookup (TE_Functions env) name = Some info \<and>
               length (CF_Args f) = length (FI_TmArgs info) \<and>
               distinct (CF_Args f) \<and>
               (case CF_Body f of
                  None \<Rightarrow> True
                | Some body \<Rightarrow>
                    core_statement_list_type
                      (module_body_env_for env (CF_Args f) info)
                      (FI_Ghost info) body \<noteq> None)))"


(* ========================================================================== *)
(* normalized_module_well_typed                                               *)
(*                                                                            *)
(* Checks an *already-normalized* module (its CM_TypeSubst is empty - that    *)
(* is the postcondition of the normalize_module it is always applied to, so   *)
(* this predicate never normalizes again). At module-check time every         *)
(* in-scope type variable is treated as a module-level abstract type          *)
(* (TE_AbstractTypes env = TE_TypeVars env) - there is no enclosing function. *)
(* For a fully-resolved module TE_TypeVars env = {||}, so this reduces to the *)
(* runtime instance of tyenv_well_formed.                                     *)
(* ========================================================================== *)

definition normalized_module_well_typed :: "CoreModule \<Rightarrow> bool" where
  "normalized_module_well_typed m =
    (TE_AbstractTypes (CM_TyEnv m) = TE_TypeVars (CM_TyEnv m)
     \<and> tyenv_well_formed (CM_TyEnv m)
     \<and> module_scope_fields_inert (CM_TyEnv m)
     \<and> module_globals_well_typed (CM_TyEnv m) (CM_GlobalVars m)
     \<and> module_functions_well_typed (CM_TyEnv m) (CM_Functions m))"


(* ========================================================================== *)
(* Capture-avoidance                                                          *)
(*                                                                            *)
(* apply_subst is a flat rewrite over CoreTy_Var with no notion of binders,   *)
(* so for normalize_module to be sound on function/ctor scopes the            *)
(* substitution's domain must avoid all bound type-parameter names: applying  *)
(* {T := tau} to a polymorphic function that uses the bare name T as one of   *)
(* its own type parameters would wrongly specialize that parameter. The       *)
(* dotted/undotted naming discipline discharges this automatically (domain    *)
(* entries are dotted abstract names; bound parameters are undotted), and it  *)
(* is preserved by linking.                                                   *)
(* ========================================================================== *)

definition capture_avoiding :: "CoreModule \<Rightarrow> bool" where
  "capture_avoiding m =
    ((\<forall>funName info.
        fmlookup (TE_Functions (CM_TyEnv m)) funName = Some info \<longrightarrow>
        fmdom (CM_TypeSubst m) |\<inter>| fset_of_list (FI_TyArgs info) = {||})
     \<and> (\<forall>ctorName dtName tyVars payload.
          fmlookup (TE_DataCtors (CM_TyEnv m)) ctorName = Some (dtName, tyVars, payload) \<longrightarrow>
          fmdom (CM_TypeSubst m) |\<inter>| fset_of_list tyVars = {||}))"

(* A module with an empty substitution is trivially capture-avoiding. *)
lemma capture_avoiding_empty_subst:
  assumes "CM_TypeSubst m = fmempty"
  shows "capture_avoiding m"
  unfolding capture_avoiding_def using assms by simp


(* ========================================================================== *)
(* core_module_well_typed                                                     *)
(* ========================================================================== *)

definition core_module_well_typed :: "CoreModule \<Rightarrow> bool" where
  "core_module_well_typed m =
    (idempotent_subst (CM_TypeSubst m)
     \<and> capture_avoiding m
     \<and> normalized_module_well_typed (normalize_module m))"


(* ========================================================================== *)
(* Properties of core_module_well_typed                                       *)
(* ========================================================================== *)

(* On a module whose substitution is already empty, well-typedness collapses
   to normalized_module_well_typed. *)
lemma core_module_well_typed_on_normalized:
  assumes "CM_TypeSubst m = fmempty"
  shows "core_module_well_typed m \<longleftrightarrow> normalized_module_well_typed m"
proof -
  have "normalize_module m = m"
    using assms normalize_module_id_when_empty by simp
  moreover have "idempotent_subst (CM_TypeSubst m)"
    using assms by simp
  moreover have "capture_avoiding m"
    using assms capture_avoiding_empty_subst by simp
  ultimately show ?thesis
    unfolding core_module_well_typed_def by simp
qed

(* Normalization preserves well-typedness. *)
lemma normalize_module_preserves_well_typed:
  assumes "core_module_well_typed m"
  shows "core_module_well_typed (normalize_module m)"
proof -
  have "normalized_module_well_typed (normalize_module m)"
    using assms unfolding core_module_well_typed_def by blast
  then show ?thesis
    using core_module_well_typed_on_normalized[OF normalized_module_has_empty_subst]
    by simp
qed

end
