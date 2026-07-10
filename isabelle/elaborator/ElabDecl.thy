theory ElabDecl
  imports ElabStmt "../core/CoreModuleTypecheck"
begin

(* The declaration-list elaborator: turns a list of BabDeclarations into a
   CoreModule.

   Declarations are elaborated one by one, folding over a state triple
   (CoreTyEnv, ElabEnv, CoreModule):

    - The CoreTyEnv is the *resolved view* of everything in scope: the imported
      context supplied by the caller, plus everything declared so far, with
      every realization of an abstract type already substituted through.
    - The ElabEnv carries the elaborator-only data (typedefs, nullary data
      constructors, void function names). Type variables in scope (module-level
      abstract types, and - locally - type parameters) are registered in
      EE_Typedefs as entries "name \<mapsto> ([], CoreTy_Var name)"; this is how
      elab_type resolves type-variable names.
    - The CoreModule accumulates this module's own declarations (CM_TyEnv) and
      definitions (CM_GlobalVars, CM_Functions, CM_TypeSubst). Unlike the state
      env, it is *not* rewritten when an abstract type is realized: it keeps
      the original (unresolved) types together with the recorded substitution,
      and the two views only meet again in normalize_module. Entries added
      after a realization are "born resolved", which is fine (resolved types
      are fixpoints of the substitution).

   The caller passes ownAbstract: the set of abstract types this module itself
   declared (empty when elaborating an interface; the interface's abstract
   types when elaborating an implementation). Only those may be realized here.

   The input list is assumed to be already in dependency order. Sorting the
   declarations - including rejecting self-referential declarations such as
   "datatype Foo = Foo1(Foo)" or a datatype whose payload mentions the abstract
   type it realizes - and the module-level checks that span both faces of a
   module are the caller's (elab_module's) job. *)


(* ========================================================================== *)
(* Empty environments                                                         *)
(* ========================================================================== *)

(* The empty module-scope type environment (satisfies tyenv_module_scope). *)
definition empty_module_tyenv :: CoreTyEnv where
  "empty_module_tyenv =
     \<lparr> TE_LocalVars = fmempty,
       TE_GlobalVars = fmempty,
       TE_GhostLocals = {||},
       TE_GhostGlobals = {||},
       TE_ConstLocals = {||},
       TE_TypeVars = {||},
       TE_RuntimeTypeVars = {||},
       TE_AbstractTypes = {||},
       TE_ReturnType = CoreTy_Record [],
       TE_FunctionGhost = NotGhost,
       TE_ProofGoal = None,
       TE_ProofTopLevel = False,
       TE_Functions = fmempty,
       TE_Datatypes = fmempty,
       TE_DataCtors = fmempty,
       TE_DataCtorsByType = fmempty,
       TE_GhostDatatypes = {||} \<rparr>"

(* The empty module: what elaboration of an empty declaration list produces. *)
definition empty_core_module :: CoreModule where
  "empty_core_module =
     \<lparr> CM_TyEnv = empty_module_tyenv,
       CM_TypeSubst = fmempty,
       CM_GlobalVars = fmempty,
       CM_Functions = fmempty \<rparr>"


(* ========================================================================== *)
(* Namespace checks                                                           *)
(* ========================================================================== *)

(* The term namespace: global constants, functions and data constructors live
   in three different maps, but a name in more than one of them would make
   term-level name resolution ambiguous, so declarations must check the whole
   namespace, not just the map they insert into. *)
definition term_name_in_scope :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> bool" where
  "term_name_in_scope env name =
     (name |\<in>| fmdom (TE_GlobalVars env)
      \<or> name |\<in>| fmdom (TE_Functions env)
      \<or> name |\<in>| fmdom (TE_DataCtors env))"

(* The type namespace: typedefs, datatypes and abstract types (type variables).
   Note fmdom (EE_Typedefs elabEnv) includes the in-scope type variables (see
   the EE_Typedefs convention above) and also any already-realized abstract
   types - which is what rejects a *second* realization of the same name (it
   is no longer in TE_TypeVars, so it looks like a plain typedef, and clashes
   here). *)
definition type_name_in_scope :: "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> string \<Rightarrow> bool" where
  "type_name_in_scope env elabEnv name =
     (name |\<in>| fmdom (EE_Typedefs elabEnv)
      \<or> name |\<in>| fmdom (TE_Datatypes env)
      \<or> name |\<in>| TE_TypeVars env)"


(* ========================================================================== *)
(* Capture-avoidance checks                                                   *)
(* ========================================================================== *)

(* Core type substitution (apply_subst) is a flat, binder-blind rewrite, so
   the module's accumulated type substitution must never touch a name that is
   used as a bound type parameter. After renaming this holds automatically
   (abstract types are dotted, type parameters are undotted), but the
   elaborator checks it explicitly, so that hand-constructed input fails with
   a well-located error instead of producing an ill-formed module. The check
   runs in both directions, since realizations and type-parameter binders may
   arrive in either order. *)

(* A new binder (type-parameter list of a function, datatype or typedef) must
   avoid the abstract types in scope (the body env unions the parameters in,
   so a collision would silently alias the abstract type) and the names of the
   module's accumulated substitution. *)
definition binder_captures :: "CoreTyEnv \<Rightarrow> CoreModule \<Rightarrow> string list \<Rightarrow> bool" where
  "binder_captures env m tyvars =
     (fset_of_list tyvars |\<inter>| (TE_TypeVars env |\<union>| subst_names (CM_TypeSubst m)) \<noteq> {||})"

(* All type-parameter names bound anywhere in scope: function type parameters,
   datatype constructor type parameters, and typedef parameters (typedef
   ranges are rewritten when a realization is applied, so their parameters can
   be captured too). *)
definition scope_bound_tyvars :: "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> string fset" where
  "scope_bound_tyvars env elabEnv =
     ffUnion ((\<lambda>info. fset_of_list (FI_TyArgs info)) |`| fmran (TE_Functions env))
     |\<union>| ffUnion ((\<lambda>(_, tyVars, _). fset_of_list tyVars) |`| fmran (TE_DataCtors env))
     |\<union>| ffUnion ((\<lambda>(tyVars, _). fset_of_list tyVars) |`| fmran (EE_Typedefs elabEnv))"

(* A new realization "name \<mapsto> target" must keep both its domain and the type
   variables of its range away from every bound type parameter in scope. *)
definition realization_captures :: "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> string \<Rightarrow> CoreType \<Rightarrow> bool" where
  "realization_captures env elabEnv name target =
     (finsert name (fset_of_list (type_tyvars_list target))
        |\<inter>| scope_bound_tyvars env elabEnv \<noteq> {||})"


(* ========================================================================== *)
(* Environment-extension helpers                                              *)
(* ========================================================================== *)

(* Register a list of type parameters in the typedef table: each maps to its
   own CoreTy_Var. Parameters shadow any existing entry of the same name (but
   the capture checks reject such collisions anyway). *)
definition tyvar_typedef_entries :: "string list \<Rightarrow> Typedefs \<Rightarrow> Typedefs" where
  "tyvar_typedef_entries tyvars tds =
     fold (\<lambda>v. fmupd v ([], CoreTy_Var v)) tyvars tds"

definition tyenv_add_global :: "string \<Rightarrow> CoreType \<Rightarrow> GhostOrNot \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv" where
  "tyenv_add_global name ty ghost env =
     env \<lparr> TE_GlobalVars := fmupd name ty (TE_GlobalVars env),
           TE_GhostGlobals := (if ghost = Ghost then finsert name (TE_GhostGlobals env)
                               else TE_GhostGlobals env) \<rparr>"

definition tyenv_add_function :: "string \<Rightarrow> FunInfo \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv" where
  "tyenv_add_function name info env =
     env \<lparr> TE_Functions := fmupd name info (TE_Functions env) \<rparr>"

(* A module-level abstract type is a top-level type variable; it is a runtime
   type variable exactly when it was declared without `ghost`. *)
definition tyenv_add_abstract_type :: "string \<Rightarrow> GhostOrNot \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv" where
  "tyenv_add_abstract_type name ghost env =
     env \<lparr> TE_TypeVars := finsert name (TE_TypeVars env),
           TE_RuntimeTypeVars := (if ghost = NotGhost
                                  then finsert name (TE_RuntimeTypeVars env)
                                  else TE_RuntimeTypeVars env),
           TE_AbstractTypes := finsert name (TE_AbstractTypes env) \<rparr>"

(* Add a datatype: its arity, its constructors (with the given payload types),
   the by-type constructor list, and (if computed ghost) the ghost marker. *)
definition tyenv_add_datatype ::
  "string \<Rightarrow> string list \<Rightarrow> (string \<times> CoreType) list \<Rightarrow> bool \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv" where
  "tyenv_add_datatype name tyvars ctors isGhost env =
     env \<lparr> TE_Datatypes := fmupd name (length tyvars) (TE_Datatypes env),
           TE_DataCtors := fold (\<lambda>(cn, payload). fmupd cn (name, tyvars, payload))
                                ctors (TE_DataCtors env),
           TE_DataCtorsByType := fmupd name (map fst ctors) (TE_DataCtorsByType env),
           TE_GhostDatatypes := (if isGhost then finsert name (TE_GhostDatatypes env)
                                 else TE_GhostDatatypes env) \<rparr>"


(* ========================================================================== *)
(* Applying a realization                                                     *)
(* ========================================================================== *)

(* Record a realization "name \<mapsto> target" of an abstract type, and make it
   visible to all later declarations. Later declarations must see through the
   realization (e.g. after "type T = i32;", a use of a previously-declared
   "x: T" must agree with freshly-elaborated occurrences of i32), so:

    - the module's substitution gains the new entry, with the new binding
      first substituted through the existing ranges (this keeps chains
      working and keeps the substitution idempotent by construction);
    - the typedef table likewise: the entry for name (previously
      ([], CoreTy_Var name)) is replaced by ([], target), so later occurrences
      of name elaborate directly to target, and existing ranges are rewritten;
    - the state env drops name from its type-variable fields (it is no longer
      abstract, as far as this elaboration is concerned) and has the
      substitution applied to all recorded signatures.

   The module's own CM_TyEnv is deliberately NOT rewritten (and, the caller
   having checked ownAbstract, name is not in its TE_TypeVars, which belongs
   to the interface that declared it): the module keeps unresolved types plus
   the substitution, and normalize_module applies it. *)
definition apply_realization ::
  "string \<Rightarrow> CoreType \<Rightarrow> CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> CoreModule
   \<Rightarrow> CoreTyEnv \<times> ElabEnv \<times> CoreModule" where
  "apply_realization name target env elabEnv m =
     (let s = fmupd name target fmempty;
          env' = (apply_subst_to_tyenv s env)
                   \<lparr> TE_TypeVars := TE_TypeVars env |-| {|name|},
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |-| {|name|},
                     TE_AbstractTypes := TE_AbstractTypes env |-| {|name|} \<rparr>;
          elabEnv' = elabEnv
                   \<lparr> EE_Typedefs := fmupd name ([], target)
                       (fmmap (\<lambda>(tyvars, ty). (tyvars, apply_subst s ty))
                              (EE_Typedefs elabEnv)) \<rparr>;
          m' = m \<lparr> CM_TypeSubst := fmupd name target
                       (fmmap (apply_subst s) (CM_TypeSubst m)) \<rparr>
      in (env', elabEnv', m'))"


(* ========================================================================== *)
(* Constants                                                                  *)
(* ========================================================================== *)

(* Elaborate a global-constant initializer against a known declared type:
   coerce the rhs to the declared type, clear leftover metavariables, and
   check the compile-time-constant restriction on non-ghost initializers
   (ghost initializers are never evaluated, so they may be arbitrary ghost
   terms). *)
definition elab_const_rhs ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> CoreType \<Rightarrow> BabTerm
   \<Rightarrow> TypeError list + CoreTerm" where
  "elab_const_rhs env elabEnv ghost loc declTy rhs =
    (case elab_term env elabEnv ghost rhs 0 of
       Inl errs \<Rightarrow> Inl errs
     | Inr (coreTm, rhsTy, next_mv) \<Rightarrow>
         (case coerce_term_to_type env loc coreTm rhsTy declTy of
            Inl errs \<Rightarrow> Inl errs
          | Inr coreTm' \<Rightarrow>
              (let finalTm = clear_metavars 0 next_mv coreTm'
               in if ghost = NotGhost \<and> \<not> is_constant_term finalTm
                  then Inl [TyErr_NotCompileTimeConstant loc]
                  else Inr finalTm)))"

(* As elab_const_rhs, but with no declared type: the constant's type is the
   inferred rhs type, which must be free of unresolved metavariables (and must
   be a runtime type for a non-ghost constant). *)
definition elab_const_rhs_infer ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> BabTerm
   \<Rightarrow> TypeError list + (CoreTerm \<times> CoreType)" where
  "elab_const_rhs_infer env elabEnv ghost loc rhs =
    (case elab_term env elabEnv ghost rhs 0 of
       Inl errs \<Rightarrow> Inl errs
     | Inr (coreTm, rhsTy, next_mv) \<Rightarrow>
         if \<not> list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)
         then Inl [TyErr_CannotInferType loc]
         else if ghost = NotGhost \<and> \<not> is_runtime_type env rhsTy
         then Inl [TyErr_GhostTypeInNonGhost loc]
         else
           (let finalTm = clear_metavars 0 next_mv coreTm
            in if ghost = NotGhost \<and> \<not> is_constant_term finalTm
               then Inl [TyErr_NotCompileTimeConstant loc]
               else Inr (finalTm, rhsTy)))"

(* Elaborate a `const` declaration. Three cases:
    - no value: a declaration without a definition (the interface case) - the
      type annotation is then required;
    - a value for a name already declared (in scope): a definition of a
      previously-declared constant - only CM_GlobalVars gains an entry (the
      declaration lives in the module that declared it; re-declaring it here
      would make linking the two a conflict), and the ghost marker and any
      type annotation must match the declaration;
    - a value for a fresh name: declaring and defining at once. *)
definition elab_const_decl ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> CoreModule \<Rightarrow> DeclConst
   \<Rightarrow> TypeError list + (CoreTyEnv \<times> ElabEnv \<times> CoreModule)" where
  "elab_const_decl env elabEnv m dc =
    (let loc = DC_Location dc; name = DC_Name dc; ghost = DC_Ghost dc
     in case DC_Value dc of
          None \<Rightarrow>
            (if term_name_in_scope env name then Inl [TyErr_DuplicateName loc name]
             else case DC_Type dc of
                    None \<Rightarrow> Inl [TyErr_ConstDeclNeedsType loc name]
                  | Some ty \<Rightarrow>
                      (case elab_type env elabEnv ghost ty of
                         Inl errs \<Rightarrow> Inl errs
                       | Inr coreTy \<Rightarrow>
                           Inr (tyenv_add_global name coreTy ghost env,
                                elabEnv,
                                m \<lparr> CM_TyEnv := tyenv_add_global name coreTy ghost (CM_TyEnv m) \<rparr>)))
        | Some rhs \<Rightarrow>
            (case fmlookup (TE_GlobalVars env) name of
               Some declTy \<Rightarrow>
                 \<comment> \<open>Definition of a previously-declared constant.\<close>
                 (if name |\<in>| fmdom (CM_GlobalVars m)
                  then Inl [TyErr_AlreadyDefined loc name]
                  else if (name |\<in>| TE_GhostGlobals env) \<noteq> (ghost = Ghost)
                  then Inl [TyErr_GhostMismatch loc name]
                  else
                    (case (case DC_Type dc of
                             None \<Rightarrow> Inr declTy
                           | Some ty \<Rightarrow>
                               (case elab_type env elabEnv ghost ty of
                                  Inl errs \<Rightarrow> Inl errs
                                | Inr coreTy \<Rightarrow>
                                    if coreTy \<noteq> declTy
                                    then Inl [TyErr_TypeMismatch loc declTy coreTy]
                                    else Inr declTy)) of
                       Inl errs \<Rightarrow> Inl errs
                     | Inr _ \<Rightarrow>
                         (case elab_const_rhs env elabEnv ghost loc declTy rhs of
                            Inl errs \<Rightarrow> Inl errs
                          | Inr finalTm \<Rightarrow>
                              Inr (env, elabEnv,
                                   m \<lparr> CM_GlobalVars := fmupd name finalTm (CM_GlobalVars m) \<rparr>))))
             | None \<Rightarrow>
                 \<comment> \<open>Declaring and defining at once.\<close>
                 (if term_name_in_scope env name then Inl [TyErr_DuplicateName loc name]
                  else case DC_Type dc of
                         None \<Rightarrow>
                           (case elab_const_rhs_infer env elabEnv ghost loc rhs of
                              Inl errs \<Rightarrow> Inl errs
                            | Inr (finalTm, declTy) \<Rightarrow>
                                Inr (tyenv_add_global name declTy ghost env,
                                     elabEnv,
                                     m \<lparr> CM_TyEnv := tyenv_add_global name declTy ghost (CM_TyEnv m),
                                         CM_GlobalVars := fmupd name finalTm (CM_GlobalVars m) \<rparr>))
                       | Some ty \<Rightarrow>
                           (case elab_type env elabEnv ghost ty of
                              Inl errs \<Rightarrow> Inl errs
                            | Inr declTy \<Rightarrow>
                                (case elab_const_rhs env elabEnv ghost loc declTy rhs of
                                   Inl errs \<Rightarrow> Inl errs
                                 | Inr finalTm \<Rightarrow>
                                     Inr (tyenv_add_global name declTy ghost env,
                                          elabEnv,
                                          m \<lparr> CM_TyEnv := tyenv_add_global name declTy ghost (CM_TyEnv m),
                                              CM_GlobalVars := fmupd name finalTm (CM_GlobalVars m) \<rparr>))))))"


(* ========================================================================== *)
(* Functions                                                                  *)
(* ========================================================================== *)

(* Elaborate a function's signature to a FunInfo. The argument and return
   types are elaborated with the function's type parameters in scope; for a
   non-ghost function they are elaborated in NotGhost mode with the type
   parameters as runtime type variables, which enforces that all argument and
   return types are runtime types (the tyenv_fun_ghost_constraint and
   tyenv_return_type_runtime conditions). A missing return type means the
   function was declared void; its Core return type is unit. *)
definition elab_fun_signature ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> DeclFun \<Rightarrow> TypeError list + FunInfo" where
  "elab_fun_signature env elabEnv df =
    (let ghost = DF_Ghost df;
         tyvars = DF_TyArgs df;
         sigEnv = env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list tyvars,
                        TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>|
                          (if ghost = NotGhost then fset_of_list tyvars else {||}) \<rparr>;
         sigElabEnv = elabEnv \<lparr> EE_Typedefs :=
                          tyvar_typedef_entries tyvars (EE_Typedefs elabEnv) \<rparr>
     in case elab_type_list sigEnv sigElabEnv ghost (map (\<lambda>(_, _, ty). ty) (DF_TmArgs df)) of
          Inl errs \<Rightarrow> Inl errs
        | Inr argTys \<Rightarrow>
            (case (case DF_ReturnType df of
                     None \<Rightarrow> Inr (CoreTy_Record [])
                   | Some rty \<Rightarrow> elab_type sigEnv sigElabEnv ghost rty) of
               Inl errs \<Rightarrow> Inl errs
             | Inr retTy \<Rightarrow>
                 Inr \<lparr> FI_TyArgs = tyvars,
                       FI_TmArgs = zip argTys (map (\<lambda>(_, vor, _). vor) (DF_TmArgs df)),
                       FI_ReturnType = retTy,
                       FI_Ghost = ghost,
                       FI_Impure = DF_Impure df \<rparr>))"

(* Typecheck a function's contract attributes and drop the results: FunInfo
   and CoreFunction have no contract fields yet, so this exists purely to flag
   type errors (verification is out of scope for now). Requires and decreases
   terms are elaborated in preEnv (the body env); ensures terms in postEnv
   (the body env plus the `return` binding, for non-void functions). All are
   elaborated in Ghost mode. An `invariant` attribute is not valid on a
   function. *)
fun elab_fun_contracts ::
  "CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> BabAttribute list \<Rightarrow> nat
   \<Rightarrow> TypeError list + nat" where
  "elab_fun_contracts preEnv postEnv elabEnv [] next_mv = Inr next_mv"
| "elab_fun_contracts preEnv postEnv elabEnv (BabAttr_Requires loc tm # rest) next_mv =
    (case elab_term preEnv elabEnv Ghost tm next_mv of
       Inl errs \<Rightarrow> Inl errs
     | Inr (_, ty, next_mv') \<Rightarrow>
         (case unify (\<lambda>n. n |\<notin>| TE_TypeVars preEnv) ty CoreTy_Bool of
            None \<Rightarrow> Inl [TyErr_TypeMismatch loc CoreTy_Bool ty]
          | Some _ \<Rightarrow> elab_fun_contracts preEnv postEnv elabEnv rest next_mv'))"
| "elab_fun_contracts preEnv postEnv elabEnv (BabAttr_Ensures loc tm # rest) next_mv =
    (case elab_term postEnv elabEnv Ghost tm next_mv of
       Inl errs \<Rightarrow> Inl errs
     | Inr (_, ty, next_mv') \<Rightarrow>
         (case unify (\<lambda>n. n |\<notin>| TE_TypeVars postEnv) ty CoreTy_Bool of
            None \<Rightarrow> Inl [TyErr_TypeMismatch loc CoreTy_Bool ty]
          | Some _ \<Rightarrow> elab_fun_contracts preEnv postEnv elabEnv rest next_mv'))"
| "elab_fun_contracts preEnv postEnv elabEnv (BabAttr_Invariant loc _ # rest) next_mv =
    Inl [TyErr_InvalidFunctionAttribute loc]"
| "elab_fun_contracts preEnv postEnv elabEnv (BabAttr_Decreases loc tm # rest) next_mv =
    (case elab_term preEnv elabEnv Ghost tm next_mv of
       Inl errs \<Rightarrow> Inl errs
     | Inr (_, ty, next_mv') \<Rightarrow>
         if \<not> is_valid_decreases_type ty
         then Inl [TyErr_InvalidDecreasesType loc ty]
         else elab_fun_contracts preEnv postEnv elabEnv rest next_mv')"

(* Typecheck a function's contracts and (if present) its body, returning the
   elaborated body for CF_Body. env must already contain the function's own
   declaration. The body env is module_body_env_for - the same env in which
   module-level typechecking will re-check the recorded body. *)
definition elab_fun_body_and_contracts ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> DeclFun \<Rightarrow> FunInfo
   \<Rightarrow> TypeError list + CoreStatement list option" where
  "elab_fun_body_and_contracts env elabEnv df funInfo =
    (let paramNames = map (\<lambda>(n, _, _). n) (DF_TmArgs df);
         bodyEnv = module_body_env_for env paramNames funInfo;
         bodyElabEnv = elabEnv
           \<lparr> EE_Typedefs := tyvar_typedef_entries (DF_TyArgs df) (EE_Typedefs elabEnv),
             EE_CurrentFunctionVoid := (DF_ReturnType df = None) \<rparr>;
         postEnv = (if DF_ReturnType df = None then bodyEnv
                    else vardecl_add_local bodyEnv Ghost ''return'' (FI_ReturnType funInfo))
     in case elab_fun_contracts bodyEnv postEnv bodyElabEnv (DF_Attributes df) 0 of
          Inl errs \<Rightarrow> Inl errs
        | Inr _ \<Rightarrow>
            (case DF_Body df of
               None \<Rightarrow> Inr None
             | Some body \<Rightarrow>
                 (case elab_statement_list bodyEnv bodyElabEnv (DF_Ghost df) body 0 of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr (coreBody, _, _) \<Rightarrow> Inr (Some coreBody))))"

(* Elaborate a function declaration. A function with a body, or marked extern,
   is a *definition* (an extern function's CF_Body is None; its implementation
   arrives when an interpreter state is built); a bodiless non-extern function
   is a declaration only. Defining a previously-declared function requires the
   FunInfo to match the declaration *literally* - including the type-parameter
   names (alpha-renaming is not accepted) and the ghost/impure flags - plus
   agreement on Babylon-level voidness, which is not recoverable from the Core
   return type. As with constants, such a definition adds no new declaration
   to the module's own type env. *)
definition elab_function_decl ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> CoreModule \<Rightarrow> DeclFun
   \<Rightarrow> TypeError list + (CoreTyEnv \<times> ElabEnv \<times> CoreModule)" where
  "elab_function_decl env elabEnv m df =
    (let loc = DF_Location df; name = DF_Name df;
         paramNames = map (\<lambda>(n, _, _). n) (DF_TmArgs df);
         isDefinition = (DF_Extern df \<or> DF_Body df \<noteq> None);
         isVoid = (DF_ReturnType df = None)
     in case first_duplicate_name (\<lambda>x. x) (DF_TyArgs df) of
          Some dup \<Rightarrow> Inl [TyErr_DuplicateName loc dup]
        | None \<Rightarrow>
        (case first_duplicate_name (\<lambda>(n, _, _). n) (DF_TmArgs df) of
           Some dup \<Rightarrow> Inl [TyErr_DuplicateName loc dup]
         | None \<Rightarrow>
           if binder_captures env m (DF_TyArgs df)
           then Inl [TyErr_TypeVarCapture loc name]
           else if DF_Extern df \<and> DF_Body df \<noteq> None
           then Inl [TyErr_ExternFunctionWithBody loc name]
           else
             (case elab_fun_signature env elabEnv df of
                Inl errs \<Rightarrow> Inl errs
              | Inr funInfo \<Rightarrow>
                  (case fmlookup (TE_Functions env) name of
                     Some declInfo \<Rightarrow>
                       \<comment> \<open>Already declared: this must be a matching definition.\<close>
                       (if \<not> isDefinition then Inl [TyErr_DuplicateName loc name]
                        else if name |\<in>| fmdom (CM_Functions m)
                        then Inl [TyErr_AlreadyDefined loc name]
                        else if funInfo \<noteq> declInfo
                        then Inl [TyErr_FunctionSignatureMismatch loc name]
                        else if (name |\<in>| EE_VoidFunctions elabEnv) \<noteq> isVoid
                        then Inl [TyErr_FunctionSignatureMismatch loc name]
                        else
                          (case elab_fun_body_and_contracts env elabEnv df funInfo of
                             Inl errs \<Rightarrow> Inl errs
                           | Inr bodyOpt \<Rightarrow>
                               Inr (env, elabEnv,
                                    m \<lparr> CM_Functions :=
                                          fmupd name \<lparr> CF_Args = paramNames, CF_Body = bodyOpt \<rparr>
                                                (CM_Functions m) \<rparr>)))
                   | None \<Rightarrow>
                       (if term_name_in_scope env name then Inl [TyErr_DuplicateName loc name]
                        else
                          (let env' = tyenv_add_function name funInfo env;
                               elabEnv' = (if isVoid
                                           then elabEnv \<lparr> EE_VoidFunctions :=
                                                  finsert name (EE_VoidFunctions elabEnv) \<rparr>
                                           else elabEnv);
                               m' = m \<lparr> CM_TyEnv := tyenv_add_function name funInfo (CM_TyEnv m) \<rparr>
                           in case elab_fun_body_and_contracts env' elabEnv' df funInfo of
                                Inl errs \<Rightarrow> Inl errs
                              | Inr bodyOpt \<Rightarrow>
                                  Inr (env', elabEnv',
                                       (if isDefinition
                                        then m' \<lparr> CM_Functions :=
                                                    fmupd name \<lparr> CF_Args = paramNames,
                                                                 CF_Body = bodyOpt \<rparr>
                                                          (CM_Functions m') \<rparr>
                                        else m'))))))))"


(* ========================================================================== *)
(* Datatypes                                                                  *)
(* ========================================================================== *)

(* Elaborate a datatype's constructors: per constructor, its name, Core
   payload type, and whether it was declared without a payload ("nullary").
   Payload types are elaborated in Ghost mode - a non-runtime payload is
   not an error, it just makes the datatype ghost (computed below). A
   missing payload is unit. Note that `C` and `C{}` both get a unit
   payload type, but only the former is nullary: `C` is used bare, while
   `C{}` must be applied to an (empty-record) argument. *)
fun elab_data_ctors ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> DataCtor list
   \<Rightarrow> TypeError list + (string \<times> CoreType \<times> bool) list" where
  "elab_data_ctors env elabEnv [] = Inr []"
| "elab_data_ctors env elabEnv ((cloc, cname, payloadOpt) # rest) =
    (case (case payloadOpt of
             None \<Rightarrow> Inr (CoreTy_Record [])
           | Some ty \<Rightarrow> elab_type env elabEnv Ghost ty) of
       Inl errs \<Rightarrow> Inl errs
     | Inr payloadTy \<Rightarrow>
         (case elab_data_ctors env elabEnv rest of
            Inl errs \<Rightarrow> Inl errs
          | Inr rest' \<Rightarrow> Inr ((cname, payloadTy, payloadOpt = None) # rest')))"

(* Elaborate a datatype declaration.

   Ghost status is computed, not declared: the payloads are elaborated with
   the datatype's own type parameters added to both TE_TypeVars and
   TE_RuntimeTypeVars (exactly the env in which tyenv_nonghost_payloads_runtime
   checks them), and the datatype is ghost iff some payload is not a runtime
   type there. No fixpoint is needed: declarations arrive in dependency order,
   so every datatype mentioned in a payload already has its ghost status
   settled in the state env.

   If the datatype's name is an abstract type in scope, the declaration also
   *realizes* it (the ADT pattern: interface "type Stack;", implementation
   "datatype Stack = ..."), recording name \<mapsto> CoreTy_Datatype name []. Such a
   datatype must have no type parameters (abstract types are zero-arity), and
   if the abstract type was declared non-ghost, the datatype must compute
   non-ghost. *)
definition elab_datatype_decl ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> string fset \<Rightarrow> CoreModule \<Rightarrow> DeclDatatype
   \<Rightarrow> TypeError list + (CoreTyEnv \<times> ElabEnv \<times> CoreModule)" where
  "elab_datatype_decl env elabEnv ownAbstract m dd =
    (let loc = DD_Location dd; name = DD_Name dd; tyvars = DD_TyArgs dd;
         isRealization = (name |\<in>| TE_TypeVars env)
     in if isRealization \<and> name |\<notin>| ownAbstract
        then Inl [TyErr_CannotRealizeImportedType loc name]
        else if isRealization \<and> tyvars \<noteq> []
        then Inl [TyErr_TypeArgsNotAllowed loc name]
        else if isRealization \<and> name |\<in>| fmdom (TE_Datatypes env)
        then Inl [TyErr_DuplicateName loc name]
        else if \<not> isRealization \<and> type_name_in_scope env elabEnv name
        then Inl [TyErr_DuplicateName loc name]
        else if DD_Ctors dd = [] then Inl [TyErr_EmptyDatatype loc name]
        else
          (case first_duplicate_name (\<lambda>x. x) tyvars of
             Some dup \<Rightarrow> Inl [TyErr_DuplicateName loc dup]
           | None \<Rightarrow>
             if binder_captures env m tyvars then Inl [TyErr_TypeVarCapture loc name]
             else
               (case first_duplicate_name (\<lambda>(_, n, _). n) (DD_Ctors dd) of
                  Some dup \<Rightarrow> Inl [TyErr_DuplicateName loc dup]
                | None \<Rightarrow>
                  (case find (\<lambda>(_, n, _). term_name_in_scope env n) (DD_Ctors dd) of
                     Some (cloc, cname, _) \<Rightarrow> Inl [TyErr_DuplicateName cloc cname]
                   | None \<Rightarrow>
                       (let payloadEnv = env
                              \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyvars,
                                TE_RuntimeTypeVars :=
                                  (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                  |\<union>| fset_of_list tyvars \<rparr>;
                            payloadElabEnv = elabEnv
                              \<lparr> EE_Typedefs :=
                                  tyvar_typedef_entries tyvars (EE_Typedefs elabEnv) \<rparr>
                        in case elab_data_ctors payloadEnv payloadElabEnv (DD_Ctors dd) of
                             Inl errs \<Rightarrow> Inl errs
                           | Inr ctorInfo \<Rightarrow>
                               (let isGhost = \<not> list_all
                                       (\<lambda>(_, payloadTy, _). is_runtime_type payloadEnv payloadTy)
                                       ctorInfo
                                in if isRealization \<and> name |\<in>| TE_RuntimeTypeVars env \<and> isGhost
                                   then Inl [TyErr_GhostRealizationOfRuntimeType loc name]
                                   else if isRealization \<and>
                                        realization_captures env elabEnv name
                                          (CoreTy_Datatype name [])
                                   then Inl [TyErr_TypeVarCapture loc name]
                                   else
                                     (let ctors = map (\<lambda>(cn, payload, _). (cn, payload)) ctorInfo;
                                          env1 = tyenv_add_datatype name tyvars ctors isGhost env;
                                          elabEnv1 = elabEnv
                                            \<lparr> EE_NullaryDataCtors :=
                                                fset_of_list
                                                  (map fst (filter (\<lambda>(_, _, isNullary). isNullary) ctorInfo))
                                                |\<union>| EE_NullaryDataCtors elabEnv \<rparr>;
                                          m1 = m \<lparr> CM_TyEnv :=
                                                     tyenv_add_datatype name tyvars ctors isGhost
                                                       (CM_TyEnv m) \<rparr>
                                      in if isRealization
                                         then Inr (apply_realization name
                                                     (CoreTy_Datatype name []) env1 elabEnv1 m1)
                                         else Inr (env1, elabEnv1, m1))))))))"


(* ========================================================================== *)
(* Typedefs                                                                   *)
(* ========================================================================== *)

(* Elaborate a typedef declaration. Four cases:
    - extern types are not currently supported;
    - the name is an abstract type in scope: this is a *realization* - legal
      only for the module's own abstract types, with no type arguments. If the
      abstract type was declared non-ghost, the target must be a runtime type
      (realizing a *ghost* abstract type by a runtime type is a sound
      weakening and is allowed). A target that mentions the name being
      realized is a cyclic definition (e.g. "type T = U; type U = T;" - the
      second target elaborates to a type mentioning U itself);
    - no definition: a new abstract type ("type T;" / "ghost type T;"),
      necessarily zero-arity;
    - otherwise: an ordinary transparent typedef, resolved entirely on the
      elaborator side (it enters EE_Typedefs and never reaches the
      CoreModule). *)
definition elab_typedef_decl ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> string fset \<Rightarrow> CoreModule \<Rightarrow> DeclTypedef
   \<Rightarrow> TypeError list + (CoreTyEnv \<times> ElabEnv \<times> CoreModule)" where
  "elab_typedef_decl env elabEnv ownAbstract m dt =
    (let loc = DT_Location dt; name = DT_Name dt; tyvars = DT_TyArgs dt
     in if DT_Extern dt then Inl [TyErr_ExternTypeNotImplemented loc]
        else if name |\<in>| TE_TypeVars env then
          \<comment> \<open>The name is an abstract type in scope: this must be a realization.\<close>
          (if name |\<notin>| ownAbstract then Inl [TyErr_CannotRealizeImportedType loc name]
           else case DT_Definition dt of
                  None \<Rightarrow> Inl [TyErr_DuplicateName loc name]
                | Some ty \<Rightarrow>
                    if tyvars \<noteq> [] then Inl [TyErr_TypeArgsNotAllowed loc name]
                    else
                      (case elab_type env elabEnv Ghost ty of
                         Inl errs \<Rightarrow> Inl errs
                       | Inr target \<Rightarrow>
                           if name \<in> type_tyvars target
                           then Inl [TyErr_SelfReferentialType loc name]
                           else if name |\<in>| TE_RuntimeTypeVars env
                                \<and> \<not> is_runtime_type env target
                           then Inl [TyErr_GhostRealizationOfRuntimeType loc name]
                           else if realization_captures env elabEnv name target
                           then Inl [TyErr_TypeVarCapture loc name]
                           else Inr (apply_realization name target env elabEnv m)))
        else if type_name_in_scope env elabEnv name then Inl [TyErr_DuplicateName loc name]
        else case DT_Definition dt of
               None \<Rightarrow>
                 \<comment> \<open>A new abstract type.\<close>
                 (if tyvars \<noteq> [] then Inl [TyErr_TypeArgsNotAllowed loc name]
                  else
                    Inr (tyenv_add_abstract_type name (DT_Ghost dt) env,
                         elabEnv \<lparr> EE_Typedefs :=
                             fmupd name ([], CoreTy_Var name) (EE_Typedefs elabEnv) \<rparr>,
                         m \<lparr> CM_TyEnv :=
                               tyenv_add_abstract_type name (DT_Ghost dt) (CM_TyEnv m) \<rparr>))
             | Some ty \<Rightarrow>
                 \<comment> \<open>An ordinary transparent typedef.\<close>
                 (case first_duplicate_name (\<lambda>x. x) tyvars of
                    Some dup \<Rightarrow> Inl [TyErr_DuplicateName loc dup]
                  | None \<Rightarrow>
                      if binder_captures env m tyvars
                      then Inl [TyErr_TypeVarCapture loc name]
                      else
                        (let tdEnv = env \<lparr> TE_TypeVars :=
                                             TE_TypeVars env |\<union>| fset_of_list tyvars \<rparr>;
                             tdElabEnv = elabEnv \<lparr> EE_Typedefs :=
                                             tyvar_typedef_entries tyvars (EE_Typedefs elabEnv) \<rparr>
                         in case elab_type tdEnv tdElabEnv Ghost ty of
                              Inl errs \<Rightarrow> Inl errs
                            | Inr target \<Rightarrow>
                                Inr (env,
                                     elabEnv \<lparr> EE_Typedefs :=
                                         fmupd name (tyvars, target) (EE_Typedefs elabEnv) \<rparr>,
                                     m))))"


(* ========================================================================== *)
(* The main fold                                                              *)
(* ========================================================================== *)

fun elab_declaration ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> string fset \<Rightarrow> CoreModule \<Rightarrow> BabDeclaration
   \<Rightarrow> TypeError list + (CoreTyEnv \<times> ElabEnv \<times> CoreModule)" where
  "elab_declaration env elabEnv ownAbstract m (BabDecl_Const dc) =
     elab_const_decl env elabEnv m dc"
| "elab_declaration env elabEnv ownAbstract m (BabDecl_Function df) =
     elab_function_decl env elabEnv m df"
| "elab_declaration env elabEnv ownAbstract m (BabDecl_Datatype dd) =
     elab_datatype_decl env elabEnv ownAbstract m dd"
| "elab_declaration env elabEnv ownAbstract m (BabDecl_Typedef dt) =
     elab_typedef_decl env elabEnv ownAbstract m dt"

(* Elaborate a declaration list, threading the state triple and stopping at
   the first failing declaration. *)
fun elab_declaration_list ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> string fset \<Rightarrow> CoreModule \<Rightarrow> BabDeclaration list
   \<Rightarrow> TypeError list + (CoreTyEnv \<times> ElabEnv \<times> CoreModule)" where
  "elab_declaration_list env elabEnv ownAbstract m [] = Inr (env, elabEnv, m)"
| "elab_declaration_list env elabEnv ownAbstract m (d # ds) =
    (case elab_declaration env elabEnv ownAbstract m d of
       Inl errs \<Rightarrow> Inl errs
     | Inr (env', elabEnv', m') \<Rightarrow>
         elab_declaration_list env' elabEnv' ownAbstract m' ds)"

(* Top-level entry point: elaborate a (dependency-ordered) declaration list in
   the given context, producing the elaborated CoreModule and the final
   ElabEnv (from which the module's exported elaborator-level data is read). *)
definition elab_declarations ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> string fset \<Rightarrow> BabDeclaration list
   \<Rightarrow> TypeError list + (CoreModule \<times> ElabEnv)" where
  "elab_declarations env elabEnv ownAbstract decls =
    (case elab_declaration_list env elabEnv ownAbstract empty_core_module decls of
       Inl errs \<Rightarrow> Inl errs
     | Inr (_, elabEnv', m) \<Rightarrow> Inr (m, elabEnv'))"

end
