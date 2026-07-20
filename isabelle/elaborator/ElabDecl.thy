theory ElabDecl
  imports ElabStmt ConstFold "../core/CoreModuleTypecheck"
begin

(* Declaration elaborator.

   elab_declaration elaborates a single BabDeclaration:
     Inputs:
      - CoreTyEnv, containing the imported declarations, plus the types of
        everything declared so far in this module. Abstract type realizations
        are already substituted through.
  
      - ElabEnv, containing elaborator-only data (typedefs, etc).
         - Abstract types are represented here, as entries "name \<mapsto> ([], CoreTy_Var name)",
           which allows elab_type to resolve them.

      - ownAbstract, the set of abstract types that are allowed to be resolved here
        (empty when elaborating the interface, and when elaborating the implementation,
        contains the abstract types declared in the interface).

      - ctxGlobals, the values of globals imported from other modules (if visible) - this
        is needed for compile-time constant evaluation.

      - A CoreModule, containing the module's own declarations and definitions so far.
        Unlike the above CoreTyEnv, abstract types are *not* necessarily fully substituted
        here; instead, they are resolved lazily by normalize_module.

     Outputs:
      - The updated CoreTyEnv, ElabEnv and CoreModule, containing the new elaborated
        declaration; or a list of TypeErrors.

   elab_declarations elaborates a list of BabDeclarations in dependency order.
   It is a fold of elab_declaration over the list (together with an extra error
   check for illegal type variable names). The caller, elab_module, is responsible
   for sorting into dependency order and rejecting cyclic dependencies.
*)


(* ========================================================================== *)
(* Empty environments                                                         *)
(* ========================================================================== *)

(* The empty type environment (satisfies tyenv_module_scope). *)
definition empty_module_tyenv :: CoreTyEnv where
  "empty_module_tyenv =
     \<lparr> TE_LocalVars = fmempty,
       TE_GlobalVars = fmempty,
       TE_GhostLocals = {||},
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

(* The empty module. *)
definition empty_core_module :: CoreModule where
  "empty_core_module =
     \<lparr> CM_TyEnv = empty_module_tyenv,
       CM_TypeSubst = fmempty,
       CM_GlobalVars = fmempty,
       CM_Functions = fmempty \<rparr>"


(* ========================================================================== *)
(* Term and type namespaces                                                   *)
(* ========================================================================== *)

(* The term namespace: global constants, functions, and data constructors. *)
definition term_name_in_scope :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> bool" where
  "term_name_in_scope env name =
     (name |\<in>| fmdom (TE_GlobalVars env)
      \<or> name |\<in>| fmdom (TE_Functions env)
      \<or> name |\<in>| fmdom (TE_DataCtors env))"

(* The type namespace: typedefs, datatypes, and abstract types (type variables). *)
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
   used as a bound type parameter. The renamer ensures this automatically
   (abstract types are dotted, type parameters are undotted), but we nevertheless
   check it explicitly in the elaborator ("belt and braces" approach). *)

(* This checks if a new local type variable (type-parameter of a function,
   datatype or typedef) would be captured. *)
definition binder_captures :: "CoreTyEnv \<Rightarrow> CoreModule \<Rightarrow> string list \<Rightarrow> bool" where
  "binder_captures env m tyvars =
     (fset_of_list tyvars |\<inter>| (TE_TypeVars env |\<union>| subst_names (CM_TypeSubst m)) \<noteq> {||})"

(* All type-parameter names bound anywhere in scope: function type parameters,
   datatype constructor type parameters, and typedef parameters. *)
definition scope_bound_tyvars :: "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> string fset" where
  "scope_bound_tyvars env elabEnv =
     ffUnion ((\<lambda>info. fset_of_list (FI_TyArgs info)) |`| fmran (TE_Functions env))
     |\<union>| ffUnion ((\<lambda>(_, tyVars, _). fset_of_list tyVars) |`| fmran (TE_DataCtors env))
     |\<union>| ffUnion ((\<lambda>(tyVars, _). fset_of_list tyVars) |`| fmran (EE_Typedefs elabEnv))"

(* This checks if a new type realization "name \<mapsto> target" would be captured. *)
definition realization_captures :: "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> string \<Rightarrow> CoreType \<Rightarrow> bool" where
  "realization_captures env elabEnv name target =
     (finsert name (fset_of_list (type_tyvars_list target))
        |\<inter>| scope_bound_tyvars env elabEnv \<noteq> {||})"


(* ========================================================================== *)
(* Environment-extension helpers                                              *)
(* ========================================================================== *)

(* Register a list of type parameters in the Typedefs table: each maps to its
   own CoreTy_Var. *)
definition tyvar_typedef_entries :: "string list \<Rightarrow> Typedefs \<Rightarrow> Typedefs" where
  "tyvar_typedef_entries tyvars tds =
     fold (\<lambda>v. fmupd v ([], CoreTy_Var v)) tyvars tds"

(* Add a new global variable ("const" declaration) to the CoreTyEnv. *)
definition tyenv_add_global :: "string \<Rightarrow> CoreType \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv" where
  "tyenv_add_global name ty env =
     env \<lparr> TE_GlobalVars := fmupd name ty (TE_GlobalVars env) \<rparr>"

(* Add a new function (and its FunInfo) to the CoreTyEnv. *)
definition tyenv_add_function :: "string \<Rightarrow> FunInfo \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv" where
  "tyenv_add_function name info env =
     env \<lparr> TE_Functions := fmupd name info (TE_Functions env) \<rparr>"

(* Add a new abstract type ("type T;") to the CoreTyEnv. Abstract types are added
   to TE_TypeVars and TE_AbstractTypes, and also to TE_RuntimeTypeVars if NotGhost. *)
definition tyenv_add_abstract_type :: "string \<Rightarrow> GhostOrNot \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv" where
  "tyenv_add_abstract_type name ghost env =
     env \<lparr> TE_TypeVars := finsert name (TE_TypeVars env),
           TE_RuntimeTypeVars := (if ghost = NotGhost
                                  then finsert name (TE_RuntimeTypeVars env)
                                  else TE_RuntimeTypeVars env),
           TE_AbstractTypes := finsert name (TE_AbstractTypes env) \<rparr>"

(* Add a datatype to the CoreTyEnv, updating all relevant fields (TE_Datatypes,
   TE_DataCtors, TE_DataCtorsByType, TE_GhostDatatypes) accordingly. *)
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

(* A realization is a typedef "type T = Foo;" in the implementation section of a
   module, following a previous "type T;" in the interface.

   The function `apply_realization` (below) updates the current CoreTyEnv, ElabEnv and
   CoreModule to add a new realization. The realization becomes visible to all later
   declarations in the same module (e.g. after "type T = Foo;", all future typechecking
   must treat T and Foo as equivalent).

   The specific changes are:
    - The substitution T := Foo is recorded in the module's CM_TypeSubst.
       - We also apply [T:=Foo] to all existing right-hand-side entries in the subst
         (this keeps the substitution idempotent).

    - EE_Typedefs is updated: the previous entry T \<mapsto> CoreTy_Var "T" is replaced
      with T \<mapsto> Foo, so that later occurrences of T elaborate directly to Foo.
       - Again, we also apply [T:=Foo] to any existing entries in EE_Typedefs.

    - The name "T" is no longer an abstract type, so it is removed from TE_TypeVars
      and related sets.
       - We also apply [T:=Foo] to the type env itself (this updates the types of
         global vars, functions and data ctors to mention Foo instead of T everywhere).

   The CoreModule itself doesn't get rewritten (other than the changes to its CM_TypeSubst);
   the module continues to mention "T", with [T:=Foo] being applied lazily when needed, by
   normalize_module.
*)
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
(* Global Constants ("const" decls)                                           *)
(* ========================================================================== *)

(* Elaborate a "const" initializer against a known declared type: 
   elaborate the rhs, coerce it to the declared type, clear leftover metavariables,
   and check the compile-time-constant restriction (non-ghost initializers must
   be a compile-time constant; ghost initializers can be any term). *)
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

(* Elaborate a constant initializer against an optional type annotation:
   calls either elab_const_rhs_infer, or elab_type + elab_const_rhs, as applicable.
   Returns the final term together with the constant's type. *)
definition elab_const_rhs_annot ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> BabType option \<Rightarrow> BabTerm
   \<Rightarrow> TypeError list + (CoreTerm \<times> CoreType)" where
  "elab_const_rhs_annot env elabEnv ghost loc optTy rhs =
    (case optTy of
       None \<Rightarrow> elab_const_rhs_infer env elabEnv ghost loc rhs
     | Some ty \<Rightarrow>
         (case elab_type env elabEnv ghost ty of
            Inl errs \<Rightarrow> Inl errs
          | Inr declTy \<Rightarrow>
              (case elab_const_rhs env elabEnv ghost loc declTy rhs of
                 Inl errs \<Rightarrow> Inl errs
               | Inr finalTm \<Rightarrow> Inr (finalTm, declTy))))"

(* Check that an optional type annotation, if present, elaborates to exactly
   the previously declared type. *)
definition check_const_type_annot ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> CoreType \<Rightarrow> BabType option
   \<Rightarrow> TypeError list + unit" where
  "check_const_type_annot env elabEnv ghost loc declTy optTy =
    (case optTy of
       None \<Rightarrow> Inr ()
     | Some ty \<Rightarrow>
         (case elab_type env elabEnv ghost ty of
            Inl errs \<Rightarrow> Inl errs
          | Inr coreTy \<Rightarrow>
              if coreTy \<noteq> declTy
              then Inl [TyErr_TypeMismatch loc declTy coreTy]
              else Inr ()))"

(* Return a FunInfo to represent a ghost constant. *)
definition ghost_const_fun_info :: "CoreType \<Rightarrow> FunInfo" where
  "ghost_const_fun_info retTy =
     \<lparr> FI_TyArgs = [], FI_TmArgs = [], FI_ReturnType = retTy,
       FI_Ghost = Ghost, FI_Impure = False \<rparr>"

(* Return a CoreFunction to represent a ghost constant. *)
definition ghost_const_fun :: "CoreTerm \<Rightarrow> CoreFunction" where
  "ghost_const_fun tm = \<lparr> CF_Args = [], CF_Body = Some [CoreStmt_Return tm] \<rparr>"

(* Ghost and non-ghost constants share the same elaboration logic, differing
   only in how the constant is represented:

    - A NotGhost constant elaborates directly to a Core global variable:
      declarations in TE_GlobalVars, definitions in CM_GlobalVars. The initializer
      term is evaluated directly at elaboration-time (by calling fold_const).

    - A Ghost constant elaborates to a Core nullary ghost function:
      `ghost const c: T = e;` becomes `ghost function c(): T { return e; }`.
      (Later references to `c` are rewritten to `c()` by elab_term.)
      Declarations go in TE_Functions (with the name recorded in EE_GhostConstants),
      and definitions in CM_Functions.
   
   The four points of difference are packaged in a ConstElabOps record:

    - CEO_LookupDecl: look up a prior declaration of the name, returning its
        declared type (Inr None if not previously declared).
    - CEO_AlreadyDefined: has the (previously-declared) name already been given
        a definition?
    - CEO_Declare: record a new declaration of the name with a given type
        (in the type env, elab env and module). Cannot fail.
    - CEO_Define: add a definition (an elaborated initializer term) to the
        module. May fail (compile-time evaluation of the initializer).

   elab_const_decl (below) contains the shared logic: it creates a suitable
   ConstElapOps (depending on ghostness) and then dispatches to one of three
   cases: declaration without a definition, definition of a previously-declared
   constant, or declaring and defining at once. *)

record ConstElabOps =
  CEO_LookupDecl :: "Location \<Rightarrow> string \<Rightarrow> CoreTyEnv \<Rightarrow> ElabEnv
                     \<Rightarrow> TypeError list + CoreType option"
  CEO_AlreadyDefined :: "string \<Rightarrow> CoreModule \<Rightarrow> bool"
  CEO_Declare :: "string \<Rightarrow> CoreType \<Rightarrow> CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> CoreModule
                  \<Rightarrow> CoreTyEnv \<times> ElabEnv \<times> CoreModule"
  CEO_Define :: "Location \<Rightarrow> string \<Rightarrow> CoreTerm \<Rightarrow> CoreModule
                 \<Rightarrow> TypeError list + CoreModule"

(* ConstElabOps for Ghost constants *)
definition ghost_const_ops :: ConstElabOps where
  "ghost_const_ops =
     \<lparr> CEO_LookupDecl = (\<lambda>loc name env elabEnv.
          if name |\<in>| EE_GhostConstants elabEnv
          then (case fmlookup (TE_Functions env) name of
                  None \<Rightarrow> Inl [TyErr_NameNotFound loc name]  \<comment> \<open>shouldn't happen\<close>
                | Some declInfo \<Rightarrow> Inr (Some (FI_ReturnType declInfo)))
          else Inr None),
       CEO_AlreadyDefined = (\<lambda>name m. name |\<in>| fmdom (CM_Functions m)),
       CEO_Declare = (\<lambda>name ty env elabEnv m.
          let funInfo = ghost_const_fun_info ty
          in (tyenv_add_function name funInfo env,
              elabEnv \<lparr> EE_GhostConstants := finsert name (EE_GhostConstants elabEnv) \<rparr>,
              m \<lparr> CM_TyEnv := tyenv_add_function name funInfo (CM_TyEnv m) \<rparr>)),
       CEO_Define = (\<lambda>loc name tm m.
          Inr (m \<lparr> CM_Functions := fmupd name (ghost_const_fun tm)
                                         (CM_Functions m) \<rparr>)) \<rparr>"

(* ConstElabOps for NotGhost constants *)
(* ctxGlobals holds constants that have been brought in via imports; together
   with the CM_GlobalVars of the module under construction, it forms the
   environment in which initializers are evaluated. *)
definition global_const_ops :: "(string, CoreValue) fmap \<Rightarrow> ConstElabOps" where
  "global_const_ops ctxGlobals =
     \<lparr> CEO_LookupDecl = (\<lambda>loc name env elabEnv.
          Inr (fmlookup (TE_GlobalVars env) name)),
       CEO_AlreadyDefined = (\<lambda>name m. name |\<in>| fmdom (CM_GlobalVars m)),
       CEO_Declare = (\<lambda>name ty env elabEnv m.
          (tyenv_add_global name ty env,
           elabEnv,
           m \<lparr> CM_TyEnv := tyenv_add_global name ty (CM_TyEnv m) \<rparr>)),
       CEO_Define = (\<lambda>loc name tm m.
          case fold_const (ctxGlobals ++\<^sub>f CM_GlobalVars m) loc tm of
            Inl errs \<Rightarrow> Inl errs
          | Inr v \<Rightarrow> Inr (m \<lparr> CM_GlobalVars := fmupd name v (CM_GlobalVars m) \<rparr>)) \<rparr>"

(* Declaration without a definition (the interface case): a type annotation is
   required; the constant is declared but no definition is added. *)
definition elab_const_declare_only ::
  "ConstElabOps \<Rightarrow> GhostOrNot \<Rightarrow> CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> CoreModule
   \<Rightarrow> Location \<Rightarrow> string \<Rightarrow> BabType option
   \<Rightarrow> TypeError list + (CoreTyEnv \<times> ElabEnv \<times> CoreModule)" where
  "elab_const_declare_only ops ghost env elabEnv m loc name optTy =
    (if term_name_in_scope env name then Inl [TyErr_DuplicateName loc name]
     else case optTy of
            None \<Rightarrow> Inl [TyErr_ConstDeclNeedsType loc name]
          | Some ty \<Rightarrow>
              (case elab_type env elabEnv ghost ty of
                 Inl errs \<Rightarrow> Inl errs
               | Inr coreTy \<Rightarrow> Inr (CEO_Declare ops name coreTy env elabEnv m)))"

(* Definition of a constant previously declared with type declTy: check that
   it is not already defined and that the annotation (if any) matches the
   declared type, then elaborate the initializer and add the definition. *)
definition elab_const_define_declared ::
  "ConstElabOps \<Rightarrow> GhostOrNot \<Rightarrow> CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> CoreModule
   \<Rightarrow> Location \<Rightarrow> string \<Rightarrow> CoreType \<Rightarrow> BabType option \<Rightarrow> BabTerm
   \<Rightarrow> TypeError list + (CoreTyEnv \<times> ElabEnv \<times> CoreModule)" where
  "elab_const_define_declared ops ghost env elabEnv m loc name declTy optTy rhs =
    (if CEO_AlreadyDefined ops name m then Inl [TyErr_DuplicateName loc name]
     else case check_const_type_annot env elabEnv ghost loc declTy optTy of
            Inl errs \<Rightarrow> Inl errs
          | Inr _ \<Rightarrow>
              (case elab_const_rhs env elabEnv ghost loc declTy rhs of
                 Inl errs \<Rightarrow> Inl errs
               | Inr finalTm \<Rightarrow>
                   (case CEO_Define ops loc name finalTm m of
                      Inl errs \<Rightarrow> Inl errs
                    | Inr m2 \<Rightarrow> Inr (env, elabEnv, m2))))"

(* Declaring and defining at once: elaborate the initializer (against the
   annotation if present, otherwise inferring the constant's type), then
   declare the constant and add its definition. *)
definition elab_const_declare_and_define ::
  "ConstElabOps \<Rightarrow> GhostOrNot \<Rightarrow> CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> CoreModule
   \<Rightarrow> Location \<Rightarrow> string \<Rightarrow> BabType option \<Rightarrow> BabTerm
   \<Rightarrow> TypeError list + (CoreTyEnv \<times> ElabEnv \<times> CoreModule)" where
  "elab_const_declare_and_define ops ghost env elabEnv m loc name optTy rhs =
    (if term_name_in_scope env name then Inl [TyErr_DuplicateName loc name]
     else case elab_const_rhs_annot env elabEnv ghost loc optTy rhs of
            Inl errs \<Rightarrow> Inl errs
          | Inr (finalTm, declTy) \<Rightarrow>
              (let (env2, elabEnv2, m2) = CEO_Declare ops name declTy env elabEnv m
               in case CEO_Define ops loc name finalTm m2 of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr m3 \<Rightarrow> Inr (env2, elabEnv2, m3)))"

(* Elaborate a `const` declaration: create appropriate ConstElabOps (depending on
   ghostness), then dispatch on whether the declaration has an initializer and whether
   the name was previously declared. *)
definition elab_const_decl ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> (string, CoreValue) fmap \<Rightarrow> CoreModule \<Rightarrow> DeclConst
   \<Rightarrow> TypeError list + (CoreTyEnv \<times> ElabEnv \<times> CoreModule)" where
  "elab_const_decl env elabEnv ctxGlobals m dc =
    (let ghost = DC_Ghost dc;
         ops = (if ghost = Ghost then ghost_const_ops else global_const_ops ctxGlobals);
         loc = DC_Location dc;
         name = DC_Name dc
     in case DC_Value dc of
          None \<Rightarrow> elab_const_declare_only ops ghost env elabEnv m loc name (DC_Type dc)
        | Some rhs \<Rightarrow>
            \<comment> \<open>Check that ghostness agrees with any previous declaration of this
               name. Without this check the mismatch would still be rejected -
               the kind-specific CEO_LookupDecl below misses (ghost constants
               live in TE_Functions, non-ghost in TE_GlobalVars), so the code
               falls into elab_const_declare_and_define, whose duplicate-name
               check fires - but with a misleading 'duplicate name' error
               rather than a ghostness-mismatch error.\<close>
            if (ghost = Ghost \<and> name |\<in>| fmdom (TE_GlobalVars env))
               \<or> (ghost = NotGhost \<and> name |\<in>| EE_GhostConstants elabEnv)
            then Inl [TyErr_ConstGhostnessMismatch loc name]
            else (case CEO_LookupDecl ops loc name env elabEnv of
               Inl errs \<Rightarrow> Inl errs
             | Inr (Some declTy) \<Rightarrow>
                 elab_const_define_declared ops ghost env elabEnv m loc name declTy
                                            (DC_Type dc) rhs
             | Inr None \<Rightarrow>
                 elab_const_declare_and_define ops ghost env elabEnv m loc name
                                               (DC_Type dc) rhs))"


(* ========================================================================== *)
(* Functions                                                                  *)
(* ========================================================================== *)

(* Elaborate a function's signature to a FunInfo. The argument and return
   types are elaborated with the function's type parameters in scope; for a
   non-ghost function they are elaborated in NotGhost mode with the type
   parameters as runtime type variables (which enforces that all arguments
   and the return value have runtime types). *)
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
   type errors (verification is out of scope for now). `requires` and `decreases`
   terms are elaborated in preEnv (the body env); `ensures` terms in postEnv
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
   elaborated body as a CoreStatement list. *)
definition elab_fun_body_and_contracts ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> DeclFun \<Rightarrow> FunInfo
   \<Rightarrow> TypeError list + CoreStatement list option" where
  "elab_fun_body_and_contracts env elabEnv df funInfo =
    \<comment> \<open>Construct envs for typechecking the body (and a separate env for `ensures`,
       with the `return` variable)\<close>
    (let paramNames = map (\<lambda>(n, _, _). n) (DF_TmArgs df);
         bodyEnv = module_body_env_for env paramNames funInfo;
         bodyElabEnv = elabEnv
           \<lparr> EE_Typedefs := tyvar_typedef_entries (DF_TyArgs df) (EE_Typedefs elabEnv),
             EE_CurrentFunctionVoid := (DF_ReturnType df = None) \<rparr>;
         postEnv = (if DF_ReturnType df = None then bodyEnv
                    else vardecl_add_local bodyEnv Ghost ''return'' (FI_ReturnType funInfo))
     \<comment> \<open>Elaborate the contracts\<close>
     in case elab_fun_contracts bodyEnv postEnv bodyElabEnv (DF_Attributes df) 0 of
          Inl errs \<Rightarrow> Inl errs
        | Inr _ \<Rightarrow>
            (case DF_Body df of
               None \<Rightarrow> Inr None
             | Some body \<Rightarrow>
                 \<comment> \<open>Elaborate the body\<close>
                 (case elab_statement_list bodyEnv bodyElabEnv (DF_Ghost df) body 0 of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr (coreBody, _, _) \<Rightarrow> Inr (Some coreBody))))"

(* Elaborate a function declaration. 

   A function with a body, or marked extern, is a *definition* (an extern
   function's CF_Body is None; its implementation arrives when an interpreter
   state is built); a bodiless non-extern function is a declaration only.

   Defining a previously-declared function requires the FunInfo to match the
   declaration *literally* - including the type-parameter names (alpha-renaming
   is not accepted) and the ghost/impure flags - plus agreement on Babylon-level
   voidness, which is not recoverable from the Core return type. *)
definition elab_function_decl ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> CoreModule \<Rightarrow> DeclFun
   \<Rightarrow> TypeError list + (CoreTyEnv \<times> ElabEnv \<times> CoreModule)" where
  "elab_function_decl env elabEnv m df =
    \<comment> \<open>Gather function info\<close>
    (let loc = DF_Location df; 
         name = DF_Name df;
         paramNames = map (\<lambda>(n, _, _). n) (DF_TmArgs df);
         isDefinition = (DF_Extern df \<or> DF_Body df \<noteq> None);
         isVoid = (DF_ReturnType df = None)
     \<comment> \<open>Check for duplicate type or term arg names\<close>
     in case first_duplicate_name (\<lambda>x. x) (DF_TyArgs df) of
          Some dup \<Rightarrow> Inl [TyErr_DuplicateName loc dup]
        | None \<Rightarrow>
        (case first_duplicate_name (\<lambda>(n, _, _). n) (DF_TmArgs df) of
           Some dup \<Rightarrow> Inl [TyErr_DuplicateName loc dup]
         | None \<Rightarrow>
           \<comment> \<open>Check for variable captures, or extern function with body\<close>
           if binder_captures env m (DF_TyArgs df)
           then Inl [TyErr_TypeVarCapture loc name]
           else if DF_Extern df \<and> DF_Body df \<noteq> None
           then Inl [TyErr_ExternFunctionWithBody loc name]
           else
             \<comment> \<open>Elaborate the signature, create FunInfo\<close>
             (case elab_fun_signature env elabEnv df of
                Inl errs \<Rightarrow> Inl errs
              | Inr funInfo \<Rightarrow>
                  (case fmlookup (TE_Functions env) name of
                     Some declInfo \<Rightarrow>
                       \<comment> \<open>Already declared: this must be a matching definition (and must
                          not be overwriting an earlier definition).\<close>
                       (if \<not> isDefinition then Inl [TyErr_DuplicateName loc name]
                        else if name |\<in>| fmdom (CM_Functions m)
                        then Inl [TyErr_DuplicateName loc name]
                        \<comment> \<open>A name declared as a ghost constant cannot be defined by a
                           function definition (even though its desugared FunInfo may
                           match): a ghost const must be defined by a ghost const.\<close>
                        else if name |\<in>| EE_GhostConstants elabEnv
                        then Inl [TyErr_DuplicateName loc name]
                        else if funInfo \<noteq> declInfo
                        then Inl [TyErr_FunctionSignatureMismatch loc name]
                        else if (name |\<in>| EE_VoidFunctions elabEnv) \<noteq> isVoid
                        then Inl [TyErr_FunctionSignatureMismatch loc name]
                        else
                          \<comment> \<open>Elaborate body and contracts; add to CM_Functions.\<close>
                          (case elab_fun_body_and_contracts env elabEnv df funInfo of
                             Inl errs \<Rightarrow> Inl errs
                           | Inr bodyOpt \<Rightarrow>
                               Inr (env, elabEnv,
                                    m \<lparr> CM_Functions :=
                                          fmupd name \<lparr> CF_Args = paramNames, CF_Body = bodyOpt \<rparr>
                                                (CM_Functions m) \<rparr>)))
                   | None \<Rightarrow>
                       \<comment> \<open>Not previously declared. This is either a declaration only, or
                          a simultaneous declaration+definition. First, check that it isn't
                          a duplicate name.\<close>
                       (if term_name_in_scope env name then Inl [TyErr_DuplicateName loc name]
                        else
                          \<comment> \<open>Add the function to the env before elaborating the body.
                             (Note: since recursion is not supported yet, this is not strictly
                             necessary - we could equally well wait until after elaborating
                             the body, before creating env' - but here we choose to do it
                             before.)\<close>
                          (let env' = tyenv_add_function name funInfo env;
                               elabEnv' = (if isVoid
                                           then elabEnv \<lparr> EE_VoidFunctions :=
                                                  finsert name (EE_VoidFunctions elabEnv) \<rparr>
                                           else elabEnv);
                               m' = m \<lparr> CM_TyEnv := tyenv_add_function name funInfo (CM_TyEnv m) \<rparr>
                           \<comment> \<open>Now elaborate the body and contracts, in this new env.\<close>
                           in case elab_fun_body_and_contracts env' elabEnv' df funInfo of
                                Inl errs \<Rightarrow> Inl errs
                              | Inr bodyOpt \<Rightarrow>
                                  \<comment> \<open>If isDefinition, this is a simultaneous declaration +
                                     definition: update both env and CM_Functions. Otherwise,
                                     update the env only.\<close>
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

(* Elaborate a list of data constructors.
   Returns, for each ctor, a tuple of: name, Core payload type, nullary flag.
   (For nullary ctors, the Core payload type is unit.) *)
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

(* Elaborate a datatype declaration. *)
definition elab_datatype_decl ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> string fset \<Rightarrow> CoreModule \<Rightarrow> DeclDatatype
   \<Rightarrow> TypeError list + (CoreTyEnv \<times> ElabEnv \<times> CoreModule)" where
  "elab_datatype_decl env elabEnv ownAbstract m dd =
    (let loc = DD_Location dd;
         name = DD_Name dd;
         tyvars = DD_TyArgs dd;
         isRealization = (name |\<in>| TE_TypeVars env)
     \<comment> \<open>Basic error checks: can't realize imported type (not possible in renamer output),
        realizations can't have type variables, can't define the same name more than once,
        can't have an empty datatype.\<close>
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
          \<comment> \<open>Type variables and data ctor names can't have duplicates, variable capture not
             allowed, data ctor names can't duplicate existing term names.\<close>
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
                       \<comment> \<open>Elaborate data ctors in a temporary env where the datatype's type
                          variables are runtime. (This is valid, because the runtime-ness
                          of the type variables doesn't affect whether kind-checking of the
                          payload types will succeed; it only affects the payload types'
                          runtime-ness. See elab_type_TE_RuntimeTypeVars_irrelevant.)\<close>
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
                               \<comment> \<open>If, in payloadEnv, all payloads have runtime type, then the
                                  datatype itself is runtime; otherwise, it is considered a
                                  ghost datatype.\<close>
                               (let isGhost = \<not> list_all
                                       (\<lambda>(_, payloadTy, _). is_runtime_type payloadEnv payloadTy)
                                       ctorInfo
                                \<comment> \<open>A runtime abstract type can't be realized by a ghost datatype.\<close>
                                in if isRealization \<and> name |\<in>| TE_RuntimeTypeVars env \<and> isGhost
                                   then Inl [TyErr_GhostRealizationOfRuntimeType loc name]
                                   \<comment> \<open>Another variable capture check.\<close>
                                   else if isRealization \<and>
                                        realization_captures env elabEnv name
                                          (CoreTy_Datatype name [])
                                   then Inl [TyErr_TypeVarCapture loc name]
                                   else
                                     \<comment> \<open>Success: update the env and module with the new datatype
                                        (and realization if applicable).\<close>
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

(* Elaborate a typedef declaration. Cases:
    - An extern type - `extern type T;` - this is not currently supported.

    - Realization - `type T = Foo;` after a previous `type T;` (or `ghost type T;`).
      Type variables are not allowed. If the type T was declared runtime (non-ghost), then
      `Foo` must also be runtime. Cyclic definitions are not allowed.

    - A new abstract type - `type T;` or `ghost type T;`.

    - An ordinary typedef - `type T = Foo;` where T was not previously declared.
      This is resolved entirely on the elaborator side (it is added to EE_Typedefs
      and never reaches Core).
*)
definition elab_typedef_decl ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> string fset \<Rightarrow> CoreModule \<Rightarrow> DeclTypedef
   \<Rightarrow> TypeError list + (CoreTyEnv \<times> ElabEnv \<times> CoreModule)" where
  "elab_typedef_decl env elabEnv ownAbstract m dt =
    (let loc = DT_Location dt;
         name = DT_Name dt;
         tyvars = DT_TyArgs dt
     in if DT_Extern dt then Inl [TyErr_ExternTypeNotImplemented loc] \<comment> \<open>Not yet implemented\<close>
        else if name |\<in>| TE_TypeVars env then
          \<comment> \<open>Realization of an abstract type.\<close>
          \<comment> \<open>Check errors: realizing an imported type (not possible in renamer output),
             duplicate names, unexpected type arguments).\<close>
          (if name |\<notin>| ownAbstract then Inl [TyErr_CannotRealizeImportedType loc name]
           else case DT_Definition dt of
                  None \<Rightarrow> Inl [TyErr_DuplicateName loc name]
                | Some ty \<Rightarrow>
                    if tyvars \<noteq> [] then Inl [TyErr_TypeArgsNotAllowed loc name]
                    else
                      \<comment> \<open>Elaborate the provided RHS type.\<close>
                      (case elab_type env elabEnv Ghost ty of
                         Inl errs \<Rightarrow> Inl errs
                       | Inr target \<Rightarrow>
                           \<comment> \<open>If the target mentions the name being defined, this is circular
                              and not allowed (this should have been ruled out by earlier
                              checks, but it doesn't hurt to check it again).\<close>
                           if name \<in> type_tyvars target
                           then Inl [TyErr_SelfReferentialType loc name]
                           \<comment> \<open>Runtime abstract types must be realized by runtime types.\<close>
                           else if name |\<in>| TE_RuntimeTypeVars env
                                \<and> \<not> is_runtime_type env target
                           then Inl [TyErr_GhostRealizationOfRuntimeType loc name]
                           \<comment> \<open>Variable capture check.\<close>
                           else if realization_captures env elabEnv name target
                           then Inl [TyErr_TypeVarCapture loc name]
                           \<comment> \<open>Success: apply the realization.\<close>
                           else Inr (apply_realization name target env elabEnv m)))
        \<comment> \<open>Declaration of new abstract type, or a new ordinary typedef.
           Check for duplicate names.\<close>
        else if type_name_in_scope env elabEnv name then Inl [TyErr_DuplicateName loc name]
        else case DT_Definition dt of
               None \<Rightarrow>
                 \<comment> \<open>A new abstract type.\<close>
                 \<comment> \<open>Abstract types currently cannot have type variables.\<close>
                 (if tyvars \<noteq> [] then Inl [TyErr_TypeArgsNotAllowed loc name]
                  else
                    \<comment> \<open>Add the new abstract type to the env and module.\<close>
                    Inr (tyenv_add_abstract_type name (DT_Ghost dt) env,
                         elabEnv \<lparr> EE_Typedefs :=
                             fmupd name ([], CoreTy_Var name) (EE_Typedefs elabEnv) \<rparr>,
                         m \<lparr> CM_TyEnv :=
                               tyenv_add_abstract_type name (DT_Ghost dt) (CM_TyEnv m) \<rparr>))
             | Some ty \<Rightarrow>
                 \<comment> \<open>An ordinary transparent typedef.\<close>
                 \<comment> \<open>Type variables allowed, so long as they are distinct.\<close>
                 (case first_duplicate_name (\<lambda>x. x) tyvars of
                    Some dup \<Rightarrow> Inl [TyErr_DuplicateName loc dup]
                  | None \<Rightarrow>
                      \<comment> \<open>Check variable capture.\<close>
                      if binder_captures env m tyvars
                      then Inl [TyErr_TypeVarCapture loc name]
                      else
                        \<comment> \<open>Elaborate the rhs type, in a suitable env, and in Ghost mode. Note
                           it doesn't matter whether the type vars are runtime or not here
                           (see elab_type_TE_RuntimeTypeVars_irrelevant).\<close>
                        (let tdEnv = env \<lparr> TE_TypeVars :=
                                             TE_TypeVars env |\<union>| fset_of_list tyvars \<rparr>;
                             tdElabEnv = elabEnv \<lparr> EE_Typedefs :=
                                             tyvar_typedef_entries tyvars (EE_Typedefs elabEnv) \<rparr>
                         in case elab_type tdEnv tdElabEnv Ghost ty of
                              Inl errs \<Rightarrow> Inl errs
                            | Inr target \<Rightarrow>
                                \<comment> \<open>Elaboration successful: add typedef to ElabEnv.\<close>
                                Inr (env,
                                     elabEnv \<lparr> EE_Typedefs :=
                                         fmupd name (tyvars, target) (EE_Typedefs elabEnv) \<rparr>,
                                     m))))"


(* ========================================================================== *)
(* The main fold                                                              *)
(* ========================================================================== *)

(* Elaborate a single declaration: dispatches to one of the above functions.
   ctxGlobals (the dependency context's global-constant values) is only
   needed by the const case, for compile-time initializer evaluation. *)
fun elab_declaration ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> string fset \<Rightarrow> (string, CoreValue) fmap \<Rightarrow> CoreModule
   \<Rightarrow> BabDeclaration
   \<Rightarrow> TypeError list + (CoreTyEnv \<times> ElabEnv \<times> CoreModule)" where
  "elab_declaration env elabEnv ownAbstract ctxGlobals m (BabDecl_Const dc) =
     elab_const_decl env elabEnv ctxGlobals m dc"
| "elab_declaration env elabEnv ownAbstract ctxGlobals m (BabDecl_Function df) =
     elab_function_decl env elabEnv m df"
| "elab_declaration env elabEnv ownAbstract ctxGlobals m (BabDecl_Datatype dd) =
     elab_datatype_decl env elabEnv ownAbstract m dd"
| "elab_declaration env elabEnv ownAbstract ctxGlobals m (BabDecl_Typedef dt) =
     elab_typedef_decl env elabEnv ownAbstract m dt"

(* Elaborate a declaration list, threading the state triple and stopping at
   the first failing declaration. *)
fun elab_declaration_list ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> string fset \<Rightarrow> (string, CoreValue) fmap \<Rightarrow> CoreModule
   \<Rightarrow> BabDeclaration list
   \<Rightarrow> TypeError list + (CoreTyEnv \<times> ElabEnv \<times> CoreModule)" where
  "elab_declaration_list env elabEnv ownAbstract ctxGlobals m [] = Inr (env, elabEnv, m)"
| "elab_declaration_list env elabEnv ownAbstract ctxGlobals m (d # ds) =
    (case elab_declaration env elabEnv ownAbstract ctxGlobals m d of
       Inl errs \<Rightarrow> Inl errs
     | Inr (env', elabEnv', m') \<Rightarrow>
         elab_declaration_list env' elabEnv' ownAbstract ctxGlobals m' ds)"

(* ========================================================================== *)
(* Type-variable binder name check                                            *)
(* ========================================================================== *)

(* The type-variable names a declaration binds: a function's or datatype's
   type parameters; a typedef's parameters plus, for "type T;", the abstract
   type name itself (which enters TE_TypeVars). Constants bind none. *)
fun decl_tyvar_binders :: "BabDeclaration \<Rightarrow> string list" where
  "decl_tyvar_binders (BabDecl_Const dc) = []"
| "decl_tyvar_binders (BabDecl_Function df) = DF_TyArgs df"
| "decl_tyvar_binders (BabDecl_Datatype dd) = DD_TyArgs dd"
| "decl_tyvar_binders (BabDecl_Typedef dt) = DT_Name dt # DT_TyArgs dt"

(* Reject any declaration that binds a type variable that begins with a '?'.
   This is needed to establish `decl_tyvars_fresh_ok` in the proofs; the
   check should never fire on "real" input, because the parser never creates
   such names. *)
definition check_decl_tyvar_names :: "BabDeclaration \<Rightarrow> TypeError list" where
  "check_decl_tyvar_names d =
     concat (map (\<lambda>n. if n \<noteq> [] \<and> hd n = CHR ''?''
                      then [TyErr_UnexpectedNameClash (bab_declaration_location d)]
                      else [])
                 (decl_tyvar_binders d))"

(* Top-level entry point: elaborate a (dependency-ordered) declaration list in
   the given context, producing the elaborated CoreModule and the final ElabEnv.
   The type-variable names are also checked for '?' characters (check_decl_tyvar_names). *)
definition elab_declarations ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> string fset \<Rightarrow> (string, CoreValue) fmap \<Rightarrow> BabDeclaration list
   \<Rightarrow> TypeError list + (CoreModule \<times> ElabEnv)" where
  "elab_declarations env elabEnv ownAbstract ctxGlobals decls =
    (let nameErrs = concat (map check_decl_tyvar_names decls)
     in if nameErrs \<noteq> [] then Inl nameErrs
        else case elab_declaration_list env elabEnv ownAbstract ctxGlobals
                                        empty_core_module decls of
               Inl errs \<Rightarrow> Inl errs
             | Inr (_, elabEnv', m) \<Rightarrow> Inr (m, elabEnv'))"

end
