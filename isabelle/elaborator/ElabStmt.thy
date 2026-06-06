theory ElabStmt
  imports ElabTerm "../core/CoreStmtTypecheck"
begin

(* ========================================================================== *)
(* Metavariable clearing helpers *)
(* ========================================================================== *)

(* Substitute every metavariable in the interval [lo, hi) with the unit type
   CoreTy_Record []. The term elaborator allocates fresh metavariables in this
   interval; some may remain unresolved in the emitted term (phantom type
   arguments). Clearing them with a ground runtime type lets the elaborated
   statement typecheck in the original env, with no fresh-tyvar extension. *)
definition clear_metavars :: "nat \<Rightarrow> nat \<Rightarrow> CoreTerm \<Rightarrow> CoreTerm" where
  "clear_metavars lo hi tm =
     apply_subst_to_term (fmap_of_list (map (\<lambda>n. (n, CoreTy_Record [])) [lo ..< hi])) tm"

(* The type-level analog of clear_metavars, for the (substituted) type arguments
   of an elaborated call emitted by CoreStmt_AssignCall / VarDeclCall. *)
definition clear_metavars_type :: "nat \<Rightarrow> nat \<Rightarrow> CoreType \<Rightarrow> CoreType" where
  "clear_metavars_type lo hi ty =
     apply_subst (fmap_of_list (map (\<lambda>n. (n, CoreTy_Record [])) [lo ..< hi])) ty"


(* ========================================================================== *)
(* Impure call helpers *)
(* ========================================================================== *)

(* Determine if a term represents an impure BabTm_Call. Impure means that FI_Impure
   is true, or there is at least one Ref arg. *)
definition is_impure_call :: "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> BabTerm \<Rightarrow> bool" where
  "is_impure_call env elabEnv rhs =
    (case rhs of
       BabTm_Call _ (BabTm_Name _ name _) _ \<Rightarrow>
         name |\<notin>| fmdom (EE_DataCtorArity elabEnv) \<and>
         (case fmlookup (TE_Functions env) name of
            None \<Rightarrow> False
          | Some funInfo \<Rightarrow>
              FI_Impure funInfo
              \<or> \<not> list_all (\<lambda>(_, _, vor). vor = Var) (FI_TmArgs funInfo))
     | _ \<Rightarrow> False)"

(* Resolve the callee of an impure call. This checks that the callee is a non-void, 
   ghost-compatible function; resolves the type arguments (allocating fresh metavariables
   when omitted); and computes the per-argument expected types and Var/Ref markers, plus
   the substituted return type. Returns:
     (fnName, newTyArgs, expArgTypes, varOrRefs, retType0, next_mv').
   The data-constructor / arg-count checks are left to the caller. *)
definition resolve_impure_callee ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> BabTerm \<Rightarrow> nat
   \<Rightarrow> TypeError list
      + (string \<times> CoreType list \<times> CoreType list \<times> VarOrRef list \<times> CoreType \<times> nat)" where
  "resolve_impure_callee env elabEnv ghost callee next_mv =
    (case callee of
       BabTm_Name nloc name tyArgs \<Rightarrow>
         (case fmlookup (TE_Functions env) name of
            None \<Rightarrow> Inl [TyErr_InternalError_NameNotFound nloc name]
          | Some funInfo \<Rightarrow>
              if name |\<in>| EE_VoidFunctions elabEnv then
                Inl [TyErr_FunctionNoReturnType nloc name]
              else if ghost = NotGhost \<and> FI_Ghost funInfo = Ghost then
                Inl [TyErr_GhostFunctionInNonGhost nloc name]
              else
                (case resolve_type_args env elabEnv ghost nloc name
                        (FI_TyArgs funInfo) tyArgs next_mv of
                   Inl errs \<Rightarrow> Inl errs
                 | Inr (newTyArgs, next_mv') \<Rightarrow>
                     let subst0 = fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs);
                         expArgTypes = map (\<lambda>(_, ty, _). apply_subst subst0 ty) (FI_TmArgs funInfo);
                         varOrRefs = map (\<lambda>(_, _, vor). vor) (FI_TmArgs funInfo);
                         retType0 = apply_subst subst0 (FI_ReturnType funInfo)
                     in Inr (name, newTyArgs, expArgTypes, varOrRefs, retType0, next_mv')))
     | _ \<Rightarrow> Inl [TyErr_CalleeNotFunction (bab_term_location callee)])"

(* Elaborate function call arguments, given the substitution that unify_type_lists
   produced. For each (term, actualTy, expectedTy, Var/Ref):
     - Var: insert an integer cast if the actual and expected types differ
       (they must both be finite integers at that point, guaranteed by
       unify_type_lists's success).
     - Ref: require the actual and expected types to be equal and the term
       to be a writable lvalue.
   Returns the final argument terms (substitution applied). *)
fun validate_call_args ::
  "CoreTyEnv \<Rightarrow> Location \<Rightarrow> TypeSubst
   \<Rightarrow> CoreTerm list \<Rightarrow> CoreType list \<Rightarrow> CoreType list \<Rightarrow> VarOrRef list
   \<Rightarrow> TypeError list + CoreTerm list" where
  "validate_call_args env loc subst [] [] [] [] = Inr []"
| "validate_call_args env loc subst (tm # tms) (actualTy # actualTys)
       (expectedTy # expectedTys) (vor # vors) =
    (let tm' = apply_subst_to_term subst tm;
         actualTy' = apply_subst subst actualTy;
         expectedTy' = apply_subst subst expectedTy
     in case vor of
          Var \<Rightarrow>
            (let finalTm = (if actualTy' = expectedTy' then tm'
                            else CoreTm_Cast expectedTy' tm')
             in case validate_call_args env loc subst tms actualTys expectedTys vors of
                  Inl errs \<Rightarrow> Inl errs
                | Inr rest \<Rightarrow> Inr (finalTm # rest))
        | Ref \<Rightarrow>
            (if actualTy' \<noteq> expectedTy' then Inl [TyErr_TypeMismatch loc expectedTy' actualTy']
             else if \<not> is_writable_lvalue env tm' then Inl [TyErr_NotWritableLvalue loc]
             else case validate_call_args env loc subst tms actualTys expectedTys vors of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr rest \<Rightarrow> Inr (tm' # rest)))"
| "validate_call_args env loc subst _ _ _ _ = undefined"

(* Elaborate an impure function call term appearing at the outermost rhs of an
   Assign or VarDecl.
   (This is a combination of the previous two helper functions.)
   Returns the elaborated call term, its return type, and the advanced counter. *)
definition elab_impure_call_term ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> BabTerm \<Rightarrow> BabTerm list \<Rightarrow> nat
   \<Rightarrow> TypeError list + (string \<times> CoreType list \<times> CoreTerm list \<times> CoreType \<times> nat)" where
  "elab_impure_call_term env elabEnv ghost loc callee args next_mv =
    (case resolve_impure_callee env elabEnv ghost callee next_mv of
       Inl errs \<Rightarrow> Inl errs
     | Inr (name, newTyArgs, expArgTypes, varOrRefs, retType0, next_mv1) \<Rightarrow>
         if length args \<noteq> length expArgTypes then
           Inl [TyErr_WrongNumberOfArgs loc name (length expArgTypes) (length args)]
         else
           (case elab_term_list env elabEnv ghost args next_mv1 of
              Inl errs \<Rightarrow> Inl errs
            | Inr (elabArgTms, actualTypes, next_mv2) \<Rightarrow>
                (case unify_type_lists (\<lambda>n. n |\<notin>| TE_TypeVars env)
                        (\<lambda>idx exp act. [TyErr_TypeMismatch (bab_term_location (args ! idx)) exp act])
                        0 actualTypes expArgTypes fmempty of
                   Inl errs \<Rightarrow> Inl errs
                 | Inr finalSubst \<Rightarrow>
                     (case validate_call_args env loc finalSubst
                             elabArgTms actualTypes expArgTypes varOrRefs of
                        Inl errs \<Rightarrow> Inl errs
                      | Inr finalArgTms \<Rightarrow>
                          Inr (name,
                               map (apply_subst finalSubst) newTyArgs,
                               finalArgTms,
                               apply_subst finalSubst retType0,
                               next_mv2)))))"


(* ========================================================================== *)
(* Helpers for VarDecl and Assign elaboration *)
(* ========================================================================== *)

(* Coerce an elaborated (pure) term `tm` of type `srcTy` to the target type
   `tgtTy`: try to unify (binding flexible metavariables, then applying the
   substitution to the term); failing that, insert an integer cast when both
   types are integers (e.g. `var x: i16 = 10;`); otherwise a type mismatch.
   The caller chooses which type to *record* (annotated VarDecl keeps the
   annotation type, which is already metavariable-free). *)
definition coerce_term_to_type ::
  "CoreTyEnv \<Rightarrow> Location \<Rightarrow> CoreTerm \<Rightarrow> CoreType \<Rightarrow> CoreType
   \<Rightarrow> TypeError list + CoreTerm" where
  "coerce_term_to_type env loc tm srcTy tgtTy =
    (case unify (\<lambda>n. n |\<notin>| TE_TypeVars env) srcTy tgtTy of
       Some subst \<Rightarrow> Inr (apply_subst_to_term subst tm)
     | None \<Rightarrow>
         if is_integer_type srcTy \<and> is_integer_type tgtTy
         then Inr (CoreTm_Cast tgtTy tm)
         else Inl [TyErr_TypeMismatch loc tgtTy srcTy])"

(* Reconcile an impure call's return type `retTy` with the target type `tgtTy`,
   choosing the castOpt for CoreStmt_VarDeclCall / AssignCall. On exact match
   (unify) returns (None, tyArgs, argTms) with the unifying substitution applied
   to the ty-args and arg terms; on an integer mismatch returns
   (Some tgtTy, tyArgs, argTms) with no further substitution (unify failed, so
   there is no substitution to apply); otherwise a type mismatch. *)
definition reconcile_call_result ::
  "CoreTyEnv \<Rightarrow> Location \<Rightarrow> CoreType list \<Rightarrow> CoreTerm list \<Rightarrow> CoreType \<Rightarrow> CoreType
   \<Rightarrow> TypeError list + (CoreType option \<times> CoreType list \<times> CoreTerm list)" where
  "reconcile_call_result env loc tyArgs argTms retTy tgtTy =
    (case unify (\<lambda>n. n |\<notin>| TE_TypeVars env) retTy tgtTy of
       Some subst \<Rightarrow>
         Inr (None,
              map (apply_subst subst) tyArgs,
              map (apply_subst_to_term subst) argTms)
     | None \<Rightarrow>
         if is_integer_type retTy \<and> is_integer_type tgtTy
         then Inr (Some tgtTy, tyArgs, argTms)
         else Inl [TyErr_TypeMismatch loc tgtTy retTy])"

(* ----- VarDecl branch helpers ----- *)

(* Install `varName` as a local of type `varTy`: set its type, set/clear its
   ghost flag from the ambient `ghost`, and clear its const flag (the Ref helper
   overrides TE_ConstLocals afterwards when the base is read-only). *)
definition vardecl_add_local ::
  "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> string \<Rightarrow> CoreType \<Rightarrow> CoreTyEnv" where
  "vardecl_add_local env ghost varName varTy =
     env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
           TE_GhostLocals := (if ghost = Ghost
                              then finsert varName (TE_GhostLocals env)
                              else fminus (TE_GhostLocals env) {|varName|}),
           TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"

(* VarDecl(Var) with a pure initializer. With no annotation the declared type is
   the inferred rhs type (which must be metavariable-free); with an annotation the
   rhs is coerced to it and the annotation type is recorded. Emits CoreStmt_VarDecl. *)
definition elab_vardecl_pure ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> string
   \<Rightarrow> BabType option \<Rightarrow> BabTerm \<Rightarrow> nat
   \<Rightarrow> TypeError list + (CoreStatement \<times> CoreTyEnv \<times> nat)" where
  "elab_vardecl_pure env elabEnv ghost loc varName tyOpt tm next_mv =
    (case elab_term env elabEnv ghost tm next_mv of
       Inl errs \<Rightarrow> Inl errs
     | Inr (coreTm, rhsTy, next_mv') \<Rightarrow>
         (case tyOpt of
            None \<Rightarrow>
              \<comment> \<open>Inferred type from the initializer; reject unresolved metavars.\<close>
              if \<not> list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)
              then Inl [TyErr_CannotInferType loc]
              else Inr (CoreStmt_VarDecl ghost varName Var rhsTy
                          (clear_metavars next_mv next_mv' coreTm),
                        vardecl_add_local env ghost varName rhsTy, next_mv')
          | Some ty \<Rightarrow>
              \<comment> \<open>Annotated: coerce the rhs to the annotation type; record the annotation.\<close>
              (case elab_type env elabEnv ghost ty of
                 Inl errs \<Rightarrow> Inl errs
               | Inr coreTy \<Rightarrow>
                   (case coerce_term_to_type env loc coreTm rhsTy coreTy of
                      Inl errs \<Rightarrow> Inl errs
                    | Inr coreTm' \<Rightarrow>
                        Inr (CoreStmt_VarDecl ghost varName Var coreTy
                               (clear_metavars next_mv next_mv' coreTm'),
                             vardecl_add_local env ghost varName coreTy, next_mv')))))"

(* VarDecl(Var) with an impure-call initializer. Takes the whole rhs term and
   pattern-matches BabTm_Call internally (undefined otherwise; callers guard on
   is_impure_call). With no annotation the declared type is the (metavar-free)
   call return type and no cast is applied; with an annotation the declared type
   is the annotation and reconcile_call_result chooses the cast. Emits
   CoreStmt_VarDeclCall. *)
definition elab_vardecl_impure ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> string
   \<Rightarrow> BabType option \<Rightarrow> BabTerm \<Rightarrow> nat
   \<Rightarrow> TypeError list + (CoreStatement \<times> CoreTyEnv \<times> nat)" where
  "elab_vardecl_impure env elabEnv ghost loc varName tyOpt tm next_mv =
    (case tm of
       BabTm_Call rloc callee rargs \<Rightarrow>
         (case elab_impure_call_term env elabEnv ghost rloc callee rargs next_mv of
            Inl errs \<Rightarrow> Inl errs
          | Inr (fnName, finalTyArgs, finalArgTms, retTy, next_mv') \<Rightarrow>
              (let mkCallStmt = \<lambda>varTy castOpt tyArgs argTms.
                         Inr (CoreStmt_VarDeclCall ghost varName varTy castOpt fnName
                                (map (clear_metavars_type next_mv next_mv') tyArgs)
                                (map (clear_metavars next_mv next_mv') argTms),
                              vardecl_add_local env ghost varName varTy, next_mv')
               in (case tyOpt of
                     None \<Rightarrow>
                       \<comment> \<open>Inferred: declared type = return type; reject metavars; no cast.\<close>
                       if \<not> list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list retTy)
                       then Inl [TyErr_CannotInferType loc]
                       else mkCallStmt retTy None finalTyArgs finalArgTms
                   | Some ty \<Rightarrow>
                       \<comment> \<open>Annotated: declared type = annotation; pick castOpt.\<close>
                       (case elab_type env elabEnv ghost ty of
                          Inl errs \<Rightarrow> Inl errs
                        | Inr coreTy \<Rightarrow>
                            (case reconcile_call_result env loc finalTyArgs finalArgTms retTy coreTy of
                               Inl errs \<Rightarrow> Inl errs
                             | Inr (castOpt, tyArgs', argTms') \<Rightarrow>
                                 mkCallStmt coreTy castOpt tyArgs' argTms')))))
     | _ \<Rightarrow> undefined)"

(* VarDecl(Ref). The initializer must be a metavariable-free lvalue (this rejects
   `ref x = f();`, pure or impure, since a call result is not an lvalue). The new
   ref is const iff its base is read-only. Emits CoreStmt_VarDecl ... Ref. *)
definition elab_vardecl_ref ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> string \<Rightarrow> BabTerm option \<Rightarrow> nat
   \<Rightarrow> TypeError list + (CoreStatement \<times> CoreTyEnv \<times> nat)" where
  "elab_vardecl_ref env elabEnv ghost loc varName tmOpt next_mv =
    (case tmOpt of
       None \<Rightarrow> Inl [TyErr_RefDeclNeedsValue loc]
     | Some tm \<Rightarrow>
         (case elab_term env elabEnv ghost tm next_mv of
            Inl errs \<Rightarrow> Inl errs
          | Inr (coreTm, rhsTy, next_mv') \<Rightarrow>
              if \<not> is_lvalue coreTm then Inl [TyErr_RefDeclNeedsLvalue loc]
              else if \<not> list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)
              then Inl [TyErr_CannotInferType loc]
              else
                Inr (CoreStmt_VarDecl ghost varName Ref rhsTy
                        (clear_metavars next_mv next_mv' coreTm),
                     (vardecl_add_local env ghost varName rhsTy)
                       \<lparr> TE_ConstLocals := (if is_writable_lvalue env coreTm
                                            then fminus (TE_ConstLocals env) {|varName|}
                                            else finsert varName (TE_ConstLocals env)) \<rparr>,
                     next_mv')))"

(* ----- Assign branch helpers ----- *)

(* Assignment with a pure rhs: coerce the rhs to the lhs type (unify or integer
   cast). The environment is unchanged. Emits CoreStmt_Assign. *)
definition elab_assign_pure ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> CoreTerm \<Rightarrow> CoreType
   \<Rightarrow> BabTerm \<Rightarrow> nat \<Rightarrow> nat
   \<Rightarrow> TypeError list + (CoreStatement \<times> CoreTyEnv \<times> nat)" where
  "elab_assign_pure env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1 =
    (case elab_term env elabEnv ghost rhs next_mv1 of
       Inl errs \<Rightarrow> Inl errs
     | Inr (rhsTm, rhsTy, next_mv2) \<Rightarrow>
         (case coerce_term_to_type env loc rhsTm rhsTy lhsTy of
            Inl errs \<Rightarrow> Inl errs
          | Inr rhsTm' \<Rightarrow>
              Inr (CoreStmt_Assign ghost
                     (clear_metavars next_mv next_mv2 lhsTm)
                     (clear_metavars next_mv next_mv2 rhsTm'),
                   env, next_mv2)))"

(* Assignment with an impure-call rhs. Takes the whole rhs term and pattern-matches
   BabTm_Call internally (undefined otherwise; callers guard on is_impure_call).
   reconcile_call_result chooses the cast against the lhs type. The environment is
   unchanged. Emits CoreStmt_AssignCall. *)
definition elab_assign_impure ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> CoreTerm \<Rightarrow> CoreType
   \<Rightarrow> BabTerm \<Rightarrow> nat \<Rightarrow> nat
   \<Rightarrow> TypeError list + (CoreStatement \<times> CoreTyEnv \<times> nat)" where
  "elab_assign_impure env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1 =
    (case rhs of
       BabTm_Call rloc callee rargs \<Rightarrow>
         (case elab_impure_call_term env elabEnv ghost rloc callee rargs next_mv1 of
            Inl errs \<Rightarrow> Inl errs
          | Inr (fnName, finalTyArgs, finalArgTms, retTy, next_mv2) \<Rightarrow>
              (case reconcile_call_result env loc finalTyArgs finalArgTms retTy lhsTy of
                 Inl errs \<Rightarrow> Inl errs
               | Inr (castOpt, tyArgs', argTms') \<Rightarrow>
                   Inr (CoreStmt_AssignCall ghost
                          (clear_metavars next_mv next_mv2 lhsTm)
                          castOpt fnName
                          (map (clear_metavars_type next_mv next_mv2) tyArgs')
                          (map (clear_metavars next_mv next_mv2) argTms'),
                        env, next_mv2)))
     | _ \<Rightarrow> undefined)"


(* ========================================================================== *)
(* Main statement elaboration functions *)
(* ========================================================================== *)

(* elab_statement translates a Babylon AST statement (BabStatement) into a 
   Core statement (CoreStatement). Like elab_term, it threads a metavariable  
   counter (nat) for the fresh type variables that term elaboration may       
   allocate; unlike elab_term, a statement transforms the type environment    
   (e.g. a VarDecl adds a local), so it also returns the updated CoreTyEnv    
   (mirroring core_statement_type, which is the spec the output must satisfy). *)

(* On success it returns (elaborated statement, transformed env, advanced
   counter); on failure a list of TypeErrors. elab_statement_list threads the
   env left-to-right through the statements. *)

function (sequential)
  elab_statement :: "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> BabStatement \<Rightarrow> nat
                      \<Rightarrow> TypeError list + (CoreStatement \<times> CoreTyEnv \<times> nat)"
and elab_statement_list :: "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> BabStatement list \<Rightarrow> nat
                           \<Rightarrow> TypeError list + (CoreStatement list \<times> CoreTyEnv \<times> nat)"
where

  (* Variable declaration.
     The surface form must supply a type annotation, an initializer, or both
     (`var x;` with neither is rejected). The chosen Core type is the
     annotation when present, otherwise the inferred type of the initializer
     (which must contain no unresolved metavariables, mirroring BabTm_Let).
     With an annotation but no initializer the variable is default-initialized
     via CoreTm_Default. A Ref declaration must have an initializer that
     elaborates to an lvalue.

     The actual work is delegated to per-branch helpers (above):
     elab_vardecl_pure / elab_vardecl_impure / elab_vardecl_ref; this clause just
     dispatches. An initializer that is_impure_call routes to elab_vardecl_impure
     (emitting CoreStmt_VarDeclCall); any other initializer routes to
     elab_vardecl_pure (emitting CoreStmt_VarDecl). *)
  "elab_statement env elabEnv ghost
       (BabStmt_VarDecl loc varName vorf tyOpt tmOpt) next_mv =
    (case vorf of
       Var \<Rightarrow>
         (case (tyOpt, tmOpt) of
            (None, None) \<Rightarrow> Inl [TyErr_VarDeclNeedsTypeOrValue loc]
          | (Some ty, None) \<Rightarrow>
              \<comment> \<open>Default-initialized: use the annotation type.\<close>
              (case elab_type env elabEnv ghost ty of
                 Inl errs \<Rightarrow> Inl errs
               | Inr coreTy \<Rightarrow>
                   Inr (CoreStmt_VarDecl ghost varName Var coreTy (CoreTm_Default coreTy),
                        vardecl_add_local env ghost varName coreTy, next_mv))
          | (_, Some tm) \<Rightarrow>
              if is_impure_call env elabEnv tm
              then elab_vardecl_impure env elabEnv ghost loc varName tyOpt tm next_mv
              else elab_vardecl_pure   env elabEnv ghost loc varName tyOpt tm next_mv)
     | Ref \<Rightarrow> elab_vardecl_ref env elabEnv ghost loc varName tmOpt next_mv)"

| "elab_statement env elabEnv ghost (BabStmt_Fix loc varName ty) next_mv = undefined"

| "elab_statement env elabEnv ghost (BabStmt_Obtain loc varName ty tm) next_mv = undefined"

| "elab_statement env elabEnv ghost (BabStmt_Use loc tm) next_mv = undefined"

  (* Assignment.
     Elaborate the lhs; it must be a writable lvalue of a fully-resolved
     (metavariable-free) type. The rhs is reconciled to the lhs type, with the
     work delegated to per-branch helpers (above): an is_impure_call rhs routes to
     elab_assign_impure (emitting CoreStmt_AssignCall); any other rhs (including
     pure / data-constructor calls) routes to elab_assign_pure (emitting
     CoreStmt_Assign). *)
| "elab_statement env elabEnv ghost (BabStmt_Assign loc lhs rhs) next_mv =
    \<comment> \<open>Elaborate lhs (the assignment target).\<close>
    (case elab_term env elabEnv ghost lhs next_mv of
       Inl errs \<Rightarrow> Inl errs
     | Inr (lhsTm, lhsTy, next_mv1) \<Rightarrow>
         \<comment> \<open>Check lhs is a writable lvalue of a ground type (no metavars).\<close>
         if \<not> is_writable_lvalue env lhsTm then Inl [TyErr_NotWritableLvalue loc]
         else if \<not> list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list lhsTy)
         then Inl [TyErr_CannotInferType loc]
         else if is_impure_call env elabEnv rhs
         then elab_assign_impure env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1
         else elab_assign_pure   env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1)"

| "elab_statement env elabEnv ghost (BabStmt_Swap loc lhs rhs) next_mv = undefined"

| "elab_statement env elabEnv ghost (BabStmt_Return loc tmOpt) next_mv = undefined"

| "elab_statement env elabEnv ghost (BabStmt_Assert loc condOpt proofBody) next_mv = undefined"

  (* Assume: elaborate the predicate in Ghost mode (matching the Core rule, which
     checks the term in Ghost context), require it to be Bool, and leave the
     environment unchanged. *)
| "elab_statement env elabEnv ghost (BabStmt_Assume loc tm) next_mv =
    (case elab_term env elabEnv Ghost tm next_mv of
       Inl errs \<Rightarrow> Inl errs
     | Inr (coreTm, ty, next_mv') \<Rightarrow>
         if ty = CoreTy_Bool
         then Inr (CoreStmt_Assume (clear_metavars next_mv next_mv' coreTm), env, next_mv')
         else Inl [TyErr_TypeMismatch loc CoreTy_Bool ty])"

| "elab_statement env elabEnv ghost (BabStmt_If loc cond thenB elseB) next_mv = undefined"

| "elab_statement env elabEnv ghost (BabStmt_While loc cond attrs body) next_mv = undefined"

| "elab_statement env elabEnv ghost (BabStmt_Call loc tm) next_mv = undefined"

| "elab_statement env elabEnv ghost (BabStmt_Match loc scrut arms) next_mv = undefined"

  (* ShowHide: no term, no environment change, counter unchanged. *)
| "elab_statement env elabEnv ghost (BabStmt_ShowHide loc sh name) next_mv =
    Inr (CoreStmt_ShowHide sh name, env, next_mv)"

  (* Ghost: elaborate the inner statement in Ghost mode. *)
| "elab_statement env elabEnv ghost (BabStmt_Ghost loc inner) next_mv =
    elab_statement env elabEnv Ghost inner next_mv"

  (* Statement lists: thread the environment and counter left-to-right. *)
| "elab_statement_list env elabEnv ghost [] next_mv = Inr ([], env, next_mv)"
| "elab_statement_list env elabEnv ghost (stmt # stmts) next_mv =
    (case elab_statement env elabEnv ghost stmt next_mv of
       Inl errs \<Rightarrow> Inl errs
     | Inr (coreStmt, env', next_mv1) \<Rightarrow>
         (case elab_statement_list env' elabEnv ghost stmts next_mv1 of
            Inl errs \<Rightarrow> Inl errs
          | Inr (coreStmts, env'', next_mv2) \<Rightarrow>
              Inr (coreStmt # coreStmts, env'', next_mv2)))"

  by pat_completeness auto
  termination
    by (relation "measure (case_sum (\<lambda>(_, _, _, stmt, _). size stmt)
                                     (\<lambda>(_, _, _, stmts, _). size_list size stmts))")
       auto

end
