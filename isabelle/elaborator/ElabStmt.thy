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
(* Helpers for VarDecl, Assign, etc. *)
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

(* ----- Swap branch helper ----- *)

(* Swap of two writable lvalues. The lhs has already been elaborated by the caller
   (giving lhsTm of type lhsTy, a writable lvalue of a metavariable-free type,
   counter advanced to next_mv1). This elaborates the rhs (pure), requires it to be
   a writable lvalue whose type is EXACTLY lhsTy (no coercion, unlike Assign), and
   emits CoreStmt_Swap. The environment is unchanged. *)
definition elab_swap ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> CoreTerm \<Rightarrow> CoreType
   \<Rightarrow> BabTerm \<Rightarrow> nat \<Rightarrow> nat
   \<Rightarrow> TypeError list + (CoreStatement \<times> CoreTyEnv \<times> nat)" where
  "elab_swap env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1 =
    (case elab_term env elabEnv ghost rhs next_mv1 of
       Inl errs \<Rightarrow> Inl errs
     | Inr (rhsTm, rhsTy, next_mv2) \<Rightarrow>
         if \<not> is_writable_lvalue env rhsTm then Inl [TyErr_NotWritableLvalue loc]
         else if rhsTy \<noteq> lhsTy then Inl [TyErr_TypeMismatch loc lhsTy rhsTy]
         else
           Inr (CoreStmt_Swap ghost
                  (clear_metavars next_mv next_mv2 lhsTm)
                  (clear_metavars next_mv next_mv2 rhsTm),
                env, next_mv2))"


(* ----- Fix branch helper ----- *)

(* Fix introduces a ghost local `varName : ty` corresponding to an enclosing
   universally-quantified proof goal `forall x : ty. P(x)`. It is only valid in
   Ghost mode, at the top level of a proof body (TE_ProofTopLevel), when there is
   such a goal whose bound-variable type matches the (elaborated) annotation. The
   resulting env adds the const ghost local and replaces the proof goal with the
   quantifier body P (the Core rule does not alpha-rename x; the goal is only
   consumed structurally). Allocates no fresh metavariables. Emits CoreStmt_Fix. *)
definition elab_fix ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> string \<Rightarrow> BabType \<Rightarrow> nat
   \<Rightarrow> TypeError list + (CoreStatement \<times> CoreTyEnv \<times> nat)" where
  "elab_fix env elabEnv ghost loc varName ty next_mv =
    (if ghost \<noteq> Ghost then Inl [TyErr_RequiresGhostContext loc]
     else case TE_ProofGoal env of
            Some (CoreTm_Quantifier Quant_Forall _ qVarTy bodyTm) \<Rightarrow>
              (if \<not> TE_ProofTopLevel env then Inl [TyErr_FixNotAtProofTopLevel loc]
               else case elab_type env elabEnv Ghost ty of
                      Inl errs \<Rightarrow> Inl errs
                    | Inr coreTy \<Rightarrow>
                        if qVarTy \<noteq> coreTy then Inl [TyErr_TypeMismatch loc qVarTy coreTy]
                        else Inr (CoreStmt_Fix varName coreTy,
                                  env \<lparr> TE_LocalVars   := fmupd varName coreTy (TE_LocalVars env),
                                        TE_GhostLocals := finsert varName (TE_GhostLocals env),
                                        TE_ConstLocals := finsert varName (TE_ConstLocals env),
                                        TE_ProofGoal   := Some bodyTm \<rparr>,
                                  next_mv))
          | _ \<Rightarrow> Inl [TyErr_FixNoForallGoal loc])"


(* ----- Use branch helper ----- *)

(* Use supplies a witness for an enclosing existential proof goal
   `exists x : T. P(x)`. It is only valid in Ghost mode, when there is such a goal;
   the witness term is elaborated (pure) and coerced (unify-or-integer-cast) to the
   bound-variable type T. The resulting env replaces the proof goal with the quantifier
   body P (witness is NOT substituted in). The `is_well_kinded env qVarTy` guard is
   not expected to fail in practice. *)
definition elab_use ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> BabTerm \<Rightarrow> nat
   \<Rightarrow> TypeError list + (CoreStatement \<times> CoreTyEnv \<times> nat)" where
  "elab_use env elabEnv ghost loc tm next_mv =
    (if ghost \<noteq> Ghost then Inl [TyErr_RequiresGhostContext loc]
     else case TE_ProofGoal env of
            Some (CoreTm_Quantifier Quant_Exists _ qVarTy bodyTm) \<Rightarrow>
              (if \<not> is_well_kinded env qVarTy
               then Inl [TyErr_InternalError_IllKindedProofGoal loc]
               else case elab_term env elabEnv Ghost tm next_mv of
                      Inl errs \<Rightarrow> Inl errs
                    | Inr (coreTm, tmTy, next_mv') \<Rightarrow>
                        (case coerce_term_to_type env loc coreTm tmTy qVarTy of
                           Inl errs \<Rightarrow> Inl errs
                         | Inr coreTm' \<Rightarrow>
                             Inr (CoreStmt_Use (clear_metavars next_mv next_mv' coreTm'),
                                  env \<lparr> TE_ProofGoal := Some bodyTm \<rparr>, next_mv')))
          | _ \<Rightarrow> Inl [TyErr_UseNoExistsGoal loc])"


(* ----- While branch helpers ----- *)

(* Validate a while loop's attribute list and split it into the invariant terms (in
   order) and the single decreases term. Every attribute must be a `BabAttr_Invariant`
   or a `BabAttr_Decreases` (anything else is an error), and there must be exactly one
   `decreases`. `loc` is the while-loop location (used for the "needs one decreases"
   error). *)
fun collect_while_attributes ::
  "Location \<Rightarrow> BabAttribute list \<Rightarrow> TypeError list + (BabTerm list \<times> BabTerm list)" where
  "collect_while_attributes loc [] = Inr ([], [])"
| "collect_while_attributes loc (attr # attrs) =
    (case collect_while_attributes loc attrs of
       Inl errs \<Rightarrow> Inl errs
     | Inr (invs, decrs) \<Rightarrow>
         (case attr of
            BabAttr_Invariant _ tm \<Rightarrow> Inr (tm # invs, decrs)
          | BabAttr_Decreases _ tm \<Rightarrow> Inr (invs, tm # decrs)
          | _ \<Rightarrow> Inl [TyErr_InvalidWhileAttribute (bab_attribute_location attr)]))"

(* Elaborate a list of while-loop invariant terms. Each is elaborated in Ghost mode and
   its type unified with Bool (as in Assume); the unifier is applied and the interval
   metavariables cleared, so each cleared term typechecks to Bool in the original env.
   Threads the metavariable counter left-to-right. *)
fun elab_while_invariants ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> BabTerm list \<Rightarrow> nat
   \<Rightarrow> TypeError list + (CoreTerm list \<times> nat)" where
  "elab_while_invariants env elabEnv [] next_mv = Inr ([], next_mv)"
| "elab_while_invariants env elabEnv (invTm # invs) next_mv =
    (case elab_term env elabEnv Ghost invTm next_mv of
       Inl errs \<Rightarrow> Inl errs
     | Inr (coreInv, invTy, next_mv1) \<Rightarrow>
         (case unify (\<lambda>n. n |\<notin>| TE_TypeVars env) invTy CoreTy_Bool of
            None \<Rightarrow> Inl [TyErr_TypeMismatch (bab_term_location invTm) CoreTy_Bool invTy]
          | Some subst \<Rightarrow>
              (case elab_while_invariants env elabEnv invs next_mv1 of
                 Inl errs \<Rightarrow> Inl errs
               | Inr (rest, next_mv2) \<Rightarrow>
                   Inr (clear_metavars next_mv next_mv1 (apply_subst_to_term subst coreInv) # rest,
                        next_mv2))))"

(* Elaborate the "header" of a while loop, given the invariant terms and the (single)
   decreases term already extracted from the attribute list. The condition is elaborated in
   the ambient ghost mode and coerced to Bool (like BabStmt_If); the invariants are each
   elaborated in Ghost mode and coerced to Bool; the decreases term is elaborated in Ghost
   mode and must have a valid decreases type. Returns the cleared condition, the cleared
   invariant terms, the cleared decreases term, and the advanced counter. The body
   elaboration (which recurses into elab_statement_list) is left to the main clause. *)
definition elab_while_header ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> BabTerm \<Rightarrow> BabTerm list \<Rightarrow> BabTerm \<Rightarrow> nat
   \<Rightarrow> TypeError list + (CoreTerm \<times> CoreTerm list \<times> CoreTerm \<times> nat)" where
  "elab_while_header env elabEnv ghost loc cond invs decr next_mv =
    (case elab_term env elabEnv ghost cond next_mv of
       Inl errs \<Rightarrow> Inl errs
     | Inr (coreCond, condTy, next_mv1) \<Rightarrow>
         (case unify (\<lambda>n. n |\<notin>| TE_TypeVars env) condTy CoreTy_Bool of
            None \<Rightarrow> Inl [TyErr_TypeMismatch loc CoreTy_Bool condTy]
          | Some subst \<Rightarrow>
              (case elab_while_invariants env elabEnv invs next_mv1 of
                 Inl errs \<Rightarrow> Inl errs
               | Inr (coreInvars, next_mv2) \<Rightarrow>
                   (case elab_term env elabEnv Ghost decr next_mv2 of
                      Inl errs \<Rightarrow> Inl errs
                    | Inr (coreDecr, decrTy, next_mv3) \<Rightarrow>
                        if \<not> is_valid_decreases_type decrTy
                        then Inl [TyErr_InvalidDecreasesType (bab_term_location decr) decrTy]
                        else
                          Inr (clear_metavars next_mv next_mv1 (apply_subst_to_term subst coreCond),
                               coreInvars,
                               clear_metavars next_mv2 next_mv3 coreDecr,
                               next_mv3)))))"


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

  (* Variable declaration: Introduce a new variable into scope. The user can supply
     a type declaration, an initializer term, or both. The initializer term can be either
     pure or impure. *)
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

  (* Fix: Introduce a ghost local corresponding to an enclosing universal TE_ProofGoal. *)
| "elab_statement env elabEnv ghost (BabStmt_Fix loc varName ty) next_mv =
    elab_fix env elabEnv ghost loc varName ty next_mv"

  (* Obtain: Introduce a ghost local satisfying a given boolean condition. *)
| "elab_statement env elabEnv ghost (BabStmt_Obtain loc varName ty tm) next_mv =
    (case elab_type env elabEnv Ghost ty of
       Inl errs \<Rightarrow> Inl errs
     | Inr coreTy \<Rightarrow>
         (let env' = vardecl_add_local env Ghost varName coreTy
          in case elab_term env' elabEnv Ghost tm next_mv of
               Inl errs \<Rightarrow> Inl errs
             | Inr (coreTm, condTy, next_mv') \<Rightarrow>
                 (case unify (\<lambda>n. n |\<notin>| TE_TypeVars env) condTy CoreTy_Bool of
                    None \<Rightarrow> Inl [TyErr_TypeMismatch loc CoreTy_Bool condTy]
                  | Some subst \<Rightarrow>
                      Inr (CoreStmt_Obtain varName coreTy
                             (clear_metavars next_mv next_mv'
                                (apply_subst_to_term subst coreTm)),
                           env', next_mv'))))"

  (* Use: Supply a witness for an enclosing existential TE_ProofGoal. *)
| "elab_statement env elabEnv ghost (BabStmt_Use loc tm) next_mv =
    elab_use env elabEnv ghost loc tm next_mv"

  (* Assignment. Lhs term must be a writable lvalue. Rhs term can be either pure or
     impure, and must match the type of the lhs. *)
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

  (* Swap: Swap two writable lvalues. Both terms must be writable lvalues and they
     must have exactly the same type. (No unifying is necessary, because lvalues always
     have ground types.) *)
| "elab_statement env elabEnv ghost (BabStmt_Swap loc lhs rhs) next_mv =
    \<comment> \<open>Elaborate lhs (the first swap operand).\<close>
    (case elab_term env elabEnv ghost lhs next_mv of
       Inl errs \<Rightarrow> Inl errs
     | Inr (lhsTm, lhsTy, next_mv1) \<Rightarrow>
         \<comment> \<open>Check lhs is a writable lvalue of a ground type (no metavars).\<close>
         if \<not> is_writable_lvalue env lhsTm then Inl [TyErr_NotWritableLvalue loc]
         else if \<not> list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list lhsTy)
         then Inl [TyErr_CannotInferType loc]
         else elab_swap env elabEnv ghost loc lhsTm lhsTy rhs next_mv next_mv1)"

  (* Return from current function. The term must be pure and must match the current
     function's return type (or be absent if the current function is void). *)
| "elab_statement env elabEnv ghost (BabStmt_Return loc tmOpt) next_mv =
    (if ghost \<noteq> TE_FunctionGhost env then Inl [TyErr_ReturnInGhostContext loc]
     else if EE_CurrentFunctionVoid elabEnv then
       \<comment> \<open>Void function: only a bare `return;` is legal; it returns unit.\<close>
       (case tmOpt of
          None \<Rightarrow> Inr (CoreStmt_Return (CoreTm_Record []), env, next_mv)
        | Some _ \<Rightarrow> Inl [TyErr_VoidReturnWithValue loc])
     else
       \<comment> \<open>Non-void function: a value is required; coerce it to the return type.\<close>
       (case tmOpt of
          None \<Rightarrow> Inl [TyErr_NonVoidReturnNeedsValue loc]
        | Some tm \<Rightarrow>
            (case elab_term env elabEnv ghost tm next_mv of
               Inl errs \<Rightarrow> Inl errs
             | Inr (coreTm, tmTy, next_mv') \<Rightarrow>
                 (case coerce_term_to_type env loc coreTm tmTy (TE_ReturnType env) of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr coreTm' \<Rightarrow>
                      Inr (CoreStmt_Return (clear_metavars next_mv next_mv' coreTm'),
                           env, next_mv')))))"

  (* Assert: asserts that a given boolean condition is true. This creates a proof
     obligation. An optional proof body (list of statements) can be given; TE_ProofGoal
     will be set appropriately when typechecking these. *)
| "elab_statement env elabEnv ghost (BabStmt_Assert loc condOpt proofBody) next_mv =
    (case condOpt of
       None \<Rightarrow>
         \<comment> \<open>`assert *`: the asserted goal is the current proof goal, which must exist.\<close>
         (if TE_ProofGoal env = None then Inl [TyErr_AssertStarNoGoal loc]
          else let goalEnv = env \<lparr> TE_ProofTopLevel := True \<rparr>
               in (case elab_statement_list goalEnv elabEnv Ghost proofBody next_mv of
                     Inl errs \<Rightarrow> Inl errs
                   | Inr (coreBody, _, next_mv') \<Rightarrow>
                       Inr (CoreStmt_Assert None coreBody, env, next_mv')))
     | Some cond \<Rightarrow>
         \<comment> \<open>`assert cond`: elaborate cond to Bool (as in Assume), install it as the goal.\<close>
         (case elab_term env elabEnv Ghost cond next_mv of
            Inl errs \<Rightarrow> Inl errs
          | Inr (coreCond, condTy, next_mv1) \<Rightarrow>
              (case unify (\<lambda>n. n |\<notin>| TE_TypeVars env) condTy CoreTy_Bool of
                 None \<Rightarrow> Inl [TyErr_TypeMismatch loc CoreTy_Bool condTy]
               | Some subst \<Rightarrow>
                   let clearedCond =
                         clear_metavars next_mv next_mv1 (apply_subst_to_term subst coreCond);
                       goalEnv = env \<lparr> TE_ProofGoal := Some clearedCond,
                                       TE_ProofTopLevel := True \<rparr>
                   in (case elab_statement_list goalEnv elabEnv Ghost proofBody next_mv1 of
                         Inl errs \<Rightarrow> Inl errs
                       | Inr (coreBody, _, next_mv') \<Rightarrow>
                           Inr (CoreStmt_Assert (Some clearedCond) coreBody, env, next_mv')))))"

  (* Assume: states without proof that a given boolean condition is true. This can be 
     used to bypass the verifier. *)
| "elab_statement env elabEnv ghost (BabStmt_Assume loc tm) next_mv =
    (case elab_term env elabEnv Ghost tm next_mv of
       Inl errs \<Rightarrow> Inl errs
     | Inr (coreTm, ty, next_mv') \<Rightarrow>
         (case unify (\<lambda>n. n |\<notin>| TE_TypeVars env) ty CoreTy_Bool of
            None \<Rightarrow> Inl [TyErr_TypeMismatch loc CoreTy_Bool ty]
          | Some subst \<Rightarrow>
              Inr (CoreStmt_Assume
                     (clear_metavars next_mv next_mv' (apply_subst_to_term subst coreTm)),
                   env, next_mv')))"

  (* If-then-else: Evaluate a boolean condition and branch to one of two statement blocks.
     Each block creates a new variable scope. Elaborates to CoreStmt_Match. *)
| "elab_statement env elabEnv ghost (BabStmt_If loc cond thenB elseB) next_mv =
    (case elab_term env elabEnv ghost cond next_mv of
       Inl errs \<Rightarrow> Inl errs
     | Inr (coreCond, condTy, next_mv1) \<Rightarrow>
         (case unify (\<lambda>n. n |\<notin>| TE_TypeVars env) condTy CoreTy_Bool of
            None \<Rightarrow> Inl [TyErr_TypeMismatch loc CoreTy_Bool condTy]
          | Some subst \<Rightarrow>
              (let armEnv = env \<lparr> TE_ProofTopLevel := False \<rparr>
               in case elab_statement_list armEnv elabEnv ghost thenB next_mv1 of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr (coreThen, _, next_mv2) \<Rightarrow>
                      (case elab_statement_list armEnv elabEnv ghost elseB next_mv2 of
                         Inl errs \<Rightarrow> Inl errs
                       | Inr (coreElse, _, next_mv3) \<Rightarrow>
                           Inr (CoreStmt_Match ghost
                                  (clear_metavars next_mv next_mv1
                                     (apply_subst_to_term subst coreCond))
                                  [(CorePat_Bool True, coreThen),
                                   (CorePat_Bool False, coreElse)],
                                env, next_mv3)))))"

  (* While: loop while a condition remains true. The cond must be boolean. The attrs can
     include only "invariant" and "decreases" (with proper types) and there must be exactly
     one "decreases". The body is typechecked in a new scope. *)
| "elab_statement env elabEnv ghost (BabStmt_While loc cond attrs body) next_mv =
    \<comment> \<open>Validate the attribute list and require exactly one `decreases`.\<close>
    (case collect_while_attributes loc attrs of
       Inl errs \<Rightarrow> Inl errs
     | Inr (invs, decrs) \<Rightarrow>
         (case decrs of
            [decr] \<Rightarrow>
              \<comment> \<open>Elaborate the condition / invariants / decreases (header), then the body.\<close>
              (case elab_while_header env elabEnv ghost loc cond invs decr next_mv of
                 Inl errs \<Rightarrow> Inl errs
               | Inr (clearedCond, coreInvars, clearedDecr, next_mv3) \<Rightarrow>
                   (let bodyEnv = env \<lparr> TE_ProofTopLevel := False \<rparr>
                    in case elab_statement_list bodyEnv elabEnv ghost body next_mv3 of
                         Inl errs \<Rightarrow> Inl errs
                       | Inr (coreBody, _, next_mv4) \<Rightarrow>
                           Inr (CoreStmt_While ghost clearedCond coreInvars clearedDecr coreBody,
                                env, next_mv4)))
          | _ \<Rightarrow> Inl [TyErr_WhileNeedsOneDecreases loc]))"

  (* Call an impure function, disregarding the return value. TODO (needs Core change). *)
| "elab_statement env elabEnv ghost (BabStmt_Call loc tm) next_mv = undefined"

  (* Match: elaborates to CoreStmt_Match. *)
| "elab_statement env elabEnv ghost (BabStmt_Match loc scrut arms) next_mv = undefined"

  (* ShowHide: show or hide a name from the verifier. Has no effect on typechecking.
     TODO: We should at least check that the name is in scope. *)
| "elab_statement env elabEnv ghost (BabStmt_ShowHide loc sh name) next_mv =
    Inr (CoreStmt_ShowHide sh name, env, next_mv)"

  (* Ghost: This is just a marker to say that the inner statements should be typechecked
     in Ghost mode. It does not create a separate nested scope. *)
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
