theory ElabStmt
  imports ElabTerm "../core/CoreStmtTypecheck"
begin

(* ========================================================================== *)
(* Statement elaboration                                                      *)
(*                                                                            *)
(* elab_statement translates a Babylon AST statement (BabStatement) into a    *)
(* Core statement (CoreStatement). Like elab_term, it threads a metavariable  *)
(* counter (nat) for the fresh type variables that term elaboration may       *)
(* allocate; unlike elab_term, a statement transforms the type environment    *)
(* (e.g. a VarDecl adds a local), so it also returns the updated CoreTyEnv    *)
(* (mirroring core_statement_type, which is the spec the output must satisfy). *)
(*                                                                            *)
(* On success it returns (elaborated statement, transformed env, advanced     *)
(* counter); on failure a list of TypeErrors. elab_statement_list threads the *)
(* env left-to-right through the statements.                                  *)
(*                                                                            *)
(* ========================================================================== *)

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
     elaborates to an lvalue. *)
  "elab_statement env elabEnv ghost
       (BabStmt_VarDecl loc declGhost varName vorf tyOpt tmOpt) next_mv =
    (if ghost = Ghost \<and> declGhost = NotGhost then
       \<comment> \<open>A non-ghost declaration is not allowed inside a ghost context
           (mirrors the core_statement_type VarDecl rule's
           ghost = Ghost \<longrightarrow> declGhost = Ghost guard).\<close>
       Inl [TyErr_RequiresGhostContext loc]
     else
     let declMode = (if declGhost = Ghost then Ghost else ghost);
         add_var = \<lambda>varTy. env \<lparr>
             TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
             TE_GhostLocals := (if declGhost = Ghost
                                then finsert varName (TE_GhostLocals env)
                                else fminus (TE_GhostLocals env) {|varName|}) \<rparr>
     in case vorf of
          Var \<Rightarrow>
            (case (tyOpt, tmOpt) of
               (None, None) \<Rightarrow> Inl [TyErr_VarDeclNeedsTypeOrValue loc]
             | (Some ty, None) \<Rightarrow>
                 \<comment> \<open>Default-initialized: use the annotation type.\<close>
                 (case elab_type env elabEnv declMode ty of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr coreTy \<Rightarrow>
                      Inr (CoreStmt_VarDecl declGhost varName Var coreTy (CoreTm_Default coreTy),
                           (add_var coreTy) \<lparr> TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>,
                           next_mv))
             | (None, Some tm) \<Rightarrow>
                 \<comment> \<open>Inferred type from the initializer; reject unresolved metavariables.\<close>
                 (case elab_term env elabEnv declMode tm next_mv of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr (coreTm, rhsTy, next_mv') \<Rightarrow>
                      if \<not> list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)
                      then Inl [TyErr_CannotInferType loc]
                      else
                        Inr (CoreStmt_VarDecl declGhost varName Var rhsTy coreTm,
                             (add_var rhsTy) \<lparr> TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>,
                             next_mv'))
             | (Some ty, Some tm) \<Rightarrow>
                 \<comment> \<open>Annotated initializer: elaborate both, then reconcile the rhs type
                     with the (metavariable-free) annotation. We first try to unify
                     (handling the exact-match case and binding any flex
                     metavariables in the rhs type); failing that, if both types are
                     integers we insert an integer cast, mirroring BabTm_Cast and the
                     coercion that unify_and_coerce performs for calls.\<close>
                 (case elab_type env elabEnv declMode ty of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr coreTy \<Rightarrow>
                      (case elab_term env elabEnv declMode tm next_mv of
                         Inl errs \<Rightarrow> Inl errs
                       | Inr (coreTm, rhsTy, next_mv') \<Rightarrow>
                           (case unify (\<lambda>n. n |\<notin>| TE_TypeVars env) rhsTy coreTy of
                              Some subst \<Rightarrow>
                                Inr (CoreStmt_VarDecl declGhost varName Var coreTy
                                        (apply_subst_to_term subst coreTm),
                                     (add_var coreTy) \<lparr> TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>,
                                     next_mv')
                            | None \<Rightarrow>
                                if is_integer_type rhsTy \<and> is_integer_type coreTy
                                then
                                  \<comment> \<open>e.g. var x: i16 = 10; casts the i32 rhs to i16.\<close>
                                  Inr (CoreStmt_VarDecl declGhost varName Var coreTy
                                          (CoreTm_Cast coreTy coreTm),
                                       (add_var coreTy) \<lparr> TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>,
                                       next_mv')
                                else Inl [TyErr_TypeMismatch loc coreTy rhsTy]))))
        | Ref \<Rightarrow>
            (case tmOpt of
               None \<Rightarrow> Inl [TyErr_RefDeclNeedsValue loc]
             | Some tm \<Rightarrow>
                 (case elab_term env elabEnv declMode tm next_mv of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr (coreTm, rhsTy, next_mv') \<Rightarrow>
                      if \<not> is_lvalue coreTm then Inl [TyErr_RefDeclNeedsLvalue loc]
                      else if \<not> list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)
                      then Inl [TyErr_CannotInferType loc]
                      else
                        (let constUpd = (if is_writable_lvalue env coreTm
                                         then fminus (TE_ConstLocals env) {|varName|}
                                         else finsert varName (TE_ConstLocals env))
                         in Inr (CoreStmt_VarDecl declGhost varName Ref rhsTy coreTm,
                                 (add_var rhsTy) \<lparr> TE_ConstLocals := constUpd \<rparr>,
                                 next_mv')))))"

| "elab_statement env elabEnv ghost (BabStmt_Fix loc varName ty) next_mv = undefined"

| "elab_statement env elabEnv ghost (BabStmt_Obtain loc varName ty tm) next_mv = undefined"

| "elab_statement env elabEnv ghost (BabStmt_Use loc tm) next_mv = undefined"

| "elab_statement env elabEnv ghost (BabStmt_Assign loc assignGhost lhs rhs) next_mv = undefined"

| "elab_statement env elabEnv ghost (BabStmt_Swap loc swapGhost lhs rhs) next_mv = undefined"

| "elab_statement env elabEnv ghost (BabStmt_Return loc returnGhost tmOpt) next_mv = undefined"

| "elab_statement env elabEnv ghost (BabStmt_Assert loc condOpt proofBody) next_mv = undefined"

  (* Assume: elaborate the predicate in Ghost mode (matching the Core rule, which
     checks the term in Ghost context), require it to be Bool, and leave the
     environment unchanged. *)
| "elab_statement env elabEnv ghost (BabStmt_Assume loc tm) next_mv =
    (case elab_term env elabEnv Ghost tm next_mv of
       Inl errs \<Rightarrow> Inl errs
     | Inr (coreTm, ty, next_mv') \<Rightarrow>
         if ty = CoreTy_Bool
         then Inr (CoreStmt_Assume coreTm, env, next_mv')
         else Inl [TyErr_TypeMismatch loc CoreTy_Bool ty])"

| "elab_statement env elabEnv ghost (BabStmt_If loc ifGhost cond thenB elseB) next_mv = undefined"

| "elab_statement env elabEnv ghost (BabStmt_While loc whileGhost cond attrs body) next_mv = undefined"

| "elab_statement env elabEnv ghost (BabStmt_Call loc callGhost tm) next_mv = undefined"

| "elab_statement env elabEnv ghost (BabStmt_Match loc matchGhost scrut arms) next_mv = undefined"

  (* ShowHide: no term, no environment change, counter unchanged. *)
| "elab_statement env elabEnv ghost (BabStmt_ShowHide loc sh name) next_mv =
    Inr (CoreStmt_ShowHide sh name, env, next_mv)"

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
