theory CoreStmtTypecheck
  imports CoreTypecheck CoreTypeProps TypeSubst
begin

(* ========================================================================== *)
(* Impure function-call typechecking                                          *)
(* ========================================================================== *)

(* Typecheck an impure call (e.g. one occurring in CoreStmt_VarDeclCall or
   CoreStmt_AssignCall). The fnName must exist in the env, and the numbers of
   tyArgs and tmArgs must be correct. The tyArgs must be well-kinded, complete,
   and (in NotGhost mode) runtime types. An impure function (FI_Impure) can only
   be called in NotGhost mode, and only from an impure function
   (TE_FunctionImpure). For each argument:
     - Ref parameter: argument must be a writable lvalue of the expected
       (substituted) type.
     - Var parameter: argument is typechecked via core_term_type, so nested
       calls must be pure (only the outermost call is impure).    *)

definition core_impure_call_type ::
  "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> string \<Rightarrow> CoreType list \<Rightarrow> CoreTerm list \<Rightarrow> CoreType option" where
  "core_impure_call_type env ghost fnName tyArgs tmArgs =
    (case fmlookup (TE_Functions env) fnName of
       None \<Rightarrow> None
     | Some funInfo \<Rightarrow>
         if length tyArgs \<noteq> length (FI_TyArgs funInfo) then None
         else if \<not> list_all (is_well_kinded env) tyArgs then None
         else if \<not> list_all is_complete_type tyArgs then None
         else if ghost = NotGhost
                 \<and> (\<not> list_all (is_runtime_type env) tyArgs
                    \<or> FI_Ghost funInfo = Ghost) then None
         else if FI_Impure funInfo
                 \<and> (ghost = Ghost \<or> \<not> TE_FunctionImpure env) then None
         else if length tmArgs \<noteq> length (FI_TmArgs funInfo) then None
         else
           let tySubst = fmap_of_list (zip (FI_TyArgs funInfo) tyArgs);
               expectedArgTypes = map (\<lambda>(ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo);
               varOrRefs = map (\<lambda>(_, vor, _). vor) (FI_TmArgs funInfo);
               argModes = map (\<lambda>(_, _, gh). param_mode ghost gh) (FI_TmArgs funInfo)
           in \<comment> \<open>Each actual is checked in the mode determined by its parameter's
                  ghost flag. A ghost Ref parameter therefore requires a ghost lvalue.\<close>
              if list_all2 (\<lambda>(tm, vor) (expectedTy, mode).
                    case vor of
                      Var \<Rightarrow>
                        core_term_type env mode tm = Some expectedTy
                    | Ref \<Rightarrow>
                        is_writable_lvalue env tm
                        \<and> ghost_lvalue_ok env mode tm
                        \<and> core_term_type env mode tm = Some expectedTy)
                  (zip tmArgs varOrRefs) (zip expectedArgTypes argModes)
              then Some (apply_subst tySubst (FI_ReturnType funInfo))
              else None)"

(* The type produced by the optional cast applied to an impure call's return value.
   Returns `Some ty` if the function returns `ty` (after the cast), or `None` if the
   attempted cast was invalid. *)
definition cast_result_type ::
  "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> CoreType \<Rightarrow> CoreType option \<Rightarrow> CoreType option" where
  "cast_result_type env ghost retTy castOpt =
    (case castOpt of
       None \<Rightarrow> Some retTy
     | Some t \<Rightarrow>
         if cast_ok env retTy t
            \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env t)
         then Some t else None)"

(* The optional decreases-term of a While loop. It may be absent; if present it
   is a Ghost term whose type is a valid decreases type (see
   is_valid_decreases_type). *)
fun has_valid_decreases_type :: "CoreTyEnv \<Rightarrow> CoreTerm option \<Rightarrow> bool" where
  "has_valid_decreases_type env None = True"
| "has_valid_decreases_type env (Some decrTm) =
    (case core_term_type env Ghost decrTm of
       Some decrTy \<Rightarrow> is_valid_decreases_type decrTy
     | None \<Rightarrow> False)"


(* ========================================================================== *)
(* Statement typechecking *)
(* ========================================================================== *)

(* Statement typechecking transforms the type environment (e.g. VarDecl adds 
   a new variable). Therefore, core_statement_type returns a new env, or None
   if ill-typed. *)

function core_statement_type :: "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> CoreStatement \<Rightarrow> CoreTyEnv option"
and core_statement_list_type :: "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> CoreStatement list \<Rightarrow> CoreTyEnv option"
where

  (* Variable declaration (Var).
     The initializer is an ordinary (pure) term. Impure function-call initializers
     use CoreStmt_VarDeclCall instead.
     In executable code (NotGhost), the new variable must have complete type. *)
  "core_statement_type env ghost (CoreStmt_VarDecl declGhost varName Var varTy initTm) =
    (if (ghost = Ghost \<longrightarrow> declGhost = Ghost)
        \<and> is_well_kinded env varTy
        \<and> (declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy)
        \<and> (declGhost = NotGhost \<longrightarrow> is_complete_type varTy)
        \<and> core_term_type env declGhost initTm = Some varTy
     then Some (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                      TE_GhostLocals := (if declGhost = Ghost
                                       then finsert varName (TE_GhostLocals env)
                                       else fminus (TE_GhostLocals env) {|varName|}),
                      TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>)
     else None)"

  (* Variable declaration initialized from an impure function call.
     The call is typechecked by core_impure_call_type, and the (optionally cast) return
     type must equal the declared variable type. As for CoreStmt_VarDecl (Var), a
     non-ghost variable must have a complete type. *)
| "core_statement_type env ghost (CoreStmt_VarDeclCall declGhost varName varTy castOpt fnName tyArgs argTms) =
    (if (ghost = Ghost \<longrightarrow> declGhost = Ghost)
        \<and> is_well_kinded env varTy
        \<and> (declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy)
        \<and> (declGhost = NotGhost \<longrightarrow> is_complete_type varTy)
     then (case core_impure_call_type env declGhost fnName tyArgs argTms of
             Some retTy \<Rightarrow>
               if cast_result_type env declGhost retTy castOpt = Some varTy
               then Some (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                TE_GhostLocals := (if declGhost = Ghost
                                                 then finsert varName (TE_GhostLocals env)
                                                 else fminus (TE_GhostLocals env) {|varName|}),
                                TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>)
               else None
           | None \<Rightarrow> None)
     else None)"

  (* Variable declaration (Ref).
     The rhs must be a syntactic lvalue with the declared type. The new ref
     becomes const iff its base is read-only (a const local or a global). *)
| "core_statement_type env ghost (CoreStmt_VarDecl declGhost varName Ref varTy initTm) =
    (if (ghost = Ghost \<longrightarrow> declGhost = Ghost)
        \<and> is_well_kinded env varTy
        \<and> (declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy)
        \<and> is_lvalue initTm
        \<and> ghost_lvalue_ok env declGhost initTm  \<comment> \<open>Ghost code can't take refs to nonghost (even if readonly); use Var instead\<close>
        \<and> core_term_type env declGhost initTm = Some varTy
     then Some (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                      TE_GhostLocals := (if declGhost = Ghost
                                       then finsert varName (TE_GhostLocals env)
                                       else fminus (TE_GhostLocals env) {|varName|}),
                      TE_ConstLocals := (if is_writable_lvalue env initTm
                                        then fminus (TE_ConstLocals env) {|varName|}
                                        else finsert varName (TE_ConstLocals env)) \<rparr>)
     else None)"

  (* Assignment.
     The rhs is an ordinary (pure) term. Impure function-call rhs's use
     CoreStmt_AssignCall instead.
     A non-ghost assignment must be at a complete type. *)
| "core_statement_type env ghost (CoreStmt_Assign assignGhost lhsTm rhsTm) =
    (if (ghost = Ghost \<longrightarrow> assignGhost = Ghost)
        \<and> is_writable_lvalue env lhsTm
        \<and> ghost_lvalue_ok env assignGhost lhsTm
     then (case core_term_type env assignGhost lhsTm of
             Some lhsTy \<Rightarrow>
               if (assignGhost = NotGhost \<longrightarrow> is_complete_type lhsTy)
                  \<and> core_term_type env assignGhost rhsTm = Some lhsTy
               then Some env
               else None
           | None \<Rightarrow> None)
     else None)"

  (* Assignment whose rhs is an impure function call.
     The lhs must be a writable lvalue; the call's (optionally cast) return type
     must equal the lhs type. As for CoreStmt_Assign, a non-ghost assignment must
     be at a complete type. *)
| "core_statement_type env ghost (CoreStmt_AssignCall assignGhost lhsTm castOpt fnName tyArgs argTms) =
    (if (ghost = Ghost \<longrightarrow> assignGhost = Ghost)
        \<and> is_writable_lvalue env lhsTm
        \<and> ghost_lvalue_ok env assignGhost lhsTm
     then (case core_term_type env assignGhost lhsTm of
             Some lhsTy \<Rightarrow>
               (case core_impure_call_type env assignGhost fnName tyArgs argTms of
                  Some retTy \<Rightarrow>
                    if (assignGhost = NotGhost \<longrightarrow> is_complete_type lhsTy)
                       \<and> cast_result_type env assignGhost retTy castOpt = Some lhsTy
                    then Some env else None
                | None \<Rightarrow> None)
           | None \<Rightarrow> None)
     else None)"

  (* Return: the term must have the expected return type.
     We require ghost = TE_FunctionGhost env:
       - In a ghost function, we always typecheck in Ghost mode, so both are Ghost.
       - In a non-ghost function, Return is only allowed in NotGhost mode
         (not inside a Ghost block). *)
| "core_statement_type env ghost (CoreStmt_Return tm) =
    (if ghost = TE_FunctionGhost env
        \<and> core_term_type env ghost tm = Some (TE_ReturnType env)
     then Some env
     else None)"

  (* Swap: both sides must be writable lvalues of the same type. A non-ghost
     swap must be at a complete type (as for CoreStmt_Assign). *)
| "core_statement_type env ghost (CoreStmt_Swap swapGhost lhsTm rhsTm) =
    (if (ghost = Ghost \<longrightarrow> swapGhost = Ghost)
        \<and> is_writable_lvalue env lhsTm
        \<and> is_writable_lvalue env rhsTm
        \<and> ghost_lvalue_ok env swapGhost lhsTm
        \<and> ghost_lvalue_ok env swapGhost rhsTm
     then (case core_term_type env swapGhost lhsTm of
             Some lhsTy \<Rightarrow>
               if (swapGhost = NotGhost \<longrightarrow> is_complete_type lhsTy)
                  \<and> core_term_type env swapGhost rhsTm = Some lhsTy
               then Some env
               else None
           | None \<Rightarrow> None)
     else None)"

  (* Assert: condition must be bool. Proof body typechecks in Ghost context.
     When a condition is present ("assert condTm"), we install condTm as
     TE_ProofGoal during the proof. 
     When the condition is absent ("assert *"), the asserted goal is the current proof
     goal (which must exist!), so TE_ProofGoal is left unchanged. *)
| "core_statement_type env ghost (CoreStmt_Assert condOpt proofBody) =
    (let newGoal = (case condOpt of Some condTm \<Rightarrow> Some condTm
                               | None \<Rightarrow> TE_ProofGoal env);
         goalEnv = env \<lparr> TE_ProofGoal := newGoal,
                         TE_ProofTopLevel := True \<rparr>;
         condOk = (case condOpt of 
                     Some condTm \<Rightarrow> core_term_type env Ghost condTm = Some CoreTy_Bool
                   | None \<Rightarrow> TE_ProofGoal env \<noteq> None)
     in (if condOk
         then (case core_statement_list_type goalEnv Ghost proofBody of
                 Some _ \<Rightarrow> Some env
               | None \<Rightarrow> None)
         else None))"

  (* Assume: term must be bool. *)
| "core_statement_type env ghost (CoreStmt_Assume tm) =
    (if core_term_type env Ghost tm = Some CoreTy_Bool
     then Some env
     else None)"

  (* ShowHide: the name must refer to a function. (Shadowing of function names
     by local variable names is ignored for the purposes of this statement.) *)
| "core_statement_type env ghost (CoreStmt_ShowHide _ name) =
    (if name |\<in>| fmdom (TE_Functions env) then Some env else None)"

  (* Pattern match.
     The scrutinee must typecheck. Each pattern must be compatible with the
     scrutinee type. Each arm's statement list must typecheck under the same env
     (match arms run in their own scope, so bindings they introduce are discarded 
     on exit).
     Note: exhaustiveness is NOT checked; "no arms match" is a runtime error, not 
     a type error. In particular, an empty match is well-typed (and always fails at
     runtime). *)
| "core_statement_type env ghost (CoreStmt_Match matchGhost scrut arms) =
    (if ghost = Ghost \<longrightarrow> matchGhost = Ghost
     then (case core_term_type env matchGhost scrut of
             None \<Rightarrow> None
           | Some scrutTy \<Rightarrow>
               let pats = map fst arms;
                   bodies = map snd arms
               in if \<not> list_all (\<lambda>p. pattern_compatible env p scrutTy) pats then None
                  else if list_all (\<lambda>body. core_statement_list_type
                                              (env \<lparr> TE_ProofTopLevel := False \<rparr>)
                                              matchGhost body \<noteq> None) bodies
                       then Some env
                       else None)
     else None)"

  (* While loop.
     The condition must be Bool.
     Invariants must be Bool and are Ghost.
     The decreases term is optional; if present it must be a valid_decreases_type
     and is Ghost.
     The body typechecks as a statement list; it runs in a separate variable scope, so
     its result env is discarded. *)
| "core_statement_type env ghost (CoreStmt_While whileGhost condTm invars decrTm body) =
    (if ghost = Ghost \<longrightarrow> whileGhost = Ghost
     then (case core_term_type env whileGhost condTm of
             Some CoreTy_Bool \<Rightarrow>
               if list_all (\<lambda>inv. core_term_type env Ghost inv = Some CoreTy_Bool) invars
               then if has_valid_decreases_type env decrTm
                    then (case core_statement_list_type
                                 (env \<lparr> TE_ProofTopLevel := False \<rparr>) whileGhost body of
                            Some _ \<Rightarrow> Some env
                          | None \<Rightarrow> None)
                    else None
               else None
           | _ \<Rightarrow> None)
     else None)"

  (* Obtain: "obtain x of type T where P(x)". Introduces a ghost local x (like a
     CoreStmt_VarDecl with declGhost = Ghost). The type T must be well-kinded and the
      predicate P must typecheck to Bool in the env extended with x. The resulting 
      env keeps x in scope. *)
| "core_statement_type env ghost (CoreStmt_Obtain varName varTy condTm) =
    (if is_well_kinded env varTy
     then let env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                            TE_GhostLocals := finsert varName (TE_GhostLocals env),
                            TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>
          in if core_term_type env' Ghost condTm = Some CoreTy_Bool
             then Some env'
             else None
     else None)"

  (* Fix: "fix x : T". Only valid if there is a current proof goal of the form
     "forall x' : T. P(x')", and we are at the top level of the proof (not inside 
     nested match/while). Introduces a ghost variable "x : T" and changes the goal
     to "P(x)".
     Note: we don't actually bother renaming x' to x in the goal. This is sound because
     TE_ProofGoal is only consumed structurually. *)
| "core_statement_type env ghost (CoreStmt_Fix varName varTy) =
    (case TE_ProofGoal env of
       Some (CoreTm_Quantifier Quant_Forall _ qVarTy bodyTm) \<Rightarrow>
         (if ghost = Ghost \<and> qVarTy = varTy \<and> is_well_kinded env varTy \<and> TE_ProofTopLevel env
          then Some (env \<lparr> TE_LocalVars   := fmupd varName varTy (TE_LocalVars env),
                            TE_GhostLocals := finsert varName (TE_GhostLocals env),
                            TE_ConstLocals := finsert varName (TE_ConstLocals env),
                            TE_ProofGoal   := Some bodyTm \<rparr>)
          else None)
     | _ \<Rightarrow> None)"

  (* Use: "use e". Only valid if there is a current proof goal of the form
     "exists x : T. P(x)", and we are at the top level of the proof (not inside
     nested match/while, as for Fix). The term "e" must be of type T. Changes the
     goal to "P(e)".
     Note: As with Fix, we don't bother substituting in the goal - TE_ProofGoal remains
     "P(x)", which is sound for typechecking because TE_ProofGoal is only consumed
     structurally. *)
| "core_statement_type env ghost (CoreStmt_Use witnessTm) =
    (case TE_ProofGoal env of
       Some (CoreTm_Quantifier Quant_Exists _ qVarTy bodyTm) \<Rightarrow>
         (if ghost = Ghost \<and> core_term_type env ghost witnessTm = Some qVarTy
             \<and> TE_ProofTopLevel env
          then Some (env \<lparr> TE_ProofGoal := Some bodyTm \<rparr>)
          else None)
     | _ \<Rightarrow> None)"

  (* Block: execute a statement list in a fresh runtime scope, discarded on exit.
     Typechecks the body under TE_ProofTopLevel := False (the body is not at the
     proof top level) using the ambient ghost flag, and returns the entry env (the
     scope's bindings are discarded). No ghost guard: a block carries no flag. *)
| "core_statement_type env ghost (CoreStmt_Block body) =
    (case core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) ghost body of
       Some _ \<Rightarrow> Some env
     | None \<Rightarrow> None)"

  (* Statement lists *)
| "core_statement_list_type env _ [] = Some env"
| "core_statement_list_type env ghost (stmt # stmts) =
    (case core_statement_type env ghost stmt of
       Some env' \<Rightarrow> core_statement_list_type env' ghost stmts
     | None \<Rightarrow> None)"

by pat_completeness auto
termination
proof (relation "measure (\<lambda>x. case x of
    Inl (_, _, stmt) \<Rightarrow> size stmt
  | Inr (_, _, stmts) \<Rightarrow> size_list size stmts)"; (simp; fail)?)
  \<comment> \<open>CoreStmt_Match arm bodies are smaller than the whole match statement. \<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix matchGhost :: GhostOrNot
  fix scrut :: CoreTerm
  fix arms :: "(CorePattern \<times> CoreStatement list) list"
  fix x2 x xa z
  assume xa_eq: "xa = map snd arms" and z_in: "z \<in> set xa"
  from xa_eq z_in obtain a where "(a, z) \<in> set arms" by auto
  hence "size_prod (\<lambda>y. 0) (size_list size) (a, z)
           \<le> size_list (size_prod (\<lambda>y. 0) (size_list size)) arms"
    by (simp add: size_list_estimation')
  hence z_le: "size_list size z \<le> size_list (size_prod (\<lambda>y. 0) (size_list size)) arms"
    by simp
  show "(Inr (env \<lparr> TE_ProofTopLevel := False \<rparr>, matchGhost, z),
         Inl (env, ghost, CoreStmt_Match matchGhost scrut arms))
        \<in> measure (\<lambda>y. case y of
            Inl (_, _, stmt) \<Rightarrow> size stmt
          | Inr (_, _, stmts) \<Rightarrow> size_list size stmts)"
    using z_le by simp
qed

end

