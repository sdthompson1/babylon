theory CoreStmtTypecheck
  imports CoreTypecheck CoreTypeProps
begin

(* ========================================================================== *)
(* Statement typechecking                                                     *)
(*                                                                            *)
(* A statement transforms the type environment (e.g. VarDecl adds a new       *)
(* variable). The typechecking function returns the resulting environment,     *)
(* or None if ill-typed.                                                      *)
(*                                                                            *)
(* The GhostOrNot parameter represents the ghost context:                     *)
(*   - Ghost context: only ghost statements are allowed                       *)
(*   - NotGhost context: both ghost and non-ghost statements are allowed      *)
(* ========================================================================== *)

function core_statement_type :: "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> CoreStatement \<Rightarrow> CoreTyEnv option"
and core_statement_list_type :: "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> CoreStatement list \<Rightarrow> CoreTyEnv option"
where

  (* Variable declaration (Var) *)
  "core_statement_type env ghost (CoreStmt_VarDecl declGhost varName Var varTy initTm) =
    (if fmlookup (TE_TermVars env) varName \<noteq> None then None  \<comment> \<open>no shadowing\<close>
     else if (ghost = Ghost \<longrightarrow> declGhost = Ghost)
        \<and> is_well_kinded env varTy
        \<and> is_ground varTy
        \<and> (declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy)
        \<and> core_term_type env declGhost initTm = Some varTy
     then Some (env \<lparr> TE_TermVars := fmupd varName varTy (TE_TermVars env),
                      TE_GhostVars := (if declGhost = Ghost
                                       then finsert varName (TE_GhostVars env)
                                       else TE_GhostVars env),
                      TE_ConstNames := TE_ConstNames env \<rparr>)
     else None)"

  (* Variable declaration (Ref) - TODO *)
| "core_statement_type _ _ (CoreStmt_VarDecl _ _ Ref _ _) = undefined"

  (* Assignment *)
| "core_statement_type env ghost (CoreStmt_Assign assignGhost lhsTm rhsTm) =
    (if (ghost = Ghost \<longrightarrow> assignGhost = Ghost)
        \<and> is_writable_lvalue env lhsTm
     then (case core_term_type env assignGhost lhsTm of
             Some lhsTy \<Rightarrow>
               if core_term_type env assignGhost rhsTm = Some lhsTy
               then Some env
               else None
           | None \<Rightarrow> None)
     else None)"

  (* TODO: remaining statement forms *)
| "core_statement_type _ _ (CoreStmt_Fix _ _) = undefined"
| "core_statement_type _ _ (CoreStmt_Obtain _ _ _) = undefined"
| "core_statement_type _ _ (CoreStmt_Use _) = undefined"
| "core_statement_type _ _ (CoreStmt_Swap _ _ _) = undefined"
| "core_statement_type _ _ (CoreStmt_Return _) = undefined"
| "core_statement_type _ _ (CoreStmt_Assert _ _) = undefined"
| "core_statement_type _ _ (CoreStmt_Assume _) = undefined"
| "core_statement_type _ _ (CoreStmt_While _ _ _ _ _) = undefined"
| "core_statement_type _ _ (CoreStmt_Match _ _ _) = undefined"
| "core_statement_type _ _ (CoreStmt_ShowHide _ _) = undefined"

  (* Statement lists *)
| "core_statement_list_type env _ [] = Some env"
| "core_statement_list_type env ghost (stmt # stmts) =
    (case core_statement_type env ghost stmt of
       Some env' \<Rightarrow> core_statement_list_type env' ghost stmts
     | None \<Rightarrow> None)"

  by pat_completeness auto
  termination by (relation "measure (\<lambda>x. case x of
    Inl (_, _, stmt) \<Rightarrow> size stmt
  | Inr (_, _, stmts) \<Rightarrow> size_list size stmts)") auto


(* ========================================================================== *)
(* Well-formedness preservation                                               *)
(* ========================================================================== *)

(* core_statement_type preserves tyenv_well_formed *)
lemma core_statement_type_preserves_well_formed:
  assumes "core_statement_type env ghost stmt = Some env'"
    and "tyenv_well_formed env"
  shows "tyenv_well_formed env'"
using assms proof (cases stmt)
  case (CoreStmt_VarDecl declGhost varName varOrRef varTy initTm)
  show ?thesis proof (cases varOrRef)
    case Var
    from assms CoreStmt_VarDecl Var obtain
      wk: "is_well_kinded env varTy" and
      gr: "is_ground varTy" and
      rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy"
      by (auto split: if_splits)
    show ?thesis proof (cases declGhost)
      case NotGhost
      from rt NotGhost have "is_runtime_type env varTy" by simp
      from tyenv_well_formed_add_var[OF assms(2) wk gr this]
      have wf': "tyenv_well_formed (env \<lparr> TE_TermVars := fmupd varName varTy (TE_TermVars env) \<rparr>)" .
      from assms CoreStmt_VarDecl Var NotGhost have env'_eq:
        "env' = env \<lparr> TE_TermVars := fmupd varName varTy (TE_TermVars env),
                      TE_GhostVars := TE_GhostVars env,
                      TE_ConstNames := TE_ConstNames env \<rparr>"
        by (auto split: if_splits)
      with wf' show ?thesis by simp
    next
      case Ghost
      from tyenv_well_formed_add_ghost_var[OF assms(2) wk gr]
      have "tyenv_well_formed (env \<lparr> TE_TermVars := fmupd varName varTy (TE_TermVars env),
                                     TE_GhostVars := finsert varName (TE_GhostVars env) \<rparr>)" .
      with assms CoreStmt_VarDecl Var Ghost show ?thesis
        by (auto split: if_splits)
    qed
  next
    case Ref
    with assms CoreStmt_VarDecl show ?thesis sorry
  qed
next
  case (CoreStmt_Assign assignGhost lhsTm rhsTm)
  with assms show ?thesis by (auto split: if_splits option.splits)
next
  case (CoreStmt_Fix _ _) with assms show ?thesis sorry
next
  case (CoreStmt_Obtain _ _ _) with assms show ?thesis sorry
next
  case (CoreStmt_Use _) with assms show ?thesis sorry
next
  case (CoreStmt_Swap _ _ _) with assms show ?thesis sorry
next
  case (CoreStmt_Return _) with assms show ?thesis sorry
next
  case (CoreStmt_Assert _ _) with assms show ?thesis sorry
next
  case (CoreStmt_Assume _) with assms show ?thesis sorry
next
  case (CoreStmt_While _ _ _ _ _) with assms show ?thesis sorry
next
  case (CoreStmt_Match _ _ _) with assms show ?thesis sorry
next
  case (CoreStmt_ShowHide _ _) with assms show ?thesis sorry
qed

(* core_statement_list_type preserves tyenv_well_formed *)
lemma core_statement_list_type_preserves_well_formed:
  assumes "core_statement_list_type env ghost stmts = Some env'"
    and "tyenv_well_formed env"
  shows "tyenv_well_formed env'"
using assms proof (induction stmts arbitrary: env)
  case Nil
  then show ?case by simp
next
  case (Cons stmt stmts)
  from Cons.prems obtain env_mid where
    mid: "core_statement_type env ghost stmt = Some env_mid" and
    rest: "core_statement_list_type env_mid ghost stmts = Some env'"
    by (auto split: option.splits)
  from core_statement_type_preserves_well_formed[OF mid Cons.prems(2)]
  have "tyenv_well_formed env_mid" .
  from Cons.IH[OF rest this] show ?case .
qed

end

