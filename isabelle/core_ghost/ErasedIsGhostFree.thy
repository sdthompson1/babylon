theory ErasedIsGhostFree
  imports EraseGhost GhostFree
begin

(* ========================================================================== *)
(* This file proves that the result of ghost-erasure does indeed satisfy  *)
(* the relevant "ghost-free" definitions.  *)
(* ========================================================================== *)

(* Helper lemma *)
lemma erase_ghost_statement_list_ghost_free_aux:
  assumes "\<And>stmt. stmt \<in> set stmts
             \<Longrightarrow> core_statement_list_ghost_free (erase_ghost_statement stmt)"
  shows "core_statement_list_ghost_free (erase_ghost_statement_list stmts)"
  using assms
  by (induction stmts) (simp_all add: core_statement_list_ghost_free_append)

(* erase_ghost_statement produces a ghost-free statement list *)
lemma erase_ghost_statement_ghost_free:
  "core_statement_list_ghost_free (erase_ghost_statement stmt)"
proof (induction stmt)
  case (CoreStmt_VarDecl declGhost varName vr varTy initTm)
  show ?case by (cases declGhost) simp_all
next
  case (CoreStmt_VarDeclCall declGhost varName varTy castOpt fnName tyArgs argTms)
  show ?case by (cases declGhost) simp_all
next
  case (CoreStmt_Fix varName varTy)
  show ?case by simp
next
  case (CoreStmt_Obtain varName varTy condTm)
  show ?case by simp
next
  case (CoreStmt_Use witnessTm)
  show ?case by simp
next
  case (CoreStmt_Assign assignGhost lhsTm rhsTm)
  show ?case by (cases assignGhost) simp_all
next
  case (CoreStmt_AssignCall assignGhost lhsTm castOpt fnName tyArgs argTms)
  show ?case by (cases assignGhost) simp_all
next
  case (CoreStmt_Swap swapGhost lhsTm rhsTm)
  show ?case by (cases swapGhost) simp_all
next
  case (CoreStmt_Return tm)
  show ?case by simp
next
  case (CoreStmt_Assert condOpt proofBody)
  show ?case by simp
next
  case (CoreStmt_Assume tm)
  show ?case by simp
next
  case (CoreStmt_While whileGhost condTm invars decrTm body)
  have b: "core_statement_list_ghost_free (erase_ghost_statement_list body)"
    by (rule erase_ghost_statement_list_ghost_free_aux) (rule CoreStmt_While.IH)
  show ?case by (cases whileGhost) (simp_all add: b)
next
  case (CoreStmt_Match matchGhost scrut arms)
  have arm: "core_statement_list_ghost_free (erase_ghost_statement_list body)"
    if arm_in: "(pat, body) \<in> set arms" for pat body
  proof (rule erase_ghost_statement_list_ghost_free_aux)
    fix s assume s_in: "s \<in> set body"
    have sn: "body \<in> Basic_BNFs.snds (pat, body)" by simp
    show "core_statement_list_ghost_free (erase_ghost_statement s)"
      by (rule CoreStmt_Match.IH[OF arm_in sn s_in])
  qed
  show ?case using arm by (cases matchGhost) (auto simp: list_all_iff)
next
  case (CoreStmt_ShowHide sh name)
  show ?case by simp
next
  case (CoreStmt_Block body)
  have b: "core_statement_list_ghost_free (erase_ghost_statement_list body)"
    by (rule erase_ghost_statement_list_ghost_free_aux) (rule CoreStmt_Block.IH)
  show ?case by (simp add: b)
qed

(* erase_ghost_statement_list produces a ghost-free statement list *)
theorem erase_ghost_statement_list_ghost_free:
  "core_statement_list_ghost_free (erase_ghost_statement_list stmts)"
  by (rule erase_ghost_statement_list_ghost_free_aux)
     (rule erase_ghost_statement_ghost_free)

(* erase_ghost_module produces a ghost-free module *)
theorem erase_ghost_module_ghost_free:
  "core_module_ghost_free (erase_ghost_module m)"
proof -
  let ?envE = "erase_ghost_tyenv (CM_TyEnv m)"
  have fns: "FI_Ghost info = NotGhost"
    if "fmlookup (TE_Functions ?envE) name = Some info" for name info
    using that unfolding erase_ghost_tyenv_fun_lookup by simp
  have gd: "TE_GhostDatatypes ?envE = {||}" by simp
  have tv: "TE_TypeVars ?envE |\<subseteq>| TE_RuntimeTypeVars ?envE" by auto
  have bodies: "core_statement_list_ghost_free body"
    if lk: "fmlookup (CM_Functions (erase_ghost_module m)) name = Some f"
      and b: "CF_Body f = Some body" for name f body
  proof -
    from lk obtain f0 where f: "f = erase_ghost_function f0"
      unfolding erase_ghost_module_fun_lookup by blast
    from b f obtain body0 where "body = erase_ghost_statement_list body0"
      by auto
    thus ?thesis by (simp add: erase_ghost_statement_list_ghost_free)
  qed
  have env_eq: "CM_TyEnv (erase_ghost_module m) = ?envE" by simp
  show ?thesis
    unfolding core_module_ghost_free_def env_eq
    using fns gd tv bodies by blast
qed

end
