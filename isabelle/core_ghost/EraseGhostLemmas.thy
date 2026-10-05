theory EraseGhostLemmas
  imports EraseGhost "../core/LinkModules"
begin

(* ========================================================================== *)
(* Ghost-erasure commutes with type substitution *)
(* ========================================================================== *)

(* For erase_ghost_statement: type-substituting and then ghost-erasing gives
   the same statements as erasing and then substituting.

   Erasure looks only at the markers and the statement forms, and substitution
   changes neither. The one place where erasure writes a term of its own is the
   decreases-term of an erased While loop, and that term contains no type. *)

lemma apply_subst_to_statement_list_append:
  "apply_subst_to_statement_list subst (stmts1 @ stmts2)
     = apply_subst_to_statement_list subst stmts1 @ apply_subst_to_statement_list subst stmts2"
  by (induction stmts1) simp_all

(* A statement list, given the result for each of its statements. *)
lemma erase_ghost_statement_list_apply_subst_aux:
  assumes "\<And>stmt. stmt \<in> set stmts \<Longrightarrow>
             erase_ghost_statement (apply_subst_to_statement subst stmt)
               = apply_subst_to_statement_list subst (erase_ghost_statement stmt)"
  shows "erase_ghost_statement_list (apply_subst_to_statement_list subst stmts)
           = apply_subst_to_statement_list subst (erase_ghost_statement_list stmts)"
  using assms
proof (induction stmts)
  case Nil
  show ?case by simp
next
  case (Cons stmt stmts)
  have hd: "erase_ghost_statement (apply_subst_to_statement subst stmt)
              = apply_subst_to_statement_list subst (erase_ghost_statement stmt)"
    by (rule Cons.prems) simp
  have tl: "erase_ghost_statement_list (apply_subst_to_statement_list subst stmts)
              = apply_subst_to_statement_list subst (erase_ghost_statement_list stmts)"
    by (rule Cons.IH) (rule Cons.prems, simp)
  show ?case
    by (simp add: hd tl apply_subst_to_statement_list_append)
qed

lemma erase_ghost_statement_apply_subst:
  "erase_ghost_statement (apply_subst_to_statement subst stmt)
     = apply_subst_to_statement_list subst (erase_ghost_statement stmt)"
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
  have b: "erase_ghost_statement_list (apply_subst_to_statement_list subst body)
             = apply_subst_to_statement_list subst (erase_ghost_statement_list body)"
    by (rule erase_ghost_statement_list_apply_subst_aux) (rule CoreStmt_While.IH)
  show ?case by (cases whileGhost) (simp_all add: b)
next
  case (CoreStmt_Match matchGhost scrut arms)
  have arm_eq:
    "erase_ghost_statement_list (apply_subst_to_statement_list subst body)
       = apply_subst_to_statement_list subst (erase_ghost_statement_list body)"
    if arm_in: "(pat, body) \<in> set arms" for pat body
  proof (rule erase_ghost_statement_list_apply_subst_aux)
    fix s assume s_in: "s \<in> set body"
    have sn: "body \<in> Basic_BNFs.snds (pat, body)" by simp
    show "erase_ghost_statement (apply_subst_to_statement subst s)
            = apply_subst_to_statement_list subst (erase_ghost_statement s)"
      by (rule CoreStmt_Match.IH[OF arm_in sn s_in])
  qed
  \<comment> \<open>Stated arm by arm: this is the form to which simp brings the equation
      between the two lists of arms.\<close>
  have arms_eq:
    "\<forall>x \<in> set arms.
       (case (case x of (pat, body) \<Rightarrow> (pat, apply_subst_to_statement_list subst body)) of
          (pat, body) \<Rightarrow> (pat, erase_ghost_statement_list body))
       = (case (case x of (pat, body) \<Rightarrow> (pat, erase_ghost_statement_list body)) of
            (pat, body) \<Rightarrow> (pat, apply_subst_to_statement_list subst body))"
    by (auto simp: arm_eq split: prod.splits)
  show ?case using arms_eq by (cases matchGhost) simp_all
next
  case (CoreStmt_ShowHide sh name)
  show ?case by simp
next
  case (CoreStmt_Block body)
  have b: "erase_ghost_statement_list (apply_subst_to_statement_list subst body)
             = apply_subst_to_statement_list subst (erase_ghost_statement_list body)"
    by (rule erase_ghost_statement_list_apply_subst_aux) (rule CoreStmt_Block.IH)
  show ?case by (simp add: b)
qed

theorem erase_ghost_statement_list_apply_subst:
  "erase_ghost_statement_list (apply_subst_to_statement_list subst stmts)
     = apply_subst_to_statement_list subst (erase_ghost_statement_list stmts)"
  by (rule erase_ghost_statement_list_apply_subst_aux)
     (rule erase_ghost_statement_apply_subst)

(* For erase_ghost_function: substituting in the erased body is erasing the substituted
   body. *)
lemma erase_ghost_function_subst:
  "(erase_ghost_function f)
     \<lparr> CF_Body := map_option (apply_subst_to_statement_list subst)
                             (CF_Body (erase_ghost_function f)) \<rparr>
   = erase_ghost_function
       (f \<lparr> CF_Body := map_option (apply_subst_to_statement_list subst) (CF_Body f) \<rparr>)"
  by (cases "CF_Body f")
     (simp_all add: erase_ghost_function_def erase_ghost_statement_list_apply_subst)


(* ========================================================================== *)
(* normalize_module commutes with erase_ghost_module_bodies *)
(* ========================================================================== *)

theorem normalize_module_erase_ghost:
  "normalize_module (erase_ghost_module_bodies m)
     = erase_ghost_module_bodies (normalize_module m)"
proof -
  let ?S = "\<lambda>f. f \<lparr> CF_Body := map_option (apply_subst_to_statement_list (CM_TypeSubst m))
                                         (CF_Body f) \<rparr>"
  have fm: "fmmap ?S (fmmap erase_ghost_function (CM_Functions m))
              = fmmap erase_ghost_function (fmmap ?S (CM_Functions m))"
    by (simp add: fmap.map_comp comp_def erase_ghost_function_subst
             del: erase_ghost_function_simps)
  show ?thesis
    unfolding normalize_module_def erase_ghost_module_bodies_def
    using fm by simp
qed


(* ========================================================================== *)
(* Finite map helpers *)
(* ========================================================================== *)

lemma fmdom_fmmap_eq:
  "fmdom (fmmap g m) = fmdom m"
  by (rule fset_eqI) (auto simp: fmlookup_dom_iff)

lemma fmmap_fmempty_eq:
  "fmmap g fmempty = fmempty"
  by (rule fmap_ext) simp

lemma fmmap_fmadd_distrib:
  "fmmap g (a ++\<^sub>f b) = fmmap g a ++\<^sub>f fmmap g b"
  by (rule fmap_ext) (auto simp: fmdom_fmmap_eq)

lemma fmdisjoint_list_map_fmmap:
  "fmdisjoint_list (map (\<lambda>x. fmmap g (h x)) ms) = fmdisjoint_list (map h ms)"
  by (induction ms) (simp_all add: fmdisjoint_list_Cons fmdisjoint_def fmdom_fmmap_eq)

lemma fmlist_union_map_fmmap:
  "fmlist_union (map (\<lambda>x. fmmap g (h x)) ms) = fmmap g (fmlist_union (map h ms))"
  by (induction ms)
     (simp_all add: fmlist_union_Cons fmmap_fmadd_distrib fmmap_fmempty_eq)


(* ========================================================================== *)
(* erase_ghost_module_bodies commutes with link_modules *)
(* ========================================================================== *)

(* The checks that link_modules makes do not look at the function bodies. *)

lemma module_bound_tyvars_erase_ghost [simp]:
  "module_bound_tyvars (erase_ghost_module_bodies x) = module_bound_tyvars x"
  by (simp add: module_bound_tyvars_def)

lemma link_fields_disjoint_erase_ghost:
  "link_fields_disjoint (map erase_ghost_module_bodies ms) = link_fields_disjoint ms"
  unfolding link_fields_disjoint_def
  by (simp add: comp_def fmdisjoint_list_map_fmmap)

lemma link_capture_ok_erase_ghost:
  "link_capture_ok (map erase_ghost_module_bodies ms) = link_capture_ok ms"
  unfolding link_capture_ok_def
  by (simp add: comp_def)

lemma map_CM_TypeSubst_erase_ghost:
  "map CM_TypeSubst (map erase_ghost_module_bodies ms) = map CM_TypeSubst ms"
  by (simp add: comp_def)

(* The linked module of the erased inputs is the erased linked module. *)
lemma link_result_erase_ghost:
  "link_result (map erase_ghost_module_bodies ms) \<sigma>
     = erase_ghost_module_bodies (link_result ms \<sigma>)"
  unfolding link_result_def
  by (simp add: erase_ghost_module_bodies_def comp_def fmlist_union_map_fmmap)

lemma link_runtime_ok_erase_ghost:
  "link_runtime_ok (map erase_ghost_module_bodies ms) \<sigma> = link_runtime_ok ms \<sigma>"
  unfolding link_runtime_ok_def link_result_erase_ghost
  by (simp add: comp_def)

(* Linking the erased modules gives the erased link. *)
theorem link_modules_erase_ghost:
  assumes "link_modules ms = Inr m"
  shows "link_modules (map erase_ghost_module_bodies ms) = Inr (erase_ghost_module_bodies m)"
proof -
  from assms obtain \<sigma> where
      d: "link_fields_disjoint ms" and
      c: "link_capture_ok ms" and
      mg: "merge_all_substs (map CM_TypeSubst ms) = Inr \<sigma>" and
      rt: "link_runtime_ok ms \<sigma>" and
      m_eq: "m = link_result ms \<sigma>"
    unfolding link_modules_Inr_iff by blast
  have "link_fields_disjoint (map erase_ghost_module_bodies ms)"
    unfolding link_fields_disjoint_erase_ghost by (rule d)
  moreover have "link_capture_ok (map erase_ghost_module_bodies ms)"
    unfolding link_capture_ok_erase_ghost by (rule c)
  moreover have "merge_all_substs (map CM_TypeSubst (map erase_ghost_module_bodies ms)) = Inr \<sigma>"
    unfolding map_CM_TypeSubst_erase_ghost by (rule mg)
  moreover have "link_runtime_ok (map erase_ghost_module_bodies ms) \<sigma>"
    unfolding link_runtime_ok_erase_ghost by (rule rt)
  moreover have "erase_ghost_module_bodies m
                   = link_result (map erase_ghost_module_bodies ms) \<sigma>"
    unfolding link_result_erase_ghost m_eq by (rule refl)
  ultimately show ?thesis
    unfolding link_modules_Inr_iff by blast
qed


end
