theory EraseGhostLemmas
  imports EraseGhost "../core/LinkModules"
begin

(* ========================================================================== *)
(* Ghost-erasure commutes with type substitution *)
(* ========================================================================== *)

(* Type-substituting and then ghost-erasing gives the same code as erasing and
   then substituting, for any table of function signatures.

   Erasure looks only at the markers, the statement forms, and the names of the
   functions called, and substitution changes none of these. The one place
   where erasure writes a term of its own is the decreases-term of an erased
   While loop, and that term contains no type. *)

(* A list of terms, given the result for each of them. *)
lemma map_erase_ghost_term_apply_subst_aux:
  assumes "\<And>tm. tm \<in> set tms \<Longrightarrow>
             erase_ghost_term funs (apply_subst_to_term subst tm)
               = apply_subst_to_term subst (erase_ghost_term funs tm)"
  shows "map (erase_ghost_term funs) (map (apply_subst_to_term subst) tms)
           = map (apply_subst_to_term subst) (map (erase_ghost_term funs) tms)"
  using assms
proof (induction tms)
  case Nil
  show ?case by simp
next
  case (Cons tm tms)
  have hd: "erase_ghost_term funs (apply_subst_to_term subst tm)
              = apply_subst_to_term subst (erase_ghost_term funs tm)"
    by (rule Cons.prems) simp
  have tl: "map (erase_ghost_term funs) (map (apply_subst_to_term subst) tms)
              = map (apply_subst_to_term subst) (map (erase_ghost_term funs) tms)"
    by (rule Cons.IH) (rule Cons.prems, simp)
  show ?case using hd tl by simp
qed

lemma erase_ghost_term_apply_subst:
  "erase_ghost_term funs (apply_subst_to_term subst tm)
     = apply_subst_to_term subst (erase_ghost_term funs tm)"
proof (induction tm)
  case (CoreTm_LitArray elemTy tms)
  have m: "map (erase_ghost_term funs) (map (apply_subst_to_term subst) tms)
             = map (apply_subst_to_term subst) (map (erase_ghost_term funs) tms)"
    by (rule map_erase_ghost_term_apply_subst_aux) (rule CoreTm_LitArray.IH)
  from m show ?case by simp
next
  case (CoreTm_FunctionCall fnName tyArgs args)
  have m: "map (erase_ghost_term funs) (map (apply_subst_to_term subst) args)
             = map (apply_subst_to_term subst) (map (erase_ghost_term funs) args)"
    by (rule map_erase_ghost_term_apply_subst_aux) (rule CoreTm_FunctionCall.IH)
  \<comment> \<open>Which arguments are dropped depends only on the name of the function. \<close>
  have "erase_ghost_args funs fnName
          (map (erase_ghost_term funs) (map (apply_subst_to_term subst) args))
        = map (apply_subst_to_term subst)
            (erase_ghost_args funs fnName (map (erase_ghost_term funs) args))"
    unfolding m by (rule erase_ghost_args_map)
  then show ?case by simp
next
  case (CoreTm_Record flds)
  have fld_eq:
    "erase_ghost_term funs (apply_subst_to_term subst t)
       = apply_subst_to_term subst (erase_ghost_term funs t)"
    if fld_in: "(name, t) \<in> set flds" for name t
  proof -
    have sn: "t \<in> Basic_BNFs.snds (name, t)" by simp
    show ?thesis by (rule CoreTm_Record.IH[OF fld_in sn])
  qed
  \<comment> \<open>Stated field by field: this is the form to which simp brings the
      equation between the two lists of fields.\<close>
  have flds_eq:
    "\<forall>x \<in> set flds.
       (case (case x of (name, tm) \<Rightarrow> (name, apply_subst_to_term subst tm)) of
          (name, tm) \<Rightarrow> (name, erase_ghost_term funs tm))
       = (case (case x of (name, tm) \<Rightarrow> (name, erase_ghost_term funs tm)) of
            (name, tm) \<Rightarrow> (name, apply_subst_to_term subst tm))"
    by (auto simp: fld_eq split: prod.splits)
  show ?case using flds_eq by simp
next
  case (CoreTm_ArrayProj arr idxs)
  have m: "map (erase_ghost_term funs) (map (apply_subst_to_term subst) idxs)
             = map (apply_subst_to_term subst) (map (erase_ghost_term funs) idxs)"
    by (rule map_erase_ghost_term_apply_subst_aux) (rule CoreTm_ArrayProj.IH(2))
  from m CoreTm_ArrayProj.IH(1) show ?case by simp
next
  case (CoreTm_Match scrut arms)
  have arm_eq:
    "erase_ghost_term funs (apply_subst_to_term subst t)
       = apply_subst_to_term subst (erase_ghost_term funs t)"
    if arm_in: "(pat, t) \<in> set arms" for pat t
  proof -
    have sn: "t \<in> Basic_BNFs.snds (pat, t)" by simp
    show ?thesis by (rule CoreTm_Match.IH(2)[OF arm_in sn])
  qed
  have arms_eq:
    "\<forall>x \<in> set arms.
       (case (case x of (pat, tm) \<Rightarrow> (pat, apply_subst_to_term subst tm)) of
          (pat, tm) \<Rightarrow> (pat, erase_ghost_term funs tm))
       = (case (case x of (pat, tm) \<Rightarrow> (pat, erase_ghost_term funs tm)) of
            (pat, tm) \<Rightarrow> (pat, apply_subst_to_term subst tm))"
    by (auto simp: arm_eq split: prod.splits)
  show ?case using arms_eq CoreTm_Match.IH(1) by simp
qed simp_all

(* The arguments of a call. *)
lemma erase_ghost_args_terms_apply_subst:
  "erase_ghost_args funs fnName
     (map (erase_ghost_term funs) (map (apply_subst_to_term subst) args))
   = map (apply_subst_to_term subst)
       (erase_ghost_args funs fnName (map (erase_ghost_term funs) args))"
proof -
  have m: "map (erase_ghost_term funs) (map (apply_subst_to_term subst) args)
             = map (apply_subst_to_term subst) (map (erase_ghost_term funs) args)"
    by (rule map_erase_ghost_term_apply_subst_aux) (rule erase_ghost_term_apply_subst)
  show ?thesis unfolding m by (rule erase_ghost_args_map)
qed

lemma apply_subst_to_statement_list_append:
  "apply_subst_to_statement_list subst (stmts1 @ stmts2)
     = apply_subst_to_statement_list subst stmts1 @ apply_subst_to_statement_list subst stmts2"
  by (induction stmts1) simp_all

(* A statement list, given the result for each of its statements. *)
lemma erase_ghost_statement_list_apply_subst_aux:
  assumes "\<And>stmt. stmt \<in> set stmts \<Longrightarrow>
             erase_ghost_statement funs (apply_subst_to_statement subst stmt)
               = apply_subst_to_statement_list subst (erase_ghost_statement funs stmt)"
  shows "erase_ghost_statement_list funs (apply_subst_to_statement_list subst stmts)
           = apply_subst_to_statement_list subst (erase_ghost_statement_list funs stmts)"
  using assms
proof (induction stmts)
  case Nil
  show ?case by simp
next
  case (Cons stmt stmts)
  have hd: "erase_ghost_statement funs (apply_subst_to_statement subst stmt)
              = apply_subst_to_statement_list subst (erase_ghost_statement funs stmt)"
    by (rule Cons.prems) simp
  have tl: "erase_ghost_statement_list funs (apply_subst_to_statement_list subst stmts)
              = apply_subst_to_statement_list subst (erase_ghost_statement_list funs stmts)"
    by (rule Cons.IH) (rule Cons.prems, simp)
  show ?case
    by (simp add: hd tl apply_subst_to_statement_list_append)
qed

lemma erase_ghost_statement_apply_subst:
  "erase_ghost_statement funs (apply_subst_to_statement subst stmt)
     = apply_subst_to_statement_list subst (erase_ghost_statement funs stmt)"
proof (induction stmt)
  case (CoreStmt_VarDecl declGhost varName vr varTy initTm)
  show ?case by (cases declGhost) (simp_all add: erase_ghost_term_apply_subst)
next
  case (CoreStmt_VarDeclCall declGhost varName varTy castOpt fnName tyArgs argTms)
  show ?case
    using erase_ghost_args_terms_apply_subst[of funs fnName subst argTms]
    by (cases declGhost) simp_all
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
  show ?case by (cases assignGhost) (simp_all add: erase_ghost_term_apply_subst)
next
  case (CoreStmt_AssignCall assignGhost lhsTm castOpt fnName tyArgs argTms)
  show ?case
    using erase_ghost_args_terms_apply_subst[of funs fnName subst argTms]
    by (cases assignGhost) (simp_all add: erase_ghost_term_apply_subst)
next
  case (CoreStmt_Swap swapGhost lhsTm rhsTm)
  show ?case by (cases swapGhost) (simp_all add: erase_ghost_term_apply_subst)
next
  case (CoreStmt_Return tm)
  show ?case by (simp add: erase_ghost_term_apply_subst)
next
  case (CoreStmt_Assert condOpt proofBody)
  show ?case by simp
next
  case (CoreStmt_Assume tm)
  show ?case by simp
next
  case (CoreStmt_While whileGhost condTm invars decrTm body)
  have b: "erase_ghost_statement_list funs (apply_subst_to_statement_list subst body)
             = apply_subst_to_statement_list subst (erase_ghost_statement_list funs body)"
    by (rule erase_ghost_statement_list_apply_subst_aux) (rule CoreStmt_While.IH)
  show ?case by (cases whileGhost) (simp_all add: b erase_ghost_term_apply_subst)
next
  case (CoreStmt_Match matchGhost scrut arms)
  have arm_eq:
    "erase_ghost_statement_list funs (apply_subst_to_statement_list subst body)
       = apply_subst_to_statement_list subst (erase_ghost_statement_list funs body)"
    if arm_in: "(pat, body) \<in> set arms" for pat body
  proof (rule erase_ghost_statement_list_apply_subst_aux)
    fix s assume s_in: "s \<in> set body"
    have sn: "body \<in> Basic_BNFs.snds (pat, body)" by simp
    show "erase_ghost_statement funs (apply_subst_to_statement subst s)
            = apply_subst_to_statement_list subst (erase_ghost_statement funs s)"
      by (rule CoreStmt_Match.IH[OF arm_in sn s_in])
  qed
  \<comment> \<open>Stated arm by arm: this is the form to which simp brings the equation
      between the two lists of arms.\<close>
  have arms_eq:
    "\<forall>x \<in> set arms.
       (case (case x of (pat, body) \<Rightarrow> (pat, apply_subst_to_statement_list subst body)) of
          (pat, body) \<Rightarrow> (pat, erase_ghost_statement_list funs body))
       = (case (case x of (pat, body) \<Rightarrow> (pat, erase_ghost_statement_list funs body)) of
            (pat, body) \<Rightarrow> (pat, apply_subst_to_statement_list subst body))"
    by (auto simp: arm_eq split: prod.splits)
  show ?case using arms_eq
    by (cases matchGhost) (simp_all add: erase_ghost_term_apply_subst)
next
  case (CoreStmt_ShowHide sh name)
  show ?case by simp
next
  case (CoreStmt_Block body)
  have b: "erase_ghost_statement_list funs (apply_subst_to_statement_list subst body)
             = apply_subst_to_statement_list subst (erase_ghost_statement_list funs body)"
    by (rule erase_ghost_statement_list_apply_subst_aux) (rule CoreStmt_Block.IH)
  show ?case by (simp add: b)
qed

theorem erase_ghost_statement_list_apply_subst:
  "erase_ghost_statement_list funs (apply_subst_to_statement_list subst stmts)
     = apply_subst_to_statement_list subst (erase_ghost_statement_list funs stmts)"
  by (rule erase_ghost_statement_list_apply_subst_aux)
     (rule erase_ghost_statement_apply_subst)

(* For erase_ghost_function_body: substituting in the erased body is erasing the
   substituted body. *)
lemma erase_ghost_function_body_subst:
  "(erase_ghost_function_body funs f)
     \<lparr> CF_Body := map_option (apply_subst_to_statement_list subst)
                             (CF_Body (erase_ghost_function_body funs f)) \<rparr>
   = erase_ghost_function_body funs
       (f \<lparr> CF_Body := map_option (apply_subst_to_statement_list subst) (CF_Body f) \<rparr>)"
  by (cases "CF_Body f")
     (simp_all add: erase_ghost_function_body_def erase_ghost_statement_list_apply_subst)


(* ========================================================================== *)
(* normalize_module commutes with erase_ghost_module_bodies *)
(* ========================================================================== *)

(* The table of function signatures is a parameter, and is the same on both
   sides. *)
theorem normalize_module_erase_ghost:
  "normalize_module (erase_ghost_module_bodies funs m)
     = erase_ghost_module_bodies funs (normalize_module m)"
proof -
  let ?S = "\<lambda>f. f \<lparr> CF_Body := map_option (apply_subst_to_statement_list (CM_TypeSubst m))
                                         (CF_Body f) \<rparr>"
  have fm: "fmmap ?S (fmmap (erase_ghost_function_body funs) (CM_Functions m))
              = fmmap (erase_ghost_function_body funs) (fmmap ?S (CM_Functions m))"
    by (simp add: fmap.map_comp comp_def erase_ghost_function_body_subst
             del: erase_ghost_function_body_simps)
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

(* Every module is erased with the same table of function signatures. The
   checks that link_modules makes do not look at the function bodies. *)

lemma module_bound_tyvars_erase_ghost [simp]:
  "module_bound_tyvars (erase_ghost_module_bodies funs x) = module_bound_tyvars x"
  by (simp add: module_bound_tyvars_def)

lemma link_fields_disjoint_erase_ghost:
  "link_fields_disjoint (map (erase_ghost_module_bodies funs) ms) = link_fields_disjoint ms"
  unfolding link_fields_disjoint_def
  by (simp add: comp_def fmdisjoint_list_map_fmmap)

lemma link_capture_ok_erase_ghost:
  "link_capture_ok (map (erase_ghost_module_bodies funs) ms) = link_capture_ok ms"
  unfolding link_capture_ok_def
  by (simp add: comp_def)

lemma map_CM_TypeSubst_erase_ghost:
  "map CM_TypeSubst (map (erase_ghost_module_bodies funs) ms) = map CM_TypeSubst ms"
  by (simp add: comp_def)

(* The linked module of the erased inputs is the erased linked module. *)
lemma link_result_erase_ghost:
  "link_result (map (erase_ghost_module_bodies funs) ms) \<sigma>
     = erase_ghost_module_bodies funs (link_result ms \<sigma>)"
  unfolding link_result_def
  by (simp add: erase_ghost_module_bodies_def comp_def fmlist_union_map_fmmap)

lemma link_runtime_ok_erase_ghost:
  "link_runtime_ok (map (erase_ghost_module_bodies funs) ms) \<sigma> = link_runtime_ok ms \<sigma>"
  unfolding link_runtime_ok_def link_result_erase_ghost
  by (simp add: comp_def)

(* Linking the erased modules gives the erased link. *)
theorem link_modules_erase_ghost:
  assumes "link_modules ms = Inr m"
  shows "link_modules (map (erase_ghost_module_bodies funs) ms)
           = Inr (erase_ghost_module_bodies funs m)"
proof -
  from assms obtain \<sigma> where
      d: "link_fields_disjoint ms" and
      c: "link_capture_ok ms" and
      mg: "merge_all_substs (map CM_TypeSubst ms) = Inr \<sigma>" and
      rt: "link_runtime_ok ms \<sigma>" and
      m_eq: "m = link_result ms \<sigma>"
    unfolding link_modules_Inr_iff by blast
  have "link_fields_disjoint (map (erase_ghost_module_bodies funs) ms)"
    unfolding link_fields_disjoint_erase_ghost by (rule d)
  moreover have "link_capture_ok (map (erase_ghost_module_bodies funs) ms)"
    unfolding link_capture_ok_erase_ghost by (rule c)
  moreover have "merge_all_substs (map CM_TypeSubst (map (erase_ghost_module_bodies funs) ms)) = Inr \<sigma>"
    unfolding map_CM_TypeSubst_erase_ghost by (rule mg)
  moreover have "link_runtime_ok (map (erase_ghost_module_bodies funs) ms) \<sigma>"
    unfolding link_runtime_ok_erase_ghost by (rule rt)
  moreover have "erase_ghost_module_bodies funs m
                   = link_result (map (erase_ghost_module_bodies funs) ms) \<sigma>"
    unfolding link_result_erase_ghost m_eq by (rule refl)
  ultimately show ?thesis
    unfolding link_modules_Inr_iff by blast
qed


end
