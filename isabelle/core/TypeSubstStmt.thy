theory TypeSubstStmt
  imports TypeSubstTerm
begin

(* ========================================================================== *)
(* Type substitution on statements *)
(*                                                                            *)
(* The statement-level analogue of apply_subst_to_term (TypeSubstTerm.thy).   *)
(* Pushes a type substitution through every CoreType and CoreTerm embedded in *)
(* a statement, recursing structurally into nested statement lists (proof     *)
(* bodies, loop/match/block bodies). CorePatterns carry no CoreType, so they  *)
(* are left untouched.                                                        *)
(* ========================================================================== *)

fun apply_subst_to_statement :: "TypeSubst \<Rightarrow> CoreStatement \<Rightarrow> CoreStatement"
and apply_subst_to_statement_list :: "TypeSubst \<Rightarrow> CoreStatement list \<Rightarrow> CoreStatement list" where
  "apply_subst_to_statement subst (CoreStmt_VarDecl ghost varName vr ty initTm) =
    CoreStmt_VarDecl ghost varName vr (apply_subst subst ty) (apply_subst_to_term subst initTm)"
| "apply_subst_to_statement subst (CoreStmt_VarDeclCall ghost varName ty castOpt fnName tyArgs argTms) =
    CoreStmt_VarDeclCall ghost varName (apply_subst subst ty) (map_option (apply_subst subst) castOpt)
                         fnName (map (apply_subst subst) tyArgs) (map (apply_subst_to_term subst) argTms)"
| "apply_subst_to_statement subst (CoreStmt_Fix varName ty) =
    CoreStmt_Fix varName (apply_subst subst ty)"
| "apply_subst_to_statement subst (CoreStmt_Obtain varName ty condTm) =
    CoreStmt_Obtain varName (apply_subst subst ty) (apply_subst_to_term subst condTm)"
| "apply_subst_to_statement subst (CoreStmt_Use witnessTm) =
    CoreStmt_Use (apply_subst_to_term subst witnessTm)"
| "apply_subst_to_statement subst (CoreStmt_Assign ghost lhsTm rhsTm) =
    CoreStmt_Assign ghost (apply_subst_to_term subst lhsTm) (apply_subst_to_term subst rhsTm)"
| "apply_subst_to_statement subst (CoreStmt_AssignCall ghost lhsTm castOpt fnName tyArgs argTms) =
    CoreStmt_AssignCall ghost (apply_subst_to_term subst lhsTm) (map_option (apply_subst subst) castOpt)
                        fnName (map (apply_subst subst) tyArgs) (map (apply_subst_to_term subst) argTms)"
| "apply_subst_to_statement subst (CoreStmt_Swap ghost lhsTm rhsTm) =
    CoreStmt_Swap ghost (apply_subst_to_term subst lhsTm) (apply_subst_to_term subst rhsTm)"
| "apply_subst_to_statement subst (CoreStmt_Return tm) =
    CoreStmt_Return (apply_subst_to_term subst tm)"
| "apply_subst_to_statement subst (CoreStmt_Assert condOpt proofBody) =
    CoreStmt_Assert (map_option (apply_subst_to_term subst) condOpt)
                    (apply_subst_to_statement_list subst proofBody)"
| "apply_subst_to_statement subst (CoreStmt_Assume tm) =
    CoreStmt_Assume (apply_subst_to_term subst tm)"
| "apply_subst_to_statement subst (CoreStmt_While ghost condTm invars decrTm body) =
    CoreStmt_While ghost (apply_subst_to_term subst condTm)
                   (map (apply_subst_to_term subst) invars)
                   (apply_subst_to_term subst decrTm)
                   (apply_subst_to_statement_list subst body)"
| "apply_subst_to_statement subst (CoreStmt_Match ghost scrut arms) =
    CoreStmt_Match ghost (apply_subst_to_term subst scrut)
                   (map (\<lambda>(pat, body). (pat, apply_subst_to_statement_list subst body)) arms)"
| "apply_subst_to_statement subst (CoreStmt_ShowHide sh name) =
    CoreStmt_ShowHide sh name"
| "apply_subst_to_statement subst (CoreStmt_Block body) =
    CoreStmt_Block (apply_subst_to_statement_list subst body)"

| "apply_subst_to_statement_list subst [] = []"
| "apply_subst_to_statement_list subst (stmt # stmts) =
    apply_subst_to_statement subst stmt # apply_subst_to_statement_list subst stmts"


(* Empty substitution leaves a statement unchanged. *)
lemma apply_subst_to_statement_empty [simp]:
  "apply_subst_to_statement fmempty stmt = stmt"
  and apply_subst_to_statement_list_empty [simp]:
  "apply_subst_to_statement_list fmempty stmts = stmts"
proof (induction "fmempty :: TypeSubst" stmt and "fmempty :: TypeSubst" stmts
       rule: apply_subst_to_statement_apply_subst_to_statement_list.induct)
  case (13 ghost scrut arms)
  have "map (\<lambda>(pat, body). (pat, apply_subst_to_statement_list fmempty body)) arms = arms"
    by (rule map_idI) (use 13 in \<open>force split: prod.splits\<close>)
  then show ?case by simp
qed (simp_all add: map_apply_subst_to_term_empty map_option_cong option.map_ident)


(* Composing substitutions: applying s2 after s1 equals applying (compose_subst s2 s1). *)
lemma apply_subst_to_statement_compose:
  "apply_subst_to_statement s2 (apply_subst_to_statement s1 stmt) =
   apply_subst_to_statement (compose_subst s2 s1) stmt"
  and apply_subst_to_statement_list_compose:
  "apply_subst_to_statement_list s2 (apply_subst_to_statement_list s1 stmts) =
   apply_subst_to_statement_list (compose_subst s2 s1) stmts"
proof (induction s1 stmt and s1 stmts
       rule: apply_subst_to_statement_apply_subst_to_statement_list.induct)
  case (13 s1 ghost scrut arms)
  have "map (\<lambda>(pat, body). (pat, apply_subst_to_statement_list s2 body))
            (map (\<lambda>(pat, body). (pat, apply_subst_to_statement_list s1 body)) arms) =
        map (\<lambda>(pat, body). (pat, apply_subst_to_statement_list (compose_subst s2 s1) body)) arms"
    unfolding map_map o_def
    by (rule map_cong[OF refl]) (use 13 in \<open>auto split: prod.splits\<close>)
  thus ?case
    by (simp add: apply_subst_to_term_compose compose_subst_correct
                  map_option.compositionality o_def)
qed (simp_all add: apply_subst_to_term_compose compose_subst_correct
                   map_option.compositionality o_def cong: map_option_cong)

end
