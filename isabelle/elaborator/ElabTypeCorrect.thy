theory ElabTypeCorrect
  imports ElabType
begin

(* Correctness lemmas for elab_type: if it succeeds, the result satisfies
   various properties (groundness, well-kindedness, runtime type). *)


(* Helper: if all elements of a list satisfy P, then (P \<circ> snd) holds for all elements of zip *)
lemma list_all_snd_zip:
  "\<forall>x\<in>set ys. P x \<Longrightarrow> list_all (P \<circ> snd) (zip xs ys)"
  by (induction xs ys rule: list_induct2') auto


(* If elab_type succeeds, the result is ground (no metavariables).
   This is proven by induction on fuel. The key insight is that elab_type
   only returns Inr for types that don't contain metavariables - it explicitly
   rejects BabTy_Meta with TyErr_MetavariableInInput. *)
lemma elab_type_is_ground:
  "elab_type fuel typedefs env ghost ty = Inr ty' \<Longrightarrow> is_ground ty'"
  "elab_type_list fuel typedefs env ghost tys = Inr tys' \<Longrightarrow> list_all is_ground tys'"
proof (induction fuel arbitrary: ty ty' tys tys')
  case 0
  { case 1 then show ?case by simp }
  { case 2 then show ?case by simp }
next
  case (Suc fuel)
  note IH1 = Suc.IH(1) and IH2 = Suc.IH(2)
  have case1: "\<And>ty ty'. elab_type (Suc fuel) typedefs env ghost ty = Inr ty' \<Longrightarrow> is_ground ty'"
  proof -
    fix ty ty'
    assume prem: "elab_type (Suc fuel) typedefs env ghost ty = Inr ty'"
    show "is_ground ty'"
    proof (cases ty)
      case (BabTy_Record loc flds)
      from prem BabTy_Record obtain fldTys where
        elab_ok: "elab_type_list fuel typedefs env ghost (map snd flds) = Inr fldTys"
        and ty'_eq: "ty' = BabTy_Record loc (zip (map fst flds) fldTys)"
        by (auto split: sum.splits)
      from IH2[OF elab_ok] have "\<forall>t \<in> set fldTys. is_ground t" by (simp add: list_all_iff)
      from list_all_snd_zip[OF this] show ?thesis using ty'_eq by simp
    qed (use prem IH1 IH2 in \<open>auto simp: Let_def list_all_iff split: if_splits option.splits sum.splits\<close>)
  qed
  { case 1
    from case1[OF "1.prems"] show ?case .
  }
  { case 2
    from "2.prems" show ?case
    proof (cases tys)
      case Nil
      then show ?thesis using "2.prems" by simp
    next
      case (Cons ty tys_rest)
      from "2.prems" Cons obtain ty' tys_rest' where
        head_ok: "elab_type (Suc fuel) typedefs env ghost ty = Inr ty'"
        and tail_ok: "elab_type_list fuel typedefs env ghost tys_rest = Inr tys_rest'"
        and result: "tys' = ty' # tys_rest'"
        by (auto split: sum.splits)
      from case1[OF head_ok] have "is_ground ty'" .
      moreover from IH2[OF tail_ok] have "list_all is_ground tys_rest'" .
      ultimately show ?thesis using Cons result by simp
    qed
  }
qed


(* If elab_type succeeds, the result is well-kinded.
   This follows from the structure of elab_type: it explicitly checks all the
   well-kindedness conditions (type vars in scope, datatype arities, etc.)
   and only returns Inr if they all pass. *)
lemma elab_type_is_well_kinded:
  "elab_type fuel typedefs env ghost ty = Inr ty' \<Longrightarrow> is_well_kinded env ty'"
  "elab_type_list fuel typedefs env ghost tys = Inr tys' \<Longrightarrow> list_all (is_well_kinded env) tys'"
proof (induction fuel arbitrary: ty ty' tys tys')
  case 0
  { case 1 then show ?case by simp }
  { case 2 then show ?case by simp }
next
  case (Suc fuel)
  note IH1 = Suc.IH(1) and IH2 = Suc.IH(2)
  have case1: "\<And>ty ty'. elab_type (Suc fuel) typedefs env ghost ty = Inr ty' \<Longrightarrow> is_well_kinded env ty'"
  proof -
    fix ty ty'
    assume prem: "elab_type (Suc fuel) typedefs env ghost ty = Inr ty'"
    show "is_well_kinded env ty'"
    proof (cases ty)
      case (BabTy_Record loc flds)
      from prem BabTy_Record obtain fldTys where
        elab_ok: "elab_type_list fuel typedefs env ghost (map snd flds) = Inr fldTys"
        and ty'_eq: "ty' = BabTy_Record loc (zip (map fst flds) fldTys)"
        by (auto split: sum.splits)
      from IH2[OF elab_ok] have "\<forall>t \<in> set fldTys. is_well_kinded env t" by (simp add: list_all_iff)
      from list_all_snd_zip[OF this] show ?thesis using ty'_eq by simp
    qed (use prem IH1 IH2 in \<open>auto simp: Let_def list_all_iff split: if_splits option.splits sum.splits\<close>)
  qed
  { case 1
    from case1[OF "1.prems"] show ?case .
  }
  { case 2
    from "2.prems" show ?case
    proof (cases tys)
      case Nil
      then show ?thesis using "2.prems" by simp
    next
      case (Cons ty tys_rest)
      from "2.prems" Cons obtain ty' tys_rest' where
        head_ok: "elab_type (Suc fuel) typedefs env ghost ty = Inr ty'"
        and tail_ok: "elab_type_list fuel typedefs env ghost tys_rest = Inr tys_rest'"
        and result: "tys' = ty' # tys_rest'"
        by (auto split: sum.splits)
      from case1[OF head_ok] have "is_well_kinded env ty'" .
      moreover from IH2[OF tail_ok] have "list_all (is_well_kinded env) tys_rest'" .
      ultimately show ?thesis using Cons result by simp
    qed
  }
qed


(* If elab_type succeeds in NotGhost mode, the result is a runtime type.
   elab_type explicitly checks is_runtime_type and returns TyErr_NonRuntimeTypeArg
   if the check fails in NotGhost mode. *)
lemma elab_type_is_runtime:
  "elab_type fuel typedefs env NotGhost ty = Inr ty' \<Longrightarrow> is_runtime_type ty'"
  "elab_type_list fuel typedefs env NotGhost tys = Inr tys' \<Longrightarrow> list_all is_runtime_type tys'"
proof (induction fuel arbitrary: ty ty' tys tys')
  case 0
  { case 1 then show ?case by simp }
  { case 2 then show ?case by simp }
next
  case (Suc fuel)
  note IH1 = Suc.IH(1) and IH2 = Suc.IH(2)
  have case1: "\<And>ty ty'. elab_type (Suc fuel) typedefs env NotGhost ty = Inr ty' \<Longrightarrow>
                         is_runtime_type ty'"
  proof -
    fix ty ty'
    assume prem: "elab_type (Suc fuel) typedefs env NotGhost ty = Inr ty'"
    show "is_runtime_type ty'"
    proof (cases ty)
      case (BabTy_Record loc flds)
      from prem BabTy_Record obtain fldTys where
        elab_ok: "elab_type_list fuel typedefs env NotGhost (map snd flds) = Inr fldTys"
        and ty'_eq: "ty' = BabTy_Record loc (zip (map fst flds) fldTys)"
        by (auto split: sum.splits)
      from IH2[OF elab_ok] have "\<forall>t \<in> set fldTys. is_runtime_type t" by (simp add: list_all_iff)
      from list_all_snd_zip[OF this] show ?thesis using ty'_eq by simp
    qed (use prem IH1 IH2 in \<open>auto simp: Let_def list_all_iff split: if_splits option.splits sum.splits\<close>)
  qed
  { case 1
    from case1[OF "1.prems"] show ?case .
  }
  { case 2
    from "2.prems" show ?case
    proof (cases tys)
      case Nil
      then show ?thesis using "2.prems" by simp
    next
      case (Cons ty tys_rest)
      from "2.prems" Cons obtain ty' tys_rest' where
        head_ok: "elab_type (Suc fuel) typedefs env NotGhost ty = Inr ty'"
        and tail_ok: "elab_type_list fuel typedefs env NotGhost tys_rest = Inr tys_rest'"
        and result: "tys' = ty' # tys_rest'"
        by (auto split: sum.splits)
      from case1[OF head_ok] have "is_runtime_type ty'" .
      moreover from IH2[OF tail_ok] have "list_all is_runtime_type tys_rest'" .
      ultimately show ?thesis using Cons result by simp
    qed
  }
qed


end
