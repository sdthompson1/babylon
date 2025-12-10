theory ElabTypeCorrect
  imports ElabType "../core/MetaSubst" "../core/CoreTyEnvWellFormed"
begin

(* Correctness properties for elab_type:
   - If elab_type succeeds, the result is ground, well-kinded, and a runtime type
     (in NotGhost mode).
   - The result of elab_type_list has the same length as the input.
*)

(* Helper lemmas about fmap_of_list and zip *)
lemma fmdom_fmap_of_list_zip:
  "length xs = length ys \<Longrightarrow> fset (fmdom (fmap_of_list (zip xs ys))) = set xs"
  by (induction xs ys rule: list_induct2) auto

lemma fmran'_fmupd_notin:
  "k |\<notin>| fmdom m \<Longrightarrow> fmran' (fmupd k v m) = insert v (fmran' m)"
proof (intro set_eqI iffI)
  fix x
  assume notin: "k |\<notin>| fmdom m"
  { assume "x \<in> fmran' (fmupd k v m)"
    then obtain a where "fmlookup (fmupd k v m) a = Some x"
      by (auto simp: fmran'_def)
    then have "x = v \<or> x \<in> fmran' m"
      by (cases "k = a") (auto simp: fmran'_def)
    thus "x \<in> insert v (fmran' m)" by auto
  }
  { assume "x \<in> insert v (fmran' m)"
    then have "x = v \<or> x \<in> fmran' m" by auto
    then show "x \<in> fmran' (fmupd k v m)"
    proof
      assume "x = v"
      thus ?thesis by (auto simp: fmran'_def)
    next
      assume "x \<in> fmran' m"
      then obtain a where lookup: "fmlookup m a = Some x"
        by (auto simp: fmran'_def)
      hence "a \<noteq> k" using notin by (auto dest: fmdomI)
      hence "fmlookup (fmupd k v m) a = Some x" using lookup by simp
      thus ?thesis
        by (simp add: fmran'I)
    qed
  }
qed

lemma fmran'_fmap_of_list_zip:
  "length xs = length ys \<Longrightarrow> distinct xs \<Longrightarrow> fmran' (fmap_of_list (zip xs ys)) = set ys"
proof (induction xs ys rule: list_induct2)
  case Nil
  then show ?case by (simp add: fmran'_def)
next
  case (Cons x xs y ys)
  from Cons.prems have x_notin: "x \<notin> set xs" and distinct_xs: "distinct xs" by simp_all
  from x_notin have x_notin_dom: "x |\<notin>| fmdom (fmap_of_list (zip xs ys))"
    using fmdom_fmap_of_list_zip[OF Cons.hyps] by simp
  have "fmran' (fmap_of_list (zip (x # xs) (y # ys))) =
        fmran' (fmupd x y (fmap_of_list (zip xs ys)))"
    by simp
  also have "... = insert y (fmran' (fmap_of_list (zip xs ys)))"
    using x_notin_dom by (rule fmran'_fmupd_notin)
  also have "... = insert y (set ys)"
    using Cons.IH distinct_xs by simp
  also have "... = set (y # ys)"
    by simp
  finally show ?case .
qed

(* Types returned by elab_type are ground *)
lemma elab_type_is_ground:
  "typedefs_well_formed env typedefs \<Longrightarrow>
   elab_type env typedefs ghost ty = Inr ty' \<Longrightarrow> is_ground ty'"
  "typedefs_well_formed env typedefs \<Longrightarrow>
   elab_type_list env typedefs ghost tys = Inr tys' \<Longrightarrow> list_all is_ground tys'"
proof (induction env typedefs ghost ty and env typedefs ghost tys
       arbitrary: ty' and tys' rule: elab_type_elab_type_list.induct)
  case (1 env typedefs ghost loc name tyargs)
  show ?case
  proof (cases "elab_type_list env typedefs ghost tyargs")
    case (Inl errs)
    then show ?thesis using "1.prems" by simp
  next
    case (Inr elabTyArgs)
    from "1.IH"(1)[OF "1.prems"(1) Inr]
    have elabTyArgs_ground: "list_all is_ground elabTyArgs" .
    show ?thesis
    proof (cases "name |\<in>| TE_TypeVars env")
      case True
      then show ?thesis using "1.prems" Inr by (auto split: if_splits)
    next
      case not_tyvar: False
      show ?thesis
      proof (cases "fmlookup typedefs name")
        case (Some typedef_entry)
        then obtain metavars targetTy where
          typedef_lookup: "fmlookup typedefs name = Some (metavars, targetTy)"
          by (cases typedef_entry) auto
        from "1.prems"(1) typedef_lookup
        have distinct_metavars: "distinct metavars"
          and metavars_subset: "type_metavars targetTy \<subseteq> set metavars"
          by (auto simp: typedefs_well_formed_def)
        show ?thesis
        proof (cases "length elabTyArgs = length metavars")
          case False
          then show ?thesis using "1.prems" Inr not_tyvar typedef_lookup by auto
        next
          case len_eq: True
          let ?subst = "fmap_of_list (zip metavars elabTyArgs)"
          let ?resultTy = "apply_subst ?subst targetTy"
          have dom_eq: "fset (fmdom ?subst) = set metavars"
            using fmdom_fmap_of_list_zip len_eq by metis
          have ran_eq: "fmran' ?subst = set elabTyArgs"
            using fmran'_fmap_of_list_zip len_eq distinct_metavars by metis
          have "type_metavars targetTy \<subseteq> fset (fmdom ?subst)"
            using metavars_subset dom_eq by auto
          moreover have "\<forall>ty' \<in> fmran' ?subst. is_ground ty'"
            using elabTyArgs_ground ran_eq by (simp add: list_all_iff)
          ultimately have result_ground: "is_ground ?resultTy"
            by (rule apply_subst_makes_ground)
          show ?thesis
          proof (cases "ghost = NotGhost \<and> \<not> is_runtime_type ?resultTy")
            case True
            then show ?thesis using "1.prems" Inr not_tyvar typedef_lookup len_eq by auto
          next
            case False
            then show ?thesis using "1.prems" Inr not_tyvar typedef_lookup len_eq result_ground by auto
          qed
        qed
      next
        case None
        then show ?thesis using "1.prems" Inr not_tyvar elabTyArgs_ground
          by (auto simp: list_all_iff split: option.splits if_splits)
      qed
    qed
  qed
next
  case (2 env typedefs ghost loc)
  then show ?case by simp
next
  case (3 env typedefs ghost loc sign bits)
  then show ?case by auto
next
  case (4 env typedefs ghost loc)
  then show ?case by (simp split: if_splits)
next
  case (5 env typedefs ghost loc)
  then show ?case by (simp split: if_splits)
next
  case (6 env typedefs ghost loc types)
  then show ?case
    by (auto simp: list_all_iff split: sum.splits dest!: set_zip_rightD)
next
  case (7 env typedefs ghost loc flds)
  then show ?case
    by (auto simp: list_all_iff split: sum.splits dest!: set_zip_rightD)
next
  case (8 env typedefs ghost loc elemTy dims)
  then show ?case by simp
next
  case (9 env typedefs ghost)
  then show ?case by simp
next
  case (10 env typedefs ghost ty tys)
  then show ?case by (auto simp: list_all_iff split: sum.splits)
qed


(* Types returned by elab_type are well-kinded *)
lemma elab_type_is_well_kinded:
  "typedefs_well_formed env typedefs \<Longrightarrow> tyenv_well_formed env \<Longrightarrow>
   elab_type env typedefs ghost ty = Inr ty' \<Longrightarrow> is_well_kinded env ty'"
  "typedefs_well_formed env typedefs \<Longrightarrow> tyenv_well_formed env \<Longrightarrow>
   elab_type_list env typedefs ghost tys = Inr tys' \<Longrightarrow> list_all (is_well_kinded env) tys'"
proof (induction env typedefs ghost ty and env typedefs ghost tys
       arbitrary: ty' and tys' rule: elab_type_elab_type_list.induct)
  case (1 env typedefs ghost loc name tyargs)
  show ?case
  proof (cases "elab_type_list env typedefs ghost tyargs")
    case (Inl errs)
    then show ?thesis using "1.prems" by simp
  next
    case (Inr elabTyArgs)
    from "1.IH"(1)[OF "1.prems"(1,2) Inr]
    have elabTyArgs_wk: "list_all (is_well_kinded env) elabTyArgs" .
    show ?thesis
    proof (cases "name |\<in>| TE_TypeVars env")
      case True
      then show ?thesis using "1.prems" Inr by (auto split: if_splits)
    next
      case not_tyvar: False
      show ?thesis
      proof (cases "fmlookup typedefs name")
        case (Some typedef_entry)
        then obtain metavars targetTy where
          typedef_lookup: "fmlookup typedefs name = Some (metavars, targetTy)"
          by (cases typedef_entry) auto
        from "1.prems"(1) typedef_lookup
        have distinct_metavars: "distinct metavars"
          and targetTy_wk: "is_well_kinded env targetTy"
          by (auto simp: typedefs_well_formed_def)
        show ?thesis
        proof (cases "length elabTyArgs = length metavars")
          case False
          then show ?thesis using "1.prems" Inr not_tyvar typedef_lookup by auto
        next
          case len_eq: True
          let ?subst = "fmap_of_list (zip metavars elabTyArgs)"
          let ?resultTy = "apply_subst ?subst targetTy"
          have ran_eq: "fmran' ?subst = set elabTyArgs"
            using fmran'_fmap_of_list_zip len_eq distinct_metavars by metis
          have "metasubst_well_kinded env ?subst"
            using elabTyArgs_wk ran_eq
            by (simp add: metasubst_well_kinded_from_zip)
          hence result_wk: "is_well_kinded env ?resultTy"
            using targetTy_wk
            by (simp add: apply_subst_preserves_well_kinded)
          show ?thesis
          proof (cases "ghost = NotGhost \<and> \<not> is_runtime_type ?resultTy")
            case True
            then show ?thesis using "1.prems" Inr not_tyvar typedef_lookup len_eq by auto
          next
            case False
            then show ?thesis using "1.prems" Inr not_tyvar typedef_lookup len_eq result_wk by auto
          qed
        qed
      next
        case None
        show ?thesis
        proof (cases "fmlookup (TE_Datatypes env) name")
          case (Some expectedArity)
          then show ?thesis using "1.prems" Inr not_tyvar None elabTyArgs_wk
            by (auto simp: list_all_iff split: if_splits)
        next
          case dtNone: None
          then show ?thesis using "1.prems" Inr not_tyvar None by simp
        qed
      qed
    qed
  qed
next
  case (2 env typedefs ghost loc)
  then show ?case by simp
next
  case (3 env typedefs ghost loc sign bits)
  then show ?case by auto
next
  case (4 env typedefs ghost loc)
  then show ?case by (simp split: if_splits)
next
  case (5 env typedefs ghost loc)
  then show ?case by (simp split: if_splits)
next
  case (6 env typedefs ghost loc types)
  then show ?case
    by (auto simp: list_all_iff split: sum.splits dest!: set_zip_rightD)
next
  case (7 env typedefs ghost loc flds)
  then show ?case
    by (auto simp: list_all_iff split: sum.splits dest!: set_zip_rightD)
next
  case (8 env typedefs ghost loc elemTy dims)
  then show ?case by simp
next
  case (9 env typedefs ghost)
  then show ?case by simp
next
  case (10 env typedefs ghost ty tys)
  then show ?case by (auto simp: list_all_iff split: sum.splits)
qed


(* Types returned by elab_type in NotGhost mode are runtime types *)
lemma elab_type_notghost_is_runtime:
  "typedefs_well_formed env typedefs \<Longrightarrow>
   elab_type env typedefs NotGhost ty = Inr ty' \<Longrightarrow> is_runtime_type ty'"
  "typedefs_well_formed env typedefs \<Longrightarrow>
   elab_type_list env typedefs NotGhost tys = Inr tys' \<Longrightarrow> list_all is_runtime_type tys'"
proof (induction env typedefs NotGhost ty and env typedefs NotGhost tys
       arbitrary: ty' and tys' rule: elab_type_elab_type_list.induct)
  case (1 env typedefs loc name tyargs)
  show ?case
  proof (cases "elab_type_list env typedefs NotGhost tyargs")
    case (Inl errs)
    then show ?thesis using "1.prems" by simp
  next
    case (Inr elabTyArgs)
    have elabTyArgs_rt: "list_all is_runtime_type elabTyArgs"
      by (simp add: "1.hyps" "1.prems"(1) Inr) 
    show ?thesis
    proof (cases "name |\<in>| TE_TypeVars env")
      case True
      then show ?thesis using "1.prems" Inr by (auto split: if_splits)
    next
      case not_tyvar: False
      show ?thesis
      proof (cases "fmlookup typedefs name")
        case (Some typedef_entry)
        then obtain metavars targetTy where
          typedef_lookup: "fmlookup typedefs name = Some (metavars, targetTy)"
          by (cases typedef_entry) auto
        show ?thesis
        proof (cases "length elabTyArgs = length metavars")
          case False
          then show ?thesis using "1.prems" Inr not_tyvar typedef_lookup by auto
        next
          case len_eq: True
          let ?subst = "fmap_of_list (zip metavars elabTyArgs)"
          let ?resultTy = "apply_subst ?subst targetTy"
          (* In NotGhost mode, we check is_runtime_type on the result *)
          show ?thesis
          proof (cases "is_runtime_type ?resultTy")
            case False
            (* If not runtime, we return Inl, so premise is false *)
            then show ?thesis using "1.prems" Inr not_tyvar typedef_lookup len_eq by auto
          next
            case True
            (* If runtime, we return Inr resultTy, and is_runtime_type holds *)
            then show ?thesis using "1.prems" Inr not_tyvar typedef_lookup len_eq by auto
          qed
        qed
      next
        case None
        show ?thesis
        proof (cases "fmlookup (TE_Datatypes env) name")
          case (Some expectedArity)
          then show ?thesis using "1.prems" Inr not_tyvar None elabTyArgs_rt
            by (auto simp: list_all_iff split: if_splits)
        next
          case dtNone: None
          then show ?thesis using "1.prems" Inr not_tyvar None by simp
        qed
      qed
    qed
  qed
next
  case (2 env typedefs loc)
  then show ?case by simp
next
  case (3 env typedefs loc sign bits)
  then show ?case by auto
next
  case (4 env typedefs loc)
  (* MathInt case - in NotGhost mode, this returns Inl, so premise is false *)
  then show ?case by simp
next
  case (5 env typedefs loc)
  (* MathReal case - in NotGhost mode, this returns Inl, so premise is false *)
  then show ?case by simp
next
  case (6 env typedefs loc types)
  then show ?case
    by (auto simp: list_all_iff split: sum.splits dest!: set_zip_rightD)
next
  case (7 env typedefs loc flds)
  then show ?case
    by (auto simp: list_all_iff split: sum.splits dest!: set_zip_rightD)
next
  case (8 env typedefs loc elemTy dims)
  (* Array case is currently stubbed to Bool *)
  then show ?case by simp
next
  case (9 env typedefs)
  then show ?case by simp
next
  case (10 env typedefs ty tys)
  then show ?case by (auto simp: list_all_iff split: sum.splits)
qed


(* The result of elab_type_list has the same length as the input *)
lemma elab_type_list_length:
  "elab_type_list env typedefs ghost tys = Inr tys' \<Longrightarrow> length tys' = length tys"
proof (induction tys arbitrary: tys')
  case Nil
  then show ?case by simp
next
  case (Cons ty tys)
  then show ?case by (auto split: sum.splits)
qed

end
