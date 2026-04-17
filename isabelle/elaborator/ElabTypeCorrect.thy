theory ElabTypeCorrect
  imports ElabType "../core/TypeSubst" "../core/CoreTyEnvWellFormed" "../core/CoreTypeSubst"
begin

(* Correctness properties for elab_type:
   - If elab_type succeeds, the result:
      - is well-kinded
      - its type variables are a subset of TE_TypeVars env
      - in NotGhost mode, it is a runtime type
   - The result of elab_type_list has the same length as the input.
*)

(* Type variables in types returned by elab_type are a subset of TE_TypeVars env *)
lemma elab_type_tyvars_subset:
  "typedefs_well_formed env (EE_Typedefs elabEnv) \<Longrightarrow>
   elab_type env elabEnv ghost ty = Inr ty' \<Longrightarrow>
   type_tyvars ty' \<subseteq> fset (TE_TypeVars env)"
  "typedefs_well_formed env (EE_Typedefs elabEnv) \<Longrightarrow>
   elab_type_list env elabEnv ghost tys = Inr tys' \<Longrightarrow>
   \<forall>t \<in> set tys'. type_tyvars t \<subseteq> fset (TE_TypeVars env)"
proof (induction env elabEnv ghost ty and env elabEnv ghost tys
       arbitrary: ty' and tys' rule: elab_type_elab_type_list.induct)
  case (1 env elabEnv ghost loc name tyargs)
  show ?case
  proof (cases "elab_type_list env elabEnv ghost tyargs")
    case (Inl errs)
    then show ?thesis using "1.prems" by simp
  next
    case (Inr elabTyArgs)
    from "1.IH"(1)[OF "1.prems"(1) Inr]
    have elabTyArgs_tyvars: "\<forall>t \<in> set elabTyArgs. type_tyvars t \<subseteq> fset (TE_TypeVars env)" .
    show ?thesis
    proof (cases "fmlookup (EE_Typedefs elabEnv) name")
      case (Some typedef_entry)
      then obtain tyvars targetTy where
        typedef_lookup: "fmlookup (EE_Typedefs elabEnv) name = Some (tyvars, targetTy)"
        by (cases typedef_entry) auto
      from "1.prems"(1) typedef_lookup
      have distinct_tyvars: "distinct tyvars"
        and tyvars_subset: "type_tyvars targetTy \<subseteq> set tyvars"
        by (auto simp: typedefs_well_formed_def)
      show ?thesis
      proof (cases "length elabTyArgs = length tyvars")
        case False
        then show ?thesis using "1.prems" Inr typedef_lookup by auto
      next
        case len_eq: True
        let ?subst = "fmap_of_list (zip tyvars elabTyArgs)"
        let ?resultTy = "apply_subst ?subst targetTy"
        have dom_eq: "fset (fmdom ?subst) = set tyvars"
          using fmdom_fmap_of_list_zip len_eq by metis
        have ran_eq: "fmran' ?subst = set elabTyArgs"
          using fmran'_fmap_of_list_zip len_eq distinct_tyvars by metis
        (* The tyvars in the result are bounded by: (tyvars in targetTy \ dom subst) \<union> range_tyvars subst
           Since tyvars in targetTy \<subseteq> set tyvars = dom subst, the first part is empty.
           The range_tyvars are tyvars from elabTyArgs, which are \<subseteq> TE_TypeVars by IH. *)
        have "type_tyvars ?resultTy \<subseteq>
              (type_tyvars targetTy - fset (fmdom ?subst)) \<union> subst_range_tyvars ?subst"
          by (rule apply_subst_tyvars_result)
        also have "... \<subseteq> subst_range_tyvars ?subst"
          using tyvars_subset dom_eq by auto
        also have "... \<subseteq> fset (TE_TypeVars env)"
          using elabTyArgs_tyvars ran_eq by (auto simp: subst_range_tyvars_def fmran'_def)
        finally have result_tyvars: "type_tyvars ?resultTy \<subseteq> fset (TE_TypeVars env)" .
        show ?thesis
        proof (cases "ghost = NotGhost \<and> \<not> is_runtime_type env ?resultTy")
          case True
          then show ?thesis using "1.prems" Inr typedef_lookup len_eq by auto
        next
          case False
          then show ?thesis using "1.prems" Inr typedef_lookup len_eq result_tyvars by auto
        qed
      qed
    next
      case None
      then show ?thesis using "1.prems" Inr elabTyArgs_tyvars
        by (force simp: list_all_iff split: option.splits if_splits)
    qed
  qed
next
  case (2 env elabEnv ghost loc)
  then show ?case by simp
next
  case (3 env elabEnv ghost loc sign bits)
  then show ?case by auto
next
  case (4 env elabEnv ghost loc)
  then show ?case by (simp split: if_splits)
next
  case (5 env elabEnv ghost loc)
  then show ?case by (simp split: if_splits)
next
  case (6 env elabEnv ghost loc types)
  then show ?case
    by (force split: sum.splits dest!: set_zip_rightD)
next
  case (7 env elabEnv ghost loc flds)
  then show ?case
    by (fastforce split: sum.splits option.splits dest!: set_zip_rightD)
next
  case (8 env elabEnv ghost loc elemTy dims)
  then show ?case
    by (auto split: sum.splits if_splits)
next
  case (9 env elabEnv ghost)
  then show ?case by simp
next
  case (10 env elabEnv ghost ty tys)
  then show ?case by (force split: sum.splits)
qed


(* The result of elab_type_list has the same length as the input *)
lemma elab_type_list_length:
  "elab_type_list env elabEnv ghost tys = Inr tys' \<Longrightarrow> length tys' = length tys"
proof (induction tys arbitrary: tys')
  case Nil
  then show ?case by simp
next
  case (Cons ty tys)
  then show ?case by (auto split: sum.splits)
qed

(* The result of elab_dimensions has the same length as the input *)
lemma elab_dimensions_length:
  "elab_dimensions dims loc = Inr dims' \<Longrightarrow> length dims' = length dims"
proof (induction dims arbitrary: dims')
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  then show ?case by (auto split: sum.splits)
qed

(* A dimension produced by elab_dimension satisfies dim_in_range *)
lemma elab_dimension_in_range:
  "elab_dimension d loc = Inr d' \<Longrightarrow> dim_in_range d'"
  by (induction d loc rule: elab_dimension.induct) (auto split: if_splits)

(* All dimensions produced by elab_dimensions satisfy dim_in_range *)
lemma elab_dimensions_in_range:
  "elab_dimensions dims loc = Inr dims' \<Longrightarrow> list_all dim_in_range dims'"
proof (induction dims arbitrary: dims')
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  then show ?case
    by (auto split: sum.splits dest: elab_dimension_in_range)
qed


(* Types returned by elab_type are well-kinded *)
lemma elab_type_is_well_kinded:
  "typedefs_well_formed env (EE_Typedefs elabEnv) \<Longrightarrow> tyenv_well_formed env \<Longrightarrow>
   elab_type env elabEnv ghost ty = Inr ty' \<Longrightarrow> is_well_kinded env ty'"
  "typedefs_well_formed env (EE_Typedefs elabEnv) \<Longrightarrow> tyenv_well_formed env \<Longrightarrow>
   elab_type_list env elabEnv ghost tys = Inr tys' \<Longrightarrow> list_all (is_well_kinded env) tys'"
proof (induction env elabEnv ghost ty and env elabEnv ghost tys
       arbitrary: ty' and tys' rule: elab_type_elab_type_list.induct)
  case (1 env elabEnv ghost loc name tyargs)
  show ?case
  proof (cases "elab_type_list env elabEnv ghost tyargs")
    case (Inl errs)
    then show ?thesis using "1.prems" by simp
  next
    case (Inr elabTyArgs)
    from "1.IH"(1)[OF "1.prems"(1,2) Inr]
    have elabTyArgs_wk: "list_all (is_well_kinded env) elabTyArgs" .
    show ?thesis
    proof (cases "fmlookup (EE_Typedefs elabEnv) name")
      case (Some typedef_entry)
      then obtain tyvars targetTy where
        typedef_lookup: "fmlookup (EE_Typedefs elabEnv) name = Some (tyvars, targetTy)"
        by (cases typedef_entry) auto
      from "1.prems"(1) typedef_lookup
      have distinct_tyvars: "distinct tyvars"
        and targetTy_wk: "is_well_kinded env targetTy"
        by (auto simp: typedefs_well_formed_def)
      show ?thesis
      proof (cases "length elabTyArgs = length tyvars")
        case False
        then show ?thesis using "1.prems" Inr typedef_lookup by auto
      next
        case len_eq: True
        let ?subst = "fmap_of_list (zip tyvars elabTyArgs)"
        let ?resultTy = "apply_subst ?subst targetTy"
        have ran_eq: "fmran' ?subst = set elabTyArgs"
          using fmran'_fmap_of_list_zip[OF len_eq[symmetric] distinct_tyvars] .
        have subst_wk: "\<And>n ty. fmlookup ?subst n = Some ty \<Longrightarrow> is_well_kinded env ty"
          using elabTyArgs_wk ran_eq by (auto simp: list_all_iff dest: fmran'I)
        have result_wk: "is_well_kinded env ?resultTy"
          using targetTy_wk
          by (rule apply_subst_preserves_well_kinded[where src=env and tgt=env])
             (auto simp: subst_wk split: option.splits)
        show ?thesis
        proof (cases "ghost = NotGhost \<and> \<not> is_runtime_type env ?resultTy")
          case True
          then show ?thesis using "1.prems" Inr typedef_lookup len_eq by auto
        next
          case False
          then show ?thesis using "1.prems" Inr typedef_lookup len_eq result_wk by auto
        qed
      qed
    next
      case None
      show ?thesis
      proof (cases "fmlookup (TE_Datatypes env) name")
        case (Some expectedArity)
        then show ?thesis using "1.prems" Inr None elabTyArgs_wk
          by (auto simp: list_all_iff split: if_splits)
      next
        case dtNone: None
        then show ?thesis using "1.prems" Inr None by simp
      qed
    qed
  qed
next
  case (2 env elabEnv ghost loc)
  then show ?case by simp
next
  case (3 env elabEnv ghost loc sign bits)
  then show ?case by auto
next
  case (4 env elabEnv ghost loc)
  then show ?case by (simp split: if_splits)
next
  case (5 env elabEnv ghost loc)
  then show ?case by (simp split: if_splits)
next
  case (6 env elabEnv ghost loc types)
  then show ?case
    by (auto simp: list_all_iff distinct_tuple_field_names tuple_field_names_def[symmetric]
             split: sum.splits dest!: set_zip_rightD)
next
  case (7 env elabEnv ghost loc flds)
  then show ?case
    by (auto simp: list_all_iff
             dest!: elab_type_list_length first_duplicate_name_None_implies_distinct
                   set_zip_rightD
             split: sum.splits option.splits)
next
  case (8 env elabEnv ghost loc elemTy dims)
  show ?case
  proof (cases "elab_type env elabEnv ghost elemTy")
    case (Inl errs)
    then show ?thesis using "8.prems" by (auto split: sum.splits)
  next
    case elemTy_inr: (Inr elemTy')
    from "8.IH"(1)[OF "8.prems"(1,2) elemTy_inr] have elemTy_wk: "is_well_kinded env elemTy'" .
    show ?thesis
    proof (cases "elab_dimensions dims loc")
      case (Inl errs)
      then show ?thesis using "8.prems" elemTy_inr by simp
    next
      case dims_inr: (Inr dims')
      show ?thesis
      proof (cases "dims = [] \<or> \<not> dims_uniform dims'")
        case True
        then show ?thesis using "8.prems" elemTy_inr dims_inr by simp
      next
        case dims_ok: False
        from dims_inr have dims_len: "length dims' = length dims"
          by (rule elab_dimensions_length)
        from dims_ok dims_len have dims_nonempty: "dims' \<noteq> []" by auto
        from dims_ok have dims_uniform': "dims_uniform dims'" by simp
        from elab_dimensions_in_range[OF dims_inr]
        have dims_range: "list_all dim_in_range dims'" .
        have dims_wk: "array_dims_well_kinded dims'"
          using dims_nonempty dims_uniform' dims_range
          by (simp add: array_dims_well_kinded_def)
        from "8.prems"(3) elemTy_inr dims_inr dims_ok
        have ty'_eq: "ty' = CoreTy_Array elemTy' dims'" by simp
        show ?thesis using ty'_eq elemTy_wk dims_wk by simp
      qed
    qed
  qed
next
  case (9 env elabEnv ghost)
  then show ?case by simp
next
  case (10 env elabEnv ghost ty tys)
  then show ?case by (auto simp: list_all_iff split: sum.splits)
qed


(* Types returned by elab_type in NotGhost mode are runtime types *)
lemma elab_type_notghost_is_runtime:
  "typedefs_well_formed env (EE_Typedefs elabEnv) \<Longrightarrow> tyenv_well_formed env \<Longrightarrow>
   elab_type env elabEnv NotGhost ty = Inr ty' \<Longrightarrow> is_runtime_type env ty'"
  "typedefs_well_formed env (EE_Typedefs elabEnv) \<Longrightarrow> tyenv_well_formed env \<Longrightarrow>
   elab_type_list env elabEnv NotGhost tys = Inr tys' \<Longrightarrow> list_all (is_runtime_type env) tys'"
proof (induction env elabEnv NotGhost ty and env elabEnv NotGhost tys
       arbitrary: ty' and tys' rule: elab_type_elab_type_list.induct)
  case (1 env elabEnv loc name tyargs)
  show ?case
  proof (cases "elab_type_list env elabEnv NotGhost tyargs")
    case (Inl errs)
    then show ?thesis using "1.prems" by simp
  next
    case (Inr elabTyArgs)
    have elabTyArgs_rt: "list_all (is_runtime_type env) elabTyArgs"
      by (simp add: "1.hyps" "1.prems"(1,2) Inr)
    show ?thesis
    proof (cases "fmlookup (EE_Typedefs elabEnv) name")
      case (Some typedef_entry)
      then obtain tyvars targetTy where
        typedef_lookup: "fmlookup (EE_Typedefs elabEnv) name = Some (tyvars, targetTy)"
        by (cases typedef_entry) auto
      show ?thesis
      proof (cases "length elabTyArgs = length tyvars")
        case False
        then show ?thesis using "1.prems" Inr typedef_lookup by auto
      next
        case len_eq: True
        let ?subst = "fmap_of_list (zip tyvars elabTyArgs)"
        let ?resultTy = "apply_subst ?subst targetTy"
        (* In NotGhost mode, we check is_runtime_type on the result *)
        show ?thesis
        proof (cases "is_runtime_type env ?resultTy")
          case False
          (* If not runtime, we return Inl, so premise is false *)
          then show ?thesis using "1.prems" Inr typedef_lookup len_eq by auto
        next
          case True
          (* If runtime, we return Inr resultTy, and is_runtime_type holds *)
          then show ?thesis using "1.prems" Inr typedef_lookup len_eq by auto
        qed
      qed
    next
      case None
      show ?thesis
      proof (cases "fmlookup (TE_Datatypes env) name")
        case (Some expectedArity)
        then show ?thesis using "1.prems" Inr None elabTyArgs_rt
          by (auto simp: list_all_iff split: if_splits)
      next
        case dtNone: None
        then show ?thesis using "1.prems" Inr None by simp
      qed
    qed
  qed
next
  case (2 env elabEnv loc)
  then show ?case by simp
next
  case (3 env elabEnv loc sign bits)
  then show ?case by auto
next
  case (4 env elabEnv loc)
  (* MathInt case - in NotGhost mode, this returns Inl, so premise is false *)
  then show ?case by simp
next
  case (5 env elabEnv loc)
  (* MathReal case - in NotGhost mode, this returns Inl, so premise is false *)
  then show ?case by simp
next
  case (6 env elabEnv loc types)
  then show ?case
    by (auto simp: list_all_iff split: sum.splits dest!: set_zip_rightD)
next
  case (7 env elabEnv loc flds)
  then show ?case
    by (auto simp: list_all_iff split: sum.splits option.splits dest!: set_zip_rightD)
next
  case (8 env elabEnv loc elemTy dims)
  then show ?case
    by (auto split: sum.splits if_splits)
next
  case (9 env elabEnv)
  then show ?case by simp
next
  case (10 env elabEnv ty tys)
  then show ?case by (auto simp: list_all_iff split: sum.splits)
qed

end
