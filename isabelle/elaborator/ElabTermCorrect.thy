theory ElabTermCorrect
  imports "ElabTerm" "ElabTypeCorrect" "../type_system/BabTypecheck" "Unify3"
begin

(* Correctness of determine_fun_call_type:
   If it succeeds, the returned information is consistent with the function declaration
   and the resulting call term will typecheck correctly. *)
lemma determine_fun_call_type_correct:
  assumes "determine_fun_call_type fuel typedefs env ghost callTm next_mv
           = Inr (newCallTm, expArgTypes, retType, fnName, next_mv')"
      and "tyenv_well_formed env"
  shows "\<exists>fnLoc newTyArgs funDecl retTyDecl.
           newCallTm = BabTm_Name fnLoc fnName newTyArgs
         \<and> fmlookup (TE_Functions env) fnName = Some funDecl
         \<and> \<not> DF_Impure funDecl
         \<and> \<not> list_ex (\<lambda>(_, vr, _). vr = Ref) (DF_TmArgs funDecl)
         \<and> (ghost = NotGhost \<longrightarrow> DF_Ghost funDecl \<noteq> Ghost)
         \<and> DF_ReturnType funDecl = Some retTyDecl
         \<and> length newTyArgs = length (DF_TyArgs funDecl)
         \<and> list_all (is_well_kinded env) newTyArgs
         \<and> (ghost = NotGhost \<longrightarrow> list_all is_runtime_type newTyArgs)
         \<and> expArgTypes = map (\<lambda>(_, _, ty). substitute_bab_type
                                (fmap_of_list (zip (DF_TyArgs funDecl) newTyArgs)) ty)
                             (DF_TmArgs funDecl)
         \<and> retType = substitute_bab_type
                       (fmap_of_list (zip (DF_TyArgs funDecl) newTyArgs)) retTyDecl"
proof (cases callTm)
  case (BabTm_Name fnLoc fnName' tyArgs)
  from assms(1) BabTm_Name obtain funDecl where
    fn_lookup: "fmlookup (TE_Functions env) fnName' = Some funDecl"
    by (auto split: option.splits)
  from assms(1) BabTm_Name fn_lookup have
    not_impure: "\<not> DF_Impure funDecl"
    and no_ref_args: "\<not> list_ex (\<lambda>(_, vr, _). vr = Ref) (DF_TmArgs funDecl)"
    and ghost_ok: "ghost = NotGhost \<longrightarrow> DF_Ghost funDecl \<noteq> Ghost"
    by (auto split: if_splits)
  from assms(1) BabTm_Name fn_lookup not_impure no_ref_args ghost_ok obtain retTyDecl where
    ret_ty: "DF_ReturnType funDecl = Some retTyDecl"
    by (auto split: option.splits if_splits)

  let ?numTyParams = "length (DF_TyArgs funDecl)"

  show ?thesis
  proof (cases "tyArgs = [] \<and> ?numTyParams > 0")
    case True
    \<comment> \<open>Type args were omitted - metavariables generated\<close>
    let ?newTyArgs = "map BabTy_Meta [next_mv..<next_mv + ?numTyParams]"
    from assms(1) BabTm_Name fn_lookup not_impure no_ref_args ghost_ok ret_ty True
    have results: "newCallTm = BabTm_Name fnLoc fnName' ?newTyArgs"
                  "fnName = fnName'"
                  "expArgTypes = map (\<lambda>(_, _, ty). substitute_bab_type
                                   (fmap_of_list (zip (DF_TyArgs funDecl) ?newTyArgs)) ty)
                                 (DF_TmArgs funDecl)"
                  "retType = substitute_bab_type
                               (fmap_of_list (zip (DF_TyArgs funDecl) ?newTyArgs)) retTyDecl"
      by (auto simp: Let_def)
    have len_ok: "length ?newTyArgs = ?numTyParams" by simp
    have wk_ok: "list_all (is_well_kinded env) ?newTyArgs"
      using list_all_is_well_kinded_meta by simp
    have runtime_ok: "list_all is_runtime_type ?newTyArgs"
      by (simp add: list_all_iff)
    show ?thesis
      using fn_lookup not_impure no_ref_args ghost_ok ret_ty results len_ok wk_ok runtime_ok
      by auto
  next
    case False
    \<comment> \<open>Type args provided or no type params\<close>
    show ?thesis
    proof (cases "?numTyParams = length tyArgs")
      case True
      \<comment> \<open>Correct number of type args provided\<close>
      \<comment> \<open>In this case, tyArgs is non-empty or numTyParams = 0, so we elaborate tyArgs\<close>
      from assms(1) BabTm_Name fn_lookup not_impure no_ref_args ghost_ok ret_ty False True
      obtain newTyArgs where
        elab_tyargs: "elab_type_list fuel typedefs env ghost tyArgs = Inr newTyArgs"
        by (cases "elab_type_list fuel typedefs env ghost tyArgs")
           (auto simp: Let_def split: if_splits)
      from assms(1) BabTm_Name fn_lookup not_impure no_ref_args ghost_ok ret_ty False True elab_tyargs
      have results: "newCallTm = BabTm_Name fnLoc fnName' newTyArgs"
                    "fnName = fnName'"
                    "expArgTypes = map (\<lambda>(_, _, ty). substitute_bab_type
                                     (fmap_of_list (zip (DF_TyArgs funDecl) newTyArgs)) ty)
                                   (DF_TmArgs funDecl)"
                    "retType = substitute_bab_type
                                 (fmap_of_list (zip (DF_TyArgs funDecl) newTyArgs)) retTyDecl"
        by (auto simp: Let_def)
      have len_ok: "length newTyArgs = ?numTyParams"
        using elab_tyargs True elab_type_list_length by fastforce
      have wk_ok: "list_all (is_well_kinded env) newTyArgs"
        using elab_tyargs elab_type_is_well_kinded(2) by auto
      have runtime_ok: "ghost = NotGhost \<longrightarrow> list_all is_runtime_type newTyArgs"
        using elab_tyargs elab_type_is_runtime(2) by (cases ghost; auto)
      show ?thesis
        using fn_lookup not_impure no_ref_args ghost_ok ret_ty results len_ok wk_ok runtime_ok
        by auto
    next
      case False2: False
      \<comment> \<open>Wrong number of type args - elaboration would fail\<close>
      from assms(1) BabTm_Name fn_lookup not_impure no_ref_args ghost_ok ret_ty False False2
      have "False" by (auto simp: Let_def split: sum.splits if_splits)
      thus ?thesis ..
    qed
  qed
qed (use assms(1) in simp_all)


(* Correctness of unify_call_types (Phase 1):
   If it succeeds, the substitution preserves well-kindedness and runtime properties,
   finalSubst extends accSubst (via composition), and for each pair of types, either:
   - apply_subst finalSubst actualTy equals apply_subst finalSubst expectedTy (up to types_equal), or
   - both are finite integer types (coercion will be inserted in phase 2) *)
lemma unify_call_types_correct:
  assumes "unify_call_types loc fnName argIdx actualTys expectedTys accSubst = Inr finalSubst"
      and "tyenv_well_formed env"
      and "length actualTys = length expectedTys"
      and "list_all (is_well_kinded env) actualTys"
      and "list_all (is_well_kinded env) expectedTys"
      and "\<forall>ty \<in> fmran' accSubst. is_well_kinded env ty"
      and "ghost = NotGhost \<longrightarrow> list_all is_runtime_type actualTys"
      and "ghost = NotGhost \<longrightarrow> list_all is_runtime_type expectedTys"
      and "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' accSubst. is_runtime_type ty)"
  shows "(\<forall>ty \<in> fmran' finalSubst. is_well_kinded env ty)
       \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type ty))
       \<and> (\<exists>theta. finalSubst = compose_subst theta accSubst)
       \<and> list_all2 (\<lambda>actualTy expectedTy.
           types_equal (apply_subst finalSubst actualTy) (apply_subst finalSubst expectedTy)
           \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
              \<and> is_finite_integer_type (apply_subst finalSubst expectedTy)))
         actualTys expectedTys"
  using assms
proof (induction loc fnName argIdx actualTys expectedTys accSubst
       arbitrary: finalSubst
       rule: unify_call_types.induct)
  case (1 loc fnName argIdx accSubst)
  from "1.prems"(1) have "finalSubst = accSubst" by simp
  moreover have "accSubst = compose_subst fmempty accSubst"
    by simp
  ultimately show ?case using "1.prems"(6,9) by blast
next
  case (2 loc fnName argIdx actualTy actualTys expectedTy expectedTys accSubst)
  let ?actualTy' = "apply_subst accSubst actualTy"
  let ?expectedTy' = "apply_subst accSubst expectedTy"

  from "2.prems"(3) have len_tl: "length actualTys = length expectedTys" by simp
  from "2.prems"(4) have actualTy_wk: "is_well_kinded env actualTy"
    and actualTys_wk: "list_all (is_well_kinded env) actualTys" by simp_all
  from "2.prems"(5) have expectedTy_wk: "is_well_kinded env expectedTy"
    and expectedTys_wk: "list_all (is_well_kinded env) expectedTys" by simp_all
  from "2.prems"(7) have actualTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type actualTy"
    and actualTys_rt: "ghost = NotGhost \<longrightarrow> list_all is_runtime_type actualTys" by simp_all
  from "2.prems"(8) have expectedTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type expectedTy"
    and expectedTys_rt: "ghost = NotGhost \<longrightarrow> list_all is_runtime_type expectedTys" by simp_all

  have actualTy'_wk: "is_well_kinded env ?actualTy'"
    using actualTy_wk "2.prems"(6) is_well_kinded_apply_subst by blast
  have expectedTy'_wk: "is_well_kinded env ?expectedTy'"
    using expectedTy_wk "2.prems"(6) is_well_kinded_apply_subst by blast
  have actualTy'_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type ?actualTy'"
    using actualTy_rt "2.prems"(9) is_runtime_type_apply_subst by blast
  have expectedTy'_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type ?expectedTy'"
    using expectedTy_rt "2.prems"(9) is_runtime_type_apply_subst by blast

  show ?case
  proof (cases "unify ?actualTy' ?expectedTy'")
    case (Some newSubst)
    let ?composedSubst = "compose_subst newSubst accSubst"

    from "2.prems"(1) Some have
      recurse: "unify_call_types loc fnName (argIdx + 1) actualTys expectedTys ?composedSubst = Inr finalSubst"
      by (simp add: Let_def)

    have newSubst_wk: "\<forall>ty \<in> fmran' newSubst. is_well_kinded env ty"
      using Some actualTy'_wk expectedTy'_wk unify_preserves_well_kinded by blast
    have newSubst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' newSubst. is_runtime_type ty)"
      using Some actualTy'_rt expectedTy'_rt unify_preserves_runtime by blast

    have composed_wk: "\<forall>ty \<in> fmran' ?composedSubst. is_well_kinded env ty"
      using newSubst_wk "2.prems"(6) compose_subst_preserves_well_kinded by blast
    have composed_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' ?composedSubst. is_runtime_type ty)"
      using newSubst_rt "2.prems"(9) compose_subst_preserves_runtime by blast

    have ih: "(\<forall>ty \<in> fmran' finalSubst. is_well_kinded env ty)
            \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type ty))
            \<and> (\<exists>theta. finalSubst = compose_subst theta ?composedSubst)
            \<and> list_all2 (\<lambda>actualTy expectedTy.
                types_equal (apply_subst finalSubst actualTy) (apply_subst finalSubst expectedTy)
                \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
                   \<and> is_finite_integer_type (apply_subst finalSubst expectedTy)))
              actualTys expectedTys"
      using "2.IH"(2) Some len_tl actualTys_rt actualTys_wk assms(2) composed_rt composed_wk expectedTys_rt
        expectedTys_wk recurse by simp

    \<comment> \<open>From unify_sound, after applying newSubst the types are equal\<close>
    from unify_sound[OF Some]
    have "types_equal (apply_subst newSubst ?actualTy') (apply_subst newSubst ?expectedTy')" .
    \<comment> \<open>By compose_subst_correct this equals apply_subst composedSubst on original types\<close>
    hence head_eq: "types_equal (apply_subst ?composedSubst actualTy) (apply_subst ?composedSubst expectedTy)"
      by (simp add: compose_subst_correct)

    \<comment> \<open>finalSubst extends composedSubst, so we can use types_equal_apply_subst\<close>
    from ih obtain theta where theta: "finalSubst = compose_subst theta ?composedSubst" by blast
    have "apply_subst finalSubst actualTy = apply_subst theta (apply_subst ?composedSubst actualTy)"
      using theta by (simp add: compose_subst_correct)
    moreover have "apply_subst finalSubst expectedTy = apply_subst theta (apply_subst ?composedSubst expectedTy)"
      using theta by (simp add: compose_subst_correct)
    moreover have "types_equal (apply_subst theta (apply_subst ?composedSubst actualTy))
                               (apply_subst theta (apply_subst ?composedSubst expectedTy))"
      using head_eq types_equal_apply_subst by blast
    ultimately have head_final: "types_equal (apply_subst finalSubst actualTy) (apply_subst finalSubst expectedTy)"
      by simp

    \<comment> \<open>finalSubst extends accSubst: compose theta with (compose newSubst accSubst) = compose (compose theta newSubst) accSubst\<close>
    have extends: "\<exists>theta'. finalSubst = compose_subst theta' accSubst"
    proof -
      have "finalSubst = compose_subst theta ?composedSubst" using theta .
      also have "... = compose_subst theta (compose_subst newSubst accSubst)" by simp
      also have "... = compose_subst (compose_subst theta newSubst) accSubst"
        by (simp add: compose_subst_assoc)
      show ?thesis
        using compose_subst_assoc ih by blast
    qed

    show ?thesis using ih head_final extends by simp
  next
    case None
    \<comment> \<open>Unification failed - must be integer coercion case\<close>
    from "2.prems"(1) None have
      is_int: "is_finite_integer_type ?actualTy' \<and> is_finite_integer_type ?expectedTy'"
      and recurse: "unify_call_types loc fnName (argIdx + 1) actualTys expectedTys accSubst = Inr finalSubst"
      by (simp_all add: Let_def split: if_splits)

    have ih: "(\<forall>ty \<in> fmran' finalSubst. is_well_kinded env ty)
            \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type ty))
            \<and> (\<exists>theta. finalSubst = compose_subst theta accSubst)
            \<and> list_all2 (\<lambda>actualTy expectedTy.
                types_equal (apply_subst finalSubst actualTy) (apply_subst finalSubst expectedTy)
                \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
                   \<and> is_finite_integer_type (apply_subst finalSubst expectedTy)))
              actualTys expectedTys"
      using "2.IH"(1) None is_int len_tl recurse "2.prems"(2) actualTys_wk expectedTys_wk
                       "2.prems"(6) actualTys_rt expectedTys_rt "2.prems"(9)
      by simp

    \<comment> \<open>The head types are finite integers after applying accSubst.
       Since finite integer types are ground, applying any substitution gives the same result.\<close>
    have actual_finite: "is_finite_integer_type (apply_subst finalSubst actualTy)"
      using is_int apply_subst_finite_integer
      by (metis compose_subst_correct ih)
    have expected_finite: "is_finite_integer_type (apply_subst finalSubst expectedTy)"
      using is_int apply_subst_finite_integer
      using compose_subst_correct ih by force
    have head_int: "is_finite_integer_type (apply_subst finalSubst actualTy)
                  \<and> is_finite_integer_type (apply_subst finalSubst expectedTy)"
      using actual_finite expected_finite by simp

    show ?thesis using ih head_int by simp
  qed
next
  case ("3_1" uu uv uw v va uz)
  then show ?case by simp
next
  case ("3_2" uu uv uw v va uz)
  then show ?case by simp
qed


(* Correctness of apply_call_coercions (Phase 2):
   If the input terms have the actual types, and the types satisfy the property from phase 1,
   then the output terms have the expected types (after substitution). *)
lemma apply_call_coercions_correct:
  assumes "list_all2 (\<lambda>tm ty. bab_term_type env ghost tm = Some ty) tms actualTys"
      and "tyenv_well_formed env"
      and "length tms = length actualTys"
      and "length actualTys = length expectedTys"
      and "\<forall>ty \<in> fmran' subst. is_well_kinded env ty"
      and "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' subst. is_runtime_type ty)"
      and "list_all2 (\<lambda>actualTy expectedTy.
             types_equal (apply_subst subst actualTy) (apply_subst subst expectedTy)
             \<or> (is_finite_integer_type (apply_subst subst actualTy)
                \<and> is_finite_integer_type (apply_subst subst expectedTy)))
           actualTys expectedTys"
  shows "list_all2 (\<lambda>tm expectedTy.
           \<exists>ty. bab_term_type env ghost tm = Some ty \<and>
                types_equal ty (apply_subst subst expectedTy))
         (apply_call_coercions subst tms actualTys expectedTys) expectedTys"
  using assms
proof (induction subst tms actualTys expectedTys rule: apply_call_coercions.induct)
  case (1 subst)
  then show ?case by simp
next
  case (2 subst tm tms actualTy actualTys expectedTy expectedTys)
  from "2.prems"(1) have
    head_typed: "bab_term_type env ghost tm = Some actualTy"
    and tail_typed: "list_all2 (\<lambda>tm ty. bab_term_type env ghost tm = Some ty) tms actualTys"
    by simp_all
  from "2.prems"(3) have len_tms: "length tms = length actualTys" by simp
  from "2.prems"(4) have len_tys: "length actualTys = length expectedTys" by simp
  from "2.prems"(7) have
    head_compat: "types_equal (apply_subst subst actualTy) (apply_subst subst expectedTy)
                  \<or> (is_finite_integer_type (apply_subst subst actualTy)
                     \<and> is_finite_integer_type (apply_subst subst expectedTy))"
    and tail_compat: "list_all2 (\<lambda>actualTy expectedTy.
             types_equal (apply_subst subst actualTy) (apply_subst subst expectedTy)
             \<or> (is_finite_integer_type (apply_subst subst actualTy)
                \<and> is_finite_integer_type (apply_subst subst expectedTy)))
           actualTys expectedTys"
    by simp_all

  let ?tm' = "apply_subst_to_term subst tm"
  let ?actualTy' = "apply_subst subst actualTy"
  let ?expectedTy' = "apply_subst subst expectedTy"

  have tm'_typed: "bab_term_type env ghost ?tm' = Some ?actualTy'"
    using head_typed apply_subst_to_term_preserves_typing "2.prems"(2,5,6) by blast

  have head_result: "\<exists>ty. bab_term_type env ghost
                       (if types_equal ?actualTy' ?expectedTy' then ?tm'
                        else BabTm_Cast (bab_term_location tm) ?expectedTy' ?tm')
                     = Some ty \<and> types_equal ty ?expectedTy'"
  proof (cases "types_equal ?actualTy' ?expectedTy'")
    case True
    \<comment> \<open>Types are equal (up to locations), so we return tm' with type actualTy'\<close>
    have "bab_term_type env ghost ?tm' = Some ?actualTy'" using tm'_typed .
    moreover have "types_equal ?actualTy' ?expectedTy'" using True .
    ultimately show ?thesis by auto
  next
    case False
    \<comment> \<open>Types not equal, so must be integer coercion case - we insert a cast\<close>
    from head_compat False have
      actual_int: "is_finite_integer_type ?actualTy'"
      and expected_int: "is_finite_integer_type ?expectedTy'"
      by auto
    have expected_runtime: "is_runtime_type ?expectedTy'"
      using expected_int by (cases ?expectedTy') auto
    have "bab_term_type env ghost (BabTm_Cast (bab_term_location tm) ?expectedTy' ?tm') = Some ?expectedTy'"
      using tm'_typed actual_int expected_int expected_runtime finite_integer_type_is_integer_type by auto
    moreover have "types_equal ?expectedTy' ?expectedTy'"
      using types_equal_reflexive by simp
    ultimately show ?thesis using False by auto
  qed

  have ih: "list_all2 (\<lambda>tm expectedTy.
              \<exists>ty. bab_term_type env ghost tm = Some ty \<and> types_equal ty (apply_subst subst expectedTy))
              (apply_call_coercions subst tms actualTys expectedTys) expectedTys"
    using "2.IH" tail_typed "2.prems"(2) len_tms len_tys "2.prems"(5,6) tail_compat by simp

  have unfolded: "apply_call_coercions subst (tm # tms) (actualTy # actualTys) (expectedTy # expectedTys)
                = (if types_equal ?actualTy' ?expectedTy' then ?tm'
                   else BabTm_Cast (bab_term_location tm) ?expectedTy' ?tm')
                  # apply_call_coercions subst tms actualTys expectedTys"
    by simp
  show ?case using head_result ih unfolded by simp
qed (simp_all) 


(* Correctness of unify_call_args:
   Combines the two phase lemmas to show that if unify_call_args succeeds,
   the resulting terms typecheck and their types match the expected types. *)
lemma unify_call_args_correct:
  assumes "unify_call_args loc fnName argIdx tms actualTys expectedTys accSubst
           = Inr (finalTms, finalSubst)"
      and "tyenv_well_formed env"
      and "list_all2 (\<lambda>tm ty. bab_term_type env ghost tm = Some ty) tms actualTys"
      and "length actualTys = length expectedTys"
      and "\<forall>ty \<in> fmran' accSubst. is_well_kinded env ty"
      and "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' accSubst. is_runtime_type ty)"
      and "list_all (is_well_kinded env) actualTys"
      and "list_all (is_well_kinded env) expectedTys"
      and "ghost = NotGhost \<longrightarrow> list_all is_runtime_type actualTys"
      and "ghost = NotGhost \<longrightarrow> list_all is_runtime_type expectedTys"
  shows "list_all2 (\<lambda>tm expectedTy.
           \<exists>ty. bab_term_type env ghost tm = Some ty \<and>
                types_equal ty (apply_subst finalSubst expectedTy))
         finalTms expectedTys
       \<and> (\<forall>ty \<in> fmran' finalSubst. is_well_kinded env ty)
       \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type ty))"
proof -
  \<comment> \<open>Unfold unify_call_args definition\<close>
  define finalSubst' where "finalSubst' = finalSubst"
  have phase1: "unify_call_types loc fnName argIdx actualTys expectedTys accSubst = Inr finalSubst'"
    using assms(1) by (simp add: unify_call_args_def finalSubst'_def split: sum.splits)
  have finalTms_def: "finalTms = apply_call_coercions finalSubst' tms actualTys expectedTys"
    using assms(1) phase1 unify_call_args_def by auto
  have finalSubst_eq: "finalSubst = finalSubst'"
    by (simp add: finalSubst'_def)

  \<comment> \<open>Get length of tms from list_all2\<close>
  have len_tms: "length tms = length actualTys"
    using assms(3) by (simp add: list_all2_lengthD)

  \<comment> \<open>Apply phase 1 correctness\<close>
  have phase1_correct: "(\<forall>ty \<in> fmran' finalSubst'. is_well_kinded env ty)
       \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst'. is_runtime_type ty))
       \<and> (\<exists>theta. finalSubst' = compose_subst theta accSubst)
       \<and> list_all2 (\<lambda>actualTy expectedTy.
           types_equal (apply_subst finalSubst' actualTy) (apply_subst finalSubst' expectedTy)
           \<or> (is_finite_integer_type (apply_subst finalSubst' actualTy)
              \<and> is_finite_integer_type (apply_subst finalSubst' expectedTy)))
         actualTys expectedTys"
    using unify_call_types_correct[OF phase1 assms(2) assms(4) assms(7) assms(8) assms(5) assms(9) assms(10) assms(6)]
    by simp

  \<comment> \<open>Apply phase 2 correctness\<close>
  have phase2_correct: "list_all2 (\<lambda>tm expectedTy.
           \<exists>ty. bab_term_type env ghost tm = Some ty \<and>
                types_equal ty (apply_subst finalSubst' expectedTy))
         (apply_call_coercions finalSubst' tms actualTys expectedTys) expectedTys"
    using apply_call_coercions_correct[OF assms(3) assms(2) len_tms assms(4)] phase1_correct by simp

  show ?thesis using phase1_correct phase2_correct finalTms_def finalSubst_eq by simp
qed


(* elab_term_list preserves list length: the output lists have the same length as the input *)
lemma elab_term_list_preserves_length:
  "elab_term_list fuel typedefs env ghost tms next_mv = Inr (newTms, tys, next_mv')
   \<Longrightarrow> length newTms = length tms \<and> length tys = length tms"
proof (induction fuel arbitrary: tms newTms tys next_mv next_mv')
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases tms)
    case Nil
    with Suc.prems show ?thesis by simp
  next
    case (Cons tm tms')
    from Suc.prems Cons obtain tm' ty' next_mv1 where
      elab_head: "elab_term fuel typedefs env ghost tm next_mv = Inr (tm', ty', next_mv1)"
      by (auto split: sum.splits)
    from Suc.prems Cons elab_head obtain tms'' tys' next_mv2 where
      elab_tail: "elab_term_list fuel typedefs env ghost tms' next_mv1 = Inr (tms'', tys', next_mv2)"
      and result: "newTms = tm' # tms''" "tys = ty' # tys'" "next_mv' = next_mv2"
      by (auto split: sum.splits)
    from Suc.IH[OF elab_tail] have "length tms'' = length tms'" "length tys' = length tms'"
      by auto
    with Cons result show ?thesis by simp
  qed
qed


(* Simultaneous correctness theorem for elab_term and elab_term_list.
   If elaboration succeeds, the resulting term(s) have the claimed type(s). *)
theorem elab_term_correct:
  "\<forall>env ghost tm newTm ty next_mv next_mv'.
   elab_term fuel typedefs env ghost tm next_mv = Inr (newTm, ty, next_mv') \<longrightarrow>
   tyenv_well_formed env \<longrightarrow>
   bab_term_type env ghost newTm = Some ty"
and elab_term_list_correct:
  "\<forall>env ghost tms newTms tys next_mv next_mv'.
   elab_term_list fuel typedefs env ghost tms next_mv = Inr (newTms, tys, next_mv') \<longrightarrow>
   tyenv_well_formed env \<longrightarrow>
   list_all2 (\<lambda>tm ty. bab_term_type env ghost tm = Some ty) newTms tys"
proof (induction fuel)
  case 0
  { case 1 show ?case by simp
  next
    case 2 show ?case by simp }
next
  case (Suc fuel)
  { case 1 show ?case
    proof (intro allI impI)
      fix env ghost tm newTm ty next_mv next_mv'
      assume elab: "elab_term (Suc fuel) typedefs env ghost tm next_mv = Inr (newTm, ty, next_mv')"
      assume wf: "tyenv_well_formed env"
      show "bab_term_type env ghost newTm = Some ty"
      proof (cases tm)
    case (BabTm_Literal loc lit)
    then show ?thesis
    proof (cases lit)
      case (BabLit_Bool b)
      thus ?thesis using BabTm_Literal elab wf by auto
    next
      case (BabLit_Int i)
      thus ?thesis using BabTm_Literal elab wf by (cases "get_type_for_int i"; auto)
    next
      case (BabLit_String str)
      then show ?thesis sorry
    next
      case (BabLit_Array arr)
      then show ?thesis sorry
    qed

  next
    case (BabTm_Name loc name tyArgs)
    show ?thesis
    proof (cases "fmlookup (TE_TermVars env) name")
      case (Some varTy)
      \<comment> \<open>Term variable case\<close>
      from elab wf BabTm_Name Some
      have tyArgs_empty: "tyArgs = []"
        and ghost_ok: "ghost = NotGhost \<longrightarrow> name |\<notin>| TE_GhostVars env"
        and results: "newTm = tm" "ty = varTy"
        by (auto split: if_splits)
      show ?thesis using Some tyArgs_empty ghost_ok results BabTm_Name by auto
    next
      case None
      \<comment> \<open>Not a variable: must be a data constructor\<close>
      show ?thesis
      proof (cases "fmlookup (TE_DataCtors env) name")
        case None2: None
        \<comment> \<open>Unknown name - elaboration would fail\<close>
        from elab wf BabTm_Name None None2 show ?thesis by (auto split: if_splits)
      next
        case (Some ctorInfo)
        obtain dtName numTyArgs payload where ctor: "ctorInfo = (dtName, numTyArgs, payload)"
          by (cases ctorInfo) auto
        from elab wf BabTm_Name None Some ctor
        have payload_none: "payload = None"
          by (auto split: if_splits sum.splits simp: Let_def)
        show ?thesis
        proof (cases "tyArgs = [] \<and> numTyArgs > 0")
          case True
          \<comment> \<open>User omitted type args: generate metavariables\<close>
          let ?actualTyArgs = "map BabTy_Meta [next_mv..<next_mv + numTyArgs]"
          from elab wf BabTm_Name None Some ctor payload_none True
          have results: "newTm = BabTm_Name loc name ?actualTyArgs" "ty = BabTy_Name loc dtName ?actualTyArgs"
            by (auto split: if_splits simp: Let_def)
          have len_ok: "length ?actualTyArgs = numTyArgs" by simp
          have runtime_ok: "ghost = NotGhost \<longrightarrow> list_all is_runtime_type ?actualTyArgs"
            by (simp add: list_all_iff)
          have wk_ok: "list_all (is_well_kinded env) ?actualTyArgs"
            using list_all_is_well_kinded_meta by simp
          show ?thesis using None Some ctor payload_none len_ok runtime_ok wk_ok results by auto
        next
          case False
          \<comment> \<open>User provided type args: use elab_type_list\<close>
          from elab wf BabTm_Name None Some ctor payload_none False
          obtain resolvedTyArgs where
            elab_ok: "elab_type_list fuel typedefs env ghost tyArgs = Inr resolvedTyArgs"
            and len_ok: "length resolvedTyArgs = numTyArgs"
            and results: "newTm = BabTm_Name loc name resolvedTyArgs" "ty = BabTy_Name loc dtName resolvedTyArgs"
            by (auto split: if_splits sum.splits simp: Let_def)
          \<comment> \<open>Use correctness lemmas from ElabTypeCorrect\<close>
          have runtime_ok: "ghost = NotGhost \<longrightarrow> list_all is_runtime_type resolvedTyArgs"
            using elab_ok elab_type_is_runtime(2) by (cases ghost; auto)
          have wk_ok: "list_all (is_well_kinded env) resolvedTyArgs"
            using elab_ok elab_type_is_well_kinded(2) by auto
          show ?thesis using None Some ctor payload_none len_ok runtime_ok wk_ok results by auto
        qed
      qed
    qed

  next
    case (BabTm_Cast loc targetTy operand)
    \<comment> \<open>Extract info from elaborator success - now uses elab_type\<close>
    from elab wf BabTm_Cast obtain resolvedTargetTy newOperand operandTy next_mv1 where
      elab_target: "elab_type fuel typedefs env ghost targetTy = Inr resolvedTargetTy"
      and elab_operand: "elab_term fuel typedefs env ghost operand next_mv = Inr (newOperand, operandTy, next_mv1)"
      and target_is_int: "is_integer_type resolvedTargetTy"
      and result_ty: "ty = resolvedTargetTy"
      by (auto split: sum.splits if_splits BabType.splits)
    \<comment> \<open>Use correctness lemmas from ElabTypeCorrect\<close>
    have runtime_ok: "ghost = NotGhost \<longrightarrow> is_runtime_type resolvedTargetTy"
      using elab_target elab_type_is_runtime(1) by (cases ghost; auto)
    have wk_ok: "is_well_kinded env resolvedTargetTy"
      using elab_target elab_type_is_well_kinded(1) by auto
    \<comment> \<open>By IH, the elaborated operand typechecks\<close>
    have ih: "bab_term_type env ghost newOperand = Some operandTy"
      using Suc(1) elab_operand wf by blast
    \<comment> \<open>Case split on whether operandTy is a metavariable\<close>
    show ?thesis
    proof (cases "\<exists>n. operandTy = BabTy_Meta n")
      case True
      \<comment> \<open>Metavariable case: cast is eliminated, substitution is applied\<close>
      then obtain n where meta: "operandTy = BabTy_Meta n" by auto
      from elab wf BabTm_Cast elab_target elab_operand target_is_int meta
      have result_tm: "newTm = apply_subst_to_term (singleton_subst n resolvedTargetTy) newOperand"
        by (auto split: sum.splits if_splits)
      \<comment> \<open>Use apply_subst_to_term_preserves_typing\<close>
      have subst_wk: "\<forall>ty' \<in> fmran' (singleton_subst n resolvedTargetTy). is_well_kinded env ty'"
        using wk_ok by (simp add: fmran'_singleton_subst)
      have subst_range: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' (singleton_subst n resolvedTargetTy). is_runtime_type ty')"
        using runtime_ok by (simp add: fmran'_singleton_subst)
      have "bab_term_type env ghost (apply_subst_to_term (singleton_subst n resolvedTargetTy) newOperand)
            = Some (apply_subst (singleton_subst n resolvedTargetTy) operandTy)"
        using ih apply_subst_to_term_preserves_typing wf subst_wk subst_range by blast
      also have "apply_subst (singleton_subst n resolvedTargetTy) operandTy = resolvedTargetTy"
        using meta apply_subst_singleton by auto
      finally show ?thesis using result_tm result_ty by simp
    next
      case False
      \<comment> \<open>Non-metavariable case: regular cast\<close>
      have operand_is_int: "is_integer_type operandTy"
        using elab wf BabTm_Cast elab_target elab_operand False
        by (cases operandTy; auto split: sum.splits if_splits)
      have result_tm: "newTm = BabTm_Cast loc resolvedTargetTy newOperand"
        using elab wf BabTm_Cast elab_target elab_operand False
        by (cases operandTy; auto split: sum.splits if_splits)
      show ?thesis
        using ih operand_is_int target_is_int runtime_ok result_tm result_ty by auto
    qed

  next
    case (BabTm_If loc cond thenTm elseTm)
    \<comment> \<open>Extract the elaboration results for all three subterms\<close>
    from elab wf BabTm_If obtain newCond condTy next_mv1 newThen thenTy next_mv2 newElse elseTy next_mv3 where
      elab_cond: "elab_term fuel typedefs env ghost cond next_mv = Inr (newCond, condTy, next_mv1)"
      and elab_then: "elab_term fuel typedefs env ghost thenTm next_mv1 = Inr (newThen, thenTy, next_mv2)"
      and elab_else: "elab_term fuel typedefs env ghost elseTm next_mv2 = Inr (newElse, elseTy, next_mv3)"
      by (auto split: sum.splits option.splits if_splits BabType.splits)
    \<comment> \<open>By IH, all three elaborated subterms typecheck\<close>
    have ih_cond: "bab_term_type env ghost newCond = Some condTy"
      using Suc(1) elab_cond wf by blast
    have ih_then: "bab_term_type env ghost newThen = Some thenTy"
      using Suc(1) elab_then wf by blast
    have ih_else: "bab_term_type env ghost newElse = Some elseTy"
      using Suc(1) elab_else wf by blast

    \<comment> \<open>Determine the final condition and its type after potential specialization\<close>
    define finalCond finalCondTy where
      "finalCond = (case condTy of BabTy_Meta n \<Rightarrow> apply_subst_to_term (singleton_subst n (BabTy_Bool loc)) newCond | _ \<Rightarrow> newCond)"
      and "finalCondTy = (case condTy of BabTy_Meta n \<Rightarrow> BabTy_Bool loc | _ \<Rightarrow> condTy)"

    \<comment> \<open>Show finalCond typechecks to finalCondTy\<close>
    have final_cond_typed: "bab_term_type env ghost finalCond = Some finalCondTy"
    proof (cases "\<exists>n. condTy = BabTy_Meta n")
      case True
      then obtain n where meta: "condTy = BabTy_Meta n" by auto
      have subst_wk: "\<forall>ty' \<in> fmran' (singleton_subst n (BabTy_Bool loc)). is_well_kinded env ty'"
        by (simp add: fmran'_singleton_subst)
      have subst_range: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' (singleton_subst n (BabTy_Bool loc)). is_runtime_type ty')"
        by (simp add: fmran'_singleton_subst)
      have "bab_term_type env ghost (apply_subst_to_term (singleton_subst n (BabTy_Bool loc)) newCond)
            = Some (apply_subst (singleton_subst n (BabTy_Bool loc)) condTy)"
        using ih_cond apply_subst_to_term_preserves_typing wf subst_wk subst_range by blast
      also have "apply_subst (singleton_subst n (BabTy_Bool loc)) condTy = BabTy_Bool loc"
        using meta apply_subst_singleton by auto
      finally show ?thesis using meta finalCond_def finalCondTy_def by simp
    next
      case False
      then show ?thesis using ih_cond finalCond_def finalCondTy_def by (cases condTy; simp)
    qed

    \<comment> \<open>The elaborator checks that finalCondTy is Bool\<close>
    from elab wf BabTm_If elab_cond elab_then elab_else
    obtain cond_loc where finalCondTy_is_Bool: "finalCondTy = BabTy_Bool cond_loc"
      by (auto split: sum.splits option.splits BabType.splits simp: finalCondTy_def Let_def)

    \<comment> \<open>Now handle the two cases: unification succeeds, or coercion is used\<close>
    show ?thesis
    proof (cases "unify thenTy elseTy")
      case (Some branchSubst)
      \<comment> \<open>Unification succeeded\<close>
      from elab wf BabTm_If elab_cond elab_then elab_else Some
      have result_tm: "newTm = BabTm_If loc finalCond
                                 (apply_subst_to_term branchSubst newThen)
                                 (apply_subst_to_term branchSubst newElse)"
        and result_ty: "ty = apply_subst branchSubst thenTy"
        by (auto split: sum.splits option.splits BabType.splits simp: finalCond_def Let_def)

      \<comment> \<open>From unify_sound, the substituted types are equal\<close>
      from unify_sound[OF Some]
      have types_eq: "types_equal (apply_subst branchSubst thenTy) (apply_subst branchSubst elseTy)" .

      \<comment> \<open>Show the substituted branches typecheck\<close>
      \<comment> \<open>First establish that thenTy and elseTy are runtime and well-kinded\<close>
      have thenTy_runtime: "ghost = NotGhost \<longrightarrow> is_runtime_type thenTy"
        using ih_then bab_term_type_runtime_invariant wf by fastforce
      have elseTy_runtime: "ghost = NotGhost \<longrightarrow> is_runtime_type elseTy"
        using ih_else bab_term_type_runtime_invariant wf by fastforce
      have thenTy_wk: "is_well_kinded env thenTy"
        using ih_then bab_term_type_well_kinded wf by fastforce
      have elseTy_wk: "is_well_kinded env elseTy"
        using ih_else bab_term_type_well_kinded wf by fastforce
      have subst_wk: "\<forall>ty' \<in> fmran' branchSubst. is_well_kinded env ty'"
        using Some thenTy_wk elseTy_wk unify_preserves_well_kinded by blast
      have subst_range: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' branchSubst. is_runtime_type ty')"
        using Some thenTy_runtime elseTy_runtime unify_preserves_runtime by blast
      have then_typed: "bab_term_type env ghost (apply_subst_to_term branchSubst newThen)
                        = Some (apply_subst branchSubst thenTy)"
        using ih_then apply_subst_to_term_preserves_typing wf subst_wk subst_range by blast
      have else_typed: "bab_term_type env ghost (apply_subst_to_term branchSubst newElse)
                        = Some (apply_subst branchSubst elseTy)"
        using ih_else apply_subst_to_term_preserves_typing wf subst_wk subst_range by blast

      show ?thesis
        using final_cond_typed finalCondTy_is_Bool then_typed else_typed types_eq result_tm result_ty
        by (simp del: types_equal.simps)
    next
      case None
      \<comment> \<open>Unification failed - try integer coercion\<close>
      from elab wf BabTm_If elab_cond elab_then elab_else None
      obtain finalThen finalElse commonTy where
        coerce_ok: "coerce_to_common_int_type newThen thenTy newElse elseTy = Some (finalThen, finalElse, commonTy)"
        and result_tm: "newTm = BabTm_If loc finalCond finalThen finalElse"
        and result_ty: "ty = commonTy"
        by (auto split: sum.splits option.splits BabType.splits simp: finalCond_def Let_def)

      \<comment> \<open>Analyze coerce_to_common_int_type\<close>
      from coerce_ok obtain loc1 sign1 bits1 loc2 sign2 bits2 commonSign commonBits where
        thenTy_int: "thenTy = BabTy_FiniteInt loc1 sign1 bits1"
        and elseTy_int: "elseTy = BabTy_FiniteInt loc2 sign2 bits2"
        and combine_ok: "combine_int_types sign1 bits1 sign2 bits2 = Some (commonSign, commonBits)"
        and commonTy_def: "commonTy = BabTy_FiniteInt loc1 commonSign commonBits"
        by (cases thenTy; cases elseTy; auto split: option.splits simp: Let_def)

      \<comment> \<open>Determine what finalThen and finalElse are\<close>
      define thenNeedsCast elseNeedsCast where
        "thenNeedsCast = (sign1 \<noteq> commonSign \<or> bits1 \<noteq> commonBits)"
        and "elseNeedsCast = (sign2 \<noteq> commonSign \<or> bits2 \<noteq> commonBits)"

      from coerce_ok thenTy_int elseTy_int combine_ok
      have finalThen_def: "finalThen = (if thenNeedsCast
                             then BabTm_Cast (bab_term_location newThen) (BabTy_FiniteInt loc1 commonSign commonBits) newThen
                             else newThen)"
        and finalElse_def: "finalElse = (if elseNeedsCast
                              then BabTm_Cast (bab_term_location newElse) (BabTy_FiniteInt loc2 commonSign commonBits) newElse
                              else newElse)"
        by (auto simp: Let_def thenNeedsCast_def elseNeedsCast_def)

      \<comment> \<open>Show finalThen typechecks to commonTy (or a types_equal type)\<close>
      have thenTy_is_int: "is_integer_type thenTy" using thenTy_int by simp
      have elseTy_is_int: "is_integer_type elseTy" using elseTy_int by simp
      have commonTy_is_int: "is_integer_type commonTy" using commonTy_def by simp
      have commonTy_runtime: "is_runtime_type commonTy" using commonTy_def by simp

      have finalThen_typed: "bab_term_type env ghost finalThen = Some commonTy"
      proof (cases thenNeedsCast)
        case True
        hence "finalThen = BabTm_Cast (bab_term_location newThen) (BabTy_FiniteInt loc1 commonSign commonBits) newThen"
          using finalThen_def by simp
        moreover have "bab_term_type env ghost (BabTm_Cast (bab_term_location newThen) commonTy newThen) = Some commonTy"
          using ih_then thenTy_is_int commonTy_is_int commonTy_runtime commonTy_def by auto
        ultimately show ?thesis using commonTy_def by simp
      next
        case False
        hence "sign1 = commonSign" "bits1 = commonBits" using thenNeedsCast_def by auto
        hence "thenTy = commonTy" using thenTy_int commonTy_def by simp
        moreover have "finalThen = newThen" using False finalThen_def by simp
        ultimately show ?thesis using ih_then by simp
      qed

      have finalElse_typed: "bab_term_type env ghost finalElse = Some (BabTy_FiniteInt loc2 commonSign commonBits)"
      proof (cases elseNeedsCast)
        case True
        hence "finalElse = BabTm_Cast (bab_term_location newElse) (BabTy_FiniteInt loc2 commonSign commonBits) newElse"
          using finalElse_def by simp
        moreover have "bab_term_type env ghost (BabTm_Cast (bab_term_location newElse) (BabTy_FiniteInt loc2 commonSign commonBits) newElse)
                       = Some (BabTy_FiniteInt loc2 commonSign commonBits)"
          using ih_else elseTy_is_int commonTy_is_int commonTy_runtime commonTy_def by auto
        ultimately show ?thesis by simp
      next
        case False
        hence "sign2 = commonSign" "bits2 = commonBits" using elseNeedsCast_def by auto
        hence "elseTy = BabTy_FiniteInt loc2 commonSign commonBits" using elseTy_int by simp
        moreover have "finalElse = newElse" using False finalElse_def by simp
        ultimately show ?thesis using ih_else by simp
      qed

      \<comment> \<open>The two branch types are types_equal\<close>
      have branches_eq: "types_equal commonTy (BabTy_FiniteInt loc2 commonSign commonBits)"
        using commonTy_def by simp

      show ?thesis
        using final_cond_typed finalCondTy_is_Bool finalThen_typed finalElse_typed branches_eq result_tm result_ty
        by (simp del: types_equal.simps)
    qed

  next
    case (BabTm_Unop loc op operand)
    \<comment> \<open>Extract common info from elaborator success\<close>
    from elab wf BabTm_Unop obtain newOperand operandTy next_mv1 where
      elab_operand: "elab_term fuel typedefs env ghost operand next_mv = Inr (newOperand, operandTy, next_mv1)"
      by (auto split: sum.splits)
    \<comment> \<open>By IH, the elaborated operand typechecks\<close>
    have ih: "bab_term_type env ghost newOperand = Some operandTy"
      using Suc(1) elab_operand wf by blast
    \<comment> \<open>Case split on whether operandTy is a metavariable\<close>
    show ?thesis
    proof (cases "\<exists>n. operandTy = BabTy_Meta n")
      case True
      \<comment> \<open>Metavariable case: operand is specialized to default type\<close>
      then obtain n where meta: "operandTy = BabTy_Meta n" by auto
      let ?defaultTy = "default_type_for_unop loc op"
      let ?specializedOperand = "apply_subst_to_term (singleton_subst n ?defaultTy) newOperand"
      from elab wf BabTm_Unop elab_operand meta
      have result_tm: "newTm = BabTm_Unop loc op ?specializedOperand"
        and result_ty: "ty = ?defaultTy"
        by (auto split: sum.splits simp: Let_def)
      \<comment> \<open>Use apply_subst_to_term_preserves_typing\<close>
      have subst_wk: "\<forall>ty' \<in> fmran' (singleton_subst n ?defaultTy). is_well_kinded env ty'"
        using default_type_for_unop_is_well_kinded by (simp add: fmran'_singleton_subst)
      have subst_range: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' (singleton_subst n ?defaultTy). is_runtime_type ty')"
        using default_type_for_unop_is_runtime by (simp add: fmran'_singleton_subst)
      have "bab_term_type env ghost ?specializedOperand
            = Some (apply_subst (singleton_subst n ?defaultTy) operandTy)"
        using ih apply_subst_to_term_preserves_typing wf subst_wk subst_range by blast
      also have "apply_subst (singleton_subst n ?defaultTy) operandTy = ?defaultTy"
        using meta apply_subst_singleton by auto
      finally have specialized_typed: "bab_term_type env ghost ?specializedOperand = Some ?defaultTy" .
      \<comment> \<open>Show the unop typechecks based on default_type_for_unop\<close>
      show ?thesis
        using specialized_typed result_tm result_ty
        by (cases op; auto)
    next
      case False
      \<comment> \<open>Non-metavariable case: regular unop checking\<close>
      from elab wf BabTm_Unop elab_operand False
      have result_tm: "newTm = BabTm_Unop loc op newOperand"
        and result_ty: "ty = operandTy"
        and type_ok: "(op = BabUnop_Negate \<longrightarrow> is_signed_integer_type operandTy)
                    \<and> (op = BabUnop_Complement \<longrightarrow> is_finite_integer_type operandTy)
                    \<and> (op = BabUnop_Not \<longrightarrow> (\<exists>bloc. operandTy = BabTy_Bool bloc))"
        by (cases operandTy; auto split: sum.splits BabUnop.splits if_splits BabType.splits)+
      show ?thesis
        using ih type_ok result_tm result_ty
        by (auto split: BabUnop.splits BabType.splits)
    qed

  next
    case (BabTm_Binop x61 x62 x63)
    then show ?thesis sorry
  next
    case (BabTm_Let x71 x72 x73 x74)
    then show ?thesis sorry
  next
    case (BabTm_Quantifier x81 x82 x83 x84 x85)
    then show ?thesis sorry

  next
    case (BabTm_Call loc callTm argTms)
    \<comment> \<open>Extract the result from determine_fun_call_type\<close>
    from elab wf BabTm_Call obtain newCallTm expArgTypes retType fnName next_mv1 where
      det_call: "determine_fun_call_type fuel typedefs env ghost callTm next_mv
                 = Inr (newCallTm, expArgTypes, retType, fnName, next_mv1)"
      by (auto split: sum.splits)

    \<comment> \<open>Check argument count\<close>
    from elab wf BabTm_Call det_call
    have arg_count: "length argTms = length expArgTypes"
      by (auto split: sum.splits if_splits)

    \<comment> \<open>Extract the result from elab_term_list\<close>
    from elab wf BabTm_Call det_call arg_count obtain elabArgTms actualTypes next_mv2 where
      elab_args: "elab_term_list fuel typedefs env ghost argTms next_mv1
                  = Inr (elabArgTms, actualTypes, next_mv2)"
      by (auto split: sum.splits if_splits)

    \<comment> \<open>Extract the result from unify_call_args\<close>
    from elab wf BabTm_Call det_call arg_count elab_args obtain finalArgTms finalSubst where
      unify_args: "unify_call_args loc fnName 0 elabArgTms actualTypes expArgTypes fmempty
                   = Inr (finalArgTms, finalSubst)"
      and result_tm: "newTm = BabTm_Call loc (apply_subst_to_term finalSubst newCallTm) finalArgTms"
      and result_ty: "ty = apply_subst finalSubst retType"
      by (auto split: sum.splits if_splits simp: Let_def empty_subst_def)

    \<comment> \<open>By IH on elab_term_list, elaborated args typecheck\<close>
    have ih_args: "list_all2 (\<lambda>tm ty. bab_term_type env ghost tm = Some ty) elabArgTms actualTypes"
      using Suc(2) elab_args wf by blast

    \<comment> \<open>Get length equalities\<close>
    have len_elab_actual: "length elabArgTms = length actualTypes"
      using ih_args by (simp add: list_all2_lengthD)
    \<comment> \<open>elab_term_list preserves list length\<close>
    from elab_term_list_preserves_length[OF elab_args]
    have len_argTms_elab: "length elabArgTms = length argTms"
      and len_actualTypes_argTms: "length actualTypes = length argTms"
      by auto
    have len_actual_exp: "length actualTypes = length expArgTypes"
      using arg_count len_actualTypes_argTms by simp

    \<comment> \<open>Get properties from determine_fun_call_type_correct\<close>
    from determine_fun_call_type_correct[OF det_call wf]
    obtain fnLoc newTyArgs funDecl retTyDecl where
      call_tm_form: "newCallTm = BabTm_Name fnLoc fnName newTyArgs"
      and fn_lookup: "fmlookup (TE_Functions env) fnName = Some funDecl"
      and not_impure: "\<not> DF_Impure funDecl"
      and no_ref_args: "\<not> list_ex (\<lambda>(_, vr, _). vr = Ref) (DF_TmArgs funDecl)"
      and ghost_ok: "ghost = NotGhost \<longrightarrow> DF_Ghost funDecl \<noteq> Ghost"
      and ret_ty_decl: "DF_ReturnType funDecl = Some retTyDecl"
      and tyargs_len: "length newTyArgs = length (DF_TyArgs funDecl)"
      and tyargs_wk: "list_all (is_well_kinded env) newTyArgs"
      and tyargs_rt: "ghost = NotGhost \<longrightarrow> list_all is_runtime_type newTyArgs"
      and exp_arg_types_def: "expArgTypes = map (\<lambda>(_, _, ty). substitute_bab_type
                               (fmap_of_list (zip (DF_TyArgs funDecl) newTyArgs)) ty)
                              (DF_TmArgs funDecl)"
      and ret_type_def: "retType = substitute_bab_type
                          (fmap_of_list (zip (DF_TyArgs funDecl) newTyArgs)) retTyDecl"
      by blast

    \<comment> \<open>Establish well-kindedness and runtime properties for actualTypes and expArgTypes\<close>
    have actualTypes_wk: "list_all (is_well_kinded env) actualTypes"
      using ih_args bab_term_type_well_kinded wf
      by (induction elabArgTms actualTypes rule: list_all2_induct) auto
    have actualTypes_rt: "ghost = NotGhost \<longrightarrow> list_all is_runtime_type actualTypes"
      using ih_args bab_term_type_runtime_invariant wf
      by (induction elabArgTms actualTypes rule: list_all2_induct) auto

    \<comment> \<open>From tyenv_well_formed, get that function arg types are well-kinded and runtime\<close>
    let ?tySubst = "fmap_of_list (zip (DF_TyArgs funDecl) newTyArgs)"
    let ?extEnv = "env_with_tyvars env (DF_TyArgs funDecl)"

    from wf fn_lookup have fn_wf: "tyenv_functions_well_formed env"
      unfolding tyenv_well_formed_def by simp
    have arg_types_ground_wk: "list_all (\<lambda>(_, _, ty). is_ground ty \<and> is_well_kinded ?extEnv ty) (DF_TmArgs funDecl)"
      by (metis (lifting) fn_lookup fn_wf tyenv_functions_well_formed_def)
    have ret_type_ground_wk: "is_ground retTyDecl \<and> is_well_kinded ?extEnv retTyDecl"
      by (metis (lifting) fn_lookup fn_wf option.simps(5) ret_ty_decl
          tyenv_functions_well_formed_def)
    have arg_types_rt_raw: "DF_Ghost funDecl = NotGhost \<longrightarrow>
                             list_all (\<lambda>(_, _, ty). is_runtime_type ty) (DF_TmArgs funDecl)"
      by (metis (lifting) fn_lookup fn_wf tyenv_functions_well_formed_def)
    from arg_types_ground_wk have arg_types_ground: "list_all (\<lambda>(_, _, ty). is_ground ty) (DF_TmArgs funDecl)"
      by (auto simp: list_all_iff)
    from arg_types_ground_wk have arg_types_wk_ext: "list_all (\<lambda>(_, _, ty). is_well_kinded ?extEnv ty) (DF_TmArgs funDecl)"
      by (auto simp: list_all_iff)
    from ret_type_ground_wk have ret_type_ground: "is_ground retTyDecl" by simp

    \<comment> \<open>Build the substitution properties\<close>
    have tySubst_wk: "subst_types_well_kinded env ?tySubst"
      using tyargs_wk by (rule subst_types_well_kinded_from_zip)

    have tySubst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' ?tySubst. is_runtime_type ty')"
    proof (intro impI ballI)
      fix ty' assume ng: "ghost = NotGhost" and "ty' \<in> fmran' ?tySubst"
      from \<open>ty' \<in> fmran' ?tySubst\<close> obtain name where "fmlookup ?tySubst name = Some ty'"
        by (auto simp: fmran'I)
      then have "(name, ty') \<in> set (zip (DF_TyArgs funDecl) newTyArgs)"
        by (metis fmap_of_list.rep_eq map_of_SomeD)
      then have "ty' \<in> set newTyArgs"
        by (meson set_zip_rightD)
      with tyargs_rt ng show "is_runtime_type ty'"
        by (simp add: list_all_iff)
    qed

    \<comment> \<open>Get the disjointness condition from tyenv_functions_well_formed\<close>
    have tyvars_disjoint: "fset_of_list (DF_TyArgs funDecl) |\<inter>| fmdom (TE_Datatypes env) = {||}"
      by (metis (lifting) fn_lookup fn_wf tyenv_functions_well_formed_def)

    \<comment> \<open>Show that tySubst covers all type variables\<close>
    have tyvars_covered: "fset_of_list (DF_TyArgs funDecl) |\<subseteq>| fmdom ?tySubst"
    proof -
      have "fmdom ?tySubst = fset_of_list (map fst (zip (DF_TyArgs funDecl) newTyArgs))"
        by simp
      also have "... = fset_of_list (take (length newTyArgs) (DF_TyArgs funDecl))"
        by (simp add: tyargs_len)
      also have "... = fset_of_list (DF_TyArgs funDecl)"
        using tyargs_len by simp
      finally show ?thesis by simp
    qed

    have expArgTypes_wk: "list_all (is_well_kinded env) expArgTypes"
      unfolding exp_arg_types_def list_all_iff
    proof (intro ballI)
      fix ty assume "ty \<in> set (map (\<lambda>(_, _, ty). substitute_bab_type ?tySubst ty) (DF_TmArgs funDecl))"
      then obtain arg where arg_in: "arg \<in> set (DF_TmArgs funDecl)"
        and ty_eq: "ty = (\<lambda>(_, _, ty). substitute_bab_type ?tySubst ty) arg" by auto
      obtain nm vr argTy where arg_eq: "arg = (nm, vr, argTy)" by (cases arg)
      with arg_in arg_types_wk_ext have "is_well_kinded ?extEnv argTy"
        by (auto simp: list_all_iff)
      moreover have "?extEnv = env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list (DF_TyArgs funDecl) \<rparr>"
        unfolding env_with_tyvars_def by simp
      ultimately have "is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list (DF_TyArgs funDecl) \<rparr>) argTy"
        by simp
      from is_well_kinded_substitute_across_ext[OF this tyvars_disjoint tyvars_covered tySubst_wk]
      show "is_well_kinded env ty" using arg_eq ty_eq by simp
    qed
    have expArgTypes_rt: "ghost = NotGhost \<longrightarrow> list_all is_runtime_type expArgTypes"
    proof (intro impI)
      assume ng: "ghost = NotGhost"
      \<comment> \<open>Since ghost = NotGhost and ghost_ok says function is not ghost when NotGhost\<close>
      from ng ghost_ok have "DF_Ghost funDecl \<noteq> Ghost" by simp
      hence fn_not_ghost: "DF_Ghost funDecl = NotGhost" by (cases "DF_Ghost funDecl"; simp)
      with arg_types_rt_raw have args_rt: "list_all (\<lambda>(_, _, ty). is_runtime_type ty) (DF_TmArgs funDecl)"
        by simp
      from ng tySubst_rt have subst_rt: "\<forall>ty' \<in> fmran' ?tySubst. is_runtime_type ty'" by simp
      show "list_all is_runtime_type expArgTypes"
        unfolding exp_arg_types_def list_all_iff
      proof (intro ballI)
        fix ty assume "ty \<in> set (map (\<lambda>(_, _, ty). substitute_bab_type ?tySubst ty) (DF_TmArgs funDecl))"
        then obtain arg where arg_in: "arg \<in> set (DF_TmArgs funDecl)"
          and ty_eq: "ty = (\<lambda>(_, _, ty). substitute_bab_type ?tySubst ty) arg" by auto
        obtain nm vr argTy where arg_eq: "arg = (nm, vr, argTy)" by (cases arg)
        with arg_in args_rt have "is_runtime_type argTy"
          by (auto simp: list_all_iff)
        with subst_rt show "is_runtime_type ty"
          using arg_eq ty_eq is_runtime_type_substitute_bab_type by auto
      qed
    qed

    \<comment> \<open>Empty substitution is trivially well-kinded and runtime\<close>
    have empty_wk: "\<forall>ty \<in> fmran' fmempty. is_well_kinded env ty" by auto
    have empty_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' fmempty. is_runtime_type ty)" by auto

    \<comment> \<open>Apply unify_call_args_correct\<close>
    have unify_correct: "list_all2 (\<lambda>tm expectedTy.
           \<exists>ty. bab_term_type env ghost tm = Some ty \<and>
                types_equal ty (apply_subst finalSubst expectedTy))
         finalArgTms expArgTypes
       \<and> (\<forall>ty \<in> fmran' finalSubst. is_well_kinded env ty)
       \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type ty))"
      using unify_call_args_correct[OF unify_args wf ih_args len_actual_exp empty_wk empty_rt
                                       actualTypes_wk expArgTypes_wk actualTypes_rt expArgTypes_rt]
      by simp

    have finalSubst_wk: "\<forall>ty \<in> fmran' finalSubst. is_well_kinded env ty"
      using unify_correct by blast
    have finalSubst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type ty)"
      using unify_correct by blast
    have args_typed: "list_all2 (\<lambda>tm expectedTy.
           \<exists>ty. bab_term_type env ghost tm = Some ty \<and>
                types_equal ty (apply_subst finalSubst expectedTy))
         finalArgTms expArgTypes"
      using unify_correct by blast

    \<comment> \<open>Show the final call term typechecks\<close>
    \<comment> \<open>First, establish the form of the final call term\<close>
    let ?finalTyArgs = "map (apply_subst finalSubst) newTyArgs"
    have final_call_tm: "apply_subst_to_term finalSubst newCallTm = BabTm_Name fnLoc fnName ?finalTyArgs"
      using call_tm_form by simp

    \<comment> \<open>Show the final type args are well-kinded\<close>
    have finalTyArgs_wk: "list_all (is_well_kinded env) ?finalTyArgs"
    proof -
      have "\<forall>ty \<in> set newTyArgs. is_well_kinded env (apply_subst finalSubst ty)"
      proof
        fix ty assume "ty \<in> set newTyArgs"
        with tyargs_wk have "is_well_kinded env ty" by (simp add: list_all_iff)
        thus "is_well_kinded env (apply_subst finalSubst ty)"
          using finalSubst_wk is_well_kinded_apply_subst by blast
      qed
      thus ?thesis by (simp add: list_all_iff)
    qed

    \<comment> \<open>Show the final type args are runtime when needed\<close>
    have finalTyArgs_rt: "ghost = NotGhost \<longrightarrow> list_all is_runtime_type ?finalTyArgs"
    proof (intro impI)
      assume ng: "ghost = NotGhost"
      have "\<forall>ty \<in> set newTyArgs. is_runtime_type (apply_subst finalSubst ty)"
      proof
        fix ty assume "ty \<in> set newTyArgs"
        with tyargs_rt ng have "is_runtime_type ty" by (simp add: list_all_iff)
        moreover from finalSubst_rt ng have "\<forall>ty' \<in> fmran' finalSubst. is_runtime_type ty'" by simp
        ultimately show "is_runtime_type (apply_subst finalSubst ty)"
          using is_runtime_type_apply_subst by blast
      qed
      thus "list_all is_runtime_type ?finalTyArgs" by (simp add: list_all_iff)
    qed

    \<comment> \<open>Length of final type args\<close>
    have finalTyArgs_len: "length ?finalTyArgs = length (DF_TyArgs funDecl)"
      using tyargs_len by simp

    \<comment> \<open>Length of final arg terms\<close>
    have finalArgTms_len: "length finalArgTms = length (DF_TmArgs funDecl)"
    proof -
      have "length finalArgTms = length expArgTypes"
        using args_typed by (simp add: list_all2_lengthD)
      also have "... = length (DF_TmArgs funDecl)"
        using exp_arg_types_def by simp
      finally show ?thesis .
    qed

    \<comment> \<open>Build the type substitution for the final type args\<close>
    let ?finalTySubst = "fmap_of_list (zip (DF_TyArgs funDecl) ?finalTyArgs)"

    \<comment> \<open>Show the expected arg types after final substitution\<close>
    let ?finalExpArgTys = "map (\<lambda>(_, _, ty). substitute_bab_type ?finalTySubst ty) (DF_TmArgs funDecl)"

    \<comment> \<open>Key lemma needed: substitute_bab_type commutes with apply_subst
        substitute_bab_type (fmap_of_list (zip tyVars (map (apply_subst subst) tyArgs))) ty
        = apply_subst subst (substitute_bab_type (fmap_of_list (zip tyVars tyArgs)) ty)\<close>

    \<comment> \<open>Using substitute_bab_type_apply_subst_commute, show finalExpArgTys = map (apply_subst finalSubst) expArgTypes\<close>
    have finalExpArgTys_eq: "?finalExpArgTys = map (apply_subst finalSubst) expArgTypes"
    proof -
      have step1: "?finalExpArgTys = map (\<lambda>(_, _, ty). substitute_bab_type ?finalTySubst ty) (DF_TmArgs funDecl)"
        by simp
      have step2: "map (\<lambda>(_, _, ty). substitute_bab_type ?finalTySubst ty) (DF_TmArgs funDecl)
                 = map (\<lambda>(_, _, ty). apply_subst finalSubst (substitute_bab_type ?tySubst ty)) (DF_TmArgs funDecl)"
      proof (intro map_cong refl)
        fix arg assume "arg \<in> set (DF_TmArgs funDecl)"
        obtain nm vr argTy where arg_eq: "arg = (nm, vr, argTy)" by (cases arg)
        with \<open>arg \<in> set (DF_TmArgs funDecl)\<close> arg_types_ground have "is_ground argTy"
          by (auto simp: list_all_iff)
        thus "(\<lambda>(_, _, ty). substitute_bab_type ?finalTySubst ty) arg
              = (\<lambda>(_, _, ty). apply_subst finalSubst (substitute_bab_type ?tySubst ty)) arg"
          using arg_eq substitute_bab_type_apply_subst_commute by simp
      qed
      have step3: "map (\<lambda>(_, _, ty). apply_subst finalSubst (substitute_bab_type ?tySubst ty)) (DF_TmArgs funDecl)
                 = map (apply_subst finalSubst) (map (\<lambda>(_, _, ty). substitute_bab_type ?tySubst ty) (DF_TmArgs funDecl))"
        by (induction "DF_TmArgs funDecl") auto
      have step4: "map (\<lambda>(_, _, ty). substitute_bab_type ?tySubst ty) (DF_TmArgs funDecl) = expArgTypes"
        using exp_arg_types_def by simp
      show ?thesis using step1 step2 step3 step4 by simp
    qed

    \<comment> \<open>Similarly for the return type\<close>
    have finalRetTy_eq: "substitute_bab_type ?finalTySubst retTyDecl = apply_subst finalSubst retType"
      using ret_type_def ret_type_ground substitute_bab_type_apply_subst_commute by simp

    \<comment> \<open>The key: show arg types match using types_equal\<close>
    have args_match: "list_all2 (\<lambda>actual expected.
                        case actual of None \<Rightarrow> False
                        | Some actualTy \<Rightarrow> types_equal actualTy expected)
                      (map (bab_term_type env ghost) finalArgTms) ?finalExpArgTys"
    proof -
      \<comment> \<open>We know args_typed gives us types_equal to apply_subst finalSubst expArgTypes\<close>
      \<comment> \<open>And finalExpArgTys = map (apply_subst finalSubst) expArgTypes\<close>
      have len_eq: "length finalArgTms = length ?finalExpArgTys"
        using finalArgTms_len exp_arg_types_def by simp
      show ?thesis using args_typed finalExpArgTys_eq
        by (auto simp: list_all2_conv_all_nth)
    qed

    \<comment> \<open>Finally show the result\<close>
    have call_typed: "bab_term_type env ghost (BabTm_Call loc (apply_subst_to_term finalSubst newCallTm) finalArgTms)
          = Some (substitute_bab_type ?finalTySubst retTyDecl)"
      using final_call_tm fn_lookup not_impure no_ref_args ghost_ok ret_ty_decl
            finalTyArgs_len finalTyArgs_wk finalTyArgs_rt finalArgTms_len args_match
      by (auto split: option.splits if_splits)

    show ?thesis
      using result_tm result_ty call_typed finalRetTy_eq by simp
  next
    case (BabTm_Tuple x101 x102)
    then show ?thesis sorry
  next
    case (BabTm_Record x111 x112)
    then show ?thesis sorry
  next
    case (BabTm_RecordUpdate x121 x122 x123)
    then show ?thesis sorry
  next
    case (BabTm_TupleProj x131 x132 x133)
    then show ?thesis sorry
  next
    case (BabTm_RecordProj x141 x142 x143)
    then show ?thesis sorry
  next
    case (BabTm_ArrayProj x151 x152 x153)
    then show ?thesis sorry
  next
    case (BabTm_Match x161 x162 x163)
    then show ?thesis sorry
  next
    case (BabTm_Sizeof x171 x172)
    then show ?thesis sorry
  next
    case (BabTm_Allocated x181 x182)
    then show ?thesis sorry
  next
    case (BabTm_Old x191 x192)
    then show ?thesis sorry
      qed
    qed
  next
    case 2 show ?case
    proof (intro allI impI)
      fix env ghost tms newTms tys next_mv next_mv'
      assume elab: "elab_term_list (Suc fuel) typedefs env ghost tms next_mv = Inr (newTms, tys, next_mv')"
      assume wf: "tyenv_well_formed env"
      show "list_all2 (\<lambda>tm ty. bab_term_type env ghost tm = Some ty) newTms tys"
      proof (cases tms)
        case Nil
        then show ?thesis using elab by simp
      next
        case (Cons tm tms')
        from elab Cons obtain tm' ty' next_mv1 tms'' tys' next_mv'' where
          elab_head: "elab_term fuel typedefs env ghost tm next_mv = Inr (tm', ty', next_mv1)" and
          elab_tail: "elab_term_list fuel typedefs env ghost tms' next_mv1 = Inr (tms'', tys', next_mv'')" and
          results: "newTms = tm' # tms''" "tys = ty' # tys'"
          by (auto split: sum.splits prod.splits)
        \<comment> \<open>Use IH for elab_term (at fuel level fuel) for the head\<close>
        have ih_head: "bab_term_type env ghost tm' = Some ty'"
          using Suc(1) elab_head wf by blast
        \<comment> \<open>Use IH for elab_term_list (at fuel level fuel) for the tail\<close>
        have ih_tail: "list_all2 (\<lambda>tm ty. bab_term_type env ghost tm = Some ty) tms'' tys'"
          using Suc(2) elab_tail wf by blast
        show ?thesis using ih_head ih_tail results by simp
      qed
    qed }
qed


end
