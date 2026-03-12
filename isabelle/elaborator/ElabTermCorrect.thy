theory ElabTermCorrect
  imports ElabTerm ElabTypeCorrect "../core/CoreTypecheck" Unify3
begin

(* Helper: map_of on zipped lists with mapped second component *)
lemma map_of_zip_map:
  assumes "length vars = length tys"
  shows "map_of (zip vars (map f tys)) = map_option f \<circ> map_of (zip vars tys)"
proof
  fix n
  show "map_of (zip vars (map f tys)) n = (map_option f \<circ> map_of (zip vars tys)) n"
    using assms by (induction vars tys rule: list_induct2) auto
qed

lemma fmlookup_zip_map:
  assumes "length vars = length tys"
      and "fmlookup (fmap_of_list (zip vars tys)) n = Some ty"
  shows "fmlookup (fmap_of_list (zip vars (map f tys))) n = Some (f ty)"
  using assms map_of_zip_map[OF assms(1), of f]
  by (simp add: fmlookup_of_list)

lemma fmlookup_zip_map_None:
  assumes "length vars = length tys"
      and "fmlookup (fmap_of_list (zip vars tys)) n = None"
  shows "fmlookup (fmap_of_list (zip vars (map f tys))) n = None"
  using assms map_of_zip_map[OF assms(1), of f]
  by (simp add: fmlookup_of_list)

(* Helper: applying a substitution built from zip with already-substituted types
   is equivalent to composing substitutions.
   Requires that all metavariables in t are in vars (otherwise the s substitution
   would affect t but not the LHS), and that vars is distinct (for map_of to work correctly). *)
lemma apply_subst_compose_zip:
  assumes "length vars = length tys"
      and "type_metavars t \<subseteq> set vars"
      and "distinct vars"
  shows "apply_subst (fmap_of_list (zip vars (map (apply_subst s) tys))) t
       = apply_subst s (apply_subst (fmap_of_list (zip vars tys)) t)"
  using assms
proof (induction t)
  case (CoreTy_Meta n)
  \<comment> \<open>From assumption, n \<in> set vars\<close>
  from CoreTy_Meta.prems(2) have "n \<in> set vars" by simp
  \<comment> \<open>So there exists a unique i with vars ! i = n\<close>
  then obtain i where i_bound: "i < length vars" and vars_i: "vars ! i = n"
    by (metis in_set_conv_nth)
  with CoreTy_Meta.prems(1) have i_bound_tys: "i < length tys" by simp
  \<comment> \<open>The lookup succeeds - use distinctness for map_of_zip_nth\<close>
  have lookup_eq: "fmlookup (fmap_of_list (zip vars tys)) n = Some (tys ! i)"
    using i_bound i_bound_tys vars_i CoreTy_Meta.prems(1,3)
    by (metis fmap_of_list.rep_eq map_of_zip_nth)
  hence "fmlookup (fmap_of_list (zip vars (map (apply_subst s) tys))) n
       = Some (apply_subst s (tys ! i))"
    by (simp add: CoreTy_Meta.prems(1) fmlookup_zip_map)
  thus ?case using lookup_eq by simp
next
  case (CoreTy_Name name tyargs)
  \<comment> \<open>Metavars of CoreTy_Name are union of metavars of tyargs\<close>
  have "\<forall>ty \<in> set tyargs. type_metavars ty \<subseteq> set vars"
    using CoreTy_Name.prems(2) by auto
  thus ?case
    using CoreTy_Name.IH CoreTy_Name.prems(1,3) by (induction tyargs) auto
next
  case (CoreTy_Record flds)
  \<comment> \<open>Metavars of CoreTy_Record are union of metavars of field types\<close>
  have flds_mvs: "\<forall>(name, ty) \<in> set flds. type_metavars ty \<subseteq> set vars"
    using CoreTy_Record.prems(2) by fastforce
  have "\<forall>(name, ty) \<in> set flds.
          apply_subst (fmap_of_list (zip vars (map (apply_subst s) tys))) ty
        = apply_subst s (apply_subst (fmap_of_list (zip vars tys)) ty)"
    using CoreTy_Record.IH CoreTy_Record.prems(1,3) flds_mvs by fastforce
  hence "map (\<lambda>(name, ty). (name, apply_subst (fmap_of_list (zip vars (map (apply_subst s) tys))) ty)) flds
       = map (\<lambda>(name, ty). (name, apply_subst s (apply_subst (fmap_of_list (zip vars tys)) ty))) flds"
    by (induction flds) auto
  also have "... = map ((\<lambda>(name, ty). (name, apply_subst s ty)) \<circ> (\<lambda>(name, ty). (name, apply_subst (fmap_of_list (zip vars tys)) ty))) flds"
    by (simp add: case_prod_unfold comp_def)
  also have "... = map (\<lambda>(name, ty). (name, apply_subst s ty)) (map (\<lambda>(name, ty). (name, apply_subst (fmap_of_list (zip vars tys)) ty)) flds)"
    by simp
  finally show ?case by simp
next
  case (CoreTy_Array elemTy dims)
  thus ?case by simp
qed simp_all

(* Corollary for mapping over a list of types *)
lemma map_apply_subst_compose_zip:
  assumes "length vars = length tys"
      and "\<forall>t \<in> set ts. type_metavars t \<subseteq> set vars"
      and "distinct vars"
  shows "map (apply_subst (fmap_of_list (zip vars (map (apply_subst s) tys)))) ts
       = map (apply_subst s) (map (apply_subst (fmap_of_list (zip vars tys))) ts)"
  using assms by (induction ts) (auto simp: apply_subst_compose_zip)


(* Length of elab_term_list output matches input *)
lemma elab_term_list_length:
  "elab_term_list env typedefs ghost tms next_mv = Inr (tms', tys', next_mv')
   \<Longrightarrow> length tms' = length tms \<and> length tys' = length tms"
proof (induction tms arbitrary: tms' tys' next_mv next_mv')
  case Nil
  then show ?case by simp
next
  case (Cons tm tms)
  then show ?case by (auto split: sum.splits)
qed

(* Correctness of determine_fun_call_type:
   If it succeeds, the returned information is consistent with the function declaration. *)
lemma determine_fun_call_type_correct:
  assumes "determine_fun_call_type env typedefs ghost callTm next_mv
           = Inr (fnName, newTyArgs, expArgTypes, retType, next_mv')"
      and "tyenv_well_formed env"
      and "typedefs_well_formed env typedefs"
  shows "\<exists>funInfo.
           fmlookup (TE_Functions env) fnName = Some funInfo
         \<and> (ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost)
         \<and> length newTyArgs = length (FI_TyArgs funInfo)
         \<and> list_all (is_well_kinded env) newTyArgs
         \<and> (ghost = NotGhost \<longrightarrow> list_all is_runtime_type newTyArgs)
         \<and> expArgTypes = map (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)))
                             (FI_TmArgs funInfo)
         \<and> retType = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs))
                                  (FI_ReturnType funInfo)"
proof (cases callTm)
  case (BabTm_Name fnLoc fnName' tyArgs)
  from assms(1) BabTm_Name obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions env) fnName' = Some funInfo"
    by (auto split: option.splits if_splits)
  from assms(1) BabTm_Name fn_lookup have
    ghost_ok: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost"
    by (auto split: if_splits sum.splits)
  from assms(1) BabTm_Name fn_lookup ghost_ok have
    fnName_eq: "fnName = fnName'"
    by (auto simp: Let_def split: if_splits sum.splits)

  let ?numTyParams = "length (FI_TyArgs funInfo)"

  show ?thesis
  proof (cases "tyArgs = [] \<and> ?numTyParams > 0")
    case True
    \<comment> \<open>Type args were omitted - metavariables generated\<close>
    let ?genTyArgs = "map CoreTy_Meta [next_mv..<next_mv + ?numTyParams]"
    from assms(1) BabTm_Name fn_lookup ghost_ok True
    have results: "newTyArgs = ?genTyArgs"
                  "expArgTypes = map (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) ?genTyArgs)))
                                     (FI_TmArgs funInfo)"
                  "retType = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) ?genTyArgs))
                                         (FI_ReturnType funInfo)"
      by (auto simp: Let_def)
    have len_ok: "length ?genTyArgs = ?numTyParams" by simp
    have wk_ok: "list_all (is_well_kinded env) ?genTyArgs"
      using list_all_meta_is_well_kinded by simp
    have runtime_ok: "list_all is_runtime_type ?genTyArgs"
      using list_all_meta_is_runtime by simp
    show ?thesis
      using fn_lookup ghost_ok fnName_eq results len_ok wk_ok runtime_ok
      by auto
  next
    case False
    show ?thesis
    proof (cases "?numTyParams = length tyArgs")
      case True
      from assms(1) BabTm_Name fn_lookup ghost_ok False True
      obtain elabTyArgs where
        elab_tyargs: "elab_type_list env typedefs ghost tyArgs = Inr elabTyArgs"
        by (cases "elab_type_list env typedefs ghost tyArgs")
           (auto simp: Let_def split: if_splits)
      from assms(1) BabTm_Name fn_lookup ghost_ok False True elab_tyargs
      have results: "newTyArgs = elabTyArgs"
                    "expArgTypes = map (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) elabTyArgs)))
                                       (FI_TmArgs funInfo)"
                    "retType = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) elabTyArgs))
                                           (FI_ReturnType funInfo)"
        by (auto simp: Let_def)
      have len_ok: "length elabTyArgs = ?numTyParams"
        using elab_tyargs True elab_type_list_length by fastforce
      have wk_ok: "list_all (is_well_kinded env) elabTyArgs"
        using elab_tyargs assms(2,3) elab_type_is_well_kinded(2) by auto
      have runtime_ok: "ghost = NotGhost \<longrightarrow> list_all is_runtime_type elabTyArgs"
        using elab_tyargs assms(3) elab_type_notghost_is_runtime(2) by (cases ghost; auto)
      show ?thesis
        using fn_lookup ghost_ok fnName_eq results len_ok wk_ok runtime_ok
        by auto
    next
      case False2: False
      from assms(1) BabTm_Name fn_lookup ghost_ok False False2
      have "False" by (auto simp: Let_def split: sum.splits if_splits)
      thus ?thesis ..
    qed
  qed
qed (use assms(1) in simp_all)


(* Correctness of unify_call_types (Phase 1):
   If it succeeds, the substitution is well-kinded and runtime-preserving,
   finalSubst extends accSubst (via composition with some theta),
   and for each pair of types, either they unify or both are finite integers. *)
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
           apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
           \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
              \<and> is_finite_integer_type (apply_subst finalSubst expectedTy)))
         actualTys expectedTys"
  using assms
proof (induction loc fnName argIdx actualTys expectedTys accSubst
       arbitrary: finalSubst
       rule: unify_call_types.induct)
  case (1 loc fnName argIdx accSubst)
  from "1.prems"(1) have "finalSubst = accSubst" by simp
  moreover have "accSubst = compose_subst fmempty accSubst" by simp
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

  show ?case
  proof (cases "unify ?actualTy' ?expectedTy'")
    case (Some newSubst)
    let ?composedSubst = "compose_subst newSubst accSubst"

    from "2.prems"(1) Some have
      recurse: "unify_call_types loc fnName (argIdx + 1) actualTys expectedTys ?composedSubst = Inr finalSubst"
      by (simp add: Let_def)

    have accSubst_wk: "metasubst_well_kinded env accSubst"
      using "2.prems"(6) by (simp add: metasubst_well_kinded_def fmran'_def)
    have actualTy'_wk: "is_well_kinded env ?actualTy'"
      using actualTy_wk accSubst_wk apply_subst_preserves_well_kinded by blast
    have expectedTy'_wk: "is_well_kinded env ?expectedTy'"
      using expectedTy_wk accSubst_wk apply_subst_preserves_well_kinded by blast
    have actualTy'_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type ?actualTy'"
      using actualTy_rt "2.prems"(9) apply_subst_preserves_runtime by blast
    have expectedTy'_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type ?expectedTy'"
      using expectedTy_rt "2.prems"(9) apply_subst_preserves_runtime by blast

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
                apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
                \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
                   \<and> is_finite_integer_type (apply_subst finalSubst expectedTy)))
              actualTys expectedTys"
      using "2.IH"(2) Some len_tl actualTys_rt actualTys_wk "2.prems"(2) composed_rt composed_wk expectedTys_rt
        expectedTys_wk recurse by simp

    \<comment> \<open>From unify_sound, after applying newSubst the types are equal\<close>
    from unify_sound[OF Some]
    have "apply_subst newSubst ?actualTy' = apply_subst newSubst ?expectedTy'" .
    hence head_eq: "apply_subst ?composedSubst actualTy = apply_subst ?composedSubst expectedTy"
      by (simp add: compose_subst_correct)

    \<comment> \<open>From IH, finalSubst = compose_subst theta composedSubst for some theta\<close>
    from ih obtain theta where finalSubst_eq: "finalSubst = compose_subst theta ?composedSubst"
      by blast
    \<comment> \<open>So finalSubst = compose_subst theta (compose_subst newSubst accSubst)
         = compose_subst (compose_subst theta newSubst) accSubst\<close>
    have finalSubst_ext: "finalSubst = compose_subst (compose_subst theta newSubst) accSubst"
      using finalSubst_eq by (simp add: compose_subst_assoc)
    hence extends_acc: "\<exists>theta'. finalSubst = compose_subst theta' accSubst" by blast

    \<comment> \<open>Use compose_subst_correct: apply_subst finalSubst t = apply_subst theta (apply_subst composedSubst t)\<close>
    have "apply_subst finalSubst actualTy = apply_subst theta (apply_subst ?composedSubst actualTy)"
      using finalSubst_eq by (simp add: compose_subst_correct)
    also have "... = apply_subst theta (apply_subst ?composedSubst expectedTy)"
      using head_eq by simp
    also have "... = apply_subst finalSubst expectedTy"
      using finalSubst_eq by (simp add: compose_subst_correct)
    finally have head_unified: "apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy" .

    show ?thesis using ih extends_acc head_unified by auto
  next
    case None
    from "2.prems"(1) None have
      is_int: "is_finite_integer_type ?actualTy' \<and> is_finite_integer_type ?expectedTy'"
      and recurse: "unify_call_types loc fnName (argIdx + 1) actualTys expectedTys accSubst = Inr finalSubst"
      by (simp_all add: Let_def split: if_splits)

    have ih: "(\<forall>ty \<in> fmran' finalSubst. is_well_kinded env ty)
            \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type ty))
            \<and> (\<exists>theta. finalSubst = compose_subst theta accSubst)
            \<and> list_all2 (\<lambda>actualTy expectedTy.
                apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
                \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
                   \<and> is_finite_integer_type (apply_subst finalSubst expectedTy)))
              actualTys expectedTys"
      using "2.IH"(1) None is_int len_tl recurse "2.prems"(2) actualTys_wk expectedTys_wk
                       "2.prems"(6) actualTys_rt expectedTys_rt "2.prems"(9)
      by simp

    \<comment> \<open>From IH, finalSubst = compose_subst theta accSubst for some theta\<close>
    from ih obtain theta where finalSubst_eq: "finalSubst = compose_subst theta accSubst"
      by blast

    \<comment> \<open>Finite integer types are ground, so applying any substitution gives same result\<close>
    have actualTy'_ground: "is_ground ?actualTy'"
      using is_int finite_integer_type_is_integer_type integer_type_is_ground by blast
    have expectedTy'_ground: "is_ground ?expectedTy'"
      using is_int finite_integer_type_is_integer_type integer_type_is_ground by blast

    \<comment> \<open>apply_subst finalSubst actualTy = apply_subst theta (apply_subst accSubst actualTy)
       = apply_subst theta ?actualTy'. Since ?actualTy' is ground, this equals ?actualTy'.\<close>
    have "apply_subst finalSubst actualTy = apply_subst theta ?actualTy'"
      using finalSubst_eq by (simp add: compose_subst_correct)
    also have "... = ?actualTy'"
      using actualTy'_ground apply_subst_ground by simp
    finally have actual_eq: "apply_subst finalSubst actualTy = ?actualTy'" .
    hence actual_finite: "is_finite_integer_type (apply_subst finalSubst actualTy)"
      using is_int by simp

    have "apply_subst finalSubst expectedTy = apply_subst theta ?expectedTy'"
      using finalSubst_eq by (simp add: compose_subst_correct)
    also have "... = ?expectedTy'"
      using expectedTy'_ground apply_subst_ground by simp
    finally have expected_eq: "apply_subst finalSubst expectedTy = ?expectedTy'" .
    hence expected_finite: "is_finite_integer_type (apply_subst finalSubst expectedTy)"
      using is_int by simp

    show ?thesis using ih actual_finite expected_finite by simp
  qed
next
  case ("3_1" uu uv uw v va uz)
  then show ?case by simp
next
  case ("3_2" uu uv uw v va uz)
  then show ?case by simp
qed


(* Correctness of apply_call_coercions (Phase 2):
   If input terms have the actual types, and the unify_call_types property holds
   (types equal after substitution or both finite integers), then output terms
   have the expected types after substitution. *)
lemma apply_call_coercions_correct:
  assumes "list_all2 (\<lambda>tm ty. core_term_type env ghost tm = Some ty) tms actualTys"
      and "list_all2 (\<lambda>actualTy expectedTy.
             apply_subst subst actualTy = apply_subst subst expectedTy
             \<or> (is_finite_integer_type (apply_subst subst actualTy)
                \<and> is_finite_integer_type (apply_subst subst expectedTy)))
           actualTys expectedTys"
      and "tyenv_well_formed env"
      and "\<forall>ty \<in> fmran' subst. is_well_kinded env ty"
      and "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' subst. is_runtime_type ty)"
      and "length tms = length actualTys"
      and "length actualTys = length expectedTys"
  shows "list_all2 (\<lambda>tm expectedTy.
           core_term_type env ghost tm = Some (apply_subst subst expectedTy))
         (apply_call_coercions subst tms actualTys expectedTys) expectedTys"
  using assms
proof (induction subst tms actualTys expectedTys rule: apply_call_coercions.induct)
  case (1 subst)
  then show ?case by simp
next
  case (2 subst tm tms actualTy actualTys expectedTy expectedTys)
  let ?tm' = "apply_subst_to_term subst tm"
  let ?actualTy' = "apply_subst subst actualTy"
  let ?expectedTy' = "apply_subst subst expectedTy"

  from "2.prems"(1) have
    head_typed: "core_term_type env ghost tm = Some actualTy" and
    tail_typed: "list_all2 (\<lambda>tm ty. core_term_type env ghost tm = Some ty) tms actualTys"
    by simp_all
  from "2.prems"(2) have
    head_prop: "?actualTy' = ?expectedTy' \<or> (is_finite_integer_type ?actualTy' \<and> is_finite_integer_type ?expectedTy')" and
    tail_prop: "list_all2 (\<lambda>actualTy expectedTy.
                  apply_subst subst actualTy = apply_subst subst expectedTy
                  \<or> (is_finite_integer_type (apply_subst subst actualTy)
                     \<and> is_finite_integer_type (apply_subst subst expectedTy)))
                actualTys expectedTys"
    by simp_all
  from "2.prems"(6,7) have
    len_tms: "length tms = length actualTys" and
    len_tys: "length actualTys = length expectedTys"
    by simp_all

  \<comment> \<open>IH for tail\<close>
  have ih: "list_all2 (\<lambda>tm expectedTy.
              core_term_type env ghost tm = Some (apply_subst subst expectedTy))
            (apply_call_coercions subst tms actualTys expectedTys) expectedTys"
    using "2.IH" tail_typed tail_prop "2.prems"(3,4,5) len_tms len_tys by simp

  \<comment> \<open>For the head: apply_subst_to_term preserves typing (with substituted type)\<close>
  have head_tm'_typed: "core_term_type env ghost ?tm' = Some ?actualTy'"
    using head_typed apply_subst_to_term_preserves_typing "2.prems"(3,4,5) by blast

  \<comment> \<open>Show the head element has the expected type\<close>
  have head_result: "core_term_type env ghost
                       (if ?actualTy' = ?expectedTy' then ?tm' else CoreTm_Cast ?expectedTy' ?tm')
                     = Some ?expectedTy'"
  proof (cases "?actualTy' = ?expectedTy'")
    case True
    then show ?thesis using head_tm'_typed by simp
  next
    case False
    \<comment> \<open>Types differ, so both must be finite integer types\<close>
    from head_prop False have
      actual_finite: "is_finite_integer_type ?actualTy'" and
      expected_finite: "is_finite_integer_type ?expectedTy'"
      by simp_all
    \<comment> \<open>Cast typechecks: operand has integer type, target has integer type, both runtime if NotGhost\<close>
    have actual_int: "is_integer_type ?actualTy'"
      using actual_finite finite_integer_type_is_integer_type by blast
    have expected_int: "is_integer_type ?expectedTy'"
      using expected_finite finite_integer_type_is_integer_type by blast
    have expected_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type ?expectedTy'"
      using expected_finite by (cases ?expectedTy') auto
    show ?thesis using head_tm'_typed actual_int expected_int expected_rt False
      by (auto split: option.splits)
  qed

  show ?case using head_result ih by (simp add: Let_def)
next
  case ("3_1" subst v va vb)
  then show ?case by simp
next
  case ("3_2" subst v va vb)
  then show ?case by simp
next
  case ("3_3" subst v va vb)
  then show ?case by simp
next
  case ("3_4" subst v va vb)
  then show ?case by simp
next
  case ("3_5" subst v va)
  then show ?case by simp
next
  case ("3_6" subst v va)
  then show ?case by simp
qed


(* Correctness of coerce_to_common_int_type:
   If coercion succeeds, both output terms have the common type. *)
lemma coerce_to_common_int_type_correct:
  assumes "coerce_to_common_int_type tm1 ty1 tm2 ty2 = Some (newTm1, newTm2, commonTy)"
      and "core_term_type env ghost tm1 = Some ty1"
      and "core_term_type env ghost tm2 = Some ty2"
      and "tyenv_well_formed env"
  shows "core_term_type env ghost newTm1 = Some commonTy
       \<and> core_term_type env ghost newTm2 = Some commonTy"
proof (cases ty1)
  case (CoreTy_FiniteInt sign1 bits1)
  then show ?thesis
  proof (cases ty2)
    case (CoreTy_FiniteInt sign2 bits2)
    from assms(1) CoreTy_FiniteInt \<open>ty1 = CoreTy_FiniteInt sign1 bits1\<close>
    obtain commonSign commonBits where
      combine: "combine_int_types sign1 bits1 sign2 bits2 = Some (commonSign, commonBits)"
      and commonTy_eq: "commonTy = CoreTy_FiniteInt commonSign commonBits"
      and newTm1_eq: "newTm1 = (if sign1 = commonSign \<and> bits1 = commonBits then tm1
                                else CoreTm_Cast (CoreTy_FiniteInt commonSign commonBits) tm1)"
      and newTm2_eq: "newTm2 = (if sign2 = commonSign \<and> bits2 = commonBits then tm2
                                else CoreTm_Cast (CoreTy_FiniteInt commonSign commonBits) tm2)"
      by (auto simp: Let_def split: option.splits)

    have ty1_int: "is_integer_type ty1" using \<open>ty1 = CoreTy_FiniteInt sign1 bits1\<close> by simp
    have ty2_int: "is_integer_type ty2" using CoreTy_FiniteInt by simp
    have commonTy_int: "is_integer_type commonTy" using commonTy_eq by simp
    have commonTy_rt: "is_runtime_type commonTy" using commonTy_eq by simp

    have newTm1_typed: "core_term_type env ghost newTm1 = Some commonTy"
    proof (cases "sign1 = commonSign \<and> bits1 = commonBits")
      case True
      hence "newTm1 = tm1" and "ty1 = commonTy"
        using newTm1_eq \<open>ty1 = CoreTy_FiniteInt sign1 bits1\<close> commonTy_eq by auto
      thus ?thesis using assms(2) by simp
    next
      case False
      hence "newTm1 = CoreTm_Cast commonTy tm1" using newTm1_eq commonTy_eq by simp
      thus ?thesis using assms(2) ty1_int commonTy_int commonTy_rt by auto
    qed

    have newTm2_typed: "core_term_type env ghost newTm2 = Some commonTy"
    proof (cases "sign2 = commonSign \<and> bits2 = commonBits")
      case True
      hence "newTm2 = tm2" and "ty2 = commonTy"
        using newTm2_eq CoreTy_FiniteInt commonTy_eq by auto
      thus ?thesis using assms(3) by simp
    next
      case False
      hence "newTm2 = CoreTm_Cast commonTy tm2" using newTm2_eq commonTy_eq by simp
      thus ?thesis using assms(3) ty2_int commonTy_int commonTy_rt by auto
    qed

    show ?thesis using newTm1_typed newTm2_typed by simp
  next
    case other: (CoreTy_Bool)
    with assms(1) \<open>ty1 = CoreTy_FiniteInt sign1 bits1\<close> show ?thesis by simp
  next
    case other: CoreTy_MathInt
    with assms(1) \<open>ty1 = CoreTy_FiniteInt sign1 bits1\<close> show ?thesis by simp
  next
    case other: CoreTy_MathReal
    with assms(1) \<open>ty1 = CoreTy_FiniteInt sign1 bits1\<close> show ?thesis by simp
  next
    case other: (CoreTy_Name x1 x2)
    with assms(1) \<open>ty1 = CoreTy_FiniteInt sign1 bits1\<close> show ?thesis by simp
  next
    case other: (CoreTy_Record x)
    with assms(1) \<open>ty1 = CoreTy_FiniteInt sign1 bits1\<close> show ?thesis by simp
  next
    case other: (CoreTy_Array x1 x2)
    with assms(1) \<open>ty1 = CoreTy_FiniteInt sign1 bits1\<close> show ?thesis by simp
  next
    case other: (CoreTy_Meta x)
    with assms(1) \<open>ty1 = CoreTy_FiniteInt sign1 bits1\<close> show ?thesis by simp
  qed
next
  case other: CoreTy_Bool
  with assms(1) show ?thesis by simp
next
  case other: CoreTy_MathInt
  with assms(1) show ?thesis by simp
next
  case other: CoreTy_MathReal
  with assms(1) show ?thesis by simp
next
  case other: (CoreTy_Name x1 x2)
  with assms(1) show ?thesis by simp
next
  case other: (CoreTy_Record x)
  with assms(1) show ?thesis by simp
next
  case other: (CoreTy_Array x1 x2)
  with assms(1) show ?thesis by simp
next
  case other: (CoreTy_Meta x)
  with assms(1) show ?thesis by simp
qed


(* ========================================================================== *)
(* Correctness of binary operator helpers *)
(* ========================================================================== *)

(* Correctness of check_and_coerce_binop: if the helper succeeds, the result is a
   CoreTm_Binop where both operands typecheck to a common type satisfying type_pred,
   and the common type is FiniteInt (when coercion was needed) or equal to the input types.
   The assumption that type_pred holds for all FiniteInt types is needed because
   coercion produces FiniteInt output. *)
lemma check_and_coerce_binop_correct:
  assumes "check_and_coerce_binop type_pred resultTyOverride errMsg cop
             lhsTm lhsTy rhsTm rhsTy loc babOp = Inr (resultTm, resultTy)"
    and "core_term_type env ghost lhsTm = Some lhsTy"
    and "core_term_type env ghost rhsTm = Some rhsTy"
    and "tyenv_well_formed env"
    and "\<And>s b. type_pred (CoreTy_FiniteInt s b)"
  shows "\<exists>opL opR commonTy.
    resultTm = CoreTm_Binop cop opL opR
    \<and> core_term_type env ghost opL = Some commonTy
    \<and> core_term_type env ghost opR = Some commonTy
    \<and> type_pred commonTy
    \<and> resultTy = (case resultTyOverride of None \<Rightarrow> commonTy | Some ty \<Rightarrow> ty)"
proof (cases "lhsTy = rhsTy")
  case True
  from assms(1) True have pred: "type_pred lhsTy"
    by (auto simp: check_and_coerce_binop_def Let_def split: if_splits)
  from assms(1) True pred have
    tm_eq: "resultTm = CoreTm_Binop cop lhsTm rhsTm" and
    ty_eq: "resultTy = (case resultTyOverride of None \<Rightarrow> lhsTy | Some ty \<Rightarrow> ty)"
    by (auto simp: check_and_coerce_binop_def Let_def)
  from pred tm_eq ty_eq assms(2,3) True show ?thesis
    by (intro exI[of _ lhsTm] exI[of _ rhsTm] exI[of _ lhsTy]) auto
next
  case False
  from assms(1) False have preds: "type_pred lhsTy" "type_pred rhsTy"
    by (auto simp: check_and_coerce_binop_def Let_def split: if_splits)
  from assms(1) False preds obtain newLhs newRhs commonTy where
    coerce: "coerce_to_common_int_type lhsTm lhsTy rhsTm rhsTy = Some (newLhs, newRhs, commonTy)" and
    tm_eq: "resultTm = CoreTm_Binop cop newLhs newRhs" and
    ty_eq: "resultTy = (case resultTyOverride of None \<Rightarrow> commonTy | Some ty \<Rightarrow> ty)"
    by (auto simp: check_and_coerce_binop_def Let_def split: option.splits)
  from coerce_to_common_int_type_correct[OF coerce assms(2,3,4)]
  have typed: "core_term_type env ghost newLhs = Some commonTy"
              "core_term_type env ghost newRhs = Some commonTy" by auto
  from coerce obtain s b where "commonTy = CoreTy_FiniteInt s b"
    by (cases lhsTy; cases rhsTy) (auto split: option.splits simp: Let_def)
  hence "type_pred commonTy" using assms(5) by simp
  with typed tm_eq ty_eq show ?thesis
    by (intro exI[of _ newLhs] exI[of _ newRhs] exI[of _ commonTy]) auto
qed

(* Helper: extract components from a successful build_comparison_chain in the let-binding case *)
lemma build_comparison_chain_let_elim:
  assumes "(case elab_binop_with_special loc ghost op lhsTm lhsTy varTm rhsTy of
              Inl errs \<Rightarrow> Inl errs
            | Inr (cmpTm, _) \<Rightarrow>
                (case build_comparison_chain loc ghost ctr' varTm rhsTy rest of
                  Inl errs \<Rightarrow> Inl errs
                | Inr restTm \<Rightarrow>
                    Inr (CoreTm_Let varName rhs
                          (CoreTm_Binop CoreBinop_And cmpTm restTm)))) = Inr resultTm"
  obtains cmpTm cmpTy restTm where
    "elab_binop_with_special loc ghost op lhsTm lhsTy varTm rhsTy = Inr (cmpTm, cmpTy)"
    "build_comparison_chain loc ghost ctr' varTm rhsTy rest = Inr restTm"
    "resultTm = CoreTm_Let varName rhs (CoreTm_Binop CoreBinop_And cmpTm restTm)"
  using assms by (auto split: sum.splits prod.splits)

(* Helper: range of fmap_of_list where all values are the same *)
lemma fmran'_fmap_of_list_const:
  "\<forall>ty' \<in> fmran' (fmap_of_list (map (\<lambda>n. (n, v)) ns)). ty' = v"
proof (induct ns)
  case Nil thus ?case by (simp add: fmran'_def fmlookup_of_list)
next
  case (Cons n ns)
  thus ?case by (auto simp: fmran'_def fmlookup_of_list)
qed

(* The range of const_subst_for contains only the default type *)
lemma const_subst_for_range:
  "\<forall>ty' \<in> fmran' (const_subst_for ty defaultTy). ty' = defaultTy"
  unfolding const_subst_for_def by (rule fmran'_fmap_of_list_const)

(* Helper: lookup in a constant-valued fmap_of_list *)
lemma fmlookup_fmap_of_list_const:
  "n \<in> set ns \<Longrightarrow> fmlookup (fmap_of_list (map (\<lambda>n. (n, v)) ns)) n = Some v"
  by (induct ns) (auto simp: fmlookup_of_list)

(* const_subst_for maps every metavariable in the type *)
lemma const_subst_for_domain:
  "n \<in> type_metavars ty \<Longrightarrow> fmlookup (const_subst_for ty defaultTy) n = Some defaultTy"
  unfolding const_subst_for_def
  using fmlookup_fmap_of_list_const[of n "type_metavars_list ty" defaultTy]
  by (simp add: set_type_metavars_list)

(* The domain of const_subst_for covers all metavars in the type *)
lemma const_subst_for_covers:
  "type_metavars ty \<subseteq> fset (fmdom (const_subst_for ty defaultTy))"
proof
  fix n assume "n \<in> type_metavars ty"
  hence "fmlookup (const_subst_for ty defaultTy) n = Some defaultTy"
    by (rule const_subst_for_domain)
  thus "n \<in> fset (fmdom (const_subst_for ty defaultTy))"
    by (simp add: fmlookup_dom_iff)
qed

(* const_subst_for makes a type ground if the default type is ground *)
lemma const_subst_for_makes_ground:
  "is_ground defaultTy \<Longrightarrow> is_ground (apply_subst (const_subst_for ty defaultTy) ty)"
  using apply_subst_makes_ground[OF const_subst_for_covers]
        const_subst_for_range[of ty defaultTy]
  by fastforce

(* Correctness of resolve_binop_metas: if the input terms typecheck at their types,
   the resolved terms typecheck at the resolved types. *)
lemma resolve_binop_metas_correct:
  assumes resolved: "resolve_binop_metas babOp lhsTm lhsTy rhsTm rhsTy = (lhsTm', lhsTy', rhsTm', rhsTy')"
    and lhs_typed: "core_term_type env ghost lhsTm = Some lhsTy"
    and rhs_typed: "core_term_type env ghost rhsTm = Some rhsTy"
    and wf: "tyenv_well_formed env"
  shows "core_term_type env ghost lhsTm' = Some lhsTy'
       \<and> core_term_type env ghost rhsTm' = Some rhsTy'"
proof (cases "unify lhsTy rhsTy")
  case None
  \<comment> \<open>Unification failed: pass through unchanged\<close>
  from resolved None have "lhsTm' = lhsTm" "lhsTy' = lhsTy" "rhsTm' = rhsTm" "rhsTy' = rhsTy"
    by simp_all
  thus ?thesis using lhs_typed rhs_typed by simp
next
  case (Some unifSubst)
  let ?unifiedTy = "apply_subst unifSubst lhsTy"
  have sound: "apply_subst unifSubst lhsTy = apply_subst unifSubst rhsTy"
    using unify_sound[OF Some] .
  \<comment> \<open>Substitution range is well-kinded and runtime\<close>
  have lhs_wk: "is_well_kinded env lhsTy"
    using core_term_type_well_kinded[OF lhs_typed wf] .
  have rhs_wk: "is_well_kinded env rhsTy"
    using core_term_type_well_kinded[OF rhs_typed wf] .
  have range_wk: "\<forall>ty' \<in> fmran' unifSubst. is_well_kinded env ty'"
    using unify_preserves_well_kinded[OF Some lhs_wk rhs_wk] .
  have range_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' unifSubst. is_runtime_type ty')"
  proof
    assume ng: "ghost = NotGhost"
    have "is_runtime_type lhsTy"
      using core_term_type_notghost_runtime lhs_typed local.wf ng by auto
    moreover have "is_runtime_type rhsTy"
      using core_term_type_notghost_runtime local.wf ng rhs_typed by auto
    ultimately show "\<forall>ty' \<in> fmran' unifSubst. is_runtime_type ty'"
      using unify_preserves_runtime[OF Some] by auto
  qed
  \<comment> \<open>Both terms typecheck after applying unifSubst\<close>
  have lhs_unif: "core_term_type env ghost (apply_subst_to_term unifSubst lhsTm) = Some ?unifiedTy"
    using apply_subst_to_term_preserves_typing[OF lhs_typed wf range_wk range_rt] by simp
  have rhs_unif: "core_term_type env ghost (apply_subst_to_term unifSubst rhsTm) = Some ?unifiedTy"
    using apply_subst_to_term_preserves_typing[OF rhs_typed wf range_wk range_rt] sound by simp
  show ?thesis
  proof (cases "is_ground ?unifiedTy")
    case True
    \<comment> \<open>Ground: directly use unified type\<close>
    have "lhsTm' = apply_subst_to_term unifSubst lhsTm"
      by (smt (verit, best) Some True old.prod.inject option.simps(5) resolve_binop_metas.simps
          resolved) 
    moreover have "lhsTy' = ?unifiedTy"
      by (smt (verit, del_insts) Pair_inject Some True option.simps(5) resolve_binop_metas.simps
          resolved) 
    moreover have "rhsTm' = apply_subst_to_term unifSubst rhsTm"
      by (smt (verit, del_insts) Some True old.prod.inject option.simps(5) resolve_binop_metas.simps
          resolved) 
    moreover have "rhsTy' = ?unifiedTy"
      by (smt (verit) Some True old.prod.inject option.simps(5) resolve_binop_metas.simps
          resolved) 
    ultimately show ?thesis using lhs_unif rhs_unif by simp
  next
    case not_ground: False
    \<comment> \<open>Not ground: fill remaining metas with default type\<close>
    let ?defaultTy = "default_type_for_binop babOp"
    let ?fillSubst = "const_subst_for ?unifiedTy ?defaultTy"
    let ?fullSubst = "compose_subst ?fillSubst unifSubst"
    have eq1: "lhsTm' = apply_subst_to_term ?fullSubst lhsTm"
      by (smt (verit, ccfv_SIG) Some not_ground old.prod.inject option.simps(5)
          resolve_binop_metas.simps resolved) 
    have eq2: "lhsTy' = apply_subst ?fillSubst ?unifiedTy"
      by (smt (verit) Some not_ground old.prod.inject option.simps(5) resolve_binop_metas.simps
          resolved) 
    have eq3: "rhsTm' = apply_subst_to_term ?fullSubst rhsTm"
      by (smt (verit) Some not_ground old.prod.inject option.simps(5) resolve_binop_metas.simps
          resolved) 
    have eq4: "rhsTy' = apply_subst ?fillSubst ?unifiedTy" 
    \<comment> \<open>The fill substitution range is well-kinded and runtime\<close>
      by (smt (verit) Some eq2 old.prod.inject option.simps(5) resolve_binop_metas.simps
          resolved)
    have default_wk: "is_well_kinded env ?defaultTy"
      by (auto simp: default_type_for_binop_def split: option.splits)
    have default_rt: "is_runtime_type ?defaultTy"
      by (auto simp: default_type_for_binop_def split: option.splits)
    have fill_range_wk: "\<forall>ty' \<in> fmran' ?fillSubst. is_well_kinded env ty'"
      using const_subst_for_range default_wk by metis
    have fill_range_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' ?fillSubst. is_runtime_type ty')"
      using const_subst_for_range default_rt by metis
    \<comment> \<open>Full substitution preserves typing\<close>
    have full_range_wk: "\<forall>ty' \<in> fmran' ?fullSubst. is_well_kinded env ty'"
      using compose_subst_preserves_well_kinded[OF range_wk fill_range_wk] by simp
    have full_range_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' ?fullSubst. is_runtime_type ty')"
    proof
      assume ng: "ghost = NotGhost"
      from range_rt ng have "\<forall>ty' \<in> fmran' unifSubst. is_runtime_type ty'" by simp
      from fill_range_rt ng have "\<forall>ty' \<in> fmran' ?fillSubst. is_runtime_type ty'" by simp
      from compose_subst_preserves_runtime[OF \<open>\<forall>ty' \<in> fmran' unifSubst. is_runtime_type ty'\<close>
                                              \<open>\<forall>ty' \<in> fmran' ?fillSubst. is_runtime_type ty'\<close>]
      show "\<forall>ty' \<in> fmran' ?fullSubst. is_runtime_type ty'" .
    qed
    have lhs': "core_term_type env ghost (apply_subst_to_term ?fullSubst lhsTm) =
                Some (apply_subst ?fullSubst lhsTy)"
      using apply_subst_to_term_preserves_typing[OF lhs_typed wf full_range_wk full_range_rt] by simp
    have "apply_subst ?fullSubst lhsTy = apply_subst ?fillSubst ?unifiedTy"
      using compose_subst_correct by simp
    have rhs': "core_term_type env ghost (apply_subst_to_term ?fullSubst rhsTm) =
                Some (apply_subst ?fullSubst rhsTy)"
      using apply_subst_to_term_preserves_typing[OF rhs_typed wf full_range_wk full_range_rt] by simp
    have "apply_subst ?fullSubst rhsTy = apply_subst ?fillSubst ?unifiedTy"
      using compose_subst_correct sound by simp
    show ?thesis using lhs' rhs' eq1 eq2 eq3 eq4
      \<open>apply_subst ?fullSubst lhsTy = apply_subst ?fillSubst ?unifiedTy\<close>
      \<open>apply_subst ?fullSubst rhsTy = apply_subst ?fillSubst ?unifiedTy\<close>
      by simp
  qed
qed

(* Correctness of elab_single_binop: if elaboration succeeds, the result typechecks. *)
lemma elab_single_binop_correct:
  assumes "elab_single_binop loc ghost babOp lhsTm lhsTy rhsTm rhsTy = Inr (resultTm, resultTy)"
    and "core_term_type env ghost lhsTm = Some lhsTy"
    and "core_term_type env ghost rhsTm = Some rhsTy"
    and "tyenv_well_formed env"
    and "binop_to_core babOp = Some cop"
  shows "core_term_type env ghost resultTm = Some resultTy"
proof -
  obtain lhsTm' lhsTy' rhsTm' rhsTy' where
    resolved: "resolve_binop_metas babOp lhsTm lhsTy rhsTm rhsTy = (lhsTm', lhsTy', rhsTm', rhsTy')"
    by (cases "resolve_binop_metas babOp lhsTm lhsTy rhsTm rhsTy") auto
  have lhs': "core_term_type env ghost lhsTm' = Some lhsTy'"
    and rhs': "core_term_type env ghost rhsTm' = Some rhsTy'"
    using resolve_binop_metas_correct[OF resolved assms(2,3,4)] by auto

  have cop: "binop_to_core babOp = Some cop" using assms(5) .

  \<comment> \<open>Case-split on the binop category using exhaustiveness\<close>
  consider (arith) "is_arithmetic_binop cop"
    | (modulo) "\<not> is_arithmetic_binop cop" "is_modulo_binop cop"
    | (bitwise) "\<not> is_arithmetic_binop cop" "\<not> is_modulo_binop cop" "is_bitwise_binop cop"
    | (shift) "\<not> is_arithmetic_binop cop" "\<not> is_modulo_binop cop" "\<not> is_bitwise_binop cop"
              "is_shift_binop cop"
    | (ordering) "\<not> is_arithmetic_binop cop" "\<not> is_modulo_binop cop" "\<not> is_bitwise_binop cop"
                 "\<not> is_shift_binop cop" "is_ordering_binop cop"
    | (eq_neq) "\<not> is_arithmetic_binop cop" "\<not> is_modulo_binop cop" "\<not> is_bitwise_binop cop"
               "\<not> is_shift_binop cop" "\<not> is_ordering_binop cop" "is_eq_neq_binop cop"
    | (logical) "\<not> is_arithmetic_binop cop" "\<not> is_modulo_binop cop" "\<not> is_bitwise_binop cop"
                "\<not> is_shift_binop cop" "\<not> is_ordering_binop cop" "\<not> is_eq_neq_binop cop"
                "is_logical_binop cop"
    using binop_category_exhaustive[of cop] by blast
  then show ?thesis
  proof cases
    \<comment> \<open>Arithmetic: both numeric, same type or coerced to common type\<close>
    case arith
    from assms(1) resolved cop arith have
      "check_and_coerce_binop is_numeric_type None TyErr_BinopRequiresNumeric cop
         lhsTm' lhsTy' rhsTm' rhsTy' loc babOp = Inr (resultTm, resultTy)"
      by (simp add: Let_def)
    from check_and_coerce_binop_correct[OF this lhs' rhs' assms(4)]
    obtain opL opR commonTy where
      tm_eq: "resultTm = CoreTm_Binop cop opL opR" and
      opL_ty: "core_term_type env ghost opL = Some commonTy" and
      opR_ty: "core_term_type env ghost opR = Some commonTy" and
      pred: "is_numeric_type commonTy" and ty_eq: "resultTy = commonTy"
      by auto
    with arith show ?thesis by auto
  next
    \<comment> \<open>Modulo: both integer, same type or coerced\<close>
    case modulo
    from assms(1) resolved cop modulo have
      "check_and_coerce_binop is_integer_type None TyErr_BinopRequiresInteger cop
         lhsTm' lhsTy' rhsTm' rhsTy' loc babOp = Inr (resultTm, resultTy)"
      by (simp add: Let_def)
    from check_and_coerce_binop_correct[OF this lhs' rhs' assms(4)]
    obtain opL opR commonTy where
      tm_eq: "resultTm = CoreTm_Binop cop opL opR" and
      opL_ty: "core_term_type env ghost opL = Some commonTy" and
      opR_ty: "core_term_type env ghost opR = Some commonTy" and
      pred: "is_integer_type commonTy" and ty_eq: "resultTy = commonTy"
      by auto
    with modulo show ?thesis by auto
  next
    \<comment> \<open>Bitwise: both finite integer, same type or coerced\<close>
    case bitwise
    from assms(1) resolved cop bitwise have
      "check_and_coerce_binop is_finite_integer_type None TyErr_BinopRequiresFiniteInteger cop
         lhsTm' lhsTy' rhsTm' rhsTy' loc babOp = Inr (resultTm, resultTy)"
      by (simp add: Let_def)
    from check_and_coerce_binop_correct[OF this lhs' rhs' assms(4)]
    obtain opL opR commonTy where
      tm_eq: "resultTm = CoreTm_Binop cop opL opR" and
      opL_ty: "core_term_type env ghost opL = Some commonTy" and
      opR_ty: "core_term_type env ghost opR = Some commonTy" and
      pred: "is_finite_integer_type commonTy" and ty_eq: "resultTy = commonTy"
      by auto
    with bitwise show ?thesis by auto
  next
    \<comment> \<open>Shift: both finite integer, cast RHS to LHS type\<close>
    case shift
    from assms(1) resolved cop shift have
      fin_lhs: "is_finite_integer_type lhsTy'" and fin_rhs: "is_finite_integer_type rhsTy'" and
      tm_eq: "resultTm = CoreTm_Binop cop lhsTm' (if lhsTy' = rhsTy' then rhsTm' else CoreTm_Cast lhsTy' rhsTm')" and
      ty_eq: "resultTy = lhsTy'"
      by (auto simp: Let_def split: if_splits)
    have cast_typed: "core_term_type env ghost (if lhsTy' = rhsTy' then rhsTm' else CoreTm_Cast lhsTy' rhsTm') = Some lhsTy'"
    proof (cases "lhsTy' = rhsTy'")
      case True
      then show ?thesis using rhs' by simp
    next
      case False
      have "is_integer_type rhsTy'" using fin_rhs finite_integer_type_is_integer_type by simp
      moreover have "is_integer_type lhsTy'" using fin_lhs finite_integer_type_is_integer_type by simp
      moreover have "is_runtime_type lhsTy'" using fin_lhs by (cases lhsTy') auto
      ultimately show ?thesis using rhs' False by auto
    qed
    with lhs' fin_lhs shift tm_eq ty_eq show ?thesis by auto
  next
    \<comment> \<open>Ordering: both numeric, result is Bool\<close>
    case ordering
    from assms(1) resolved cop ordering have
      "check_and_coerce_binop is_numeric_type (Some CoreTy_Bool) TyErr_BinopRequiresNumeric cop
         lhsTm' lhsTy' rhsTm' rhsTy' loc babOp = Inr (resultTm, resultTy)"
      by (simp add: Let_def)
    from check_and_coerce_binop_correct[OF this lhs' rhs' assms(4)]
    obtain opL opR commonTy where
      tm_eq: "resultTm = CoreTm_Binop cop opL opR" and
      opL_ty: "core_term_type env ghost opL = Some commonTy" and
      opR_ty: "core_term_type env ghost opR = Some commonTy" and
      pred: "is_numeric_type commonTy" and ty_eq: "resultTy = CoreTy_Bool"
      by auto
    with ordering show ?thesis by auto
  next
    \<comment> \<open>Equality/inequality\<close>
    case eq_neq
    show ?thesis
    proof (cases "lhsTy' = rhsTy'")
      case True
      with assms(1) resolved cop eq_neq have
        cond: "ghost = Ghost \<or> lhsTy' = CoreTy_Bool \<or> is_numeric_type lhsTy'" and
        tm_eq: "resultTm = CoreTm_Binop cop lhsTm' rhsTm'" and ty_eq: "resultTy = CoreTy_Bool"
        by (auto simp: Let_def split: if_splits)
      with lhs' rhs' eq_neq True show ?thesis by auto
    next
      case False
      with assms(1) resolved cop eq_neq obtain newLhs newRhs commonTy where
        coerce: "coerce_to_common_int_type lhsTm' lhsTy' rhsTm' rhsTy' = Some (newLhs, newRhs, commonTy)"
        and tm_eq: "resultTm = CoreTm_Binop cop newLhs newRhs" and ty_eq: "resultTy = CoreTy_Bool"
        by (auto simp: Let_def split: option.splits if_splits)
      from coerce_to_common_int_type_correct[OF coerce lhs' rhs' assms(4)]
      have typed: "core_term_type env ghost newLhs = Some commonTy"
                  "core_term_type env ghost newRhs = Some commonTy" by auto
      from coerce have "is_finite_integer_type commonTy"
        by (cases lhsTy'; cases rhsTy') (auto split: option.splits simp: Let_def)
      hence "is_numeric_type commonTy" by (cases commonTy) auto
      with typed eq_neq tm_eq ty_eq show ?thesis by auto
    qed
  next
    \<comment> \<open>Logical: both Bool\<close>
    case logical
    from assms(1) resolved cop logical have
      "lhsTy' = CoreTy_Bool" "rhsTy' = CoreTy_Bool"
      "resultTm = CoreTm_Binop cop lhsTm' rhsTm'" "resultTy = CoreTy_Bool"
      by (auto simp: Let_def split: if_splits)
    with lhs' rhs' logical show ?thesis by auto
  qed
qed

(* Correctness of elab_binop_with_special *)
lemma elab_binop_with_special_correct:
  assumes "elab_binop_with_special loc ghost babOp lhsTm lhsTy rhsTm rhsTy = Inr (resultTm, resultTy)"
    and "core_term_type env ghost lhsTm = Some lhsTy"
    and "core_term_type env ghost rhsTm = Some rhsTy"
    and "tyenv_well_formed env"
  shows "core_term_type env ghost resultTm = Some resultTy"
proof (cases "babOp = BabBinop_ImpliedBy \<or> babOp = BabBinop_Iff")
  case True
  then show ?thesis
  proof
    assume "babOp = BabBinop_ImpliedBy"
    \<comment> \<open>ImpliedBy: swaps operands and calls elab_single_binop with Implies\<close>
    with assms(1) have
      "elab_single_binop loc ghost BabBinop_Implies rhsTm rhsTy lhsTm lhsTy = Inr (resultTm, resultTy)"
      by simp
    thus ?thesis using elab_single_binop_correct[OF _ assms(3,2,4)]
      using binop_to_core.simps(19) by blast
  next
    assume iff: "babOp = BabBinop_Iff"
    \<comment> \<open>Iff: resolves metas then checks both Bool\<close>
    obtain lhsTm' lhsTy' rhsTm' rhsTy' where
      resolved: "resolve_binop_metas BabBinop_Iff lhsTm lhsTy rhsTm rhsTy = (lhsTm', lhsTy', rhsTm', rhsTy')"
      by (cases "resolve_binop_metas BabBinop_Iff lhsTm lhsTy rhsTm rhsTy") auto
    have lhs': "core_term_type env ghost lhsTm' = Some lhsTy'"
      and rhs': "core_term_type env ghost rhsTm' = Some rhsTy'"
      using resolve_binop_metas_correct[OF resolved assms(2,3,4)] by auto
    from assms(1) iff resolved have
      "lhsTy' = CoreTy_Bool" "rhsTy' = CoreTy_Bool"
      "resultTm = CoreTm_Binop CoreBinop_Equal lhsTm' rhsTm'" "resultTy = CoreTy_Bool"
      by (auto simp: Let_def split: if_splits)
    with lhs' rhs' show ?thesis by auto
  qed
next
  case False
  \<comment> \<open>All other cases: elab_binop_with_special delegates to elab_single_binop\<close>
  hence eq: "elab_binop_with_special loc ghost babOp lhsTm lhsTy rhsTm rhsTy
       = elab_single_binop loc ghost babOp lhsTm lhsTy rhsTm rhsTy"
    by (cases babOp) simp_all
  from False obtain cop where "binop_to_core babOp = Some cop"
    by (cases babOp) auto
  with assms(1) eq show ?thesis using elab_single_binop_correct assms(2,3,4) by auto
qed

(* For comparison operators (those with a comparison_direction), elab_binop_with_special
   always returns CoreTy_Bool as the result type when it succeeds. *)
lemma elab_binop_with_special_comparison_bool:
  assumes "elab_binop_with_special loc ghost babOp lhsTm lhsTy rhsTm rhsTy = Inr (resultTm, resultTy)"
    and "comparison_direction babOp \<noteq> None"
  shows "resultTy = CoreTy_Bool"
proof -
  \<comment> \<open>comparison_direction is only Some for <, <=, >, >=, ==, !=\<close>
  from assms(2) have "babOp \<in> {BabBinop_Less, BabBinop_LessEqual, BabBinop_Greater,
    BabBinop_GreaterEqual, BabBinop_Equal, BabBinop_NotEqual}"
    by (cases babOp) auto
  \<comment> \<open>None of these are ImpliedBy or Iff, so elab_binop_with_special calls elab_single_binop\<close>
  hence eq: "elab_single_binop loc ghost babOp lhsTm lhsTy rhsTm rhsTy = Inr (resultTm, resultTy)"
    using assms(1) by auto
  \<comment> \<open>For each of these 6 ops, elab_single_binop returns CoreTy_Bool on success\<close>
  from \<open>babOp \<in> _\<close> eq show "resultTy = CoreTy_Bool"
    by (auto simp: check_and_coerce_binop_def Let_def
             split: prod.splits option.splits if_splits)
qed

(* If check_comparison_chain_directions succeeds, all ops are comparisons *)
lemma check_comparison_chain_directions_all_comparison:
  assumes "check_comparison_chain_directions ops dir"
    and "(op, tm, ty) \<in> set ops"
  shows "comparison_direction op \<noteq> None"
  using assms by (induction ops arbitrary: dir) (auto split: option.splits if_splits)

(* Correctness of fold_binop_left *)
lemma fold_binop_left_correct:
  assumes "fold_binop_left loc ghost accTm accTy ops = Inr (resultTm, resultTy)"
    and "core_term_type env ghost accTm = Some accTy"
    and "list_all (\<lambda>(op, tm, ty). core_term_type env ghost tm = Some ty) ops"
    and "tyenv_well_formed env"
  shows "core_term_type env ghost resultTm = Some resultTy"
using assms proof (induction ops arbitrary: accTm accTy)
  case Nil
  then show ?case by simp
next
  case (Cons triple rest)
  obtain op rhsTm rhsTy where triple_eq: "triple = (op, rhsTm, rhsTy)"
    by (cases triple) auto
  from Cons.prems(1) triple_eq obtain midTm midTy where
    step: "elab_binop_with_special loc ghost op accTm accTy rhsTm rhsTy = Inr (midTm, midTy)" and
    rest: "fold_binop_left loc ghost midTm midTy rest = Inr (resultTm, resultTy)"
    by (auto split: sum.splits)
  have mid_typed: "core_term_type env ghost midTm = Some midTy"
    using elab_binop_with_special_correct[OF step Cons.prems(2) _ Cons.prems(4)]
      Cons.prems(3) triple_eq by simp
  show ?case using Cons.IH[OF rest mid_typed] Cons.prems(3,4) triple_eq by simp
qed

(* Correctness of fold_implies_right *)
lemma fold_implies_right_correct:
  assumes "fold_implies_right loc ghost lhsTm lhsTy ops = Inr (resultTm, resultTy)"
    and "core_term_type env ghost lhsTm = Some lhsTy"
    and "list_all (\<lambda>(op, tm, ty). core_term_type env ghost tm = Some ty) ops"
    and "tyenv_well_formed env"
  shows "core_term_type env ghost resultTm = Some resultTy"
using assms proof (induction ops arbitrary: lhsTm lhsTy resultTm resultTy)
  case Nil
  then show ?case by simp
next
  case (Cons triple rest)
  obtain op rhsTm rhsTy where triple_eq: "triple = (op, rhsTm, rhsTy)"
    by (cases triple) auto
  have rhs_typed: "core_term_type env ghost rhsTm = Some rhsTy"
    using Cons.prems(3) triple_eq by simp
  show ?case
  proof (cases rest)
    case Nil
    \<comment> \<open>Single element: just call elab_binop_with_special\<close>
    from Cons.prems(1) triple_eq Nil have
      "elab_binop_with_special loc ghost op lhsTm lhsTy rhsTm rhsTy = Inr (resultTm, resultTy)"
      by simp
    thus ?thesis using elab_binop_with_special_correct Cons.prems(2) rhs_typed Cons.prems(4) by blast
  next
    case (Cons triple2 rest2)
    \<comment> \<open>Multiple elements: recurse on right side, then combine\<close>
    from Cons.prems(1) triple_eq \<open>rest = triple2 # rest2\<close> obtain rightTm rightTy where
      recurse: "fold_implies_right loc ghost rhsTm rhsTy rest = Inr (rightTm, rightTy)" and
      combine: "elab_binop_with_special loc ghost op lhsTm lhsTy rightTm rightTy = Inr (resultTm, resultTy)"
      by (auto split: sum.splits)
    have rest_all: "list_all (\<lambda>(op, tm, ty). core_term_type env ghost tm = Some ty) rest"
      using Cons.prems(3) triple_eq by simp
    have right_typed: "core_term_type env ghost rightTm = Some rightTy"
      using Cons.IH[OF recurse rhs_typed rest_all Cons.prems(4)] .
    show ?thesis using elab_binop_with_special_correct[OF combine Cons.prems(2) right_typed Cons.prems(4)] .
  qed
qed

(* Helper: ''chain@@'' @ nat_to_string n starts with ''chain@@'' *)
lemma chain_var_prefix: "take 7 (''chain@@'' @ nat_to_string n) = ''chain@@''"
  by simp

(* Helper: the empty string does not start with ''chain@@'' *)
lemma empty_not_chain_prefix: "take 7 '''' \<noteq> ''chain@@''"
  by simp

(* Helper: if has_unexpected_chain_var returns False, then the only chain@@-prefixed
   free variable (if any) is the allowed one. *)
lemma not_has_unexpected_chain_var:
  assumes "\<not> has_unexpected_chain_var tm allowed"
    and "v \<in> core_term_free_vars tm"
    and "take 7 v = ''chain@@''"
  shows "v = allowed"
  using assms by (auto simp: has_unexpected_chain_var_def)

(* If build_comparison_chain returns Inr, then chain@@ variables (with index >= chainCtr)
   are not free in lhsTm, and chain@@ variables are not free in the op terms.
   This follows from the has_unexpected_chain_var runtime checks.
   We prove a combined statement to avoid issues with multi-conclusion induction. *)
lemma build_comparison_chain_inputs_fresh_combined:
  assumes "build_comparison_chain loc ghost chainCtr lhsTm lhsTy ops = Inr resultTm"
  shows "(\<forall>n \<ge> chainCtr. ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars lhsTm)
       \<and> (\<forall>opx \<in> set ops. \<forall>n. ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars (fst (snd opx)))"
  using assms
proof (induction ops arbitrary: chainCtr lhsTm lhsTy resultTm)
  case Nil
  \<comment> \<open>build_comparison_chain returns Inl [] for empty ops, contradicting Inr\<close>
  thus ?case by simp
next
  case (Cons triple rest)
  obtain op rhsTm rhsTy where triple_eq: "triple = (op, rhsTm, rhsTy)"
    by (cases triple) auto

  \<comment> \<open>Extract the check results from the Inr return\<close>
  let ?lhsAllowed = "if chainCtr = 0 then '''' else ''chain@@'' @ nat_to_string (chainCtr - 1)"

  \<comment> \<open>The Cons equation starts with a check; if it fails we get Inl, contradicting Inr.\<close>
  have checks_passed: "\<not> (has_unexpected_chain_var lhsTm ?lhsAllowed
                          \<or> has_unexpected_chain_var rhsTm '''')"
  proof (rule notI)
    assume "has_unexpected_chain_var lhsTm ?lhsAllowed
            \<or> has_unexpected_chain_var rhsTm ''''"
    hence "build_comparison_chain loc ghost chainCtr lhsTm lhsTy (triple # rest)
           = Inl [TyErr_InternalError_UnexpectedChainVar loc]"
      using triple_eq by (simp add: Let_def)
    with Cons.prems show False by simp
  qed
  hence check_lhs: "\<not> has_unexpected_chain_var lhsTm ?lhsAllowed"
    and check_rhs: "\<not> has_unexpected_chain_var rhsTm ''''"
    by auto

  \<comment> \<open>Part 1: chain@@n not free in lhsTm for n \<ge> chainCtr\<close>
  have lhs_result: "\<forall>n \<ge> chainCtr. ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars lhsTm"
  proof (intro allI impI notI)
    fix n assume n_ge: "n \<ge> chainCtr"
    assume in_fv: "''chain@@'' @ nat_to_string n \<in> core_term_free_vars lhsTm"
    have eq_allowed: "''chain@@'' @ nat_to_string n = ?lhsAllowed"
      using not_has_unexpected_chain_var[OF check_lhs in_fv chain_var_prefix] .
    show False
    proof (cases "chainCtr = 0")
      case True
      from True eq_allowed have "''chain@@'' @ nat_to_string n = ''''" by simp
      thus False by simp
    next
      case False
      from False eq_allowed
      have "''chain@@'' @ nat_to_string n = ''chain@@'' @ nat_to_string (chainCtr - 1)" by simp
      hence "nat_to_string n = nat_to_string (chainCtr - 1)" by simp
      hence "n = chainCtr - 1" using nat_to_string_injective by blast
      with n_ge False show False by arith
    qed
  qed

  \<comment> \<open>Part 2a: chain@@n not free in rhsTm (the first op term)\<close>
  have rhs_result: "\<forall>n. ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars rhsTm"
  proof (intro allI notI)
    fix n assume in_fv: "''chain@@'' @ nat_to_string n \<in> core_term_free_vars rhsTm"
    have "''chain@@'' @ nat_to_string n = ''''"
      using not_has_unexpected_chain_var[OF check_rhs in_fv chain_var_prefix] .
    thus False by simp
  qed

  \<comment> \<open>Part 2b: chain@@n not free in ops in rest (from IH via recursive call)\<close>
  have rest_result: "\<forall>opx \<in> set rest. \<forall>n. ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars (fst (snd opx))"
  proof (cases rest)
    case Nil thus ?thesis by simp
  next
    case (Cons triple2 rest2)
    \<comment> \<open>rest is non-empty, so there is a recursive call that returns Inr\<close>
    obtain resolvedLhs resolvedLhsTy resolvedRhs resolvedRhsTy where
      resolved: "resolve_binop_metas op lhsTm lhsTy rhsTm rhsTy =
                 (resolvedLhs, resolvedLhsTy, resolvedRhs, resolvedRhsTy)"
      by (cases "resolve_binop_metas op lhsTm lhsTy rhsTm rhsTy") auto
    \<comment> \<open>Simplify the function with checks eliminated\<close>
    from checks_passed triple_eq
    have bcc_simplified:
      "build_comparison_chain loc ghost chainCtr lhsTm lhsTy (triple # rest) =
       (case rest of
         [] \<Rightarrow> (case elab_binop_with_special loc ghost op lhsTm lhsTy rhsTm rhsTy of
                  Inl errs \<Rightarrow> Inl errs | Inr (cmpTm, _) \<Rightarrow> Inr cmpTm)
       | _ \<Rightarrow>
         let (_, _, resolvedRhs', resolvedRhsTy') = resolve_binop_metas op lhsTm lhsTy rhsTm rhsTy
         in if is_simple_term resolvedRhs' then
              (case elab_binop_with_special loc ghost op lhsTm lhsTy resolvedRhs' resolvedRhsTy' of
                Inl errs \<Rightarrow> Inl errs
              | Inr (cmpTm, _) \<Rightarrow>
                  (case build_comparison_chain loc ghost chainCtr resolvedRhs' resolvedRhsTy' rest of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr restTm \<Rightarrow> Inr (CoreTm_Binop CoreBinop_And cmpTm restTm)))
            else if \<not> is_ground resolvedRhsTy' then Inl [TyErr_CannotInferType loc]
            else let varName = ''chain@@'' @ nat_to_string chainCtr;
                     varTm = CoreTm_Var varName
                 in (case elab_binop_with_special loc ghost op lhsTm lhsTy varTm resolvedRhsTy' of
                      Inl errs \<Rightarrow> Inl errs
                    | Inr (cmpTm, _) \<Rightarrow>
                        (case build_comparison_chain loc ghost (chainCtr + 1) varTm resolvedRhsTy' rest of
                          Inl errs \<Rightarrow> Inl errs
                        | Inr restTm \<Rightarrow>
                            Inr (CoreTm_Let varName resolvedRhs'
                                  (CoreTm_Binop CoreBinop_And cmpTm restTm)))))"
      by (simp add: Let_def)

    show ?thesis
    proof (cases "is_simple_term resolvedRhs")
      case True
      \<comment> \<open>Simple term: recursive call with same chainCtr\<close>
      from Cons.prems bcc_simplified Cons resolved True
      obtain restTm where
        recurse: "build_comparison_chain loc ghost chainCtr resolvedRhs resolvedRhsTy rest = Inr restTm"
        by (auto simp: Let_def split: sum.splits prod.splits list.splits)
      from Cons.IH[OF recurse] show ?thesis by (simp add: prod.case_eq_if)
    next
      case not_simple: False
      \<comment> \<open>Hide nat_to_string chainCtr behind a definition to prevent linarith looping\<close>
      define varName where "varName = ''chain@@'' @ nat_to_string chainCtr"
      let ?varTm = "CoreTm_Var varName"

      \<comment> \<open>Derive a simplified equation for the complex case\<close>
      from bcc_simplified Cons resolved not_simple
      have bcc_complex:
        "build_comparison_chain loc ghost chainCtr lhsTm lhsTy (triple # rest) =
         (if \<not> is_ground resolvedRhsTy then Inl [TyErr_CannotInferType loc]
          else (case elab_binop_with_special loc ghost op lhsTm lhsTy ?varTm resolvedRhsTy of
                  Inl errs \<Rightarrow> Inl errs
                | Inr (cmpTm, _) \<Rightarrow>
                    (case build_comparison_chain loc ghost (chainCtr + 1) ?varTm resolvedRhsTy rest of
                      Inl errs \<Rightarrow> Inl errs
                    | Inr restTm \<Rightarrow>
                        Inr (CoreTm_Let varName resolvedRhs
                              (CoreTm_Binop CoreBinop_And cmpTm restTm)))))"
        unfolding varName_def[symmetric]
        by (simp add: Let_def split: list.splits prod.splits)

      show ?thesis
      proof (cases "is_ground resolvedRhsTy")
        case not_ground: False
        \<comment> \<open>Not ground: returns Inl, contradicting Inr\<close>
        from Cons.prems bcc_complex not_ground
        have False by simp
        thus ?thesis ..
      next
        case ground: True
        \<comment> \<open>Complex term: recursive call with chainCtr + 1\<close>
        from Cons.prems bcc_complex ground
        obtain restTm where
          recurse: "build_comparison_chain loc ghost (chainCtr + 1) ?varTm resolvedRhsTy rest = Inr restTm"
          by (auto split: sum.splits prod.splits)
        from Cons.IH[OF recurse] show ?thesis by (simp add: prod.case_eq_if)
      qed
    qed
  qed

  \<comment> \<open>Combine parts\<close>
  from lhs_result rhs_result rest_result
  show ?case using triple_eq by (auto simp: prod.case_eq_if)
qed

(* Split the combined lemma into the two conclusions used elsewhere *)
lemma build_comparison_chain_inputs_fresh:
  assumes "build_comparison_chain loc ghost chainCtr lhsTm lhsTy ops = Inr resultTm"
  shows "\<And>n. n \<ge> chainCtr \<Longrightarrow> ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars lhsTm"
    and "\<And>op tm ty n. (op, tm, ty) \<in> set ops \<Longrightarrow>
           ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars tm"
proof -
  note combined = build_comparison_chain_inputs_fresh_combined[OF assms]
  { fix n assume "n \<ge> chainCtr"
    with combined show "''chain@@'' @ nat_to_string n \<notin> core_term_free_vars lhsTm" by blast }
  { fix op tm ty n assume "(op, tm, ty) \<in> set ops"
    hence "(op, tm, ty) \<in> set ops" .
    with combined have "''chain@@'' @ nat_to_string n \<notin> core_term_free_vars (fst (snd (op, tm, ty)))"
      by blast
    thus "''chain@@'' @ nat_to_string n \<notin> core_term_free_vars tm" by simp }
qed

(* Correctness of build_comparison_chain. *)
lemma build_comparison_chain_correct:
  assumes "build_comparison_chain loc ghost chainCtr lhsTm lhsTy ops = Inr resultTm"
    and "core_term_type env ghost lhsTm = Some lhsTy"
    and "list_all (\<lambda>(op, tm, ty). core_term_type env ghost tm = Some ty) ops"
    and "tyenv_well_formed env"
    and "check_comparison_chain_directions ops dir"
  shows "core_term_type env ghost resultTm = Some CoreTy_Bool"
  using assms
proof (induction ops arbitrary: chainCtr lhsTm lhsTy resultTm env dir)
  case Nil
  then show ?case by simp
next
  case (Cons triple rest)
  obtain op rhsTm rhsTy where triple_eq: "triple = (op, rhsTm, rhsTy)"
    by (cases triple) auto
  have rhs_typed: "core_term_type env ghost rhsTm = Some rhsTy"
    using Cons.prems(3) triple_eq by simp

  \<comment> \<open>Get the chain direction info for op\<close>
  have op_cmp: "comparison_direction op \<noteq> None"
    using check_comparison_chain_directions_all_comparison[OF Cons.prems(5)]
          triple_eq by (meson list.set_intros(1) prod_cases3)

  \<comment> \<open>Get resolved operands\<close>
  obtain resolvedLhs resolvedLhsTy resolvedRhs resolvedRhsTy where
    resolved: "resolve_binop_metas op lhsTm lhsTy rhsTm rhsTy =
               (resolvedLhs, resolvedLhsTy, resolvedRhs, resolvedRhsTy)"
    by (cases "resolve_binop_metas op lhsTm lhsTy rhsTm rhsTy") auto

  have resolvedRhs_typed: "core_term_type env ghost resolvedRhs = Some resolvedRhsTy"
    using resolve_binop_metas_correct[OF resolved Cons.prems(2) rhs_typed Cons.prems(4)] by simp

  \<comment> \<open>Propagate chain direction check to rest\<close>
  have rest_dirs: "check_comparison_chain_directions rest
      (if comparison_direction op = Some ChainNeutral then dir else the (comparison_direction op))"
    using Cons.prems(5) triple_eq by (auto split: option.splits if_splits)

  \<comment> \<open>The has_unexpected_chain_var checks must have passed (otherwise we'd get Inl)\<close>
  let ?lhsAllowed = "if chainCtr = 0 then '''' else ''chain@@'' @ nat_to_string (chainCtr - 1)"
  have checks_passed: "\<not> (has_unexpected_chain_var lhsTm ?lhsAllowed
                          \<or> has_unexpected_chain_var rhsTm '''')"
  proof (rule notI)
    assume "has_unexpected_chain_var lhsTm ?lhsAllowed
            \<or> has_unexpected_chain_var rhsTm ''''"
    hence "build_comparison_chain loc ghost chainCtr lhsTm lhsTy (triple # rest)
           = Inl [TyErr_InternalError_UnexpectedChainVar loc]"
      using triple_eq by (simp add: Let_def)
    with Cons.prems(1) show False by simp
  qed

  show ?case
  proof (cases rest)
    case Nil
    \<comment> \<open>Last comparison: just elaborate normally\<close>
    from Cons.prems(1) triple_eq Nil checks_passed
    obtain cmpTm cmpTy where
      elab: "elab_binop_with_special loc ghost op lhsTm lhsTy rhsTm rhsTy = Inr (cmpTm, cmpTy)"
      and result: "resultTm = cmpTm"
      by (auto simp: Let_def split: sum.splits prod.splits)
    have "core_term_type env ghost cmpTm = Some cmpTy"
      using elab_binop_with_special_correct[OF elab Cons.prems(2) rhs_typed Cons.prems(4)] .
    moreover have "cmpTy = CoreTy_Bool"
      using elab_binop_with_special_comparison_bool[OF elab op_cmp] .
    ultimately show ?thesis using result by simp
  next
    case rest_cons: (Cons triple2 rest2)
    \<comment> \<open>More comparisons follow\<close>

    \<comment> \<open>Common facts for both subcases\<close>
    have rest_all: "list_all (\<lambda>(op, tm, ty). core_term_type env ghost tm = Some ty) rest"
      using Cons.prems(3) triple_eq by simp

    show ?thesis
    proof (cases "is_simple_term resolvedRhs")
      case True
      \<comment> \<open>Simple term: duplicate directly\<close>
      from Cons.prems(1) triple_eq rest_cons resolved True checks_passed
      obtain cmpTm cmpTy restTm where
        elab: "elab_binop_with_special loc ghost op lhsTm lhsTy resolvedRhs resolvedRhsTy
               = Inr (cmpTm, cmpTy)" and
        recurse: "build_comparison_chain loc ghost chainCtr resolvedRhs resolvedRhsTy rest
                  = Inr restTm" and
        result: "resultTm = CoreTm_Binop CoreBinop_And cmpTm restTm"
        by (auto simp: Let_def split: sum.splits prod.splits)
      have cmpTy_bool: "cmpTy = CoreTy_Bool"
        using elab_binop_with_special_comparison_bool[OF elab op_cmp] .
      have cmp_typed: "core_term_type env ghost cmpTm = Some CoreTy_Bool"
        using elab_binop_with_special_correct[OF elab Cons.prems(2) resolvedRhs_typed Cons.prems(4)]
              cmpTy_bool by simp
      have rest_typed: "core_term_type env ghost restTm = Some CoreTy_Bool"
        using Cons.IH[OF recurse resolvedRhs_typed rest_all Cons.prems(4) rest_dirs] .
      show ?thesis using cmp_typed rest_typed result by simp
    next
      case not_simple: False
      \<comment> \<open>Complex term: let-binding case\<close>
      let ?varName = "''chain@@'' @ nat_to_string chainCtr"
      let ?varTm = "CoreTm_Var ?varName"

      \<comment> \<open>The is_ground check must pass (otherwise we'd get Inl).\<close>
      from Cons.prems(1) triple_eq rest_cons resolved not_simple checks_passed
      have ground: "is_ground resolvedRhsTy"
        by (auto simp: Let_def split: if_splits sum.splits prod.splits)

      \<comment> \<open>Extract the elab and recursive call results via the helper lemma.\<close>
      from Cons.prems(1) triple_eq rest_cons resolved not_simple ground
      obtain cmpTm cmpTy restTm where
        elab: "elab_binop_with_special loc ghost op lhsTm lhsTy ?varTm resolvedRhsTy
               = Inr (cmpTm, cmpTy)" and
        recurse: "build_comparison_chain loc ghost (chainCtr + 1) ?varTm resolvedRhsTy rest
                  = Inr restTm" and
        result: "resultTm = CoreTm_Let ?varName resolvedRhs
                              (CoreTm_Binop CoreBinop_And cmpTm restTm)"
      proof -
        have "build_comparison_chain loc ghost chainCtr lhsTm lhsTy (Cons triple rest)
          = (let varName = ''chain@@'' @ nat_to_string chainCtr;
              varTm = CoreTm_Var varName
          in (case elab_binop_with_special loc ghost op lhsTm lhsTy varTm resolvedRhsTy of
            Inl errs \<Rightarrow> Inl errs
          | Inr (cmpTm, _) \<Rightarrow>
              (case build_comparison_chain loc ghost (chainCtr + 1) varTm resolvedRhsTy rest of
                Inl errs \<Rightarrow> Inl errs
              | Inr restTm \<Rightarrow>
                  Inr (CoreTm_Let varName resolvedRhs
                        (CoreTm_Binop CoreBinop_And cmpTm restTm)))))"
          using rest_cons triple_eq resolved not_simple ground checks_passed
          by (simp only: build_comparison_chain.simps prod.case Let_def list.case
                         if_False if_True if_not_P[OF not_simple]
                         not_True_eq_False not_False_eq_True ground)

        hence "(case elab_binop_with_special loc ghost op lhsTm lhsTy ?varTm resolvedRhsTy of
                Inl errs \<Rightarrow> Inl errs
              | Inr (cmpTm, _) \<Rightarrow>
                  (case build_comparison_chain loc ghost (chainCtr + 1) ?varTm resolvedRhsTy rest of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr restTm \<Rightarrow>
                      Inr (CoreTm_Let ?varName resolvedRhs
                            (CoreTm_Binop CoreBinop_And cmpTm restTm)))) = Inr resultTm"
          by (metis Cons.prems(1))

        thus ?thesis using build_comparison_chain_let_elim that by blast
      qed

      \<comment> \<open>Hide nat_to_string chainCtr behind a definition to prevent linarith looping\<close>
      define vn where "vn = ''chain@@'' @ nat_to_string chainCtr"
      have vn_eq: "?varName = vn" by (simp add: vn_def)

      \<comment> \<open>Rewrite elab, recurse, result to use vn\<close>
      note elab' = elab[unfolded vn_eq[symmetric]]
      note recurse' = recurse[unfolded vn_eq[symmetric]]
      note result' = result[unfolded vn_eq[symmetric]]

      \<comment> \<open>Derive chain@@ freshness from build_comparison_chain_inputs_fresh\<close>
      have lhs_fresh: "vn \<notin> core_term_free_vars lhsTm"
        using build_comparison_chain_inputs_fresh(1)[OF Cons.prems(1)] vn_def by blast
      have rest_fresh: "\<And>op tm ty n. (op, tm, ty) \<in> set rest \<Longrightarrow>
             ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars tm"
        using build_comparison_chain_inputs_fresh(2)[OF Cons.prems(1)]
              triple_eq by (meson list.set_intros(2))

      \<comment> \<open>Build the extended environment\<close>
      define gv' where "gv' = (if ghost = Ghost then finsert vn (TE_GhostVars env)
                               else fminus (TE_GhostVars env) {|vn|})"
      define env' where "env' = env \<lparr> TE_TermVars := fmupd vn resolvedRhsTy (TE_TermVars env),
                                       TE_GhostVars := gv' \<rparr>"

      \<comment> \<open>env' is well-formed\<close>
      have wk: "is_well_kinded env resolvedRhsTy"
        using core_term_type_well_kinded[OF resolvedRhs_typed Cons.prems(4)] .
      have env'_wf: "tyenv_well_formed env'"
      proof (cases ghost)
        case Ghost
        show ?thesis using tyenv_well_formed_add_ghost_var[OF Cons.prems(4) wk ground] Ghost
          by (simp add: env'_def gv'_def)
      next
        case NotGhost
        have "is_runtime_type resolvedRhsTy"
          using core_term_type_notghost_runtime[OF _ Cons.prems(4)] resolvedRhs_typed NotGhost by simp
        thus ?thesis using tyenv_well_formed_add_var[OF Cons.prems(4) wk ground] NotGhost
          by (simp add: env'_def gv'_def)
      qed

      \<comment> \<open>The variable typechecks in env'\<close>
      have var_typed: "core_term_type env' ghost (CoreTm_Var vn) = Some resolvedRhsTy"
        by (cases ghost) (simp_all add: env'_def gv'_def)

      \<comment> \<open>lhsTm typechecks in env' by weakening (vn not free in lhsTm)\<close>
      have gv'_agree: "\<forall>y. y \<noteq> vn \<longrightarrow> (y |\<in>| gv' \<longleftrightarrow> y |\<in>| TE_GhostVars env)"
        by (auto simp: gv'_def)
      have lhs_typed': "core_term_type env' ghost lhsTm = Some lhsTy"
        using core_term_type_irrelevant_var[OF lhs_fresh Cons.prems(2) gv'_agree]
        by (simp add: env'_def)

      \<comment> \<open>cmpTm typechecks in env'\<close>
      have cmpTy_bool: "cmpTy = CoreTy_Bool"
        using elab_binop_with_special_comparison_bool[OF elab op_cmp] .
      have elab_vn: "elab_binop_with_special loc ghost op lhsTm lhsTy (CoreTm_Var vn) resolvedRhsTy
                     = Inr (cmpTm, cmpTy)"
        using elab using vn_eq by auto
      have cmp_typed: "core_term_type env' ghost cmpTm = Some CoreTy_Bool"
        using elab_binop_with_special_correct[OF elab_vn lhs_typed' var_typed env'_wf]
              cmpTy_bool by simp

      \<comment> \<open>The ops in rest typecheck in env' by weakening\<close>
      have rest_all': "list_all (\<lambda>(op, tm, ty). core_term_type env' ghost tm = Some ty) rest"
        unfolding list_all_iff
      proof (intro ballI, clarify)
        fix xop xtm xty assume in_rest: "(xop, xtm, xty) \<in> set rest"
        have xtm_typed: "core_term_type env ghost xtm = Some xty"
          using rest_all in_rest by (auto simp: list_all_iff)
        have xtm_fresh: "vn \<notin> core_term_free_vars xtm"
          using rest_fresh in_rest vn_def by blast
        show "core_term_type env' ghost xtm = Some xty"
          using core_term_type_irrelevant_var[OF xtm_fresh xtm_typed gv'_agree]
          by (simp add: env'_def)
      qed

      \<comment> \<open>restTm typechecks in env' by the inductive hypothesis\<close>
      have recurse_vn: "build_comparison_chain loc ghost (chainCtr + 1)
                          (CoreTm_Var vn) resolvedRhsTy rest = Inr restTm"
        using recurse using vn_eq by auto
      have rest_typed: "core_term_type env' ghost restTm = Some CoreTy_Bool"
        using Cons.IH[OF recurse_vn var_typed rest_all' env'_wf rest_dirs] .

      \<comment> \<open>The body (And cmpTm restTm) typechecks in env'\<close>
      have body_typed: "core_term_type env' ghost (CoreTm_Binop CoreBinop_And cmpTm restTm)
                        = Some CoreTy_Bool"
        using cmp_typed rest_typed by simp

      \<comment> \<open>The whole let-expression typechecks\<close>
      have result_vn: "resultTm = CoreTm_Let vn resolvedRhs
                                    (CoreTm_Binop CoreBinop_And cmpTm restTm)"
        using result vn_def by simp
      have "core_term_type env ghost (CoreTm_Let vn resolvedRhs
              (CoreTm_Binop CoreBinop_And cmpTm restTm)) = Some CoreTy_Bool"
        using resolvedRhs_typed ground body_typed
        by (simp add: env'_def gv'_def Let_def)
      thus ?thesis using result_vn by simp
    qed
  qed
qed

(* Correctness of process_binop_chain *)
lemma process_binop_chain_correct:
  assumes "process_binop_chain loc ghost lhsTm lhsTy ops = Inr (resultTm, resultTy)"
    and "core_term_type env ghost lhsTm = Some lhsTy"
    and "list_all (\<lambda>(op, tm, ty). core_term_type env ghost tm = Some ty) ops"
    and "tyenv_well_formed env"
  shows "core_term_type env ghost resultTm = Some resultTy"
proof (cases ops)
  case Nil
  with assms(1) show ?thesis using assms(2) by simp
next
  case (Cons triple rest)
  let ?firstOp = "fst (hd ops)"
  show ?thesis
  proof (cases "?firstOp = BabBinop_Implies \<or> ?firstOp = BabBinop_ImpliedBy")
    case True
    \<comment> \<open>Implies chain: right-associates (check_implies_chain must pass, else we'd get Inl)\<close>
    with assms(1) Cons have "fold_implies_right loc ghost lhsTm lhsTy ops = Inr (resultTm, resultTy)"
      by (auto simp: Let_def split: if_splits)
    thus ?thesis using fold_implies_right_correct assms(2,3,4) by blast
  next
    case not_implies: False
    show ?thesis
    proof (cases "is_comparison_bab_binop ?firstOp \<and> length ops > 1")
      case True
      \<comment> \<open>Comparison chain\<close>
      from assms(1) Cons not_implies True
      have dirs: "check_comparison_chain_directions ops ChainNeutral"
        by (auto simp: Let_def split: sum.splits if_splits)
      from assms(1) Cons not_implies True
      obtain chainTm where
        chain_ok: "build_comparison_chain loc ghost 0 lhsTm lhsTy ops = Inr chainTm"
        and result: "resultTm = chainTm" and rty: "resultTy = CoreTy_Bool"
        by (auto simp: Let_def split: sum.splits if_splits)
      have "core_term_type env ghost chainTm = Some CoreTy_Bool"
        using build_comparison_chain_correct[OF chain_ok assms(2,3,4) dirs] .
      thus ?thesis using result rty by simp
    next
      case False
      \<comment> \<open>Left-associate\<close>
      with assms(1) Cons not_implies have
        "fold_binop_left loc ghost lhsTm lhsTy ops = Inr (resultTm, resultTy)"
        by (auto simp: Let_def split: if_splits)
      thus ?thesis using fold_binop_left_correct assms(2,3,4) by blast
    qed
  qed
qed


(* ========================================================================== *)
(* Main correctness theorem *)
(* ========================================================================== *)

(* Correctness theorem for elab_term and elab_term_list.
   If elaboration succeeds, the resulting term(s) have the claimed type(s). *)
theorem elab_term_correct:
  "elab_term env typedefs ghost tm next_mv = Inr (newTm, ty, next_mv') \<Longrightarrow>
   tyenv_well_formed env \<Longrightarrow>
   typedefs_well_formed env typedefs \<Longrightarrow>
   core_term_type env ghost newTm = Some ty"
and elab_term_list_correct:
  "elab_term_list env typedefs ghost tms next_mv = Inr (newTms, tys, next_mv') \<Longrightarrow>
   tyenv_well_formed env \<Longrightarrow>
   typedefs_well_formed env typedefs \<Longrightarrow>
   list_all2 (\<lambda>tm ty. core_term_type env ghost tm = Some ty) newTms tys"
proof (induction env typedefs ghost tm next_mv and env typedefs ghost tms next_mv
       arbitrary: newTm ty next_mv' and newTms tys next_mv'
       rule: elab_term_elab_term_list.induct)
  \<comment> \<open>Case: BabTm_Literal\<close>
  case (1 env typedefs ghost loc lit next_mv)
  show ?case
  proof (cases lit)
    case (BabLit_Bool b)
    with "1.prems"(1) have "newTm = CoreTm_LitBool b" and "ty = CoreTy_Bool"
      by auto
    thus ?thesis by simp
  next
    case (BabLit_Int i)
    with "1.prems"(1) obtain sign bits where
      get_type: "get_type_for_int i = Some (sign, bits)" and
      newTm_eq: "newTm = CoreTm_LitInt i" and
      ty_eq: "ty = CoreTy_FiniteInt sign bits"
      by (auto split: option.splits)
    thus ?thesis using get_type by simp
  next
    (* TODO *)
    case (BabLit_String x3)
    then show ?thesis sorry
  next
    (* TODO *)
    case (BabLit_Array x4)
    then show ?thesis sorry
  qed
next
  \<comment> \<open>Case: BabTm_Name (undefined)\<close>
  case (2 env typedefs ghost loc name tyArgs next_mv)
  then show ?case sorry

next
  \<comment> \<open>Case: BabTm_Cast\<close>
  case (3 env typedefs ghost loc targetTy operand next_mv)
  \<comment> \<open>Extract intermediate results\<close>
  from "3.prems"(1) obtain newTargetTy where
    elab_target: "elab_type env typedefs ghost targetTy = Inr newTargetTy"
    by (auto split: sum.splits)
  from "3.prems"(1) elab_target obtain newOperand operandTy next_mv' where
    elab_operand: "elab_term env typedefs ghost operand next_mv = Inr (newOperand, operandTy, next_mv')"
    by (auto split: sum.splits)
  from "3.prems"(1) elab_target elab_operand have
    target_is_int: "is_integer_type newTargetTy"
    by (auto split: if_splits)

  \<comment> \<open>IH: operand has its type\<close>
  have ih: "core_term_type env ghost newOperand = Some operandTy"
    using "3.IH" elab_target elab_operand "3.prems"(2,3) by simp

  show ?case
  proof (cases operandTy)
    case (CoreTy_Meta n)
    \<comment> \<open>Metavariable case: cast is eliminated via substitution\<close>
    from "3.prems"(1) elab_target elab_operand target_is_int CoreTy_Meta have
      result: "newTm = apply_subst_to_term (singleton_subst n newTargetTy) newOperand"
              "ty = newTargetTy"
      by auto
    \<comment> \<open>After substitution, the term has type newTargetTy\<close>
    have subst_wk: "\<forall>ty \<in> fmran' (singleton_subst n newTargetTy). is_well_kinded env ty"
      by (simp add: fmran'_singleton_subst is_integer_type_well_kinded target_is_int)
    have subst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' (singleton_subst n newTargetTy). is_runtime_type ty)"
      by (metis "3.prems"(3) elab_target elab_type_notghost_is_runtime(1) fmempty_lookup fmran'E
          fmupd_lookup option.discI option.inject singleton_subst_def)
    have "core_term_type env ghost (apply_subst_to_term (singleton_subst n newTargetTy) newOperand)
        = Some (apply_subst (singleton_subst n newTargetTy) operandTy)"
      using ih "3.prems"(2) subst_wk subst_rt apply_subst_to_term_preserves_typing by blast
    also have "apply_subst (singleton_subst n newTargetTy) operandTy = newTargetTy"
      using CoreTy_Meta apply_subst_singleton by blast
    finally show ?thesis using result by simp
  next
    case (CoreTy_FiniteInt sign bits)
    \<comment> \<open>Finite integer case: cast is kept\<close>
    from "3.prems"(1) elab_target elab_operand target_is_int CoreTy_FiniteInt have
      result: "newTm = CoreTm_Cast newTargetTy newOperand" "ty = newTargetTy"
      by auto
    have operand_is_int: "is_integer_type operandTy"
      using CoreTy_FiniteInt by simp
    have target_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type newTargetTy"
      using elab_target "3.prems"(3) elab_type_notghost_is_runtime by (cases ghost) auto
    show ?thesis using result ih operand_is_int target_is_int target_rt by auto
  next
    case CoreTy_MathInt
    \<comment> \<open>MathInt case: cast is kept\<close>
    from "3.prems"(1) elab_target elab_operand target_is_int CoreTy_MathInt have
      result: "newTm = CoreTm_Cast newTargetTy newOperand" "ty = newTargetTy"
      by auto
    have operand_is_int: "is_integer_type operandTy"
      using CoreTy_MathInt by simp
    have target_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type newTargetTy"
      using elab_target "3.prems"(3) elab_type_notghost_is_runtime by (cases ghost) auto
    show ?thesis using result ih operand_is_int target_is_int target_rt by auto
  next
    \<comment> \<open>Other cases result in error, so don't reach Inr\<close>
    case CoreTy_Bool
    with "3.prems"(1) elab_target elab_operand target_is_int show ?thesis by auto
  next
    case (CoreTy_Name x1 x2)
    with "3.prems"(1) elab_target elab_operand target_is_int show ?thesis by auto
  next
    case CoreTy_MathReal
    with "3.prems"(1) elab_target elab_operand target_is_int show ?thesis by auto
  next
    case (CoreTy_Record x)
    with "3.prems"(1) elab_target elab_operand target_is_int show ?thesis by auto
  next
    case (CoreTy_Array x1 x2)
    with "3.prems"(1) elab_target elab_operand target_is_int show ?thesis by auto
  qed

next
  \<comment> \<open>Case: BabTm_If - elaborates to CoreTm_Match with True/False patterns\<close>
  case (4 env typedefs ghost loc condTm thenTm elseTm next_mv)

  \<comment> \<open>Extract intermediate elaboration results\<close>
  from "4.prems"(1) obtain newCond condTy next_mv1 where
    elab_cond: "elab_term env typedefs ghost condTm next_mv = Inr (newCond, condTy, next_mv1)"
    by (auto split: sum.splits)
  from "4.prems"(1) elab_cond obtain newThen thenTy next_mv2 where
    elab_then: "elab_term env typedefs ghost thenTm next_mv1 = Inr (newThen, thenTy, next_mv2)"
    by (auto split: sum.splits)
  from "4.prems"(1) elab_cond elab_then obtain newElse elseTy next_mv3 where
    elab_else: "elab_term env typedefs ghost elseTm next_mv2 = Inr (newElse, elseTy, next_mv3)"
    by (auto split: sum.splits)

  \<comment> \<open>Get the final condition after possible metavariable specialization\<close>
  define finalCond where
    "finalCond = (case condTy of CoreTy_Meta n \<Rightarrow> apply_subst_to_term (singleton_subst n CoreTy_Bool) newCond | _ \<Rightarrow> newCond)"

  \<comment> \<open>The condition type must be Bool or Meta for elaboration to succeed\<close>
  from "4.prems"(1) elab_cond elab_then elab_else have condTy_bool_or_meta:
    "condTy = CoreTy_Bool \<or> (\<exists>n. condTy = CoreTy_Meta n)"
    by (auto simp: Let_def split: CoreType.splits option.splits if_splits)

  \<comment> \<open>IH: elaborated subterms have their claimed types\<close>
  have ih_cond: "core_term_type env ghost newCond = Some condTy"
    using "4.IH"(1) elab_cond "4.prems"(2,3) by simp
  have ih_then: "core_term_type env ghost newThen = Some thenTy"
    using "4.IH"(2) elab_cond elab_then "4.prems"(2,3) by simp
  have ih_else: "core_term_type env ghost newElse = Some elseTy"
    using "4.IH"(3) elab_cond elab_then elab_else "4.prems"(2,3) by simp

  \<comment> \<open>Final condition has type Bool\<close>
  have ih_finalCond: "core_term_type env ghost finalCond = Some CoreTy_Bool"
    using condTy_bool_or_meta
  proof
    assume "condTy = CoreTy_Bool"
    thus ?thesis using ih_cond by (simp add: finalCond_def)
  next
    assume "\<exists>n. condTy = CoreTy_Meta n"
    then obtain n where condTy_meta: "condTy = CoreTy_Meta n" by blast
    hence "finalCond = apply_subst_to_term (singleton_subst n CoreTy_Bool) newCond"
      by (simp add: finalCond_def)
    moreover have "core_term_type env ghost (apply_subst_to_term (singleton_subst n CoreTy_Bool) newCond)
                 = Some (apply_subst (singleton_subst n CoreTy_Bool) condTy)"
      using ih_cond "4.prems"(2) apply_subst_to_term_preserves_typing
      by (simp add: fmran'_singleton_subst)
    moreover have "apply_subst (singleton_subst n CoreTy_Bool) condTy = CoreTy_Bool"
      using condTy_meta apply_subst_singleton by auto
    ultimately show ?thesis by simp
  qed

  \<comment> \<open>Now handle the two cases: unification succeeds or integer coercion\<close>
  show ?case
  proof (cases "unify thenTy elseTy")
    case (Some branchSubst)
    \<comment> \<open>Unification succeeded\<close>
    let ?resultTy = "apply_subst branchSubst thenTy"
    let ?newThen' = "apply_subst_to_term branchSubst newThen"
    let ?newElse' = "apply_subst_to_term branchSubst newElse"
    let ?matchArms = "[(CorePat_Bool True, ?newThen'), (CorePat_Bool False, ?newElse')]"

    from "4.prems"(1) elab_cond elab_then elab_else condTy_bool_or_meta Some have
      result_eq: "newTm = CoreTm_Match finalCond ?matchArms" "ty = ?resultTy"
      by (auto simp: finalCond_def Let_def split: CoreType.splits)

    \<comment> \<open>From unify_sound: applying branchSubst unifies the types\<close>
    from unify_sound[OF Some] have unified: "apply_subst branchSubst thenTy = apply_subst branchSubst elseTy" .

    \<comment> \<open>Substituted branches have the result type\<close>
    have branchSubst_wk: "\<forall>ty \<in> fmran' branchSubst. is_well_kinded env ty"
      using Some ih_then ih_else "4.prems"(2) core_term_type_well_kinded unify_preserves_well_kinded by blast
    have branchSubst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' branchSubst. is_runtime_type ty)"
      using Some ih_then ih_else "4.prems"(2) core_term_type_notghost_runtime unify_preserves_runtime by blast

    have then'_typed: "core_term_type env ghost ?newThen' = Some ?resultTy"
      using ih_then "4.prems"(2) branchSubst_wk branchSubst_rt apply_subst_to_term_preserves_typing by blast
    have else'_typed: "core_term_type env ghost ?newElse' = Some ?resultTy"
      using ih_else "4.prems"(2) branchSubst_wk branchSubst_rt apply_subst_to_term_preserves_typing unified by fastforce

    \<comment> \<open>The match typechecks\<close>
    have "core_term_type env ghost (CoreTm_Match finalCond ?matchArms) = Some ?resultTy"
    proof -
      have "?matchArms \<noteq> []" by simp
      have pats_compat: "list_all (\<lambda>p. pattern_compatible env p CoreTy_Bool) (map fst ?matchArms)"
        by simp
      have pats_regular: "patterns_regular (map fst ?matchArms)"
        by (simp add: patterns_regular_def)
      have pats_exhaustive: "patterns_exhaustive env CoreTy_Bool (map fst ?matchArms)"
        by simp
      have bodies_typed: "list_all (\<lambda>body. core_term_type env ghost body = Some ?resultTy) (map snd ?matchArms)"
        using then'_typed else'_typed by simp
      show ?thesis
        using ih_finalCond \<open>?matchArms \<noteq> []\<close> pats_compat pats_regular pats_exhaustive bodies_typed
        by (simp add: then'_typed)
    qed
    thus ?thesis using result_eq by simp

  next
    case None
    \<comment> \<open>Unification failed - try integer coercion\<close>
    from "4.prems"(1) elab_cond elab_then elab_else condTy_bool_or_meta None
    obtain coercedThen coercedElse commonTy where
      coerce: "coerce_to_common_int_type newThen thenTy newElse elseTy = Some (coercedThen, coercedElse, commonTy)"
      by (auto simp: finalCond_def Let_def split: CoreType.splits option.splits)

    let ?matchArms = "[(CorePat_Bool True, coercedThen), (CorePat_Bool False, coercedElse)]"

    from "4.prems"(1) elab_cond elab_then elab_else condTy_bool_or_meta None coerce have
      result_eq: "newTm = CoreTm_Match finalCond ?matchArms" "ty = commonTy"
      by (auto simp: finalCond_def Let_def split: CoreType.splits)

    \<comment> \<open>From coerce_to_common_int_type_correct: coerced terms have common type\<close>
    have coerced_typed: "core_term_type env ghost coercedThen = Some commonTy
                       \<and> core_term_type env ghost coercedElse = Some commonTy"
      using coerce_to_common_int_type_correct[OF coerce ih_then ih_else "4.prems"(2)] .
    hence coerced_then_typed: "core_term_type env ghost coercedThen = Some commonTy"
      and coerced_else_typed: "core_term_type env ghost coercedElse = Some commonTy"
      by simp_all

    \<comment> \<open>The match typechecks\<close>
    have "core_term_type env ghost (CoreTm_Match finalCond ?matchArms) = Some commonTy"
    proof -
      have "?matchArms \<noteq> []" by simp
      have pats_compat: "list_all (\<lambda>p. pattern_compatible env p CoreTy_Bool) (map fst ?matchArms)"
        by simp
      have pats_regular: "patterns_regular (map fst ?matchArms)"
        by (simp add: patterns_regular_def)
      have pats_exhaustive: "patterns_exhaustive env CoreTy_Bool (map fst ?matchArms)"
        by simp
      have bodies_typed: "list_all (\<lambda>body. core_term_type env ghost body = Some commonTy) (map snd ?matchArms)"
        using coerced_then_typed coerced_else_typed by simp
      show ?thesis
        using ih_finalCond \<open>?matchArms \<noteq> []\<close> pats_compat pats_regular pats_exhaustive bodies_typed
        by (simp add: coerced_then_typed)
    qed
    thus ?thesis using result_eq by simp
  qed

next
  \<comment> \<open>Case: BabTm_Unop\<close>
  case (5 env typedefs ghost loc op operand next_mv)
  \<comment> \<open>Extract intermediate results\<close>
  from "5.prems"(1) obtain newOperand operandTy next_mv' where
    elab_operand: "elab_term env typedefs ghost operand next_mv = Inr (newOperand, operandTy, next_mv')"
    by (auto split: sum.splits)

  \<comment> \<open>IH: operand has its type\<close>
  have ih: "core_term_type env ghost newOperand = Some operandTy"
    using "5.IH" elab_operand "5.prems"(2,3) by simp

  show ?case
  proof (cases operandTy)
    case (CoreTy_Meta n)
    \<comment> \<open>Metavariable case: use default type\<close>
    let ?cop = "unop_to_core op"
    let ?defaultTy = "default_type_for_unop ?cop"
    let ?subst = "singleton_subst n ?defaultTy"
    let ?newOperand2 = "apply_subst_to_term ?subst newOperand"

    from "5.prems"(1) elab_operand CoreTy_Meta have
      result: "newTm = CoreTm_Unop ?cop ?newOperand2" "ty = ?defaultTy"
      by (auto simp: Let_def)

    \<comment> \<open>Substitution properties\<close>
    have subst_wk: "\<forall>ty \<in> fmran' ?subst. is_well_kinded env ty"
      by (simp add: fmran'_singleton_subst default_type_for_unop_is_well_kinded)
    have subst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' ?subst. is_runtime_type ty)"
      by (simp add: fmran'_singleton_subst default_type_for_unop_is_runtime)

    \<comment> \<open>After substitution, operand has the default type\<close>
    have "core_term_type env ghost ?newOperand2 = Some (apply_subst ?subst operandTy)"
      using ih "5.prems"(2) subst_wk subst_rt apply_subst_to_term_preserves_typing by blast
    hence operand2_typed: "core_term_type env ghost ?newOperand2 = Some ?defaultTy"
      using CoreTy_Meta apply_subst_singleton by simp

    \<comment> \<open>The default type satisfies the operator's requirement\<close>
    have op_ok: "(case ?cop of
        CoreUnop_Negate \<Rightarrow> is_signed_numeric_type ?defaultTy
      | CoreUnop_Complement \<Rightarrow> is_finite_integer_type ?defaultTy
      | CoreUnop_Not \<Rightarrow> ?defaultTy = CoreTy_Bool)"
      by (cases op) simp_all

    show ?thesis using result operand2_typed op_ok by (cases ?cop) auto
  next
    case (CoreTy_FiniteInt sign bits)
    \<comment> \<open>Finite integer: depends on the operator\<close>
    show ?thesis
    proof (cases op)
      case BabUnop_Negate
      show ?thesis
      proof (cases sign)
        case Signed
        with "5.prems"(1) elab_operand CoreTy_FiniteInt BabUnop_Negate have
          result: "newTm = CoreTm_Unop CoreUnop_Negate newOperand" "ty = operandTy"
          by auto
        have signed: "is_signed_numeric_type operandTy" using CoreTy_FiniteInt Signed by simp
        show ?thesis using result ih signed by simp
      next
        case Unsigned
        \<comment> \<open>Unsigned finite int cannot be negated - elaboration fails\<close>
        with "5.prems"(1) elab_operand CoreTy_FiniteInt BabUnop_Negate show ?thesis by auto
      qed
    next
      case BabUnop_Complement
      from "5.prems"(1) elab_operand CoreTy_FiniteInt BabUnop_Complement have
        result: "newTm = CoreTm_Unop CoreUnop_Complement newOperand" "ty = operandTy"
        by auto
      have finite: "is_finite_integer_type operandTy" using CoreTy_FiniteInt by simp
      show ?thesis using result ih finite by simp
    next
      case BabUnop_Not
      from "5.prems"(1) elab_operand CoreTy_FiniteInt BabUnop_Not show ?thesis by auto
    qed
  next
    case CoreTy_MathInt
    show ?thesis
    proof (cases op)
      case BabUnop_Negate
      from "5.prems"(1) elab_operand CoreTy_MathInt BabUnop_Negate have
        result: "newTm = CoreTm_Unop CoreUnop_Negate newOperand" "ty = operandTy"
        by auto
      have signed: "is_signed_numeric_type operandTy" using CoreTy_MathInt by simp
      show ?thesis using result ih signed by simp
    next
      case BabUnop_Complement
      \<comment> \<open>MathInt is not finite, so complement fails\<close>
      from "5.prems"(1) elab_operand CoreTy_MathInt BabUnop_Complement show ?thesis by auto
    next
      case BabUnop_Not
      from "5.prems"(1) elab_operand CoreTy_MathInt BabUnop_Not show ?thesis by auto
    qed
  next
    case CoreTy_Bool
    show ?thesis
    proof (cases op)
      case BabUnop_Not
      from "5.prems"(1) elab_operand CoreTy_Bool BabUnop_Not have
        result: "newTm = CoreTm_Unop CoreUnop_Not newOperand" "ty = operandTy"
        by auto
      show ?thesis using result ih CoreTy_Bool by simp
    next
      case BabUnop_Negate
      from "5.prems"(1) elab_operand CoreTy_Bool BabUnop_Negate show ?thesis by auto
    next
      case BabUnop_Complement
      from "5.prems"(1) elab_operand CoreTy_Bool BabUnop_Complement show ?thesis by auto
    qed
  next
    \<comment> \<open>Other operand types result in error\<close>
    case (CoreTy_Name x1 x2)
    with "5.prems"(1) elab_operand show ?thesis by (cases op) auto
  next
    case CoreTy_MathReal
    show ?thesis
    proof (cases op)
      case BabUnop_Negate
      from "5.prems"(1) elab_operand CoreTy_MathReal BabUnop_Negate have
        result: "newTm = CoreTm_Unop CoreUnop_Negate newOperand" "ty = operandTy"
        by auto
      have signed: "is_signed_numeric_type operandTy" using CoreTy_MathReal by simp
      show ?thesis using result ih signed by simp
    next
      case BabUnop_Complement
      \<comment> \<open>MathReal is not a finite integer, so complement fails\<close>
      from "5.prems"(1) elab_operand CoreTy_MathReal BabUnop_Complement show ?thesis by auto
    next
      case BabUnop_Not
      from "5.prems"(1) elab_operand CoreTy_MathReal BabUnop_Not show ?thesis by auto
    qed
  next
    case (CoreTy_Record x)
    with "5.prems"(1) elab_operand show ?thesis by (cases op) auto
  next
    case (CoreTy_Array x1 x2)
    with "5.prems"(1) elab_operand show ?thesis by (cases op) auto
  qed

next
  \<comment> \<open>Case: BabTm_Binop\<close>
  case (6 env typedefs ghost loc lhs operands next_mv)
  \<comment> \<open>Extract elaboration of LHS\<close>
  from "6.prems"(1) obtain newLhs lhsTy next_mv1 where
    elab_lhs: "elab_term env typedefs ghost lhs next_mv = Inr (newLhs, lhsTy, next_mv1)"
    by (auto split: sum.splits)
  \<comment> \<open>Extract elaboration of RHS terms\<close>
  from "6.prems"(1) elab_lhs obtain rhsTms rhsTys next_mv2 where
    elab_rhs_list: "elab_term_list env typedefs ghost (map snd operands) next_mv1
                    = Inr (rhsTms, rhsTys, next_mv2)"
    by (auto split: sum.splits)
  \<comment> \<open>Build the operator list\<close>
  let ?opTriples = "zip (map fst operands) (zip rhsTms rhsTys)"
  let ?opList = "map (\<lambda>(op, tm_ty). (op, fst tm_ty, snd tm_ty)) ?opTriples"
  \<comment> \<open>Extract process_binop_chain success\<close>
  from "6.prems"(1) elab_lhs elab_rhs_list obtain resultTm resultTy where
    process_result: "process_binop_chain loc ghost newLhs lhsTy ?opList = Inr (resultTm, resultTy)"
    and result_eq: "newTm = resultTm" "ty = resultTy"
    by (auto simp: Let_def split: sum.splits)
  \<comment> \<open>IH on LHS: newLhs has type lhsTy\<close>
  have lhs_typing: "core_term_type env ghost newLhs = Some lhsTy"
    using "6.IH"(1)[OF elab_lhs "6.prems"(2,3)] .
  \<comment> \<open>IH on RHS list: each rhsTm has its corresponding type\<close>
  have rhs_typing: "list_all2 (\<lambda>tm ty. core_term_type env ghost tm = Some ty) rhsTms rhsTys"
    by (simp add: "6.IH"(2) "6.prems"(2,3) elab_lhs elab_rhs_list)
  \<comment> \<open>Convert list_all2 on rhsTms/rhsTys to list_all on opList\<close>
  have rhs_len: "length rhsTms = length rhsTys"
    using rhs_typing by (auto dest: list_all2_lengthD)
  have ops_typed: "list_all (\<lambda>(op, tm, ty). core_term_type env ghost tm = Some ty) ?opList"
  proof (unfold list_all_iff, intro ballI, clarify)
    fix op tm tyR
    assume in_set: "(op, tm, tyR) \<in> set ?opList"
    \<comment> \<open>Element of opList comes from zipping operators with (rhsTm, rhsTy) pairs\<close>
    from in_set obtain tmTy where
      tmTy_in: "(op, tmTy) \<in> set (zip (map fst operands) (zip rhsTms rhsTys))" and
      tmTy_eq: "tm = fst tmTy" "tyR = snd tmTy"
      by auto
    from tmTy_in have "tmTy \<in> set (zip rhsTms rhsTys)"
      using set_zip_rightD by metis
    then obtain i where i_bound: "i < length rhsTms" and "i < length rhsTys"
      and tm_eq: "tm = rhsTms ! i" and ty_eq: "tyR = rhsTys ! i"
      using tmTy_eq rhs_len by (auto simp: set_zip in_set_conv_nth)
    thus "core_term_type env ghost tm = Some tyR"
      using rhs_typing by (auto dest: list_all2_nthD)
  qed
  \<comment> \<open>Apply process_binop_chain_correct\<close>
  have "core_term_type env ghost resultTm = Some resultTy"
    using process_binop_chain_correct[OF process_result lhs_typing ops_typed "6.prems"(2)] .
  thus ?case using result_eq by simp

next
  \<comment> \<open>Case: BabTm_Let\<close>
  case (7 env typedefs ghost loc varName rhs body next_mv)
  \<comment> \<open>Extract intermediate results from elaboration\<close>
  from "7.prems"(1) obtain rhsTm rhsTy next_mv1 where
    elab_rhs: "elab_term env typedefs ghost rhs next_mv = Inr (rhsTm, rhsTy, next_mv1)"
    by (auto split: sum.splits)
  from "7.prems"(1) elab_rhs have rhs_ground: "is_ground rhsTy"
    by (auto split: if_splits)
  let ?env' = "env \<lparr> TE_TermVars := fmupd varName rhsTy (TE_TermVars env),
                     TE_GhostVars := (if ghost = Ghost then finsert varName (TE_GhostVars env)
                                      else fminus (TE_GhostVars env) {|varName|}) \<rparr>"
  from "7.prems"(1) elab_rhs rhs_ground obtain bodyTm bodyTy next_mv2 where
    elab_body: "elab_term ?env' typedefs ghost body next_mv1 = Inr (bodyTm, bodyTy, next_mv2)" and
    result_eq: "newTm = CoreTm_Let varName rhsTm bodyTm" "ty = bodyTy"
    by (auto simp: Let_def split: sum.splits)
  \<comment> \<open>IH on rhs: rhsTm has type rhsTy\<close>
  have rhs_typing: "core_term_type env ghost rhsTm = Some rhsTy"
    using "7.IH"(1)[OF elab_rhs "7.prems"(2,3)] .
  \<comment> \<open>Get well-kindedness and runtime properties of rhsTy\<close>
  have rhs_props: "is_well_kinded env rhsTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type rhsTy)"
    using core_term_type_well_kinded_and_runtime[OF rhs_typing "7.prems"(2)] .
  hence rhs_wk: "is_well_kinded env rhsTy" by blast
  \<comment> \<open>Show tyenv_well_formed env'\<close>
  have wf_env': "tyenv_well_formed ?env'"
  proof (cases "ghost = Ghost")
    case True
    then show ?thesis
      using tyenv_well_formed_add_ghost_var[OF "7.prems"(2) rhs_wk rhs_ground] by simp
  next
    case False
    hence rhs_rt: "is_runtime_type rhsTy" using rhs_props GhostOrNot.exhaust by blast
    show ?thesis using False
      tyenv_well_formed_add_var[OF "7.prems"(2) rhs_wk rhs_ground rhs_rt] by simp
  qed
  \<comment> \<open>Show typedefs_well_formed env' typedefs (only depends on TE_TypeVars and TE_Datatypes)\<close>
  have env'_fields: "TE_TypeVars ?env' = TE_TypeVars env"
                     "TE_Datatypes ?env' = TE_Datatypes env" by simp_all
  have wk_eq: "\<And>t. is_well_kinded ?env' t = is_well_kinded env t"
    using is_well_kinded_cong_env[OF env'_fields] by simp
  have td_wf': "typedefs_well_formed ?env' typedefs"
    using "7.prems"(3) unfolding typedefs_well_formed_def by (simp add: wk_eq)
  \<comment> \<open>IH on body: bodyTm has type bodyTy in env'\<close>
  have body_typing: "core_term_type ?env' ghost bodyTm = Some bodyTy"
    using "7.IH"(2) elab_rhs rhs_ground elab_body wf_env' td_wf' by simp
  \<comment> \<open>Combine: core_term_type for CoreTm_Let\<close>
  show ?case
    using rhs_typing rhs_ground body_typing result_eq
    by (simp add: Let_def)
next
  \<comment> \<open>Case: BabTm_Quantifier (undefined)\<close>
  case (8 env typedefs ghost loc quant name varTy tm next_mv)
  then show ?case sorry

next
  \<comment> \<open>Case: BabTm_Call\<close>
  case (9 env typedefs ghost loc callee args next_mv)
  \<comment> \<open>Extract intermediate results from elaboration\<close>
  from "9.prems"(1) obtain fnName tyArgs expArgTypes retType next_mv1 where
    det_call: "determine_fun_call_type env typedefs ghost callee next_mv
               = Inr (fnName, tyArgs, expArgTypes, retType, next_mv1)"
    by (auto split: sum.splits)
  from "9.prems"(1) det_call have len_args: "length args = length expArgTypes"
    by (auto split: if_splits)
  from "9.prems"(1) det_call len_args obtain elabArgTms actualTypes next_mv2 where
    elab_args: "elab_term_list env typedefs ghost args next_mv1 = Inr (elabArgTms, actualTypes, next_mv2)"
    by (auto split: sum.splits)
  from "9.prems"(1) det_call len_args elab_args obtain finalArgTms finalSubst where
    unify_args: "unify_call_args loc fnName 0 elabArgTms actualTypes expArgTypes fmempty
                 = Inr (finalArgTms, finalSubst)"
    by (auto simp: Let_def split: sum.splits)
  from "9.prems"(1) det_call len_args elab_args unify_args have
    result_eq: "newTm = CoreTm_FunctionCall fnName (map (apply_subst finalSubst) tyArgs) finalArgTms"
               "ty = apply_subst finalSubst retType"
    by (auto simp: Let_def)

  \<comment> \<open>Get function info from determine_fun_call_type_correct\<close>
  from determine_fun_call_type_correct[OF det_call "9.prems"(2,3)] obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
    ghost_ok: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost" and
    len_tyargs: "length tyArgs = length (FI_TyArgs funInfo)" and
    tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
    tyargs_rt: "ghost = NotGhost \<longrightarrow> list_all is_runtime_type tyArgs" and
    expArgTypes_eq: "expArgTypes = map (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)))
                                       (FI_TmArgs funInfo)" and
    retType_eq: "retType = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                                       (FI_ReturnType funInfo)"
    by blast

  \<comment> \<open>From IH on elab_term_list: elaborated args have their types\<close>
  have ih_args: "list_all2 (\<lambda>tm ty. core_term_type env ghost tm = Some ty) elabArgTms actualTypes"
    by (simp add: "9.IH" "9.prems"(2,3) det_call elab_args len_args)

  \<comment> \<open>Extract unify_call_types result from unify_call_args\<close>
  obtain unifySubst where
    unify_types: "unify_call_types loc fnName 0 actualTypes expArgTypes fmempty = Inr unifySubst" and
    finalArgTms_eq: "finalArgTms = apply_call_coercions unifySubst elabArgTms actualTypes expArgTypes" and
    finalSubst_eq: "finalSubst = unifySubst"
  proof -
    from unify_args show ?thesis
      by (auto simp: unify_call_args_def split: sum.splits intro: that)
  qed

  \<comment> \<open>Get lengths from list_all2\<close>
  have len_elabArgTms: "length elabArgTms = length actualTypes"
    using ih_args by (simp add: list_all2_lengthD)
  have len_actualTypes: "length actualTypes = length expArgTypes"
    using len_args elab_args by (simp add: elab_term_list_length)

  \<comment> \<open>Need well-kindedness and runtime properties for actualTypes and expArgTypes\<close>
  \<comment> \<open>From ih_args and core_term_type_well_kinded\<close>
  have actualTypes_wk: "list_all (is_well_kinded env) actualTypes"
  proof (simp add: list_all_length, intro allI impI)
    fix i assume "i < length actualTypes"
    with ih_args have "core_term_type env ghost (elabArgTms ! i) = Some (actualTypes ! i)"
      by (simp add: list_all2_conv_all_nth)
    thus "is_well_kinded env (actualTypes ! i)"
      using "9.prems"(2) core_term_type_well_kinded by blast
  qed
  \<comment> \<open>From ih_args and core_term_type_notghost_runtime\<close>
  have actualTypes_rt: "ghost = NotGhost \<longrightarrow> list_all is_runtime_type actualTypes"
    using ih_args "9.prems"(2) core_term_type_notghost_runtime
    by (auto simp: list_all2_conv_all_nth list_all_length)

  \<comment> \<open>expArgTypes are well-kinded and runtime (from function info)\<close>
  have "tyenv_fun_types_well_kinded env"
    using "9.prems"(2) tyenv_well_formed_def by blast
  hence fi_args_wk: "list_all (is_well_kinded env) (FI_TmArgs funInfo)"
    using fn_lookup tyenv_fun_types_well_kinded_def by (simp add: list_all_iff)
  have expArgTypes_wk: "list_all (is_well_kinded env) expArgTypes"
    using expArgTypes_eq fi_args_wk tyargs_wk
    by (simp add: list_all_iff apply_subst_preserves_well_kinded metasubst_well_kinded_from_zip)

  have "tyenv_fun_ghost_constraint env"
    using "9.prems"(2) tyenv_well_formed_def by blast
  hence fi_args_rt: "FI_Ghost funInfo = NotGhost \<longrightarrow> list_all is_runtime_type (FI_TmArgs funInfo)"
    using fn_lookup tyenv_fun_ghost_constraint_def
    by (metis fi_args_wk list.pred_mono_strong)
  have expArgTypes_rt: "ghost = NotGhost \<longrightarrow> list_all is_runtime_type expArgTypes"
  proof
    assume ng: "ghost = NotGhost"
    hence "FI_Ghost funInfo = NotGhost" using GhostOrNot.exhaust ghost_ok by auto
    hence fi_args_rt': "list_all is_runtime_type (FI_TmArgs funInfo)" using fi_args_rt by simp
    have tyargs_rt': "list_all is_runtime_type tyArgs" using tyargs_rt ng by simp
    \<comment> \<open>Build a runtime-preserving substitution from tyArgs\<close>
    have subst_rt: "\<forall>ty \<in> fmran' (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)). is_runtime_type ty"
    proof
      fix ty assume "ty \<in> fmran' (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))"
      then obtain var where lookup: "fmlookup (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) var = Some ty"
        by (auto simp: fmran'_def)
      hence "map_of (zip (FI_TyArgs funInfo) tyArgs) var = Some ty"
        by (simp add: fmlookup_of_list)
      hence "(var, ty) \<in> set (zip (FI_TyArgs funInfo) tyArgs)"
        by (simp add: map_of_SomeD)
      then obtain i where "i < length (FI_TyArgs funInfo)" "i < length tyArgs"
                     and "ty = tyArgs ! i"
        using len_tyargs by (auto simp: set_zip)
      thus "is_runtime_type ty"
        using tyargs_rt' by (simp add: list_all_length)
    qed
    show "list_all is_runtime_type expArgTypes"
      using expArgTypes_eq fi_args_rt' subst_rt
      by (simp add: list_all_iff apply_subst_preserves_runtime)
  qed

  \<comment> \<open>Apply unify_call_types_correct\<close>
  have unify_correct: "(\<forall>ty \<in> fmran' finalSubst. is_well_kinded env ty)
       \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type ty))
       \<and> (\<exists>theta. finalSubst = compose_subst theta fmempty)
       \<and> list_all2 (\<lambda>actualTy expectedTy.
           apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
           \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
              \<and> is_finite_integer_type (apply_subst finalSubst expectedTy)))
         actualTypes expArgTypes"
    using unify_call_types_correct[OF unify_types "9.prems"(2) len_actualTypes
            actualTypes_wk expArgTypes_wk _ actualTypes_rt expArgTypes_rt]
          finalSubst_eq by fastforce

  from unify_correct have
    finalSubst_wk: "\<forall>ty \<in> fmran' finalSubst. is_well_kinded env ty" and
    finalSubst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type ty)" and
    types_unified: "list_all2 (\<lambda>actualTy expectedTy.
           apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
           \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
              \<and> is_finite_integer_type (apply_subst finalSubst expectedTy)))
         actualTypes expArgTypes"
    by blast+

  \<comment> \<open>Apply apply_call_coercions_correct\<close>
  have coerce_correct: "list_all2 (\<lambda>tm expectedTy.
           core_term_type env ghost tm = Some (apply_subst finalSubst expectedTy))
         finalArgTms expArgTypes"
    using apply_call_coercions_correct[OF ih_args types_unified "9.prems"(2)
            finalSubst_wk finalSubst_rt len_elabArgTms len_actualTypes]
          finalArgTms_eq finalSubst_eq by simp

  \<comment> \<open>The final type args in the output term\<close>
  let ?finalTyArgs = "map (apply_subst finalSubst) tyArgs"

  \<comment> \<open>Show finalTyArgs are well-kinded\<close>
  have finalTyArgs_wk: "list_all (is_well_kinded env) ?finalTyArgs"
    using tyargs_wk finalSubst_wk
    by (simp add: list_all_iff apply_subst_preserves_well_kinded metasubst_well_kinded_def fmran'_def)

  \<comment> \<open>Show finalTyArgs are runtime if NotGhost\<close>
  have finalTyArgs_rt: "ghost = NotGhost \<longrightarrow> list_all is_runtime_type ?finalTyArgs"
    using tyargs_rt finalSubst_rt
    by (auto simp: list_all_iff apply_subst_preserves_runtime)

  \<comment> \<open>Length of finalTyArgs matches\<close>
  have len_finalTyArgs: "length ?finalTyArgs = length (FI_TyArgs funInfo)"
    using len_tyargs by simp

  \<comment> \<open>The substitution used in core_term_type\<close>
  let ?coreTySubst = "fmap_of_list (zip (FI_TyArgs funInfo) ?finalTyArgs)"

  \<comment> \<open>Expected arg types in core_term_type\<close>
  let ?coreExpArgTypes = "map (apply_subst ?coreTySubst) (FI_TmArgs funInfo)"

  \<comment> \<open>Function arg types have metavars only from FI_TyArgs\<close>
  have "tyenv_funs_have_expected_metavars env"
    using "9.prems"(2) tyenv_well_formed_def by blast
  hence fi_args_metavars: "\<forall>ty \<in> set (FI_TmArgs funInfo). type_metavars ty \<subseteq> set (FI_TyArgs funInfo)"
    using fn_lookup tyenv_funs_have_expected_metavars_def by blast

  \<comment> \<open>Function type args are distinct\<close>
  have "tyenv_fun_metavars_distinct env"
    using "9.prems"(2) tyenv_well_formed_def by blast
  hence fi_tyargs_distinct: "distinct (FI_TyArgs funInfo)"
    using fn_lookup tyenv_fun_metavars_distinct_def by blast

  \<comment> \<open>Key: ?coreExpArgTypes = map (apply_subst finalSubst) expArgTypes\<close>
  have core_exp_eq: "?coreExpArgTypes = map (apply_subst finalSubst) expArgTypes"
    using expArgTypes_eq len_tyargs fi_args_metavars fi_tyargs_distinct
    by (simp add: map_apply_subst_compose_zip)

  \<comment> \<open>From coerce_correct, finalArgTms have these types\<close>
  have args_match: "list_all2 (\<lambda>tm expectedTy.
           case core_term_type env ghost tm of
             None \<Rightarrow> False
           | Some actualTy \<Rightarrow> actualTy = expectedTy)
         finalArgTms ?coreExpArgTypes"
  proof -
    have "list_all2 (\<lambda>tm expectedTy.
             core_term_type env ghost tm = Some expectedTy)
           finalArgTms (map (apply_subst finalSubst) expArgTypes)"
      using coerce_correct by (simp add: list_all2_conv_all_nth)
    thus ?thesis
      using core_exp_eq by (simp add: list_all2_conv_all_nth)
  qed

  \<comment> \<open>Length of finalArgTms\<close>
  have len_finalArgTms: "length finalArgTms = length (FI_TmArgs funInfo)"
    using coerce_correct expArgTypes_eq by (simp add: list_all2_lengthD)

  \<comment> \<open>Return type - need metavars assumption from tyenv_funs_have_expected_metavars\<close>
  have fi_ret_metavars: "type_metavars (FI_ReturnType funInfo) \<subseteq> set (FI_TyArgs funInfo)"
    using \<open>tyenv_funs_have_expected_metavars env\<close> fn_lookup
    by (simp add: tyenv_funs_have_expected_metavars_def)
  have ret_eq: "ty = apply_subst ?coreTySubst (FI_ReturnType funInfo)"
    using result_eq retType_eq len_tyargs fi_ret_metavars fi_tyargs_distinct
    by (simp add: apply_subst_compose_zip)

  \<comment> \<open>Put it all together\<close>
  show ?case
    using result_eq fn_lookup ghost_ok len_finalTyArgs finalTyArgs_wk finalTyArgs_rt
          len_finalArgTms args_match ret_eq
    by (auto simp: Let_def)

next
  \<comment> \<open>Case: BabTm_Tuple (undefined)\<close>
  case (10 env typedefs ghost loc tms next_mv)
  then show ?case sorry
next
  \<comment> \<open>Case: BabTm_Record (undefined)\<close>
  case (11 env typedefs ghost loc flds next_mv)
  then show ?case sorry
next
  \<comment> \<open>Case: BabTm_RecordUpdate (undefined)\<close>
  case (12 env typedefs ghost loc tm flds next_mv)
  then show ?case sorry
next
  \<comment> \<open>Case: BabTm_TupleProj (undefined)\<close>
  case (13 env typedefs ghost loc tm idx next_mv)
  then show ?case sorry
next
  \<comment> \<open>Case: BabTm_RecordProj (undefined)\<close>
  case (14 env typedefs ghost loc tm fldName next_mv)
  then show ?case sorry
next
  \<comment> \<open>Case: BabTm_ArrayProj (undefined)\<close>
  case (15 env typedefs ghost loc tm idxs next_mv)
  then show ?case sorry
next
  \<comment> \<open>Case: BabTm_Match (undefined)\<close>
  case (16 env typedefs ghost loc scrut arms next_mv)
  then show ?case sorry
next
  \<comment> \<open>Case: BabTm_Sizeof (undefined)\<close>
  case (17 env typedefs ghost loc tm next_mv)
  then show ?case sorry
next
  \<comment> \<open>Case: BabTm_Allocated (undefined)\<close>
  case (18 env typedefs ghost loc tm next_mv)
  then show ?case sorry
next
  \<comment> \<open>Case: BabTm_Old (undefined)\<close>
  case (19 env typedefs ghost loc tm next_mv)
  then show ?case sorry
next
  \<comment> \<open>Case: elab_term_list empty\<close>
  case (20 env typedefs ghost next_mv)
  from "20.prems"(1) have "newTms = []" and "tys = []" by simp_all
  thus ?case by simp
next
  \<comment> \<open>Case: elab_term_list cons\<close>
  case (21 env typedefs ghost tm tms next_mv)
  from "21.prems"(1) obtain tm' ty' next_mv1 tms' tys' next_mv'' where
    elab_head: "elab_term env typedefs ghost tm next_mv = Inr (tm', ty', next_mv1)" and
    elab_tail: "elab_term_list env typedefs ghost tms next_mv1 = Inr (tms', tys', next_mv'')" and
    results: "newTms = tm' # tms'" "tys = ty' # tys'"
    by (auto split: sum.splits)
  \<comment> \<open>Apply IH for head\<close>
  have ih_head: "core_term_type env ghost tm' = Some ty'"
    using "21.IH"(1) elab_head "21.prems"(2,3) by simp
  \<comment> \<open>Apply IH for tail\<close>
  have ih_tail: "list_all2 (\<lambda>tm ty. core_term_type env ghost tm = Some ty) tms' tys'"
    using "21.IH"(3) elab_head elab_tail "21.prems"(2,3) by simp
  show ?case using ih_head ih_tail results by simp
qed

end
