theory CoreTermTypeMode
  imports CoreStmtTypecheck
begin

(* ========================================================================== *)
(* NotGhost typing implies Ghost typing, for terms *)
(* ========================================================================== *)

(* A term that typechecks in some mode also typechecks in Ghost mode,
   in any env whose ghost locals include the original ones. *)
lemma core_term_type_ghost_weaken:
  assumes "core_term_type env ghost tm = Some ty"
      and "TE_GhostLocals env |\<subseteq>| G"
  shows "core_term_type (env \<lparr> TE_GhostLocals := G \<rparr>) Ghost tm = Some ty"
using assms proof (induction tm arbitrary: env ghost ty G)
  case (CoreTm_Var name)
  have lookup_eq: "tyenv_lookup_var (env \<lparr> TE_GhostLocals := G \<rparr>) name = tyenv_lookup_var env name"
    unfolding tyenv_lookup_var_def by (simp split: option.splits)
  from CoreTm_Var.prems(1) show ?case
    by (simp add: lookup_eq split: option.splits if_splits)
next
  case (CoreTm_Let var rhs body)
  let ?envG = "env \<lparr> TE_GhostLocals := G \<rparr>"
  from CoreTm_Let.prems(1) obtain rhsTy where
    rhs_ty: "core_term_type env ghost rhs = Some rhsTy" and
    body_ty: "core_term_type
      (env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
             TE_GhostLocals := (if ghost = Ghost then finsert var (TE_GhostLocals env)
                                 else fminus (TE_GhostLocals env) {|var|}),
             TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>)
      ghost body = Some ty"
    by (auto simp: Let_def split: option.splits)
  from CoreTm_Let.IH(1)[OF rhs_ty CoreTm_Let.prems(2)]
  have rhs_ty': "core_term_type ?envG Ghost rhs = Some rhsTy" .
  let ?body_env = "env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                        TE_GhostLocals := (if ghost = Ghost then finsert var (TE_GhostLocals env)
                                            else fminus (TE_GhostLocals env) {|var|}),
                        TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
  have sub_body: "TE_GhostLocals ?body_env |\<subseteq>| finsert var G"
    using CoreTm_Let.prems(2) by auto
  from CoreTm_Let.IH(2)[OF body_ty sub_body]
  have body_ty': "core_term_type (?body_env \<lparr> TE_GhostLocals := finsert var G \<rparr>) Ghost body = Some ty" .
  have env_eq: "?body_env \<lparr> TE_GhostLocals := finsert var G \<rparr>
                = ?envG \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars ?envG),
                          TE_GhostLocals := finsert var (TE_GhostLocals ?envG),
                          TE_ConstLocals := finsert var (TE_ConstLocals ?envG) \<rparr>"
    by simp
  from body_ty' env_eq rhs_ty' show ?case by (simp add: Let_def)
next
  case (CoreTm_Quantifier quant var varTy body)
  show ?case
  proof (cases ghost)
    case NotGhost
    with CoreTm_Quantifier.prems(1) show ?thesis by simp
  next
    case Ghost
    let ?envG = "env \<lparr> TE_GhostLocals := G \<rparr>"
    from Ghost CoreTm_Quantifier.prems(1) have wk: "is_well_kinded env varTy"
      by (auto simp: Let_def split: option.splits if_splits CoreType.splits)
    have wk': "is_well_kinded ?envG varTy"
      using wk is_well_kinded_cong_env[of ?envG env] by simp
    from Ghost CoreTm_Quantifier.prems(1) obtain bodyTy where
      body_ty: "core_term_type
        (env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
               TE_GhostLocals := finsert var (TE_GhostLocals env) \<rparr>)
        Ghost body = Some bodyTy"
      and ty_eq: "ty = CoreTy_Bool" and body_bool: "bodyTy = CoreTy_Bool"
      by (auto simp: Let_def split: option.splits if_splits CoreType.splits)
    let ?body_env = "env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                          TE_GhostLocals := finsert var (TE_GhostLocals env) \<rparr>"
    have sub_body: "TE_GhostLocals ?body_env |\<subseteq>| finsert var G"
      using CoreTm_Quantifier.prems(2) by auto
    from CoreTm_Quantifier.IH[OF body_ty sub_body]
    have body_ty': "core_term_type (?body_env \<lparr> TE_GhostLocals := finsert var G \<rparr>) Ghost body
                      = Some bodyTy" .
    have env_eq: "?body_env \<lparr> TE_GhostLocals := finsert var G \<rparr>
                  = ?envG \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars ?envG),
                            TE_GhostLocals := finsert var (TE_GhostLocals ?envG) \<rparr>"
      by simp
    from body_ty' env_eq body_bool ty_eq wk' show ?thesis by (simp add: Let_def)
  qed
next
  case (CoreTm_LitBool b) then show ?case by simp
next
  case (CoreTm_LitInt i) then show ?case by (auto split: option.splits)
next
  case (CoreTm_LitArray elemTy tms)
  let ?envG = "env \<lparr> TE_GhostLocals := G \<rparr>"
  have wk_eq: "is_well_kinded ?envG elemTy = is_well_kinded env elemTy"
    using is_well_kinded_cong_env[of ?envG env] by simp
  from CoreTm_LitArray.IH CoreTm_LitArray.prems(2)
  have "\<forall>tm \<in> set tms. \<forall>ty. core_term_type env ghost tm = Some ty \<longrightarrow>
      core_term_type ?envG Ghost tm = Some ty" by blast
  then show ?case using CoreTm_LitArray.prems(1) wk_eq
    by (auto simp: list_all_iff split: if_splits)
next
  case (CoreTm_Cast targetTy tm)
  let ?envG = "env \<lparr> TE_GhostLocals := G \<rparr>"
  have co_eq: "\<And>a b. cast_ok ?envG a b = cast_ok env a b"
    using cast_ok_cong_env[of ?envG env] by simp
  from CoreTm_Cast show ?case by (auto simp: co_eq split: option.splits if_splits)
next
  case (CoreTm_Unop op tm)
  from CoreTm_Unop.prems(1) obtain operandTy where
    op_ty: "core_term_type env ghost tm = Some operandTy"
    by (auto split: option.splits)
  from CoreTm_Unop.IH[OF op_ty CoreTm_Unop.prems(2)]
  have op_ty': "core_term_type (env \<lparr> TE_GhostLocals := G \<rparr>) Ghost tm = Some operandTy" .
  from CoreTm_Unop.prems(1) show ?case using op_ty op_ty'
    by (auto split: option.splits)
next
  case (CoreTm_Binop op lhs rhs)
  from CoreTm_Binop.prems(1) obtain lhsTy rhsTy where
    lhs_ty: "core_term_type env ghost lhs = Some lhsTy" and
    rhs_ty: "core_term_type env ghost rhs = Some rhsTy"
    by (auto split: option.splits prod.splits)
  from CoreTm_Binop.IH(1)[OF lhs_ty CoreTm_Binop.prems(2)]
  have lhs_ty': "core_term_type (env \<lparr> TE_GhostLocals := G \<rparr>) Ghost lhs = Some lhsTy" .
  from CoreTm_Binop.IH(2)[OF rhs_ty CoreTm_Binop.prems(2)]
  have rhs_ty': "core_term_type (env \<lparr> TE_GhostLocals := G \<rparr>) Ghost rhs = Some rhsTy" .
  from CoreTm_Binop.prems(1) show ?case using lhs_ty lhs_ty' rhs_ty rhs_ty'
    by (auto split: option.splits if_splits)
next
  case (CoreTm_FunctionCall fnName tyArgs tmArgs)
  let ?envG = "env \<lparr> TE_GhostLocals := G \<rparr>"
  have wk_eq: "\<And>t. is_well_kinded ?envG t = is_well_kinded env t"
    using is_well_kinded_cong_env[of ?envG env] by simp
  from CoreTm_FunctionCall.IH CoreTm_FunctionCall.prems(2)
  have IH: "\<forall>tm \<in> set tmArgs. \<forall>mode ty. core_term_type env mode tm = Some ty \<longrightarrow>
      core_term_type ?envG Ghost tm = Some ty" by blast
  from CoreTm_FunctionCall.prems(1) obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
    len_tyargs: "length tyArgs = length (FI_TyArgs funInfo)" and
    tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
    tyargs_cp: "list_all is_complete_type tyArgs" and
    len_tmargs: "length tmArgs = length (FI_TmArgs funInfo)" and
    not_impure: "\<not> FI_Impure funInfo" and
    all_var: "list_all (\<lambda>(_, vor, _). vor = Var) (FI_TmArgs funInfo)" and
    la2: "list_all2 (\<lambda>tm (expectedTy, mode). core_term_type env mode tm = Some expectedTy) tmArgs
            (zip (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                      (FI_TmArgs funInfo))
                 (map (\<lambda>(_, _, gh). param_mode ghost gh) (FI_TmArgs funInfo)))" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo)"
    by (auto simp: Let_def split: option.splits if_splits)
  let ?exps = "map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                   (FI_TmArgs funInfo)"
  let ?modes = "map (\<lambda>(_, _, gh). param_mode ghost gh) (FI_TmArgs funInfo)"
  let ?modesG = "map (\<lambda>(_, _, gh). param_mode Ghost gh) (FI_TmArgs funInfo)"
  \<comment> \<open>Every argument is now checked in Ghost mode, whatever mode it was
      checked in before.\<close>
  have la2': "list_all2 (\<lambda>tm (expectedTy, mode).
                  core_term_type ?envG mode tm = Some expectedTy) tmArgs (zip ?exps ?modesG)"
    unfolding list_all2_case_prod_conv_all_nth
  proof (intro conjI allI impI)
    show "length tmArgs = length (zip ?exps ?modesG)" using len_tmargs by simp
  next
    fix i assume i_lt: "i < length tmArgs"
    with len_tmargs have i_lt_fi: "i < length (FI_TmArgs funInfo)" by simp
    obtain ti vor gh where fi_arg: "FI_TmArgs funInfo ! i = (ti, vor, gh)"
      by (cases "FI_TmArgs funInfo ! i") auto
    have exp_nth: "zip ?exps ?modes ! i
                     = (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ti, param_mode ghost gh)"
      using i_lt_fi fi_arg by simp
    have expG_nth: "zip ?exps ?modesG ! i
                      = (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ti, Ghost)"
      using i_lt_fi fi_arg by simp
    have "core_term_type env (param_mode ghost gh) (tmArgs ! i)
            = Some (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ti)"
      using list_all2_case_prod_nthD[OF la2 i_lt] exp_nth by simp
    hence "core_term_type ?envG Ghost (tmArgs ! i)
             = Some (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ti)"
      using IH i_lt by (blast intro: nth_mem)
    thus "core_term_type ?envG (snd (zip ?exps ?modesG ! i)) (tmArgs ! i)
            = Some (fst (zip ?exps ?modesG ! i))"
      using expG_nth by simp
  qed
  have fn_lookup': "fmlookup (TE_Functions ?envG) fnName = Some funInfo"
    using fn_lookup by simp
  have tyargs_wk': "list_all (is_well_kinded ?envG) tyArgs"
    using tyargs_wk by (simp add: list_all_iff wk_eq)
  \<comment> \<open>simp does not rewrite under the pattern-lambda, so normalise the mode
      list explicitly.\<close>
  have modesG_simp: "?modesG = map (\<lambda>(_, _, _). Ghost) (FI_TmArgs funInfo)"
    by (rule map_cong[OF refl]) (auto split: prod.splits)
  show ?case
    using fn_lookup' len_tyargs tyargs_wk' tyargs_cp len_tmargs not_impure all_var la2' ty_eq
    by (auto simp: Let_def modesG_simp)
next
  case (CoreTm_VariantCtor ctorName tyArgs payload)
  let ?envG = "env \<lparr> TE_GhostLocals := G \<rparr>"
  have wk_eq: "\<And>t. is_well_kinded ?envG t = is_well_kinded env t"
    using is_well_kinded_cong_env[of ?envG env] by simp
  then show ?case using CoreTm_VariantCtor.prems CoreTm_VariantCtor.IH
    by (auto simp: wk_eq list_all_iff split: option.splits if_splits)
next
  case (CoreTm_Record flds)
  let ?envG = "env \<lparr> TE_GhostLocals := G \<rparr>"
  from CoreTm_Record.prems(1) obtain tys where
    distinct_names: "distinct (map fst flds)" and
    those_eq: "those (map (\<lambda>(name, tm). core_term_type env ghost tm) flds) = Some tys" and
    ty_eq: "ty = CoreTy_Record (zip (map fst flds) tys)"
    by (auto split: option.splits if_splits)
  from those_eq have la2: "list_all2 (\<lambda>x y. x = Some y)
      (map (\<lambda>(name, tm). core_term_type env ghost tm) flds) tys"
    using those_eq_Some by blast
  hence len_eq: "length flds = length tys" by (auto dest: list_all2_lengthD)
  have "\<And>i. i < length flds \<Longrightarrow> core_term_type ?envG Ghost (snd (flds ! i)) =
        core_term_type env ghost (snd (flds ! i))"
  proof -
    fix i assume "i < length flds"
    obtain nm tm where p_eq: "flds ! i = (nm, tm)" by (cases "flds ! i") auto
    from \<open>i < length flds\<close> have "flds ! i \<in> set flds" by simp
    from la2 \<open>i < length flds\<close> len_eq
    have "core_term_type env ghost tm = Some (tys ! i)"
      by (auto dest: list_all2_nthD simp: p_eq)
    from p_eq have "tm \<in> Basic_BNFs.snds (flds ! i)" by simp
    from CoreTm_Record.IH[OF \<open>flds ! i \<in> set flds\<close> this
        \<open>core_term_type env ghost tm = Some (tys ! i)\<close> CoreTm_Record.prems(2)]
    have "core_term_type ?envG Ghost tm = Some (tys ! i)" .
    with \<open>core_term_type env ghost tm = Some (tys ! i)\<close>
    show "core_term_type ?envG Ghost (snd (flds ! i)) = core_term_type env ghost (snd (flds ! i))"
      by (simp add: p_eq)
  qed
  hence map_eq: "map (\<lambda>(name, tm). core_term_type ?envG Ghost tm) flds =
                 map (\<lambda>(name, tm). core_term_type env ghost tm) flds"
    by (metis (mono_tags, lifting) map_equality_iff split_beta)
  show ?case by (simp add: map_eq those_eq ty_eq distinct_names)
next
  case (CoreTm_RecordProj tm fldName) then show ?case
    by (auto split: option.splits CoreType.splits)
next
  case (CoreTm_VariantProj tm ctorName) then show ?case
    by (auto split: option.splits CoreType.splits)
next
  case (CoreTm_ArrayProj arr idxs)
  let ?envG = "env \<lparr> TE_GhostLocals := G \<rparr>"
  from CoreTm_ArrayProj.prems(1) obtain elemTy dims where
    arr_ty: "core_term_type env ghost arr = Some (CoreTy_Array elemTy dims)"
    by (auto split: option.splits CoreType.splits if_splits)
  from CoreTm_ArrayProj.IH(1)[OF arr_ty CoreTm_ArrayProj.prems(2)]
  have arr_ty': "core_term_type ?envG Ghost arr = Some (CoreTy_Array elemTy dims)" .
  have idx_transfer: "\<And>tm. tm \<in> set idxs \<Longrightarrow>
      core_term_type env ghost tm = Some (CoreTy_FiniteInt Unsigned IntBits_64) \<Longrightarrow>
      core_term_type ?envG Ghost tm = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
    using CoreTm_ArrayProj.IH(2) CoreTm_ArrayProj.prems(2) by blast
  from CoreTm_ArrayProj.prems(1) show ?case using arr_ty arr_ty' idx_transfer
    by (auto simp: list_all_iff split: option.splits CoreType.splits if_splits)
next
  case (CoreTm_Match scrut arms)
  let ?envG = "env \<lparr> TE_GhostLocals := G \<rparr>"
  have pc_eq: "\<And>p t. pattern_compatible ?envG p t = pattern_compatible env p t"
    by (rule pattern_compatible_cong_env) simp
  from CoreTm_Match.prems(1) obtain scrutTy where
    scrut_ty: "core_term_type env ghost scrut = Some scrutTy"
    by (auto split: option.splits)
  from CoreTm_Match.IH(1)[OF scrut_ty CoreTm_Match.prems(2)]
  have scrut_ty': "core_term_type ?envG Ghost scrut = Some scrutTy" .
  have body_transfer: "\<And>arm body resultTy. arm \<in> set arms \<Longrightarrow> body = snd arm \<Longrightarrow>
      core_term_type env ghost body = Some resultTy \<Longrightarrow>
      core_term_type ?envG Ghost body = Some resultTy"
  proof -
    fix arm body resultTy
    assume "arm \<in> set arms" and "body = snd arm"
      and body_ty: "core_term_type env ghost body = Some resultTy"
    have "body \<in> Basic_BNFs.snds arm"
      using \<open>body = snd arm\<close> by (cases arm) simp
    from CoreTm_Match.IH(2)[OF \<open>arm \<in> set arms\<close> \<open>body \<in> Basic_BNFs.snds arm\<close>
        body_ty CoreTm_Match.prems(2)]
    show "core_term_type ?envG Ghost body = Some resultTy" .
  qed
  have hd_transfer: "arms \<noteq> [] \<Longrightarrow> core_term_type env ghost (snd (hd arms)) = Some resultTy \<Longrightarrow>
      core_term_type ?envG Ghost (snd (hd arms)) = Some resultTy" for resultTy
    using body_transfer[of "hd arms" "snd (hd arms)"] by (cases arms) auto
  have tl_transfer: "\<And>body resultTy. body \<in> set (tl (map snd arms)) \<Longrightarrow>
      core_term_type env ghost body = Some resultTy \<Longrightarrow>
      core_term_type ?envG Ghost body = Some resultTy"
  proof -
    fix body resultTy
    assume "body \<in> set (tl (map snd arms))"
      and body_ty: "core_term_type env ghost body = Some resultTy"
    from \<open>body \<in> set (tl (map snd arms))\<close> obtain arm where
      "arm \<in> set arms" and "body = snd arm" by (cases arms) auto
    from body_transfer[OF this body_ty]
    show "core_term_type ?envG Ghost body = Some resultTy" .
  qed
  from CoreTm_Match.prems(1) show ?case
    using scrut_ty scrut_ty' pc_eq hd_transfer tl_transfer
    by (auto simp: list_all_iff Let_def split: option.splits if_splits)
next
  case (CoreTm_Sizeof tm) then show ?case
    by (auto split: option.splits CoreType.splits if_splits)
next
  case (CoreTm_Allocated tm)
  then show ?case
    by (cases ghost) (auto split: option.splits if_splits)
next
  case (CoreTm_Old tm)
  then show ?case
    by (cases ghost) auto
next
  case (CoreTm_Default tyD)
  let ?envG = "env \<lparr> TE_GhostLocals := G \<rparr>"
  have wk_eq: "is_well_kinded ?envG tyD = is_well_kinded env tyD"
    using is_well_kinded_cong_env[of ?envG env] by simp
  from CoreTm_Default.prems(1) show ?case
    by (metis GhostOrNot.distinct(1) core_term_type.simps(23) option.distinct(1) wk_eq)
qed

(* A term that types in NotGhost mode also types in Ghost mode. *)
corollary core_term_type_NotGhost_imp_Ghost:
  assumes "core_term_type env ghost tm = Some ty"
  shows "core_term_type env Ghost tm = Some ty"
  using core_term_type_ghost_weaken[OF assms, of "TE_GhostLocals env"] by simp


(* ========================================================================== *)
(* Typechecking of CoreTm_FunctionCall *)
(* ========================================================================== *)

(* If the per-argument typecheck done while typing a CoreTm_FunctionCall succeeds (in
   any modes), then the args all have their expected types in *Ghost* mode. *)
lemma args_typed_imp_Ghost:
  assumes typed: "list_all2 (\<lambda>tm (expectedTy, mode). core_term_type env mode tm = Some expectedTy)
                    tmArgs (zip expectedTys modes)"
    and len: "length expectedTys = length modes"
  shows "list_all2 (\<lambda>tm expectedTy. core_term_type env Ghost tm = Some expectedTy)
           tmArgs expectedTys"
  unfolding list_all2_conv_all_nth
proof (intro conjI allI impI)
  show "length tmArgs = length expectedTys"
    using list_all2_lengthD[OF typed] len by simp
next
  fix i assume i_lt: "i < length tmArgs"
  have i_exp: "i < length expectedTys" and i_modes: "i < length modes"
    using list_all2_lengthD[OF typed] len i_lt by simp_all
  from list_all2_case_prod_nthD[OF typed i_lt] i_exp i_modes
  have t: "core_term_type env (modes ! i) (tmArgs ! i) = Some (expectedTys ! i)"
    by simp
  from core_term_type_NotGhost_imp_Ghost[OF t]
  show "core_term_type env Ghost (tmArgs ! i) = Some (expectedTys ! i)"
    by simp
qed

(* Conversely, if a call's args all have their expected types, in either Ghost mode or the
   ambient mode, then the per-argument typecheck done while typing a CoreTm_FunctionCall
   will succeed. *)
lemma args_typed_weaken_modes:
  assumes typed: "list_all2 (\<lambda>tm expectedTy. core_term_type env ghost tm = Some expectedTy)
                    tmArgs expectedTys"
      and len: "length expectedTys = length modes"
      and modes: "\<And>m. m \<in> set modes \<Longrightarrow> m = ghost \<or> m = Ghost"
  shows "list_all2 (\<lambda>tm (expectedTy, mode). core_term_type env mode tm = Some expectedTy)
           tmArgs (zip expectedTys modes)"
  unfolding list_all2_case_prod_conv_all_nth
proof (intro conjI allI impI)
  show "length tmArgs = length (zip expectedTys modes)"
    using list_all2_lengthD[OF typed] len by simp
next
  fix i assume i_lt: "i < length tmArgs"
  hence i_exp: "i < length expectedTys" and i_modes: "i < length modes"
    using list_all2_lengthD[OF typed] len by simp_all
  have t: "core_term_type env ghost (tmArgs ! i) = Some (expectedTys ! i)"
    using list_all2_nthD[OF typed i_lt] .
  have "core_term_type env (modes ! i) (tmArgs ! i) = Some (expectedTys ! i)"
    using modes[OF nth_mem[OF i_modes]] t core_term_type_NotGhost_imp_Ghost[OF t] by auto
  thus "core_term_type env (snd (zip expectedTys modes ! i)) (tmArgs ! i)
          = Some (fst (zip expectedTys modes ! i))"
    using i_exp i_modes by simp
qed

(* If a CoreTm_FunctionCall typechecks (in any mode), we can deduce that its arguments
   all typecheck (in Ghost mode) at the expected types, and the type of the term overall
   is the function's return type. *)
lemma core_term_type_FunctionCall_args_Ghost:
  assumes typing: "core_term_type env ghost (CoreTm_FunctionCall fnName tyArgs tmArgs) = Some ty"
    and fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo"
  shows "list_all2 (\<lambda>tm expectedTy. core_term_type env Ghost tm = Some expectedTy)
          tmArgs
          (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
               (FI_TmArgs funInfo))"
    and "ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo)"
proof -
  from typing fn_lookup have
    la2: "list_all2 (\<lambda>tm (expectedTy, mode). core_term_type env mode tm = Some expectedTy) tmArgs
            (zip (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                      (FI_TmArgs funInfo))
                 (map (\<lambda>(_, _, gh). param_mode ghost gh) (FI_TmArgs funInfo)))"
    and ty_eq: "ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo)"
    by (auto simp: Let_def split: option.splits if_splits)
  show "list_all2 (\<lambda>tm expectedTy. core_term_type env Ghost tm = Some expectedTy)
          tmArgs
          (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
               (FI_TmArgs funInfo))"
    by (rule args_typed_imp_Ghost[OF la2]) simp
  show "ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo)"
    using ty_eq by simp
qed


(* ========================================================================== *)
(* Typechecking of impure calls and casts *)
(* ========================================================================== *)

(* What a typed impure call says about its function and its arguments, with the
   arguments typed in Ghost mode. (As core_impure_call_type_fn_facts, without
   the facts that depend on the mode.) *)
lemma core_impure_call_type_fn_facts_Ghost:
  assumes "core_impure_call_type env ghost fnName tyArgs tmArgs = Some ty"
  shows "\<exists>funInfo.
            fmlookup (TE_Functions env) fnName = Some funInfo
            \<and> length tyArgs = length (FI_TyArgs funInfo)
            \<and> list_all (is_well_kinded env) tyArgs
            \<and> list_all is_complete_type tyArgs
            \<and> length tmArgs = length (FI_TmArgs funInfo)
            \<and> ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                               (FI_ReturnType funInfo)
            \<and> list_all2 (\<lambda>tm expectedTy.
                  core_term_type env Ghost tm = Some expectedTy)
                tmArgs
                (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo))
            \<and> (\<forall>i < length tmArgs.
                 fst (snd (FI_TmArgs funInfo ! i)) = Ref
                   \<longrightarrow> is_writable_lvalue env (tmArgs ! i))"
proof -
  from core_impure_call_type_fn_facts[OF assms] obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
    len_ty: "length tyArgs = length (FI_TyArgs funInfo)" and
    wk: "list_all (is_well_kinded env) tyArgs" and
    cp: "list_all is_complete_type tyArgs" and
    len_tm: "length tmArgs = length (FI_TmArgs funInfo)" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                             (FI_ReturnType funInfo)" and
    args: "list_all2 (\<lambda>tm (expectedTy, mode). core_term_type env mode tm = Some expectedTy) tmArgs
                (zip (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                          (FI_TmArgs funInfo))
                     (map (\<lambda>(_, _, gh). param_mode ghost gh) (FI_TmArgs funInfo)))" and
    refs: "\<forall>i < length tmArgs.
                 fst (snd (FI_TmArgs funInfo ! i)) = Ref
                   \<longrightarrow> is_writable_lvalue env (tmArgs ! i)
                       \<and> ghost_lvalue_ok env (param_mode ghost (snd (snd (FI_TmArgs funInfo ! i))))
                                          (tmArgs ! i)"
    by blast
  have args_g: "list_all2 (\<lambda>tm expectedTy. core_term_type env Ghost tm = Some expectedTy)
                tmArgs
                (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo))"
    by (rule args_typed_imp_Ghost[OF args]) simp
  from refs have refs_g: "\<forall>i < length tmArgs.
                 fst (snd (FI_TmArgs funInfo ! i)) = Ref
                   \<longrightarrow> is_writable_lvalue env (tmArgs ! i)"
    by blast
  from fn_lookup len_ty wk cp len_tm ty_eq args_g refs_g show ?thesis by blast
qed

(* cast_result_type in any mode implies cast_result_type in Ghost mode. *)
lemma cast_result_type_imp_Ghost:
  assumes "cast_result_type env ghost retTy castOpt = Some ty"
  shows "cast_result_type env Ghost retTy castOpt = Some ty"
  using assms by (auto simp: cast_result_type_def split: option.splits if_splits)


(* ========================================================================== *)
(* Well-formedness of the environment after a Ghost-mode declaration *)
(* ========================================================================== *)

(* Declaring a ghost local: the variable is added to TE_LocalVars and
   TE_GhostLocals, and TE_ConstLocals changes. (This is the environment that
   Ghost-mode typing gives to the body of a Let, and to the statements after an
   Obtain.) *)
lemma tyenv_well_formed_declare_ghost:
  assumes "tyenv_well_formed env"
    and "is_well_kinded env ty"
  shows "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd var ty (TE_LocalVars env),
                                 TE_GhostLocals := finsert var (TE_GhostLocals env),
                                 TE_ConstLocals := c \<rparr>)"
  by (rule tyenv_well_formed_TE_ConstLocals_irrelevant
             [OF tyenv_well_formed_add_ghost_var[OF assms]])

end
