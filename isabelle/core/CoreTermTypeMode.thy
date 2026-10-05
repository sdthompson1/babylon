theory CoreTermTypeMode
  imports CoreStmtTypecheck
begin

(* A term that is typed in some mode is typed in Ghost mode, at the same type. 
   Ghost mode imposes no ghost restrictions, so it is the weaker of the two. *)

(* ========================================================================== *)
(* What Ghost-mode typing reads from the environment *)
(* ========================================================================== *)

(* In Ghost mode, core_term_type depends on the environment only through the
   variable maps, the type variables in scope, and the function, datatype and
   constructor tables. In particular it does not depend on TE_GhostLocals,
   TE_RuntimeTypeVars or TE_GhostDatatypes. *)
lemma core_term_type_Ghost_cong_env:
  assumes "TE_LocalVars env1 = TE_LocalVars env2"
    and "TE_GlobalVars env1 = TE_GlobalVars env2"
    and "TE_TypeVars env1 = TE_TypeVars env2"
    and "TE_Functions env1 = TE_Functions env2"
    and "TE_Datatypes env1 = TE_Datatypes env2"
    and "TE_DataCtors env1 = TE_DataCtors env2"
  shows "core_term_type env1 Ghost tm = core_term_type env2 Ghost tm"
  using assms
proof (induction tm arbitrary: env1 env2)
  case (CoreTm_Let var rhs body)
  have rhs_eq: "core_term_type env1 Ghost rhs = core_term_type env2 Ghost rhs"
    using CoreTm_Let.IH(1) CoreTm_Let.prems by blast
  show ?case
  proof (cases "core_term_type env2 Ghost rhs")
    case None
    then show ?thesis using rhs_eq by (simp add: Let_def)
  next
    case (Some rhsTy)
    have body_eq:
      "core_term_type
         (env1 \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env1),
                 TE_GhostLocals := finsert var (TE_GhostLocals env1),
                 TE_ConstLocals := finsert var (TE_ConstLocals env1) \<rparr>) Ghost body
       = core_term_type
         (env2 \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env2),
                 TE_GhostLocals := finsert var (TE_GhostLocals env2),
                 TE_ConstLocals := finsert var (TE_ConstLocals env2) \<rparr>) Ghost body"
      by (rule CoreTm_Let.IH(2)) (simp_all add: CoreTm_Let.prems)
    show ?thesis using Some rhs_eq body_eq CoreTm_Let.prems by (simp add: Let_def)
  qed
next
  case (CoreTm_LitArray ty tms)
  have wk_eq: "is_well_kinded env1 ty = is_well_kinded env2 ty"
    by (rule is_well_kinded_cong_env) (rule CoreTm_LitArray.prems)+
  have elem_eq: "\<And>tm. tm \<in> set tms \<Longrightarrow>
      core_term_type env1 Ghost tm = core_term_type env2 Ghost tm"
    using CoreTm_LitArray.IH CoreTm_LitArray.prems by blast
  have la_eq: "list_all (\<lambda>tm. core_term_type env1 Ghost tm = Some ty) tms =
               list_all (\<lambda>tm. core_term_type env2 Ghost tm = Some ty) tms"
    unfolding list_all_iff using elem_eq by auto
  show ?case using wk_eq la_eq by simp
next
  case (CoreTm_Var name)
  then show ?case
    by (simp add: tyenv_lookup_var_def split: option.splits)
next
  case (CoreTm_FunctionCall fnName tyArgs args)
  have wk_eq: "\<And>ty. is_well_kinded env1 ty = is_well_kinded env2 ty"
    by (rule is_well_kinded_cong_env) (rule CoreTm_FunctionCall.prems)+
  have IH: "\<And>tm. tm \<in> set args \<Longrightarrow>
    core_term_type env1 Ghost tm = core_term_type env2 Ghost tm"
    using CoreTm_FunctionCall.IH CoreTm_FunctionCall.prems by blast
  have la2_eq: "\<And>ys. list_all2 (\<lambda>tm expectedTy.
        case core_term_type env1 Ghost tm of
          None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy) args ys =
      list_all2 (\<lambda>tm expectedTy.
        case core_term_type env2 Ghost tm of
          None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy) args ys"
    by (rule iffI; erule list.rel_mono_strong; simp add: IH)
  have la_wk: "list_all (is_well_kinded env1) tyArgs = list_all (is_well_kinded env2) tyArgs"
    by (simp add: list_all_iff wk_eq)
  show ?case
    using CoreTm_FunctionCall.prems
    by (auto simp add: la_wk la2_eq split: option.splits if_splits)
next
  case (CoreTm_VariantCtor ctorName tyArgs arg)
  have wk_eq: "\<And>ty. is_well_kinded env1 ty = is_well_kinded env2 ty"
    by (rule is_well_kinded_cong_env) (rule CoreTm_VariantCtor.prems)+
  have arg_eq: "core_term_type env1 Ghost arg = core_term_type env2 Ghost arg"
    using CoreTm_VariantCtor.IH CoreTm_VariantCtor.prems by blast
  have la_wk: "list_all (is_well_kinded env1) tyArgs = list_all (is_well_kinded env2) tyArgs"
    by (simp add: list_all_iff wk_eq)
  have ctors_eq: "TE_DataCtors env1 = TE_DataCtors env2"
    by (rule CoreTm_VariantCtor.prems)
  show ?case
  proof (cases "fmlookup (TE_DataCtors env2) ctorName")
    case None
    then show ?thesis by (simp add: ctors_eq)
  next
    case (Some ctor)
    obtain dtName tyvars payloadTy where ctor_eq: "ctor = (dtName, tyvars, payloadTy)"
      by (cases ctor) auto
    show ?thesis using Some
      by (simp add: ctors_eq ctor_eq arg_eq la_wk Let_def)
  qed
next
  case (CoreTm_Record flds)
  have IH: "\<And>nm tm. (nm, tm) \<in> set flds \<Longrightarrow>
    core_term_type env1 Ghost tm = core_term_type env2 Ghost tm"
  proof -
    fix nm tm assume f_in: "(nm, tm) \<in> set flds"
    have sn: "tm \<in> Basic_BNFs.snds (nm, tm)" by simp
    show "core_term_type env1 Ghost tm = core_term_type env2 Ghost tm"
      by (rule CoreTm_Record.IH[OF f_in sn]) (rule CoreTm_Record.prems)+
  qed
  have map_eq: "map (\<lambda>(name, y). core_term_type env1 Ghost y) flds =
                map (\<lambda>(name, y). core_term_type env2 Ghost y) flds"
    by (rule map_cong) (auto simp: IH)
  show ?case by (simp add: map_eq)
next
  case (CoreTm_Match scrut arms)
  have scrut_eq: "core_term_type env1 Ghost scrut = core_term_type env2 Ghost scrut"
    using CoreTm_Match.IH(1) CoreTm_Match.prems by blast
  have bodies_eq: "\<And>body. body \<in> snd ` set arms \<Longrightarrow>
    core_term_type env1 Ghost body = core_term_type env2 Ghost body"
  proof -
    fix body assume "body \<in> snd ` set arms"
    then obtain pat where arm_in: "(pat, body) \<in> set arms" by auto
    have sn: "body \<in> Basic_BNFs.snds (pat, body)" by simp
    show "core_term_type env1 Ghost body = core_term_type env2 Ghost body"
      by (rule CoreTm_Match.IH(2)[OF arm_in sn]) (rule CoreTm_Match.prems)+
  qed
  have hd_eq: "arms \<noteq> [] \<Longrightarrow>
    core_term_type env1 Ghost (snd (hd arms)) = core_term_type env2 Ghost (snd (hd arms))"
    using bodies_eq by (cases arms) auto
  have tl_eq: "\<And>ty. list_all (\<lambda>body. core_term_type env1 Ghost body = Some ty)
                              (tl (map snd arms)) =
               list_all (\<lambda>body. core_term_type env2 Ghost body = Some ty)
                              (tl (map snd arms))"
  proof -
    fix ty
    have "\<And>body. body \<in> set (tl (map snd arms)) \<Longrightarrow> body \<in> snd ` set arms"
      by (cases arms) auto
    then show "?thesis ty" using bodies_eq by (auto simp: list_all_iff)
  qed
  have pc_eq: "\<And>p t. pattern_compatible env1 p t = pattern_compatible env2 p t"
    by (rule pattern_compatible_cong_env) (rule CoreTm_Match.prems)
  show ?case
  proof (cases "core_term_type env2 Ghost scrut")
    case None then show ?thesis using scrut_eq by simp
  next
    case (Some scrutTy)
    show ?thesis
    proof (cases "arms = []")
      case True then show ?thesis using Some scrut_eq by simp
    next
      case False
      have "core_term_type env1 Ghost (snd (hd arms)) =
            core_term_type env2 Ghost (snd (hd arms))"
        using hd_eq False .
      then show ?thesis using Some False scrut_eq tl_eq pc_eq
        by (auto split: if_splits CoreType.splits option.splits simp: Let_def)
    qed
  qed
next
  case (CoreTm_Quantifier quant var varTy body)
  have body_eq:
    "core_term_type
       (env1 \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env1),
               TE_GhostLocals := finsert var (TE_GhostLocals env1) \<rparr>) Ghost body
     = core_term_type
       (env2 \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env2),
               TE_GhostLocals := finsert var (TE_GhostLocals env2) \<rparr>) Ghost body"
    by (rule CoreTm_Quantifier.IH) (simp_all add: CoreTm_Quantifier.prems)
  have wk_eq: "is_well_kinded env1 varTy = is_well_kinded env2 varTy"
    by (rule is_well_kinded_cong_env) (rule CoreTm_Quantifier.prems)+
  show ?case
    using CoreTm_Quantifier.prems body_eq wk_eq
    by (simp add: Let_def split: option.splits CoreType.splits)
next
  case (CoreTm_ArrayProj tm idxTms)
  have IH_tm: "core_term_type env1 Ghost tm = core_term_type env2 Ghost tm"
    using CoreTm_ArrayProj.IH(1) CoreTm_ArrayProj.prems by blast
  have IH_idx: "\<And>idx. idx \<in> set idxTms \<Longrightarrow>
    core_term_type env1 Ghost idx = core_term_type env2 Ghost idx"
    using CoreTm_ArrayProj.IH(2) CoreTm_ArrayProj.prems by blast
  have la_eq: "\<And>ty. list_all (\<lambda>tm. core_term_type env1 Ghost tm = Some ty) idxTms =
                    list_all (\<lambda>tm. core_term_type env2 Ghost tm = Some ty) idxTms"
    using IH_idx by (auto simp: list_all_iff)
  show ?case using IH_tm la_eq by (simp split: option.splits CoreType.splits if_splits)
next
  case (CoreTm_Cast targetTy tm)
  have co_eq: "\<And>a b. cast_ok env1 a b = cast_ok env2 a b"
    by (rule cast_ok_cong_env) (rule CoreTm_Cast.prems)+
  have tm_eq: "core_term_type env1 Ghost tm = core_term_type env2 Ghost tm"
    using CoreTm_Cast.IH CoreTm_Cast.prems by blast
  show ?case
    by (auto simp: tm_eq co_eq split: option.splits)
next
  case (CoreTm_VariantProj tm ctorName)
  have tm_eq: "core_term_type env1 Ghost tm = core_term_type env2 Ghost tm"
    using CoreTm_VariantProj.IH CoreTm_VariantProj.prems by blast
  show ?case
    by (simp only: core_term_type.simps tm_eq CoreTm_VariantProj.prems)
next
  case (CoreTm_Allocated tm)
  have tm_eq: "core_term_type env1 Ghost tm = core_term_type env2 Ghost tm"
    using CoreTm_Allocated.IH CoreTm_Allocated.prems by blast
  show ?case using tm_eq by simp
next
  case (CoreTm_Old tm)
  have tm_eq: "core_term_type env1 Ghost tm = core_term_type env2 Ghost tm"
    using CoreTm_Old.IH CoreTm_Old.prems by blast
  show ?case using tm_eq by simp
next
  case (CoreTm_Unop op operand)
  have "core_term_type env1 Ghost operand = core_term_type env2 Ghost operand"
    using CoreTm_Unop.IH CoreTm_Unop.prems by blast
  then show ?case by (simp split: option.splits)
next
  case (CoreTm_Binop op lhs rhs)
  have "core_term_type env1 Ghost lhs = core_term_type env2 Ghost lhs"
       "core_term_type env1 Ghost rhs = core_term_type env2 Ghost rhs"
    using CoreTm_Binop.IH CoreTm_Binop.prems by blast+
  then show ?case by (simp split: option.splits prod.splits)
next
  case (CoreTm_RecordProj tm fldName)
  have "core_term_type env1 Ghost tm = core_term_type env2 Ghost tm"
    using CoreTm_RecordProj.IH CoreTm_RecordProj.prems by blast
  then show ?case by (simp split: option.splits CoreType.splits)
next
  case (CoreTm_Sizeof tm)
  have "core_term_type env1 Ghost tm = core_term_type env2 Ghost tm"
    using CoreTm_Sizeof.IH CoreTm_Sizeof.prems by blast
  then show ?case by (simp split: option.splits CoreType.splits)
next
  case (CoreTm_Default ty)
  have wk_eq: "is_well_kinded env1 ty = is_well_kinded env2 ty"
    by (rule is_well_kinded_cong_env) (rule CoreTm_Default.prems)+
  show ?case by (simp add: wk_eq)
qed simp_all


(* ========================================================================== *)
(* A list lemma *)
(* ========================================================================== *)

lemma those_map_weaken:
  assumes "those (map f xs) = Some ys"
    and "\<And>x y. x \<in> set xs \<Longrightarrow> f x = Some y \<Longrightarrow> h x = Some y"
  shows "those (map h xs) = Some ys"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  from Cons.prems(1) obtain y ys' where
    fx: "f x = Some y" and
    rest: "those (map f xs) = Some ys'" and
    ys_eq: "ys = y # ys'"
    by (auto split: option.splits)
  have hx: "h x = Some y"
    by (rule Cons.prems(2)[OF _ fx]) simp
  have "those (map h xs) = Some ys'"
  proof (rule Cons.IH[OF rest])
    fix x' y' assume "x' \<in> set xs" and "f x' = Some y'"
    then show "h x' = Some y'" using Cons.prems(2) by simp
  qed
  with hx ys_eq show ?case by simp
qed


(* ========================================================================== *)
(* Terms *)
(* ========================================================================== *)

(* The Let case uses core_term_type_Ghost_cong_env: the two modes give the body
   environments that differ only in TE_GhostLocals. *)
lemma core_term_type_NotGhost_imp_Ghost:
  "core_term_type env NotGhost tm = Some ty \<Longrightarrow> core_term_type env Ghost tm = Some ty"
proof (induction tm arbitrary: env ty)
  case (CoreTm_LitBool b)
  then show ?case by simp
next
  case (CoreTm_LitInt i)
  then show ?case by simp
next
  case (CoreTm_LitArray elemTy tms)
  from CoreTm_LitArray.prems have
    wk: "is_well_kinded env elemTy" and
    elems: "list_all (\<lambda>tm. core_term_type env NotGhost tm = Some elemTy) tms" and
    rng: "int_in_range (int_range Unsigned IntBits_64) (int (length tms))" and
    ty_eq: "ty = CoreTy_Array elemTy [CoreDim_Fixed (int (length tms))]"
    by (auto split: if_splits)
  have "list_all (\<lambda>tm. core_term_type env Ghost tm = Some elemTy) tms"
    using elems CoreTm_LitArray.IH by (auto simp: list_all_iff)
  with wk rng ty_eq show ?case by simp
next
  case (CoreTm_Var name)
  then show ?case by (auto split: option.splits if_splits)
next
  case (CoreTm_Cast targetTy operand)
  show ?case
  proof (cases "core_term_type env NotGhost operand")
    case None
    then show ?thesis using CoreTm_Cast.prems by simp
  next
    case (Some operandTy)
    have g: "core_term_type env Ghost operand = Some operandTy"
      by (rule CoreTm_Cast.IH[OF Some])
    show ?thesis using CoreTm_Cast.prems Some g by (auto split: if_splits)
  qed
next
  case (CoreTm_Unop op operand)
  show ?case
  proof (cases "core_term_type env NotGhost operand")
    case None
    then show ?thesis using CoreTm_Unop.prems by simp
  next
    case (Some operandTy)
    have g: "core_term_type env Ghost operand = Some operandTy"
      by (rule CoreTm_Unop.IH[OF Some])
    show ?thesis using CoreTm_Unop.prems Some g by simp
  qed
next
  case (CoreTm_Binop op lhs rhs)
  show ?case
  proof (cases "core_term_type env NotGhost lhs")
    case None
    then show ?thesis using CoreTm_Binop.prems by simp
  next
    case lhs_some: (Some lhsTy)
    have g1: "core_term_type env Ghost lhs = Some lhsTy"
      by (rule CoreTm_Binop.IH(1)[OF lhs_some])
    show ?thesis
    proof (cases "core_term_type env NotGhost rhs")
      case None
      then show ?thesis using CoreTm_Binop.prems lhs_some by simp
    next
      case rhs_some: (Some rhsTy)
      have g2: "core_term_type env Ghost rhs = Some rhsTy"
        by (rule CoreTm_Binop.IH(2)[OF rhs_some])
      show ?thesis using CoreTm_Binop.prems lhs_some rhs_some g1 g2
        by (auto split: if_splits)
    qed
  qed
next
  case (CoreTm_Let var rhs body)
  show ?case
  proof (cases "core_term_type env NotGhost rhs")
    case None
    then show ?thesis using CoreTm_Let.prems by simp
  next
    case (Some rhsTy)
    have g: "core_term_type env Ghost rhs = Some rhsTy"
      by (rule CoreTm_Let.IH(1)[OF Some])
    \<comment> \<open>The environment of the body: in NotGhost mode, in Ghost mode.\<close>
    let ?envN = "env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                        TE_GhostLocals := fminus (TE_GhostLocals env) {|var|},
                        TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
    let ?envG = "env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                        TE_GhostLocals := finsert var (TE_GhostLocals env),
                        TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
    have n_body: "core_term_type ?envN NotGhost body = Some ty"
      using CoreTm_Let.prems Some by (simp add: Let_def)
    have gN_body: "core_term_type ?envN Ghost body = Some ty"
      by (rule CoreTm_Let.IH(2)[OF n_body])
    have g_eq: "core_term_type ?envG Ghost body = core_term_type ?envN Ghost body"
      by (rule core_term_type_Ghost_cong_env) simp_all
    show ?thesis using g gN_body g_eq by (simp add: Let_def)
  qed
next
  case (CoreTm_Quantifier quant var varTy body)
  then show ?case by simp
next
  case (CoreTm_FunctionCall fnName tyArgs tmArgs)
  have args: "list_all2 (\<lambda>tm ety. case core_term_type env Ghost tm of
                                     None \<Rightarrow> False | Some a \<Rightarrow> a = ety) tmArgs etys"
    if n_args: "list_all2 (\<lambda>tm ety. case core_term_type env NotGhost tm of
                                     None \<Rightarrow> False | Some a \<Rightarrow> a = ety) tmArgs etys"
    for etys
  proof (rule list.rel_mono_strong[OF n_args])
    fix tm ety
    assume tm_in: "tm \<in> set tmArgs"
      and n: "case core_term_type env NotGhost tm of None \<Rightarrow> False | Some a \<Rightarrow> a = ety"
    from n have n': "core_term_type env NotGhost tm = Some ety"
      by (simp split: option.splits)
    have "core_term_type env Ghost tm = Some ety"
      by (rule CoreTm_FunctionCall.IH[OF tm_in n'])
    then show "case core_term_type env Ghost tm of None \<Rightarrow> False | Some a \<Rightarrow> a = ety"
      by simp
  qed
  show ?case
  proof (cases "fmlookup (TE_Functions env) fnName")
    case None
    then show ?thesis using CoreTm_FunctionCall.prems by simp
  next
    case (Some funInfo)
    show ?thesis using CoreTm_FunctionCall.prems Some
      by (auto simp: Let_def split: if_splits intro: args)
  qed
next
  case (CoreTm_VariantCtor ctorName tyArgs payload)
  show ?case
  proof (cases "fmlookup (TE_DataCtors env) ctorName")
    case None
    then show ?thesis using CoreTm_VariantCtor.prems by simp
  next
    case ctor_some: (Some ctor)
    obtain dtName tyvars payloadTy where ctor_eq: "ctor = (dtName, tyvars, payloadTy)"
      by (cases ctor) auto
    show ?thesis
    proof (cases "core_term_type env NotGhost payload")
      case None
      then show ?thesis using CoreTm_VariantCtor.prems ctor_some ctor_eq
        by (auto simp: Let_def split: if_splits)
    next
      case (Some actualTy)
      have g: "core_term_type env Ghost payload = Some actualTy"
        by (rule CoreTm_VariantCtor.IH[OF Some])
      show ?thesis using CoreTm_VariantCtor.prems ctor_some ctor_eq Some g
        by (auto simp: Let_def split: if_splits)
    qed
  qed
next
  case (CoreTm_Record flds)
  from CoreTm_Record.prems obtain tys where
    dist: "distinct (map fst flds)" and
    n: "those (map (\<lambda>(name, tm). core_term_type env NotGhost tm) flds) = Some tys" and
    ty_eq: "ty = CoreTy_Record (zip (map fst flds) tys)"
    by (auto split: if_splits option.splits)
  have g: "those (map (\<lambda>(name, tm). core_term_type env Ghost tm) flds) = Some tys"
  proof (rule those_map_weaken[OF n])
    fix x y
    assume x_in: "x \<in> set flds"
      and fx: "(case x of (name, tm) \<Rightarrow> core_term_type env NotGhost tm) = Some y"
    obtain name tm where x_eq: "x = (name, tm)" by (cases x)
    from fx have n': "core_term_type env NotGhost tm = Some y" by (simp add: x_eq)
    have "core_term_type env Ghost tm = Some y"
      by (rule CoreTm_Record.IH[OF x_in _ n']) (simp add: x_eq)
    then show "(case x of (name, tm) \<Rightarrow> core_term_type env Ghost tm) = Some y"
      by (simp add: x_eq)
  qed
  show ?case using dist g ty_eq by simp
next
  case (CoreTm_RecordProj tm fldName)
  show ?case
  proof (cases "core_term_type env NotGhost tm")
    case None
    then show ?thesis using CoreTm_RecordProj.prems by simp
  next
    case (Some tmTy)
    have g: "core_term_type env Ghost tm = Some tmTy"
      by (rule CoreTm_RecordProj.IH[OF Some])
    show ?thesis using CoreTm_RecordProj.prems Some g by simp
  qed
next
  case (CoreTm_VariantProj tm ctorName)
  show ?case
  proof (cases "core_term_type env NotGhost tm")
    case None
    then show ?thesis using CoreTm_VariantProj.prems by simp
  next
    case (Some tmTy)
    have g: "core_term_type env Ghost tm = Some tmTy"
      by (rule CoreTm_VariantProj.IH[OF Some])
    show ?thesis using CoreTm_VariantProj.prems Some g by simp
  qed
next
  case (CoreTm_ArrayProj arr idxTms)
  have idx: "list_all (\<lambda>tm. core_term_type env Ghost tm = Some t) idxTms"
    if "list_all (\<lambda>tm. core_term_type env NotGhost tm = Some t) idxTms" for t
    using that CoreTm_ArrayProj.IH(2) by (auto simp: list_all_iff)
  show ?case
  proof (cases "core_term_type env NotGhost arr")
    case None
    then show ?thesis using CoreTm_ArrayProj.prems by simp
  next
    case (Some arrTy)
    have g: "core_term_type env Ghost arr = Some arrTy"
      by (rule CoreTm_ArrayProj.IH(1)[OF Some])
    show ?thesis using CoreTm_ArrayProj.prems Some g
      by (auto split: CoreType.splits if_splits intro: idx)
  qed
next
  case (CoreTm_Match scrut arms)
  have body_ih: "core_term_type env Ghost body = Some t"
    if body_in: "body \<in> set (map snd arms)"
      and n: "core_term_type env NotGhost body = Some t" for body t
  proof -
    from body_in obtain pat where arm_in: "(pat, body) \<in> set arms" by auto
    have sn: "body \<in> Basic_BNFs.snds (pat, body)" by simp
    show ?thesis by (rule CoreTm_Match.IH(2)[OF arm_in sn n])
  qed
  show ?case
  proof (cases "core_term_type env NotGhost scrut")
    case None
    then show ?thesis using CoreTm_Match.prems by simp
  next
    case scrut_some: (Some scrutTy)
    have g1: "core_term_type env Ghost scrut = Some scrutTy"
      by (rule CoreTm_Match.IH(1)[OF scrut_some])
    show ?thesis
    proof (cases "arms = []")
      case True
      then show ?thesis using CoreTm_Match.prems scrut_some by (simp add: Let_def)
    next
      case False
      have hd_in: "snd (hd arms) \<in> set (map snd arms)"
        using False by (cases arms) auto
      have tl_sub: "\<And>z. z \<in> set (tl (map snd arms)) \<Longrightarrow> z \<in> set (map snd arms)"
        by (cases arms) auto
      show ?thesis
      proof (cases "core_term_type env NotGhost (snd (hd arms))")
        case None
        then show ?thesis using CoreTm_Match.prems scrut_some False
          by (auto simp: Let_def split: if_splits)
      next
        case hd_some: (Some resultTy)
        have g_hd: "core_term_type env Ghost (snd (hd arms)) = Some resultTy"
          by (rule body_ih[OF hd_in hd_some])
        have tl_g: "list_all (\<lambda>body. core_term_type env Ghost body = Some t)
                             (tl (map snd arms))"
          if "list_all (\<lambda>body. core_term_type env NotGhost body = Some t)
                       (tl (map snd arms))" for t
          using that body_ih tl_sub by (auto simp: list_all_iff)
        show ?thesis using CoreTm_Match.prems scrut_some g1 False hd_some g_hd
          by (auto simp: Let_def split: if_splits intro: tl_g)
      qed
    qed
  qed
next
  case (CoreTm_Sizeof tm)
  show ?case
  proof (cases "core_term_type env NotGhost tm")
    case None
    then show ?thesis using CoreTm_Sizeof.prems by simp
  next
    case (Some tmTy)
    have g: "core_term_type env Ghost tm = Some tmTy"
      by (rule CoreTm_Sizeof.IH[OF Some])
    show ?thesis using CoreTm_Sizeof.prems Some g
      by (auto split: CoreType.splits if_splits)
  qed
next
  case (CoreTm_Allocated tm)
  then show ?case by simp
next
  case (CoreTm_Old tm)
  then show ?case by simp
next
  case (CoreTm_Default defTy)
  then show ?case by (auto split: if_splits)
qed

(* The same, for a mode that is not known. *)
lemma core_term_type_imp_Ghost:
  assumes "core_term_type env ghost tm = Some ty"
  shows "core_term_type env Ghost tm = Some ty"
proof (cases ghost)
  case Ghost
  with assms show ?thesis by simp
next
  case NotGhost
  with assms show ?thesis by (simp add: core_term_type_NotGhost_imp_Ghost)
qed


(* ========================================================================== *)
(* Impure calls and casts *)
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
                  case core_term_type env Ghost tm of
                    None \<Rightarrow> False
                  | Some actualTy \<Rightarrow> actualTy = expectedTy)
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
    args: "list_all2 (\<lambda>tm expectedTy.
                  case core_term_type env ghost tm of
                    None \<Rightarrow> False
                  | Some actualTy \<Rightarrow> actualTy = expectedTy)
                tmArgs
                (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo))" and
    refs: "\<forall>i < length tmArgs.
                 fst (snd (FI_TmArgs funInfo ! i)) = Ref
                   \<longrightarrow> is_writable_lvalue env (tmArgs ! i)
                       \<and> ghost_lvalue_ok env ghost (tmArgs ! i)"
    by blast
  have args_g: "list_all2 (\<lambda>tm expectedTy.
                  case core_term_type env Ghost tm of
                    None \<Rightarrow> False
                  | Some actualTy \<Rightarrow> actualTy = expectedTy)
                tmArgs
                (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo))"
  proof (rule list_all2_mono[OF args])
    fix tm ety
    assume a: "case core_term_type env ghost tm of None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = ety"
    then have "core_term_type env ghost tm = Some ety" by (simp split: option.splits)
    then have "core_term_type env Ghost tm = Some ety" by (rule core_term_type_imp_Ghost)
    then show "case core_term_type env Ghost tm of None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = ety"
      by simp
  qed
  from refs have refs_g: "\<forall>i < length tmArgs.
                 fst (snd (FI_TmArgs funInfo ! i)) = Ref
                   \<longrightarrow> is_writable_lvalue env (tmArgs ! i)"
    by blast
  from fn_lookup len_ty wk cp len_tm ty_eq args_g refs_g show ?thesis by blast
qed

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
