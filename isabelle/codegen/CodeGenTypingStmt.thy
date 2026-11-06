theory CodeGenTypingStmt
  imports CodeGenTypingTerm
begin

declare int_fits.simps [simp del]

(* ========================================================================== *)
(* The typing theorem: statements                                             *)
(* ========================================================================== *)

section \<open>Size facts of statements\<close>

(* Every type the lowering of a statement (list) computes a size of fits:
   the types of stmt_types / stmts_types (SizeBound.thy). *)
definition stmt_fits :: "CoreTyEnv \<Rightarrow> CoreStatement \<Rightarrow> bool" where
  "stmt_fits env s = (\<exists>tys. stmt_types env s = Some tys \<and> (\<forall>ty \<in> set tys. fits env ty))"

definition stmts_fits :: "CoreTyEnv \<Rightarrow> CoreStatement list \<Rightarrow> bool" where
  "stmts_fits env ss = (\<exists>tys. stmts_types env ss = Some tys \<and> (\<forall>ty \<in> set tys. fits env ty))"

lemma stmts_fits_Nil [simp]: "stmts_fits env []"
  by (simp add: stmts_fits_def)

(* fits does not look at the local variables. *)
lemma fits_locals_irrelevant:
  assumes "TE_DataCtors env' = TE_DataCtors env" and "TE_DataCtorsByType env' = TE_DataCtorsByType env"
  shows "fits env' ty = fits env ty"
  unfolding fits_def by (rule size_fits_cong_env[OF assms])

lemma fits_nested [simp]: "fits (env \<lparr> TE_ProofTopLevel := False \<rparr>) ty = fits env ty"
  by (rule fits_locals_irrelevant) simp_all

lemma fits_stmt_env:
  assumes "core_statement_type env g s = Some env'"
  shows "fits env' ty = fits env ty"
  using core_statement_type_fixed_eq[OF assms] by (intro fits_locals_irrelevant) (simp_all add: tyenv_fixed_eq_def)

lemma stmts_fits_Cons:
  assumes "stmts_fits env (s # ss)"
  shows "stmt_fits env s"
    and "\<And>env'. core_statement_type env NotGhost s = Some env' \<Longrightarrow> stmts_fits env' ss"
proof -
  from assms obtain l env1 l2 where st: "stmt_types env s = Some l" and ct: "core_statement_type env NotGhost s = Some env1"
    and ss: "stmts_types env1 ss = Some l2" and f: "\<forall>ty \<in> set (l @ l2). fits env ty"
    unfolding stmts_fits_def by (auto split: option.splits)
  show "stmt_fits env s" using st f unfolding stmt_fits_def by auto
  fix env' assume "core_statement_type env NotGhost s = Some env'"
  then have "env' = env1" using ct by simp
  then show "stmts_fits env' ss" using ss f fits_stmt_env[OF ct] unfolding stmts_fits_def by auto
qed

lemma stmt_fits_VarDecl:
  assumes "stmt_fits env (CoreStmt_VarDecl g x vor ty tm)"
  shows "fits env ty" and "term_fits env tm"
  using assms unfolding stmt_fits_def term_fits_def by auto

lemma stmt_fits_VarDeclCall:
  assumes "stmt_fits env (CoreStmt_VarDeclCall g x ty castOpt f tys args)"
  obtains retTy where "core_impure_call_type env NotGhost f tys args = Some retTy"
    and "fits env ty" and "fits env retTy" and "\<And>t. castOpt = Some t \<Longrightarrow> fits env t"
    and "\<forall>ty \<in> set tys. fits env ty" and "\<forall>a \<in> set args. term_fits env a"
proof -
  from assms obtain retTy ls where ct: "core_impure_call_type env NotGhost f tys args = Some retTy"
    and th: "those (map (term_types env) args) = Some ls"
    and f: "\<forall>ty' \<in> set (ty # retTy # (case castOpt of None \<Rightarrow> [] | Some t \<Rightarrow> [t]) @ tys @ concat ls). fits env ty'"
    unfolding stmt_fits_def by (auto split: option.splits)
  show thesis
  proof (rule that[OF ct])
    show "\<forall>a \<in> set args. term_fits env a" using term_fits_of_those[OF th] f by auto
  qed (use f in \<open>auto split: option.splits\<close>)
qed

lemma stmt_fits_Assign:
  assumes "stmt_fits env (CoreStmt_Assign g ty lhs rhs)"
  shows "fits env ty" and "term_fits env lhs" and "term_fits env rhs"
  using assms unfolding stmt_fits_def term_fits_def by (auto split: option.splits)

lemma stmt_fits_AssignCall:
  assumes "stmt_fits env (CoreStmt_AssignCall g lhs castOpt f tys args)"
  obtains retTy where "core_impure_call_type env NotGhost f tys args = Some retTy"
    and "fits env retTy" and "\<And>t. castOpt = Some t \<Longrightarrow> fits env t"
    and "\<forall>ty \<in> set tys. fits env ty" and "term_fits env lhs" and "\<forall>a \<in> set args. term_fits env a"
proof -
  from assms obtain retTy l ls where ct: "core_impure_call_type env NotGhost f tys args = Some retTy"
    and tl: "term_types env lhs = Some l"
    and th: "those (map (term_types env) args) = Some ls"
    and f: "\<forall>ty' \<in> set (retTy # (case castOpt of None \<Rightarrow> [] | Some t \<Rightarrow> [t]) @ tys @ l @ concat ls). fits env ty'"
    unfolding stmt_fits_def by (auto split: option.splits)
  show thesis
  proof (rule that[OF ct])
    show "\<forall>a \<in> set args. term_fits env a" using term_fits_of_those[OF th] f by auto
    show "term_fits env lhs" using tl f unfolding term_fits_def by auto
  qed (use f in \<open>auto split: option.splits\<close>)
qed

lemma stmt_fits_Swap:
  assumes "stmt_fits env (CoreStmt_Swap g lhs rhs)"
  shows "term_fits env lhs" and "term_fits env rhs"
  using assms unfolding stmt_fits_def term_fits_def by (auto split: option.splits)

lemma stmt_fits_Return:
  assumes "stmt_fits env (CoreStmt_Return tm)"
  shows "term_fits env tm"
  using assms unfolding stmt_fits_def term_fits_def by auto

lemma stmt_fits_While:
  assumes "stmt_fits env (CoreStmt_While g c invs decr body)"
  shows "term_fits env c" and "stmts_fits (env \<lparr> TE_ProofTopLevel := False \<rparr>) body"
proof -
  from assms obtain l1 l2 where tc: "term_types env c = Some l1"
    and tb: "stmts_types (env \<lparr> TE_ProofTopLevel := False \<rparr>) body = Some l2"
    and f: "\<forall>ty \<in> set (l1 @ l2). fits env ty"
    unfolding stmt_fits_def by (auto simp del: term_types.simps split: option.splits)
  show "term_fits env c" using tc f unfolding term_fits_def by auto
  show "stmts_fits (env \<lparr> TE_ProofTopLevel := False \<rparr>) body" using tb f unfolding stmts_fits_def by auto
qed

lemma stmt_fits_Match:
  assumes "stmt_fits env (CoreStmt_Match g s arms)"
  shows "term_fits env s" and "\<And>p body. (p, body) \<in> set arms \<Longrightarrow> stmts_fits (env \<lparr> TE_ProofTopLevel := False \<rparr>) body"
proof -
  from assms obtain l ls where ts: "term_types env s = Some l"
    and th: "those (map (stmts_types (env \<lparr> TE_ProofTopLevel := False \<rparr>) \<circ> snd) arms) = Some ls"
    and f: "\<forall>ty \<in> set (l @ concat ls). fits env ty"
    unfolding stmt_fits_def by (auto simp del: term_types.simps split: option.splits)
  show "term_fits env s" using ts f unfolding term_fits_def by auto
  fix p body assume "(p, body) \<in> set arms"
  then have "stmts_types (env \<lparr> TE_ProofTopLevel := False \<rparr>) body \<in> set (map (stmts_types (env \<lparr> TE_ProofTopLevel := False \<rparr>) \<circ> snd) arms)"
    by force
  then obtain l' where "stmts_types (env \<lparr> TE_ProofTopLevel := False \<rparr>) body = Some l'" and "l' \<in> set ls"
    using those_Some_elem[OF th] by auto
  then show "stmts_fits (env \<lparr> TE_ProofTopLevel := False \<rparr>) body" using f unfolding stmts_fits_def by auto
qed

lemma stmt_fits_Block:
  assumes "stmt_fits env (CoreStmt_Block body)"
  shows "stmts_fits env body"
  using assms unfolding stmt_fits_def stmts_fits_def by auto


section \<open>Declaring a variable\<close>

(* The invariant after a VarDecl: the new context binds x to ty (a well-kinded
   runtime type) with a representation typed in the extended environment. *)
lemma cg_ok_decl:
  assumes ok: "cg_ok prog E cg" and wk: "is_well_kinded (CG_TyEnv cg) ty" and rtt: "is_runtime_type (CG_TyEnv cg) ty"
    and le: "env_le E E'"
    and rep: "rep_ok E' (CG_TyEnv cg) ty rep"
  shows "cg_ok prog E' (cg_bind_var cg ((CG_TyEnv cg) \<lparr> TE_LocalVars := fmupd x ty (TE_LocalVars (CG_TyEnv cg)),
                                                       TE_GhostLocals := fminus (TE_GhostLocals (CG_TyEnv cg)) {|x|},
                                                       TE_ConstLocals := c \<rparr>) x rep)"
proof (rule cg_okI)
  let ?env' = "(CG_TyEnv cg) \<lparr> TE_LocalVars := fmupd x ty (TE_LocalVars (CG_TyEnv cg)),
                             TE_GhostLocals := fminus (TE_GhostLocals (CG_TyEnv cg)) {|x|},
                             TE_ConstLocals := c \<rparr>"
  let ?cg' = "cg_bind_var cg ?env' x rep"
  have A: "CG_TyEnv ?cg' = ?env'" by (simp add: cg_bind_var_def)
  show "tyenv_well_formed (CG_TyEnv ?cg')"
    using tyenv_well_formed_declare_var[OF cg_ok_wf[OF ok] wk, where g = NotGhost and var = x and c = c] rtt
    unfolding A by simp
  show "sizes_in E' (fset (TE_TypeVars (CG_TyEnv ?cg')))"
    using sizes_in_mono[OF le cg_ok_sizes_in[OF ok]] unfolding A by simp
  show "\<And>y r. fmlookup (CG_Vars ?cg') y = Some r \<Longrightarrow>
          \<exists>ty. tyenv_lookup_var (CG_TyEnv ?cg') y = Some ty \<and> rep_ok E' (CG_TyEnv ?cg') ty r"
  proof -
    fix y r assume lk: "fmlookup (CG_Vars ?cg') y = Some r"
    have cong: "\<And>ty r. rep_ok E' ?env' ty r = rep_ok E' (CG_TyEnv cg) ty r"
      by (rule rep_ok_cong_env(1)) simp_all
    have lk': "\<And>y. tyenv_lookup_var ?env' y = (if y = x then Some ty else tyenv_lookup_var (CG_TyEnv cg) y)"
      by (simp add: tyenv_lookup_var_def split: option.splits)
    show "\<exists>ty. tyenv_lookup_var (CG_TyEnv ?cg') y = Some ty \<and> rep_ok E' (CG_TyEnv ?cg') ty r"
    proof (cases "y = x")
      case True
      then have "r = rep" using lk by (simp add: cg_bind_var_def)
      then show ?thesis using True rep unfolding A cong lk' by simp
    next
      case False
      then have "fmlookup (CG_Vars cg) y = Some r" using lk by (simp add: cg_bind_var_def)
      then obtain ty where "tyenv_lookup_var (CG_TyEnv cg) y = Some ty" "rep_ok E (CG_TyEnv cg) ty r"
        using cg_ok_var[OF ok] by blast
      then show ?thesis using False rep_ok_mono[OF le] unfolding A cong lk' by auto
    qed
  qed
  show "CG_Ret ?cg' = ret_kind (TE_ReturnType (CG_TyEnv ?cg'))"
    using cg_ok_ret[OF ok] unfolding A by (simp add: cg_bind_var_def)
  show "CG_Ret ?cg' = RK_Buf \<Longrightarrow> fmlookup E' ret_param = Some (VT_Scalar CTy_CharPtr)"
    using cg_ok_ret_param[OF ok] env_le_lookup[OF le] by (simp add: cg_bind_var_def)
  show "size_fits (CG_TyEnv ?cg') 0 (\<lambda>_. 0) (TE_ReturnType (CG_TyEnv ?cg'))"
    using cg_ok_ret_fits[OF ok] size_fits_cong_env[of ?env' "CG_TyEnv cg"] unfolding A by simp
  show "\<And>d. dt_tags_fit (CG_TyEnv ?cg') d"
    using cg_ok_tags[OF ok] unfolding A by (simp add: dt_tags_fit_def dt_ctors_def)
  show "prog_ok prog (CG_TyEnv ?cg')"
    using cg_ok_prog[OF ok] unfolding A by (simp add: prog_ok_def)
qed

lemma cg_mapM_length: "cg_mapM f xs st = Inr (ys, st') \<Longrightarrow> length ys = length xs"
proof (induction xs arbitrary: st ys)
  case Nil
  then show ?case by (simp add: cg_mapM.simps)
next
  case (Cons x xs)
  from Cons.prems obtain y st1 ys' where "cg_mapM f xs st1 = Inr (ys', st')" and "ys = y # ys'"
    by (auto simp: cg_mapM.simps elim!: cg_bind_InrE)
  then show ?case using Cons.IH by simp
qed


section \<open>Frozen lvalues\<close>

(* The index variables of a frozen array projection: each index value in a
   fresh uint64_t variable. *)
lemma freeze_indices_ok:
  assumes "cg_mapM (\<lambda>e. cg_bind (fresh_name (CG_Fun cg) ''idx'')
                       (\<lambda>v. cg_return (v, [MS_DeclScalar v CTy_U64, MS_Assign v e]))) es st = Inr (vs, st')"
    and "scope_ok prog (E, ds) st" and "\<forall>e \<in> set es. u64_ok E e"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st (concat (map snd vs)) st' (E', ds')
           \<and> (\<forall>v \<in> set (map fst vs). fmlookup E' v = Some (VT_Scalar CTy_U64))"
proof -
  have "\<exists>E' ds'. lowered_ok prog rt (E, ds) st (concat (map snd vs)) st' (E', ds')
           \<and> (\<forall>y \<in> set vs. fmlookup E' (fst y) = Some (VT_Scalar CTy_U64))"
  proof (rule cg_mapM_chain[OF assms(1,2)])
    fix e sta y stb Ea dsa
    assume e: "e \<in> set es"
      and fy: "cg_bind (fresh_name (CG_Fun cg) ''idx'') (\<lambda>v. cg_return (v, [MS_DeclScalar v CTy_U64, MS_Assign v e])) sta = Inr (y, stb)"
      and sca: "scope_ok prog (Ea, dsa) sta" and le: "env_le E Ea"
    from fy obtain v where fr: "fresh_name (CG_Fun cg) ''idx'' sta = Inr (v, stb)"
      and y: "y = (v, [MS_DeclScalar v CTy_U64, MS_Assign v e])"
      by (auto simp: cg_return_def elim!: cg_bind_InrE)
    let ?E2 = "fmupd v (VT_Scalar CTy_U64) Ea"
    have d: "lowered_ok prog rt (Ea, dsa) sta [MS_DeclScalar v CTy_U64] stb (?E2, v # dsa)"
      by (rule fresh_scalar_ok[OF sca fr])
    have le2: "env_le E ?E2" by (rule env_le_trans[OF le lowered_ok_env_le'[OF d]])
    have ue: "u64_ok ?E2 e" using assms(3) e expr_type_mono[OF le2] by (auto simp: u64_ok_def)
    have a: "lowered_ok prog rt (?E2, v # dsa) stb [MS_Assign v e] stb (?E2, v # dsa)"
      using lowered_ok_scope[OF d] ue by (intro assign_ok[where cty' = CTy_U64]) (auto simp: ty_compat_def)
    show "\<exists>E2 ds2. lowered_ok prog rt (Ea, dsa) sta (snd y) stb (E2, ds2) \<and> fmlookup E2 (fst y) = Some (VT_Scalar CTy_U64)"
      unfolding y using lowered_ok_append[OF d a] by auto
  next
    fix E1 E2 y assume "env_le E1 E2" "fmlookup E1 (fst y) = Some (VT_Scalar CTy_U64)"
    then show "fmlookup E2 (fst y) = Some (VT_Scalar CTy_U64)" by (rule env_le_lookup)
  qed
  then show ?thesis by auto
qed

lemma freeze_lvalue_ok:
  "freeze_lvalue cg lv st = Inr ((S, ll), st') \<Longrightarrow> cg_ok prog E cg \<Longrightarrow> scope_ok prog (E, ds) st
   \<Longrightarrow> term_fits (CG_TyEnv cg) lv \<Longrightarrow> core_term_type (CG_TyEnv cg) NotGhost lv = Some ty
   \<Longrightarrow> \<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> ll_type ll = ty \<and> ll_ok E' (CG_TyEnv cg) ll"
proof (induction cg lv arbitrary: st S ll st' E ds ty rule: freeze_lvalue.induct)
  case (1 cg x)
  from 1(1) obtain rep where rep: "fmlookup (CG_Vars cg) x = Some rep"
    and r: "(case rep of VR_Lazy ll \<Rightarrow> cg_return ([], ll) | _ \<Rightarrow> cg_return ([], LL_Base rep ty)) st = Inr ((S, ll), st')"
    using 1(5) by (auto simp: freeze_lvalue.simps ty_of_Inr lookup_var_Inr elim!: cg_bind_InrE)
  obtain ty' where "tyenv_lookup_var (CG_TyEnv cg) x = Some ty'" "rep_ok E (CG_TyEnv cg) ty' rep"
    using cg_ok_var[OF 1(2) rep] by blast
  then have ro: "rep_ok E (CG_TyEnv cg) ty rep" using var_typed[OF 1(5)] by simp
  have wk: "is_well_kinded (CG_TyEnv cg) ty" using term_type_wk(1)[OF 1(2,5)] .
  have f: "fits (CG_TyEnv cg) ty" using term_fits_ty[OF 1(4,5)] .
  show ?case
  proof (cases rep)
    case (VR_Lazy ll')
    then have "S = []" "ll = ll'" "st' = st" using r by (auto simp: cg_return_def)
    then show ?thesis using ro VR_Lazy lowered_ok_nil[OF 1(3)] by auto
  next
    case (VR_Scalar n cty)
    then have "S = []" "ll = LL_Base rep ty" "st' = st" using r by (auto simp: cg_return_def)
    then show ?thesis using ro wk f VR_Scalar lowered_ok_nil[OF 1(3)] by (auto simp: fits_def)
  next
    case (VR_Buf n)
    then have "S = []" "ll = LL_Base rep ty" "st' = st" using r by (auto simp: cg_return_def)
    then show ?thesis using ro wk f VR_Buf lowered_ok_nil[OF 1(3)] by (auto simp: fits_def)
  next
    case (VR_Ptr n)
    then have "S = []" "ll = LL_Base rep ty" "st' = st" using r by (auto simp: cg_return_def)
    then show ?thesis using ro wk f VR_Ptr lowered_ok_nil[OF 1(3)] by (auto simp: fits_def)
  qed
next
  case (2 cg t f)
  obtain fldTys where tt: "core_term_type (CG_TyEnv cg) NotGhost t = Some (CoreTy_Record fldTys)" and mo: "map_of fldTys f = Some ty"
    using record_proj_typed[OF 2(6)] by blast
  from 2(2) obtain S1 ll1 where fr: "freeze_lvalue cg t st = Inr ((S1, ll1), st')" and S: "S = S1" and ll: "ll = LL_Field ll1 f ty"
    using 2(6) by (auto simp: freeze_lvalue.simps ty_of_Inr cg_return_def elim!: cg_bind_InrE)
  obtain E1 ds1 where lo: "lowered_ok prog rt (E, ds) st S1 st' (E1, ds1)" and lt: "ll_type ll1 = CoreTy_Record fldTys"
    and lok: "ll_ok E1 (CG_TyEnv cg) ll1"
    using 2(1)[OF ty_of_Some[OF 2(6)] fr 2(3,4) term_fits_RecordProj[OF 2(5)] tt] by blast
  have wk: "is_well_kinded (CG_TyEnv cg) ty" using term_type_wk(1)[OF 2(3,6)] .
  have f: "fits (CG_TyEnv cg) ty" using term_fits_ty[OF 2(5,6)] .
  show ?case unfolding S ll using lo lt lok mo wk f by (auto simp: fits_def)
next
  case (3 cg t c)
  obtain dtName args tyvars payloadTy where tt: "core_term_type (CG_TyEnv cg) NotGhost t = Some (CoreTy_Datatype dtName args)"
    using variant_proj_typed[OF 3(6)] by blast
  from 3(2) obtain S1 ll1 where fr: "freeze_lvalue cg t st = Inr ((S1, ll1), st')" and S: "S = S1" and ll: "ll = LL_Payload ll1 c ty"
    using 3(6) by (auto simp: freeze_lvalue.simps ty_of_Inr cg_return_def elim!: cg_bind_InrE)
  obtain E1 ds1 where lo: "lowered_ok prog rt (E, ds) st S1 st' (E1, ds1)" and lt: "ll_type ll1 = CoreTy_Datatype dtName args"
    and lok: "ll_ok E1 (CG_TyEnv cg) ll1"
    using 3(1)[OF ty_of_Some[OF 3(6)] fr 3(3,4) term_fits_VariantProj[OF 3(5)] tt] by blast
  have wk: "is_well_kinded (CG_TyEnv cg) ty" using term_type_wk(1)[OF 3(3,6)] .
  have f: "fits (CG_TyEnv cg) ty" using term_fits_ty[OF 3(5,6)] .
  show ?case unfolding S ll using lo lt lok wk f by (auto simp: fits_def)
next
  case (4 cg t idxs)
  obtain dims where tt: "core_term_type (CG_TyEnv cg) NotGhost t = Some (CoreTy_Array ty dims)"
    and lens: "length idxs = length dims"
    and idxty: "\<forall>i \<in> set idxs. core_term_type (CG_TyEnv cg) NotGhost i = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
    using array_proj_typed[OF 4(6)] by blast
  let ?vf = "\<lambda>e. cg_bind (fresh_name (CG_Fun cg) ''idx'') (\<lambda>v. cg_return (v, [MS_DeclScalar v CTy_U64, MS_Assign v e]))"
  have unf: "freeze_lvalue cg (CoreTm_ArrayProj t idxs) st =
      cg_bind (freeze_lvalue cg t) (\<lambda>(S, ll).
      cg_bind (cg_mapM (lower_term cg) idxs) (\<lambda>rs.
      cg_bind (cg_mapM ?vf (map snd rs)) (\<lambda>vs.
      cg_return (S @ concat (map fst rs) @ concat (map snd vs), LL_Index ll (map fst vs) ty)))) st"
    unfolding freeze_lvalue.simps by (simp add: cg_bind_def ty_of_Some[OF 4(6)])
  from 4(2)[unfolded unf] obtain r1 st1 where fr': "freeze_lvalue cg t st = Inr (r1, st1)"
    and k1: "(\<lambda>(S, ll). cg_bind (cg_mapM (lower_term cg) idxs) (\<lambda>rs.
      cg_bind (cg_mapM ?vf (map snd rs)) (\<lambda>vs.
      cg_return (S @ concat (map fst rs) @ concat (map snd vs), LL_Index ll (map fst vs) ty)))) r1 st1 = Inr ((S, ll), st')"
    by (rule cg_bind_InrE)
  obtain S1 ll1 where r1: "r1 = (S1, ll1)" by (cases r1)
  have fr: "freeze_lvalue cg t st = Inr ((S1, ll1), st1)" using fr' r1 by simp
  from k1[unfolded r1 case_prod_conv] obtain rs st2 where lm: "cg_mapM (lower_term cg) idxs st1 = Inr (rs, st2)"
    and k2: "cg_bind (cg_mapM ?vf (map snd rs)) (\<lambda>vs.
      cg_return (S1 @ concat (map fst rs) @ concat (map snd vs), LL_Index ll1 (map fst vs) ty)) st2 = Inr ((S, ll), st')"
    by (rule cg_bind_InrE)
  from k2 obtain vs st3 where lv: "cg_mapM ?vf (map snd rs) st2 = Inr (vs, st3)"
    and k3: "cg_return (S1 @ concat (map fst rs) @ concat (map snd vs), LL_Index ll1 (map fst vs) ty) st3 = Inr ((S, ll), st')"
    by (rule cg_bind_InrE)
  from k3 have S: "S = S1 @ concat (map fst rs) @ concat (map snd vs)" and ll: "ll = LL_Index ll1 (map fst vs) ty" and st': "st' = st3"
    by (auto simp: cg_return_def)
  note tfs = term_fits_ArrayProj[OF 4(5)]
  obtain E1 ds1 where lo1: "lowered_ok prog rt (E, ds) st S1 st1 (E1, ds1)" and lt: "ll_type ll1 = CoreTy_Array ty dims"
    and lok: "ll_ok E1 (CG_TyEnv cg) ll1"
    using 4(1)[OF ty_of_Some[OF 4(6)] fr 4(3,4) tfs[THEN conjunct1] tt] by blast
  have ok1: "cg_ok prog E1 cg" using cg_ok_mono[OF lowered_ok_env_le'[OF lo1] 4(3)] .
  obtain E2 ds2 where lo2: "lowered_ok prog rt (E1, ds1) st1 (concat (map fst rs)) st2 (E2, ds2)"
    and idx: "\<forall>r \<in> set rs. u64_ok E2 (snd r)"
    using lower_indices_ok[OF lm _ ok1 lowered_ok_scope[OF lo1]] lower_ok(1) tfs idxty by blast
  have idx': "\<forall>e \<in> set (map snd rs). u64_ok E2 e" using idx by auto
  obtain E3 ds3 where lo3: "lowered_ok prog rt (E2, ds2) st2 (concat (map snd vs)) st' (E3, ds3)"
    and vsok: "\<forall>v \<in> set (map fst vs). fmlookup E3 v = Some (VT_Scalar CTy_U64)"
    using freeze_indices_ok[OF lv[folded st'] lowered_ok_scope[OF lo2] idx', where rt = rt] by blast
  have lenvs: "length vs = length dims"
    using cg_mapM_length[OF lv] cg_mapM_length[OF lm] lens by simp
  have lok3: "ll_ok E3 (CG_TyEnv cg) ll1"
    using ll_ok_mono[OF env_le_trans[OF lowered_ok_env_le'[OF lo2] lowered_ok_env_le'[OF lo3]] lok] .
  have wk: "is_well_kinded (CG_TyEnv cg) ty" using term_type_wk(1)[OF 4(3,6)] .
  have f: "fits (CG_TyEnv cg) ty" using term_fits_ty[OF 4(5,6)] .
  have lo: "lowered_ok prog rt (E, ds) st S st' (E3, ds3)"
    unfolding S using lowered_ok_append[OF lowered_ok_append[OF lo1 lo2] lo3] by simp
  show ?case unfolding ll using lo lok3 lt lenvs vsok wk f by (auto simp: fits_def)
next
  case (5 cg ty' t)
  from cast_typed[OF 5(6)] obtain fromTy where ty': "ty = ty'" and ft: "core_term_type (CG_TyEnv cg) NotGhost t = Some fromTy"
    and co: "cast_ok (CG_TyEnv cg) fromTy ty'" by blast
  have arr: "is_array_type ty'" using 5(2) by (auto simp: freeze_lvalue.simps internal_def cg_fail_def split: if_splits)
  from 5(2) obtain S1 ll1 where fr: "freeze_lvalue cg t st = Inr ((S1, ll1), st')" and S: "S = S1" and ll: "ll = LL_Cast ll1 ty'"
    using arr by (auto simp: freeze_lvalue.simps cg_return_def elim!: cg_bind_InrE)
  obtain E1 ds1 where lo: "lowered_ok prog rt (E, ds) st S1 st' (E1, ds1)" and lt: "ll_type ll1 = fromTy"
    and lok: "ll_ok E1 (CG_TyEnv cg) ll1"
    using 5(1)[OF arr fr 5(3,4) term_fits_Cast[OF 5(5)] ft] by blast
  have aco: "array_cast_ok fromTy ty'" using co arr by (cases ty') (auto simp: cast_ok_def)
  have wk: "is_well_kinded (CG_TyEnv cg) ty'" using term_type_wk(1)[OF 5(3,6)] ty' by simp
  have f: "fits (CG_TyEnv cg) ty'" using term_fits_ty[OF 5(5,6)] ty' by simp
  show ?case unfolding S ll ty' using lo lt lok aco wk f by (auto simp: fits_def)
qed (auto simp: freeze_lvalue.simps internal_def cg_fail_def)


section \<open>Stores\<close>

lemma lower_store_ok:
  assumes "lower_store cg lv ty e st = Inr (S, st')" and "cg_ok prog E cg" and "scope_ok prog (E, ds) st"
    and "term_fits (CG_TyEnv cg) lv" and "core_term_type (CG_TyEnv cg) NotGhost lv = Some ty"
    and "expr_ok E e (res_cty ty)" and "fits (CG_TyEnv cg) ty"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds')"
proof -
  have "(\<exists>x n cty. lv = CoreTm_Var x \<and> fmlookup (CG_Vars cg) x = Some (VR_Scalar n cty) \<and> S = [MS_Assign n e] \<and> st' = st)
      \<or> cg_bind (lower_addr cg lv) (\<lambda>(S, a). cg_return (S @ [store_at cg ty a e])) st = Inr (S, st')"
    using assms(1) unfolding lower_store_def
    by (cases lv) (auto simp: cg_return_def split: option.splits VarRep.splits simp del: lower_addr.simps)
  then have "(\<exists>x n cty. lv = CoreTm_Var x \<and> fmlookup (CG_Vars cg) x = Some (VR_Scalar n cty) \<and> S = [MS_Assign n e] \<and> st' = st)
      \<or> (\<exists>S1 a. lower_addr cg lv st = Inr ((S1, a), st') \<and> S = S1 @ [store_at cg ty a e])"
    by (auto simp: cg_return_def split: prod.splits elim!: cg_bind_InrE simp del: lower_addr.simps)
  then show ?thesis
  proof (elim disjE exE conjE)
    fix x n cty assume lv: "lv = CoreTm_Var x" and rep: "fmlookup (CG_Vars cg) x = Some (VR_Scalar n cty)"
      and S: "S = [MS_Assign n e]" and st': "st' = st"
    obtain ty' where "tyenv_lookup_var (CG_TyEnv cg) x = Some ty'" "rep_ok E (CG_TyEnv cg) ty' (VR_Scalar n cty)"
      using cg_ok_var[OF assms(2) rep] by blast
    then have ro: "rep_ok E (CG_TyEnv cg) ty (VR_Scalar n cty)" using var_typed[OF assms(5)[unfolded lv]] by simp
    then have "scalar_ty ty = Some cty" "fmlookup E n = Some (VT_Scalar cty)" by simp_all
    then show ?thesis unfolding S st' using assms(3,6) by (auto intro!: exI assign_ok[where cty' = cty] simp: ty_compat_def)
  next
    fix S1 a assume la: "lower_addr cg lv st = Inr ((S1, a), st')" and S: "S = S1 @ [store_at cg ty a e]"
    obtain E1 ds1 where lo1: "lowered_ok prog rt (E, ds) st S1 st' (E1, ds1)" and a: "expr_ok E1 a CTy_CharPtr"
      by (rule lower_addr_ok[OF la assms(2,3,4)])
    have le: "env_le E E1" by (rule lowered_ok_env_le'[OF lo1])
    have sz: "u64_ok E1 (cg_size cg ty)" using cg_size_ok[OF cg_ok_mono[OF le assms(2)] term_type_wk(1)[OF assms(2,5)] assms(7)] .
    have "lowered_ok prog rt (E1, ds1) st' [store_at cg ty a e] st' (E1, ds1)"
      by (rule store_at_ok[OF lowered_ok_scope[OF lo1] a expr_ok_mono[OF le assms(6)] sz])
    then show ?thesis unfolding S using lowered_ok_append[OF lo1] by blast
  qed
qed

lemma store_lazy_ok:
  assumes "store_lazy cg ll ty e st = Inr (S, st')" and "cg_ok prog E cg" and "scope_ok prog (E, ds) st"
    and "ll_ok E (CG_TyEnv cg) ll" and "ll_type ll = ty"
    and "expr_ok E e (res_cty ty)" and "u64_ok E (cg_size cg ty)"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds')"
proof -
  have "(\<exists>n cty ty'. ll = LL_Base (VR_Scalar n cty) ty' \<and> S = [MS_Assign n e] \<and> st' = st)
      \<or> cg_bind (lazy_addr cg ll) (\<lambda>(S, a). cg_return (S @ [store_at cg ty a e])) st = Inr (S, st')"
    using assms(1) unfolding store_lazy_def
    apply (cases ll)
    subgoal for rep ty' by (cases rep) (auto simp: cg_return_def simp del: lazy_addr.simps)
    by (auto simp del: lazy_addr.simps)
  then have "(\<exists>n cty ty'. ll = LL_Base (VR_Scalar n cty) ty' \<and> S = [MS_Assign n e] \<and> st' = st)
      \<or> (\<exists>S1 a. lazy_addr cg ll st = Inr ((S1, a), st') \<and> S = S1 @ [store_at cg ty a e])"
    by (auto simp: cg_return_def split: prod.splits elim!: cg_bind_InrE simp del: lazy_addr.simps)
  then show ?thesis
  proof (elim disjE exE conjE)
    fix n cty ty' assume ll: "ll = LL_Base (VR_Scalar n cty) ty'" and S: "S = [MS_Assign n e]" and st': "st' = st"
    have "scalar_ty ty = Some cty" "fmlookup E n = Some (VT_Scalar cty)" using assms(4,5) unfolding ll by simp_all
    then show ?thesis unfolding S st' using assms(3,6) by (auto intro!: exI assign_ok[where cty' = cty] simp: ty_compat_def)
  next
    fix S1 a assume la: "lazy_addr cg ll st = Inr ((S1, a), st')" and S: "S = S1 @ [store_at cg ty a e]"
    obtain E1 ds1 where lo1: "lowered_ok prog rt (E, ds) st S1 st' (E1, ds1)" and a: "expr_ok E1 a CTy_CharPtr"
      using lazy_addr_ok[OF la assms(2,3,4)] by blast
    have le: "env_le E E1" by (rule lowered_ok_env_le'[OF lo1])
    have "lowered_ok prog rt (E1, ds1) st' [store_at cg ty a e] st' (E1, ds1)"
      by (rule store_at_ok[OF lowered_ok_scope[OF lo1] a expr_ok_mono[OF le assms(6)]]) (use assms(7) le in \<open>auto simp: u64_ok_def expr_type_mono\<close>)
    then show ?thesis unfolding S using lowered_ok_append[OF lo1] by blast
  qed
qed


section \<open>Call results\<close>

(* The result of a call at its (instantiated, possibly cast) result type. *)
fun cres_ok :: "MTyEnv \<Rightarrow> CoreType \<Rightarrow> CallRes \<Rightarrow> bool" where
  "cres_ok E ty (CR_Scalar e) = expr_ok E e (res_cty ty)"
| "cres_ok E ty (CR_Place p) = expr_ok E p CTy_CharPtr"
| "cres_ok E ty CR_Unit = True"

lemma cres_ok_mono: "env_le E E' \<Longrightarrow> cres_ok E ty res \<Longrightarrow> cres_ok E' ty res"
  by (cases res) (auto intro: expr_ok_mono)

lemma cres_ok_of_res_ok:
  assumes "res_ok E info res"
  shows "cres_ok E (apply_subst s (FI_ReturnType info)) res"
proof (cases res)
  case (CR_Scalar e)
  then obtain cty where "ret_kind (FI_ReturnType info) = RK_Scalar cty" "expr_ok E e cty" using assms by auto
  then have "scalar_ty (FI_ReturnType info) = Some cty" by (auto simp: ret_kind_def split: option.splits if_splits)
  then show ?thesis using \<open>expr_ok E e cty\<close> CR_Scalar by (simp add: res_cty_apply_subst_scalar)
qed (use assms in auto)

lemma call_result_expr_cres:
  assumes "cres_ok E ty res" and "call_result_expr ty res = Some e"
  shows "expr_ok E e (res_cty ty)"
  using assms by (cases res) (auto simp: call_result_expr_def intro: expr_ok_load_at)

lemma cast_ok_wk: "cast_ok env a b \<Longrightarrow> is_runtime_type env b \<Longrightarrow> is_well_kinded env b"
  unfolding cast_ok_def by (cases b) auto

lemma cast_call_res_ok:
  assumes "cast_call_res cg retTy castOpt res st = Inr ((S, res'), st')" and "cg_ok prog E cg" and "scope_ok prog (E, ds) st"
    and "cres_ok E retTy res" and "cast_result_type (CG_TyEnv cg) NotGhost retTy castOpt = Some ty"
    and "is_well_kinded (CG_TyEnv cg) retTy" and "is_runtime_type (CG_TyEnv cg) retTy" and "fits (CG_TyEnv cg) ty"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> cres_ok E' ty res'"
proof (cases castOpt)
  case None
  then have "S = []" "res' = res" "st' = st" "ty = retTy" using assms(1,5) by (auto simp: cast_call_res_def cast_result_type_def cg_return_def)
  then show ?thesis using lowered_ok_nil[OF assms(3)] assms(4) by auto
next
  case (Some toTy)
  have ty: "ty = toTy" and co: "cast_ok (CG_TyEnv cg) retTy toTy" and rtt: "is_runtime_type (CG_TyEnv cg) toTy"
    using assms(5) Some by (auto simp: cast_result_type_def split: if_splits)
  from assms(1) obtain e S1 e1 where cr: "call_result_expr retTy res = Some e"
    and cres: "cast_result cg retTy toTy e st = Inr ((S1, e1), st')"
    and S: "S = S1" and res': "res' = (if is_scalar toTy then CR_Scalar e1 else CR_Place e1)"
    unfolding cast_call_res_def Some by (auto simp: cg_return_def internal_def cg_fail_def split: option.splits elim!: cg_bind_InrE)
  have e: "expr_ok E e (res_cty retTy)" by (rule call_result_expr_cres[OF assms(4) cr])
  obtain E1 ds1 where lo: "lowered_ok prog rt (E, ds) st S1 st' (E1, ds1)" and e1: "expr_ok E1 e1 (res_cty toTy)"
    using cast_result_ok[OF cres assms(2,3) e co assms(7) rtt assms(6) cast_ok_wk[OF co rtt] assms(8)[unfolded ty]] by blast
  show ?thesis unfolding S ty res' using lo e1 by (cases "scalar_ty toTy") (auto simp: res_cty_def)
qed

lemma call_store_ok:
  assumes "call_store cg store ty res st = Inr (S, st')" and "cres_ok E ty res" and "scope_ok prog (E, ds) st"
    and "\<And>e S st'. store e st = Inr (S, st') \<Longrightarrow> expr_ok E e (res_cty ty) \<Longrightarrow> \<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds')"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds')"
proof (cases "call_result_expr ty res")
  case None
  then have "S = []" "st' = st" using assms(1) by (auto simp: call_store_def cg_return_def)
  then show ?thesis using lowered_ok_nil[OF assms(3)] by auto
next
  case (Some e)
  then have "store e st = Inr (S, st')" using assms(1) by (simp add: call_store_def)
  then show ?thesis using assms(4) call_result_expr_cres[OF assms(2) Some] by blast
qed


section \<open>Locals\<close>

lemma decl_local_ok:
  assumes "decl_local cg x ty st = Inr ((decl, rep), st')" and "cg_ok prog E cg" and "scope_ok prog (E, ds) st"
    and "is_well_kinded (CG_TyEnv cg) ty" and "fits (CG_TyEnv cg) ty"
  obtains n where "lowered_ok prog rt (E, ds) st [decl] st' (fmupd n (case scalar_ty ty of Some cty \<Rightarrow> VT_Scalar cty | None \<Rightarrow> VT_Buf) E, n # ds)"
    and "rep_ok (fmupd n (case scalar_ty ty of Some cty \<Rightarrow> VT_Scalar cty | None \<Rightarrow> VT_Buf) E) (CG_TyEnv cg) ty rep"
    and "n |\<notin>| fmdom E"
    and "rep = (case scalar_ty ty of Some cty \<Rightarrow> VR_Scalar n cty | None \<Rightarrow> VR_Buf n)"
proof -
  from assms(1) obtain n where ln: "local_name (CG_Fun cg) x st = Inr (n, st')"
    and decl: "decl = (case scalar_ty ty of Some cty \<Rightarrow> MS_DeclScalar n cty | None \<Rightarrow> MS_DeclBuf n (buf_size (cg_size cg ty)))"
    and rep: "rep = (case scalar_ty ty of Some cty \<Rightarrow> VR_Scalar n cty | None \<Rightarrow> VR_Buf n)"
    by (auto simp: decl_local_def cg_return_def split: option.splits elim!: cg_bind_InrE)
  have nd: "n |\<notin>| fmdom E" using local_decl_facts[OF assms(3) ln] by blast
  show thesis
  proof (cases "scalar_ty ty")
    case (Some cty)
    show thesis
      by (rule that[of n]) (use Some decl rep local_scalar_ok[OF assms(3) ln, where cty = cty] nd in auto)
  next
    case None
    have sz: "u64_ok E (buf_size (cg_size cg ty))" using cg_buf_size_ok[OF assms(2,4,5)] .
    show thesis
      by (rule that[of n]) (use None decl rep local_buf_ok[OF assms(3) ln sz] nd in auto)
  qed
qed

lemma init_local_ok:
  assumes "init_local cg rep ty e st = Inr (S, st')" and "scope_ok prog (E, ds) st" and "rep_ok E (CG_TyEnv cg) ty rep"
    and "rep = (case scalar_ty ty of Some cty \<Rightarrow> VR_Scalar n cty | None \<Rightarrow> VR_Buf n)"
    and "expr_ok E e (res_cty ty)" and "u64_ok E (cg_size cg ty)"
  shows "lowered_ok prog rt (E, ds) st S st (E, ds) \<and> st' = st"
proof (cases "scalar_ty ty")
  case (Some cty)
  then have rep: "rep = VR_Scalar n cty" using assms(4) by simp
  have "S = [MS_Assign n e]" "st' = st" using assms(1) unfolding rep by (auto simp: init_local_def cg_return_def)
  then show ?thesis using assms(2,3,5) Some unfolding rep by (auto intro!: assign_ok[where cty' = cty] simp: ty_compat_def)
next
  case None
  then have rep: "rep = VR_Buf n" using assms(4) by simp
  have "S = [MS_Copy (ME_AddrOf n) e (cg_size cg ty)]" "st' = st" using assms(1) unfolding rep by (auto simp: init_local_def cg_return_def)
  then show ?thesis using assms(2,3,5,6) None unfolding rep
    by (auto intro!: copy_ok[where dty = CTy_CharPtr and sty = CTy_CharPtr] simp: expr_ok_def res_cty_def)
qed

end
