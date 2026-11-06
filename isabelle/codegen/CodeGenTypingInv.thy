theory CodeGenTypingInv
  imports CodeGenTypingBase
begin

(* ========================================================================== *)
(* The typing theorem: the invariant and the lemmas about the helpers        *)
(* ========================================================================== *)

(* The invariant relating the generator's environment CGEnv to the MiniC
   typing environment is cg_ok (section 8 of DESIGN.md: "the CGEnv is
   consistent with the Core typing context and the MTyEnv"); scope_ok says
   that every name the MiniC scope knows is among the names the generator
   has recorded as used, so that every fresh name can be declared; and
   lowered_ok is the conclusion every lowering lemma has: the statements
   are accepted by stmts_ok, the environment only grows, the scope and the
   state are still related, the statements are syntactically well-formed,
   and the set of used names grew. *)


section \<open>The program and the functions\<close>

(* The C return type of a return kind. *)
fun rk_cty :: "RetKind \<Rightarrow> CTy option" where
  "rk_cty (RK_Scalar cty) = Some cty"
| "rk_cty RK_Unit = None"
| "rk_cty RK_Buf = None"

(* The parameter types of a function's prototype (section 3.4). *)
definition param_ctys :: "FunInfo \<Rightarrow> CTy list" where
  "param_ctys info =
    (case ret_kind (FI_ReturnType info) of RK_Buf \<Rightarrow> [CTy_CharPtr] | _ \<Rightarrow> [])
    @ map (\<lambda>_. CTy_U64) (FI_TyArgs info)
    @ map (\<lambda>(ty, vor, _). param_cty ty vor) (FI_TmArgs info)"

lemma fun_params_ctys:
  "length (CF_Args cf) = length (FI_TmArgs info) \<Longrightarrow> map snd (fun_params cf info) = param_ctys info"
  by (auto simp: fun_params_def param_ctys_def split_beta split: RetKind.splits intro!: nth_equalityI)

(* Every function of the Core signature table has a MiniC function of the
   program with the prototype of section 3.4, and no ghost parameters. *)
definition prog_ok :: "MProgram \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "prog_ok prog env =
    (\<forall>f info. fmlookup (TE_Functions env) f = Some info \<longrightarrow>
       no_ghost_params info
       \<and> (\<exists>fn. lookup_fun prog f = Some fn \<and> map snd (MF_Params fn) = param_ctys info
                \<and> MF_Ret fn = rk_cty (ret_kind (FI_ReturnType info))))"


section \<open>Representations\<close>

(* A representation is typed by E for a variable of Core type ty; a lazy
   lvalue's nodes are typed, well-kinded and of fitting size, with its
   index variables uint64_t scalars. TV is the set of type variables in
   scope (their size parameters are in E, see cg_ok). *)
fun rep_ok :: "MTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> CoreType \<Rightarrow> VarRep \<Rightarrow> bool"
and ll_ok :: "MTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> LazyLv \<Rightarrow> bool" where
  "rep_ok E env ty (VR_Scalar n cty) = (scalar_ty ty = Some cty \<and> fmlookup E n = Some (VT_Scalar cty))"
| "rep_ok E env ty (VR_Buf n) = (scalar_ty ty = None \<and> fmlookup E n = Some VT_Buf)"
| "rep_ok E env ty (VR_Ptr n) = (fmlookup E n = Some (VT_Scalar CTy_CharPtr))"
| "rep_ok E env ty (VR_Lazy ll) = (ll_type ll = ty \<and> ll_ok E env ll)"
| "ll_ok E env (LL_Base rep ty) =
    (rep_ok E env ty rep \<and> (\<forall>ll. rep \<noteq> VR_Lazy ll)
     \<and> is_well_kinded env ty \<and> size_fits env 0 (\<lambda>_. 0) ty)"
| "ll_ok E env (LL_Field ll f ty) = (ll_ok E env ll \<and> is_well_kinded env ty \<and> size_fits env 0 (\<lambda>_. 0) ty)"
| "ll_ok E env (LL_Payload ll c ty) = (ll_ok E env ll \<and> is_well_kinded env ty \<and> size_fits env 0 (\<lambda>_. 0) ty)"
| "ll_ok E env (LL_Index ll vs ty) =
    (ll_ok E env ll \<and> is_well_kinded env ty \<and> size_fits env 0 (\<lambda>_. 0) ty
     \<and> (\<forall>v \<in> set vs. fmlookup E v = Some (VT_Scalar CTy_U64)))"
| "ll_ok E env (LL_Cast ll ty) = (ll_ok E env ll \<and> is_well_kinded env ty \<and> size_fits env 0 (\<lambda>_. 0) ty)"

(* The size check reads only the datatype tables of the environment. *)
lemma tsz_fits_cong_env:
  assumes "TE_DataCtors env' = TE_DataCtors env" and "TE_DataCtorsByType env' = TE_DataCtorsByType env"
  shows "tsz_fits fuel env' P sz ty = tsz_fits fuel env P sz ty"
proof (induction fuel arbitrary: ty sz)
  case 0
  show ?case
  proof (induction ty)
    case (CoreTy_Record flds)
    have "\<And>fld. fld \<in> set flds \<Longrightarrow> tsz_fits 0 env' P sz (snd fld) = tsz_fits 0 env P sz (snd fld)"
      using CoreTy_Record.IH[OF _ snds.intros] by blast
    then show ?case by (simp add: tsz_cong_env[OF assms] list_all_iff)
  qed (simp_all add: tsz_fits_0_Datatype tsz_cong_env[OF assms] list_all_iff)
next
  case (Suc fuel)
  note IH_fuel = Suc.IH
  show ?case
  proof (induction ty)
    case (CoreTy_Record flds)
    have "\<And>fld. fld \<in> set flds \<Longrightarrow> tsz_fits (Suc fuel) env' P sz (snd fld) = tsz_fits (Suc fuel) env P sz (snd fld)"
      using CoreTy_Record.IH[OF _ snds.intros] by blast
    then show ?case by (simp add: tsz_cong_env[OF assms] list_all_iff)
  next
    case (CoreTy_Datatype dtName args)
    have ctors: "dt_ctors env' dtName = dt_ctors env dtName" by (simp add: dt_ctors_def assms(2))
    have args: "list_all (tsz_fits (Suc fuel) env' P sz) args = list_all (tsz_fits (Suc fuel) env P sz) args"
      using CoreTy_Datatype.IH by (simp add: list_all_iff)
    have m: "tsz (Suc fuel) env' P sz = tsz (Suc fuel) env P sz" by (rule ext) (rule tsz_cong_env[OF assms])
    have "\<And>ctor. ctor_tsz_fits fuel env' P (map (tsz (Suc fuel) env' P sz) args) ctor
                 = ctor_tsz_fits fuel env P (map (tsz (Suc fuel) env P sz) args) ctor"
      by (simp add: ctor_tsz_fits_def assms(1) m IH_fuel split: option.splits)
    then show ?case
      unfolding tsz_fits_Suc_Datatype using args ctors
      by (simp add: tsz_cong_env[OF assms] list_all_iff)
  qed (simp_all add: tsz_cong_env[OF assms] list_all_iff)
qed

lemma size_fits_cong_env:
  assumes "TE_DataCtors env' = TE_DataCtors env" and "TE_DataCtorsByType env' = TE_DataCtorsByType env"
  shows "size_fits env' P sz ty = size_fits env P sz ty"
  unfolding size_fits_def dt_fuel_def assms(2) by (rule tsz_fits_cong_env[OF assms])

lemma ll_ok_type: "ll_ok E env ll \<Longrightarrow> is_well_kinded env (ll_type ll) \<and> size_fits env 0 (\<lambda>_. 0) (ll_type ll)"
  by (cases ll) simp_all

lemma rep_ok_mono_aux:
  "env_le E E' \<Longrightarrow> \<forall>ty. rep_ok E env ty rep \<longrightarrow> rep_ok E' env ty rep"
  "env_le E E' \<Longrightarrow> ll_ok E env ll \<longrightarrow> ll_ok E' env ll"
  by (induction rep and ll) (auto simp: env_le_def)

lemma rep_ok_mono: "env_le E E' \<Longrightarrow> rep_ok E env ty rep \<Longrightarrow> rep_ok E' env ty rep"
  using rep_ok_mono_aux(1) by blast

lemma ll_ok_mono: "env_le E E' \<Longrightarrow> ll_ok E env ll \<Longrightarrow> ll_ok E' env ll"
  using rep_ok_mono_aux(2) by blast

(* The datatype tables and the kinding context are all ll_ok and rep_ok
   read of the Core environment. *)
lemma rep_ok_cong_env:
  assumes "TE_DataCtors env = TE_DataCtors env'" and "TE_DataCtorsByType env = TE_DataCtorsByType env'"
    and "TE_TypeVars env = TE_TypeVars env'" and "TE_Datatypes env = TE_Datatypes env'"
  shows "rep_ok E env ty rep = rep_ok E env' ty rep" and "ll_ok E env ll = ll_ok E env' ll"
proof -
  have wk: "\<And>ty. is_well_kinded env ty = is_well_kinded env' ty"
    using assms by (intro is_well_kinded_cong_env) simp_all
  have sf: "\<And>ty. size_fits env 0 (\<lambda>_. 0) ty = size_fits env' 0 (\<lambda>_. 0) ty"
    using assms by (intro size_fits_cong_env) simp_all
  have "(\<forall>ty. rep_ok E env ty rep = rep_ok E env' ty rep) \<and> True" "ll_ok E env ll = ll_ok E env' ll"
    by (induction rep and ll) (simp_all add: wk sf)
  then show "rep_ok E env ty rep = rep_ok E env' ty rep" and "ll_ok E env ll = ll_ok E env' ll" by simp_all
qed


section \<open>The invariant\<close>

(* The static half of the per-frame relation: the Core context is well
   formed; the size parameters of its type variables are in scope; every
   Core variable's representation is typed for the variable's Core type;
   the return kind is that of the context's return type, with the return
   buffer in scope if there is one; the return type fits; the datatypes'
   tags fit; the program has every function of the signature table. *)
definition cg_ok :: "MProgram \<Rightarrow> MTyEnv \<Rightarrow> CGEnv \<Rightarrow> bool" where
  "cg_ok prog E cg =
    (tyenv_well_formed (CG_TyEnv cg)
     \<and> sizes_in E (fset (TE_TypeVars (CG_TyEnv cg)))
     \<and> (\<forall>x rep. fmlookup (CG_Vars cg) x = Some rep \<longrightarrow>
          (\<exists>ty. tyenv_lookup_var (CG_TyEnv cg) x = Some ty \<and> rep_ok E (CG_TyEnv cg) ty rep))
     \<and> CG_Ret cg = ret_kind (TE_ReturnType (CG_TyEnv cg))
     \<and> (CG_Ret cg = RK_Buf \<longrightarrow> fmlookup E ret_param = Some (VT_Scalar CTy_CharPtr))
     \<and> size_fits (CG_TyEnv cg) 0 (\<lambda>_. 0) (TE_ReturnType (CG_TyEnv cg))
     \<and> (\<forall>d. dt_tags_fit (CG_TyEnv cg) d)
     \<and> prog_ok prog (CG_TyEnv cg))"

lemma cg_okD:
  assumes "cg_ok prog E cg"
  shows cg_ok_wf: "tyenv_well_formed (CG_TyEnv cg)"
    and cg_ok_sizes_in: "sizes_in E (fset (TE_TypeVars (CG_TyEnv cg)))"
    and cg_ok_vars: "\<And>x rep. fmlookup (CG_Vars cg) x = Some rep \<Longrightarrow>
                      \<exists>ty. tyenv_lookup_var (CG_TyEnv cg) x = Some ty \<and> rep_ok E (CG_TyEnv cg) ty rep"
    and cg_ok_ret: "CG_Ret cg = ret_kind (TE_ReturnType (CG_TyEnv cg))"
    and cg_ok_ret_param: "CG_Ret cg = RK_Buf \<Longrightarrow> fmlookup E ret_param = Some (VT_Scalar CTy_CharPtr)"
    and cg_ok_ret_fits: "size_fits (CG_TyEnv cg) 0 (\<lambda>_. 0) (TE_ReturnType (CG_TyEnv cg))"
    and cg_ok_tags: "\<And>d. dt_tags_fit (CG_TyEnv cg) d"
    and cg_ok_prog: "prog_ok prog (CG_TyEnv cg)"
proof -
  note c = assms[unfolded cg_ok_def]
  show "tyenv_well_formed (CG_TyEnv cg)" using c by (elim conjE)
  show "sizes_in E (fset (TE_TypeVars (CG_TyEnv cg)))" using c by (elim conjE)
  show "\<And>x rep. fmlookup (CG_Vars cg) x = Some rep \<Longrightarrow>
          \<exists>ty. tyenv_lookup_var (CG_TyEnv cg) x = Some ty \<and> rep_ok E (CG_TyEnv cg) ty rep"
    using c by (elim conjE) blast
  show "CG_Ret cg = ret_kind (TE_ReturnType (CG_TyEnv cg))" using c by (elim conjE)
  show "CG_Ret cg = RK_Buf \<Longrightarrow> fmlookup E ret_param = Some (VT_Scalar CTy_CharPtr)" using c by (elim conjE) simp
  show "size_fits (CG_TyEnv cg) 0 (\<lambda>_. 0) (TE_ReturnType (CG_TyEnv cg))" using c by (elim conjE)
  show "\<And>d. dt_tags_fit (CG_TyEnv cg) d" using c by (elim conjE) simp
  show "prog_ok prog (CG_TyEnv cg)" using c by (elim conjE)
qed

lemma cg_okI:
  assumes "tyenv_well_formed (CG_TyEnv cg)" and "sizes_in E (fset (TE_TypeVars (CG_TyEnv cg)))"
    and "\<And>x rep. fmlookup (CG_Vars cg) x = Some rep \<Longrightarrow>
           \<exists>ty. tyenv_lookup_var (CG_TyEnv cg) x = Some ty \<and> rep_ok E (CG_TyEnv cg) ty rep"
    and "CG_Ret cg = ret_kind (TE_ReturnType (CG_TyEnv cg))"
    and "CG_Ret cg = RK_Buf \<Longrightarrow> fmlookup E ret_param = Some (VT_Scalar CTy_CharPtr)"
    and "size_fits (CG_TyEnv cg) 0 (\<lambda>_. 0) (TE_ReturnType (CG_TyEnv cg))"
    and "\<And>d. dt_tags_fit (CG_TyEnv cg) d"
    and "prog_ok prog (CG_TyEnv cg)"
  shows "cg_ok prog E cg"
  using assms unfolding cg_ok_def by blast

lemma cg_ok_mono:
  assumes le: "env_le E E'" and ok: "cg_ok prog E cg"
  shows "cg_ok prog E' cg"
proof (rule cg_okI)
  fix x rep assume "fmlookup (CG_Vars cg) x = Some rep"
  then obtain ty where "tyenv_lookup_var (CG_TyEnv cg) x = Some ty" "rep_ok E (CG_TyEnv cg) ty rep"
    using cg_ok_vars[OF ok] by blast
  then show "\<exists>ty. tyenv_lookup_var (CG_TyEnv cg) x = Some ty \<and> rep_ok E' (CG_TyEnv cg) ty rep"
    using rep_ok_mono[OF le] by blast
qed (use cg_okD[OF ok] sizes_in_mono[OF le] env_le_lookup[OF le] in blast)+

lemma cg_ok_sizes:
  assumes "cg_ok prog E cg" and "is_well_kinded (CG_TyEnv cg) ty"
  shows "sizes_in E (type_tyvars ty)"
  using cg_ok_sizes_in[OF assms(1)] is_well_kinded_type_tyvars_subset[OF assms(2)] by (rule sizes_in_subset)

lemma cg_ok_var:
  assumes "cg_ok prog E cg" and "fmlookup (CG_Vars cg) x = Some rep"
  obtains ty where "tyenv_lookup_var (CG_TyEnv cg) x = Some ty" and "rep_ok E (CG_TyEnv cg) ty rep"
  using cg_ok_vars[OF assms] that by blast

(* The nested-scope context (TE_ProofTopLevel cleared) satisfies the same
   invariant. *)
lemma cg_ok_nested:
  assumes ok: "cg_ok prog E cg"
  shows "cg_ok prog E (cg_nested cg)"
proof -
  let ?env = "CG_TyEnv cg"
  let ?env' = "CG_TyEnv cg \<lparr> TE_ProofTopLevel := False \<rparr>"
  have wf: "tyenv_well_formed ?env'"
    using ok by (simp add: cg_ok_def tyenv_well_formed_TE_ProofTopLevel_irrelevant)
  have rep: "\<And>ty rep. rep_ok E ?env' ty rep = rep_ok E ?env ty rep"
    by (rule rep_ok_cong_env(1)) simp_all
  have sf: "\<And>ty. size_fits ?env' 0 (\<lambda>_. 0) ty = size_fits ?env 0 (\<lambda>_. 0) ty"
    by (rule size_fits_cong_env) simp_all
  have A: "CG_TyEnv (cg_nested cg) = ?env'" and B: "CG_Vars (cg_nested cg) = CG_Vars cg"
    and C: "CG_Ret (cg_nested cg) = CG_Ret cg"
    by (simp_all add: cg_nested_def)
  have lk: "\<And>x. tyenv_lookup_var ?env' x = tyenv_lookup_var ?env x"
    by (simp add: tyenv_lookup_var_def split: option.splits)
  have tags: "dt_tags_fit ?env' = dt_tags_fit ?env" by (rule ext) (simp add: dt_tags_fit_def dt_ctors_def)
  have po: "prog_ok prog ?env' = prog_ok prog ?env" by (simp add: prog_ok_def)
  show ?thesis
  proof (rule cg_okI)
    show "tyenv_well_formed (CG_TyEnv (cg_nested cg))" using wf by (simp add: A)
    show "sizes_in E (fset (TE_TypeVars (CG_TyEnv (cg_nested cg))))" using cg_ok_sizes_in[OF ok] by (simp add: A)
    show "\<And>x rep. fmlookup (CG_Vars (cg_nested cg)) x = Some rep \<Longrightarrow>
            \<exists>ty. tyenv_lookup_var (CG_TyEnv (cg_nested cg)) x = Some ty \<and> rep_ok E (CG_TyEnv (cg_nested cg)) ty rep"
      using cg_ok_vars[OF ok] by (simp add: A B lk rep)
    show "CG_Ret (cg_nested cg) = ret_kind (TE_ReturnType (CG_TyEnv (cg_nested cg)))" using cg_ok_ret[OF ok] by (simp add: A C)
    show "CG_Ret (cg_nested cg) = RK_Buf \<Longrightarrow> fmlookup E ret_param = Some (VT_Scalar CTy_CharPtr)"
      using cg_ok_ret_param[OF ok] by (simp add: C)
    show "size_fits (CG_TyEnv (cg_nested cg)) 0 (\<lambda>_. 0) (TE_ReturnType (CG_TyEnv (cg_nested cg)))"
      using cg_ok_ret_fits[OF ok] by (simp add: A sf)
    show "\<And>d. dt_tags_fit (CG_TyEnv (cg_nested cg)) d" using cg_ok_tags[OF ok] by (simp add: A tags)
    show "prog_ok prog (CG_TyEnv (cg_nested cg))" using cg_ok_prog[OF ok] by (simp add: A po)
  qed
qed

(* The scope and the generator's state: every name in the environment, in
   the current scope's declared list and among the functions is in use. *)
definition scope_ok :: "MProgram \<Rightarrow> MScope \<Rightarrow> CGState \<Rightarrow> bool" where
  "scope_ok prog sc st =
    (fset (fmdom (fst sc)) \<subseteq> fset (CS_Used st) \<and> set (snd sc) \<subseteq> fset (CS_Used st)
     \<and> set (fun_names prog) \<subseteq> fset (CS_Used st))"

definition used_le :: "CGState \<Rightarrow> CGState \<Rightarrow> bool" where
  "used_le st st' = (CS_Used st |\<subseteq>| CS_Used st')"

lemma used_le_refl [simp]: "used_le st st"
  by (simp add: used_le_def)

lemma used_le_trans: "used_le st1 st2 \<Longrightarrow> used_le st2 st3 \<Longrightarrow> used_le st1 st3"
  by (auto simp: used_le_def)

lemma scope_ok_used_le: "scope_ok prog sc st \<Longrightarrow> used_le st st' \<Longrightarrow> scope_ok prog sc st'"
  by (auto simp: scope_ok_def used_le_def less_eq_fset.rep_eq)

lemma scope_ok_inner: "scope_ok prog (E, ds) st \<Longrightarrow> scope_ok prog (E, []) st"
  by (simp add: scope_ok_def)

(* The typing context of a body: the program and the declared return type. *)
definition mk_ctx :: "MProgram \<Rightarrow> CTy option \<Rightarrow> MTyCtx" where
  "mk_ctx prog rt = \<lparr> TC_Prog = prog, TC_Ret = rt \<rparr>"

lemma mk_ctx_simps [simp]: "TC_Prog (mk_ctx prog rt) = prog" "TC_Ret (mk_ctx prog rt) = rt"
  by (simp_all add: mk_ctx_def)

(* The conclusion of every lowering lemma. *)
definition lowered_ok :: "MProgram \<Rightarrow> CTy option \<Rightarrow> MScope \<Rightarrow> CGState \<Rightarrow> MStmt list \<Rightarrow> CGState \<Rightarrow> MScope \<Rightarrow> bool" where
  "lowered_ok prog rt sc st S st' sc' =
    (stmts_ok (mk_ctx prog rt) sc S = Some sc' \<and> env_le (fst sc) (fst sc') \<and> scope_ok prog sc' st'
     \<and> (\<forall>l. stmts_wf prog l S) \<and> used_le st st')"

definition expr_ok :: "MTyEnv \<Rightarrow> MExpr \<Rightarrow> CTy \<Rightarrow> bool" where
  "expr_ok E e cty = (expr_type E e = Some cty \<and> expr_wf e)"

lemma expr_ok_mono: "env_le E E' \<Longrightarrow> expr_ok E e cty \<Longrightarrow> expr_ok E' e cty"
  by (simp add: expr_ok_def expr_type_mono)

lemma expr_ok_u64 [simp]: "expr_ok E e CTy_U64 = u64_ok E e"
  by (auto simp: expr_ok_def u64_ok_def)

lemma expr_ok_Var: "fmlookup E x = Some (VT_Scalar cty) \<Longrightarrow> expr_ok E (ME_Var x) cty"
  by (simp add: expr_ok_def)

lemma expr_ok_AddrOf: "fmlookup E x = Some vty \<Longrightarrow> expr_ok E (ME_AddrOf x) CTy_CharPtr"
  by (simp add: expr_ok_def)

lemma expr_ok_Load: "expr_ok E p pty \<Longrightarrow> is_ptr_ty pty \<Longrightarrow> expr_ok E (ME_Load cty p) cty"
  by (simp add: expr_ok_def)

lemma expr_ok_ptr_add: "expr_ok E p pty \<Longrightarrow> is_ptr_ty pty \<Longrightarrow> u64_ok E off \<Longrightarrow> expr_ok E (ptr_add p off) pty"
  by (auto simp: expr_ok_def u64_ok_def ptr_add_def)

lemma expr_ok_PtrAdd: "expr_ok E p pty \<Longrightarrow> is_ptr_ty pty \<Longrightarrow> u64_ok E off \<Longrightarrow> expr_ok E (ME_PtrAdd p off) pty"
  by (auto simp: expr_ok_def u64_ok_def)

lemma expr_ok_compat: "expr_ok E e cty \<Longrightarrow> expr_compat E e cty"
  by (simp add: expr_ok_def expr_compat_def)

lemma expr_ok_compat_ptr: "expr_ok E e cty \<Longrightarrow> is_ptr_ty cty \<Longrightarrow> is_ptr_ty cty' \<Longrightarrow> expr_compat E e cty'"
  by (simp add: expr_ok_def expr_compat_def ty_compat_def)

lemma expr_ok_is_ptr: "expr_ok E e cty \<Longrightarrow> is_ptr_ty cty \<Longrightarrow> expr_is_ptr E e"
  by (simp add: expr_ok_def expr_is_ptr_def)

lemma expr_ok_is_int: "expr_ok E e (CTy_Int s b) \<Longrightarrow> expr_is_int E e"
  by (simp add: expr_ok_def expr_is_int_def)

lemma expr_ok_wf: "expr_ok E e cty \<Longrightarrow> expr_wf e"
  by (simp add: expr_ok_def)

(* The result of a term of Core type ty: a value of its scalar type or a
   place. The load of a scalar from a place. *)
lemma expr_ok_load_at:
  assumes "expr_ok E p CTy_CharPtr"
  shows "expr_ok E (load_at ty p) (res_cty ty)"
  using assms by (auto simp: load_at_def res_cty_def expr_ok_def split: option.splits)

lemma res_cty_cases: "res_cty ty = CTy_CharPtr \<or> (\<exists>cty. scalar_ty ty = Some cty \<and> res_cty ty = cty)"
  by (auto simp: res_cty_def split: option.splits)


section \<open>Composition\<close>

lemma lowered_ok_nil: "scope_ok prog sc st \<Longrightarrow> lowered_ok prog rt sc st [] st sc"
  by (simp add: lowered_ok_def)

lemma lowered_ok_append:
  assumes "lowered_ok prog rt sc st S1 st1 sc1" and "lowered_ok prog rt sc1 st1 S2 st2 sc2"
  shows "lowered_ok prog rt sc st (S1 @ S2) st2 sc2"
  using assms unfolding lowered_ok_def
  by (auto simp: stmts_ok_append stmts_wf_append intro: env_le_trans used_le_trans)

lemma lowered_ok_scope: "lowered_ok prog rt sc st S st' sc' \<Longrightarrow> scope_ok prog sc' st'"
  by (simp add: lowered_ok_def)

lemma lowered_ok_env_le: "lowered_ok prog rt sc st S st' sc' \<Longrightarrow> env_le (fst sc) (fst sc')"
  by (simp add: lowered_ok_def)

lemma lowered_ok_used_le: "lowered_ok prog rt sc st S st' sc' \<Longrightarrow> used_le st st'"
  by (simp add: lowered_ok_def)

lemma lowered_ok_stmts_ok: "lowered_ok prog rt sc st S st' sc' \<Longrightarrow> stmts_ok (mk_ctx prog rt) sc S = Some sc'"
  by (simp add: lowered_ok_def)

lemma lowered_ok_wf: "lowered_ok prog rt sc st S st' sc' \<Longrightarrow> stmts_wf prog l S"
  by (simp add: lowered_ok_def)

(* A statement without declarations and effects on the scope. *)
lemma lowered_ok_single:
  assumes "scope_ok prog sc st" and "stmt_ok (mk_ctx prog rt) sc s = Some sc" and "\<And>l. stmt_wf prog l s"
  shows "lowered_ok prog rt sc st [s] st sc"
  using assms by (simp add: lowered_ok_def)

(* A fresh name can be declared. *)
lemma fresh_name_decl:
  assumes "scope_ok prog (E, ds) st" and "fresh_name f hint st = Inr (n, st')"
  shows "n \<notin> set ds" and "n \<notin> set (fun_names prog)" and "n |\<notin>| fmdom E"
    and "scope_ok prog (fmupd n vty E, n # ds) st'" and "scope_ok prog (E, ds) st'"
    and "used_le st st'" and "env_le E (fmupd n vty E)"
proof -
  note f = fresh_name_Inr[OF assms(2)]
  have nd: "n |\<notin>| fmdom E" using assms(1) f(1) by (auto simp: scope_ok_def)
  show "n \<notin> set ds" "n \<notin> set (fun_names prog)" "n |\<notin>| fmdom E"
    using assms(1) f(1) nd by (auto simp: scope_ok_def)
  show "env_le E (fmupd n vty E)" by (rule env_le_upd[OF nd])
  show "scope_ok prog (fmupd n vty E, n # ds) st'" "scope_ok prog (E, ds) st'" "used_le st st'"
    using assms(1) f(2) by (auto simp: scope_ok_def used_le_def)
qed

lemma local_name_decl:
  assumes "scope_ok prog (E, ds) st" and "local_name f x st = Inr (n, st')"
  shows "n \<notin> set ds" and "n \<notin> set (fun_names prog)" and "n |\<notin>| fmdom E"
    and "scope_ok prog (fmupd n vty E, n # ds) st'" and "scope_ok prog (E, ds) st'"
    and "used_le st st'" and "env_le E (fmupd n vty E)"
proof -
  note f = local_name_Inr[OF assms(2)]
  have nd: "n |\<notin>| fmdom E" using assms(1) f(1) by (auto simp: scope_ok_def)
  show "n \<notin> set ds" "n \<notin> set (fun_names prog)" "n |\<notin>| fmdom E"
    using assms(1) f(1) nd by (auto simp: scope_ok_def)
  show "env_le E (fmupd n vty E)" by (rule env_le_upd[OF nd])
  show "scope_ok prog (fmupd n vty E, n # ds) st'" "scope_ok prog (E, ds) st'" "used_le st st'"
    using assms(1) f(2) by (auto simp: scope_ok_def used_le_def)
qed

(* Declaring a fresh scalar or buffer. *)
lemma decl_scalar_ok:
  assumes "scope_ok prog (E, ds) st" and "n \<notin> set ds" and "n \<notin> set (fun_names prog)"
    and "scope_ok prog (fmupd n (VT_Scalar cty) E, n # ds) st'" and "used_le st st'" and "n |\<notin>| fmdom E"
  shows "lowered_ok prog rt (E, ds) st [MS_DeclScalar n cty] st' (fmupd n (VT_Scalar cty) E, n # ds)"
  using assms by (simp add: lowered_ok_def sc_declare_def fun_names_def env_le_upd)

lemma decl_buf_ok:
  assumes "scope_ok prog (E, ds) st" and "n \<notin> set ds" and "n \<notin> set (fun_names prog)"
    and "scope_ok prog (fmupd n VT_Buf E, n # ds) st'" and "used_le st st'" and "n |\<notin>| fmdom E"
    and "u64_ok E sz"
  shows "lowered_ok prog rt (E, ds) st [MS_DeclBuf n sz] st' (fmupd n VT_Buf E, n # ds)"
  using assms by (simp add: lowered_ok_def sc_declare_def fun_names_def env_le_upd u64_ok_def expr_is_int_def)

(* Declaring with a fresh name, as one step. *)
lemma fresh_decl_facts:
  assumes "scope_ok prog (E, ds) st" and "fresh_name f hint st = Inr (n, st')"
  shows "n \<notin> set ds \<and> n \<notin> set (fun_names prog) \<and> n |\<notin>| fmdom E
         \<and> scope_ok prog (fmupd n vty E, n # ds) st' \<and> used_le st st'"
  using assms(1) fresh_name_Inr(1,2)[OF assms(2)] by (auto simp: scope_ok_def used_le_def)

lemma local_decl_facts:
  assumes "scope_ok prog (E, ds) st" and "local_name f x st = Inr (n, st')"
  shows "n \<notin> set ds \<and> n \<notin> set (fun_names prog) \<and> n |\<notin>| fmdom E
         \<and> scope_ok prog (fmupd n vty E, n # ds) st' \<and> used_le st st'"
  using assms(1) local_name_Inr(1,2)[OF assms(2)] by (auto simp: scope_ok_def used_le_def)

lemma fresh_scalar_ok:
  assumes "scope_ok prog (E, ds) st" and "fresh_name f hint st = Inr (n, st')"
  shows "lowered_ok prog rt (E, ds) st [MS_DeclScalar n cty] st' (fmupd n (VT_Scalar cty) E, n # ds)"
  using fresh_decl_facts[OF assms, of "VT_Scalar cty"] assms(1) by (intro decl_scalar_ok) simp_all

lemma fresh_buf_ok:
  assumes "scope_ok prog (E, ds) st" and "fresh_name f hint st = Inr (n, st')" and "u64_ok E sz"
  shows "lowered_ok prog rt (E, ds) st [MS_DeclBuf n sz] st' (fmupd n VT_Buf E, n # ds)"
  using fresh_decl_facts[OF assms(1,2), of VT_Buf] assms(1,3) by (intro decl_buf_ok) simp_all

lemma local_scalar_ok:
  assumes "scope_ok prog (E, ds) st" and "local_name f x st = Inr (n, st')"
  shows "lowered_ok prog rt (E, ds) st [MS_DeclScalar n cty] st' (fmupd n (VT_Scalar cty) E, n # ds)"
  using local_decl_facts[OF assms, of "VT_Scalar cty"] assms(1) by (intro decl_scalar_ok) simp_all

lemma local_buf_ok:
  assumes "scope_ok prog (E, ds) st" and "local_name f x st = Inr (n, st')" and "u64_ok E sz"
  shows "lowered_ok prog rt (E, ds) st [MS_DeclBuf n sz] st' (fmupd n VT_Buf E, n # ds)"
  using local_decl_facts[OF assms(1,2), of VT_Buf] assms(1,3) by (intro decl_buf_ok) simp_all

(* The effect-free statements. *)
lemma assign_ok:
  assumes "scope_ok prog (E, ds) st" and "fmlookup E x = Some (VT_Scalar cty)" and "expr_ok E e cty'" and "ty_compat cty' cty"
  shows "lowered_ok prog rt (E, ds) st [MS_Assign x e] st (E, ds)"
  using assms by (intro lowered_ok_single) (auto simp: expr_ok_def expr_compat_def)

lemma store_ok:
  assumes "scope_ok prog (E, ds) st" and "expr_ok E p pty" and "is_ptr_ty pty" and "expr_ok E e cty'" and "ty_compat cty' cty"
  shows "lowered_ok prog rt (E, ds) st [MS_Store cty p e] st (E, ds)"
  using assms by (intro lowered_ok_single) (auto simp: expr_ok_def expr_compat_def expr_is_ptr_def)

lemma copy_ok:
  assumes "scope_ok prog (E, ds) st" and "expr_ok E d dty" and "is_ptr_ty dty" and "expr_ok E s sty" and "is_ptr_ty sty"
    and "u64_ok E n"
  shows "lowered_ok prog rt (E, ds) st [MS_Copy d s n] st (E, ds)"
  using assms by (intro lowered_ok_single) (auto simp: expr_ok_def u64_ok_def expr_is_ptr_def expr_is_int_def)

lemma zero_ok:
  assumes "scope_ok prog (E, ds) st" and "expr_ok E p pty" and "is_ptr_ty pty" and "u64_ok E n"
  shows "lowered_ok prog rt (E, ds) st [MS_Zero p n] st (E, ds)"
  using assms by (intro lowered_ok_single) (auto simp: expr_ok_def u64_ok_def expr_is_ptr_def expr_is_int_def)

lemma uninit_ok:
  assumes "scope_ok prog (E, ds) st" and "expr_ok E p pty" and "is_ptr_ty pty" and "u64_ok E n"
  shows "lowered_ok prog rt (E, ds) st [MS_Uninit p n] st (E, ds)"
  using assms by (intro lowered_ok_single) (auto simp: expr_ok_def u64_ok_def expr_is_ptr_def expr_is_int_def)

(* A store of a term result at a Core type. *)
lemma store_at_ok:
  assumes "scope_ok prog (E, ds) st" and "expr_ok E dst CTy_CharPtr" and "expr_ok E e (res_cty ty)" and "u64_ok E (cg_size cg ty)"
  shows "lowered_ok prog rt (E, ds) st [store_at cg ty dst e] st (E, ds)"
  using assms unfolding store_at_def
  by (cases "scalar_ty ty") (auto intro!: store_ok copy_ok)

(* Nested scopes: a block, a loop, the branches of an if. *)
lemma block_ok:
  assumes "scope_ok prog (E, ds) st" and "lowered_ok prog rt (E, []) st S st' sc'"
  shows "lowered_ok prog rt (E, ds) st [MS_Block S] st' (E, ds)"
  using assms unfolding lowered_ok_def by (auto intro: scope_ok_used_le)

lemma loop_ok:
  assumes "scope_ok prog (E, ds) st" and "lowered_ok prog rt (E, []) st S st' sc'"
  shows "lowered_ok prog rt (E, ds) st [MS_Loop S] st' (E, ds)"
  using assms unfolding lowered_ok_def by (auto intro: scope_ok_used_le)

lemma if_ok:
  assumes "scope_ok prog (E, ds) st" and "expr_ok E c (CTy_Int s b)"
    and "lowered_ok prog rt (E, []) st S1 st1 sc1" and "lowered_ok prog rt (E, []) st1 S2 st2 sc2"
  shows "lowered_ok prog rt (E, ds) st [MS_If c S1 S2] st2 (E, ds)"
  using assms unfolding lowered_ok_def
  by (auto simp: expr_ok_def expr_is_int_def intro: scope_ok_used_le used_le_trans)

(* The loop of a while: the break is inside the loop, so the body is
   checked with the in-loop flag set. *)
lemma while_loop_ok:
  assumes sc: "scope_ok prog (E, ds) st"
    and c: "lowered_ok prog rt (E, []) st Sc st1 (E1, ds1)" and ec: "expr_ok E1 ec CTy_U8"
    and b: "lowered_ok prog rt (E1, ds1) st1 Sb st2 sc2"
  shows "lowered_ok prog rt (E, ds) st [MS_Loop (Sc @ [MS_If (ME_Unop CU_Not ec) [MS_Break] []] @ Sb)] st2 (E, ds)"
proof -
  let ?brk = "MS_If (ME_Unop CU_Not ec) [MS_Break] []"
  have ect: "expr_type E1 (ME_Unop CU_Not ec) = Some CTy_U8" using ec unfolding expr_ok_def by simp
  have ifok: "stmts_ok (mk_ctx prog rt) (E1, ds1) [?brk] = Some (E1, ds1)"
    using ect by (simp add: expr_is_int_def)
  have body: "stmts_ok (mk_ctx prog rt) (E, []) (Sc @ [?brk] @ Sb) = Some sc2"
    by (rule stmts_ok_append_Some[OF lowered_ok_stmts_ok[OF c] stmts_ok_append_Some[OF ifok lowered_ok_stmts_ok[OF b]]])
  have wf: "stmts_wf prog True (Sc @ [?brk] @ Sb)"
    using c b ec by (simp add: lowered_ok_def stmts_wf_append expr_ok_def)
  have used: "used_le st st2" using c b by (auto simp: lowered_ok_def intro: used_le_trans)
  show ?thesis
    unfolding lowered_ok_def using sc body wf used scope_ok_used_le[OF sc used] by simp
qed

lemma return_ok:
  assumes "scope_ok prog sc st" and "rt = Some cty" and "expr_ok (fst sc) e cty'" and "ty_compat cty' cty"
  shows "lowered_ok prog rt sc st [MS_Return (Some e)] st sc"
  using assms by (intro lowered_ok_single) (auto simp: expr_ok_def expr_compat_def)

lemma return_none_ok:
  assumes "scope_ok prog sc st" and "rt = None"
  shows "lowered_ok prog rt sc st [MS_Return None] st sc"
  using assms by (intro lowered_ok_single) auto

(* A call. *)
lemma args_compat_iff:
  "args_compat E es ps \<longleftrightarrow> list_all2 (\<lambda>e p. expr_compat E e (snd p)) es ps"
  by (induction E es ps rule: args_compat.induct) auto

lemma call_ok:
  assumes "scope_ok prog (E, ds) st" and "lookup_fun prog f = Some fn"
    and "list_all2 (\<lambda>e cty. expr_compat E e cty \<and> expr_wf e) args (map snd (MF_Params fn))"
    and "case xopt of None \<Rightarrow> True
          | Some x \<Rightarrow> (\<exists>rty ty. MF_Ret fn = Some rty \<and> fmlookup E x = Some (VT_Scalar ty) \<and> ty_compat rty ty)"
  shows "lowered_ok prog rt (E, ds) st [MS_Call xopt f args] st (E, ds)"
proof (rule lowered_ok_single[OF assms(1)])
  have ac: "args_compat E args (MF_Params fn)"
    unfolding args_compat_iff using assms(3) by (auto simp: list_all2_conv_all_nth)
  show "stmt_ok (mk_ctx prog rt) (E, ds) (MS_Call xopt f args) = Some (E, ds)"
    using assms(2,4) ac by (auto split: option.splits)
  show "\<And>l. stmt_wf prog l (MS_Call xopt f args)"
    using assms(2,3) by (auto simp: list_all_iff list_all2_conv_all_nth in_set_conv_nth)
qed


section \<open>Lists of lowerings\<close>

(* The chained lowering of a list: each element's statements are typed in
   the scope the previous ones left, the state threads, and a property R
   of each result (monotone in the environment) holds in the final
   environment. *)
lemma cg_mapM_chain:
  assumes "cg_mapM f xs st = Inr (ys, st')"
    and "scope_ok prog (E, ds) st"
    and step: "\<And>x st1 y st2 E1 ds1. x \<in> set xs \<Longrightarrow> f x st1 = Inr (y, st2) \<Longrightarrow> scope_ok prog (E1, ds1) st1 \<Longrightarrow> env_le E E1
                 \<Longrightarrow> \<exists>E2 ds2. lowered_ok prog rt (E1, ds1) st1 (stmts y) st2 (E2, ds2) \<and> R E2 y"
    and mono: "\<And>E1 E2 y. env_le E1 E2 \<Longrightarrow> R E1 y \<Longrightarrow> R E2 y"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st (concat (map stmts ys)) st' (E', ds') \<and> (\<forall>y \<in> set ys. R E' y)"
  using assms(1,2) step
proof (induction xs arbitrary: st ys E ds)
  case Nil
  then show ?case by (auto simp: cg_mapM.simps intro!: exI lowered_ok_nil)
next
  case (Cons x xs)
  from Cons.prems(1) obtain y st1 ys' where fx: "f x st = Inr (y, st1)" and rest: "cg_mapM f xs st1 = Inr (ys', st')"
    and ys: "ys = y # ys'"
    by (auto simp: cg_mapM.simps elim!: cg_bind_InrE)
  obtain E1 ds1 where l1: "lowered_ok prog rt (E, ds) st (stmts y) st1 (E1, ds1)" and r1: "R E1 y"
    using Cons.prems(3)[OF _ fx Cons.prems(2)] by auto
  have sc1: "scope_ok prog (E1, ds1) st1" using l1 by (rule lowered_ok_scope)
  have le1: "env_le E E1" using l1 by (simp add: lowered_ok_def)
  have step': "\<And>x st1 y st2 E1a ds1a. x \<in> set xs \<Longrightarrow> f x st1 = Inr (y, st2) \<Longrightarrow> scope_ok prog (E1a, ds1a) st1
                 \<Longrightarrow> env_le E1 E1a \<Longrightarrow> \<exists>E2 ds2. lowered_ok prog rt (E1a, ds1a) st1 (stmts y) st2 (E2, ds2) \<and> R E2 y"
  proof -
    fix x st1 y st2 E1a ds1a
    assume "x \<in> set xs" "f x st1 = Inr (y, st2)" "scope_ok prog (E1a, ds1a) st1" "env_le E1 E1a"
    then show "\<exists>E2 ds2. lowered_ok prog rt (E1a, ds1a) st1 (stmts y) st2 (E2, ds2) \<and> R E2 y"
      using le1 by (intro Cons.prems(3)) (auto intro: env_le_trans)
  qed
  have IH: "\<exists>E' ds'. lowered_ok prog rt (E1, ds1) st1 (concat (map stmts ys')) st' (E', ds') \<and> (\<forall>y \<in> set ys'. R E' y)"
  proof (rule Cons.IH[OF rest sc1])
    fix x st1 y st2 E1a ds1a
    assume "x \<in> set xs" "f x st1 = Inr (y, st2)" "scope_ok prog (E1a, ds1a) st1" "env_le E1 E1a"
    then show "\<exists>E2 ds2. lowered_ok prog rt (E1a, ds1a) st1 (stmts y) st2 (E2, ds2) \<and> R E2 y" by (rule step')
  qed
  then obtain E2 ds2 where l2: "lowered_ok prog rt (E1, ds1) st1 (concat (map stmts ys')) st' (E2, ds2)"
    and r2: "\<forall>y \<in> set ys'. R E2 y" by blast
  have "R E2 y" using r1 l2 mono by (auto simp: lowered_ok_def)
  then show ?case using lowered_ok_append[OF l1 l2] r2 by (auto simp: ys)
qed

(* The lowering of a list whose elements are all typed in one scope (the
   arms of a match), with the state threading through. *)
lemma cg_mapM_same_scope:
  assumes "cg_mapM f xs st = Inr (ys, st')"
    and "scope_ok prog sc st"
    and step: "\<And>x st1 y st2. x \<in> set xs \<Longrightarrow> f x st1 = Inr (y, st2) \<Longrightarrow> scope_ok prog sc st1 \<Longrightarrow> R y \<and> used_le st1 st2"
  shows "(\<forall>y \<in> set ys. R y) \<and> used_le st st'"
  using assms(1,2) step
proof (induction xs arbitrary: st ys)
  case Nil
  then show ?case by (auto simp: cg_mapM.simps)
next
  case (Cons x xs)
  from Cons.prems(1) obtain y st1 ys' where fx: "f x st = Inr (y, st1)" and rest: "cg_mapM f xs st1 = Inr (ys', st')"
    and ys: "ys = y # ys'"
    by (auto simp: cg_mapM.simps elim!: cg_bind_InrE)
  have r1: "R y \<and> used_le st st1" using Cons.prems(3)[OF _ fx Cons.prems(2)] by simp
  have sc1: "scope_ok prog sc st1" using Cons.prems(2) r1 by (blast intro: scope_ok_used_le)
  have IH: "(\<forall>y \<in> set ys'. R y) \<and> used_le st1 st'"
  proof (rule Cons.IH[OF rest sc1])
    fix xa st1 y st2 assume "xa \<in> set xs" "f xa st1 = Inr (y, st2)" "scope_ok prog sc st1"
    then show "R y \<and> used_le st1 st2" by (intro Cons.prems(3)) simp_all
  qed
  show ?case using IH r1 by (auto simp: ys intro: used_le_trans)
qed

(* A pure mapM (no statements; the state only grows). *)
lemma cg_mapM_fresh_used_le:
  assumes "cg_mapM f xs st = Inr (ys, st')"
    and "\<And>x st1 y st2. x \<in> set xs \<Longrightarrow> f x st1 = Inr (y, st2) \<Longrightarrow> used_le st1 st2"
  shows "used_le st st'"
  using assms
proof (induction xs arbitrary: st ys)
  case Nil
  then show ?case by (simp add: cg_mapM.simps)
next
  case (Cons x xs)
  from Cons.prems(1) obtain y st1 ys' where fx: "f x st = Inr (y, st1)" and rest: "cg_mapM f xs st1 = Inr (ys', st')"
    by (auto simp: cg_mapM.simps elim!: cg_bind_InrE)
  have "used_le st st1" using Cons.prems(2)[OF _ fx] by simp
  moreover have "used_le st1 st'"
  proof (rule Cons.IH[OF rest])
    fix xa st1 y st2 assume "xa \<in> set xs" "f xa st1 = Inr (y, st2)"
    then show "used_le st1 st2" by (intro Cons.prems(2)) simp_all
  qed
  ultimately show ?case by (rule used_le_trans)
qed


section \<open>Variables, lazy references, casts\<close>

lemma rep_addr_ok:
  assumes "rep_ok E env ty rep" and "rep_addr rep = Some a"
  shows "expr_ok E a CTy_CharPtr"
  using assms by (cases rep) (auto simp: expr_ok_def)

(* A lazy address: typed as a place; it may declare a descriptor temporary
   (a cast from fixed to descriptor dimensions). *)
lemma build_desc_ok:
  assumes "build_desc cg dimsF toTy p st = Inr ((S, a), st')"
    and "scope_ok prog (E, ds) st" and "expr_ok E p CTy_CharPtr"
    and "u64_ok E (cg_size cg toTy)" and "array_dims_well_kinded dimsF"
    and "\<not> dims_all_fixed (case toTy of CoreTy_Array _ d \<Rightarrow> d | _ \<Rightarrow> [])"
    and "8 * length dimsF < u64_max"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' a CTy_CharPtr"
proof -
  from assms(1) obtain tmp st1 where fr: "fresh_name (CG_Fun cg) ''desc'' st = Inr (tmp, st1)"
    and S: "S = [MS_DeclBuf tmp (buf_size (cg_size cg toTy)), MS_Store CTy_CharPtr (ME_AddrOf tmp) p]
                @ map (\<lambda>k. MS_Store CTy_U64 (ptr_add (ME_AddrOf tmp) (dim_off k)) (u64_lit (dim_size (dimsF ! k)))) [0..<length dimsF]"
    and a: "a = ME_AddrOf tmp" and st': "st' = st1"
    unfolding build_desc_def by (auto elim!: cg_bind_InrE)
  let ?E1 = "fmupd tmp VT_Buf E"
  have d: "lowered_ok prog rt (E, ds) st [MS_DeclBuf tmp (buf_size (cg_size cg toTy))] st1 (?E1, tmp # ds)"
    using assms(2,4) fr by (intro fresh_buf_ok buf_size_ok)
  have sc1: "scope_ok prog (?E1, tmp # ds) st1" using d by (rule lowered_ok_scope)
  have le1: "env_le E ?E1" using d by (simp add: lowered_ok_def)
  have tmp: "expr_ok ?E1 (ME_AddrOf tmp) CTy_CharPtr" by (simp add: expr_ok_def)
  have s1: "lowered_ok prog rt (?E1, tmp # ds) st1 [MS_Store CTy_CharPtr (ME_AddrOf tmp) p] st1 (?E1, tmp # ds)"
    using sc1 tmp expr_ok_mono[OF le1 assms(3)] by (intro store_ok[where cty' = CTy_CharPtr]) auto
  have dims: "\<And>k. k < length dimsF \<Longrightarrow>
      lowered_ok prog rt (?E1, tmp # ds) st1
        [MS_Store CTy_U64 (ptr_add (ME_AddrOf tmp) (dim_off k)) (u64_lit (dim_size (dimsF ! k)))] st1 (?E1, tmp # ds)"
  proof -
    fix k assume k: "k < length dimsF"
    have "8 * k < u64_max" using k assms(7) by simp
    then have off: "expr_ok ?E1 (ptr_add (ME_AddrOf tmp) (dim_off k)) CTy_CharPtr"
      by (intro expr_ok_ptr_add[OF tmp]) (simp_all add: u64_ok_def)
    have "dim_size (dimsF ! k) < u64_max" using k assms(5) by (intro dim_size_lt_u64_max) auto
    then show "?thesis k" using sc1 off by (intro store_ok[where cty' = CTy_U64]) auto
  qed
  have dimsL: "lowered_ok prog rt (?E1, tmp # ds) st1
      (map (\<lambda>k. MS_Store CTy_U64 (ptr_add (ME_AddrOf tmp) (dim_off k)) (u64_lit (dim_size (dimsF ! k)))) [0..<length dimsF])
      st1 (?E1, tmp # ds)"
  proof -
    have "\<And>n. n \<le> length dimsF \<Longrightarrow> lowered_ok prog rt (?E1, tmp # ds) st1
      (map (\<lambda>k. MS_Store CTy_U64 (ptr_add (ME_AddrOf tmp) (dim_off k)) (u64_lit (dim_size (dimsF ! k)))) [0..<n])
      st1 (?E1, tmp # ds)"
    proof -
      fix n show "n \<le> length dimsF \<Longrightarrow> ?thesis n"
      proof (induction n)
        case 0
        then show ?case using sc1 by (simp add: lowered_ok_nil)
      next
        case (Suc n)
        then show ?case using dims[of n] by (auto intro: lowered_ok_append)
      qed
    qed
    then show ?thesis by simp
  qed
  show ?thesis
    unfolding S a st'
    using lowered_ok_append[OF lowered_ok_append[OF d s1] dimsL] tmp by (intro exI conjI) simp_all
qed

end
