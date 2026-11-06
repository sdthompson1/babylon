theory CodeGenTypingBase
  imports CodeGen "../minic/MiniCTyping"
begin

(* ========================================================================== *)
(* The typing theorem: MiniC typing facts, size expressions, the invariant    *)
(* (minic/DESIGN.md, section 8)                                               *)
(* ========================================================================== *)

(* This theory collects what the typing proof of the generator
   (CodeGenTypingTerm.thy, CodeGenTyping.thy) needs about the MiniC typing
   judgement, about the size and offset expressions of stage 4, and the
   invariant that relates the generator's environment to the MiniC typing
   environment ("the static half of the per-frame relation", section 8). *)


section \<open>The MiniC typing judgement\<close>

(* An environment extends another: every binding is kept. The generated
   code only ever declares fresh names, so its scopes grow this way. *)
definition env_le :: "MTyEnv \<Rightarrow> MTyEnv \<Rightarrow> bool" where
  "env_le E E' = (\<forall>x v. fmlookup E x = Some v \<longrightarrow> fmlookup E' x = Some v)"

lemma env_le_refl [simp]: "env_le E E"
  by (simp add: env_le_def)

lemma env_le_trans: "env_le E1 E2 \<Longrightarrow> env_le E2 E3 \<Longrightarrow> env_le E1 E3"
  by (simp add: env_le_def)

lemma env_le_upd: "x |\<notin>| fmdom E \<Longrightarrow> env_le E (fmupd x v E)"
  by (auto simp: env_le_def fmlookup_dom_iff)

lemma env_le_lookup: "env_le E E' \<Longrightarrow> fmlookup E x = Some v \<Longrightarrow> fmlookup E' x = Some v"
  by (simp add: env_le_def)

lemma expr_type_mono:
  assumes "env_le E E'" and "expr_type E e = Some t"
  shows "expr_type E' e = Some t"
  using assms(2)
proof (induction e arbitrary: t)
  case (ME_Var x)
  then show ?case using assms(1) by (auto simp: env_le_def split: option.splits MVarTy.splits)
next
  case (ME_AddrOf x)
  then show ?case using assms(1) by (auto simp: env_le_def split: option.splits)
next
  case (ME_Load ty e)
  then show ?case by (auto split: option.splits if_splits)
next
  case (ME_Unop op e)
  then show ?case by (auto split: option.splits CTy.splits CUnop.splits)
next
  case (ME_Binop op e1 e2)
  then show ?case by (auto split: option.splits CTy.splits if_splits)
next
  case (ME_Cast ty e)
  then show ?case by (auto split: option.splits if_splits)
next
  case (ME_PtrAdd e1 e2)
  then show ?case by (auto split: option.splits if_splits)
qed auto

lemma expr_is_int_mono: "env_le E E' \<Longrightarrow> expr_is_int E e \<Longrightarrow> expr_is_int E' e"
  by (auto simp: expr_is_int_def expr_type_mono split: option.splits)

lemma expr_is_ptr_mono: "env_le E E' \<Longrightarrow> expr_is_ptr E e \<Longrightarrow> expr_is_ptr E' e"
  by (auto simp: expr_is_ptr_def expr_type_mono split: option.splits)

lemma expr_compat_mono: "env_le E E' \<Longrightarrow> expr_compat E e ty \<Longrightarrow> expr_compat E' e ty"
  by (auto simp: expr_compat_def expr_type_mono split: option.splits)

lemma stmts_ok_append:
  "stmts_ok ctx sc (S1 @ S2) =
    (case stmts_ok ctx sc S1 of None \<Rightarrow> None | Some sc' \<Rightarrow> stmts_ok ctx sc' S2)"
  by (induction S1 arbitrary: sc) (auto split: option.splits)

lemma stmts_ok_append_Some:
  "stmts_ok ctx sc S1 = Some sc1 \<Longrightarrow> stmts_ok ctx sc1 S2 = Some sc2 \<Longrightarrow> stmts_ok ctx sc (S1 @ S2) = Some sc2"
  by (simp add: stmts_ok_append)

lemma stmts_wf_append: "stmts_wf prog l (S1 @ S2) = (stmts_wf prog l S1 \<and> stmts_wf prog l S2)"
  by (induction S1) auto

lemma stmts_wf_map: "stmts_wf prog l (map f xs) = (\<forall>x \<in> set xs. stmt_wf prog l (f x))"
  by (induction xs) auto

lemma stmts_wf_concat: "stmts_wf prog l (concat xss) = (\<forall>S \<in> set xss. stmts_wf prog l S)"
  by (induction xss) (auto simp: stmts_wf_append)

lemma sc_declare_fresh:
  assumes "x \<notin> set (snd sc)" and "x \<notin> set (fun_names (TC_Prog ctx))"
  shows "sc_declare ctx sc x vty = Some (fmupd x vty (fst sc), x # snd sc)"
  using assms by (simp add: sc_declare_def)

(* The scalar C type of a Core type's representation as a MiniC value:
   its scalar type, or char * for a place. *)
definition res_cty :: "CoreType \<Rightarrow> CTy" where
  "res_cty ty = (case scalar_ty ty of Some cty \<Rightarrow> cty | None \<Rightarrow> CTy_CharPtr)"

lemma res_cty_scalar [simp]: "scalar_ty ty = Some cty \<Longrightarrow> res_cty ty = cty"
  by (simp add: res_cty_def)

lemma res_cty_aggregate [simp]: "scalar_ty ty = None \<Longrightarrow> res_cty ty = CTy_CharPtr"
  by (simp add: res_cty_def)

lemma is_ptr_ty_CharPtr [simp]: "is_ptr_ty CTy_CharPtr"
  by simp

lemma ty_compat_refl [simp]: "ty_compat t t"
  by (simp add: ty_compat_def)

lemma ty_compat_ptr: "is_ptr_ty t1 \<Longrightarrow> is_ptr_ty t2 \<Longrightarrow> ty_compat t1 t2"
  by (simp add: ty_compat_def)

lemma expr_compat_of_type: "expr_type E e = Some t \<Longrightarrow> expr_compat E e t"
  by (simp add: expr_compat_def)

lemma expr_compat_ptr: "expr_type E e = Some t \<Longrightarrow> is_ptr_ty t \<Longrightarrow> is_ptr_ty t' \<Longrightarrow> expr_compat E e t'"
  by (simp add: expr_compat_def ty_compat_def)

lemma expr_is_int_U64: "expr_type E e = Some CTy_U64 \<Longrightarrow> expr_is_int E e"
  by (simp add: expr_is_int_def)

lemma expr_is_ptr_of: "expr_type E e = Some t \<Longrightarrow> is_ptr_ty t \<Longrightarrow> expr_is_ptr E e"
  by (simp add: expr_is_ptr_def)


section \<open>Literals and uint64_t arithmetic\<close>

(* Simp unfolds int_fits to a numeral comparison; these rules keep u64_max
   opaque for uint64_t literals. *)
lemma int_fits_u64_nat [simp]: "int_fits Unsigned IntBits_64 (int n) \<longleftrightarrow> n < u64_max"
  unfolding int_fits_u64 by simp

lemma int_fits_u64_8 [simp]: "int_fits Unsigned IntBits_64 (8 * int k) \<longleftrightarrow> 8 * k < u64_max"
  using int_fits_u64_nat[of "8 * k"] by simp

lemma one_lt_u64_max [simp]: "1 < u64_max" and zero_lt_u64_max [simp]: "0 < u64_max"
  and Suc_0_lt_u64_max [simp]: "Suc 0 < u64_max"
  by (simp_all add: u64_max_def)

lemma int_fits_u64_numeral [simp]:
  "int_fits Unsigned IntBits_64 0" "int_fits Unsigned IntBits_64 1"
  unfolding int_fits_u64 by (simp_all add: u64_max_def)

declare int_fits.simps [simp del]

lemma inj_size_param: "size_param v = size_param w \<Longrightarrow> v = w"
  by (simp add: size_param_def)

lemma map_of_size_params:
  "v \<in> set vs \<Longrightarrow> map_of (map (\<lambda>v. (size_param v, c)) vs) (size_param v) = Some c"
  by (induction vs) (auto dest: inj_size_param)

lemma expr_wf_u64_lit [simp]: "expr_wf (u64_lit n) \<longleftrightarrow> n < u64_max"
  by simp

lemma expr_type_u64_lit [simp]: "n < u64_max \<Longrightarrow> expr_type E (u64_lit n) = Some CTy_U64"
  by simp

lemma expr_type_u8_bit [simp]:
  "expr_type E (ME_Int Unsigned IntBits_8 (if b then 1 else 0)) = Some CTy_U8"
  "expr_wf (ME_Int Unsigned IntBits_8 (if b then 1 else 0))"
  by (simp_all add: int_fits_unsigned)

lemma expr_type_zero_lit [simp]:
  "expr_type E (ME_Int s b 0) = Some (CTy_Int s b)" "expr_wf (ME_Int s b 0)"
  by (cases s; cases b; simp add: int_fits_signed int_fits_unsigned)+

lemma expr_type_i32_zero [simp]:
  "expr_type E (ME_Int Signed IntBits_32 0) = Some CTy_I32"
  by (simp add: int_fits_signed)

(* The value of a size expression when the pointer size and every variable
   are zero; the folded literals of a size expression are values of this
   kind, which is how their range is bounded. *)
fun eval0 :: "MExpr \<Rightarrow> nat" where
  "eval0 (ME_Int _ _ i) = nat i"
| "eval0 ME_PtrSize = 0"
| "eval0 (ME_Var _) = 0"
| "eval0 (ME_Binop CB_Add a b) = eval0 a + eval0 b"
| "eval0 (ME_Binop CB_Mul a b) = eval0 a * eval0 b"
| "eval0 (ME_Binop CB_Max a b) = max (eval0 a) (eval0 b)"
| "eval0 _ = 0"

lemma eval0_u64_lit [simp]: "eval0 (u64_lit n) = n"
  by simp

lemma eval0_e_add [simp]: "eval0 (e_add a b) = eval0 a + eval0 b"
  by (auto simp: e_fold2_def split: option.splits dest!: u64_lit_of_Some)

lemma eval0_e_mul [simp]: "eval0 (e_mul a b) = eval0 a * eval0 b"
  by (auto simp: e_fold2_def nat_mult_distrib split: option.splits dest!: u64_lit_of_Some)

lemma eval0_e_max [simp]: "eval0 (e_max a b) = max (eval0 a) (eval0 b)"
  by (auto simp: e_fold2_def max_def split: option.splits dest!: u64_lit_of_Some)

(* Well-formed and typed uint64_t expressions. *)
definition u64_ok :: "MTyEnv \<Rightarrow> MExpr \<Rightarrow> bool" where
  "u64_ok E e = (expr_wf e \<and> expr_type E e = Some CTy_U64)"

lemma u64_ok_lit [simp]: "u64_ok E (u64_lit n) \<longleftrightarrow> n < u64_max"
  by (simp add: u64_ok_def)

lemma u64_ok_PtrSize [simp]: "u64_ok E ME_PtrSize"
  by (simp add: u64_ok_def)

lemma u64_ok_zero [simp]: "u64_ok E (ME_Int Unsigned IntBits_64 0)"
  by (simp add: u64_ok_def)

lemma u64_ok_one [simp]: "u64_ok E (ME_Int Unsigned IntBits_64 1)"
  by (simp add: u64_ok_def)

lemma byte_width_lt_u64_max [simp]: "byte_width b < u64_max"
  by (cases b) (simp_all add: u64_max_def)

lemma tag_size_lt_u64_max [simp]: "tag_size env d < u64_max"
  by (simp add: tag_size_def)

lemma u64_ok_byte_width [simp]: "u64_ok E (u64_lit (byte_width b))"
  by simp

lemma u64_ok_binop:
  assumes "u64_ok E a" and "u64_ok E b" and "op = CB_Add \<or> op = CB_Mul \<or> op = CB_Max"
  shows "u64_ok E (ME_Binop op a b)"
  using assms by (auto simp: u64_ok_def)

lemma u64_ok_e_fold2:
  assumes "u64_ok E a" and "u64_ok E b" and "f (eval0 a) (eval0 b) < u64_max"
    and "op = CB_Add \<or> op = CB_Mul \<or> op = CB_Max"
  shows "u64_ok E (e_fold2 f op a b)"
  using assms by (auto simp: e_fold2_def u64_ok_def split: option.splits dest!: u64_lit_of_Some)

lemma eval0_foldr_add: "eval0 (foldr e_add es (ME_Int Unsigned IntBits_64 0)) = sum_list (map eval0 es)"
  by (induction es) simp_all

lemma eval0_foldr_max: "eval0 (foldr e_max es (ME_Int Unsigned IntBits_64 0)) = max_list (map eval0 es)"
  by (induction es) simp_all

lemma u64_ok_foldr_add:
  assumes "\<forall>e \<in> set es. u64_ok E e" and "sum_list (map eval0 es) < u64_max"
  shows "u64_ok E (foldr e_add es (ME_Int Unsigned IntBits_64 0))"
  using assms
proof (induction es)
  case Nil
  show ?case by simp
next
  case (Cons e es)
  have "u64_ok E (foldr e_add es (ME_Int Unsigned IntBits_64 0))" using Cons.prems by (intro Cons.IH) auto
  then show ?case
    using Cons.prems unfolding foldr.simps o_apply by (intro u64_ok_e_fold2) (auto simp: eval0_foldr_add)
qed

lemma u64_ok_foldr_max:
  assumes "\<forall>e \<in> set es. u64_ok E e" and "max_list (map eval0 es) < u64_max"
  shows "u64_ok E (foldr e_max es (ME_Int Unsigned IntBits_64 0))"
  using assms
proof (induction es)
  case Nil
  show ?case by simp
next
  case (Cons e es)
  have "u64_ok E (foldr e_max es (ME_Int Unsigned IntBits_64 0))" using Cons.prems by (intro Cons.IH) auto
  then show ?case
    using Cons.prems unfolding foldr.simps o_apply by (intro u64_ok_e_fold2) (auto simp: eval0_foldr_max)
qed


section \<open>Size expressions\<close>

(* The size expression of a type evaluates, in the sense of eval0, to the
   size of the type at pointer size 0 and the assignment that the
   type-variable expressions evaluate to. *)
lemma eval0_tyvar_exprs:
  "eval0 (tyvar_exprs tyvars es v) = tyvar_sizes tyvars (map eval0 es) v"
  by (auto simp: tyvar_exprs_def tyvar_sizes_def zip_map2 map_of_map split: option.splits)

lemma eval0_tsz_expr:
  "(\<forall>v. eval0 (tv v) = sz v) \<Longrightarrow> eval0 (tsz_expr fuel env tv ty) = tsz fuel env 0 sz ty"
proof (induction fuel arbitrary: ty sz tv)
  case 0
  then show ?case
  proof (induction ty)
    case (CoreTy_Record flds)
    have fld: "\<And>fld. fld \<in> set flds \<Longrightarrow> eval0 (tsz_expr 0 env tv (snd fld)) = tsz 0 env 0 sz (snd fld)"
      using CoreTy_Record.IH[OF _ snds.intros] CoreTy_Record.prems by blast
    then show ?case by (simp add: eval0_foldr_add comp_def cong: map_cong)
  qed (simp_all add: tsz_expr.simps(1) tsz.simps(1) desc_size_def nat_mult_distrib)
next
  case (Suc fuel)
  note IH_fuel = Suc.IH
  from Suc.prems show ?case
  proof (induction ty)
    case (CoreTy_Datatype dtName args)
    let ?argExprs = "map (tsz_expr (Suc fuel) env tv) args"
    let ?argSizes = "map (tsz (Suc fuel) env 0 sz) args"
    have args: "map (eval0 \<circ> tsz_expr (Suc fuel) env tv) args = ?argSizes"
      by (rule map_cong[OF refl]) (simp add: CoreTy_Datatype.IH[OF _ CoreTy_Datatype.prems])
    have ctors: "\<And>ctor. eval0 (ctor_tsz_expr fuel env ?argExprs ctor) = ctor_tsz fuel env 0 ?argSizes ctor"
    proof -
      fix ctor
      show "eval0 (ctor_tsz_expr fuel env ?argExprs ctor) = ctor_tsz fuel env 0 ?argSizes ctor"
      proof (cases "fmlookup (TE_DataCtors env) ctor")
        case None
        then show ?thesis by (simp add: ctor_tsz_expr_def ctor_tsz_def)
      next
        case (Some x)
        then obtain dt tyvars payloadTy where lk: "fmlookup (TE_DataCtors env) ctor = Some (dt, tyvars, payloadTy)"
          by (cases x) auto
        have tv': "\<forall>v. eval0 (tyvar_exprs tyvars ?argExprs v) = tyvar_sizes tyvars ?argSizes v"
          using eval0_tyvar_exprs[of tyvars ?argExprs] args by simp
        show ?thesis using lk IH_fuel[OF tv'] by (simp add: ctor_tsz_expr_def ctor_tsz_def)
      qed
    qed
    show ?case
      unfolding tsz_expr_Suc_Datatype tsz_Suc_Datatype
      by (simp add: eval0_foldr_max ctors comp_def)
  next
    case (CoreTy_Record flds)
    have fld: "\<And>fld. fld \<in> set flds \<Longrightarrow> eval0 (tsz_expr (Suc fuel) env tv (snd fld)) = tsz (Suc fuel) env 0 sz (snd fld)"
      using CoreTy_Record.IH[OF _ snds.intros] CoreTy_Record.prems by blast
    then show ?case by (simp add: eval0_foldr_add comp_def cong: map_cong)
  qed (simp_all add: desc_size_def nat_mult_distrib)
qed

(* The type-variable expressions of a type: well-formed and uint64_t, and
   evaluating (eval0) to the assignment. *)
definition tv_ok :: "MTyEnv \<Rightarrow> (string \<Rightarrow> MExpr) \<Rightarrow> (string \<Rightarrow> nat) \<Rightarrow> CoreType \<Rightarrow> bool" where
  "tv_ok E tv sz ty = ((\<forall>v \<in> type_tyvars ty. u64_ok E (tv v)) \<and> (\<forall>v. eval0 (tv v) = sz v))"

lemma tv_ok_subset: "tv_ok E tv sz ty \<Longrightarrow> type_tyvars ty' \<subseteq> type_tyvars ty \<Longrightarrow> tv_ok E tv sz ty'"
  by (auto simp: tv_ok_def)

lemma tv_ok_Record_fld: "tv_ok E tv sz (CoreTy_Record flds) \<Longrightarrow> fld \<in> set flds \<Longrightarrow> tv_ok E tv sz (snd fld)"
  by (rule tv_ok_subset) auto

lemma tv_ok_Datatype_arg: "tv_ok E tv sz (CoreTy_Datatype d args) \<Longrightarrow> arg \<in> set args \<Longrightarrow> tv_ok E tv sz arg"
  by (rule tv_ok_subset) auto

lemma tv_ok_Array_elem: "tv_ok E tv sz (CoreTy_Array elemTy dims) \<Longrightarrow> tv_ok E tv sz elemTy"
  by (rule tv_ok_subset) auto

lemma tv_ok_eval0: "tv_ok E tv sz ty \<Longrightarrow> \<forall>v. eval0 (tv v) = sz v"
  by (simp add: tv_ok_def)

(* The well-formedness and the type of a size expression follow from the
   static size check at pointer size 0 and the zero assignment (every
   folded literal is the eval0 value of a sub-expression, which the check
   bounds). *)
lemma tsz_expr_ok:
  "tsz_fits fuel env 0 sz ty \<Longrightarrow> tv_ok E tv sz ty \<Longrightarrow> u64_ok E (tsz_expr fuel env tv ty)"
proof (induction fuel arbitrary: ty sz tv)
  case 0
  then show ?case
  proof (induction ty)
    case (CoreTy_Record flds)
    have fld: "\<And>fld. fld \<in> set flds \<Longrightarrow> u64_ok E (tsz_expr 0 env tv (snd fld))"
      using CoreTy_Record.IH[OF _ snds.intros tsz_fits_Record_fld[OF CoreTy_Record.prems(1)] tv_ok_Record_fld[OF CoreTy_Record.prems(2)]]
      by blast
    have "tsz 0 env 0 sz (CoreTy_Record flds) < u64_max" by (rule tsz_fits_lt[OF CoreTy_Record.prems(1)])
    then show ?case
      using fld unfolding tsz_expr.simps(6) of_nat_0
      by (intro u64_ok_foldr_add) (auto simp: eval0_tsz_expr[OF tv_ok_eval0[OF CoreTy_Record.prems(2)]] comp_def)
  next
    case (CoreTy_Array elemTy dims)
    show ?case
    proof (cases "dims_all_fixed dims")
      case True
      have ih: "u64_ok E (tsz_expr 0 env tv elemTy)"
        by (rule CoreTy_Array.IH[OF tsz_fits_Array_elem[OF CoreTy_Array.prems(1) True] tv_ok_Array_elem[OF CoreTy_Array.prems(2)]])
      from CoreTy_Array.prems(1) True have cnt: "dims_count dims < u64_max"
        and fits: "tsz 0 env 0 sz elemTy * dims_count dims < u64_max" by simp_all
      show ?thesis using True ih cnt fits
        by (simp only: tsz_expr.simps(7) if_True)
           (intro u64_ok_e_fold2, auto simp: eval0_tsz_expr[OF tv_ok_eval0[OF CoreTy_Array.prems(2)]])
    next
      case False
      then show ?thesis using CoreTy_Array.prems(1)
        by (simp add: tsz_expr.simps(7) desc_size_def e_fold2_def u64_ok_def)
    qed
  next
    case (CoreTy_Var v)
    then show ?case by (simp add: tv_ok_def)
  qed (simp_all add: tsz_expr.simps(1))
next
  case (Suc fuel)
  note IH_fuel = Suc.IH
  from Suc.prems show ?case
  proof (induction ty)
    case (CoreTy_Datatype dtName args)
    let ?argExprs = "map (tsz_expr (Suc fuel) env tv) args"
    let ?argSizes = "map (tsz (Suc fuel) env 0 sz) args"
    have e0: "\<forall>v. eval0 (tv v) = sz v" using CoreTy_Datatype.prems(2) by (simp add: tv_ok_def)
    have args: "\<And>arg. arg \<in> set args \<Longrightarrow> u64_ok E (tsz_expr (Suc fuel) env tv arg)"
      using CoreTy_Datatype.IH tsz_fits_Datatype_arg[OF CoreTy_Datatype.prems(1)]
            tv_ok_Datatype_arg[OF CoreTy_Datatype.prems(2)] by blast
    have argSizes: "map (eval0 \<circ> tsz_expr (Suc fuel) env tv) args = ?argSizes"
      by (rule map_cong[OF refl]) (simp add: eval0_tsz_expr[OF e0])
    have tv': "\<And>tyvars. \<forall>v. eval0 (tyvar_exprs tyvars ?argExprs v) = tyvar_sizes tyvars ?argSizes v"
      using eval0_tyvar_exprs[of _ ?argExprs] argSizes by simp
    have ctors: "\<And>ctor. ctor \<in> set (dt_ctors env dtName) \<Longrightarrow> u64_ok E (ctor_tsz_expr fuel env ?argExprs ctor)"
    proof -
      fix ctor assume c: "ctor \<in> set (dt_ctors env dtName)"
      show "u64_ok E (ctor_tsz_expr fuel env ?argExprs ctor)"
      proof (cases "fmlookup (TE_DataCtors env) ctor")
        case None
        then show ?thesis by (simp add: ctor_tsz_expr_def)
      next
        case (Some x)
        then obtain dt tyvars payloadTy where lk: "fmlookup (TE_DataCtors env) ctor = Some (dt, tyvars, payloadTy)"
          by (cases x) auto
        have ok: "tv_ok E (tyvar_exprs tyvars ?argExprs) (tyvar_sizes tyvars ?argSizes) payloadTy"
          unfolding tv_ok_def
        proof (intro conjI allI ballI)
          fix v
          show "eval0 (tyvar_exprs tyvars ?argExprs v) = tyvar_sizes tyvars ?argSizes v" using tv' by simp
        next
          fix v assume "v \<in> type_tyvars payloadTy"
          show "u64_ok E (tyvar_exprs tyvars ?argExprs v)"
            using args unfolding tyvar_exprs_def
            by (auto split: option.splits dest!: map_of_SomeD set_zip_rightD)
        qed
        show ?thesis
          using lk IH_fuel[OF tsz_fits_Datatype_payload[OF CoreTy_Datatype.prems(1) c lk] ok]
          by (simp add: ctor_tsz_expr_def)
      qed
    qed
    have fits: "tag_size env dtName + max_list (map (ctor_tsz fuel env 0 ?argSizes) (dt_ctors env dtName)) < u64_max"
      using tsz_fits_lt[OF CoreTy_Datatype.prems(1)] unfolding tsz_Suc_Datatype .
    have ev: "\<And>ctor. eval0 (ctor_tsz_expr fuel env ?argExprs ctor) = ctor_tsz fuel env 0 ?argSizes ctor"
    proof -
      fix ctor
      show "eval0 (ctor_tsz_expr fuel env ?argExprs ctor) = ctor_tsz fuel env 0 ?argSizes ctor"
      proof (cases "fmlookup (TE_DataCtors env) ctor")
        case None
        then show ?thesis by (simp add: ctor_tsz_expr_def ctor_tsz_def)
      next
        case (Some x)
        then obtain dt tyvars payloadTy where lk: "fmlookup (TE_DataCtors env) ctor = Some (dt, tyvars, payloadTy)"
          by (cases x) auto
        then show ?thesis using eval0_tsz_expr[OF tv'[of tyvars]]
          by (simp add: ctor_tsz_expr_def ctor_tsz_def)
      qed
    qed
    have maxes: "u64_ok E (foldr e_max (map (ctor_tsz_expr fuel env ?argExprs) (dt_ctors env dtName)) (ME_Int Unsigned IntBits_64 0))"
      using ctors fits by (intro u64_ok_foldr_max) (auto simp: ev comp_def)
    show ?case
      unfolding tsz_expr_Suc_Datatype of_nat_0
      using maxes fits
      by (intro u64_ok_e_fold2) (auto simp: eval0_foldr_max ev comp_def)
  next
    case (CoreTy_Record flds)
    have fld: "\<And>fld. fld \<in> set flds \<Longrightarrow> u64_ok E (tsz_expr (Suc fuel) env tv (snd fld))"
      using CoreTy_Record.IH[OF _ snds.intros tsz_fits_Record_fld[OF CoreTy_Record.prems(1)] tv_ok_Record_fld[OF CoreTy_Record.prems(2)]]
      by blast
    have "tsz (Suc fuel) env 0 sz (CoreTy_Record flds) < u64_max" by (rule tsz_fits_lt[OF CoreTy_Record.prems(1)])
    then show ?case
      using fld unfolding tsz_expr.simps(6) of_nat_0
      by (intro u64_ok_foldr_add) (auto simp: eval0_tsz_expr[OF tv_ok_eval0[OF CoreTy_Record.prems(2)]] comp_def)
  next
    case (CoreTy_Array elemTy dims)
    show ?case
    proof (cases "dims_all_fixed dims")
      case True
      have ih: "u64_ok E (tsz_expr (Suc fuel) env tv elemTy)"
        by (rule CoreTy_Array.IH[OF tsz_fits_Array_elem[OF CoreTy_Array.prems(1) True] tv_ok_Array_elem[OF CoreTy_Array.prems(2)]])
      from CoreTy_Array.prems(1) True have cnt: "dims_count dims < u64_max"
        and fits: "tsz (Suc fuel) env 0 sz elemTy * dims_count dims < u64_max" by simp_all
      show ?thesis using True ih cnt fits
        by (simp only: tsz_expr.simps(7) if_True)
           (intro u64_ok_e_fold2, auto simp: eval0_tsz_expr[OF tv_ok_eval0[OF CoreTy_Array.prems(2)]])
    next
      case False
      then show ?thesis using CoreTy_Array.prems(1)
        by (simp add: tsz_expr.simps(7) desc_size_def e_fold2_def u64_ok_def)
    qed
  next
    case (CoreTy_Var v)
    then show ?case by (simp add: tv_ok_def)
  qed simp_all
qed

(* The size parameters of a set of type variables are in scope. *)
definition sizes_in :: "MTyEnv \<Rightarrow> string set \<Rightarrow> bool" where
  "sizes_in E TV = (\<forall>v \<in> TV. fmlookup E (size_param v) = Some (VT_Scalar CTy_U64))"

lemma sizes_in_mono: "env_le E E' \<Longrightarrow> sizes_in E TV \<Longrightarrow> sizes_in E' TV"
  by (auto simp: sizes_in_def env_le_def)

lemma sizes_in_subset: "sizes_in E TV \<Longrightarrow> TV' \<subseteq> TV \<Longrightarrow> sizes_in E TV'"
  by (auto simp: sizes_in_def)

lemma size_of_ok:
  assumes "sizes_in E (type_tyvars ty)" and "size_fits env 0 (\<lambda>_. 0) ty"
  shows "u64_ok E (size_of env ty)"
  using assms unfolding size_of_def size_expr_def size_fits_def
  by (intro tsz_expr_ok) (auto simp: tv_ok_def size_tv_def sizes_in_def u64_ok_def)

lemma size_of_type:
  "sizes_in E (type_tyvars ty) \<Longrightarrow> size_fits env 0 (\<lambda>_. 0) ty \<Longrightarrow> expr_type E (size_of env ty) = Some CTy_U64"
  using size_of_ok by (simp add: u64_ok_def)

(* Well-formedness alone needs no environment: a type with free type
   variables is well-formed under an environment that has their sizes. *)
lemma size_expr_wf:
  assumes "size_fits env 0 (\<lambda>_. 0) ty"
  shows "expr_wf (size_of env ty)"
proof -
  let ?E = "fmap_of_list (map (\<lambda>v. (size_param v, VT_Scalar CTy_U64)) (type_tyvars_list ty))"
  have "sizes_in ?E (type_tyvars ty)"
    by (auto simp: sizes_in_def set_type_tyvars_list[symmetric] fmlookup_of_list map_of_size_params)
  then show ?thesis using size_of_ok[OF _ assms] by (simp add: u64_ok_def)
qed

lemma eval0_size_of: "eval0 (size_of env ty) = type_size env 0 (\<lambda>_. 0) ty"
  unfolding size_of_def size_expr_def type_size_def
  by (rule eval0_tsz_expr) (simp add: size_tv_def)

(* Field offsets. *)
lemma field_off_ok:
  assumes "sizes_in E (type_tyvars (CoreTy_Record flds))" and "size_fits env 0 (\<lambda>_. 0) (CoreTy_Record flds)"
  shows "u64_ok E (field_off env flds f)"
proof -
  have each: "\<And>fld. fld \<in> set flds \<Longrightarrow> u64_ok E (size_of env (snd fld))"
    using assms by (auto intro!: size_of_ok simp: size_fits_def tsz_fits.simps list_all_iff sizes_in_def)
  have "sum_list (map (eval0 \<circ> (\<lambda>fld. size_of env (snd fld))) (takeWhile (\<lambda>fld. fst fld \<noteq> f) flds))
        \<le> sum_list (map (eval0 \<circ> (\<lambda>fld. size_of env (snd fld))) flds)"
    by (metis map_append sum_list_append le_add1 takeWhile_dropWhile_id)
  also have "... = type_size env 0 (\<lambda>_. 0) (CoreTy_Record flds)"
    by (simp add: eval0_size_of type_size_def comp_def)
  also have "... < u64_max"
    using assms(2) unfolding size_fits_def by (simp add: tsz_fits_lt type_size_def)
  finally have bound: "sum_list (map (eval0 \<circ> (\<lambda>fld. size_of env (snd fld))) (takeWhile (\<lambda>fld. fst fld \<noteq> f) flds)) < u64_max" .
  have pre: "\<forall>fld \<in> set (takeWhile (\<lambda>fld. fst fld \<noteq> f) flds). u64_ok E (size_of env (snd fld))"
  proof
    fix fld assume "fld \<in> set (takeWhile (\<lambda>fld. fst fld \<noteq> f) flds)"
    then have "fld \<in> set flds" by (rule set_takeWhileD[THEN conjunct1])
    then show "u64_ok E (size_of env (snd fld))" by (rule each)
  qed
  show ?thesis
    unfolding field_off_def field_offset_expr_def of_nat_0 size_of_def[symmetric]
    using pre bound by (intro u64_ok_foldr_add) (auto simp: comp_def)
qed

lemma field_off_type:
  "sizes_in E (type_tyvars (CoreTy_Record flds)) \<Longrightarrow> size_fits env 0 (\<lambda>_. 0) (CoreTy_Record flds)
   \<Longrightarrow> expr_type E (field_off env flds f) = Some CTy_U64"
  using field_off_ok by (simp add: u64_ok_def)

lemma field_off_wf:
  assumes "size_fits env 0 (\<lambda>_. 0) (CoreTy_Record flds)"
  shows "expr_wf (field_off env flds f)"
proof -
  let ?ty = "CoreTy_Record flds"
  let ?E = "fmap_of_list (map (\<lambda>v. (size_param v, VT_Scalar CTy_U64)) (type_tyvars_list ?ty))"
  have "sizes_in ?E (type_tyvars ?ty)"
    by (auto simp: sizes_in_def set_type_tyvars_list[symmetric] fmlookup_of_list map_of_size_params)
  then show ?thesis using field_off_ok[OF _ assms] by (simp add: u64_ok_def)
qed

(* The other small expressions of the generator. *)
lemma ptr_add_type:
  assumes "expr_type E p = Some pty" and "is_ptr_ty pty" and "expr_type E off = Some CTy_U64"
  shows "expr_type E (ptr_add p off) = Some pty"
  using assms by (auto simp: ptr_add_def)

lemma ptr_add_wf: "expr_wf p \<Longrightarrow> expr_wf off \<Longrightarrow> expr_wf (ptr_add p off)"
  by (auto simp: ptr_add_def)

lemma buf_size_ok: "u64_ok E e \<Longrightarrow> u64_ok E (buf_size e)"
  unfolding buf_size_def
proof (cases "u64_lit_of e")
  case None
  then show "u64_ok E e \<Longrightarrow> u64_ok E (if expr_positive e then e else e_max (u64_lit 1) e)"
    by (auto simp: e_fold2_def u64_ok_def)
next
  case (Some x)
  then have e: "e = u64_lit x" by (rule u64_lit_of_Some)
  show "u64_ok E e \<Longrightarrow> u64_ok E (if expr_positive e then e else e_max (u64_lit 1) e)"
    unfolding e by (simp add: e_fold2_def max_less_iff_conj)
qed

lemma buf_size_type: "u64_ok E e \<Longrightarrow> expr_type E (buf_size e) = Some CTy_U64"
  using buf_size_ok by (simp add: u64_ok_def)

lemma buf_size_wf: "u64_ok E e \<Longrightarrow> expr_wf (buf_size e)"
  using buf_size_ok[of E e] by (simp add: u64_ok_def)

lemma dim_off_type [simp]: "8 * k < u64_max \<Longrightarrow> expr_type E (dim_off k) = Some CTy_U64"
  by (simp add: dim_off_def e_fold2_def)

lemma dim_off_wf [simp]: "8 * k < u64_max \<Longrightarrow> expr_wf (dim_off k)"
  by (simp add: dim_off_def e_fold2_def)

lemma tag_off_type [simp]: "expr_type E (tag_off env d) = Some CTy_U64"
  by (simp add: tag_off_def)

lemma tag_off_wf [simp]: "expr_wf (tag_off env d)"
  by (simp add: tag_off_def)

lemma tag_lit_type:
  assumes "ctor \<in> set (dt_ctors env d)" and "dt_tags_fit env d"
  shows "expr_type E (tag_lit env d ctor) = Some (tag_ty env d)" and "expr_wf (tag_lit env d ctor)"
  using ctor_tag_fits[OF assms] by (simp_all add: tag_lit_def tag_ty_def)

lemma desc_data_type: "expr_type E p = Some pty \<Longrightarrow> is_ptr_ty pty \<Longrightarrow> expr_type E (desc_data p) = Some CTy_CharPtr"
  by (simp add: desc_data_def)

(* A well-kinded fixed dimension fits uint64_t. *)
lemma dim_size_lt_u64_max:
  assumes "array_dims_well_kinded dims" and "d \<in> set dims"
  shows "dim_size d < u64_max"
proof (cases d)
  case (CoreDim_Fixed n)
  have "dim_in_range d" using assms by (auto simp: array_dims_well_kinded_def list_all_iff)
  then have "0 \<le> n \<and> n \<le> 18446744073709551615" unfolding CoreDim_Fixed by simp
  then show ?thesis unfolding CoreDim_Fixed by (auto simp: dim_size_def u64_max_def nat_less_iff)
qed simp_all

lemma flat_index_raw_type:
  "\<forall>e \<in> set ns. expr_type E e = Some CTy_U64 \<Longrightarrow> \<forall>e \<in> set is. expr_type E e = Some CTy_U64
   \<Longrightarrow> expr_type E (flat_index_raw ns is) = Some CTy_U64"
  by (induction ns "is" rule: flat_index_raw.induct) simp_all

lemma flat_index_raw_wf:
  "\<forall>e \<in> set ns. expr_wf e \<Longrightarrow> \<forall>e \<in> set is. expr_wf e \<Longrightarrow> expr_wf (flat_index_raw ns is)"
  by (induction ns "is" rule: flat_index_raw.induct) simp_all

lemma u64_ok_flat_index_raw:
  "\<forall>e \<in> set ns. u64_ok E e \<Longrightarrow> \<forall>e \<in> set is. u64_ok E e \<Longrightarrow> u64_ok E (flat_index_raw ns is)"
  by (induction ns "is" rule: flat_index_raw.induct) (auto intro!: u64_ok_binop)

lemma fixed_dim_exprs_ok:
  assumes "array_dims_well_kinded dims"
  shows "\<forall>e \<in> set (fixed_dim_exprs dims). u64_ok E e"
  using dim_size_lt_u64_max[OF assms] by (auto simp: fixed_dim_exprs_def)

lemma desc_dim_exprs_ok:
  assumes "8 * length dims < u64_max" and "expr_type E p = Some CTy_CharPtr" and "expr_wf p"
  shows "\<forall>e \<in> set (desc_dim_exprs p (length dims)). u64_ok E e"
proof
  fix e assume "e \<in> set (desc_dim_exprs p (length dims))"
  then obtain k where k: "k < length dims" and e: "e = ME_Load CTy_U64 (ptr_add p (dim_off k))"
    by (auto simp: desc_dim_exprs_def)
  have "8 * k < u64_max" using k assms(1) by simp
  then show "u64_ok E e"
    unfolding e u64_ok_def using assms(2,3) by (simp add: ptr_add_def)
qed

lemma elem_addr_type:
  assumes "sizes_in E (type_tyvars elemTy)" and "size_fits env 0 (\<lambda>_. 0) elemTy"
    and "array_dims_well_kinded dims" and "\<not> dims_all_fixed dims \<longrightarrow> 8 * length dims < u64_max"
    and "expr_type E p = Some CTy_CharPtr" and "expr_wf p"
    and "\<forall>e \<in> set idxs. u64_ok E e"
  shows "expr_type E (elem_addr env elemTy dims p idxs) = Some CTy_CharPtr"
    and "expr_wf (elem_addr env elemTy dims p idxs)"
proof -
  have esz: "u64_ok E (size_of env elemTy)" using assms(1,2) by (rule size_of_ok)
  note fixed = fixed_dim_exprs_ok[OF assms(3)]
  have off: "u64_ok E (if dims_all_fixed dims then elem_offset_raw (size_of env elemTy) (fixed_dim_exprs dims) idxs
                       else elem_offset_raw (size_of env elemTy) (desc_dim_exprs p (length dims)) idxs)"
  proof (cases "dims_all_fixed dims")
    case True
    then show ?thesis
      unfolding elem_offset_raw_def
      by (simp, intro u64_ok_binop[OF esz u64_ok_flat_index_raw[OF fixed assms(7)]]) simp
  next
    case False
    note desc = desc_dim_exprs_ok[OF assms(4)[rule_format, OF False] assms(5,6)]
    show ?thesis using False
      unfolding elem_offset_raw_def
      by (simp, intro u64_ok_binop[OF esz u64_ok_flat_index_raw[OF desc assms(7)]]) simp
  qed
  show "expr_type E (elem_addr env elemTy dims p idxs) = Some CTy_CharPtr"
    using assms(5) off by (auto simp: elem_addr_def desc_data_def u64_ok_def split: if_splits)
  show "expr_wf (elem_addr env elemTy dims p idxs)"
    using assms(6) off by (auto simp: elem_addr_def desc_data_def u64_ok_def split: if_splits)
qed

end
