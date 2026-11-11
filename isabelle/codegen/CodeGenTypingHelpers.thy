theory CodeGenTypingHelpers
  imports CodeGenTypingInv
begin

(* ========================================================================== *)
(* The typing theorem: the helpers of the term lowering                       *)
(* ========================================================================== *)


section \<open>Facts about Core typing\<close>

(* A constructor is among its datatype's constructors (tyenv_well_formed:
   TE_DataCtors, TE_Datatypes and TE_DataCtorsByType are consistent). *)
lemma ctor_in_dt_ctors:
  assumes "tyenv_well_formed env" and "fmlookup (TE_DataCtors env) c = Some (d, tyvars, payloadTy)"
  shows "c \<in> set (dt_ctors env d)"
proof -
  have "fmlookup (TE_Datatypes env) d = Some (length tyvars)"
    using assms unfolding tyenv_well_formed_def tyenv_ctors_consistent_def by blast
  then have "d |\<in>| fmdom (TE_Datatypes env)" by (simp add: fmlookup_dom_iff)
  moreover have "fmdom (TE_Datatypes env) |\<subseteq>| fmdom (TE_DataCtorsByType env)"
    using assms(1) unfolding tyenv_well_formed_def tyenv_datatypes_nonempty_def by blast
  ultimately have "d |\<in>| fmdom (TE_DataCtorsByType env)" by (rule fsubsetD[rotated])
  then obtain ctors where lk: "fmlookup (TE_DataCtorsByType env) d = Some ctors" by (auto simp: fmlookup_dom_iff)
  then have "c \<in> set ctors"
    using assms unfolding tyenv_well_formed_def tyenv_ctors_by_type_consistent_def by blast
  then show ?thesis using lk by (simp add: dt_ctors_def)
qed

lemma scalar_ty_apply_subst: "scalar_ty ty = Some cty \<Longrightarrow> scalar_ty (apply_subst s ty) = Some cty"
  by (cases ty) simp_all

lemma res_cty_apply_subst_scalar: "scalar_ty ty = Some cty \<Longrightarrow> res_cty (apply_subst s ty) = cty"
  by (simp add: scalar_ty_apply_subst)

(* A runtime numeric type is a finite integer type. *)
lemma runtime_numeric_finite:
  assumes "is_numeric_type ty" and "is_runtime_type env ty"
  obtains s b where "ty = CoreTy_FiniteInt s b"
  using assms by (cases ty) auto

lemma those_Some_elem:
  "those xs = Some ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<exists>y. x = Some y \<and> y \<in> set ys"
  by (induction xs arbitrary: ys) (auto split: option.splits)

lemma those_Some_nth:
  "those xs = Some ys \<Longrightarrow> length ys = length xs \<and> (\<forall>i < length xs. xs ! i = Some (ys ! i))"
  by (induction xs arbitrary: ys) (auto split: option.splits simp: nth_Cons split: nat.splits)

(* The fitting of every type of a term (the hypothesis of the term lemma,
   established by the size check). *)
definition fits :: "CoreTyEnv \<Rightarrow> CoreType \<Rightarrow> bool" where
  "fits env ty = size_fits env 0 (\<lambda>_. 0) ty"

definition term_fits :: "CoreTyEnv \<Rightarrow> CoreTerm \<Rightarrow> bool" where
  "term_fits env tm = (\<exists>tys. term_types env tm = Some tys \<and> (\<forall>ty \<in> set tys. fits env ty))"

lemma term_fits_type:
  assumes "term_fits env tm"
  obtains ty where "core_term_type env NotGhost tm = Some ty" and "fits env ty"
  using assms unfolding term_fits_def term_types.simps[of env tm]
  by (auto split: option.splits)

lemma term_fits_unfold:
  assumes "term_fits env tm"
  shows "\<exists>ty tys. core_term_type env NotGhost tm = Some ty \<and> fits env ty
          \<and> (case tm of
              CoreTm_LitArray _ tms \<Rightarrow> map_option concat (those (map (term_types env) tms))
            | CoreTm_Cast _ t \<Rightarrow> term_types env t
            | CoreTm_Unop _ t \<Rightarrow> term_types env t
            | CoreTm_Binop _ t1 t2 \<Rightarrow>
                (case (term_types env t1, term_types env t2) of
                   (Some l1, Some l2) \<Rightarrow> Some (l1 @ l2) | _ \<Rightarrow> None)
            | CoreTm_Let x t1 t2 \<Rightarrow>
                (case core_term_type env NotGhost t1 of
                   None \<Rightarrow> None
                 | Some rhsTy \<Rightarrow>
                     (case (term_types env t1, term_types (let_env env x rhsTy) t2) of
                        (Some l1, Some l2) \<Rightarrow> Some (l1 @ l2) | _ \<Rightarrow> None))
            | CoreTm_FunctionCall _ tys args \<Rightarrow>
                map_option (\<lambda>ls. tys @ concat ls) (those (map (term_types env) args))
            | CoreTm_VariantCtor _ tys t \<Rightarrow> map_option (\<lambda>l. tys @ l) (term_types env t)
            | CoreTm_Record flds \<Rightarrow> map_option concat (those (map (term_types env \<circ> snd) flds))
            | CoreTm_RecordProj t _ \<Rightarrow> term_types env t
            | CoreTm_VariantProj t _ \<Rightarrow> term_types env t
            | CoreTm_ArrayProj t idxs \<Rightarrow>
                (case (term_types env t, those (map (term_types env) idxs)) of
                   (Some l, Some ls) \<Rightarrow> Some (l @ concat ls) | _ \<Rightarrow> None)
            | CoreTm_Match s arms \<Rightarrow>
                (case (term_types env s, those (map (term_types env \<circ> snd) arms)) of
                   (Some l, Some ls) \<Rightarrow> Some (l @ concat ls) | _ \<Rightarrow> None)
            | CoreTm_Sizeof t \<Rightarrow> term_types env t
            | _ \<Rightarrow> Some []) = Some tys
          \<and> (\<forall>ty \<in> set tys. fits env ty)"
  using assms unfolding term_fits_def term_types.simps[of env tm]
  by (auto split: option.splits)

lemma term_fitsI: "term_types env t = Some l \<Longrightarrow> (\<forall>ty \<in> set l. fits env ty) \<Longrightarrow> term_fits env t"
  by (auto simp: term_fits_def)

(* The destructors, one per term form that has subterms. *)
lemma term_fits_of_those:
  assumes "those (map (term_types env) ts) = Some ls" and "\<forall>ty \<in> set (concat ls). fits env ty" and "t \<in> set ts"
  shows "term_fits env t"
proof -
  from those_Some_elem[OF assms(1), of "term_types env t"] assms(3) obtain l where "term_types env t = Some l" "l \<in> set ls"
    by auto
  then show ?thesis using assms(2) by (auto simp: term_fits_def)
qed

lemma term_fits_LitArray:
  assumes "term_fits env (CoreTm_LitArray ety tms)" and "t \<in> set tms"
  shows "term_fits env t"
proof -
  from term_fits_unfold[OF assms(1)] obtain ty tys ls where th: "those (map (term_types env) tms) = Some ls"
    and tys: "tys = ty # concat ls" and f: "\<forall>ty \<in> set tys. fits env ty"
    by (auto split: option.splits)
  show ?thesis using term_fits_of_those[OF th _ assms(2)] f tys by simp
qed

lemma term_fits_Cast: "term_fits env (CoreTm_Cast ty t) \<Longrightarrow> term_fits env t"
  using term_fits_unfold[of env "CoreTm_Cast ty t"] by (auto simp: term_fits_def split: option.splits)

lemma term_fits_Unop: "term_fits env (CoreTm_Unop op t) \<Longrightarrow> term_fits env t"
  using term_fits_unfold[of env "CoreTm_Unop op t"] by (auto simp: term_fits_def split: option.splits)

lemma term_fits_Binop: "term_fits env (CoreTm_Binop op t1 t2) \<Longrightarrow> term_fits env t1 \<and> term_fits env t2"
  using term_fits_unfold[of env "CoreTm_Binop op t1 t2"] by (auto simp: term_fits_def split: option.splits)

lemma fits_let_env [simp]: "fits (let_env env x ty') ty = fits env ty"
  unfolding fits_def let_env_def by (rule size_fits_cong_env) simp_all

lemma term_fits_Let:
  assumes "term_fits env (CoreTm_Let x t1 t2)" and "core_term_type env NotGhost t1 = Some rhsTy"
  shows "term_fits env t1 \<and> term_fits (let_env env x rhsTy) t2"
proof -
  from term_fits_unfold[OF assms(1)] obtain ty tys l1 l2 where
    "term_types env t1 = Some l1" "term_types (let_env env x rhsTy) t2 = Some l2"
    "tys = ty # l1 @ l2" "\<forall>ty \<in> set tys. fits env ty"
    using assms(2) by (auto split: option.splits)
  then show ?thesis by (auto simp: term_fits_def)
qed

lemma term_fits_FunctionCall:
  assumes "term_fits env (CoreTm_FunctionCall f tys args)"
  shows "(\<forall>t \<in> set args. term_fits env t) \<and> (\<forall>ty \<in> set tys. fits env ty)"
proof -
  from term_fits_unfold[OF assms(1)] obtain ty tys' ls where th: "those (map (term_types env) args) = Some ls"
    and tys': "tys' = ty # tys @ concat ls" and f: "\<forall>ty \<in> set tys'. fits env ty"
    by (auto split: option.splits)
  show ?thesis using term_fits_of_those[OF th] f tys' by auto
qed

lemma term_fits_VariantCtor:
  "term_fits env (CoreTm_VariantCtor c tys t) \<Longrightarrow> term_fits env t \<and> (\<forall>ty \<in> set tys. fits env ty)"
  using term_fits_unfold[of env "CoreTm_VariantCtor c tys t"] by (auto simp: term_fits_def split: option.splits)

lemma term_fits_Record:
  assumes "term_fits env (CoreTm_Record flds)" and "(f, t) \<in> set flds"
  shows "term_fits env t"
proof -
  from term_fits_unfold[OF assms(1)] obtain ty tys ls where th: "those (map (term_types env \<circ> snd) flds) = Some ls"
    and tys: "tys = ty # concat ls" and fi: "\<forall>ty \<in> set tys. fits env ty"
    by (auto split: option.splits)
  have th': "those (map (term_types env) (map snd flds)) = Some ls" using th by (simp add: map_map[symmetric] comp_def)
  have mem: "t \<in> set (map snd flds)" using assms(2) by (force simp: image_iff)
  show ?thesis using term_fits_of_those[OF th' _ mem] fi tys by simp
qed

lemma term_fits_RecordProj: "term_fits env (CoreTm_RecordProj t f) \<Longrightarrow> term_fits env t"
  using term_fits_unfold[of env "CoreTm_RecordProj t f"] by (auto simp: term_fits_def split: option.splits)

lemma term_fits_VariantProj: "term_fits env (CoreTm_VariantProj t c) \<Longrightarrow> term_fits env t"
  using term_fits_unfold[of env "CoreTm_VariantProj t c"] by (auto simp: term_fits_def split: option.splits)

lemma term_fits_ArrayProj:
  assumes "term_fits env (CoreTm_ArrayProj t idxs)"
  shows "term_fits env t \<and> (\<forall>i \<in> set idxs. term_fits env i)"
proof -
  from term_fits_unfold[OF assms(1)] obtain ty tys l ls where tt: "term_types env t = Some l"
    and th: "those (map (term_types env) idxs) = Some ls"
    and tys: "tys = ty # l @ concat ls" and f: "\<forall>ty \<in> set tys. fits env ty"
    by (auto split: option.splits)
  show ?thesis using term_fits_of_those[OF th] f tys tt by (auto simp: term_fits_def)
qed

lemma term_fits_Match:
  assumes "term_fits env (CoreTm_Match s arms)"
  shows "term_fits env s \<and> (\<forall>(p, body) \<in> set arms. term_fits env body)"
proof -
  from term_fits_unfold[OF assms(1)] obtain ty tys l ls where ts: "term_types env s = Some l"
    and th: "those (map (term_types env \<circ> snd) arms) = Some ls"
    and tys: "tys = ty # l @ concat ls" and f: "\<forall>ty \<in> set tys. fits env ty"
    by (auto split: option.splits)
  have th': "those (map (term_types env) (map snd arms)) = Some ls" using th by (simp add: map_map[symmetric] comp_def)
  show ?thesis
  proof (intro conjI ballI)
    show "term_fits env s" using ts f tys by (auto simp: term_fits_def)
    fix pb assume "pb \<in> set arms"
    then have "snd pb \<in> set (map snd arms)" by auto
    then have "term_fits env (snd pb)" using term_fits_of_those[OF th'] f tys by auto
    then show "case pb of (p, body) \<Rightarrow> term_fits env body" by (cases pb) auto
  qed
qed

lemma term_fits_Sizeof: "term_fits env (CoreTm_Sizeof t) \<Longrightarrow> term_fits env t"
  using term_fits_unfold[of env "CoreTm_Sizeof t"] by (auto simp: term_fits_def split: option.splits)

(* Components of a fitting type fit (from tsz_fits). *)
lemma fits_Record_fld:
  assumes "fits env (CoreTy_Record flds)" and "map_of flds f = Some fty"
  shows "fits env fty"
proof -
  have "(f, fty) \<in> set flds" by (rule map_of_SomeD[OF assms(2)])
  then show ?thesis using assms(1) unfolding fits_def size_fits_def by (auto simp: tsz_fits.simps list_all_iff)
qed

lemma fits_Array_elem_fixed: "fits env (CoreTy_Array elemTy dims) \<Longrightarrow> dims_all_fixed dims \<Longrightarrow> fits env elemTy"
  unfolding fits_def size_fits_def by (simp add: tsz_fits.simps)

lemma fits_Array_desc: "fits env (CoreTy_Array elemTy dims) \<Longrightarrow> \<not> dims_all_fixed dims \<Longrightarrow> 8 * length dims < u64_max"
  unfolding fits_def size_fits_def by (simp add: tsz_fits.simps desc_size_def)

lemma fits_Array_dims: "fits env (CoreTy_Array elemTy dims) \<Longrightarrow> \<not> dims_all_fixed dims \<longrightarrow> 8 * length dims < u64_max"
  using fits_Array_desc by blast

lemma cg_size_ok:
  assumes "cg_ok prog E cg" and "is_well_kinded (CG_TyEnv cg) ty" and "fits (CG_TyEnv cg) ty"
  shows "u64_ok E (cg_size cg ty)"
  unfolding cg_size_def using cg_ok_sizes[OF assms(1,2)] assms(3)[unfolded fits_def] by (rule size_of_ok)

lemma cg_buf_size_ok:
  assumes "cg_ok prog E cg" and "is_well_kinded (CG_TyEnv cg) ty" and "fits (CG_TyEnv cg) ty"
  shows "u64_ok E (buf_size (cg_size cg ty))"
  using cg_size_ok[OF assms] by (rule buf_size_ok)

lemma cg_field_off_ok:
  assumes "cg_ok prog E cg" and "is_well_kinded (CG_TyEnv cg) (CoreTy_Record flds)" and "fits (CG_TyEnv cg) (CoreTy_Record flds)"
  shows "u64_ok E (field_off (CG_TyEnv cg) flds f)"
  using cg_ok_sizes[OF assms(1,2)] assms(3)[unfolded fits_def] by (rule field_off_ok)

lemma cg_elem_addr_ok:
  assumes "cg_ok prog E cg" and "is_well_kinded (CG_TyEnv cg) (CoreTy_Array elemTy dims)" and "fits (CG_TyEnv cg) elemTy"
    and "fits (CG_TyEnv cg) (CoreTy_Array elemTy dims)"
    and "expr_ok E p CTy_CharPtr" and "\<forall>e \<in> set idxs. u64_ok E e"
  shows "expr_ok E (elem_addr (CG_TyEnv cg) elemTy dims p idxs) CTy_CharPtr"
proof -
  have wk: "is_well_kinded (CG_TyEnv cg) elemTy" and dims: "array_dims_well_kinded dims" using assms(2) by simp_all
  show ?thesis
    unfolding expr_ok_def
    using elem_addr_type[OF cg_ok_sizes[OF assms(1) wk] assms(3)[unfolded fits_def] dims fits_Array_dims[OF assms(4)]
                            assms(5)[unfolded expr_ok_def, THEN conjunct1] assms(5)[unfolded expr_ok_def, THEN conjunct2] assms(6)]
    by simp
qed


section \<open>Results of calls\<close>

(* The result of a call, typed for the declared return type of the callee. *)
fun res_ok :: "MTyEnv \<Rightarrow> FunInfo \<Rightarrow> CallRes \<Rightarrow> bool" where
  "res_ok E info (CR_Scalar e) = (\<exists>cty. ret_kind (FI_ReturnType info) = RK_Scalar cty \<and> expr_ok E e cty)"
| "res_ok E info (CR_Place p) = (ret_kind (FI_ReturnType info) = RK_Buf \<and> expr_ok E p CTy_CharPtr)"
| "res_ok E info CR_Unit = (ret_kind (FI_ReturnType info) = RK_Unit)"

lemma res_ok_mono: "env_le E E' \<Longrightarrow> res_ok E info res \<Longrightarrow> res_ok E' info res"
  by (cases res) (auto intro: expr_ok_mono)

(* The result as a term of the instantiated return type. *)
lemma call_result_expr_ok:
  assumes "res_ok E info res" and "call_result_expr (apply_subst s (FI_ReturnType info)) res = Some e"
  shows "expr_ok E e (res_cty (apply_subst s (FI_ReturnType info)))"
proof (cases res)
  case (CR_Scalar e')
  then obtain cty where "ret_kind (FI_ReturnType info) = RK_Scalar cty" "expr_ok E e' cty"
    using assms(1) by auto
  then have "scalar_ty (FI_ReturnType info) = Some cty" by (auto simp: ret_kind_def split: option.splits if_splits)
  then show ?thesis using assms(2) \<open>expr_ok E e' cty\<close> CR_Scalar
    by (simp add: call_result_expr_def res_cty_apply_subst_scalar)
next
  case (CR_Place p)
  then show ?thesis using assms by (auto simp: call_result_expr_def intro: expr_ok_load_at)
next
  case CR_Unit
  then show ?thesis using assms(2) by (simp add: call_result_expr_def)
qed

lemma call_result_expr_None: "call_result_expr rty res = None \<longleftrightarrow> res = CR_Unit"
  by (cases res) (simp_all add: call_result_expr_def)


section \<open>Variables and lazy references\<close>

lemma read_rep_ok:
  assumes "read_rep cg rep ty st = Inr ((S, e), st')"
    and "cg_ok prog E cg" and "scope_ok prog (E, ds) st" and "rep_ok E (CG_TyEnv cg) ty rep"
    and lazy: "\<And>ll S a st'. rep = VR_Lazy ll \<Longrightarrow> lazy_addr cg ll st = Inr ((S, a), st') \<Longrightarrow>
                 \<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' a CTy_CharPtr"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e (res_cty ty)"
proof (cases rep)
  case (VR_Scalar n cty)
  then have "S = []" "e = ME_Var n" "st' = st" using assms(1) by (simp_all add: read_rep_def)
  then show ?thesis using assms(3,4) VR_Scalar
    by (intro exI[where x = E] exI[where x = ds] conjI) (auto simp: expr_ok_def intro: lowered_ok_nil)
next
  case (VR_Buf n)
  then have "S = []" "e = ME_AddrOf n" "st' = st" using assms(1) by (simp_all add: read_rep_def)
  then show ?thesis using assms(3,4) VR_Buf
    by (intro exI[where x = E] exI[where x = ds] conjI) (auto simp: expr_ok_def intro: lowered_ok_nil)
next
  case (VR_Ptr n)
  then have "S = []" "e = load_at ty (ME_Var n)" "st' = st" using assms(1) by (simp_all add: read_rep_def)
  then show ?thesis using assms(3,4) VR_Ptr expr_ok_load_at[of E "ME_Var n" ty]
    by (intro exI[where x = E] exI[where x = ds] conjI) (auto simp: expr_ok_def intro: lowered_ok_nil)
next
  case (VR_Lazy ll)
  with assms(1) obtain S' a st'' where la: "lazy_addr cg ll st = Inr ((S', a), st'')"
    and S: "S = S'" and e: "e = load_at ty a" and st': "st' = st''"
    by (auto simp: read_rep_def elim!: cg_bind_InrE)
  from lazy[OF VR_Lazy la] obtain E' ds' where "lowered_ok prog rt (E, ds) st S' st'' (E', ds')" "expr_ok E' a CTy_CharPtr"
    by blast
  then show ?thesis unfolding S e st' using expr_ok_load_at by blast
qed

lemma cast_place_ok:
  assumes "cast_place cg fromTy toTy p st = Inr ((S, a), st')"
    and "cg_ok prog E cg" and "scope_ok prog (E, ds) st" and "expr_ok E p CTy_CharPtr"
    and "array_cast_ok fromTy toTy" and "is_well_kinded (CG_TyEnv cg) fromTy"
    and "is_well_kinded (CG_TyEnv cg) toTy" and "fits (CG_TyEnv cg) toTy"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' a CTy_CharPtr"
proof -
  from assms(5) obtain elemTy dimsF dimsT where f: "fromTy = CoreTy_Array elemTy dimsF"
    and t: "toTy = CoreTy_Array elemTy dimsT" and lens: "length dimsF = length dimsT"
    by (cases fromTy; cases toTy) (auto simp: list_all2_lengthD)
  show ?thesis
  proof (cases "dims_all_fixed dimsF = dims_all_fixed dimsT")
    case True
    then have "S = []" "a = p" "st' = st" using assms(1) unfolding cast_place_def f t by simp_all
    then show ?thesis using assms(3,4) by (intro exI[where x = E] exI[where x = ds] conjI) (auto intro: lowered_ok_nil)
  next
    case False
    show ?thesis
    proof (cases "dims_all_fixed dimsF")
      case True
      then have bd: "build_desc cg dimsF toTy p st = Inr ((S, a), st')" and nf: "\<not> dims_all_fixed dimsT"
        using assms(1) False unfolding cast_place_def f t by auto
      have sz: "u64_ok E (cg_size cg toTy)" using assms(2,7,8) by (rule cg_size_ok)
      have wk: "array_dims_well_kinded dimsF" using assms(6) f by simp
      have "8 * length dimsT < u64_max" using assms(8) nf t by (auto dest: fits_Array_desc)
      then have len: "8 * length dimsF < u64_max" by (simp add: lens)
      show ?thesis by (rule build_desc_ok[OF bd assms(3,4) sz wk len])
    next
      case False2: False
      then have "S = []" "a = desc_data p" "st' = st" using assms(1) False unfolding cast_place_def f t by simp_all
      then show ?thesis using assms(3,4)
        by (intro exI[where x = E] exI[where x = ds] conjI) (auto simp: expr_ok_def desc_data_def intro: lowered_ok_nil)
    qed
  qed
qed

lemma cast_result_ok:
  assumes "cast_result cg fromTy toTy e st = Inr ((S, e'), st')"
    and "cg_ok prog E cg" and "scope_ok prog (E, ds) st" and "expr_ok E e (res_cty fromTy)"
    and "cast_ok (CG_TyEnv cg) fromTy toTy" and "is_runtime_type (CG_TyEnv cg) fromTy" and "is_runtime_type (CG_TyEnv cg) toTy"
    and "is_well_kinded (CG_TyEnv cg) fromTy" and "is_well_kinded (CG_TyEnv cg) toTy" and "fits (CG_TyEnv cg) toTy"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e' (res_cty toTy)"
proof (cases "scalar_ty toTy")
  case (Some cty)
  have "is_numeric_type toTy" using assms(5) Some by (cases toTy) (auto simp: cast_ok_def)
  then obtain s b where t: "toTy = CoreTy_FiniteInt s b" using Some by (cases toTy) auto
  then have "is_numeric_type fromTy" using assms(5) by (cases fromTy) (auto simp: cast_ok_def)
  then obtain s' b' where f: "fromTy = CoreTy_FiniteInt s' b'" using assms(6) by (rule runtime_numeric_finite)
  have "S = []" "e' = ME_Cast (CTy_Int s b) e" "st' = st" using assms(1) unfolding cast_result_def Some t by simp_all
  then show ?thesis using assms(3,4) f t
    by (intro exI[where x = E] exI[where x = ds] conjI) (auto simp: expr_ok_def intro: lowered_ok_nil)
next
  case None
  then have cp: "cast_place cg fromTy toTy e st = Inr ((S, e'), st')" using assms(1) by (simp add: cast_result_def)
  have arr: "array_cast_ok fromTy toTy" using assms(5,7) None by (cases toTy) (auto simp: cast_ok_def)
  from arr obtain elemTy dims where f: "fromTy = CoreTy_Array elemTy dims" by (cases fromTy) auto
  have "expr_ok E e CTy_CharPtr" using assms(4) f by (simp add: res_cty_def)
  then show ?thesis using cast_place_ok[OF cp assms(2,3) _ arr assms(8,9,10)] None by (simp add: res_cty_def)
qed

(* The lazy address. *)
lemma lazy_addr_ok:
  "lazy_addr cg ll st = Inr ((S, a), st') \<Longrightarrow> cg_ok prog E cg \<Longrightarrow> scope_ok prog (E, ds) st \<Longrightarrow> ll_ok E (CG_TyEnv cg) ll
   \<Longrightarrow> \<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' a CTy_CharPtr"
proof (induction cg ll arbitrary: E ds st S a st' rule: lazy_addr.induct)
  case (1 cg rep ty)
  then obtain a' where "rep_addr rep = Some a'" "S = []" "a = a'" "st' = st"
    by (auto simp: lazy_addr.simps internal_def cg_fail_def split: option.splits)
  then show ?case using "1.prems"(3,4) rep_addr_ok[of E "CG_TyEnv cg" ty rep a']
    by (intro exI[where x = E] exI[where x = ds] conjI) (auto intro: lowered_ok_nil)
next
  case (2 cg ll f ty)
  from "2.prems"(1) obtain S1 p st1 where la: "lazy_addr cg ll st = Inr ((S1, p), st1)"
    and rest: "(case ll_type ll of CoreTy_Record flds \<Rightarrow> cg_return (S1, ptr_add p (field_off (CG_TyEnv cg) flds f))
                 | _ \<Rightarrow> internal cg ''field of a non-record'') st1 = Inr ((S, a), st')"
    by (auto simp: lazy_addr.simps elim!: cg_bind_InrE)
  from "2.prems"(4) obtain flds where lt: "ll_type ll = CoreTy_Record flds" and sub: "ll_ok E (CG_TyEnv cg) ll" by auto
  from rest lt have S: "S = S1" and a: "a = ptr_add p (field_off (CG_TyEnv cg) flds f)" and st': "st' = st1" by auto
  obtain E' ds' where l: "lowered_ok prog rt (E, ds) st S1 st1 (E', ds')" and p: "expr_ok E' p CTy_CharPtr"
    using "2.IH"[OF la "2.prems"(2,3) sub] by blast
  have ok': "cg_ok prog E' cg" using cg_ok_mono[OF lowered_ok_env_le'[OF l] "2.prems"(2)] by simp
  have off: "u64_ok E' (field_off (CG_TyEnv cg) flds f)"
    using ll_ok_type[OF sub] lt by (intro cg_field_off_ok[OF ok']) (simp_all add: fits_def)
  show ?case unfolding S a st' using l expr_ok_ptr_add[OF p _ off] by auto
next
  case (3 cg ll c ty)
  from "3.prems"(1) obtain S1 p st1 where la: "lazy_addr cg ll st = Inr ((S1, p), st1)"
    and rest: "(case ll_type ll of CoreTy_Datatype dtName _ \<Rightarrow> cg_return (S1, ptr_add p (tag_off (CG_TyEnv cg) dtName))
                 | _ \<Rightarrow> internal cg ''payload of a non-variant'') st1 = Inr ((S, a), st')"
    by (auto simp: lazy_addr.simps elim!: cg_bind_InrE)
  from "3.prems"(4) obtain d args where lt: "ll_type ll = CoreTy_Datatype d args" and sub: "ll_ok E (CG_TyEnv cg) ll" by auto
  from rest lt have S: "S = S1" and a: "a = ptr_add p (tag_off (CG_TyEnv cg) d)" and st': "st' = st1" by auto
  obtain E' ds' where l: "lowered_ok prog rt (E, ds) st S1 st1 (E', ds')" and p: "expr_ok E' p CTy_CharPtr"
    using "3.IH"[OF la "3.prems"(2,3) sub] by blast
  have off: "u64_ok E' (tag_off (CG_TyEnv cg) d)" by (simp add: u64_ok_def)
  show ?case unfolding S a st' using l expr_ok_ptr_add[OF p _ off] by auto
next
  case (4 cg ll vs ty)
  from "4.prems"(1) obtain S1 p st1 where la: "lazy_addr cg ll st = Inr ((S1, p), st1)"
    and rest: "(case ll_type ll of CoreTy_Array elemTy dims \<Rightarrow>
                   cg_return (S1, elem_addr (CG_TyEnv cg) elemTy dims p (map ME_Var vs))
                 | _ \<Rightarrow> internal cg ''index of a non-array'') st1 = Inr ((S, a), st')"
    by (auto simp: lazy_addr.simps elim!: cg_bind_InrE)
  from "4.prems"(4) obtain dims where lt: "ll_type ll = CoreTy_Array ty dims" and sub: "ll_ok E (CG_TyEnv cg) ll"
    and vs: "\<forall>v \<in> set vs. fmlookup E v = Some (VT_Scalar CTy_U64)"
    and wk: "is_well_kinded (CG_TyEnv cg) ty" and ft: "fits (CG_TyEnv cg) ty" by (auto simp: fits_def)
  from rest lt have S: "S = S1" and a: "a = elem_addr (CG_TyEnv cg) ty dims p (map ME_Var vs)" and st': "st' = st1" by auto
  obtain E' ds' where l: "lowered_ok prog rt (E, ds) st S1 st1 (E', ds')" and p: "expr_ok E' p CTy_CharPtr"
    using "4.IH"[OF la "4.prems"(2,3) sub] by blast
  have le: "env_le E E'" using l by (rule lowered_ok_env_le')
  have ok': "cg_ok prog E' cg" using cg_ok_mono[OF le "4.prems"(2)] by simp
  have idx: "\<forall>e \<in> set (map ME_Var vs). u64_ok E' e"
    using vs env_le_lookup[OF le] by (auto simp: u64_ok_def)
  have arr_wk: "is_well_kinded (CG_TyEnv cg) (CoreTy_Array ty dims)" and arr_ft: "fits (CG_TyEnv cg) (CoreTy_Array ty dims)"
    using ll_ok_type[OF sub] lt by (simp_all add: fits_def)
  show ?case unfolding S a st' using l cg_elem_addr_ok[OF ok' arr_wk ft arr_ft p idx] by auto
next
  case (5 cg ll ty)
  from "5.prems"(1) obtain S1 p st1 S2 p2 st2 where la: "lazy_addr cg ll st = Inr ((S1, p), st1)"
    and cp: "cast_place cg (ll_type ll) ty p st1 = Inr ((S2, p2), st2)"
    and S: "S = S1 @ S2" and a: "a = p2" and st': "st' = st2"
    by (auto simp: lazy_addr.simps elim!: cg_bind_InrE)
  from "5.prems"(4) have sub: "ll_ok E (CG_TyEnv cg) ll" and ac: "array_cast_ok (ll_type ll) ty"
    and wk: "is_well_kinded (CG_TyEnv cg) ty" and ft: "fits (CG_TyEnv cg) ty" by (auto simp: fits_def)
  obtain E1 ds1 where l1: "lowered_ok prog rt (E, ds) st S1 st1 (E1, ds1)" and p: "expr_ok E1 p CTy_CharPtr"
    using "5.IH"[OF la "5.prems"(2,3) sub] by blast
  have ok1: "cg_ok prog E1 cg" using cg_ok_mono[OF lowered_ok_env_le'[OF l1] "5.prems"(2)] by simp
  obtain E2 ds2 where l2: "lowered_ok prog rt (E1, ds1) st1 S2 st2 (E2, ds2)" and p2: "expr_ok E2 p2 CTy_CharPtr"
    using cast_place_ok[OF cp ok1 lowered_ok_scope[OF l1] p ac ll_ok_type[OF sub, THEN conjunct1] wk ft] by blast
  show ?case unfolding S a st' using lowered_ok_append[OF l1 l2] p2 by blast
qed

lemma addr_rep_ok:
  assumes "addr_rep cg rep st = Inr ((S, a), st')"
    and "cg_ok prog E cg" and "scope_ok prog (E, ds) st" and "rep_ok E (CG_TyEnv cg) ty rep"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' a CTy_CharPtr"
proof (cases rep)
  case (VR_Lazy ll)
  then show ?thesis using assms lazy_addr_ok[OF _ assms(2,3)] by (simp add: addr_rep_def)
next
  case (VR_Scalar n cty)
  then have "S = []" "a = ME_AddrOf n" "st' = st" using assms(1) by (simp_all add: addr_rep_def)
  then show ?thesis using assms(3,4) VR_Scalar
    by (intro exI[where x = E] exI[where x = ds] conjI) (auto simp: expr_ok_def intro: lowered_ok_nil)
next
  case (VR_Buf n)
  then have "S = []" "a = ME_AddrOf n" "st' = st" using assms(1) by (simp_all add: addr_rep_def)
  then show ?thesis using assms(3,4) VR_Buf
    by (intro exI[where x = E] exI[where x = ds] conjI) (auto simp: expr_ok_def intro: lowered_ok_nil)
next
  case (VR_Ptr n)
  then have "S = []" "a = ME_Var n" "st' = st" using assms(1) by (simp_all add: addr_rep_def)
  then show ?thesis using assms(3,4) VR_Ptr
    by (intro exI[where x = E] exI[where x = ds] conjI) (auto simp: expr_ok_def intro: lowered_ok_nil)
qed

lemma read_rep_ok':
  assumes "read_rep cg rep ty st = Inr ((S, e), st')"
    and "cg_ok prog E cg" and "scope_ok prog (E, ds) st" and "rep_ok E (CG_TyEnv cg) ty rep"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e (res_cty ty)"
proof (rule read_rep_ok[OF assms])
  fix ll S a st'
  assume "rep = VR_Lazy ll" "lazy_addr cg ll st = Inr ((S, a), st')"
  then show "\<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' a CTy_CharPtr"
    using lazy_addr_ok[OF _ assms(2,3)] assms(4) by simp
qed


section \<open>Temporaries, matches\<close>

lemma temp_for_ok:
  assumes "temp_for cg hint ty st = Inr ((tmp, decl), st')"
    and "cg_ok prog E cg" and "scope_ok prog (E, ds) st" and "is_well_kinded (CG_TyEnv cg) ty" and "fits (CG_TyEnv cg) ty"
  obtains E' where "lowered_ok prog rt (E, ds) st [decl] st' (E', tmp # ds)"
    and "expr_ok E' (temp_result ty tmp) (res_cty ty)"
    and "fmlookup E' tmp = Some (case scalar_ty ty of Some cty \<Rightarrow> VT_Scalar cty | None \<Rightarrow> VT_Buf)"
    and "E' = fmupd tmp (case scalar_ty ty of Some cty \<Rightarrow> VT_Scalar cty | None \<Rightarrow> VT_Buf) E"
proof -
  from assms(1) obtain st1 where fr: "fresh_name (CG_Fun cg) hint st = Inr (tmp, st1)" and st': "st' = st1"
    and decl: "decl = (case scalar_ty ty of Some cty \<Rightarrow> MS_DeclScalar tmp cty | None \<Rightarrow> MS_DeclBuf tmp (buf_size (cg_size cg ty)))"
    by (auto simp: temp_for_def elim!: cg_bind_InrE)
  show thesis
  proof (cases "scalar_ty ty")
    case (Some cty)
    show thesis
      by (rule that[of "fmupd tmp (VT_Scalar cty) E"])
         (use fresh_scalar_ok[OF assms(3) fr, where cty = cty] Some
          in \<open>auto simp: decl st' temp_result_def expr_ok_def\<close>)
  next
    case None
    have sz: "u64_ok E (buf_size (cg_size cg ty))" using assms(2,4,5) by (rule cg_buf_size_ok)
    show thesis
      by (rule that[of "fmupd tmp VT_Buf E"])
         (use fresh_buf_ok[OF assms(3) fr sz] None
          in \<open>auto simp: decl st' temp_result_def expr_ok_def\<close>)
  qed
qed

lemma temp_store_ok:
  assumes "scope_ok prog (E, ds) st"
    and "fmlookup E tmp = Some (case scalar_ty ty of Some cty \<Rightarrow> VT_Scalar cty | None \<Rightarrow> VT_Buf)"
    and "expr_ok E e (res_cty ty)" and "u64_ok E (cg_size cg ty)"
  shows "lowered_ok prog rt (E, ds) st [temp_store cg ty tmp e] st (E, ds)"
proof (cases "scalar_ty ty")
  case (Some cty)
  then have ts: "temp_store cg ty tmp e = MS_Assign tmp e" by (simp add: temp_store_def)
  show ?thesis unfolding ts using assms Some by (intro assign_ok[where cty' = cty]) auto
next
  case None
  then have ts: "temp_store cg ty tmp e = MS_Copy (ME_AddrOf tmp) e (cg_size cg ty)" by (simp add: temp_store_def)
  show ?thesis unfolding ts using assms None
    by (intro copy_ok[where dty = CTy_CharPtr and sty = CTy_CharPtr]) (auto simp: expr_ok_def)
qed

(* The tag of a scrutinee of the given type. *)
definition tag_cty :: "CoreTyEnv \<Rightarrow> CoreType \<Rightarrow> CTy" where
  "tag_cty env scrutTy =
    (case scrutTy of
       CoreTy_Datatype d _ \<Rightarrow> tag_ty env d
     | CoreTy_Bool \<Rightarrow> CTy_U8
     | CoreTy_FiniteInt s b \<Rightarrow> CTy_Int s b
     | _ \<Rightarrow> res_cty scrutTy)"

lemma match_tag_ok:
  assumes "match_tag cg scrutTy es st = Inr ((St, tag), st')"
    and "scope_ok prog (E, ds) st" and "expr_ok E es (res_cty scrutTy)"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st St st' (E', ds') \<and> expr_ok E' tag (tag_cty (CG_TyEnv cg) scrutTy)"
proof (cases scrutTy)
  case (CoreTy_Datatype d args)
  from assms(1) obtain t st1 where fr: "fresh_name (CG_Fun cg) ''tag'' st = Inr (t, st1)"
    and St: "St = [MS_DeclScalar t (tag_ty (CG_TyEnv cg) d), MS_Assign t (ME_Load (tag_ty (CG_TyEnv cg) d) es)]"
    and tag: "tag = ME_Var t" and st': "st' = st1"
    unfolding match_tag_def CoreTy_Datatype by (auto elim!: cg_bind_InrE)
  let ?E1 = "fmupd t (VT_Scalar (tag_ty (CG_TyEnv cg) d)) E"
  have d: "lowered_ok prog rt (E, ds) st [MS_DeclScalar t (tag_ty (CG_TyEnv cg) d)] st1 (?E1, t # ds)"
    by (rule fresh_scalar_ok[OF assms(2) fr])
  have es: "expr_ok ?E1 es CTy_CharPtr"
    using assms(3) lowered_ok_env_le[OF d] CoreTy_Datatype by (auto simp: res_cty_def intro: expr_ok_mono)
  have a: "lowered_ok prog rt (?E1, t # ds) st1 [MS_Assign t (ME_Load (tag_ty (CG_TyEnv cg) d) es)] st1 (?E1, t # ds)"
    using lowered_ok_scope[OF d] expr_ok_Load[OF es]
    by (intro assign_ok[where cty' = "tag_ty (CG_TyEnv cg) d"]) auto
  show ?thesis unfolding St tag st' using lowered_ok_append[OF d a] CoreTy_Datatype
    by (auto simp: tag_cty_def expr_ok_def)
next
  case CoreTy_Bool
  from assms(1) obtain t st1 where fr: "fresh_name (CG_Fun cg) ''tag'' st = Inr (t, st1)"
    and St: "St = [MS_DeclScalar t CTy_U8, MS_Assign t es]" and tag: "tag = ME_Var t" and st': "st' = st1"
    unfolding match_tag_def CoreTy_Bool by (auto elim!: cg_bind_InrE)
  let ?E1 = "fmupd t (VT_Scalar CTy_U8) E"
  have d: "lowered_ok prog rt (E, ds) st [MS_DeclScalar t CTy_U8] st1 (?E1, t # ds)"
    by (rule fresh_scalar_ok[OF assms(2) fr])
  have es: "expr_ok ?E1 es CTy_U8"
    using assms(3) lowered_ok_env_le[OF d] CoreTy_Bool by (auto simp: res_cty_def intro: expr_ok_mono)
  have a: "lowered_ok prog rt (?E1, t # ds) st1 [MS_Assign t es] st1 (?E1, t # ds)"
    using lowered_ok_scope[OF d] es by (intro assign_ok[where cty' = CTy_U8]) auto
  show ?thesis unfolding St tag st' using lowered_ok_append[OF d a] CoreTy_Bool
    by (auto simp: tag_cty_def expr_ok_def)
next
  case (CoreTy_FiniteInt s b)
  from assms(1) obtain t st1 where fr: "fresh_name (CG_Fun cg) ''tag'' st = Inr (t, st1)"
    and St: "St = [MS_DeclScalar t (CTy_Int s b), MS_Assign t es]" and tag: "tag = ME_Var t" and st': "st' = st1"
    unfolding match_tag_def CoreTy_FiniteInt by (auto elim!: cg_bind_InrE)
  let ?E1 = "fmupd t (VT_Scalar (CTy_Int s b)) E"
  have d: "lowered_ok prog rt (E, ds) st [MS_DeclScalar t (CTy_Int s b)] st1 (?E1, t # ds)"
    by (rule fresh_scalar_ok[OF assms(2) fr])
  have es: "expr_ok ?E1 es (CTy_Int s b)"
    using assms(3) lowered_ok_env_le[OF d] CoreTy_FiniteInt by (auto simp: res_cty_def intro: expr_ok_mono)
  have a: "lowered_ok prog rt (?E1, t # ds) st1 [MS_Assign t es] st1 (?E1, t # ds)"
    using lowered_ok_scope[OF d] es by (intro assign_ok[where cty' = "CTy_Int s b"]) auto
  show ?thesis unfolding St tag st' using lowered_ok_append[OF d a] CoreTy_FiniteInt
    by (auto simp: tag_cty_def expr_ok_def)
qed (use assms in \<open>auto simp: match_tag_def tag_cty_def intro!: lowered_ok_nil\<close>)

(* The condition of an arm. *)
lemma arm_cond_ok:
  assumes "arm_cond cg scrutTy tag pat st = Inr (c, st')"
    and "tyenv_well_formed (CG_TyEnv cg)" and "\<And>d. dt_tags_fit (CG_TyEnv cg) d"
    and "expr_ok E tag (tag_cty (CG_TyEnv cg) scrutTy)"
    and "pattern_compatible (CG_TyEnv cg) pat scrutTy"
  shows "st' = st \<and> (\<forall>ce. c = Some ce \<longrightarrow> expr_ok E ce CTy_U8)"
proof (cases pat)
  case CorePat_Wildcard
  then show ?thesis using assms(1) by (simp add: arm_cond_def)
next
  case (CorePat_Bool b)
  then have "scrutTy = CoreTy_Bool" using assms(5) by simp
  then show ?thesis using assms(1,4) CorePat_Bool by (auto simp: arm_cond_def tag_cty_def expr_ok_def int_fits_unsigned)
next
  case (CorePat_Int i)
  then obtain s b where "scrutTy = CoreTy_FiniteInt s b" and "int_in_range (int_range s b) i"
    using assms(5) by (cases scrutTy) auto
  then show ?thesis using assms(1,4) CorePat_Int
    by (auto simp: arm_cond_def tag_cty_def expr_ok_def int_fits.simps)
next
  case (CorePat_Variant ctor p)
  then obtain d args tyvars payloadTy where sc: "scrutTy = CoreTy_Datatype d args"
    and lk: "fmlookup (TE_DataCtors (CG_TyEnv cg)) ctor = Some (d, tyvars, payloadTy)"
    using assms(5) by (cases scrutTy) (auto split: option.splits)
  have mem: "ctor \<in> set (dt_ctors (CG_TyEnv cg) d)" using ctor_in_dt_ctors[OF assms(2) lk] .
  note tl = tag_lit_type[OF mem assms(3)]
  show ?thesis using assms(1,4) CorePat_Variant sc tl
    by (auto simp: arm_cond_def tag_cty_def expr_ok_def tag_ty_def internal_def cg_fail_def split: if_splits)
next
  case (CorePat_Record flds)
  then show ?thesis using assms(1) by (simp add: arm_cond_def internal_def cg_fail_def)
qed

(* The if chain of a match: every arm is a scope. *)
lemma if_chain_ok:
  assumes "scope_ok prog (E, ds) st" and "used_le st st'"
    and "\<forall>(c, S) \<in> set armsL. (\<forall>ce. c = Some ce \<longrightarrow> expr_ok E ce CTy_U8)
           \<and> stmts_ok (mk_ctx prog rt) (E, []) S \<noteq> None \<and> (\<forall>l. stmts_wf prog l S)"
  shows "lowered_ok prog rt (E, ds) st (if_chain armsL) st' (E, ds)"
  using assms(1,3)
proof (induction armsL arbitrary: ds)
  case Nil
  then show ?case using assms(2) scope_ok_used_le[OF Nil.prems(1) assms(2)] by (simp add: lowered_ok_def)
next
  case (Cons x xs)
  obtain c S where x: "x = (c, S)" by (cases x)
  have arm: "(\<forall>ce. c = Some ce \<longrightarrow> expr_ok E ce CTy_U8) \<and> stmts_ok (mk_ctx prog rt) (E, []) S \<noteq> None \<and> (\<forall>l. stmts_wf prog l S)"
    using Cons.prems(2) x by simp
  have sc': "scope_ok prog (E, ds) st'" using scope_ok_used_le[OF Cons.prems(1) assms(2)] .
  have block: "lowered_ok prog rt (E, ds) st [MS_Block S] st' (E, ds)"
    using arm assms(2) Cons.prems(1) sc' by (auto simp: lowered_ok_def)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis using block x by simp
  next
    case (Cons y ys)
    show ?thesis
    proof (cases c)
      case None
      then show ?thesis using block x Cons by simp
    next
      case (Some ce)
      have IH: "lowered_ok prog rt (E, []) st (if_chain xs) st' (E, [])"
        using Cons.IH[OF scope_ok_inner[OF Cons.prems(1)]] Cons.prems(2) by simp
      have "stmts_ok (mk_ctx prog rt) (E, ds) [MS_If ce S (if_chain xs)] = Some (E, ds)"
        using arm IH Some by (auto simp: lowered_ok_def expr_ok_def expr_is_int_def)
      moreover have "\<And>l. stmts_wf prog l [MS_If ce S (if_chain xs)]"
        using arm IH Some by (auto simp: lowered_ok_def expr_ok_def)
      ultimately show ?thesis using x Some Cons assms(2) sc' by (simp add: lowered_ok_def)
    qed
  qed
qed

end
