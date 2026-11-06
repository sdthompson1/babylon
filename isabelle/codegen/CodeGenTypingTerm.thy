theory CodeGenTypingTerm
  imports CodeGenTypingHelpers "../core/CoreStmtTypecheckLemmas"
begin

(* ========================================================================== *)
(* The typing theorem: terms, addresses and calls                            *)
(* ========================================================================== *)

(* The three statements proved by mutual induction over the lowering
   functions (lower_term_lower_addr_lower_call.induct). Each is quantified
   over the scope and the state, so that the inductive hypotheses apply at
   the scope a subterm is lowered in. *)

section \<open>The statements\<close>

definition lt_ok :: "MProgram \<Rightarrow> CTy option \<Rightarrow> CGEnv \<Rightarrow> CoreTerm \<Rightarrow> bool" where
  "lt_ok prog rt cg tm =
    (\<forall>E ds st S e st'. lower_term cg tm st = Inr ((S, e), st') \<longrightarrow> cg_ok prog E cg
       \<longrightarrow> scope_ok prog (E, ds) st \<longrightarrow> term_fits (CG_TyEnv cg) tm
       \<longrightarrow> (\<exists>E' ds' ty. core_term_type (CG_TyEnv cg) NotGhost tm = Some ty
              \<and> lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e (res_cty ty)))"

definition la_ok :: "MProgram \<Rightarrow> CTy option \<Rightarrow> CGEnv \<Rightarrow> CoreTerm \<Rightarrow> bool" where
  "la_ok prog rt cg tm =
    (\<forall>E ds st S a st'. lower_addr cg tm st = Inr ((S, a), st') \<longrightarrow> cg_ok prog E cg
       \<longrightarrow> scope_ok prog (E, ds) st \<longrightarrow> term_fits (CG_TyEnv cg) tm
       \<longrightarrow> (\<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' a CTy_CharPtr))"

(* The Core typing facts of a call (pure or impure) that the lowering of
   the call needs: the type arguments are well-kinded, and every argument
   has the instantiated declared type of its parameter (checked in NotGhost
   mode, since no parameter is ghost). *)
definition call_args_typed :: "CoreTyEnv \<Rightarrow> FunInfo \<Rightarrow> CoreType list \<Rightarrow> CoreTerm list \<Rightarrow> bool" where
  "call_args_typed env info tys args =
    (length tys = length (FI_TyArgs info) \<and> length args = length (FI_TmArgs info)
     \<and> list_all (is_well_kinded env) tys
     \<and> (\<forall>i < length args. core_term_type env NotGhost (args ! i)
          = Some (apply_subst (fmap_of_list (zip (FI_TyArgs info) tys)) (fst (FI_TmArgs info ! i)))))"

definition lc_ok :: "MProgram \<Rightarrow> CTy option \<Rightarrow> CGEnv \<Rightarrow> string \<Rightarrow> CoreType list \<Rightarrow> CoreTerm list \<Rightarrow> bool" where
  "lc_ok prog rt cg f tys args =
    (\<forall>E ds st S res st' info. lower_call cg f tys args st = Inr ((S, res), st') \<longrightarrow> cg_ok prog E cg
       \<longrightarrow> scope_ok prog (E, ds) st
       \<longrightarrow> fmlookup (TE_Functions (CG_TyEnv cg)) f = Some info
       \<longrightarrow> call_args_typed (CG_TyEnv cg) info tys args
       \<longrightarrow> (\<forall>t \<in> set args. term_fits (CG_TyEnv cg) t) \<longrightarrow> (\<forall>ty \<in> set tys. fits (CG_TyEnv cg) ty)
       \<longrightarrow> fits (CG_TyEnv cg) (apply_subst (fmap_of_list (zip (FI_TyArgs info) tys)) (FI_ReturnType info))
       \<longrightarrow> (\<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> res_ok E' info res))"

lemma lt_okD:
  assumes "lt_ok prog rt cg tm" and "lower_term cg tm st = Inr ((S, e), st')" and "cg_ok prog E cg"
    and "scope_ok prog (E, ds) st" and "term_fits (CG_TyEnv cg) tm"
  obtains E' ds' ty where "core_term_type (CG_TyEnv cg) NotGhost tm = Some ty"
    and "lowered_ok prog rt (E, ds) st S st' (E', ds')" and "expr_ok E' e (res_cty ty)"
  using assms unfolding lt_ok_def by blast

lemma la_okD:
  assumes "la_ok prog rt cg tm" and "lower_addr cg tm st = Inr ((S, a), st')" and "cg_ok prog E cg"
    and "scope_ok prog (E, ds) st" and "term_fits (CG_TyEnv cg) tm"
  obtains E' ds' where "lowered_ok prog rt (E, ds) st S st' (E', ds')" and "expr_ok E' a CTy_CharPtr"
  using assms unfolding la_ok_def by blast


section \<open>Core typing facts\<close>

(* The type of a term is well-kinded and a runtime type; its size
   parameters are in scope. *)
lemma term_type_wk:
  assumes "cg_ok prog E cg" and "core_term_type (CG_TyEnv cg) NotGhost tm = Some ty"
  shows "is_well_kinded (CG_TyEnv cg) ty" and "is_runtime_type (CG_TyEnv cg) ty"
  using core_term_type_well_kinded_and_runtime[OF assms(2) cg_ok_wf[OF assms(1)]] by simp_all

lemma term_fits_ty:
  assumes "term_fits (CG_TyEnv cg) tm" and "core_term_type (CG_TyEnv cg) NotGhost tm = Some ty"
  shows "fits (CG_TyEnv cg) ty"
  using term_fits_type[OF assms(1)] assms(2) by auto

(* A pure call: the arguments are typed at the instantiated parameter
   types, in NotGhost mode because no parameter is ghost. *)
lemma call_typed_pure:
  assumes "core_term_type env NotGhost (CoreTm_FunctionCall f tys args) = Some rty"
    and "fmlookup (TE_Functions env) f = Some info" and "no_ghost_params info"
  shows "call_args_typed env info tys args"
    and "rty = apply_subst (fmap_of_list (zip (FI_TyArgs info) tys)) (FI_ReturnType info)"
proof -
  let ?subst = "fmap_of_list (zip (FI_TyArgs info) tys)"
  have modes: "\<And>i. i < length (FI_TmArgs info) \<Longrightarrow> (\<lambda>(_, _, gh). param_mode NotGhost gh) (FI_TmArgs info ! i) = NotGhost"
    using assms(3) unfolding no_ghost_params_def list_all_length by (auto simp: param_mode_def split_beta)
  from assms(1,2) have
    lens: "length tys = length (FI_TyArgs info)" "length args = length (FI_TmArgs info)"
    and wk: "list_all (is_well_kinded env) tys"
    and la: "list_all2 (\<lambda>tm (expectedTy, mode). core_term_type env mode tm = Some expectedTy) args
              (zip (map (\<lambda>(ty, _). apply_subst ?subst ty) (FI_TmArgs info))
                   (map (\<lambda>(_, _, gh). param_mode NotGhost gh) (FI_TmArgs info)))"
    and rty: "rty = apply_subst ?subst (FI_ReturnType info)"
    by (auto simp: Let_def split: if_splits)
  show "rty = apply_subst ?subst (FI_ReturnType info)" by (rule rty)
  show "call_args_typed env info tys args"
    unfolding call_args_typed_def
  proof (intro conjI allI impI)
    fix i assume i: "i < length args"
    have "core_term_type env ((\<lambda>(_, _, gh). param_mode NotGhost gh) (FI_TmArgs info ! i)) (args ! i)
          = Some ((\<lambda>(ty, _). apply_subst ?subst ty) (FI_TmArgs info ! i))"
      using la i lens by (auto simp: list_all2_conv_all_nth split_beta)
    then show "core_term_type env NotGhost (args ! i) = Some (apply_subst ?subst (fst (FI_TmArgs info ! i)))"
      using modes[of i] i lens by (simp add: split_beta)
  qed (use lens wk in simp_all)
qed

(* The same for an impure (statement-level) call. *)
lemma call_typed_impure:
  assumes "core_impure_call_type env NotGhost f tys args = Some rty"
    and "fmlookup (TE_Functions env) f = Some info" and "no_ghost_params info"
  shows "call_args_typed env info tys args"
    and "rty = apply_subst (fmap_of_list (zip (FI_TyArgs info) tys)) (FI_ReturnType info)"
proof -
  let ?subst = "fmap_of_list (zip (FI_TyArgs info) tys)"
  have modes: "\<And>i. i < length (FI_TmArgs info) \<Longrightarrow> (\<lambda>(_, _, gh). param_mode NotGhost gh) (FI_TmArgs info ! i) = NotGhost"
    using assms(3) unfolding no_ghost_params_def list_all_length by (auto simp: param_mode_def split_beta)
  from core_impure_call_type_fn_facts[OF assms(1)] assms(2) have
    lens: "length tys = length (FI_TyArgs info)" "length args = length (FI_TmArgs info)"
    and wk: "list_all (is_well_kinded env) tys"
    and la: "list_all2 (\<lambda>tm (expectedTy, mode). core_term_type env mode tm = Some expectedTy) args
              (zip (map (\<lambda>(ty, _). apply_subst ?subst ty) (FI_TmArgs info))
                   (map (\<lambda>(_, _, gh). param_mode NotGhost gh) (FI_TmArgs info)))"
    and rty: "rty = apply_subst ?subst (FI_ReturnType info)"
    by auto
  show "rty = apply_subst ?subst (FI_ReturnType info)" by (rule rty)
  show "call_args_typed env info tys args"
    unfolding call_args_typed_def
  proof (intro conjI allI impI)
    fix i assume i: "i < length args"
    have "core_term_type env ((\<lambda>(_, _, gh). param_mode NotGhost gh) (FI_TmArgs info ! i)) (args ! i)
          = Some ((\<lambda>(ty, _). apply_subst ?subst ty) (FI_TmArgs info ! i))"
      using la i lens by (auto simp: list_all2_conv_all_nth split_beta)
    then show "core_term_type env NotGhost (args ! i) = Some (apply_subst ?subst (fst (FI_TmArgs info ! i)))"
      using modes[of i] i lens by (simp add: split_beta)
  qed (use lens wk in simp_all)
qed

(* Record construction: every field's term has the field's type. *)
lemma record_field_typed:
  assumes "core_term_type env NotGhost (CoreTm_Record flds) = Some (CoreTy_Record fldTys)" and "(f, t) \<in> set flds"
  shows "\<exists>fty. map_of fldTys f = Some fty \<and> core_term_type env NotGhost t = Some fty"
proof -
  from assms(1) obtain tys where dist: "distinct (map fst flds)"
    and th: "those (map (\<lambda>(name, tm). core_term_type env NotGhost tm) flds) = Some tys"
    and eq: "fldTys = zip (map fst flds) tys"
    by (auto split: option.splits if_splits)
  from assms(2) obtain i where i: "i < length flds" and fi: "flds ! i = (f, t)" by (auto simp: in_set_conv_nth)
  have len: "length tys = length flds" using those_Some_nth[OF th] by simp
  have ti: "core_term_type env NotGhost t = Some (tys ! i)"
    using those_Some_nth[OF th] i fi by (auto simp: split_beta)
  have fi': "map fst flds ! i = f" using i fi by simp
  have "map_of (zip (map fst flds) tys) (map fst flds ! i) = Some (tys ! i)"
    using dist i len by (intro map_of_zip_nth) simp_all
  then have "map_of fldTys f = Some (tys ! i)" unfolding eq fi' .
  then show ?thesis using ti by blast
qed

(* Matches: the patterns are compatible and every arm has the result type. *)
lemma match_typed:
  assumes "core_term_type env NotGhost (CoreTm_Match s arms) = Some resTy"
  obtains scrutTy where "core_term_type env NotGhost s = Some scrutTy"
    and "\<forall>(p, body) \<in> set arms. pattern_compatible env p scrutTy \<and> core_term_type env NotGhost body = Some resTy"
proof -
  from assms obtain scrutTy where sc: "core_term_type env NotGhost s = Some scrutTy"
    and ne: "arms \<noteq> []"
    and pats: "list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst arms)"
    and hd: "core_term_type env NotGhost (snd (hd arms)) = Some resTy"
    and tl: "list_all (\<lambda>body. core_term_type env NotGhost body = Some resTy) (tl (map snd arms))"
    by (auto simp: Let_def split: option.splits if_splits)
  have eq: "map snd arms = snd (hd arms) # tl (map snd arms)" using ne by (cases arms) auto
  have S: "set (map snd arms) = insert (snd (hd arms)) (set (tl (map snd arms)))"
    using arg_cong[OF eq, where f = set] by (simp only: list.set)
  have bodies: "\<forall>b \<in> set (map snd arms). core_term_type env NotGhost b = Some resTy"
    unfolding S using hd tl by (auto simp: list_all_iff)
  have "\<forall>(p, body) \<in> set arms. pattern_compatible env p scrutTy \<and> core_term_type env NotGhost body = Some resTy"
  proof
    fix pb assume m: "pb \<in> set arms"
    obtain p b where pb: "pb = (p, b)" by (cases pb)
    have "p \<in> set (map fst arms)" using m unfolding pb set_map by (metis fst_conv image_eqI)
    moreover have "b \<in> set (map snd arms)" using m unfolding pb set_map by (metis snd_conv image_eqI)
    ultimately have "p \<in> set (map fst arms)" "b \<in> set (map snd arms)" by simp_all
    then have "pattern_compatible env p scrutTy" "core_term_type env NotGhost b = Some resTy"
      using pats bodies unfolding list_all_iff by blast+
    then show "case pb of (p, body) \<Rightarrow> pattern_compatible env p scrutTy \<and> core_term_type env NotGhost body = Some resTy"
      by (simp add: pb)
  qed
  then show thesis using sc that by blast
qed


section \<open>More list lemmas\<close>

(* The chained lowering of a list, with the per-element property stated
   positionally (for the arguments of a call). *)
lemma cg_mapM_chain2:
  assumes "cg_mapM f xs st = Inr (ys, st')"
    and "scope_ok prog (E, ds) st"
    and step: "\<And>x st1 y st2 E1 ds1. x \<in> set xs \<Longrightarrow> f x st1 = Inr (y, st2) \<Longrightarrow> scope_ok prog (E1, ds1) st1 \<Longrightarrow> env_le E E1
                 \<Longrightarrow> \<exists>E2 ds2. lowered_ok prog rt (E1, ds1) st1 (stmts y) st2 (E2, ds2) \<and> R E2 x y"
    and mono: "\<And>E1 E2 x y. env_le E1 E2 \<Longrightarrow> R E1 x y \<Longrightarrow> R E2 x y"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st (concat (map stmts ys)) st' (E', ds') \<and> list_all2 (R E') xs ys"
  using assms(1,2) step
proof (induction xs arbitrary: st ys E ds)
  case Nil
  then show ?case by (auto simp: cg_mapM.simps intro!: exI lowered_ok_nil)
next
  case (Cons x xs)
  from Cons.prems(1) obtain y st1 ys' where fx: "f x st = Inr (y, st1)" and rest: "cg_mapM f xs st1 = Inr (ys', st')"
    and ys: "ys = y # ys'"
    by (auto simp: cg_mapM.simps elim!: cg_bind_InrE)
  obtain E1 ds1 where l1: "lowered_ok prog rt (E, ds) st (stmts y) st1 (E1, ds1)" and r1: "R E1 x y"
    using Cons.prems(3)[OF _ fx Cons.prems(2)] by auto
  have sc1: "scope_ok prog (E1, ds1) st1" using l1 by (rule lowered_ok_scope)
  have le1: "env_le E E1" using l1 by (rule lowered_ok_env_le')
  have IH: "\<exists>E' ds'. lowered_ok prog rt (E1, ds1) st1 (concat (map stmts ys')) st' (E', ds') \<and> list_all2 (R E') xs ys'"
  proof (rule Cons.IH[OF rest sc1])
    fix x st1 y st2 E1a ds1a
    assume "x \<in> set xs" "f x st1 = Inr (y, st2)" "scope_ok prog (E1a, ds1a) st1" "env_le E1 E1a"
    then show "\<exists>E2 ds2. lowered_ok prog rt (E1a, ds1a) st1 (stmts y) st2 (E2, ds2) \<and> R E2 x y"
      using le1 by (intro Cons.prems(3)) (auto intro: env_le_trans)
  qed
  then obtain E2 ds2 where l2: "lowered_ok prog rt (E1, ds1) st1 (concat (map stmts ys')) st' (E2, ds2)"
    and r2: "list_all2 (R E2) xs ys'" by blast
  have "R E2 x y" using r1 mono[OF lowered_ok_env_le'[OF l2]] by blast
  then show ?case using lowered_ok_append[OF l1 l2] r2 by (auto simp: ys)
qed

(* A list of effect-free statements. *)
lemma lowered_ok_pure_list:
  assumes "scope_ok prog (E, ds) st" and "\<And>s. s \<in> set S \<Longrightarrow> lowered_ok prog rt (E, ds) st [s] st (E, ds)"
  shows "lowered_ok prog rt (E, ds) st S st (E, ds)"
  using assms
proof (induction S)
  case Nil
  then show ?case by (simp add: lowered_ok_nil)
next
  case (Cons s S)
  have "lowered_ok prog rt (E, ds) st ([s] @ S) st (E, ds)"
    using Cons.prems(2) by (intro lowered_ok_append[OF _ Cons.IH[OF Cons.prems(1)]]) simp_all
  then show ?case by simp
qed

(* Materialising a scalar value in a temporary (lower_addr of a non-lvalue
   scalar term). *)
lemma materialise_ok:
  assumes "lowered_ok prog rt (E, ds) st S st1 (E1, ds1)" and "expr_ok E1 e (res_cty ty)" and "scalar_ty ty = Some cty"
    and "temp_for cg hint ty st1 = Inr ((tmp, decl), st2)" and "cg_ok prog E1 cg"
    and "is_well_kinded (CG_TyEnv cg) ty" and "fits (CG_TyEnv cg) ty"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st (S @ [decl, MS_Assign tmp e]) st2 (E', ds') \<and> expr_ok E' (ME_AddrOf tmp) CTy_CharPtr"
proof -
  from temp_for_ok[OF assms(4,5) lowered_ok_scope[OF assms(1)] assms(6,7)] obtain E2 where
    d: "lowered_ok prog rt (E1, ds1) st1 [decl] st2 (E2, tmp # ds1)" and
    lk: "fmlookup E2 tmp = Some (case scalar_ty ty of Some cty \<Rightarrow> VT_Scalar cty | None \<Rightarrow> VT_Buf)" by blast
  have e2: "expr_ok E2 e cty" using expr_ok_mono[OF lowered_ok_env_le'[OF d] assms(2)] assms(3) by simp
  have a: "lowered_ok prog rt (E2, tmp # ds1) st2 [MS_Assign tmp e] st2 (E2, tmp # ds1)"
    using lowered_ok_scope[OF d] lk assms(3) e2 by (intro assign_ok[where cty' = cty]) auto
  have "lowered_ok prog rt (E, ds) st (S @ [decl, MS_Assign tmp e]) st2 (E2, tmp # ds1)"
    using lowered_ok_append[OF assms(1) lowered_ok_append[OF d a]] by simp
  then show ?thesis using lk assms(3) by (auto simp: expr_ok_def)
qed

(* The same with temp_store (the numeric cast in lower_addr). *)
lemma materialise_store_ok:
  assumes "lowered_ok prog rt (E, ds) st S st1 (E1, ds1)" and "expr_ok E1 e (res_cty ty)" and "scalar_ty ty = Some cty"
    and "temp_for cg hint ty st1 = Inr ((tmp, decl), st2)" and "cg_ok prog E1 cg"
    and "is_well_kinded (CG_TyEnv cg) ty" and "fits (CG_TyEnv cg) ty"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st (S @ [decl, temp_store cg ty tmp e]) st2 (E', ds') \<and> expr_ok E' (ME_AddrOf tmp) CTy_CharPtr"
  using materialise_ok[OF assms] assms(3) by (simp add: temp_store_def)


section \<open>The Let environment\<close>

lemma cg_ok_let:
  assumes ok: "cg_ok prog E cg" and ty1: "core_term_type (CG_TyEnv cg) NotGhost t1 = Some ty1"
    and E': "E' = fmupd n vty E" and nd: "n |\<notin>| fmdom E"
    and rep: "rep_ok E' (CG_TyEnv cg) ty1 rep"
  shows "cg_ok prog E' (cg_bind_var cg (let_env (CG_TyEnv cg) x ty1) x rep)"
proof (rule cg_okI)
  let ?cg' = "cg_bind_var cg (let_env (CG_TyEnv cg) x ty1) x rep"
  have le: "env_le E E'" using E' nd by (simp add: env_le_upd)
  have wk: "is_well_kinded (CG_TyEnv cg) ty1" and rtt: "is_runtime_type (CG_TyEnv cg) ty1"
    using term_type_wk[OF ok ty1] by simp_all
  show "tyenv_well_formed (CG_TyEnv ?cg')"
    using tyenv_well_formed_declare_var[OF cg_ok_wf[OF ok] wk, where g = NotGhost and var = x and c = "finsert x (TE_ConstLocals (CG_TyEnv cg))"] rtt
    by (simp add: cg_bind_var_def let_env_def)
  show "sizes_in E' (fset (TE_TypeVars (CG_TyEnv ?cg')))"
    using sizes_in_mono[OF le cg_ok_sizes_in[OF ok]] by (simp add: cg_bind_var_def let_env_def)
  show "\<And>y r. fmlookup (CG_Vars ?cg') y = Some r \<Longrightarrow>
          \<exists>ty. tyenv_lookup_var (CG_TyEnv ?cg') y = Some ty \<and> rep_ok E' (CG_TyEnv ?cg') ty r"
  proof -
    fix y r assume lk: "fmlookup (CG_Vars ?cg') y = Some r"
    have cong: "\<And>ty r. rep_ok E' (let_env (CG_TyEnv cg) x ty1) ty r = rep_ok E' (CG_TyEnv cg) ty r"
      by (rule rep_ok_cong_env(1)) (simp_all add: let_env_def)
    have lk': "\<And>y. tyenv_lookup_var (let_env (CG_TyEnv cg) x ty1) y
                 = (if y = x then Some ty1 else tyenv_lookup_var (CG_TyEnv cg) y)"
      by (simp add: let_env_def tyenv_lookup_var_def split: option.splits)
    have A: "CG_TyEnv ?cg' = let_env (CG_TyEnv cg) x ty1" by (simp add: cg_bind_var_def)
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
    using cg_ok_ret[OF ok] by (simp add: cg_bind_var_def let_env_def)
  show "CG_Ret ?cg' = RK_Buf \<Longrightarrow> fmlookup E' ret_param = Some (VT_Scalar CTy_CharPtr)"
    using cg_ok_ret_param[OF ok] env_le_lookup[OF le] by (simp add: cg_bind_var_def)
  show "size_fits (CG_TyEnv ?cg') 0 (\<lambda>_. 0) (TE_ReturnType (CG_TyEnv ?cg'))"
    using cg_ok_ret_fits[OF ok] fits_let_env[of "CG_TyEnv cg" x ty1, unfolded fits_def]
    by (simp add: cg_bind_var_def let_env_def)
  show "\<And>d. dt_tags_fit (CG_TyEnv ?cg') d"
    using cg_ok_tags[OF ok] by (simp add: cg_bind_var_def let_env_def dt_tags_fit_def dt_ctors_def)
  show "prog_ok prog (CG_TyEnv ?cg')"
    using cg_ok_prog[OF ok] by (simp add: cg_bind_var_def let_env_def prog_ok_def)
qed


section \<open>Typing facts per term form\<close>

lemma ty_of_Inr: "ty_of cg t st = Inr (ty, st') \<longleftrightarrow> core_term_type (CG_TyEnv cg) NotGhost t = Some ty \<and> st' = st"
  by (auto simp: ty_of_def cg_lift_def internal_def cg_fail_def cg_return_def split: option.splits)

lemma ty_of_Some: "core_term_type (CG_TyEnv cg) NotGhost t = Some ty \<Longrightarrow> ty_of cg t st = Inr (ty, st)"
  by (simp add: ty_of_Inr)

lemma lookup_var_Inr: "lookup_var cg x st = Inr (rep, st') \<longleftrightarrow> fmlookup (CG_Vars cg) x = Some rep \<and> st' = st"
  by (auto simp: lookup_var_def cg_lift_def cg_fail_def cg_return_def split: option.splits)

lemma cg_lift_Inr: "cg_lift f msg opt st = Inr (x, st') \<longleftrightarrow> opt = Some x \<and> st' = st"
  by (auto simp: cg_lift_def cg_fail_def cg_return_def split: option.splits)

lemma internal_Inr [simp]: "internal cg msg st = Inr r \<longleftrightarrow> False"
  by (simp add: internal_def cg_fail_def)

lemma get_type_for_int_fits: "get_type_for_int i = Some (s, b) \<Longrightarrow> int_fits s b i"
  by (auto simp: int_fits.simps split: if_splits)

lemma var_typed:
  "core_term_type env NotGhost (CoreTm_Var x) = Some ty \<Longrightarrow> tyenv_lookup_var env x = Some ty"
  by (auto split: option.splits if_splits)

lemma cast_typed:
  assumes "core_term_type env NotGhost (CoreTm_Cast ty t) = Some ty'"
  shows "ty' = ty \<and> (\<exists>fromTy. core_term_type env NotGhost t = Some fromTy \<and> cast_ok env fromTy ty \<and> is_runtime_type env ty)"
  using assms by (auto split: option.splits if_splits)

(* A unary operator: on a finite integer type (negation, complement) or on
   bool (not); the result has the operand's type. *)
lemma unop_typed:
  assumes "core_term_type env NotGhost (CoreTm_Unop op t) = Some ty" and "tyenv_well_formed env"
  obtains tyt where "core_term_type env NotGhost t = Some tyt" and "ty = tyt"
    and "(\<exists>s b. tyt = CoreTy_FiniteInt s b \<and> op \<noteq> CoreUnop_Not) \<or> (tyt = CoreTy_Bool \<and> op = CoreUnop_Not)"
proof -
  from assms(1) obtain tyt where tt: "core_term_type env NotGhost t = Some tyt" by (auto split: option.splits)
  have rt: "is_runtime_type env tyt" using core_term_type_notghost_runtime[OF tt assms(2)] .
  show thesis
  proof (cases op)
    case CoreUnop_Negate
    then have "is_signed_numeric_type tyt" "ty = tyt" using assms(1) tt by (auto split: if_splits)
    then show thesis using rt tt that CoreUnop_Negate by (cases tyt) auto
  next
    case CoreUnop_Complement
    then have "is_finite_integer_type tyt" "ty = tyt" using assms(1) tt by (auto split: if_splits)
    then show thesis using tt that CoreUnop_Complement by (cases tyt) auto
  next
    case CoreUnop_Not
    then show thesis using assms(1) tt that by (auto split: if_splits)
  qed
qed

(* A binary operator: both operands have one scalar type (a finite integer
   type or bool); the result is bool for a comparison or a logical
   operator and the operand type otherwise. *)
lemma binop_typed:
  assumes "core_term_type env NotGhost (CoreTm_Binop op t1 t2) = Some ty" and "tyenv_well_formed env"
  obtains tyL where "core_term_type env NotGhost t1 = Some tyL" and "core_term_type env NotGhost t2 = Some tyL"
    and "(\<exists>s b. tyL = CoreTy_FiniteInt s b) \<or> tyL = CoreTy_Bool"
    and "binop_of op = None \<longrightarrow> tyL = CoreTy_Bool \<and> ty = CoreTy_Bool"
    and "\<And>cop. binop_of op = Some cop \<Longrightarrow> (is_cmp cop \<longrightarrow> ty = CoreTy_Bool) \<and> (\<not> is_cmp cop \<longrightarrow> ty = tyL \<and> (\<exists>s b. tyL = CoreTy_FiniteInt s b))"
proof -
  from assms(1) obtain tyL tyR where tL: "core_term_type env NotGhost t1 = Some tyL"
    and tR: "core_term_type env NotGhost t2 = Some tyR" by (auto split: option.splits)
  have rtL: "is_runtime_type env tyL" using core_term_type_notghost_runtime[OF tL assms(2)] .
  have rtR: "is_runtime_type env tyR" using core_term_type_notghost_runtime[OF tR assms(2)] .
  note T = assms(1)[unfolded core_term_type.simps tL tR option.case prod.case]
  show thesis
  proof (cases op)
    case CoreBinop_And
    then show thesis using T tL tR that by (auto split: if_splits)
  next
    case CoreBinop_Or
    then show thesis using T tL tR that by (auto split: if_splits)
  next
    case CoreBinop_Implies
    then show thesis using T tL tR that by (auto split: if_splits)
  next
    case CoreBinop_Equal
    then have "tyL = tyR" "tyL = CoreTy_Bool \<or> is_numeric_type tyL" "ty = CoreTy_Bool" using T by (auto split: if_splits)
    then show thesis using tL tR rtL that CoreBinop_Equal by (cases tyL) auto
  next
    case CoreBinop_NotEqual
    then have "tyL = tyR" "tyL = CoreTy_Bool \<or> is_numeric_type tyL" "ty = CoreTy_Bool" using T by (auto split: if_splits)
    then show thesis using tL tR rtL that CoreBinop_NotEqual by (cases tyL) auto
  next
    case CoreBinop_Less
    then have "tyL = tyR" "is_numeric_type tyL" "ty = CoreTy_Bool" using T by (auto split: if_splits)
    then show thesis using tL tR rtL that CoreBinop_Less by (cases tyL) auto
  next
    case CoreBinop_LessEqual
    then have "tyL = tyR" "is_numeric_type tyL" "ty = CoreTy_Bool" using T by (auto split: if_splits)
    then show thesis using tL tR rtL that CoreBinop_LessEqual by (cases tyL) auto
  next
    case CoreBinop_Greater
    then have "tyL = tyR" "is_numeric_type tyL" "ty = CoreTy_Bool" using T by (auto split: if_splits)
    then show thesis using tL tR rtL that CoreBinop_Greater by (cases tyL) auto
  next
    case CoreBinop_GreaterEqual
    then have "tyL = tyR" "is_numeric_type tyL" "ty = CoreTy_Bool" using T by (auto split: if_splits)
    then show thesis using tL tR rtL that CoreBinop_GreaterEqual by (cases tyL) auto
  next
    case CoreBinop_Add
    then have "tyL = tyR" "is_numeric_type tyL" "ty = tyL" using T by (auto split: if_splits)
    then show thesis using tL tR rtL that CoreBinop_Add by (cases tyL) auto
  next
    case CoreBinop_Subtract
    then have "tyL = tyR" "is_numeric_type tyL" "ty = tyL" using T by (auto split: if_splits)
    then show thesis using tL tR rtL that CoreBinop_Subtract by (cases tyL) auto
  next
    case CoreBinop_Multiply
    then have "tyL = tyR" "is_numeric_type tyL" "ty = tyL" using T by (auto split: if_splits)
    then show thesis using tL tR rtL that CoreBinop_Multiply by (cases tyL) auto
  next
    case CoreBinop_Divide
    then have "tyL = tyR" "is_numeric_type tyL" "ty = tyL" using T by (auto split: if_splits)
    then show thesis using tL tR rtL that CoreBinop_Divide by (cases tyL) auto
  next
    case CoreBinop_Modulo
    then have "tyL = tyR" "is_integer_type tyL" "ty = tyL" using T by (auto split: if_splits)
    then show thesis using tL tR rtL that CoreBinop_Modulo by (cases tyL) auto
  next
    case CoreBinop_BitAnd
    then have "tyL = tyR" "is_finite_integer_type tyL" "ty = tyL" using T by (auto split: if_splits)
    then show thesis using tL tR that CoreBinop_BitAnd by (cases tyL) auto
  next
    case CoreBinop_BitOr
    then have "tyL = tyR" "is_finite_integer_type tyL" "ty = tyL" using T by (auto split: if_splits)
    then show thesis using tL tR that CoreBinop_BitOr by (cases tyL) auto
  next
    case CoreBinop_BitXor
    then have "tyL = tyR" "is_finite_integer_type tyL" "ty = tyL" using T by (auto split: if_splits)
    then show thesis using tL tR that CoreBinop_BitXor by (cases tyL) auto
  next
    case CoreBinop_ShiftLeft
    then have "tyL = tyR" "is_finite_integer_type tyL" "ty = tyL" using T by (auto split: if_splits)
    then show thesis using tL tR that CoreBinop_ShiftLeft by (cases tyL) auto
  next
    case CoreBinop_ShiftRight
    then have "tyL = tyR" "is_finite_integer_type tyL" "ty = tyL" using T by (auto split: if_splits)
    then show thesis using tL tR that CoreBinop_ShiftRight by (cases tyL) auto
  qed
qed

lemma let_typed:
  assumes "core_term_type env NotGhost (CoreTm_Let x t1 t2) = Some ty"
  obtains ty1 where "core_term_type env NotGhost t1 = Some ty1" and "core_term_type (let_env env x ty1) NotGhost t2 = Some ty"
  using assms by (auto simp: let_env_def Let_def split: option.splits intro: that)

lemma variant_ctor_typed:
  assumes "core_term_type env NotGhost (CoreTm_VariantCtor c tys t) = Some ty"
  obtains dtName tyvars payloadTy where "ty = CoreTy_Datatype dtName tys"
    and "fmlookup (TE_DataCtors env) c = Some (dtName, tyvars, payloadTy)"
    and "core_term_type env NotGhost t = Some (apply_subst (fmap_of_list (zip tyvars tys)) payloadTy)"
  using assms by (auto simp: Let_def split: option.splits if_splits intro: that)

lemma record_proj_typed:
  assumes "core_term_type env NotGhost (CoreTm_RecordProj t f) = Some ty"
  obtains fldTys where "core_term_type env NotGhost t = Some (CoreTy_Record fldTys)" and "map_of fldTys f = Some ty"
  using assms by (auto split: option.splits CoreType.splits intro: that)

lemma variant_proj_typed:
  assumes "core_term_type env NotGhost (CoreTm_VariantProj t c) = Some ty"
  obtains dtName args tyvars payloadTy where "core_term_type env NotGhost t = Some (CoreTy_Datatype dtName args)"
    and "fmlookup (TE_DataCtors env) c = Some (dtName, tyvars, payloadTy)"
    and "ty = apply_subst (fmap_of_list (zip tyvars args)) payloadTy"
  using assms by (auto split: option.splits CoreType.splits if_splits intro: that)

lemma array_proj_typed:
  assumes "core_term_type env NotGhost (CoreTm_ArrayProj t idxs) = Some ty"
  obtains dims where "core_term_type env NotGhost t = Some (CoreTy_Array ty dims)"
    and "length idxs = length dims"
    and "\<forall>i \<in> set idxs. core_term_type env NotGhost i = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
  using assms by (auto simp: list_all_iff split: option.splits CoreType.splits if_splits intro: that)

lemma sizeof_typed:
  assumes "core_term_type env NotGhost (CoreTm_Sizeof t) = Some ty"
  obtains elemTy dims where "core_term_type env NotGhost t = Some (CoreTy_Array elemTy dims)" and "ty = sizeof_type dims"
  using assms by (auto split: option.splits CoreType.splits if_splits intro: that)

lemma default_typed:
  "core_term_type env NotGhost (CoreTm_Default ty) = Some ty' \<Longrightarrow> ty' = ty \<and> is_well_kinded env ty \<and> is_runtime_type env ty"
  by (auto split: if_splits)

lemma lit_array_typed:
  assumes "core_term_type env NotGhost (CoreTm_LitArray elemTy tms) = Some ty"
  shows "ty = CoreTy_Array elemTy [CoreDim_Fixed (int (length tms))]"
    and "\<forall>t \<in> set tms. core_term_type env NotGhost t = Some elemTy"
    and "length tms < u64_max"
  using assms by (auto simp: list_all_iff int_in_range.simps int_range.simps u64_max_def split: if_splits)


section \<open>The simple terms\<close>

lemma lt_LitBool: "lt_ok prog rt cg (CoreTm_LitBool b)"
  unfolding lt_ok_def
proof (intro allI impI)
  fix E ds st S e st'
  assume "lower_term cg (CoreTm_LitBool b) st = Inr ((S, e), st')" "cg_ok prog E cg" "scope_ok prog (E, ds) st"
  then show "\<exists>E' ds' ty. core_term_type (CG_TyEnv cg) NotGhost (CoreTm_LitBool b) = Some ty
          \<and> lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e (res_cty ty)"
    by (auto simp: lower_term.simps cg_return_def expr_ok_def intro!: exI[where x = E] exI[where x = ds] lowered_ok_nil)
qed

lemma lt_LitInt: "lt_ok prog rt cg (CoreTm_LitInt i)"
  unfolding lt_ok_def
proof (intro allI impI)
  fix E ds st S e st'
  assume l: "lower_term cg (CoreTm_LitInt i) st = Inr ((S, e), st')" and sc: "scope_ok prog (E, ds) st"
  from l obtain s b where g: "get_type_for_int i = Some (s, b)" and S: "S = []" and e: "e = ME_Int s b i" and st': "st' = st"
    by (auto simp: lower_term.simps cg_return_def split: option.splits)
  have "core_term_type (CG_TyEnv cg) NotGhost (CoreTm_LitInt i) = Some (CoreTy_FiniteInt s b)" using g by simp
  moreover have "expr_ok E (ME_Int s b i) (res_cty (CoreTy_FiniteInt s b))"
    using get_type_for_int_fits[OF g] by (simp add: expr_ok_def)
  ultimately show "\<exists>E' ds' ty. core_term_type (CG_TyEnv cg) NotGhost (CoreTm_LitInt i) = Some ty
          \<and> lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e (res_cty ty)"
    unfolding S e st' using lowered_ok_nil[OF sc] by blast
qed

lemma lt_Var: "lt_ok prog rt cg (CoreTm_Var x)"
  unfolding lt_ok_def
proof (intro allI impI)
  fix E ds st S e st'
  assume l: "lower_term cg (CoreTm_Var x) st = Inr ((S, e), st')" and ok: "cg_ok prog E cg" and sc: "scope_ok prog (E, ds) st"
  from l obtain ty rep where ty: "core_term_type (CG_TyEnv cg) NotGhost (CoreTm_Var x) = Some ty"
    and rep: "fmlookup (CG_Vars cg) x = Some rep" and rr: "read_rep cg rep ty st = Inr ((S, e), st')"
    by (auto simp: lower_term.simps ty_of_Inr lookup_var_Inr elim!: cg_bind_InrE)
  obtain ty' where "tyenv_lookup_var (CG_TyEnv cg) x = Some ty'" "rep_ok E (CG_TyEnv cg) ty' rep"
    using cg_ok_var[OF ok rep] by blast
  then have ro: "rep_ok E (CG_TyEnv cg) ty rep" using var_typed[OF ty] by simp
  show "\<exists>E' ds' ty. core_term_type (CG_TyEnv cg) NotGhost (CoreTm_Var x) = Some ty
          \<and> lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e (res_cty ty)"
    using read_rep_ok'[OF rr ok sc ro] ty by blast
qed

lemma lt_Cast:
  assumes IH: "lt_ok prog rt cg t"
  shows "lt_ok prog rt cg (CoreTm_Cast ty t)"
  unfolding lt_ok_def
proof (intro allI impI)
  fix E ds st S e st'
  assume l: "lower_term cg (CoreTm_Cast ty t) st = Inr ((S, e), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and tf: "term_fits (CG_TyEnv cg) (CoreTm_Cast ty t)"
  from l obtain fromTy S1 e1 st1 S2 e2 st2 where ft: "core_term_type (CG_TyEnv cg) NotGhost t = Some fromTy"
    and l1: "lower_term cg t st = Inr ((S1, e1), st1)" and cr: "cast_result cg fromTy ty e1 st1 = Inr ((S2, e2), st2)"
    and S: "S = S1 @ S2" and e: "e = e2" and st': "st' = st2"
    by (auto simp: lower_term.simps ty_of_Inr cg_return_def elim!: cg_bind_InrE)
  obtain E1 ds1 ty1 where ty1: "core_term_type (CG_TyEnv cg) NotGhost t = Some ty1"
    and lo1: "lowered_ok prog rt (E, ds) st S1 st1 (E1, ds1)" and e1: "expr_ok E1 e1 (res_cty ty1)"
    using lt_okD[OF IH l1 ok sc term_fits_Cast[OF tf]] by blast
  have ty1': "ty1 = fromTy" using ty1 ft by simp
  from term_fits_type[OF tf] obtain ty' where tyc: "core_term_type (CG_TyEnv cg) NotGhost (CoreTm_Cast ty t) = Some ty'"
    and fc: "fits (CG_TyEnv cg) ty'" by blast
  from cast_typed[OF tyc] have ty': "ty' = ty" and co: "cast_ok (CG_TyEnv cg) fromTy ty" and rtt: "is_runtime_type (CG_TyEnv cg) ty"
    using ft by auto
  have ok1: "cg_ok prog E1 cg" using cg_ok_mono[OF lowered_ok_env_le'[OF lo1] ok] .
  obtain E2 ds2 where lo2: "lowered_ok prog rt (E1, ds1) st1 S2 st2 (E2, ds2)" and e2: "expr_ok E2 e2 (res_cty ty)"
    using cast_result_ok[OF cr ok1 lowered_ok_scope[OF lo1] e1[unfolded ty1'] co term_type_wk(2)[OF ok ft] rtt
                            term_type_wk(1)[OF ok ft] term_type_wk(1)[OF ok tyc, unfolded ty'] fc[unfolded ty']] by blast
  show "\<exists>E' ds' ty'. core_term_type (CG_TyEnv cg) NotGhost (CoreTm_Cast ty t) = Some ty'
          \<and> lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e (res_cty ty')"
    unfolding S e st' using tyc ty' lowered_ok_append[OF lo1 lo2] e2 by blast
qed

lemma lt_Unop:
  assumes IH: "lt_ok prog rt cg t"
  shows "lt_ok prog rt cg (CoreTm_Unop op t)"
  unfolding lt_ok_def
proof (intro allI impI)
  fix E ds st S e st'
  assume l: "lower_term cg (CoreTm_Unop op t) st = Inr ((S, e), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and tf: "term_fits (CG_TyEnv cg) (CoreTm_Unop op t)"
  from l obtain S1 e1 where l1: "lower_term cg t st = Inr ((S1, e1), st')" and S: "S = S1" and e: "e = ME_Unop (unop_of op) e1"
    by (auto simp: lower_term.simps cg_return_def elim!: cg_bind_InrE)
  from term_fits_type[OF tf] obtain ty where tyu: "core_term_type (CG_TyEnv cg) NotGhost (CoreTm_Unop op t) = Some ty" by blast
  obtain E1 ds1 ty1 where ty1: "core_term_type (CG_TyEnv cg) NotGhost t = Some ty1"
    and lo1: "lowered_ok prog rt (E, ds) st S1 st' (E1, ds1)" and e1: "expr_ok E1 e1 (res_cty ty1)"
    using lt_okD[OF IH l1 ok sc term_fits_Unop[OF tf]] by blast
  obtain tyt where tt: "core_term_type (CG_TyEnv cg) NotGhost t = Some tyt" and tyeq: "ty = tyt"
    and shape: "(\<exists>s b. tyt = CoreTy_FiniteInt s b \<and> op \<noteq> CoreUnop_Not) \<or> (tyt = CoreTy_Bool \<and> op = CoreUnop_Not)"
    using unop_typed[OF tyu cg_ok_wf[OF ok]] by blast
  have "expr_ok E1 (ME_Unop (unop_of op) e1) (res_cty ty)"
    using shape e1 tt ty1 tyeq by (cases op) (auto simp: expr_ok_def)
  then show "\<exists>E' ds' ty. core_term_type (CG_TyEnv cg) NotGhost (CoreTm_Unop op t) = Some ty
          \<and> lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e (res_cty ty)"
    unfolding S e using tyu lo1 by blast
qed

lemma lt_Binop:
  assumes IH1: "lt_ok prog rt cg t1" and IH2: "lt_ok prog rt cg t2"
  shows "lt_ok prog rt cg (CoreTm_Binop op t1 t2)"
  unfolding lt_ok_def
proof (intro allI impI)
  fix E ds st S e st'
  assume l: "lower_term cg (CoreTm_Binop op t1 t2) st = Inr ((S, e), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and tf: "term_fits (CG_TyEnv cg) (CoreTm_Binop op t1 t2)"
  from term_fits_type[OF tf] obtain ty where tyb: "core_term_type (CG_TyEnv cg) NotGhost (CoreTm_Binop op t1 t2) = Some ty" by blast
  obtain tyL where tL: "core_term_type (CG_TyEnv cg) NotGhost t1 = Some tyL" and tR: "core_term_type (CG_TyEnv cg) NotGhost t2 = Some tyL"
    and shape: "(\<exists>s b. tyL = CoreTy_FiniteInt s b) \<or> tyL = CoreTy_Bool"
    and none: "binop_of op = None \<longrightarrow> tyL = CoreTy_Bool \<and> ty = CoreTy_Bool"
    and some: "\<And>cop. binop_of op = Some cop \<Longrightarrow> (is_cmp cop \<longrightarrow> ty = CoreTy_Bool) \<and> (\<not> is_cmp cop \<longrightarrow> ty = tyL \<and> (\<exists>s b. tyL = CoreTy_FiniteInt s b))"
    using binop_typed[OF tyb cg_ok_wf[OF ok]] by blast
  note tf12 = term_fits_Binop[OF tf]
  show "\<exists>E' ds' ty. core_term_type (CG_TyEnv cg) NotGhost (CoreTm_Binop op t1 t2) = Some ty
          \<and> lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e (res_cty ty)"
  proof (cases "binop_of op")
    case (Some cop)
    from l Some obtain S1 e1 st1 S2 e2 where l1: "lower_term cg t1 st = Inr ((S1, e1), st1)"
      and l2: "lower_term cg t2 st1 = Inr ((S2, e2), st')" and S: "S = S1 @ S2" and e: "e = ME_Binop cop e1 e2"
      by (auto simp: lower_term.simps cg_return_def elim!: cg_bind_InrE)
    obtain E1 ds1 ty1 where ty1: "core_term_type (CG_TyEnv cg) NotGhost t1 = Some ty1"
      and lo1: "lowered_ok prog rt (E, ds) st S1 st1 (E1, ds1)" and e1: "expr_ok E1 e1 (res_cty ty1)"
      using lt_okD[OF IH1 l1 ok sc] tf12 by blast
    obtain E2 ds2 ty2 where ty2: "core_term_type (CG_TyEnv cg) NotGhost t2 = Some ty2"
      and lo2: "lowered_ok prog rt (E1, ds1) st1 S2 st' (E2, ds2)" and e2: "expr_ok E2 e2 (res_cty ty2)"
      using lt_okD[OF IH2 l2 cg_ok_mono[OF lowered_ok_env_le'[OF lo1] ok] lowered_ok_scope[OF lo1]] tf12 by blast
    have e1': "expr_ok E2 e1 (res_cty tyL)" using expr_ok_mono[OF lowered_ok_env_le'[OF lo2] e1] ty1 tL by simp
    have e2': "expr_ok E2 e2 (res_cty tyL)" using e2 ty2 tR by simp
    have "expr_ok E2 (ME_Binop cop e1 e2) (res_cty ty)"
      using some[OF Some] shape e1' e2' by (auto simp: expr_ok_def)
    then show ?thesis unfolding S e using tyb lowered_ok_append[OF lo1 lo2] by blast
  next
    case None
    from l None obtain S1 e1 st1 tmp st2 S2 e2 where l1: "lower_term cg t1 st = Inr ((S1, e1), st1)"
      and fr: "fresh_name (CG_Fun cg) ''sc'' st1 = Inr (tmp, st2)"
      and l2: "lower_term cg t2 st2 = Inr ((S2, e2), st')"
      and S: "S = S1 @ [MS_DeclScalar tmp CTy_U8]
                  @ (if op = CoreBinop_And then [MS_Assign tmp e1, MS_If (ME_Var tmp) (S2 @ [MS_Assign tmp e2]) []]
                     else if op = CoreBinop_Or then [MS_Assign tmp e1, MS_If (ME_Var tmp) [] (S2 @ [MS_Assign tmp e2])]
                     else [MS_Assign tmp (ME_Unop CU_Not e1), MS_If (ME_Var tmp) [] (S2 @ [MS_Assign tmp e2])])"
      and e: "e = ME_Var tmp"
      by (auto simp: lower_term.simps cg_return_def elim!: cg_bind_InrE)
    have tyL: "tyL = CoreTy_Bool" and ty: "ty = CoreTy_Bool" using none None by simp_all
    obtain E1 ds1 ty1 where ty1: "core_term_type (CG_TyEnv cg) NotGhost t1 = Some ty1"
      and lo1: "lowered_ok prog rt (E, ds) st S1 st1 (E1, ds1)" and e1: "expr_ok E1 e1 (res_cty ty1)"
      using lt_okD[OF IH1 l1 ok sc] tf12 by blast
    let ?E2 = "fmupd tmp (VT_Scalar CTy_U8) E1"
    have d: "lowered_ok prog rt (E1, ds1) st1 [MS_DeclScalar tmp CTy_U8] st2 (?E2, tmp # ds1)"
      by (rule fresh_scalar_ok[OF lowered_ok_scope[OF lo1] fr])
    have e1': "expr_ok ?E2 e1 CTy_U8" using expr_ok_mono[OF lowered_ok_env_le'[OF d] e1] ty1 tL tyL by simp
    have sc2: "scope_ok prog (?E2, tmp # ds1) st2" by (rule lowered_ok_scope[OF d])
    have ok2: "cg_ok prog ?E2 cg" using cg_ok_mono[OF lowered_ok_env_le'[OF lowered_ok_append[OF lo1 d]] ok] .
    obtain E3 ds3 ty2 where ty2: "core_term_type (CG_TyEnv cg) NotGhost t2 = Some ty2"
      and lo2: "lowered_ok prog rt (?E2, []) st2 S2 st' (E3, ds3)" and e2: "expr_ok E3 e2 (res_cty ty2)"
      using lt_okD[OF IH2 l2 ok2 scope_ok_inner[OF sc2]] tf12 by blast
    have e2': "expr_ok E3 e2 CTy_U8" using e2 ty2 tR tyL by simp
    have tmp3: "fmlookup E3 tmp = Some (VT_Scalar CTy_U8)" using env_le_lookup[OF lowered_ok_env_le'[OF lo2]] by simp
    have inner: "lowered_ok prog rt (?E2, []) st2 (S2 @ [MS_Assign tmp e2]) st' (E3, ds3)"
      using lowered_ok_append[OF lo2 assign_ok[OF lowered_ok_scope[OF lo2] tmp3 e2' ty_compat_refl]] by simp
    have asg: "lowered_ok prog rt (?E2, tmp # ds1) st2 [MS_Assign tmp e1] st2 (?E2, tmp # ds1)"
      using sc2 e1' by (intro assign_ok[where cty' = CTy_U8]) auto
    have asgn: "lowered_ok prog rt (?E2, tmp # ds1) st2 [MS_Assign tmp (ME_Unop CU_Not e1)] st2 (?E2, tmp # ds1)"
      using sc2 e1' by (intro assign_ok[where cty' = CTy_U8]) (auto simp: expr_ok_def)
    have tmpv: "expr_ok ?E2 (ME_Var tmp) CTy_U8" by (simp add: expr_ok_def)
    have ifA: "lowered_ok prog rt (?E2, tmp # ds1) st2 [MS_If (ME_Var tmp) (S2 @ [MS_Assign tmp e2]) []] st' (?E2, tmp # ds1)"
      using sc2 tmpv inner lowered_ok_nil[OF scope_ok_inner[OF scope_ok_used_le[OF sc2 lowered_ok_used_le[OF inner]]]]
      by (intro if_ok[where s = Unsigned and b = IntBits_8]) auto
    have ifB: "lowered_ok prog rt (?E2, tmp # ds1) st2 [MS_If (ME_Var tmp) [] (S2 @ [MS_Assign tmp e2])] st' (?E2, tmp # ds1)"
      using sc2 tmpv inner lowered_ok_nil[OF scope_ok_inner[OF sc2]]
      by (intro if_ok[where s = Unsigned and b = IntBits_8]) auto
    have tail: "lowered_ok prog rt (?E2, tmp # ds1) st2
        (if op = CoreBinop_And then [MS_Assign tmp e1, MS_If (ME_Var tmp) (S2 @ [MS_Assign tmp e2]) []]
         else if op = CoreBinop_Or then [MS_Assign tmp e1, MS_If (ME_Var tmp) [] (S2 @ [MS_Assign tmp e2])]
         else [MS_Assign tmp (ME_Unop CU_Not e1), MS_If (ME_Var tmp) [] (S2 @ [MS_Assign tmp e2])])
        st' (?E2, tmp # ds1)"
      using lowered_ok_append[OF asg ifA] lowered_ok_append[OF asg ifB] lowered_ok_append[OF asgn ifB] by auto
    have res: "expr_ok ?E2 (ME_Var tmp) (res_cty ty)" using ty by (simp add: expr_ok_def)
    show ?thesis unfolding S e
      using tyb lowered_ok_append[OF lowered_ok_append[OF lo1 d] tail] res by (intro exI conjI) (assumption | simp)+
  qed
qed

end
