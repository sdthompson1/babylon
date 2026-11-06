theory CodeGenTypingTerm
  imports CodeGenTypingHelpers "../core/CoreStmtTypecheckLemmas"
begin

declare int_fits.simps [simp del]

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
       \<longrightarrow> is_well_kinded (CG_TyEnv cg) (apply_subst (fmap_of_list (zip (FI_TyArgs info) tys)) (FI_ReturnType info))
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

lemma lc_okD:
  assumes "lc_ok prog rt cg f tys args" and "lower_call cg f tys args st = Inr ((S, res), st')" and "cg_ok prog E cg"
    and "scope_ok prog (E, ds) st" and "fmlookup (TE_Functions (CG_TyEnv cg)) f = Some info"
    and "call_args_typed (CG_TyEnv cg) info tys args"
    and "\<forall>t \<in> set args. term_fits (CG_TyEnv cg) t" and "\<forall>ty \<in> set tys. fits (CG_TyEnv cg) ty"
    and "is_well_kinded (CG_TyEnv cg) (apply_subst (fmap_of_list (zip (FI_TyArgs info) tys)) (FI_ReturnType info))"
    and "fits (CG_TyEnv cg) (apply_subst (fmap_of_list (zip (FI_TyArgs info) tys)) (FI_ReturnType info))"
  obtains E' ds' where "lowered_ok prog rt (E, ds) st S st' (E', ds')" and "res_ok E' info res"
  using assms unfolding lc_ok_def by blast


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
  assumes IH: "\<And>x st st'. ty_of cg t st = Inr (x, st') \<Longrightarrow> lt_ok prog rt cg t"
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
    using lt_okD[OF IH[OF ty_of_Some[OF ft]] l1 ok sc term_fits_Cast[OF tf]] by blast
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
  assumes IH1n: "binop_of op = None \<Longrightarrow> lt_ok prog rt cg t1"
    and IH2n: "\<And>x st st' xa y xb sta st'a. binop_of op = None \<Longrightarrow> lower_term cg t1 st = Inr (x, st') \<Longrightarrow> (xa, y) = x
                 \<Longrightarrow> fresh_name (CG_Fun cg) ''sc'' sta = Inr (xb, st'a) \<Longrightarrow> lt_ok prog rt cg t2"
    and IH1s: "\<And>x2. binop_of op = Some x2 \<Longrightarrow> lt_ok prog rt cg t1"
    and IH2s: "\<And>x2 x st st' xa y. binop_of op = Some x2 \<Longrightarrow> lower_term cg t1 st = Inr (x, st') \<Longrightarrow> (xa, y) = x
                 \<Longrightarrow> lt_ok prog rt cg t2"
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
      using lt_okD[OF IH1s[OF Some] l1 ok sc] tf12 by blast
    obtain E2 ds2 ty2 where ty2: "core_term_type (CG_TyEnv cg) NotGhost t2 = Some ty2"
      and lo2: "lowered_ok prog rt (E1, ds1) st1 S2 st' (E2, ds2)" and e2: "expr_ok E2 e2 (res_cty ty2)"
      using lt_okD[OF IH2s[OF Some l1 refl] l2 cg_ok_mono[OF lowered_ok_env_le'[OF lo1] ok] lowered_ok_scope[OF lo1]] tf12 by blast
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
      using lt_okD[OF IH1n[OF None] l1 ok sc] tf12 by blast
    note IH2 = IH2n[OF None l1 refl fr]
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


section \<open>Let, Default, constructors, projections, sizeof\<close>

lemma lt_Let:
  assumes IH1: "\<And>xa st st'. ty_of cg t1 st = Inr (xa, st') \<Longrightarrow> lt_ok prog rt cg t1"
    and IH2: "\<And>xa st st' xb sta st'a xc y xba stb st'b xbb xbc xaa ya.
        ty_of cg t1 st = Inr (xa, st') \<Longrightarrow> lower_term cg t1 sta = Inr (xb, st'a) \<Longrightarrow> (xc, y) = xb \<Longrightarrow>
        local_name (CG_Fun cg) x stb = Inr (xba, st'b) \<Longrightarrow> xbb = let_env (CG_TyEnv cg) x xa \<Longrightarrow>
        xbc = (case scalar_ty xa of
                 None \<Rightarrow> ([MS_DeclScalar xba CTy_CharPtr, MS_Assign xba y], VR_Ptr xba)
               | Some cty \<Rightarrow> ([MS_DeclScalar xba cty, MS_Assign xba y], VR_Scalar xba cty)) \<Longrightarrow>
        (xaa, ya) = xbc \<Longrightarrow> lt_ok prog rt (cg_bind_var cg xbb x ya) t2"
  shows "lt_ok prog rt cg (CoreTm_Let x t1 t2)"
  unfolding lt_ok_def
proof (intro allI impI)
  fix E ds st S e st'
  assume l: "lower_term cg (CoreTm_Let x t1 t2) st = Inr ((S, e), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and tf: "term_fits (CG_TyEnv cg) (CoreTm_Let x t1 t2)"
  let ?decl = "\<lambda>ty1 n e1. (case scalar_ty ty1 of
                 None \<Rightarrow> ([MS_DeclScalar n CTy_CharPtr, MS_Assign n e1], VR_Ptr n)
               | Some cty \<Rightarrow> ([MS_DeclScalar n cty, MS_Assign n e1], VR_Scalar n cty))"
  from l obtain ty1 S1 e1 st1 n st2 where
    ty1: "core_term_type (CG_TyEnv cg) NotGhost t1 = Some ty1"
    and l1: "lower_term cg t1 st = Inr ((S1, e1), st1)"
    and ln: "local_name (CG_Fun cg) x st1 = Inr (n, st2)"
    and rest: "(case ?decl ty1 n e1 of (decl, rep) \<Rightarrow>
                 do { (S2, e2) \<leftarrow> lower_term (cg_bind_var cg (let_env (CG_TyEnv cg) x ty1) x rep) t2;
                      cg_return (S1 @ decl @ S2, e2) }) st2 = Inr ((S, e), st')"
    by (auto simp: lower_term.simps ty_of_Inr Let_def elim!: cg_bind_InrE)
  obtain decl rep where dr: "?decl ty1 n e1 = (decl, rep)" by (cases "?decl ty1 n e1")
  from rest obtain S2 e2 where
    l2: "lower_term (cg_bind_var cg (let_env (CG_TyEnv cg) x ty1) x rep) t2 st2 = Inr ((S2, e2), st')"
    and S: "S = S1 @ decl @ S2" and e: "e = e2"
    unfolding dr by (auto simp: cg_return_def elim!: cg_bind_InrE)
  let ?cg' = "cg_bind_var cg (let_env (CG_TyEnv cg) x ty1) x rep"
  note tf12 = term_fits_Let[OF tf ty1]
  obtain E1 ds1 ty1' where ty1': "core_term_type (CG_TyEnv cg) NotGhost t1 = Some ty1'"
    and lo1: "lowered_ok prog rt (E, ds) st S1 st1 (E1, ds1)" and e1: "expr_ok E1 e1 (res_cty ty1')"
    using lt_okD[OF IH1[OF ty_of_Some[OF ty1]] l1 ok sc] tf12 by blast
  have e1': "expr_ok E1 e1 (res_cty ty1)" using e1 ty1 ty1' by simp
  have ok1: "cg_ok prog E1 cg" using cg_ok_mono[OF lowered_ok_env_le'[OF lo1] ok] .
  from term_fits_type[OF tf] obtain ty where tyl: "core_term_type (CG_TyEnv cg) NotGhost (CoreTm_Let x t1 t2) = Some ty" by blast
  have ty2: "core_term_type (let_env (CG_TyEnv cg) x ty1) NotGhost t2 = Some ty"
    using let_typed[OF tyl] ty1 by (auto simp: let_env_def)
  note nd = local_decl_facts[OF lowered_ok_scope[OF lo1] ln]
  (* the declaration and the extended environment *)
  have "\<exists>E' vty. lowered_ok prog rt (E1, ds1) st1 decl st2 (E', n # ds1)
          \<and> E' = fmupd n vty E1 \<and> rep_ok E' (CG_TyEnv cg) ty1 rep"
  proof (cases "scalar_ty ty1")
    case (Some cty)
    then have decl: "decl = [MS_DeclScalar n cty, MS_Assign n e1]" and rep: "rep = VR_Scalar n cty" using dr by simp_all
    let ?E' = "fmupd n (VT_Scalar cty) E1"
    have d: "lowered_ok prog rt (E1, ds1) st1 [MS_DeclScalar n cty] st2 (?E', n # ds1)"
      by (rule local_scalar_ok[OF lowered_ok_scope[OF lo1] ln])
    have a: "lowered_ok prog rt (?E', n # ds1) st2 [MS_Assign n e1] st2 (?E', n # ds1)"
      using lowered_ok_scope[OF d] expr_ok_mono[OF lowered_ok_env_le'[OF d] e1'] Some
      by (intro assign_ok[where cty' = cty]) auto
    show ?thesis unfolding decl rep using lowered_ok_append[OF d a] Some by (intro exI[where x = "?E'"]) auto
  next
    case None
    then have decl: "decl = [MS_DeclScalar n CTy_CharPtr, MS_Assign n e1]" and rep: "rep = VR_Ptr n" using dr by simp_all
    let ?E' = "fmupd n (VT_Scalar CTy_CharPtr) E1"
    have d: "lowered_ok prog rt (E1, ds1) st1 [MS_DeclScalar n CTy_CharPtr] st2 (?E', n # ds1)"
      by (rule local_scalar_ok[OF lowered_ok_scope[OF lo1] ln])
    have a: "lowered_ok prog rt (?E', n # ds1) st2 [MS_Assign n e1] st2 (?E', n # ds1)"
      using lowered_ok_scope[OF d] expr_ok_mono[OF lowered_ok_env_le'[OF d] e1'] None
      by (intro assign_ok[where cty' = CTy_CharPtr]) auto
    show ?thesis unfolding decl rep using lowered_ok_append[OF d a] None by (intro exI[where x = "?E'"]) auto
  qed
  then obtain E' vty where lod: "lowered_ok prog rt (E1, ds1) st1 decl st2 (E', n # ds1)"
    and E': "E' = fmupd n vty E1" and ro: "rep_ok E' (CG_TyEnv cg) ty1 rep" by blast
  have ok': "cg_ok prog E' ?cg'" by (rule cg_ok_let[OF ok1 ty1 E' _ ro]) (use nd in simp)
  have IH2': "lt_ok prog rt ?cg' t2"
    by (rule IH2[OF ty_of_Some[OF ty1] l1 refl ln refl refl dr[symmetric]])
  have tf2: "term_fits (CG_TyEnv ?cg') t2" using tf12 by (simp add: cg_bind_var_def)
  obtain E2 ds2 ty2' where ty2': "core_term_type (CG_TyEnv ?cg') NotGhost t2 = Some ty2'"
    and lo2: "lowered_ok prog rt (E', n # ds1) st2 S2 st' (E2, ds2)" and e2: "expr_ok E2 e2 (res_cty ty2')"
    using lt_okD[OF IH2' l2 ok' lowered_ok_scope[OF lod] tf2] by blast
  have "ty2' = ty" using ty2' ty2 by (simp add: cg_bind_var_def)
  moreover have "lowered_ok prog rt (E, ds) st S st' (E2, ds2)"
    unfolding S using lowered_ok_append[OF lowered_ok_append[OF lo1 lod] lo2] by simp
  ultimately show "\<exists>E' ds' ty. core_term_type (CG_TyEnv cg) NotGhost (CoreTm_Let x t1 t2) = Some ty
          \<and> lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e (res_cty ty)"
    unfolding e using tyl e2 by blast
qed

lemma lt_Ghost: "lt_ok prog rt cg (CoreTm_Quantifier q x ty t)" "lt_ok prog rt cg (CoreTm_Allocated ty' t')"
  by (simp_all add: lt_ok_def lower_term.simps cg_fail_def)

lemma la_Ghost: "la_ok prog rt cg (CoreTm_Quantifier q x ty t)" "la_ok prog rt cg (CoreTm_Allocated ty' t')"
  by (simp_all add: la_ok_def lower_addr.simps cg_fail_def)

lemma scalar_ty_not_CharPtr: "scalar_ty ty \<noteq> Some CTy_CharPtr"
  by (cases ty) simp_all

lemma lt_Default: "lt_ok prog rt cg (CoreTm_Default ty)"
  unfolding lt_ok_def
proof (intro allI impI)
  fix E ds st S e st'
  assume l: "lower_term cg (CoreTm_Default ty) st = Inr ((S, e), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and tf: "term_fits (CG_TyEnv cg) (CoreTm_Default ty)"
  from term_fits_type[OF tf] obtain ty' where tyd: "core_term_type (CG_TyEnv cg) NotGhost (CoreTm_Default ty) = Some ty'"
    and f: "fits (CG_TyEnv cg) ty'" by blast
  have ty': "ty' = ty" and wk: "is_well_kinded (CG_TyEnv cg) ty" using default_typed[OF tyd] by simp_all
  show "\<exists>E' ds' ty'. core_term_type (CG_TyEnv cg) NotGhost (CoreTm_Default ty) = Some ty'
          \<and> lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e (res_cty ty')"
  proof (cases "scalar_ty ty")
    case (Some cty)
    show ?thesis
    proof (cases cty)
      case (CTy_Int s b)
      then have "S = []" "e = ME_Int s b 0" "st' = st" using l Some by (simp_all add: lower_term.simps cg_return_def)
      moreover have "expr_ok E (ME_Int s b 0) (res_cty ty)" using Some CTy_Int by (simp add: expr_ok_def)
      ultimately show ?thesis using tyd ty' lowered_ok_nil[OF sc] by blast
    next
      case CTy_CharPtr
      then show ?thesis using Some scalar_ty_not_CharPtr by simp
    next
      case CTy_VoidPtr
      have unf: "lower_term cg (CoreTm_Default ty) st =
          cg_bind (fresh_name (CG_Fun cg) ''null'')
            (\<lambda>tmp. cg_return ([MS_DeclScalar tmp CTy_VoidPtr, MS_Zero (ME_AddrOf tmp) ME_PtrSize], ME_Var tmp)) st"
        using Some CTy_VoidPtr by (simp add: lower_term.simps)
      from l[unfolded unf] obtain tmp st1 where fr: "fresh_name (CG_Fun cg) ''null'' st = Inr (tmp, st1)"
        and r: "cg_return ([MS_DeclScalar tmp CTy_VoidPtr, MS_Zero (ME_AddrOf tmp) ME_PtrSize], ME_Var tmp) st1 = Inr ((S, e), st')"
        by (rule cg_bind_InrE)
      from r have S: "S = [MS_DeclScalar tmp CTy_VoidPtr, MS_Zero (ME_AddrOf tmp) ME_PtrSize]" and e: "e = ME_Var tmp"
        and st': "st' = st1" by (auto simp: cg_return_def)
      note fr = fr[folded st']
      let ?E' = "fmupd tmp (VT_Scalar CTy_VoidPtr) E"
      have d: "lowered_ok prog rt (E, ds) st [MS_DeclScalar tmp CTy_VoidPtr] st' (?E', tmp # ds)"
        by (rule fresh_scalar_ok[OF sc fr])
      have z: "lowered_ok prog rt (?E', tmp # ds) st' [MS_Zero (ME_AddrOf tmp) ME_PtrSize] st' (?E', tmp # ds)"
        using lowered_ok_scope[OF d] by (intro zero_ok[where pty = CTy_CharPtr]) (auto simp: expr_ok_def)
      have res: "expr_ok ?E' (ME_Var tmp) (res_cty ty)" using Some CTy_VoidPtr by (simp add: expr_ok_def)
      have lo: "lowered_ok prog rt (E, ds) st S st' (?E', tmp # ds)" unfolding S using lowered_ok_append[OF d z] by simp
      show ?thesis unfolding e using tyd ty' lo res by blast
    qed
  next
    case None
    have unf: "lower_term cg (CoreTm_Default ty) st =
        cg_bind (fresh_name (CG_Fun cg) ''def'')
          (\<lambda>tmp. cg_return ([MS_DeclBuf tmp (buf_size (cg_size cg ty)), MS_Zero (ME_AddrOf tmp) (cg_size cg ty)], ME_AddrOf tmp)) st"
      using None by (simp add: lower_term.simps)
    from l[unfolded unf] obtain tmp st1 where fr: "fresh_name (CG_Fun cg) ''def'' st = Inr (tmp, st1)"
      and r: "cg_return ([MS_DeclBuf tmp (buf_size (cg_size cg ty)), MS_Zero (ME_AddrOf tmp) (cg_size cg ty)], ME_AddrOf tmp) st1 = Inr ((S, e), st')"
      by (rule cg_bind_InrE)
    from r have S: "S = [MS_DeclBuf tmp (buf_size (cg_size cg ty)), MS_Zero (ME_AddrOf tmp) (cg_size cg ty)]" and e: "e = ME_AddrOf tmp"
      and st': "st' = st1" by (auto simp: cg_return_def)
    note fr = fr[folded st']
    have sz: "u64_ok E (cg_size cg ty)" using cg_size_ok[OF ok wk] f ty' by simp
    let ?E' = "fmupd tmp VT_Buf E"
    have d: "lowered_ok prog rt (E, ds) st [MS_DeclBuf tmp (buf_size (cg_size cg ty))] st' (?E', tmp # ds)"
      by (rule fresh_buf_ok[OF sc fr buf_size_ok[OF sz]])
    have z: "lowered_ok prog rt (?E', tmp # ds) st' [MS_Zero (ME_AddrOf tmp) (cg_size cg ty)] st' (?E', tmp # ds)"
      using lowered_ok_scope[OF d] u64_ok_def[of ?E'] expr_type_mono[OF lowered_ok_env_le'[OF d]] sz
      by (intro zero_ok[where pty = CTy_CharPtr]) (auto simp: expr_ok_def u64_ok_def)
    have res: "expr_ok ?E' (ME_AddrOf tmp) (res_cty ty)" using None by (simp add: expr_ok_def)
    have lo: "lowered_ok prog rt (E, ds) st S st' (?E', tmp # ds)" unfolding S using lowered_ok_append[OF d z] by simp
    show ?thesis unfolding e using tyd ty' lo res by blast
  qed
qed

lemma lt_VariantCtor:
  assumes IH: "\<And>x st st' xa sta st'a x11 x12 xb stb st'b.
        ty_of cg (CoreTm_VariantCtor c tys t) st = Inr (x, st') \<Longrightarrow> ty_of cg t sta = Inr (xa, st'a) \<Longrightarrow>
        x = CoreTy_Datatype x11 x12 \<Longrightarrow> fresh_name (CG_Fun cg) ''var'' stb = Inr (xb, st'b) \<Longrightarrow> lt_ok prog rt cg t"
  shows "lt_ok prog rt cg (CoreTm_VariantCtor c tys t)"
  unfolding lt_ok_def
proof (intro allI impI)
  fix E ds st S e st'
  assume l: "lower_term cg (CoreTm_VariantCtor c tys t) st = Inr ((S, e), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and tf: "term_fits (CG_TyEnv cg) (CoreTm_VariantCtor c tys t)"
  from term_fits_type[OF tf] obtain dtTy where tyv: "core_term_type (CG_TyEnv cg) NotGhost (CoreTm_VariantCtor c tys t) = Some dtTy"
    and fdt: "fits (CG_TyEnv cg) dtTy" by blast
  obtain dtName tyvars payloadTy where dt: "dtTy = CoreTy_Datatype dtName tys"
    and lk: "fmlookup (TE_DataCtors (CG_TyEnv cg)) c = Some (dtName, tyvars, payloadTy)"
    and tp: "core_term_type (CG_TyEnv cg) NotGhost t = Some (apply_subst (fmap_of_list (zip tyvars tys)) payloadTy)"
    using variant_ctor_typed[OF tyv] by blast
  define pty where "pty = apply_subst (fmap_of_list (zip tyvars tys)) payloadTy"
  let ?pty = "pty"
  let ?env = "CG_TyEnv cg"
  have tp: "core_term_type (CG_TyEnv cg) NotGhost t = Some pty" using tp by (simp add: pty_def)
  have unf: "lower_term cg (CoreTm_VariantCtor c tys t) st =
      cg_bind (fresh_name (CG_Fun cg) ''var'')
        (\<lambda>tmp. cg_bind (lower_term cg t)
          (\<lambda>(S1, e1). cg_return ([MS_DeclBuf tmp (buf_size (cg_size cg dtTy)), MS_Uninit (ME_AddrOf tmp) (cg_size cg dtTy),
                                   MS_Store (tag_ty ?env dtName) (ME_AddrOf tmp) (tag_lit ?env dtName c)]
                                  @ S1 @ [store_at cg ?pty (ptr_add (ME_AddrOf tmp) (tag_off ?env dtName)) e1],
                                  ME_AddrOf tmp))) st"
    unfolding lower_term.simps by (simp add: cg_bind_def ty_of_Some[OF tyv] ty_of_Some[OF tp] dt)
  from l[unfolded unf] obtain tmp st1 where fr: "fresh_name (CG_Fun cg) ''var'' st = Inr (tmp, st1)"
    and r1: "cg_bind (lower_term cg t)
          (\<lambda>(S1, e1). cg_return ([MS_DeclBuf tmp (buf_size (cg_size cg dtTy)), MS_Uninit (ME_AddrOf tmp) (cg_size cg dtTy),
                                   MS_Store (tag_ty ?env dtName) (ME_AddrOf tmp) (tag_lit ?env dtName c)]
                                  @ S1 @ [store_at cg ?pty (ptr_add (ME_AddrOf tmp) (tag_off ?env dtName)) e1],
                                  ME_AddrOf tmp)) st1 = Inr ((S, e), st')"
    by (rule cg_bind_InrE)
  from r1 obtain r st2 where l1': "lower_term cg t st1 = Inr (r, st2)"
    and r2: "(\<lambda>(S1, e1). cg_return ([MS_DeclBuf tmp (buf_size (cg_size cg dtTy)), MS_Uninit (ME_AddrOf tmp) (cg_size cg dtTy),
                                   MS_Store (tag_ty ?env dtName) (ME_AddrOf tmp) (tag_lit ?env dtName c)]
                                  @ S1 @ [store_at cg ?pty (ptr_add (ME_AddrOf tmp) (tag_off ?env dtName)) e1],
                                  ME_AddrOf tmp)) r st2 = Inr ((S, e), st')"
    by (rule cg_bind_InrE)
  obtain S1 e1 where r: "r = (S1, e1)" by (cases r)
  have l1: "lower_term cg t st1 = Inr ((S1, e1), st2)" using l1' r by simp
  from r2 have S: "S = [MS_DeclBuf tmp (buf_size (cg_size cg dtTy)), MS_Uninit (ME_AddrOf tmp) (cg_size cg dtTy),
                 MS_Store (tag_ty ?env dtName) (ME_AddrOf tmp) (tag_lit ?env dtName c)]
                @ S1 @ [store_at cg ?pty (ptr_add (ME_AddrOf tmp) (tag_off ?env dtName)) e1]"
    and e: "e = ME_AddrOf tmp" and st': "st' = st2" unfolding r by (auto simp: cg_return_def)
  note l1 = l1[folded st']
  have sz: "u64_ok E (cg_size cg dtTy)" using cg_size_ok[OF ok term_type_wk(1)[OF ok tyv] fdt] .
  let ?E1 = "fmupd tmp VT_Buf E"
  have d: "lowered_ok prog rt (E, ds) st [MS_DeclBuf tmp (buf_size (cg_size cg dtTy))] st1 (?E1, tmp # ds)"
    by (rule fresh_buf_ok[OF sc fr buf_size_ok[OF sz]])
  have le1: "env_le E ?E1" by (rule lowered_ok_env_le'[OF d])
  have sz1: "u64_ok ?E1 (cg_size cg dtTy)" using sz expr_type_mono[OF le1] by (auto simp: u64_ok_def)
  have tmp1: "expr_ok ?E1 (ME_AddrOf tmp) CTy_CharPtr" by (simp add: expr_ok_def)
  have sc1: "scope_ok prog (?E1, tmp # ds) st1" by (rule lowered_ok_scope[OF d])
  have u: "lowered_ok prog rt (?E1, tmp # ds) st1 [MS_Uninit (ME_AddrOf tmp) (cg_size cg dtTy)] st1 (?E1, tmp # ds)"
    using sc1 tmp1 sz1 by (intro uninit_ok[where pty = CTy_CharPtr]) auto
  have mem: "c \<in> set (dt_ctors ?env dtName)" using ctor_in_dt_ctors[OF cg_ok_wf[OF ok] lk] .
  note tl = tag_lit_type[OF mem cg_ok_tags[OF ok]]
  have tg: "lowered_ok prog rt (?E1, tmp # ds) st1 [MS_Store (tag_ty ?env dtName) (ME_AddrOf tmp) (tag_lit ?env dtName c)] st1 (?E1, tmp # ds)"
    using sc1 tmp1 tl by (intro store_ok[where cty' = "tag_ty ?env dtName"]) (auto simp: expr_ok_def)
  have ok1: "cg_ok prog ?E1 cg" using cg_ok_mono[OF le1 ok] .
  obtain E2 ds2 ty2 where ty2: "core_term_type ?env NotGhost t = Some ty2"
    and lo1: "lowered_ok prog rt (?E1, tmp # ds) st1 S1 st' (E2, ds2)" and e1: "expr_ok E2 e1 (res_cty ty2)"
    using lt_okD[OF IH[OF ty_of_Some[OF tyv] ty_of_Some[OF tp] dt fr] l1 ok1 sc1 term_fits_VariantCtor[OF tf, THEN conjunct1]] by blast
  have ty2': "ty2 = ?pty" using ty2 tp by simp
  have le2: "env_le ?E1 E2" by (rule lowered_ok_env_le'[OF lo1])
  have pwk: "is_well_kinded ?env ?pty" using term_type_wk(1)[OF ok tp] .
  have pf: "fits ?env ?pty" using term_fits_ty[OF term_fits_VariantCtor[OF tf, THEN conjunct1] tp] .
  have psz: "u64_ok E2 (cg_size cg ?pty)" using cg_size_ok[OF cg_ok_mono[OF le2 ok1] pwk pf] .
  have dst: "expr_ok E2 (ptr_add (ME_AddrOf tmp) (tag_off ?env dtName)) CTy_CharPtr"
    using expr_ok_mono[OF le2 tmp1] by (intro expr_ok_ptr_add) (auto simp: u64_ok_def)
  have st2: "lowered_ok prog rt (E2, ds2) st' [store_at cg ?pty (ptr_add (ME_AddrOf tmp) (tag_off ?env dtName)) e1] st' (E2, ds2)"
    using store_at_ok[OF lowered_ok_scope[OF lo1] dst e1[unfolded ty2'] psz] .
  have res: "expr_ok E2 (ME_AddrOf tmp) (res_cty dtTy)" using expr_ok_mono[OF le2 tmp1] dt by (simp add: res_cty_def)
  have lo: "lowered_ok prog rt (E, ds) st S st' (E2, ds2)"
    unfolding S using lowered_ok_append[OF lowered_ok_append[OF lowered_ok_append[OF lowered_ok_append[OF d u] tg] lo1] st2] by simp
  show "\<exists>E' ds' ty. core_term_type ?env NotGhost (CoreTm_VariantCtor c tys t) = Some ty
          \<and> lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e (res_cty ty)"
    unfolding e using tyv res lo by blast
qed

lemma lt_RecordProj:
  assumes IH: "\<And>x st st' x6 xa sta st'a. ty_of cg t st = Inr (x, st') \<Longrightarrow> x = CoreTy_Record x6 \<Longrightarrow>
        cg_lift (CG_Fun cg) ''unknown field'' (map_of x6 f) sta = Inr (xa, st'a) \<Longrightarrow> la_ok prog rt cg t"
  shows "lt_ok prog rt cg (CoreTm_RecordProj t f)"
  unfolding lt_ok_def
proof (intro allI impI)
  fix E ds st S e st'
  assume l: "lower_term cg (CoreTm_RecordProj t f) st = Inr ((S, e), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and tf: "term_fits (CG_TyEnv cg) (CoreTm_RecordProj t f)"
  from term_fits_type[OF tf] obtain ty where tyP: "core_term_type (CG_TyEnv cg) NotGhost (CoreTm_RecordProj t f) = Some ty" by blast
  obtain fldTys where tt: "core_term_type (CG_TyEnv cg) NotGhost t = Some (CoreTy_Record fldTys)" and mo: "map_of fldTys f = Some ty"
    using record_proj_typed[OF tyP] by blast
  from l tt mo obtain S1 p where la: "lower_addr cg t st = Inr ((S1, p), st')" and S: "S = S1"
    and e: "e = load_at ty (ptr_add p (field_off (CG_TyEnv cg) fldTys f))"
    by (auto simp: lower_term.simps ty_of_Inr cg_lift_Inr cg_return_def elim!: cg_bind_InrE)
  obtain E1 ds1 where lo1: "lowered_ok prog rt (E, ds) st S1 st' (E1, ds1)" and p: "expr_ok E1 p CTy_CharPtr"
    using la_okD[OF IH[OF ty_of_Some[OF tt] refl] la ok sc term_fits_RecordProj[OF tf]] by (auto simp: cg_lift_Inr mo)
  have off: "u64_ok E1 (field_off (CG_TyEnv cg) fldTys f)"
    using cg_field_off_ok[OF cg_ok_mono[OF lowered_ok_env_le'[OF lo1] ok] term_type_wk(1)[OF ok tt]
                             term_fits_ty[OF term_fits_RecordProj[OF tf] tt]] .
  show "\<exists>E' ds' ty. core_term_type (CG_TyEnv cg) NotGhost (CoreTm_RecordProj t f) = Some ty
          \<and> lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e (res_cty ty)"
    unfolding S e using tyP lo1 expr_ok_load_at[OF expr_ok_ptr_add[OF p _ off]] by (intro exI conjI) (assumption | simp)+
qed

lemma lt_VariantProj:
  assumes IH: "\<And>x st st' xa sta st'a x11 x12. ty_of cg t st = Inr (x, st') \<Longrightarrow>
        ty_of cg (CoreTm_VariantProj t c) sta = Inr (xa, st'a) \<Longrightarrow> x = CoreTy_Datatype x11 x12 \<Longrightarrow> la_ok prog rt cg t"
  shows "lt_ok prog rt cg (CoreTm_VariantProj t c)"
  unfolding lt_ok_def
proof (intro allI impI)
  fix E ds st S e st'
  assume l: "lower_term cg (CoreTm_VariantProj t c) st = Inr ((S, e), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and tf: "term_fits (CG_TyEnv cg) (CoreTm_VariantProj t c)"
  from term_fits_type[OF tf] obtain ty where tyP: "core_term_type (CG_TyEnv cg) NotGhost (CoreTm_VariantProj t c) = Some ty" by blast
  obtain dtName args tyvars payloadTy where tt: "core_term_type (CG_TyEnv cg) NotGhost t = Some (CoreTy_Datatype dtName args)"
    using variant_proj_typed[OF tyP] by blast
  from l tt tyP obtain S1 p where la: "lower_addr cg t st = Inr ((S1, p), st')" and S: "S = S1"
    and e: "e = load_at ty (ptr_add p (tag_off (CG_TyEnv cg) dtName))"
    by (auto simp: lower_term.simps ty_of_Inr cg_return_def elim!: cg_bind_InrE)
  obtain E1 ds1 where lo1: "lowered_ok prog rt (E, ds) st S1 st' (E1, ds1)" and p: "expr_ok E1 p CTy_CharPtr"
    using la_okD[OF IH[OF ty_of_Some[OF tt] ty_of_Some[OF tyP] refl] la ok sc term_fits_VariantProj[OF tf]] by blast
  show "\<exists>E' ds' ty. core_term_type (CG_TyEnv cg) NotGhost (CoreTm_VariantProj t c) = Some ty
          \<and> lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e (res_cty ty)"
    unfolding S e using tyP lo1 expr_ok_load_at[OF expr_ok_ptr_add[OF p _ tag_off_type[THEN u64_ok_def[THEN iffD2, OF conjI[OF tag_off_wf]]]]]
    by (intro exI conjI) (assumption | simp)+
qed

(* The indices of an array projection, lowered one after the other. *)
lemma lower_indices_ok:
  assumes "cg_mapM (lower_term cg) idxs st = Inr (rs, st')"
    and IH: "\<And>i. i \<in> set idxs \<Longrightarrow> lt_ok prog rt cg i"
    and "cg_ok prog E cg" and "scope_ok prog (E, ds) st"
    and "\<forall>i \<in> set idxs. term_fits (CG_TyEnv cg) i"
    and "\<forall>i \<in> set idxs. core_term_type (CG_TyEnv cg) NotGhost i = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st (concat (map fst rs)) st' (E', ds') \<and> (\<forall>r \<in> set rs. u64_ok E' (snd r))"
proof (rule cg_mapM_chain[OF assms(1,4)])
  fix i st1 r st2 E1 ds1
  assume i: "i \<in> set idxs" and li: "lower_term cg i st1 = Inr (r, st2)" and sc1: "scope_ok prog (E1, ds1) st1" and le: "env_le E E1"
  obtain S e where r: "r = (S, e)" by (cases r)
  have tfi: "term_fits (CG_TyEnv cg) i" using assms(5) i by simp
  obtain E2 ds2 ty where ty: "core_term_type (CG_TyEnv cg) NotGhost i = Some ty"
    and lo: "lowered_ok prog rt (E1, ds1) st1 S st2 (E2, ds2)" and e: "expr_ok E2 e (res_cty ty)"
    by (rule lt_okD[OF IH[OF i] li[unfolded r] cg_ok_mono[OF le assms(3)] sc1 tfi])
  have "ty = CoreTy_FiniteInt Unsigned IntBits_64" using assms(6) i ty by simp
  then have "u64_ok E2 e" using e by simp
  then show "\<exists>E2 ds2. lowered_ok prog rt (E1, ds1) st1 (fst r) st2 (E2, ds2) \<and> u64_ok E2 (snd r)"
    using lo unfolding r by auto
next
  fix E1 E2 r assume "env_le E1 E2" "u64_ok E1 (snd r)"
  then show "u64_ok E2 (snd r)" by (auto simp: u64_ok_def expr_type_mono)
qed

lemma lt_ArrayProj:
  assumes IHt: "\<And>x st st' x71 x72. ty_of cg t st = Inr (x, st') \<Longrightarrow> x = CoreTy_Array x71 x72 \<Longrightarrow> la_ok prog rt cg t"
    and IHi: "\<And>x st st' x71 x72 xa sta st'a xb y xc. ty_of cg t st = Inr (x, st') \<Longrightarrow> x = CoreTy_Array x71 x72 \<Longrightarrow>
        lower_addr cg t sta = Inr (xa, st'a) \<Longrightarrow> (xb, y) = xa \<Longrightarrow> xc \<in> set idxs \<Longrightarrow> lt_ok prog rt cg xc"
  shows "lt_ok prog rt cg (CoreTm_ArrayProj t idxs)"
  unfolding lt_ok_def
proof (intro allI impI)
  fix E ds st S e st'
  assume l: "lower_term cg (CoreTm_ArrayProj t idxs) st = Inr ((S, e), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and tf: "term_fits (CG_TyEnv cg) (CoreTm_ArrayProj t idxs)"
  from term_fits_type[OF tf] obtain elemTy where tyP: "core_term_type (CG_TyEnv cg) NotGhost (CoreTm_ArrayProj t idxs) = Some elemTy"
    and fe: "fits (CG_TyEnv cg) elemTy" by blast
  obtain dims where tt: "core_term_type (CG_TyEnv cg) NotGhost t = Some (CoreTy_Array elemTy dims)"
    and lens: "length idxs = length dims"
    and idxty: "\<forall>i \<in> set idxs. core_term_type (CG_TyEnv cg) NotGhost i = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
    using array_proj_typed[OF tyP] by blast
  let ?env = "CG_TyEnv cg"
  from l tt obtain S1 p st1 rs where la: "lower_addr cg t st = Inr ((S1, p), st1)"
    and lm: "cg_mapM (lower_term cg) idxs st1 = Inr (rs, st')"
    and S: "S = S1 @ concat (map fst rs)" and e: "e = load_at elemTy (elem_addr ?env elemTy dims p (map snd rs))"
    by (auto simp: lower_term.simps ty_of_Inr cg_return_def elim!: cg_bind_InrE)
  note tfs = term_fits_ArrayProj[OF tf]
  obtain E1 ds1 where lo1: "lowered_ok prog rt (E, ds) st S1 st1 (E1, ds1)" and p: "expr_ok E1 p CTy_CharPtr"
    using la_okD[OF IHt[OF ty_of_Some[OF tt] refl] la ok sc] tfs by blast
  have ok1: "cg_ok prog E1 cg" using cg_ok_mono[OF lowered_ok_env_le'[OF lo1] ok] .
  obtain E2 ds2 where lo2: "lowered_ok prog rt (E1, ds1) st1 (concat (map fst rs)) st' (E2, ds2)"
    and idx: "\<forall>r \<in> set rs. u64_ok E2 (snd r)"
    using lower_indices_ok[OF lm IHi[OF ty_of_Some[OF tt] refl la refl] ok1 lowered_ok_scope[OF lo1]] tfs idxty by blast
  have p2: "expr_ok E2 p CTy_CharPtr" using expr_ok_mono[OF lowered_ok_env_le'[OF lo2] p] .
  have addr: "expr_ok E2 (elem_addr ?env elemTy dims p (map snd rs)) CTy_CharPtr"
    using cg_elem_addr_ok[OF cg_ok_mono[OF lowered_ok_env_le'[OF lo2] ok1] term_type_wk(1)[OF ok tt] fe
                             term_fits_ty[OF tfs[THEN conjunct1] tt] p2] idx by auto
  show "\<exists>E' ds' ty. core_term_type ?env NotGhost (CoreTm_ArrayProj t idxs) = Some ty
          \<and> lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e (res_cty ty)"
    unfolding S e using tyP lowered_ok_append[OF lo1 lo2] expr_ok_load_at[OF addr] by blast
qed

(* The size of the result type of sizeof: 8 bytes per dimension. *)
lemma sizeof_type_scalar: "scalar_ty (sizeof_type dims) = (if length dims = 1 then Some CTy_U64 else None)"
  by (cases dims rule: sizeof_type.cases) (simp_all add: u64_type_def)

lemma map_snd_zip_replicate:
  "length ns = n \<Longrightarrow> map (\<lambda>fld. f (snd fld)) (zip ns (replicate n x)) = replicate n (f x)"
proof (induction ns arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a ns)
  then obtain m where "n = Suc m" by (cases n) auto
  then show ?case using Cons by simp
qed

lemma sizeof_type_fits_dims:
  assumes "fits env (sizeof_type dims)" and "length dims \<noteq> 1"
  shows "8 * length dims < u64_max"
proof -
  have "sizeof_type dims = CoreTy_Record (zip (tuple_field_names (length dims)) (replicate (length dims) u64_type))"
    using assms(2) by (cases dims rule: sizeof_type.cases) auto
  moreover have "tsz (dt_fuel env) env 0 (\<lambda>_. 0) (CoreTy_Record (zip (tuple_field_names (length dims)) (replicate (length dims) u64_type)))
                 = 8 * length dims"
  proof -
    have "map (\<lambda>fld. tsz (dt_fuel env) env 0 (\<lambda>_. 0) (snd fld)) (zip (tuple_field_names (length dims)) (replicate (length dims) u64_type))
          = replicate (length dims) (tsz (dt_fuel env) env 0 (\<lambda>_. 0) u64_type)"
      by (rule map_snd_zip_replicate) simp
    then show ?thesis by (simp add: sum_list_replicate u64_type_def)
  qed
  ultimately show ?thesis
    using assms(1) unfolding fits_def size_fits_def by (simp add: tsz_fits.simps)
qed

lemma lt_Sizeof:
  assumes IH: "\<And>x st st' x71 x72. ty_of cg t st = Inr (x, st') \<Longrightarrow> x = CoreTy_Array x71 x72 \<Longrightarrow> \<not> dims_all_fixed x72 \<Longrightarrow> lt_ok prog rt cg t"
  shows "lt_ok prog rt cg (CoreTm_Sizeof t)"
  unfolding lt_ok_def
proof (intro allI impI)
  fix E ds st S e st'
  assume l: "lower_term cg (CoreTm_Sizeof t) st = Inr ((S, e), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and tf: "term_fits (CG_TyEnv cg) (CoreTm_Sizeof t)"
  from term_fits_type[OF tf] obtain ty where tyP: "core_term_type (CG_TyEnv cg) NotGhost (CoreTm_Sizeof t) = Some ty"
    and f: "fits (CG_TyEnv cg) ty" by blast
  obtain elemTy dims where tt: "core_term_type (CG_TyEnv cg) NotGhost t = Some (CoreTy_Array elemTy dims)" and ty: "ty = sizeof_type dims"
    using sizeof_typed[OF tyP] by blast
  have dwk: "array_dims_well_kinded dims" using term_type_wk(1)[OF ok tt] by simp
  have dlt: "\<And>k. k < length dims \<Longrightarrow> dim_size (dims ! k) < u64_max" using dim_size_lt_u64_max[OF dwk] by simp
  note res = sizeof_type_scalar[of dims]
  show "\<exists>E' ds' ty. core_term_type (CG_TyEnv cg) NotGhost (CoreTm_Sizeof t) = Some ty
          \<and> lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e (res_cty ty)"
  proof (cases "dims_all_fixed dims")
    case True
    note fx = \<open>dims_all_fixed dims\<close>
    show ?thesis
    proof (cases "length dims = 1")
      case True
      note len1 = \<open>length dims = 1\<close>
      obtain d where d: "dims = [d]" using len1 length_Suc_conv[of dims 0] by auto
      have "S = []" "e = u64_lit (dim_size d)" "st' = st"
        using l fx d by (simp_all add: lower_term.simps cg_bind_def ty_of_Some[OF tt] cg_return_def)
      then show ?thesis using tyP ty d dlt[of 0] lowered_ok_nil[OF sc] by (auto simp: expr_ok_def res_cty_def u64_type_def)
    next
      case False
      note nlen = \<open>length dims \<noteq> 1\<close>
      have unf: "lower_term cg (CoreTm_Sizeof t) st =
          cg_bind (fresh_name (CG_Fun cg) ''sz'')
            (\<lambda>tmp. cg_return ([MS_DeclBuf tmp (u64_lit (8 * length dims))]
                   @ map (\<lambda>k. MS_Store CTy_U64 (ptr_add (ME_AddrOf tmp) (u64_lit (8 * k))) (u64_lit (dim_size (dims ! k)))) [0..<length dims],
                   ME_AddrOf tmp)) st"
        using fx nlen by (cases dims rule: sizeof_type.cases) (simp_all add: lower_term.simps cg_bind_def ty_of_Some[OF tt])
      from l[unfolded unf] obtain tmp st1 where fr: "fresh_name (CG_Fun cg) ''sz'' st = Inr (tmp, st1)"
        and r: "cg_return ([MS_DeclBuf tmp (u64_lit (8 * length dims))]
                   @ map (\<lambda>k. MS_Store CTy_U64 (ptr_add (ME_AddrOf tmp) (u64_lit (8 * k))) (u64_lit (dim_size (dims ! k)))) [0..<length dims],
                   ME_AddrOf tmp) st1 = Inr ((S, e), st')"
        by (rule cg_bind_InrE)
      from r have S: "S = [MS_DeclBuf tmp (u64_lit (8 * length dims))]
                   @ map (\<lambda>k. MS_Store CTy_U64 (ptr_add (ME_AddrOf tmp) (u64_lit (8 * k))) (u64_lit (dim_size (dims ! k)))) [0..<length dims]"
        and e: "e = ME_AddrOf tmp" and st': "st' = st1" by (auto simp: cg_return_def)
      note fr = fr[folded st']
      have lt: "8 * length dims < u64_max" using sizeof_type_fits_dims[OF f[unfolded ty] nlen] .
      let ?E1 = "fmupd tmp VT_Buf E"
      have d: "lowered_ok prog rt (E, ds) st [MS_DeclBuf tmp (u64_lit (8 * length dims))] st' (?E1, tmp # ds)"
        using lt by (intro fresh_buf_ok[OF sc fr]) simp
      have stores: "lowered_ok prog rt (?E1, tmp # ds) st'
          (map (\<lambda>k. MS_Store CTy_U64 (ptr_add (ME_AddrOf tmp) (u64_lit (8 * k))) (u64_lit (dim_size (dims ! k)))) [0..<length dims])
          st' (?E1, tmp # ds)"
      proof (rule lowered_ok_pure_list[OF lowered_ok_scope[OF d]])
        fix s assume "s \<in> set (map (\<lambda>k. MS_Store CTy_U64 (ptr_add (ME_AddrOf tmp) (u64_lit (8 * k))) (u64_lit (dim_size (dims ! k)))) [0..<length dims])"
        then obtain k where k: "k < length dims"
          and s: "s = MS_Store CTy_U64 (ptr_add (ME_AddrOf tmp) (u64_lit (8 * k))) (u64_lit (dim_size (dims ! k)))" by auto
        have "8 * k < u64_max" using k lt by simp
        then show "lowered_ok prog rt (?E1, tmp # ds) st' [s] st' (?E1, tmp # ds)"
          unfolding s using lowered_ok_scope[OF d] dlt[OF k]
          by (intro store_ok[where cty' = CTy_U64 and pty = CTy_CharPtr]) (auto simp: expr_ok_def ptr_add_def)
      qed
      have res': "expr_ok ?E1 (ME_AddrOf tmp) (res_cty ty)" using res nlen ty by (simp add: expr_ok_def res_cty_def)
      show ?thesis unfolding S e using tyP lowered_ok_append[OF d stores] res' by blast
    qed
  next
    case False
    note nfx = \<open>\<not> dims_all_fixed dims\<close>
    let ?k = "\<lambda>(S1, p). (case dims of [_] \<Rightarrow> cg_return (S1, ME_Load CTy_U64 (ptr_add p (dim_off 0)))
                  | _ \<Rightarrow> do { tmp \<leftarrow> fresh_name (CG_Fun cg) ''sz'';
                               cg_return (S1 @ [MS_DeclBuf tmp (u64_lit (8 * length dims)),
                                                MS_Copy (ME_AddrOf tmp) (ptr_add p (dim_off 0)) (u64_lit (8 * length dims))],
                                          ME_AddrOf tmp) })"
    have unf: "lower_term cg (CoreTm_Sizeof t) st = cg_bind (lower_term cg t) ?k st"
      using nfx by (simp add: lower_term.simps cg_bind_def ty_of_Some[OF tt])
    from l[unfolded unf] obtain r st1 where l1': "lower_term cg t st = Inr (r, st1)" and rest': "?k r st1 = Inr ((S, e), st')"
      by (rule cg_bind_InrE)
    obtain S1 p where r: "r = (S1, p)" by (cases r)
    have l1: "lower_term cg t st = Inr ((S1, p), st1)" using l1' r by simp
    have rest: "(case dims of [_] \<Rightarrow> cg_return (S1, ME_Load CTy_U64 (ptr_add p (dim_off 0)))
                  | _ \<Rightarrow> do { tmp \<leftarrow> fresh_name (CG_Fun cg) ''sz'';
                               cg_return (S1 @ [MS_DeclBuf tmp (u64_lit (8 * length dims)),
                                                MS_Copy (ME_AddrOf tmp) (ptr_add p (dim_off 0)) (u64_lit (8 * length dims))],
                                          ME_AddrOf tmp) }) st1 = Inr ((S, e), st')"
      using rest' unfolding r by simp
    obtain E1 ds1 ty1 where ty1: "core_term_type (CG_TyEnv cg) NotGhost t = Some ty1"
      and lo1: "lowered_ok prog rt (E, ds) st S1 st1 (E1, ds1)" and p: "expr_ok E1 p (res_cty ty1)"
      using lt_okD[OF IH[OF ty_of_Some[OF tt] refl nfx] l1 ok sc term_fits_Sizeof[OF tf]] by blast
    have "ty1 = CoreTy_Array elemTy dims" using ty1 tt by simp
    then have p': "expr_ok E1 p CTy_CharPtr" using p by (simp add: res_cty_def)
    have dimoff: "expr_ok E1 (ptr_add p (dim_off 0)) CTy_CharPtr"
      by (intro expr_ok_ptr_add[OF p']) (auto simp: u64_ok_def)
    show ?thesis
    proof (cases "length dims = 1")
      case True
      note len1 = \<open>length dims = 1\<close>
      obtain d where dd: "dims = [d]" using len1 length_Suc_conv[of dims 0] by auto
      have Se: "S = S1" "e = ME_Load CTy_U64 (ptr_add p (dim_off 0))" "st' = st1" using rest dd by (simp_all add: cg_return_def)
      have "expr_ok E1 (ME_Load CTy_U64 (ptr_add p (dim_off 0))) CTy_U64" by (rule expr_ok_Load[OF dimoff]) simp
      then have res': "expr_ok E1 e (res_cty ty)" unfolding Se ty dd by (simp add: u64_type_def)
      show ?thesis unfolding Se(1) Se(3) using tyP lo1 res' by blast
    next
      case False
      note nlen = \<open>length dims \<noteq> 1\<close>
      have rest': "cg_bind (fresh_name (CG_Fun cg) ''sz'')
            (\<lambda>tmp. cg_return (S1 @ [MS_DeclBuf tmp (u64_lit (8 * length dims)),
                                    MS_Copy (ME_AddrOf tmp) (ptr_add p (dim_off 0)) (u64_lit (8 * length dims))],
                               ME_AddrOf tmp)) st1 = Inr ((S, e), st')"
        using rest nlen by (cases dims rule: sizeof_type.cases) simp_all
      from rest' obtain tmp st2 where fr: "fresh_name (CG_Fun cg) ''sz'' st1 = Inr (tmp, st2)"
        and r: "cg_return (S1 @ [MS_DeclBuf tmp (u64_lit (8 * length dims)),
                                    MS_Copy (ME_AddrOf tmp) (ptr_add p (dim_off 0)) (u64_lit (8 * length dims))],
                               ME_AddrOf tmp) st2 = Inr ((S, e), st')"
        by (rule cg_bind_InrE)
      from r have S: "S = S1 @ [MS_DeclBuf tmp (u64_lit (8 * length dims)),
                           MS_Copy (ME_AddrOf tmp) (ptr_add p (dim_off 0)) (u64_lit (8 * length dims))]"
        and e: "e = ME_AddrOf tmp" and st': "st' = st2" by (auto simp: cg_return_def)
      note fr = fr[folded st']
      have lt: "8 * length dims < u64_max" using sizeof_type_fits_dims[OF f[unfolded ty] nlen] .
      let ?E2 = "fmupd tmp VT_Buf E1"
      have d: "lowered_ok prog rt (E1, ds1) st1 [MS_DeclBuf tmp (u64_lit (8 * length dims))] st' (?E2, tmp # ds1)"
        using lt by (intro fresh_buf_ok[OF lowered_ok_scope[OF lo1] fr]) simp
      have cp: "lowered_ok prog rt (?E2, tmp # ds1) st' [MS_Copy (ME_AddrOf tmp) (ptr_add p (dim_off 0)) (u64_lit (8 * length dims))] st' (?E2, tmp # ds1)"
        using lowered_ok_scope[OF d] expr_ok_mono[OF lowered_ok_env_le'[OF d] dimoff] lt
        by (intro copy_ok[where dty = CTy_CharPtr and sty = CTy_CharPtr]) (auto simp: expr_ok_def)
      have res': "expr_ok ?E2 (ME_AddrOf tmp) (res_cty ty)" using res nlen ty by (simp add: expr_ok_def res_cty_def)
      have lo: "lowered_ok prog rt (E, ds) st S st' (?E2, tmp # ds1)"
        unfolding S using lowered_ok_append[OF lo1 lowered_ok_append[OF d cp]] by simp
      show ?thesis unfolding e using tyP lo res' by blast
    qed
  qed
qed


section \<open>Array literals, records, matches and calls\<close>

(* The element offsets of an array literal: k * size fits for k <= n. *)
lemma lit_array_size_ok:
  assumes "cg_ok prog E cg" and "is_well_kinded (CG_TyEnv cg) elemTy"
    and "fits (CG_TyEnv cg) (CoreTy_Array elemTy [CoreDim_Fixed (int n)])" and "k \<le> n"
  shows "u64_ok E (e_mul (cg_size cg elemTy) (u64_lit k))"
proof -
  have fe: "fits (CG_TyEnv cg) elemTy" using fits_Array_elem_fixed[OF assms(3)] by (simp add: dims_all_fixed_def)
  have sz: "u64_ok E (cg_size cg elemTy)" using cg_size_ok[OF assms(1,2) fe] .
  have bound: "n < u64_max" "type_size (CG_TyEnv cg) 0 (\<lambda>_. 0) elemTy * n < u64_max"
    using assms(3) unfolding fits_def size_fits_def type_size_def
    by (simp_all add: dims_all_fixed_def dims_count_def)
  have ev: "eval0 (cg_size cg elemTy) = type_size (CG_TyEnv cg) 0 (\<lambda>_. 0) elemTy"
    unfolding cg_size_def by (rule eval0_size_of)
  have lt: "eval0 (cg_size cg elemTy) * k < u64_max"
    unfolding ev by (rule le_less_trans[OF mult_le_mono2[OF assms(4)] bound(2)])
  show ?thesis using sz bound(1) assms(4) lt by (intro u64_ok_e_fold2) simp_all
qed

lemma lt_LitArray:
  assumes IH: "\<And>x st st' xa. fresh_name (CG_Fun cg) ''arr'' st = Inr (x, st') \<Longrightarrow> xa \<in> set tms \<Longrightarrow> lt_ok prog rt cg xa"
  shows "lt_ok prog rt cg (CoreTm_LitArray elemTy tms)"
  unfolding lt_ok_def
proof (intro allI impI)
  fix E ds st S e st'
  assume l: "lower_term cg (CoreTm_LitArray elemTy tms) st = Inr ((S, e), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and tf: "term_fits (CG_TyEnv cg) (CoreTm_LitArray elemTy tms)"
  let ?env = "CG_TyEnv cg"
  let ?n = "length tms"
  let ?sz = "\<lambda>k. e_mul (cg_size cg elemTy) (u64_lit k)"
  let ?store = "\<lambda>tmp. \<lambda>(k, e). store_at cg elemTy (ptr_add (ME_AddrOf tmp) (?sz k)) e"
  from term_fits_type[OF tf] obtain ty where tyP: "core_term_type ?env NotGhost (CoreTm_LitArray elemTy tms) = Some ty"
    and fa: "fits ?env ty" by blast
  note lat = lit_array_typed[OF tyP]
  have unf: "lower_term cg (CoreTm_LitArray elemTy tms) st =
      cg_bind (fresh_name (CG_Fun cg) ''arr'')
        (\<lambda>tmp. cg_bind (cg_mapM (lower_term cg) tms)
          (\<lambda>rs. cg_return ([MS_DeclBuf tmp (buf_size (?sz ?n))] @ concat (map fst rs)
                             @ map (?store tmp) (zip [0..<?n] (map snd rs)), ME_AddrOf tmp))) st"
    unfolding lower_term.simps by (simp add: cg_bind_def)
  from l[unfolded unf] obtain tmp st1 where fr: "fresh_name (CG_Fun cg) ''arr'' st = Inr (tmp, st1)"
    and r1: "cg_bind (cg_mapM (lower_term cg) tms)
          (\<lambda>rs. cg_return ([MS_DeclBuf tmp (buf_size (?sz ?n))] @ concat (map fst rs)
                             @ map (?store tmp) (zip [0..<?n] (map snd rs)), ME_AddrOf tmp)) st1 = Inr ((S, e), st')"
    by (rule cg_bind_InrE)
  from r1 obtain rs st2 where lm: "cg_mapM (lower_term cg) tms st1 = Inr (rs, st2)"
    and r2: "cg_return ([MS_DeclBuf tmp (buf_size (?sz ?n))] @ concat (map fst rs)
                             @ map (?store tmp) (zip [0..<?n] (map snd rs)), ME_AddrOf tmp) st2 = Inr ((S, e), st')"
    by (rule cg_bind_InrE)
  from r2 have S: "S = [MS_DeclBuf tmp (buf_size (?sz ?n))] @ concat (map fst rs) @ map (?store tmp) (zip [0..<?n] (map snd rs))"
    and e: "e = ME_AddrOf tmp" and st': "st' = st2" by (auto simp: cg_return_def)
  note lm = lm[folded st']
  have ewk: "is_well_kinded ?env elemTy" using term_type_wk(1)[OF ok tyP] unfolding lat(1) by simp
  have fe: "fits ?env elemTy" using fits_Array_elem_fixed[OF fa[unfolded lat(1)]] by (simp add: dims_all_fixed_def)
  have szk: "\<And>E k. cg_ok prog E cg \<Longrightarrow> k \<le> ?n \<Longrightarrow> u64_ok E (?sz k)"
    by (rule lit_array_size_ok[OF _ ewk fa[unfolded lat(1)]])
  let ?E1 = "fmupd tmp VT_Buf E"
  have d: "lowered_ok prog rt (E, ds) st [MS_DeclBuf tmp (buf_size (?sz ?n))] st1 (?E1, tmp # ds)"
    by (rule fresh_buf_ok[OF sc fr buf_size_ok[OF szk[OF ok order_refl]]])
  have le1: "env_le E ?E1" by (rule lowered_ok_env_le'[OF d])
  have ok1: "cg_ok prog ?E1 cg" using cg_ok_mono[OF le1 ok] .
  have sc1: "scope_ok prog (?E1, tmp # ds) st1" by (rule lowered_ok_scope[OF d])
  have tmp1: "expr_ok ?E1 (ME_AddrOf tmp) CTy_CharPtr" by (simp add: expr_ok_def)
  have "\<exists>E' ds'. lowered_ok prog rt (?E1, tmp # ds) st1 (concat (map fst rs)) st' (E', ds')
          \<and> (\<forall>r \<in> set rs. expr_ok E' (snd r) (res_cty elemTy))"
  proof (rule cg_mapM_chain[OF lm sc1])
    fix t sta r stb Ea dsa
    assume t: "t \<in> set tms" and lt: "lower_term cg t sta = Inr (r, stb)" and sca: "scope_ok prog (Ea, dsa) sta" and le: "env_le ?E1 Ea"
    obtain S1 e1 where r: "r = (S1, e1)" by (cases r)
    obtain E2 ds2 ty2 where ty2: "core_term_type ?env NotGhost t = Some ty2"
      and lo: "lowered_ok prog rt (Ea, dsa) sta S1 stb (E2, ds2)" and e1: "expr_ok E2 e1 (res_cty ty2)"
      by (rule lt_okD[OF IH[OF fr t] lt[unfolded r] cg_ok_mono[OF le ok1] sca term_fits_LitArray[OF tf t]])
    have "ty2 = elemTy" using lat(2) t ty2 by simp
    then show "\<exists>E2 ds2. lowered_ok prog rt (Ea, dsa) sta (fst r) stb (E2, ds2) \<and> expr_ok E2 (snd r) (res_cty elemTy)"
      using lo e1 unfolding r by auto
  next
    fix E1 E2 r assume "env_le E1 E2" "expr_ok E1 (snd r) (res_cty elemTy)"
    then show "expr_ok E2 (snd r) (res_cty elemTy)" by (rule expr_ok_mono)
  qed
  then obtain E2 ds2 where lo2: "lowered_ok prog rt (?E1, tmp # ds) st1 (concat (map fst rs)) st' (E2, ds2)"
    and els: "\<forall>r \<in> set rs. expr_ok E2 (snd r) (res_cty elemTy)" by blast
  have le2: "env_le ?E1 E2" by (rule lowered_ok_env_le'[OF lo2])
  have ok2: "cg_ok prog E2 cg" using cg_ok_mono[OF le2 ok1] .
  have tmp2: "expr_ok E2 (ME_AddrOf tmp) CTy_CharPtr" using expr_ok_mono[OF le2 tmp1] .
  have esz: "u64_ok E2 (cg_size cg elemTy)" using cg_size_ok[OF ok2 ewk fe] .
  have stores: "lowered_ok prog rt (E2, ds2) st' (map (?store tmp) (zip [0..<?n] (map snd rs))) st' (E2, ds2)"
  proof (rule lowered_ok_pure_list[OF lowered_ok_scope[OF lo2]])
    fix s assume "s \<in> set (map (?store tmp) (zip [0..<?n] (map snd rs)))"
    then obtain p where p: "p \<in> set (zip [0..<?n] (map snd rs))" and s: "s = ?store tmp p" by auto
    obtain k e1 where pk: "p = (k, e1)" by (cases p)
    have k: "k < ?n" using set_zip_leftD[OF p[unfolded pk]] by simp
    have e1: "e1 \<in> set (map snd rs)" using set_zip_rightD[OF p[unfolded pk]] .
    have e1ok: "expr_ok E2 e1 (res_cty elemTy)" using els e1 by auto
    have dst: "expr_ok E2 (ptr_add (ME_AddrOf tmp) (?sz k)) CTy_CharPtr"
      using tmp2 szk[OF ok2, of k] k by (intro expr_ok_ptr_add) auto
    show "lowered_ok prog rt (E2, ds2) st' [s] st' (E2, ds2)"
      unfolding s pk using store_at_ok[OF lowered_ok_scope[OF lo2] dst e1ok esz] by simp
  qed
  have res: "expr_ok E2 (ME_AddrOf tmp) (res_cty ty)" using tmp2 unfolding lat(1) by (simp add: res_cty_def)
  have lo: "lowered_ok prog rt (E, ds) st S st' (E2, ds2)"
    unfolding S using lowered_ok_append[OF lowered_ok_append[OF d lo2] stores] by simp
  show "\<exists>E' ds' ty. core_term_type ?env NotGhost (CoreTm_LitArray elemTy tms) = Some ty
          \<and> lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e (res_cty ty)"
    unfolding e using tyP res lo by blast
qed

lemma lt_Record:
  assumes IH: "\<And>x st st' x6 xa sta st'a xb xc y xd stb st'b.
        ty_of cg (CoreTm_Record flds) st = Inr (x, st') \<Longrightarrow> x = CoreTy_Record x6 \<Longrightarrow>
        fresh_name (CG_Fun cg) ''rec'' sta = Inr (xa, st'a) \<Longrightarrow> xb \<in> set flds \<Longrightarrow> (xc, y) = xb \<Longrightarrow>
        cg_lift (CG_Fun cg) ''unknown field'' (map_of x6 xc) stb = Inr (xd, st'b) \<Longrightarrow> lt_ok prog rt cg y"
  shows "lt_ok prog rt cg (CoreTm_Record flds)"
  unfolding lt_ok_def
proof (intro allI impI)
  fix E ds st S e st'
  assume l: "lower_term cg (CoreTm_Record flds) st = Inr ((S, e), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and tf: "term_fits (CG_TyEnv cg) (CoreTm_Record flds)"
  let ?env = "CG_TyEnv cg"
  from term_fits_type[OF tf] obtain recTy where tyP: "core_term_type ?env NotGhost (CoreTm_Record flds) = Some recTy"
    and fr: "fits ?env recTy" by blast
  obtain fldTys where rec: "recTy = CoreTy_Record fldTys" using tyP by (auto split: option.splits if_splits)
  let ?fld = "\<lambda>tmp. \<lambda>(f, t). cg_bind (cg_lift (CG_Fun cg) ''unknown field'' (map_of fldTys f))
                 (\<lambda>fty. cg_bind (lower_term cg t)
                   (\<lambda>(S, e). cg_return (S @ [store_at cg fty (ptr_add (ME_AddrOf tmp) (field_off ?env fldTys f)) e])))"
  have unf: "lower_term cg (CoreTm_Record flds) st =
      cg_bind (fresh_name (CG_Fun cg) ''rec'')
        (\<lambda>tmp. cg_bind (cg_mapM (?fld tmp) flds)
          (\<lambda>rs. cg_return ([MS_DeclBuf tmp (buf_size (cg_size cg recTy))] @ concat rs, ME_AddrOf tmp))) st"
    unfolding lower_term.simps by (simp add: cg_bind_def ty_of_Some[OF tyP] rec)
  from l[unfolded unf] obtain tmp st1 where fn: "fresh_name (CG_Fun cg) ''rec'' st = Inr (tmp, st1)"
    and r1: "cg_bind (cg_mapM (?fld tmp) flds)
          (\<lambda>rs. cg_return ([MS_DeclBuf tmp (buf_size (cg_size cg recTy))] @ concat rs, ME_AddrOf tmp)) st1 = Inr ((S, e), st')"
    by (rule cg_bind_InrE)
  from r1 obtain rs st2 where lm: "cg_mapM (?fld tmp) flds st1 = Inr (rs, st2)"
    and r2: "cg_return ([MS_DeclBuf tmp (buf_size (cg_size cg recTy))] @ concat rs, ME_AddrOf tmp) st2 = Inr ((S, e), st')"
    by (rule cg_bind_InrE)
  from r2 have S: "S = [MS_DeclBuf tmp (buf_size (cg_size cg recTy))] @ concat rs"
    and e: "e = ME_AddrOf tmp" and st': "st' = st2" by (auto simp: cg_return_def)
  note lm = lm[folded st']
  have rwk: "is_well_kinded ?env recTy" using term_type_wk(1)[OF ok tyP] .
  have sz: "u64_ok E (buf_size (cg_size cg recTy))" using cg_buf_size_ok[OF ok rwk fr] .
  let ?E1 = "fmupd tmp VT_Buf E"
  have d: "lowered_ok prog rt (E, ds) st [MS_DeclBuf tmp (buf_size (cg_size cg recTy))] st1 (?E1, tmp # ds)"
    by (rule fresh_buf_ok[OF sc fn sz])
  have le1: "env_le E ?E1" by (rule lowered_ok_env_le'[OF d])
  have ok1: "cg_ok prog ?E1 cg" using cg_ok_mono[OF le1 ok] .
  have sc1: "scope_ok prog (?E1, tmp # ds) st1" by (rule lowered_ok_scope[OF d])
  have tmp1: "expr_ok ?E1 (ME_AddrOf tmp) CTy_CharPtr" by (simp add: expr_ok_def)
  have "\<exists>E' ds'. lowered_ok prog rt (?E1, tmp # ds) st1 (concat (map (\<lambda>y. y) rs)) st' (E', ds') \<and> (\<forall>y \<in> set rs. True)"
  proof (rule cg_mapM_chain[OF lm sc1])
    fix x sta y stb Ea dsa
    assume x: "x \<in> set flds" and fx: "?fld tmp x sta = Inr (y, stb)" and sca: "scope_ok prog (Ea, dsa) sta" and le: "env_le ?E1 Ea"
    obtain f t where xft: "x = (f, t)" by (cases x)
    obtain fty where mo: "map_of fldTys f = Some fty" and tt: "core_term_type ?env NotGhost t = Some fty"
      using record_field_typed[OF tyP[unfolded rec] x[unfolded xft]] by blast
    have fx': "cg_bind (cg_lift (CG_Fun cg) ''unknown field'' (map_of fldTys f))
                 (\<lambda>fty. cg_bind (lower_term cg t)
                   (\<lambda>(S, e). cg_return (S @ [store_at cg fty (ptr_add (ME_AddrOf tmp) (field_off ?env fldTys f)) e]))) sta = Inr (y, stb)"
      using fx unfolding xft by simp
    from fx' obtain fty' sta1 where cl: "cg_lift (CG_Fun cg) ''unknown field'' (map_of fldTys f) sta = Inr (fty', sta1)"
      and r3: "cg_bind (lower_term cg t)
                   (\<lambda>(S, e). cg_return (S @ [store_at cg fty' (ptr_add (ME_AddrOf tmp) (field_off ?env fldTys f)) e])) sta1 = Inr (y, stb)"
      by (rule cg_bind_InrE)
    have fty': "fty' = fty" and sta1: "sta1 = sta" using cl mo by (simp_all add: cg_lift_Inr)
    from r3 obtain r stb' where lt': "lower_term cg t sta1 = Inr (r, stb')"
      and r4: "(\<lambda>(S, e). cg_return (S @ [store_at cg fty' (ptr_add (ME_AddrOf tmp) (field_off ?env fldTys f)) e])) r stb' = Inr (y, stb)"
      by (rule cg_bind_InrE)
    obtain S1 e1 where r: "r = (S1, e1)" by (cases r)
    from r4 have y: "y = S1 @ [store_at cg fty (ptr_add (ME_AddrOf tmp) (field_off ?env fldTys f)) e1]" and stb: "stb = stb'"
      unfolding r fty' by (auto simp: cg_return_def)
    have lt: "lower_term cg t sta = Inr ((S1, e1), stb)" using lt' unfolding r sta1 stb .
    obtain E2 ds2 ty2 where ty2: "core_term_type ?env NotGhost t = Some ty2"
      and lo: "lowered_ok prog rt (Ea, dsa) sta S1 stb (E2, ds2)" and e1: "expr_ok E2 e1 (res_cty ty2)"
      by (rule lt_okD[OF IH[OF ty_of_Some[OF tyP] rec fn x xft[symmetric] cl] lt cg_ok_mono[OF le ok1] sca term_fits_Record[OF tf x[unfolded xft]]])
    have ty2: "ty2 = fty" using ty2 tt by simp
    have le2: "env_le Ea E2" by (rule lowered_ok_env_le'[OF lo])
    have ok2: "cg_ok prog E2 cg" using cg_ok_mono[OF le2 cg_ok_mono[OF le ok1]] .
    have dst: "expr_ok E2 (ptr_add (ME_AddrOf tmp) (field_off ?env fldTys f)) CTy_CharPtr"
      using expr_ok_mono[OF le2 expr_ok_mono[OF le tmp1]] cg_field_off_ok[OF ok2 rwk[unfolded rec] fr[unfolded rec]]
      by (intro expr_ok_ptr_add) auto
    have fsz: "u64_ok E2 (cg_size cg fty)"
      using cg_size_ok[OF ok2 term_type_wk(1)[OF ok tt] fits_Record_fld[OF fr[unfolded rec] mo]] .
    have st: "lowered_ok prog rt (E2, ds2) stb [store_at cg fty (ptr_add (ME_AddrOf tmp) (field_off ?env fldTys f)) e1] stb (E2, ds2)"
      using store_at_ok[OF lowered_ok_scope[OF lo] dst e1[unfolded ty2] fsz] .
    show "\<exists>E2 ds2. lowered_ok prog rt (Ea, dsa) sta ((\<lambda>y. y) y) stb (E2, ds2) \<and> True"
      unfolding y using lowered_ok_append[OF lo st] by auto
  next
    show "\<And>E1 E2 y. env_le E1 E2 \<Longrightarrow> True \<Longrightarrow> True" by simp
  qed
  then obtain E2 ds2 where lo2: "lowered_ok prog rt (?E1, tmp # ds) st1 (concat rs) st' (E2, ds2)" by auto
  have res: "expr_ok E2 (ME_AddrOf tmp) (res_cty recTy)"
    using expr_ok_mono[OF lowered_ok_env_le'[OF lo2] tmp1] rec by (simp add: res_cty_def)
  have lo: "lowered_ok prog rt (E, ds) st S st' (E2, ds2)" unfolding S using lowered_ok_append[OF d lo2] by simp
  show "\<exists>E' ds' ty. core_term_type ?env NotGhost (CoreTm_Record flds) = Some ty
          \<and> lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e (res_cty ty)"
    unfolding e using tyP res lo by blast
qed

lemma lt_Match:
  assumes IHs: "\<And>x st st' xa sta st'a. ty_of cg s st = Inr (x, st') \<Longrightarrow> ty_of cg (CoreTm_Match s arms) sta = Inr (xa, st'a) \<Longrightarrow> lt_ok prog rt cg s"
    and IHb: "\<And>x st st' xa sta st'a xb stb st'b xc y xba stc st'c xbb ya xbc std st'd xbd yb xbe xbf yc xbg ste st'e.
        ty_of cg s st = Inr (x, st') \<Longrightarrow> ty_of cg (CoreTm_Match s arms) sta = Inr (xa, st'a) \<Longrightarrow>
        lower_term cg s stb = Inr (xb, st'b) \<Longrightarrow> (xc, y) = xb \<Longrightarrow>
        match_tag cg x y stc = Inr (xba, st'c) \<Longrightarrow> (xbb, ya) = xba \<Longrightarrow>
        temp_for cg ''res'' xa std = Inr (xbc, st'd) \<Longrightarrow> (xbd, yb) = xbc \<Longrightarrow>
        xbe \<in> set arms \<Longrightarrow> (xbf, yc) = xbe \<Longrightarrow> arm_cond cg x ya xbf ste = Inr (xbg, st'e) \<Longrightarrow> lt_ok prog rt cg yc"
  shows "lt_ok prog rt cg (CoreTm_Match s arms)"
  unfolding lt_ok_def
proof (intro allI impI)
  fix E ds st S e st'
  assume l: "lower_term cg (CoreTm_Match s arms) st = Inr ((S, e), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and tf: "term_fits (CG_TyEnv cg) (CoreTm_Match s arms)"
  let ?env = "CG_TyEnv cg"
  from term_fits_type[OF tf] obtain resTy where tyP: "core_term_type ?env NotGhost (CoreTm_Match s arms) = Some resTy"
    and fres: "fits ?env resTy" by blast
  obtain scrutTy where ts: "core_term_type ?env NotGhost s = Some scrutTy"
    and arms_ty: "\<forall>(p, body) \<in> set arms. pattern_compatible ?env p scrutTy \<and> core_term_type ?env NotGhost body = Some resTy"
    by (rule match_typed[OF tyP])
  note tfs = term_fits_Match[OF tf]
  have rwk: "is_well_kinded ?env resTy" using term_type_wk(1)[OF ok tyP] .
  let ?arm = "\<lambda>tag res. \<lambda>(pat, body). cg_bind (arm_cond cg scrutTy tag pat)
                 (\<lambda>c. cg_bind (lower_term cg body)
                   (\<lambda>(Sb, eb). cg_return (c, Sb @ [temp_store cg resTy res eb])))"
  have unf: "lower_term cg (CoreTm_Match s arms) st =
      cg_bind (lower_term cg s) (\<lambda>(Ss, es).
      cg_bind (match_tag cg scrutTy es) (\<lambda>(St, tag).
      cg_bind (temp_for cg ''res'' resTy) (\<lambda>(res, decl).
      cg_bind (cg_mapM (?arm tag res) arms) (\<lambda>armsL.
      cg_return (Ss @ St @ [decl] @ if_chain armsL, temp_result resTy res))))) st"
    unfolding lower_term.simps by (simp add: cg_bind_def ty_of_Some[OF ts] ty_of_Some[OF tyP])
  from l[unfolded unf] obtain r1 st1 where ls': "lower_term cg s st = Inr (r1, st1)"
    and k1: "(\<lambda>(Ss, es). cg_bind (match_tag cg scrutTy es) (\<lambda>(St, tag).
      cg_bind (temp_for cg ''res'' resTy) (\<lambda>(res, decl).
      cg_bind (cg_mapM (?arm tag res) arms) (\<lambda>armsL.
      cg_return (Ss @ St @ [decl] @ if_chain armsL, temp_result resTy res))))) r1 st1 = Inr ((S, e), st')"
    by (rule cg_bind_InrE)
  obtain Ss es where r1: "r1 = (Ss, es)" by (cases r1)
  have ls: "lower_term cg s st = Inr ((Ss, es), st1)" using ls' r1 by simp
  from k1[unfolded r1 case_prod_conv] obtain r2 st2 where mt': "match_tag cg scrutTy es st1 = Inr (r2, st2)"
    and k2: "(\<lambda>(St, tag). cg_bind (temp_for cg ''res'' resTy) (\<lambda>(res, decl).
      cg_bind (cg_mapM (?arm tag res) arms) (\<lambda>armsL.
      cg_return (Ss @ St @ [decl] @ if_chain armsL, temp_result resTy res)))) r2 st2 = Inr ((S, e), st')"
    by (rule cg_bind_InrE)
  obtain St tag where r2: "r2 = (St, tag)" by (cases r2)
  have mt: "match_tag cg scrutTy es st1 = Inr ((St, tag), st2)" using mt' r2 by simp
  from k2[unfolded r2 case_prod_conv] obtain r3 st3 where tfr': "temp_for cg ''res'' resTy st2 = Inr (r3, st3)"
    and k3: "(\<lambda>(res, decl). cg_bind (cg_mapM (?arm tag res) arms) (\<lambda>armsL.
      cg_return (Ss @ St @ [decl] @ if_chain armsL, temp_result resTy res))) r3 st3 = Inr ((S, e), st')"
    by (rule cg_bind_InrE)
  obtain res decl where r3: "r3 = (res, decl)" by (cases r3)
  have tfr: "temp_for cg ''res'' resTy st2 = Inr ((res, decl), st3)" using tfr' r3 by simp
  from k3[unfolded r3 case_prod_conv] obtain armsL st4 where lm: "cg_mapM (?arm tag res) arms st3 = Inr (armsL, st4)"
    and k4: "cg_return (Ss @ St @ [decl] @ if_chain armsL, temp_result resTy res) st4 = Inr ((S, e), st')"
    by (rule cg_bind_InrE)
  from k4 have S: "S = Ss @ St @ [decl] @ if_chain armsL" and e: "e = temp_result resTy res" and st': "st' = st4"
    by (auto simp: cg_return_def)
  note lm = lm[folded st']
  (* the scrutinee *)
  obtain E1 ds1 ty1 where ty1: "core_term_type ?env NotGhost s = Some ty1"
    and lo1: "lowered_ok prog rt (E, ds) st Ss st1 (E1, ds1)" and es: "expr_ok E1 es (res_cty ty1)"
    by (rule lt_okD[OF IHs[OF ty_of_Some[OF ts] ty_of_Some[OF tyP]] ls ok sc tfs[THEN conjunct1]])
  have ty1: "ty1 = scrutTy" using ty1 ts by simp
  (* the tag *)
  obtain E2 ds2 where lo2: "lowered_ok prog rt (E1, ds1) st1 St st2 (E2, ds2)" and tag: "expr_ok E2 tag (tag_cty ?env scrutTy)"
    using match_tag_ok[OF mt lowered_ok_scope[OF lo1] es[unfolded ty1]] by blast
  have ok2: "cg_ok prog E2 cg" using cg_ok_mono[OF lowered_ok_env_le'[OF lo2] cg_ok_mono[OF lowered_ok_env_le'[OF lo1] ok]] .
  (* the result temporary *)
  from temp_for_ok[OF tfr ok2 lowered_ok_scope[OF lo2] rwk fres] obtain E3 where
    d: "lowered_ok prog rt (E2, ds2) st2 [decl] st3 (E3, res # ds2)"
    and resE: "expr_ok E3 (temp_result resTy res) (res_cty resTy)"
    and lk: "fmlookup E3 res = Some (case scalar_ty resTy of Some cty \<Rightarrow> VT_Scalar cty | None \<Rightarrow> VT_Buf)"
    by blast
  have le3: "env_le E2 E3" by (rule lowered_ok_env_le'[OF d])
  have ok3: "cg_ok prog E3 cg" using cg_ok_mono[OF le3 ok2] .
  have tag3: "expr_ok E3 tag (tag_cty ?env scrutTy)" using expr_ok_mono[OF le3 tag] .
  have sc3: "scope_ok prog (E3, res # ds2) st3" by (rule lowered_ok_scope[OF d])
  (* the arms *)
  have arms: "(\<forall>(c, Sb) \<in> set armsL. (\<forall>ce. c = Some ce \<longrightarrow> expr_ok E3 ce CTy_U8)
                \<and> stmts_ok (mk_ctx prog rt) (E3, []) Sb \<noteq> None \<and> (\<forall>l. stmts_wf prog l Sb)) \<and> used_le st3 st'"
  proof (rule cg_mapM_same_scope[OF lm sc3])
    fix x sta y stb
    assume x: "x \<in> set arms" and fx: "?arm tag res x sta = Inr (y, stb)" and sca: "scope_ok prog (E3, res # ds2) sta"
    obtain pat body where xpb: "x = (pat, body)" by (cases x)
    have pc: "pattern_compatible ?env pat scrutTy" and bt: "core_term_type ?env NotGhost body = Some resTy"
      using arms_ty x unfolding xpb by auto
    have tfb: "term_fits ?env body" using tfs x unfolding xpb by auto
    have fx': "cg_bind (arm_cond cg scrutTy tag pat) (\<lambda>c. cg_bind (lower_term cg body)
                   (\<lambda>(Sb, eb). cg_return (c, Sb @ [temp_store cg resTy res eb]))) sta = Inr (y, stb)"
      using fx unfolding xpb by simp
    from fx' obtain c sta1 where ac: "arm_cond cg scrutTy tag pat sta = Inr (c, sta1)"
      and k5: "cg_bind (lower_term cg body) (\<lambda>(Sb, eb). cg_return (c, Sb @ [temp_store cg resTy res eb])) sta1 = Inr (y, stb)"
      by (rule cg_bind_InrE)
    have acok: "sta1 = sta \<and> (\<forall>ce. c = Some ce \<longrightarrow> expr_ok E3 ce CTy_U8)"
      by (rule arm_cond_ok[OF ac cg_ok_wf[OF ok] cg_ok_tags[OF ok] tag3 pc])
    from k5 obtain r stb' where lb': "lower_term cg body sta1 = Inr (r, stb')"
      and k6: "(\<lambda>(Sb, eb). cg_return (c, Sb @ [temp_store cg resTy res eb])) r stb' = Inr (y, stb)"
      by (rule cg_bind_InrE)
    obtain Sb eb where r: "r = (Sb, eb)" by (cases r)
    from k6 have y: "y = (c, Sb @ [temp_store cg resTy res eb])" and stb: "stb = stb'" unfolding r by (auto simp: cg_return_def)
    have lb: "lower_term cg body sta = Inr ((Sb, eb), stb)" using lb' acok unfolding r stb by simp
    have sca0: "scope_ok prog (E3, []) sta" using sca by (simp add: scope_ok_def)
    obtain E4 ds4 ty4 where ty4: "core_term_type ?env NotGhost body = Some ty4"
      and lo4: "lowered_ok prog rt (E3, []) sta Sb stb (E4, ds4)" and eb: "expr_ok E4 eb (res_cty ty4)"
      by (rule lt_okD[OF IHb[OF ty_of_Some[OF ts] ty_of_Some[OF tyP] ls refl mt refl tfr refl x xpb[symmetric] ac] lb ok3 sca0 tfb])
    have ty4: "ty4 = resTy" using ty4 bt by simp
    have le4: "env_le E3 E4" by (rule lowered_ok_env_le'[OF lo4])
    have tst: "lowered_ok prog rt (E4, ds4) stb [temp_store cg resTy res eb] stb (E4, ds4)"
      using temp_store_ok[OF lowered_ok_scope[OF lo4] env_le_lookup[OF le4 lk] eb[unfolded ty4]
                             cg_size_ok[OF cg_ok_mono[OF le4 ok3] rwk fres]] .
    have lo5: "lowered_ok prog rt (E3, []) sta (Sb @ [temp_store cg resTy res eb]) stb (E4, ds4)"
      by (rule lowered_ok_append[OF lo4 tst])
    show "(case y of (c, Sb) \<Rightarrow> (\<forall>ce. c = Some ce \<longrightarrow> expr_ok E3 ce CTy_U8)
                \<and> stmts_ok (mk_ctx prog rt) (E3, []) Sb \<noteq> None \<and> (\<forall>l. stmts_wf prog l Sb)) \<and> used_le sta stb"
      using acok lo5 unfolding y lowered_ok_def by simp
  qed
  have ic: "lowered_ok prog rt (E3, res # ds2) st3 (if_chain armsL) st' (E3, res # ds2)"
    using if_chain_ok[OF sc3 arms[THEN conjunct2] arms[THEN conjunct1]] .
  have lo: "lowered_ok prog rt (E, ds) st S st' (E3, res # ds2)"
    unfolding S using lowered_ok_append[OF lowered_ok_append[OF lowered_ok_append[OF lo1 lo2] d] ic] by simp
  show "\<exists>E' ds' ty. core_term_type ?env NotGhost (CoreTm_Match s arms) = Some ty
          \<and> lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e (res_cty ty)"
    unfolding e using tyP resE lo by blast
qed

lemma lt_FunctionCall:
  assumes IH: "\<And>x st st'. ty_of cg (CoreTm_FunctionCall f tys args) st = Inr (x, st') \<Longrightarrow> lc_ok prog rt cg f tys args"
  shows "lt_ok prog rt cg (CoreTm_FunctionCall f tys args)"
  unfolding lt_ok_def
proof (intro allI impI)
  fix E ds st S e st'
  assume l: "lower_term cg (CoreTm_FunctionCall f tys args) st = Inr ((S, e), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and tf: "term_fits (CG_TyEnv cg) (CoreTm_FunctionCall f tys args)"
  let ?env = "CG_TyEnv cg"
  from term_fits_type[OF tf] obtain rty where tyP: "core_term_type ?env NotGhost (CoreTm_FunctionCall f tys args) = Some rty"
    and frty: "fits ?env rty" by blast
  obtain info where info: "fmlookup (TE_Functions ?env) f = Some info" using tyP by (auto split: option.splits)
  have ngp: "no_ghost_params info" using cg_ok_prog[OF ok] info unfolding prog_ok_def by blast
  note ct = call_typed_pure[OF tyP info ngp]
  have unf: "lower_term cg (CoreTm_FunctionCall f tys args) st =
      cg_bind (lower_call cg f tys args) (\<lambda>(S, res).
        (case call_result_expr rty res of
           Some e \<Rightarrow> cg_return (S, e)
         | None \<Rightarrow> cg_bind (fresh_name (CG_Fun cg) ''unit'') (\<lambda>tmp. cg_return (S @ [MS_DeclBuf tmp (u64_lit 1)], ME_AddrOf tmp)))) st"
    unfolding lower_term.simps by (simp add: cg_bind_def ty_of_Some[OF tyP])
  from l[unfolded unf] obtain r1 st1 where lc': "lower_call cg f tys args st = Inr (r1, st1)"
    and k1: "(\<lambda>(S, res). (case call_result_expr rty res of
           Some e \<Rightarrow> cg_return (S, e)
         | None \<Rightarrow> cg_bind (fresh_name (CG_Fun cg) ''unit'') (\<lambda>tmp. cg_return (S @ [MS_DeclBuf tmp (u64_lit 1)], ME_AddrOf tmp)))) r1 st1 = Inr ((S, e), st')"
    by (rule cg_bind_InrE)
  obtain S1 res where r1: "r1 = (S1, res)" by (cases r1)
  have lc: "lower_call cg f tys args st = Inr ((S1, res), st1)" using lc' r1 by simp
  note tfs = term_fits_FunctionCall[OF tf]
  obtain E1 ds1 where lo1: "lowered_ok prog rt (E, ds) st S1 st1 (E1, ds1)" and ro: "res_ok E1 info res"
    by (rule lc_okD[OF IH[OF ty_of_Some[OF tyP]] lc ok sc info ct(1) tfs[THEN conjunct1] tfs[THEN conjunct2]
                       term_type_wk(1)[OF ok tyP, unfolded ct(2)] frty[unfolded ct(2)]])
  show "\<exists>E' ds' ty. core_term_type ?env NotGhost (CoreTm_FunctionCall f tys args) = Some ty
          \<and> lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> expr_ok E' e (res_cty ty)"
  proof (cases "call_result_expr rty res")
    case (Some e1)
    have Se: "S = S1" "e = e1" "st' = st1" using k1 Some unfolding r1 by (simp_all add: cg_return_def)
    have res1: "expr_ok E1 e1 (res_cty rty)" unfolding ct(2) by (rule call_result_expr_ok[OF ro Some[unfolded ct(2)]])
    show ?thesis unfolding Se using tyP lo1 res1 by blast
  next
    case None
    then have ru: "res = CR_Unit" by (simp add: call_result_expr_None)
    have k1': "cg_bind (fresh_name (CG_Fun cg) ''unit'') (\<lambda>tmp. cg_return (S1 @ [MS_DeclBuf tmp (u64_lit 1)], ME_AddrOf tmp)) st1 = Inr ((S, e), st')"
      using k1 None unfolding r1 by simp
    from k1' obtain tmp st2 where fr: "fresh_name (CG_Fun cg) ''unit'' st1 = Inr (tmp, st2)"
      and k2: "cg_return (S1 @ [MS_DeclBuf tmp (u64_lit 1)], ME_AddrOf tmp) st2 = Inr ((S, e), st')"
      by (rule cg_bind_InrE)
    from k2 have S: "S = S1 @ [MS_DeclBuf tmp (u64_lit 1)]" and e: "e = ME_AddrOf tmp" and st': "st' = st2"
      by (auto simp: cg_return_def)
    note fr = fr[folded st']
    have d: "lowered_ok prog rt (E1, ds1) st1 [MS_DeclBuf tmp (u64_lit 1)] st' (fmupd tmp VT_Buf E1, tmp # ds1)"
      by (rule fresh_buf_ok[OF lowered_ok_scope[OF lo1] fr]) (simp add: u64_max_def)
    have unit: "ret_kind (FI_ReturnType info) = RK_Unit" using ro ru by simp
    have "FI_ReturnType info = CoreTy_Record []" using unit by (auto simp: ret_kind_def split: option.splits if_splits)
    then have "rty = CoreTy_Record []" using ct(2) by simp
    then have res: "expr_ok (fmupd tmp VT_Buf E1) (ME_AddrOf tmp) (res_cty rty)" by (simp add: expr_ok_def res_cty_def)
    have lo: "lowered_ok prog rt (E, ds) st S st' (fmupd tmp VT_Buf E1, tmp # ds1)"
      unfolding S using lowered_ok_append[OF lo1 d] by simp
    show ?thesis unfolding e using tyP lo res by blast
  qed
qed

lemma lc_call:
  assumes IHa: "\<And>x st st' xa sta st'a xaa xab stb st'b xac y xad ya xae yb xaf xb yc xc yd xd ye.
        cg_lift (CG_Fun cg) (''unknown function '' @ f) (fmlookup (TE_Functions (CG_TyEnv cg)) f) st = Inr (x, st') \<Longrightarrow>
        (if length args \<noteq> length (FI_TmArgs x) \<or> length tys \<noteq> length (FI_TyArgs x)
         then internal cg (''wrong number of arguments in a call of '' @ f) else cg_return ()) sta = Inr (xa, st'a) \<Longrightarrow>
        xaa = fmap_of_list (zip (FI_TyArgs x) tys) \<Longrightarrow>
        (case ret_kind (FI_ReturnType x) of
           RK_Scalar cty \<Rightarrow> cg_bind (fresh_name (CG_Fun cg) ''call'') (\<lambda>x. cg_return ([MS_DeclScalar x cty], [], Some x, CR_Scalar (ME_Var x)))
         | RK_Unit \<Rightarrow> cg_return ([], [], None, CR_Unit)
         | RK_Buf \<Rightarrow> cg_bind (fresh_name (CG_Fun cg) ''ret'')
               (\<lambda>r. cg_return ([MS_DeclBuf r (buf_size (cg_size cg (apply_subst xaa (FI_ReturnType x))))], [ME_AddrOf r], None, CR_Place (ME_AddrOf r)))) stb = Inr (xab, st'b) \<Longrightarrow>
        (xac, y) = xab \<Longrightarrow> (xad, ya) = y \<Longrightarrow> (xae, yb) = ya \<Longrightarrow>
        xaf \<in> set (zip args (FI_TmArgs x)) \<Longrightarrow> (xb, yc) = xaf \<Longrightarrow> (xc, yd) = yc \<Longrightarrow> (xd, ye) = yd \<Longrightarrow> param_by_ptr xc xd \<Longrightarrow>
        la_ok prog rt cg xb"
    and IHt: "\<And>x st st' xa sta st'a xaa xab stb st'b xac y xad ya xae yb xaf xb yc xc yd xd ye.
        cg_lift (CG_Fun cg) (''unknown function '' @ f) (fmlookup (TE_Functions (CG_TyEnv cg)) f) st = Inr (x, st') \<Longrightarrow>
        (if length args \<noteq> length (FI_TmArgs x) \<or> length tys \<noteq> length (FI_TyArgs x)
         then internal cg (''wrong number of arguments in a call of '' @ f) else cg_return ()) sta = Inr (xa, st'a) \<Longrightarrow>
        xaa = fmap_of_list (zip (FI_TyArgs x) tys) \<Longrightarrow>
        (case ret_kind (FI_ReturnType x) of
           RK_Scalar cty \<Rightarrow> cg_bind (fresh_name (CG_Fun cg) ''call'') (\<lambda>x. cg_return ([MS_DeclScalar x cty], [], Some x, CR_Scalar (ME_Var x)))
         | RK_Unit \<Rightarrow> cg_return ([], [], None, CR_Unit)
         | RK_Buf \<Rightarrow> cg_bind (fresh_name (CG_Fun cg) ''ret'')
               (\<lambda>r. cg_return ([MS_DeclBuf r (buf_size (cg_size cg (apply_subst xaa (FI_ReturnType x))))], [ME_AddrOf r], None, CR_Place (ME_AddrOf r)))) stb = Inr (xab, st'b) \<Longrightarrow>
        (xac, y) = xab \<Longrightarrow> (xad, ya) = y \<Longrightarrow> (xae, yb) = ya \<Longrightarrow>
        xaf \<in> set (zip args (FI_TmArgs x)) \<Longrightarrow> (xb, yc) = xaf \<Longrightarrow> (xc, yd) = yc \<Longrightarrow> (xd, ye) = yd \<Longrightarrow> \<not> param_by_ptr xc xd \<Longrightarrow>
        lt_ok prog rt cg xb"
  shows "lc_ok prog rt cg f tys args"
  unfolding lc_ok_def
proof (intro allI impI)
  fix E ds st S res st' info
  assume l: "lower_call cg f tys args st = Inr ((S, res), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and info: "fmlookup (TE_Functions (CG_TyEnv cg)) f = Some info"
    and cat: "call_args_typed (CG_TyEnv cg) info tys args"
    and tfa: "\<forall>t \<in> set args. term_fits (CG_TyEnv cg) t" and ftys: "\<forall>ty \<in> set tys. fits (CG_TyEnv cg) ty"
    and rwk: "is_well_kinded (CG_TyEnv cg) (apply_subst (fmap_of_list (zip (FI_TyArgs info) tys)) (FI_ReturnType info))"
    and rf: "fits (CG_TyEnv cg) (apply_subst (fmap_of_list (zip (FI_TyArgs info) tys)) (FI_ReturnType info))"
  let ?env = "CG_TyEnv cg"
  let ?subst = "fmap_of_list (zip (FI_TyArgs info) tys)"
  let ?retTy = "apply_subst ?subst (FI_ReturnType info)"
  have lens: "length args = length (FI_TmArgs info)" "length tys = length (FI_TyArgs info)"
    using cat unfolding call_args_typed_def by simp_all
  have cl: "cg_lift (CG_Fun cg) (''unknown function '' @ f) (fmlookup (TE_Functions ?env) f) st = Inr (info, st)"
    using info by (simp add: cg_lift_Inr)
  let ?chk = "(if length args \<noteq> length (FI_TmArgs info) \<or> length tys \<noteq> length (FI_TyArgs info)
               then internal cg (''wrong number of arguments in a call of '' @ f) else cg_return ())"
  have chk: "?chk st = Inr ((), st)" using lens by (simp add: cg_return_def)
  let ?retK = "(case ret_kind (FI_ReturnType info) of
           RK_Scalar cty \<Rightarrow> cg_bind (fresh_name (CG_Fun cg) ''call'') (\<lambda>x. cg_return ([MS_DeclScalar x cty], [], Some x, CR_Scalar (ME_Var x)))
         | RK_Unit \<Rightarrow> cg_return ([], [], None, CR_Unit)
         | RK_Buf \<Rightarrow> cg_bind (fresh_name (CG_Fun cg) ''ret'')
               (\<lambda>r. cg_return ([MS_DeclBuf r (buf_size (cg_size cg ?retTy))], [ME_AddrOf r], None, CR_Place (ME_AddrOf r))))"
  let ?argf = "\<lambda>(a, (pty, vor, _)). if param_by_ptr pty vor then lower_addr cg a else lower_term cg a"
  have unf: "lower_call cg f tys args st =
      cg_bind ?retK (\<lambda>(Sret, retArgs, xopt, res).
      cg_bind (cg_mapM ?argf (zip args (FI_TmArgs info))) (\<lambda>argsL.
      cg_return (Sret @ concat (map fst argsL) @ [MS_Call xopt f (retArgs @ map (cg_size cg) tys @ map snd argsL)], res))) st"
    unfolding lower_call.simps cg_bind_def cl by (simp add: lens cg_return_def Let_def)
  from l[unfolded unf] obtain r1 st1 where rk': "?retK st = Inr (r1, st1)"
    and k1: "(\<lambda>(Sret, retArgs, xopt, res). cg_bind (cg_mapM ?argf (zip args (FI_TmArgs info))) (\<lambda>argsL.
      cg_return (Sret @ concat (map fst argsL) @ [MS_Call xopt f (retArgs @ map (cg_size cg) tys @ map snd argsL)], res))) r1 st1 = Inr ((S, res), st')"
    by (rule cg_bind_InrE)
  obtain Sret retArgs xopt res1 where r1: "r1 = (Sret, retArgs, xopt, res1)" by (rule prod_cases4)
  have rk: "?retK st = Inr ((Sret, retArgs, xopt, res1), st1)" using rk' r1 by simp
  from k1[unfolded r1 case_prod_conv] obtain argsL st2 where lm: "cg_mapM ?argf (zip args (FI_TmArgs info)) st1 = Inr (argsL, st2)"
    and k2: "cg_return (Sret @ concat (map fst argsL) @ [MS_Call xopt f (retArgs @ map (cg_size cg) tys @ map snd argsL)], res1) st2 = Inr ((S, res), st')"
    by (rule cg_bind_InrE)
  from k2 have S: "S = Sret @ concat (map fst argsL) @ [MS_Call xopt f (retArgs @ map (cg_size cg) tys @ map snd argsL)]"
    and res: "res = res1" and st': "st' = st2" by (auto simp: cg_return_def)
  note lm = lm[folded st']
  (* the function's prototype *)
  obtain fn where fn: "lookup_fun prog f = Some fn" and params: "map snd (MF_Params fn) = param_ctys info"
    and mret: "MF_Ret fn = rk_cty (ret_kind (FI_ReturnType info))"
    using cg_ok_prog[OF ok] info unfolding prog_ok_def by blast
  (* the return kind *)
  have retk: "\<exists>E1 ds1. lowered_ok prog rt (E, ds) st Sret st1 (E1, ds1) \<and> res_ok E1 info res1
          \<and> list_all2 (\<lambda>e cty. expr_ok E1 e cty) retArgs (case ret_kind (FI_ReturnType info) of RK_Buf \<Rightarrow> [CTy_CharPtr] | _ \<Rightarrow> [])
          \<and> (case xopt of None \<Rightarrow> True
               | Some x \<Rightarrow> (\<exists>rty ty. MF_Ret fn = Some rty \<and> fmlookup E1 x = Some (VT_Scalar ty) \<and> ty_compat rty ty))"
  proof (cases "ret_kind (FI_ReturnType info)")
    case (RK_Scalar cty)
    from rk[unfolded RK_Scalar RetKind.case] obtain x where fr: "fresh_name (CG_Fun cg) ''call'' st = Inr (x, st1)"
      and eq: "Sret = [MS_DeclScalar x cty]" "retArgs = []" "xopt = Some x" "res1 = CR_Scalar (ME_Var x)"
      by (auto simp: cg_return_def elim!: cg_bind_InrE)
    let ?E1 = "fmupd x (VT_Scalar cty) E"
    have d: "lowered_ok prog rt (E, ds) st [MS_DeclScalar x cty] st1 (?E1, x # ds)" by (rule fresh_scalar_ok[OF sc fr])
    have "res_ok ?E1 info res1" unfolding eq(4) using RK_Scalar by (auto simp: expr_ok_def)
    moreover have "case xopt of None \<Rightarrow> True | Some x \<Rightarrow> (\<exists>rty ty. MF_Ret fn = Some rty \<and> fmlookup ?E1 x = Some (VT_Scalar ty) \<and> ty_compat rty ty)"
      unfolding eq(3) using mret RK_Scalar by (simp add: ty_compat_def)
    ultimately show ?thesis using d unfolding eq(1,2) RK_Scalar by auto
  next
    case RK_Unit
    have eq: "Sret = []" "retArgs = []" "xopt = None" "res1 = CR_Unit" "st1 = st"
      using rk unfolding RK_Unit RetKind.case by (auto simp: cg_return_def)
    show ?thesis unfolding eq RK_Unit using lowered_ok_nil[OF sc] RK_Unit by auto
  next
    case RK_Buf
    from rk[unfolded RK_Buf RetKind.case] obtain r where fr: "fresh_name (CG_Fun cg) ''ret'' st = Inr (r, st1)"
      and eq: "Sret = [MS_DeclBuf r (buf_size (cg_size cg ?retTy))]" "retArgs = [ME_AddrOf r]" "xopt = None" "res1 = CR_Place (ME_AddrOf r)"
      by (auto simp: cg_return_def elim!: cg_bind_InrE)
    let ?E1 = "fmupd r VT_Buf E"
    have d: "lowered_ok prog rt (E, ds) st [MS_DeclBuf r (buf_size (cg_size cg ?retTy))] st1 (?E1, r # ds)"
      by (rule fresh_buf_ok[OF sc fr cg_buf_size_ok[OF ok rwk rf]])
    show ?thesis unfolding eq RK_Buf using d RK_Buf by (auto simp: expr_ok_def)
  qed
  then obtain E1 ds1 where lo1: "lowered_ok prog rt (E, ds) st Sret st1 (E1, ds1)" and ro1: "res_ok E1 info res1"
    and ra1: "list_all2 (\<lambda>e cty. expr_ok E1 e cty) retArgs (case ret_kind (FI_ReturnType info) of RK_Buf \<Rightarrow> [CTy_CharPtr] | _ \<Rightarrow> [])"
    and xo1: "case xopt of None \<Rightarrow> True
               | Some x \<Rightarrow> (\<exists>rty ty. MF_Ret fn = Some rty \<and> fmlookup E1 x = Some (VT_Scalar ty) \<and> ty_compat rty ty)"
    by blast
  have ok1: "cg_ok prog E1 cg" using cg_ok_mono[OF lowered_ok_env_le'[OF lo1] ok] .
  (* the arguments *)
  have args: "\<exists>E' ds'. lowered_ok prog rt (E1, ds1) st1 (concat (map fst argsL)) st' (E', ds')
       \<and> list_all2 (\<lambda>x y. expr_ok E' (snd y) ((\<lambda>(ty, vor, _). param_cty ty vor) (snd x))) (zip args (FI_TmArgs info)) argsL"
  proof (rule cg_mapM_chain2[OF lm lowered_ok_scope[OF lo1]])
    fix x sta y stb Ea dsa
    assume x: "x \<in> set (zip args (FI_TmArgs info))" and fx: "?argf x sta = Inr (y, stb)"
      and sca: "scope_ok prog (Ea, dsa) sta" and le: "env_le E1 Ea"
    obtain a pty vor gh where xa: "x = (a, pty, vor, gh)" by (rule prod_cases4)
    have mem: "(a, (pty, vor, gh)) \<in> set (zip args (FI_TmArgs info))" using x xa by simp
    obtain i where i: "i < length args" and ai: "args ! i = a" and pi: "FI_TmArgs info ! i = (pty, vor, gh)"
      using mem lens(1) by (auto simp: in_set_zip)
    have aty: "core_term_type ?env NotGhost a = Some (apply_subst ?subst pty)"
      using cat[unfolded call_args_typed_def, THEN conjunct2, THEN conjunct2, THEN conjunct2, rule_format, OF i] ai pi by simp
    have ain: "a \<in> set args" using i ai by auto
    have tfa': "term_fits ?env a" using tfa ain by simp
    have oka: "cg_ok prog Ea cg" using cg_ok_mono[OF le ok1] .
    show "\<exists>E2 ds2. lowered_ok prog rt (Ea, dsa) sta (fst y) stb (E2, ds2)
            \<and> expr_ok E2 (snd y) ((\<lambda>(ty, vor, _). param_cty ty vor) (snd x))"
    proof (cases "param_by_ptr pty vor")
      case True
      have la: "lower_addr cg a sta = Inr (y, stb)" using fx True unfolding xa by simp
      obtain Sa ea where y: "y = (Sa, ea)" by (cases y)
      obtain E2 ds2 where lo: "lowered_ok prog rt (Ea, dsa) sta Sa stb (E2, ds2)" and ea: "expr_ok E2 ea CTy_CharPtr"
        by (rule la_okD[OF IHa[OF cl chk refl rk refl refl refl mem refl refl refl True] la[unfolded y] oka sca tfa'])
      show ?thesis unfolding y xa using lo ea True by (auto simp: param_cty_def)
    next
      case False
      have lt: "lower_term cg a sta = Inr (y, stb)" using fx False unfolding xa by simp
      obtain Sa ea where y: "y = (Sa, ea)" by (cases y)
      obtain E2 ds2 ty2 where ty2: "core_term_type ?env NotGhost a = Some ty2"
        and lo: "lowered_ok prog rt (Ea, dsa) sta Sa stb (E2, ds2)" and ea: "expr_ok E2 ea (res_cty ty2)"
        by (rule lt_okD[OF IHt[OF cl chk refl rk refl refl refl mem refl refl refl False] lt[unfolded y] oka sca tfa'])
      obtain cty where sty: "scalar_ty pty = Some cty" using False by (auto simp: param_by_ptr_def)
      have "ty2 = apply_subst ?subst pty" using ty2 aty by simp
      then have "res_cty ty2 = cty" using res_cty_apply_subst_scalar[OF sty, of ?subst] by simp
      moreover have "param_cty pty vor = cty" using False sty by (simp add: param_cty_def)
      ultimately show ?thesis unfolding y xa using lo ea by auto
    qed
  next
    fix E1 E2 x y assume "env_le E1 E2" "expr_ok E1 (snd y) ((\<lambda>(ty, vor, _). param_cty ty vor) (snd x))"
    then show "expr_ok E2 (snd y) ((\<lambda>(ty, vor, _). param_cty ty vor) (snd x))" by (rule expr_ok_mono)
  qed
  from args obtain E2 ds2 where lo2: "lowered_ok prog rt (E1, ds1) st1 (concat (map fst argsL)) st' (E2, ds2)"
    and al: "list_all2 (\<lambda>x y. expr_ok E2 (snd y) ((\<lambda>(ty, vor, _). param_cty ty vor) (snd x))) (zip args (FI_TmArgs info)) argsL"
    by blast
  have le2: "env_le E1 E2" by (rule lowered_ok_env_le'[OF lo2])
  have ok2: "cg_ok prog E2 cg" using cg_ok_mono[OF le2 ok1] .
  (* the call *)
  have wktys: "list_all (is_well_kinded ?env) tys" using cat unfolding call_args_typed_def by simp
  have szs: "list_all2 (\<lambda>e cty. expr_ok E2 e cty) (map (cg_size cg) tys) (map (\<lambda>_. CTy_U64) (FI_TyArgs info))"
    using lens(2) wktys ftys by (auto simp: list_all2_conv_all_nth list_all_length intro!: cg_size_ok[OF ok2])
  have argsl: "list_all2 (\<lambda>e cty. expr_ok E2 e cty) (map snd argsL) (map (\<lambda>(ty, vor, _). param_cty ty vor) (FI_TmArgs info))"
  proof -
    have len: "length argsL = length (FI_TmArgs info)" using list_all2_lengthD[OF al] lens(1) by simp
    show ?thesis using al lens(1) unfolding list_all2_conv_all_nth by (auto simp: len)
  qed
  have ra2: "list_all2 (\<lambda>e cty. expr_ok E2 e cty) retArgs (case ret_kind (FI_ReturnType info) of RK_Buf \<Rightarrow> [CTy_CharPtr] | _ \<Rightarrow> [])"
    using ra1 expr_ok_mono[OF le2] by (auto simp: list_all2_conv_all_nth)
  have callargs: "list_all2 (\<lambda>e cty. expr_compat E2 e cty \<and> expr_wf e)
       (retArgs @ map (cg_size cg) tys @ map snd argsL) (map snd (MF_Params fn))"
    unfolding params param_ctys_def
    by (rule list_all2_mono[OF list_all2_appendI[OF ra2 list_all2_appendI[OF szs argsl]]]) (auto simp: expr_ok_compat expr_ok_wf)
  have xo2: "case xopt of None \<Rightarrow> True
               | Some x \<Rightarrow> (\<exists>rty ty. MF_Ret fn = Some rty \<and> fmlookup E2 x = Some (VT_Scalar ty) \<and> ty_compat rty ty)"
    using xo1 env_le_lookup[OF le2] by (auto split: option.splits)
  have call: "lowered_ok prog rt (E2, ds2) st' [MS_Call xopt f (retArgs @ map (cg_size cg) tys @ map snd argsL)] st' (E2, ds2)"
    by (rule call_ok[OF lowered_ok_scope[OF lo2] fn callargs xo2])
  have ro2: "res_ok E2 info res" unfolding res using res_ok_mono[OF le2 ro1] .
  have lo: "lowered_ok prog rt (E, ds) st S st' (E2, ds2)"
    unfolding S using lowered_ok_append[OF lowered_ok_append[OF lo1 lo2] call] by simp
  show "\<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> res_ok E' info res" using lo ro2 by blast
qed

end
