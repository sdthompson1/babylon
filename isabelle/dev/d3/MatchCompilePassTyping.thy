theory MatchCompilePassTyping
  imports BabylonDev2.MatchCompilePassFlat Babylon.CoreModuleTypecheck
    Babylon.CoreStmtTypecheckLemmas
begin

(* Type preservation for the match compilation pass.

   The pass only rewrites function bodies, so the type environment of the
   module is unchanged, and the module-level theorem
   (match_compile_module_well_typed) only needs each compiled function body
   to typecheck in the same body environment as the original: that is
   match_compile_statement_list_type, which rests on match_compile_term_type.

   For a compiled match, the typing comes from the MatchCompileTyping layer:
   compile_match_arm_patterns_compatible says that every test scrutinee of the
   tree has a type and that the test patterns are compatible with it, and
   compile_match_bodies_subset says that every leaf is one of the original arm
   bodies. Translating the tree back to Core then gives a well-typed term
   (match_tree_to_term_type) or statement list (match_tree_to_statements_type).
   The term case also needs every test to have at least one arm, which is
   compile_matrix_tests_ok from MatchCompilePassFlat.thy. *)


section \<open>Lvalues\<close>

lemma is_writable_lvalue_is_lvalue:
  "is_writable_lvalue env tm \<Longrightarrow> is_lvalue tm"
  by (induction tm) (auto simp: is_lvalue_def)

lemma is_writable_lvalue_match_compile_term:
  "is_lvalue tm \<Longrightarrow> is_writable_lvalue env (match_compile_term tm) = is_writable_lvalue env tm"
  by (induction tm) (auto simp: is_lvalue_def split: if_splits)

lemma ghost_lvalue_ok_match_compile_term:
  "is_lvalue tm \<Longrightarrow> ghost_lvalue_ok env g (match_compile_term tm) = ghost_lvalue_ok env g tm"
  by (simp add: ghost_lvalue_ok_def)


section \<open>Typing of a translated tree\<close>

(* arm_patterns_compatible depends on the environment only through the typing
   of terms and the compatibility of patterns, neither of which looks at
   TE_ProofTopLevel. *)
lemma arm_patterns_compatible_TE_ProofTopLevel_irrelevant [simp]:
  "arm_patterns_compatible (env \<lparr> TE_ProofTopLevel := b \<rparr>) g t = arm_patterns_compatible env g t"
proof (induction t)
  case (MT_Leaf body)
  then show ?case by simp
next
  case (MT_Test s arms)
  have pc: "pattern_compatible (env \<lparr> TE_ProofTopLevel := b \<rparr>) p ty = pattern_compatible env p ty"
    for p ty
    by (rule pattern_compatible_cong_env) simp
  have ih: "arm_patterns_compatible (env \<lparr> TE_ProofTopLevel := b \<rparr>) g t
              = arm_patterns_compatible env g t"
    if "(p, t) \<in> set arms" for p t
    using MT_Test.IH[OF that, of t] by simp
  show ?case
    by (auto simp: core_term_type_TE_ProofTopLevel_irrelevant pc ih list_all_iff
             split: option.splits)
qed

(* A term tree whose tests are well-typed and non-empty, and whose leaves all
   have type ty, translates to a term of type ty. *)
lemma match_tree_to_term_type:
  assumes "arm_patterns_compatible env ghost t"
      and "match_tree_tests_ok (\<lambda>_. True) t"
      and "\<And>body. body \<in> match_tree_bodies t \<Longrightarrow> core_term_type env ghost body = Some ty"
  shows "core_term_type env ghost (match_tree_to_term t) = Some ty"
  using assms
proof (induction t)
  case (MT_Leaf body)
  then show ?case by simp
next
  case (MT_Test s arms)
  let ?arms' = "map (\<lambda>(p, t). (p, match_tree_to_term t)) arms"
  from MT_Test.prems(1) obtain sTy where
    s_ty: "core_term_type env ghost s = Some sTy" and
    arms_ok: "list_all (\<lambda>(p, t). pattern_compatible env p sTy \<and> arm_patterns_compatible env ghost t)
                arms"
    by (auto split: option.splits)
  from MT_Test.prems(2) have ne: "arms \<noteq> []"
    and tests: "list_all (\<lambda>(_, t). match_tree_tests_ok (\<lambda>_. True) t) arms" by simp_all
  have sub: "core_term_type env ghost (match_tree_to_term t) = Some ty"
    if arm_in: "(p, t) \<in> set arms" for p t
  proof (rule MT_Test.IH)
    show "t \<in> Basic_BNFs.snds (p, t)" by simp
    show "(p, t) \<in> set arms" by (rule arm_in)
    from arms_ok arm_in show "arm_patterns_compatible env ghost t" by (auto simp: list_all_iff)
    from tests arm_in show "match_tree_tests_ok (\<lambda>_. True) t" by (auto simp: list_all_iff)
    fix body assume "body \<in> match_tree_bodies t"
    with arm_in show "core_term_type env ghost body = Some ty" by (intro MT_Test.prems(3)) auto
  qed
  have pats: "list_all (\<lambda>p. pattern_compatible env p sTy) (map fst ?arms')"
    using arms_ok by (auto simp: list_all_iff)
  have ne': "?arms' \<noteq> []" using ne by simp
  have hd_ty: "core_term_type env ghost (snd (hd ?arms')) = Some ty"
  proof -
    from ne obtain p t rest where arms_eq: "arms = (p, t) # rest" by (cases arms) auto
    hence "(p, t) \<in> set arms" by simp
    from sub[OF this] arms_eq show ?thesis by simp
  qed
  have all_ty: "list_all (\<lambda>body. core_term_type env ghost body = Some ty) (map snd ?arms')"
    using sub by (auto simp: list_all_iff)
  have tl_ty: "list_all (\<lambda>body. core_term_type env ghost body = Some ty) (tl (map snd ?arms'))"
    using all_ty by (cases arms) auto
  show ?case
    using s_ty pats ne' hd_ty tl_ty by (simp add: Let_def)
qed

(* A statement tree, with the ghost flag of the original match, translates to
   a well-typed statement list, in the environment of the arm bodies (which
   is the match's environment with TE_ProofTopLevel cleared, and therefore
   stays the same for the nested matches). *)
lemma match_tree_to_statements_type:
  assumes "TE_ProofTopLevel env = False"
      and "arm_patterns_compatible env mg t"
      and "\<And>body. body \<in> match_tree_bodies t \<Longrightarrow> core_statement_list_type env mg body \<noteq> None"
  shows "core_statement_list_type env mg (match_tree_to_statements mg t) \<noteq> None"
  using assms(2,3)
proof (induction t)
  case (MT_Leaf body)
  then show ?case by simp
next
  case (MT_Test s arms)
  let ?arms' = "map (\<lambda>(p, t). (p, match_tree_to_statements mg t)) arms"
  from MT_Test.prems(1) obtain sTy where
    s_ty: "core_term_type env mg s = Some sTy" and
    arms_ok: "list_all (\<lambda>(p, t). pattern_compatible env p sTy \<and> arm_patterns_compatible env mg t)
                arms"
    by (auto split: option.splits)
  have sub: "core_statement_list_type env mg (match_tree_to_statements mg t) \<noteq> None"
    if arm_in: "(p, t) \<in> set arms" for p t
  proof (rule MT_Test.IH)
    show "t \<in> Basic_BNFs.snds (p, t)" by simp
    show "(p, t) \<in> set arms" by (rule arm_in)
    from arms_ok arm_in show "arm_patterns_compatible env mg t" by (auto simp: list_all_iff)
    fix body assume "body \<in> match_tree_bodies t"
    with arm_in show "core_statement_list_type env mg body \<noteq> None"
      by (intro MT_Test.prems(2)) auto
  qed
  have env_eq: "env \<lparr> TE_ProofTopLevel := False \<rparr> = env"
    using assms(1) by simp
  have pats: "list_all (\<lambda>p. pattern_compatible env p sTy) (map fst ?arms')"
    using arms_ok by (auto simp: list_all_iff)
  have bodies: "list_all (\<lambda>body. core_statement_list_type env mg body \<noteq> None) (map snd ?arms')"
    using sub by (auto simp: list_all_iff)
  have "core_statement_type env mg (CoreStmt_Match mg s ?arms') = Some env"
    using s_ty pats bodies env_eq by (simp add: Let_def)
  thus ?case by simp
qed


section \<open>Typing of one compiled match\<close>

lemma compile_match_tree_arm_patterns_compatible:
  assumes "core_term_type env g scrut = Some scrutTy"
      and "arms \<noteq> []"
      and "list_all (\<lambda>(p, _). pattern_compatible env p scrutTy) arms"
      and "tyenv_well_formed env"
  shows "arm_patterns_compatible env g (compile_match_tree scrut arms)"
  unfolding compile_match_tree_eq_compile_match[of scrut arms scrutTy]
  by (rule compile_match_arm_patterns_compatible[OF assms])

theorem compile_match_term_type:
  assumes scrut: "core_term_type env ghost scrut = Some scrutTy"
      and ne: "arms \<noteq> []"
      and pats: "list_all (\<lambda>(p, _). pattern_compatible env p scrutTy) arms"
      and wf: "tyenv_well_formed env"
      and bodies: "\<And>p body. (p, body) \<in> set arms \<Longrightarrow> core_term_type env ghost body = Some ty"
  shows "core_term_type env ghost (compile_match_term scrut arms) = Some ty"
  unfolding compile_match_term_def
proof (rule match_tree_to_term_type)
  show "arm_patterns_compatible env ghost (compile_match_tree scrut arms)"
    by (rule compile_match_tree_arm_patterns_compatible[OF scrut ne pats wf])
  show "match_tree_tests_ok (\<lambda>_. True) (compile_match_tree scrut arms)"
    by (rule compile_match_tree_tests_ok[OF _ _ ne]) simp_all
  fix body assume "body \<in> match_tree_bodies (compile_match_tree scrut arms)"
  with compile_match_tree_bodies_subset[OF ne] have "body \<in> set (map snd arms)" by blast
  thus "core_term_type env ghost body = Some ty" using bodies by auto
qed

theorem compile_match_statement_type:
  assumes gm: "ghost = Ghost \<longrightarrow> mg = Ghost"
      and scrut: "core_term_type env mg scrut = Some scrutTy"
      and ne: "arms \<noteq> []"
      and pats: "list_all (\<lambda>(p, _). pattern_compatible env p scrutTy) arms"
      and wf: "tyenv_well_formed env"
      and bodies: "\<And>p body. (p, body) \<in> set arms \<Longrightarrow>
                     core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) mg body \<noteq> None"
  shows "core_statement_list_type env ghost (compile_match_statement mg scrut arms) = Some env"
proof -
  let ?env1 = "env \<lparr> TE_ProofTopLevel := False \<rparr>"
  have apc: "arm_patterns_compatible env mg (compile_match_tree scrut arms)"
    by (rule compile_match_tree_arm_patterns_compatible[OF scrut ne pats wf])
  have bodies': "core_statement_list_type ?env1 mg body \<noteq> None"
    if "body \<in> match_tree_bodies (compile_match_tree scrut arms)" for body
  proof -
    from that compile_match_tree_bodies_subset[OF ne] have "body \<in> set (map snd arms)" by blast
    thus ?thesis using bodies by auto
  qed
  show ?thesis
  proof (cases "compile_match_tree scrut arms")
    case (MT_Leaf body)
    have "core_statement_list_type ?env1 mg body \<noteq> None"
      using bodies'[of body] MT_Leaf by simp
    with gm scrut show ?thesis
      unfolding compile_match_statement_def MT_Leaf by simp
  next
    case (MT_Test s arms')
    let ?arms'' = "map (\<lambda>(p, t). (p, match_tree_to_statements mg t)) arms'"
    from apc MT_Test obtain sTy where
      s_ty: "core_term_type env mg s = Some sTy" and
      arms_ok: "list_all (\<lambda>(p, t). pattern_compatible env p sTy
                                 \<and> arm_patterns_compatible env mg t) arms'"
      by (auto split: option.splits)
    have sub: "core_statement_list_type ?env1 mg (match_tree_to_statements mg t) \<noteq> None"
      if arm_in: "(p, t) \<in> set arms'" for p t
    proof (rule match_tree_to_statements_type)
      show "TE_ProofTopLevel ?env1 = False" by simp
      from arms_ok arm_in have "arm_patterns_compatible env mg t" by (auto simp: list_all_iff)
      thus "arm_patterns_compatible ?env1 mg t" by simp
      fix body assume "body \<in> match_tree_bodies t"
      with arm_in MT_Test show "core_statement_list_type ?env1 mg body \<noteq> None"
        by (intro bodies') auto
    qed
    have pats': "list_all (\<lambda>p. pattern_compatible env p sTy) (map fst ?arms'')"
      using arms_ok by (auto simp: list_all_iff)
    have bodies'': "list_all (\<lambda>body. core_statement_list_type ?env1 mg body \<noteq> None)
                      (map snd ?arms'')"
      using sub by (auto simp: list_all_iff)
    have "core_statement_type env ghost (CoreStmt_Match mg s ?arms'') = Some env"
      using gm s_ty pats' bodies'' by (simp add: Let_def)
    thus ?thesis
      unfolding compile_match_statement_def MT_Test by simp
  qed
qed


section \<open>Terms\<close>

theorem match_compile_term_type:
  "core_term_type env ghost tm = Some ty \<Longrightarrow> tyenv_well_formed env
   \<Longrightarrow> core_term_match_scrutinees_ok tm
   \<Longrightarrow> core_term_type env ghost (match_compile_term tm) = Some ty"
proof (induction tm arbitrary: env ghost ty)
  case (CoreTm_LitBool b)
  then show ?case by simp
next
  case (CoreTm_LitInt i)
  then show ?case by simp
next
  case (CoreTm_LitArray elemTy tms)
  from CoreTm_LitArray.prems(1) have
      wk: "is_well_kinded env elemTy" and
      rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env elemTy" and
      all: "list_all (\<lambda>tm. core_term_type env ghost tm = Some elemTy) tms" and
      len: "int_in_range (int_range Unsigned IntBits_64) (int (length tms))" and
      ty_eq: "ty = CoreTy_Array elemTy [CoreDim_Fixed (int (length tms))]"
    by (auto split: if_splits)
  have all': "list_all (\<lambda>tm. core_term_type env ghost tm = Some elemTy) (map match_compile_term tms)"
    unfolding list_all_iff
  proof
    fix tm' assume "tm' \<in> set (map match_compile_term tms)"
    then obtain tm where tin: "tm \<in> set tms" and tm': "tm' = match_compile_term tm" by auto
    have "core_term_type env ghost tm = Some elemTy" using all tin by (simp add: list_all_iff)
    hence "core_term_type env ghost (match_compile_term tm) = Some elemTy"
      using CoreTm_LitArray.prems(3) tin
      by (intro CoreTm_LitArray.IH[OF tin _ CoreTm_LitArray.prems(2)]) (auto simp: list_all_iff)
    thus "core_term_type env ghost tm' = Some elemTy" unfolding tm' .
  qed
  show ?case using wk rt all' len ty_eq by simp
next
  case (CoreTm_Var name)
  then show ?case by simp
next
  case (CoreTm_Cast targetTy tm)
  from CoreTm_Cast.prems(1) obtain operandTy where
    op: "core_term_type env ghost tm = Some operandTy" and
    rest: "cast_ok env operandTy targetTy" "ghost = NotGhost \<longrightarrow> is_runtime_type env targetTy"
      "ty = targetTy"
    by (auto split: option.splits if_splits)
  from CoreTm_Cast.IH[OF op CoreTm_Cast.prems(2)] CoreTm_Cast.prems(3)
  have "core_term_type env ghost (match_compile_term tm) = Some operandTy" by simp
  with rest show ?case by simp
next
  case (CoreTm_Unop op tm)
  from CoreTm_Unop.prems(1) obtain operandTy where
    opty: "core_term_type env ghost tm = Some operandTy"
    by (auto split: option.splits)
  from CoreTm_Unop.IH[OF opty CoreTm_Unop.prems(2)] CoreTm_Unop.prems(3)
  have "core_term_type env ghost (match_compile_term tm) = Some operandTy" by simp
  with CoreTm_Unop.prems(1) opty show ?case by simp
next
  case (CoreTm_Binop op lhs rhs)
  from CoreTm_Binop.prems(1) obtain lhsTy rhsTy where
    l: "core_term_type env ghost lhs = Some lhsTy" and
    r: "core_term_type env ghost rhs = Some rhsTy"
    by (auto split: option.splits)
  from CoreTm_Binop.IH(1)[OF l CoreTm_Binop.prems(2)] CoreTm_Binop.prems(3)
  have l': "core_term_type env ghost (match_compile_term lhs) = Some lhsTy" by simp
  from CoreTm_Binop.IH(2)[OF r CoreTm_Binop.prems(2)] CoreTm_Binop.prems(3)
  have r': "core_term_type env ghost (match_compile_term rhs) = Some rhsTy" by simp
  from CoreTm_Binop.prems(1) l r l' r' show ?case by simp
next
  case (CoreTm_Let var rhs body)
  from CoreTm_Let.prems(1) obtain rhsTy where
    rhs_ty: "core_term_type env ghost rhs = Some rhsTy" and
    body_ty: "core_term_type
        (env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
               TE_GhostLocals := (if ghost = Ghost then finsert var (TE_GhostLocals env)
                                  else fminus (TE_GhostLocals env) {|var|}),
               TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>)
        ghost body = Some ty"
    by (auto simp: Let_def split: option.splits)
  let ?env' = "env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                     TE_GhostLocals := (if ghost = Ghost then finsert var (TE_GhostLocals env)
                                        else fminus (TE_GhostLocals env) {|var|}),
                     TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
  have wf': "tyenv_well_formed ?env'"
  proof (rule tyenv_well_formed_declare_var[OF CoreTm_Let.prems(2)])
    show "is_well_kinded env rhsTy"
      by (rule core_term_type_well_kinded[OF rhs_ty CoreTm_Let.prems(2)])
    show "ghost = NotGhost \<longrightarrow> is_runtime_type env rhsTy"
      using core_term_type_notghost_runtime[OF _ CoreTm_Let.prems(2)] rhs_ty by auto
  qed
  from CoreTm_Let.IH(1)[OF rhs_ty CoreTm_Let.prems(2)] CoreTm_Let.prems(3)
  have rhs': "core_term_type env ghost (match_compile_term rhs) = Some rhsTy" by simp
  from CoreTm_Let.IH(2)[OF body_ty wf'] CoreTm_Let.prems(3)
  have body': "core_term_type ?env' ghost (match_compile_term body) = Some ty" by simp
  show ?case using rhs' body' by (simp add: Let_def)
next
  case (CoreTm_Quantifier q var varTy body)
  from CoreTm_Quantifier.prems(1) have g: "ghost = Ghost" by (cases ghost) simp_all
  let ?env' = "env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                     TE_GhostLocals := finsert var (TE_GhostLocals env),
                     TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
  from CoreTm_Quantifier.prems(1) g have
    wk: "is_well_kinded env varTy" and
    body_ty: "core_term_type ?env' Ghost body = Some CoreTy_Bool" and
    ty_eq: "ty = CoreTy_Bool"
    by (auto simp: Let_def split: if_splits option.splits CoreType.splits)
  have wf': "tyenv_well_formed ?env'"
    using tyenv_well_formed_declare_var[OF CoreTm_Quantifier.prems(2) wk, where g = Ghost
            and var = var and c = "finsert var (TE_ConstLocals env)"]
    by simp
  from CoreTm_Quantifier.IH[OF body_ty wf'] CoreTm_Quantifier.prems(3)
  have body': "core_term_type ?env' Ghost (match_compile_term body) = Some CoreTy_Bool" by simp
  show ?case using g wk body' ty_eq by (simp add: Let_def)
next
  case (CoreTm_FunctionCall fnName tyArgs tmArgs)
  from CoreTm_FunctionCall.prems(1) obtain funInfo where
    fi: "fmlookup (TE_Functions env) fnName = Some funInfo"
    by (auto split: option.splits)
  let ?tySubst = "fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)"
  let ?expected = "map (\<lambda>(ty, _). apply_subst ?tySubst ty) (FI_TmArgs funInfo)"
  let ?modes = "map (\<lambda>(_, _, gh). param_mode ghost gh) (FI_TmArgs funInfo)"
  let ?argok = "\<lambda>tm (expectedTy, mode). core_term_type env mode tm = Some expectedTy"
  from CoreTm_FunctionCall.prems(1) fi have
    checks: "length tyArgs = length (FI_TyArgs funInfo)"
      "list_all (is_well_kinded env) tyArgs" "list_all is_complete_type tyArgs"
      "\<not> (ghost = NotGhost \<and> (\<not> list_all (is_runtime_type env) tyArgs \<or> FI_Ghost funInfo = Ghost))"
      "list_all (\<lambda>(_, vor, _). vor = Var) (FI_TmArgs funInfo)" "\<not> FI_Impure funInfo"
      "length tmArgs = length (FI_TmArgs funInfo)" and
    args: "list_all2 ?argok tmArgs (zip ?expected ?modes)" and
    ty_eq: "ty = apply_subst ?tySubst (FI_ReturnType funInfo)"
    by (auto simp: Let_def split: if_splits)
  have len_e: "length ?expected = length (FI_TmArgs funInfo)"
    and len_m: "length ?modes = length (FI_TmArgs funInfo)" by simp_all
  have args': "list_all2 ?argok (map match_compile_term tmArgs) (zip ?expected ?modes)"
  proof (rule list_all2_all_nthI)
    show "length (map match_compile_term tmArgs) = length (zip ?expected ?modes)"
      using list_all2_lengthD[OF args] by simp
    fix i assume i_lt: "i < length (map match_compile_term tmArgs)"
    hence i_lt': "i < length tmArgs" and i_lt_f: "i < length (FI_TmArgs funInfo)"
      using checks(7) by simp_all
    have zip_e: "zip ?expected ?modes ! i = (?expected ! i, ?modes ! i)"
      using i_lt_f len_e len_m by (simp only: nth_zip)
    have nth_m: "map match_compile_term tmArgs ! i = match_compile_term (tmArgs ! i)"
      using i_lt' by (simp only: nth_map)
    have mem: "tmArgs ! i \<in> set tmArgs" using i_lt' by simp
    with CoreTm_FunctionCall.prems(3) have ok_i: "core_term_match_scrutinees_ok (tmArgs ! i)"
      by (simp add: list_all_iff)
    have ai0: "?argok (tmArgs ! i) (zip ?expected ?modes ! i)"
      by (rule list_all2_nthD[OF args i_lt'])
    hence t: "core_term_type env (?modes ! i) (tmArgs ! i) = Some (?expected ! i)"
      unfolding zip_e by simp
    have "core_term_type env (?modes ! i) (match_compile_term (tmArgs ! i)) = Some (?expected ! i)"
      by (rule CoreTm_FunctionCall.IH[OF mem t CoreTm_FunctionCall.prems(2) ok_i])
    thus "?argok (map match_compile_term tmArgs ! i) (zip ?expected ?modes ! i)"
      unfolding zip_e nth_m by simp
  qed
  show ?case using fi checks args' ty_eq by (simp add: Let_def)
next
  case (CoreTm_VariantCtor ctorName tyArgs payload)
  from CoreTm_VariantCtor.prems(1) obtain dtName tyvars payloadTy where
    ctor: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payloadTy)" and
    len: "length tyArgs = length tyvars" and
    wk: "list_all (is_well_kinded env) tyArgs" and
    cp: "list_all is_complete_type tyArgs" and
    rt: "\<not> (ghost = NotGhost \<and> (\<not> list_all (is_runtime_type env) tyArgs
                                \<or> dtName \<in> ghost_datatypes env))" and
    p_ty: "core_term_type env ghost payload
             = Some (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)" and
    ty_eq: "ty = CoreTy_Datatype dtName tyArgs"
    by (auto simp: Let_def split: option.splits if_splits)
  from CoreTm_VariantCtor.IH[OF p_ty CoreTm_VariantCtor.prems(2)] CoreTm_VariantCtor.prems(3)
  have p': "core_term_type env ghost (match_compile_term payload)
              = Some (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)" by simp
  show ?case
    using ctor len wk cp rt p' ty_eq by (simp add: Let_def)
next
  case (CoreTm_Record flds)
  let ?flds' = "map (\<lambda>(name, tm). (name, match_compile_term tm)) flds"
  from CoreTm_Record.prems(1) obtain tys where
    dist: "distinct (map fst flds)" and
    those1: "those (map (\<lambda>(name, tm). core_term_type env ghost tm) flds) = Some tys" and
    ty_eq: "ty = CoreTy_Record (zip (map fst flds) tys)"
    by (auto split: option.splits if_splits)
  have "those (map (\<lambda>(name, tm). core_term_type env ghost (match_compile_term tm)) flds) = Some tys"
  proof (rule those_map_mono[OF those1])
    fix x y
    assume x_in: "x \<in> set flds"
      and x_ty: "(case x of (name, tm) \<Rightarrow> core_term_type env ghost tm) = Some y"
    obtain name tm where x_eq: "x = (name, tm)" by (cases x) auto
    with x_ty have t: "core_term_type env ghost tm = Some y" by simp
    have tm_in: "tm \<in> Basic_BNFs.snds x" using x_eq by simp
    from CoreTm_Record.IH[OF x_in tm_in t CoreTm_Record.prems(2)] CoreTm_Record.prems(3) x_in x_eq
    have "core_term_type env ghost (match_compile_term tm) = Some y"
      by (auto simp: list_all_iff)
    thus "(case x of (name, tm) \<Rightarrow> core_term_type env ghost (match_compile_term tm)) = Some y"
      using x_eq by simp
  qed
  hence T: "those (map (\<lambda>(name, tm). core_term_type env ghost tm) ?flds') = Some tys"
    by (simp add: case_prod_unfold comp_def)
  have F: "map fst ?flds' = map fst flds" by (simp add: case_prod_unfold comp_def)
  have "core_term_type env ghost (CoreTm_Record ?flds') = Some ty"
    apply (subst core_term_type.simps)
    apply (unfold F T)
    by (simp add: dist ty_eq)
  thus ?case by simp
next
  case (CoreTm_RecordProj tm fldName)
  from CoreTm_RecordProj.prems(1) obtain fieldTypes where
    t: "core_term_type env ghost tm = Some (CoreTy_Record fieldTypes)"
    by (auto split: option.splits CoreType.splits)
  from CoreTm_RecordProj.IH[OF t CoreTm_RecordProj.prems(2)] CoreTm_RecordProj.prems(3)
  have "core_term_type env ghost (match_compile_term tm) = Some (CoreTy_Record fieldTypes)" by simp
  with CoreTm_RecordProj.prems(1) t show ?case by simp
next
  case (CoreTm_VariantProj tm ctorName)
  from CoreTm_VariantProj.prems(1) obtain dtName tyArgs where
    t: "core_term_type env ghost tm = Some (CoreTy_Datatype dtName tyArgs)"
    by (auto split: option.splits CoreType.splits)
  from CoreTm_VariantProj.IH[OF t CoreTm_VariantProj.prems(2)] CoreTm_VariantProj.prems(3)
  have "core_term_type env ghost (match_compile_term tm) = Some (CoreTy_Datatype dtName tyArgs)"
    by simp
  with CoreTm_VariantProj.prems(1) t show ?case by simp
next
  case (CoreTm_ArrayProj arr idxTms)
  from CoreTm_ArrayProj.prems(1) obtain elemTy dims where
    a: "core_term_type env ghost arr = Some (CoreTy_Array elemTy dims)" and
    len: "length idxTms = length dims" and
    idx: "list_all (\<lambda>tm. core_term_type env ghost tm = Some (CoreTy_FiniteInt Unsigned IntBits_64))
            idxTms" and
    ty_eq: "ty = elemTy"
    by (auto split: option.splits CoreType.splits if_splits)
  from CoreTm_ArrayProj.IH(1)[OF a CoreTm_ArrayProj.prems(2)] CoreTm_ArrayProj.prems(3)
  have a': "core_term_type env ghost (match_compile_term arr) = Some (CoreTy_Array elemTy dims)"
    by simp
  have idx': "list_all (\<lambda>tm. core_term_type env ghost tm = Some (CoreTy_FiniteInt Unsigned IntBits_64))
                (map match_compile_term idxTms)"
    unfolding list_all_iff
  proof
    fix tm' assume "tm' \<in> set (map match_compile_term idxTms)"
    then obtain tm where tin: "tm \<in> set idxTms" and tm': "tm' = match_compile_term tm" by auto
    have "core_term_type env ghost tm = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
      using idx tin by (simp add: list_all_iff)
    hence "core_term_type env ghost (match_compile_term tm)
             = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
      using CoreTm_ArrayProj.prems(3) tin
      by (intro CoreTm_ArrayProj.IH(2)[OF tin _ CoreTm_ArrayProj.prems(2)]) (auto simp: list_all_iff)
    thus "core_term_type env ghost tm' = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
      unfolding tm' .
  qed
  show ?case using a' len idx' ty_eq by simp
next
  case (CoreTm_Match scrut arms)
  let ?arms' = "map (\<lambda>(p, b). (p, match_compile_term b)) arms"
  from CoreTm_Match.prems(1) obtain scrutTy where
    s_ty: "core_term_type env ghost scrut = Some scrutTy"
    by (auto split: option.splits)
  from CoreTm_Match.prems(1) s_ty have
    ne: "arms \<noteq> []" and
    pats: "list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst arms)" and
    hd_ty: "core_term_type env ghost (snd (hd arms)) = Some ty" and
    tl_ty: "list_all (\<lambda>body. core_term_type env ghost body = Some ty) (tl (map snd arms))"
    by (auto simp: Let_def split: option.splits if_splits)
  have bodies: "core_term_type env ghost b = Some ty" if arm_in: "(p, b) \<in> set arms" for p b
  proof -
    from ne obtain a rest where arms_eq: "arms = a # rest" by (cases arms) auto
    show ?thesis
    proof (cases "(p, b) = a")
      case True
      hence "b = snd a" by (cases a) auto
      with hd_ty arms_eq show ?thesis by simp
    next
      case False
      with arm_in arms_eq have "(p, b) \<in> set rest" by simp
      hence "b \<in> set (map snd rest)" by force
      with tl_ty arms_eq show ?thesis by (auto simp: list_all_iff)
    qed
  qed
  have bodies': "core_term_type env ghost (match_compile_term b) = Some ty"
    if arm_in: "(p, b) \<in> set arms" for p b
  proof -
    have b_in: "b \<in> Basic_BNFs.snds (p, b)" by simp
    from CoreTm_Match.IH(2)[OF arm_in b_in bodies[OF arm_in] CoreTm_Match.prems(2)]
         CoreTm_Match.prems(3) arm_in
    show ?thesis by (auto simp: list_all_iff)
  qed
  from CoreTm_Match.IH(1)[OF s_ty CoreTm_Match.prems(2)] CoreTm_Match.prems(3)
  have s': "core_term_type env ghost (match_compile_term scrut) = Some scrutTy" by simp
  show ?case
  proof (cases "arms_flat arms")
    case True
    have hd': "core_term_type env ghost (snd (hd ?arms')) = Some ty"
    proof -
      from ne obtain p b rest where arms_eq: "arms = (p, b) # rest" by (cases arms) auto
      hence "(p, b) \<in> set arms" by simp
      from bodies'[OF this] arms_eq show ?thesis by simp
    qed
    have all': "list_all (\<lambda>body. core_term_type env ghost body = Some ty) (map snd ?arms')"
      using bodies' by (auto simp: list_all_iff)
    have tl': "list_all (\<lambda>body. core_term_type env ghost body = Some ty) (tl (map snd ?arms'))"
      using all' by (cases arms) auto
    have pats': "list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst ?arms')"
      using pats by (simp add: case_prod_unfold comp_def)
    have ne': "?arms' \<noteq> []" using ne by simp
    from True s' pats' ne' hd' tl' show ?thesis by (simp add: Let_def)
  next
    case False
    have ne': "?arms' \<noteq> []" using ne by simp
    have pats': "list_all (\<lambda>(p, _). pattern_compatible env p scrutTy) ?arms'"
      using pats by (auto simp: list_all_iff)
    have "core_term_type env ghost (compile_match_term (match_compile_term scrut) ?arms') = Some ty"
      by (rule compile_match_term_type[OF s' ne' pats' CoreTm_Match.prems(2)])
         (use bodies' in auto)
    with False show ?thesis by simp
  qed
next
  case (CoreTm_Sizeof tm)
  from CoreTm_Sizeof.prems(1) obtain elemTy dims where
    t: "core_term_type env ghost tm = Some (CoreTy_Array elemTy dims)" and
    ok: "\<not> (list_ex (\<lambda>d. d = CoreDim_Allocatable) dims \<and> \<not> is_lvalue tm \<and> ghost = NotGhost)" and
    ty_eq: "ty = sizeof_type dims"
    by (auto split: option.splits CoreType.splits if_splits)
  from CoreTm_Sizeof.IH[OF t CoreTm_Sizeof.prems(2)] CoreTm_Sizeof.prems(3)
  have t': "core_term_type env ghost (match_compile_term tm) = Some (CoreTy_Array elemTy dims)"
    by simp
  \<comment> \<open>An lvalue stays an lvalue, so the compiled Sizeof is accepted whenever the
     original was.\<close>
  have ok': "\<not> (list_ex (\<lambda>d. d = CoreDim_Allocatable) dims \<and> \<not> is_lvalue (match_compile_term tm)
                \<and> ghost = NotGhost)"
    using ok is_lvalue_match_compile_term by blast
  show ?case using t' ok' ty_eq by simp
next
  case (CoreTm_Allocated aty tm)
  from CoreTm_Allocated.prems(1) have g: "ghost = Ghost" by (cases ghost) simp_all
  from CoreTm_Allocated.prems(1) g obtain ty' where
    t: "core_term_type env Ghost tm = Some ty'"
    by (auto split: option.splits)
  from CoreTm_Allocated.IH[OF t CoreTm_Allocated.prems(2)] CoreTm_Allocated.prems(3)
  have "core_term_type env Ghost (match_compile_term tm) = Some ty'" by simp
  with CoreTm_Allocated.prems(1) g t show ?case by simp
next
  case (CoreTm_Default dty)
  then show ?case by simp
qed


section \<open>Statements\<close>

(* The impure-call typing only looks at the types of the Var arguments, and
   at the lvalue shape and type of the Ref arguments. *)
lemma core_impure_call_type_match_compile:
  assumes "core_impure_call_type env ghost fnName tyArgs tmArgs = Some retTy"
      and wf: "tyenv_well_formed env"
      and ok: "list_all core_term_match_scrutinees_ok tmArgs"
  shows "core_impure_call_type env ghost fnName tyArgs (map match_compile_term tmArgs) = Some retTy"
proof -
  from assms(1) obtain funInfo where
    fi: "fmlookup (TE_Functions env) fnName = Some funInfo"
    unfolding core_impure_call_type_def by (auto split: option.splits)
  let ?tySubst = "fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)"
  let ?expected = "map (\<lambda>(ty, _). apply_subst ?tySubst ty) (FI_TmArgs funInfo)"
  let ?vors = "map (\<lambda>(_, vor, _). vor) (FI_TmArgs funInfo)"
  let ?modes = "map (\<lambda>(_, _, gh). param_mode ghost gh) (FI_TmArgs funInfo)"
  let ?argok = "\<lambda>(tm, vor) (expectedTy, mode).
                    case vor of
                      Var \<Rightarrow> core_term_type env mode tm = Some expectedTy
                    | Ref \<Rightarrow> is_writable_lvalue env tm \<and> ghost_lvalue_ok env mode tm
                             \<and> core_term_type env mode tm = Some expectedTy"
  from assms(1) fi have
    checks: "length tyArgs = length (FI_TyArgs funInfo)"
      "list_all (is_well_kinded env) tyArgs" "list_all is_complete_type tyArgs"
      "\<not> (ghost = NotGhost \<and> (\<not> list_all (is_runtime_type env) tyArgs \<or> FI_Ghost funInfo = Ghost))"
      "\<not> (FI_Impure funInfo \<and> (ghost = Ghost \<or> \<not> TE_FunctionImpure env))"
      "length tmArgs = length (FI_TmArgs funInfo)" and
    args: "list_all2 ?argok (zip tmArgs ?vors) (zip ?expected ?modes)" and
    ret_eq: "retTy = apply_subst ?tySubst (FI_ReturnType funInfo)"
    unfolding core_impure_call_type_def by (auto simp: Let_def split: if_splits)
  have len_e: "length ?expected = length (FI_TmArgs funInfo)"
    and len_m: "length ?modes = length (FI_TmArgs funInfo)"
    and len_v: "length ?vors = length (FI_TmArgs funInfo)" by simp_all
  have args': "list_all2 ?argok (zip (map match_compile_term tmArgs) ?vors) (zip ?expected ?modes)"
  proof (rule list_all2_all_nthI)
    show "length (zip (map match_compile_term tmArgs) ?vors) = length (zip ?expected ?modes)"
      using list_all2_lengthD[OF args] by simp
    fix i assume i_lt: "i < length (zip (map match_compile_term tmArgs) ?vors)"
    hence i_lt': "i < length tmArgs" and i_lt_f: "i < length (FI_TmArgs funInfo)"
      using checks(6) by simp_all
    have zip_i: "zip tmArgs ?vors ! i = (tmArgs ! i, ?vors ! i)"
      using i_lt' i_lt_f len_v by (simp only: nth_zip)
    have zip_i': "zip (map match_compile_term tmArgs) ?vors ! i
                    = (match_compile_term (tmArgs ! i), ?vors ! i)"
      using i_lt' i_lt_f len_v by (simp only: nth_zip length_map nth_map)
    have zip_e: "zip ?expected ?modes ! i = (?expected ! i, ?modes ! i)"
      using i_lt_f len_e len_m by (simp only: nth_zip)
    have mem: "tmArgs ! i \<in> set tmArgs" using i_lt' by simp
    with ok have ok_i: "core_term_match_scrutinees_ok (tmArgs ! i)" by (simp add: list_all_iff)
    have ai0: "?argok (zip tmArgs ?vors ! i) (zip ?expected ?modes ! i)"
      by (rule list_all2_nthD[OF args]) (simp add: i_lt' i_lt_f len_v)
    hence ai: "?argok (tmArgs ! i, ?vors ! i) (?expected ! i, ?modes ! i)"
      unfolding zip_i zip_e .
    have "?argok (match_compile_term (tmArgs ! i), ?vors ! i) (?expected ! i, ?modes ! i)"
    proof (cases "?vors ! i")
      case Var
      with ai have "core_term_type env (?modes ! i) (tmArgs ! i) = Some (?expected ! i)" by simp
      from match_compile_term_type[OF this wf ok_i] Var show ?thesis by simp
    next
      case Ref
      with ai have w: "is_writable_lvalue env (tmArgs ! i)"
        and gl: "ghost_lvalue_ok env (?modes ! i) (tmArgs ! i)"
        and t: "core_term_type env (?modes ! i) (tmArgs ! i) = Some (?expected ! i)" by simp_all
      have lv: "is_lvalue (tmArgs ! i)" by (rule is_writable_lvalue_is_lvalue[OF w])
      from match_compile_term_type[OF t wf ok_i] w gl Ref show ?thesis
        by (simp add: is_writable_lvalue_match_compile_term[OF lv]
                      ghost_lvalue_ok_match_compile_term[OF lv])
    qed
    thus "?argok (zip (map match_compile_term tmArgs) ?vors ! i) (zip ?expected ?modes ! i)"
      unfolding zip_i' zip_e .
  qed
  show ?thesis
    unfolding core_impure_call_type_def
    using fi checks args' ret_eq by (simp add: Let_def)
qed

(* A one-statement list types as the statement. *)
lemma core_statement_list_type_single:
  "core_statement_list_type env ghost [stmt] = core_statement_type env ghost stmt"
  by (simp split: option.splits)

(* Lifting the per-statement theorem to statement lists. *)
lemma match_compile_statement_list_type_aux:
  assumes "\<And>stmt env env'. stmt \<in> set stmts \<Longrightarrow> core_statement_type env ghost stmt = Some env'
             \<Longrightarrow> tyenv_well_formed env \<Longrightarrow> core_statement_match_scrutinees_ok stmt
             \<Longrightarrow> core_statement_list_type env ghost (match_compile_statement stmt) = Some env'"
      and "core_statement_list_type env ghost stmts = Some env'"
      and "tyenv_well_formed env"
      and "core_statement_list_match_scrutinees_ok stmts"
  shows "core_statement_list_type env ghost (match_compile_statement_list stmts) = Some env'"
  using assms
proof (induction stmts arbitrary: env)
  case Nil
  then show ?case by simp
next
  case (Cons stmt stmts)
  from Cons.prems(2) obtain env1 where
    s: "core_statement_type env ghost stmt = Some env1" and
    rest: "core_statement_list_type env1 ghost stmts = Some env'"
    by (auto split: option.splits)
  have wf1: "tyenv_well_formed env1"
    by (rule core_statement_type_preserves_well_formed[OF s Cons.prems(3)])
  have s': "core_statement_list_type env ghost (match_compile_statement stmt) = Some env1"
    using Cons.prems(1)[OF _ s Cons.prems(3)] Cons.prems(4) by simp
  have rest': "core_statement_list_type env1 ghost (match_compile_statement_list stmts) = Some env'"
    using Cons.IH[OF _ rest wf1] Cons.prems(1) Cons.prems(4) by simp
  show ?case
    using s' rest' by (simp add: core_statement_list_type_append)
qed

theorem match_compile_statement_type:
  "core_statement_type env ghost stmt = Some env' \<Longrightarrow> tyenv_well_formed env
   \<Longrightarrow> core_statement_match_scrutinees_ok stmt
   \<Longrightarrow> core_statement_list_type env ghost (match_compile_statement stmt) = Some env'"
proof (induction stmt arbitrary: env ghost env')
  case (CoreStmt_VarDecl declGhost varName vr varTy initTm)
  show ?case
  proof (cases vr)
    case Var
    from CoreStmt_VarDecl.prems(1) Var have
      t: "core_term_type env declGhost initTm = Some varTy"
      by (auto split: if_splits)
    from match_compile_term_type[OF t CoreStmt_VarDecl.prems(2)] CoreStmt_VarDecl.prems(3)
    have t': "core_term_type env declGhost (match_compile_term initTm) = Some varTy" by simp
    from CoreStmt_VarDecl.prems(1) Var t' show ?thesis by (auto split: if_splits)
  next
    case Ref
    from CoreStmt_VarDecl.prems(1) Ref have
      lv: "is_lvalue initTm" and
      t: "core_term_type env declGhost initTm = Some varTy"
      by (auto split: if_splits)
    from match_compile_term_type[OF t CoreStmt_VarDecl.prems(2)] CoreStmt_VarDecl.prems(3)
    have t': "core_term_type env declGhost (match_compile_term initTm) = Some varTy" by simp
    from CoreStmt_VarDecl.prems(1) Ref t' lv show ?thesis
      by (auto simp: is_writable_lvalue_match_compile_term ghost_lvalue_ok_match_compile_term
               split: if_splits)
  qed
next
  case (CoreStmt_VarDeclCall declGhost varName varTy castOpt fnName tyArgs argTms)
  from CoreStmt_VarDeclCall.prems(1) obtain retTy where
    c: "core_impure_call_type env declGhost fnName tyArgs argTms = Some retTy"
    by (auto split: if_splits option.splits)
  from core_impure_call_type_match_compile[OF c CoreStmt_VarDeclCall.prems(2)]
       CoreStmt_VarDeclCall.prems(3)
  have c': "core_impure_call_type env declGhost fnName tyArgs (map match_compile_term argTms)
              = Some retTy" by simp
  from CoreStmt_VarDeclCall.prems(1) c c' show ?case by (auto split: if_splits)
next
  case (CoreStmt_Fix varName varTy)
  then show ?case by (simp add: core_statement_list_type_single)
next
  case (CoreStmt_Obtain varName varTy condTm)
  let ?env' = "env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                     TE_GhostLocals := finsert varName (TE_GhostLocals env),
                     TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
  from CoreStmt_Obtain.prems(1) have
    wk: "is_well_kinded env varTy" and
    t: "core_term_type ?env' Ghost condTm = Some CoreTy_Bool" and
    env'_eq: "env' = ?env'"
    by (auto simp: Let_def split: if_splits)
  have wf': "tyenv_well_formed ?env'"
    using tyenv_well_formed_declare_var[OF CoreStmt_Obtain.prems(2) wk, where g = Ghost
            and var = varName and c = "fminus (TE_ConstLocals env) {|varName|}"]
    by simp
  from match_compile_term_type[OF t wf'] CoreStmt_Obtain.prems(3)
  have t': "core_term_type ?env' Ghost (match_compile_term condTm) = Some CoreTy_Bool" by simp
  from wk t' env'_eq show ?case by (simp add: Let_def)
next
  case (CoreStmt_Use witnessTm)
  from CoreStmt_Use.prems(1) obtain qVar qVarTy bodyTm where
    goal: "TE_ProofGoal env = Some (CoreTm_Quantifier Quant_Exists qVar qVarTy bodyTm)" and
    t: "core_term_type env ghost witnessTm = Some qVarTy" and
    g: "ghost = Ghost" and top: "TE_ProofTopLevel env" and
    env'_eq: "env' = env \<lparr> TE_ProofGoal := Some bodyTm \<rparr>"
    by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
  from match_compile_term_type[OF t CoreStmt_Use.prems(2)] CoreStmt_Use.prems(3)
  have t': "core_term_type env ghost (match_compile_term witnessTm) = Some qVarTy" by simp
  from goal t' g top env'_eq show ?case by simp
next
  case (CoreStmt_Assign assignGhost lhsTm rhsTm)
  from CoreStmt_Assign.prems(1) obtain lhsTy where
    w: "is_writable_lvalue env lhsTm" and
    l: "core_term_type env assignGhost lhsTm = Some lhsTy" and
    r: "core_term_type env assignGhost rhsTm = Some lhsTy"
    by (auto split: if_splits option.splits)
  have lv: "is_lvalue lhsTm" by (rule is_writable_lvalue_is_lvalue[OF w])
  from match_compile_term_type[OF l CoreStmt_Assign.prems(2)] CoreStmt_Assign.prems(3)
  have l': "core_term_type env assignGhost (match_compile_term lhsTm) = Some lhsTy" by simp
  from match_compile_term_type[OF r CoreStmt_Assign.prems(2)] CoreStmt_Assign.prems(3)
  have r': "core_term_type env assignGhost (match_compile_term rhsTm) = Some lhsTy" by simp
  from CoreStmt_Assign.prems(1) l l' r' lv show ?case
    by (auto simp: is_writable_lvalue_match_compile_term ghost_lvalue_ok_match_compile_term
             split: if_splits)
next
  case (CoreStmt_AssignCall assignGhost lhsTm castOpt fnName tyArgs argTms)
  from CoreStmt_AssignCall.prems(1) obtain lhsTy retTy where
    w: "is_writable_lvalue env lhsTm" and
    l: "core_term_type env assignGhost lhsTm = Some lhsTy" and
    c: "core_impure_call_type env assignGhost fnName tyArgs argTms = Some retTy"
    by (auto split: if_splits option.splits)
  have lv: "is_lvalue lhsTm" by (rule is_writable_lvalue_is_lvalue[OF w])
  from match_compile_term_type[OF l CoreStmt_AssignCall.prems(2)] CoreStmt_AssignCall.prems(3)
  have l': "core_term_type env assignGhost (match_compile_term lhsTm) = Some lhsTy" by simp
  from core_impure_call_type_match_compile[OF c CoreStmt_AssignCall.prems(2)]
       CoreStmt_AssignCall.prems(3)
  have c': "core_impure_call_type env assignGhost fnName tyArgs (map match_compile_term argTms)
              = Some retTy" by simp
  from CoreStmt_AssignCall.prems(1) l l' c c' lv show ?case
    by (auto simp: is_writable_lvalue_match_compile_term ghost_lvalue_ok_match_compile_term
             split: if_splits)
next
  case (CoreStmt_Swap swapGhost lhsTm rhsTm)
  from CoreStmt_Swap.prems(1) obtain lhsTy where
    wl: "is_writable_lvalue env lhsTm" and
    wr: "is_writable_lvalue env rhsTm" and
    l: "core_term_type env swapGhost lhsTm = Some lhsTy" and
    r: "core_term_type env swapGhost rhsTm = Some lhsTy"
    by (auto split: if_splits option.splits)
  have lvl: "is_lvalue lhsTm" by (rule is_writable_lvalue_is_lvalue[OF wl])
  have lvr: "is_lvalue rhsTm" by (rule is_writable_lvalue_is_lvalue[OF wr])
  from match_compile_term_type[OF l CoreStmt_Swap.prems(2)] CoreStmt_Swap.prems(3)
  have l': "core_term_type env swapGhost (match_compile_term lhsTm) = Some lhsTy" by simp
  from match_compile_term_type[OF r CoreStmt_Swap.prems(2)] CoreStmt_Swap.prems(3)
  have r': "core_term_type env swapGhost (match_compile_term rhsTm) = Some lhsTy" by simp
  from CoreStmt_Swap.prems(1) l l' r' lvl lvr show ?case
    by (auto simp: is_writable_lvalue_match_compile_term ghost_lvalue_ok_match_compile_term
             split: if_splits)
next
  case (CoreStmt_Return tm)
  from CoreStmt_Return.prems(1) have
    t: "core_term_type env ghost tm = Some (TE_ReturnType env)"
    by (auto split: if_splits)
  from match_compile_term_type[OF t CoreStmt_Return.prems(2)] CoreStmt_Return.prems(3)
  have t': "core_term_type env ghost (match_compile_term tm) = Some (TE_ReturnType env)" by simp
  from CoreStmt_Return.prems(1) t' show ?case by (auto split: if_splits)
next
  case (CoreStmt_Assert condOpt proofBody)
  then show ?case by (simp add: core_statement_list_type_single)
next
  case (CoreStmt_Assume tm)
  from CoreStmt_Assume.prems(1) have t: "core_term_type env Ghost tm = Some CoreTy_Bool"
    and env'_eq: "env' = env"
    by (auto split: if_splits)
  from match_compile_term_type[OF t CoreStmt_Assume.prems(2)] CoreStmt_Assume.prems(3)
  have "core_term_type env Ghost (match_compile_term tm) = Some CoreTy_Bool" by simp
  with env'_eq show ?case by simp
next
  case (CoreStmt_While whileGhost condTm invars decrTm body)
  let ?env1 = "env \<lparr> TE_ProofTopLevel := False \<rparr>"
  from CoreStmt_While.prems(1) obtain envB where
    gm: "ghost = Ghost \<longrightarrow> whileGhost = Ghost" and
    c: "core_term_type env whileGhost condTm = Some CoreTy_Bool" and
    inv: "list_all (\<lambda>inv. core_term_type env Ghost inv = Some CoreTy_Bool) invars" and
    decr: "has_valid_decreases_type env decrTm" and
    b: "core_statement_list_type ?env1 whileGhost body = Some envB" and
    env'_eq: "env' = env"
    by (auto split: if_splits option.splits CoreType.splits)
  from CoreStmt_While.prems(3) have
    ok_c: "core_term_match_scrutinees_ok condTm" and
    ok_inv: "list_all core_term_match_scrutinees_ok invars" and
    ok_decr: "case decrTm of None \<Rightarrow> True | Some tm \<Rightarrow> core_term_match_scrutinees_ok tm" and
    ok_body: "core_statement_list_match_scrutinees_ok body"
    by simp_all
  have c': "core_term_type env whileGhost (match_compile_term condTm) = Some CoreTy_Bool"
    by (rule match_compile_term_type[OF c CoreStmt_While.prems(2) ok_c])
  have inv': "list_all (\<lambda>inv. core_term_type env Ghost inv = Some CoreTy_Bool)
                (map match_compile_term invars)"
    using inv ok_inv match_compile_term_type[OF _ CoreStmt_While.prems(2)]
    by (auto simp: list_all_iff)
  have decr': "has_valid_decreases_type env (map_option match_compile_term decrTm)"
    using decr ok_decr match_compile_term_type[OF _ CoreStmt_While.prems(2)]
    by (cases decrTm) (auto split: option.splits)
  have wf1: "tyenv_well_formed ?env1"
    using CoreStmt_While.prems(2) by (simp add: tyenv_well_formed_TE_ProofTopLevel_irrelevant)
  have b': "core_statement_list_type ?env1 whileGhost (match_compile_statement_list body) = Some envB"
  proof (rule match_compile_statement_list_type_aux[OF _ b wf1 ok_body])
    fix stmt env env'
    assume s_in: "stmt \<in> set body"
    show "core_statement_type env whileGhost stmt = Some env' \<Longrightarrow> tyenv_well_formed env
          \<Longrightarrow> core_statement_match_scrutinees_ok stmt
          \<Longrightarrow> core_statement_list_type env whileGhost (match_compile_statement stmt) = Some env'"
      by (rule CoreStmt_While.IH[OF s_in])
  qed
  show ?case using gm c' inv' decr' b' env'_eq by simp
next
  case (CoreStmt_Match matchGhost scrut arms)
  let ?env1 = "env \<lparr> TE_ProofTopLevel := False \<rparr>"
  let ?arms' = "map (\<lambda>(p, body). (p, match_compile_statement_list body)) arms"
  from CoreStmt_Match.prems(1) obtain scrutTy where
    gm: "ghost = Ghost \<longrightarrow> matchGhost = Ghost" and
    s: "core_term_type env matchGhost scrut = Some scrutTy" and
    pats: "list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst arms)" and
    bodies: "list_all (\<lambda>body. core_statement_list_type ?env1 matchGhost body \<noteq> None) (map snd arms)" and
    env'_eq: "env' = env"
    by (auto simp: Let_def split: if_splits option.splits)
  from CoreStmt_Match.prems(3) have
    ok_s: "core_term_match_scrutinees_ok scrut" and
    ok_arms: "list_all (\<lambda>(_, body). core_statement_list_match_scrutinees_ok body) arms"
    by simp_all
  have s': "core_term_type env matchGhost (match_compile_term scrut) = Some scrutTy"
    by (rule match_compile_term_type[OF s CoreStmt_Match.prems(2) ok_s])
  have wf1: "tyenv_well_formed ?env1"
    using CoreStmt_Match.prems(2) by (simp add: tyenv_well_formed_TE_ProofTopLevel_irrelevant)
  have bodies': "core_statement_list_type ?env1 matchGhost (match_compile_statement_list body) \<noteq> None"
    if arm_in: "(p, body) \<in> set arms" for p body
  proof -
    from bodies arm_in obtain envB where
      b: "core_statement_list_type ?env1 matchGhost body = Some envB"
      by (auto simp: list_all_iff)
    from ok_arms arm_in have ok_b: "core_statement_list_match_scrutinees_ok body"
      by (auto simp: list_all_iff)
    have "core_statement_list_type ?env1 matchGhost (match_compile_statement_list body) = Some envB"
    proof (rule match_compile_statement_list_type_aux[OF _ b wf1 ok_b])
      fix stmt env env'
      assume s_in: "stmt \<in> set body"
      have sn: "body \<in> Basic_BNFs.snds (p, body)" by simp
      show "core_statement_type env matchGhost stmt = Some env' \<Longrightarrow> tyenv_well_formed env
            \<Longrightarrow> core_statement_match_scrutinees_ok stmt
            \<Longrightarrow> core_statement_list_type env matchGhost (match_compile_statement stmt) = Some env'"
        by (rule CoreStmt_Match.IH[OF arm_in sn s_in])
    qed
    thus ?thesis by simp
  qed
  show ?case
  proof (cases "arms_flat arms")
    case True
    have pats': "list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst ?arms')"
      using pats by (simp add: case_prod_unfold comp_def)
    have bodies'': "list_all (\<lambda>body. core_statement_list_type ?env1 matchGhost body \<noteq> None)
                      (map snd ?arms')"
      using bodies' by (auto simp: list_all_iff)
    from True gm s' pats' bodies'' env'_eq show ?thesis by (simp add: Let_def)
  next
    case False
    hence ne': "?arms' \<noteq> []" by (auto simp: arms_flat_def)
    have pats': "list_all (\<lambda>(p, _). pattern_compatible env p scrutTy) ?arms'"
      using pats by (auto simp: list_all_iff)
    have "core_statement_list_type env ghost
            (compile_match_statement matchGhost (match_compile_term scrut) ?arms') = Some env"
      by (rule compile_match_statement_type[OF gm s' ne' pats' CoreStmt_Match.prems(2)])
         (use bodies' in auto)
    with False env'_eq show ?thesis by simp
  qed
next
  case (CoreStmt_ShowHide sh name)
  then show ?case by (simp add: core_statement_list_type_single)
next
  case (CoreStmt_Block body)
  let ?env1 = "env \<lparr> TE_ProofTopLevel := False \<rparr>"
  from CoreStmt_Block.prems(1) obtain envB where
    b: "core_statement_list_type ?env1 ghost body = Some envB" and
    env'_eq: "env' = env"
    by (auto split: option.splits)
  have wf1: "tyenv_well_formed ?env1"
    using CoreStmt_Block.prems(2) by (simp add: tyenv_well_formed_TE_ProofTopLevel_irrelevant)
  have b': "core_statement_list_type ?env1 ghost (match_compile_statement_list body) = Some envB"
  proof (rule match_compile_statement_list_type_aux[OF _ b wf1])
    from CoreStmt_Block.prems(3) show "core_statement_list_match_scrutinees_ok body" by simp
    fix stmt env env'
    assume s_in: "stmt \<in> set body"
    show "core_statement_type env ghost stmt = Some env' \<Longrightarrow> tyenv_well_formed env
          \<Longrightarrow> core_statement_match_scrutinees_ok stmt
          \<Longrightarrow> core_statement_list_type env ghost (match_compile_statement stmt) = Some env'"
      by (rule CoreStmt_Block.IH[OF s_in])
  qed
  show ?case using b' env'_eq by simp
qed

theorem match_compile_statement_list_type:
  "core_statement_list_type env ghost stmts = Some env' \<Longrightarrow> tyenv_well_formed env
   \<Longrightarrow> core_statement_list_match_scrutinees_ok stmts
   \<Longrightarrow> core_statement_list_type env ghost (match_compile_statement_list stmts) = Some env'"
  by (rule match_compile_statement_list_type_aux) (rule match_compile_statement_type)


section \<open>Modules\<close>

(* The pass preserves well-typedness of a normalized module (one whose type
   substitution is empty, as after whole-program linking and normalization;
   erase_ghost_module_well_typed has the same hypothesis). The type
   environment is unchanged, so only the function bodies are at issue. *)
theorem match_compile_module_well_typed:
  assumes wt: "core_module_well_typed m"
      and norm: "CM_TypeSubst m = fmempty"
      and ok: "core_module_match_scrutinees_ok m"
  shows "core_module_well_typed (match_compile_module m)"
proof -
  let ?env = "CM_TyEnv m"
  let ?m' = "match_compile_module m"
  have nwt: "normalized_module_well_typed m"
    using wt core_module_well_typed_on_normalized[OF norm] by simp
  hence wf: "tyenv_well_formed ?env"
    and scope: "tyenv_module_scope ?env"
    and glob: "module_globals_well_typed ?env (CM_GlobalVars m)"
    and funs: "module_functions_well_typed ?env (CM_Functions m)"
    unfolding normalized_module_well_typed_def by simp_all
  have funs': "module_functions_well_typed ?env (CM_Functions ?m')"
    unfolding module_functions_well_typed_def
  proof (intro allI impI)
    fix name f
    assume lk: "fmlookup (CM_Functions ?m') name = Some f"
    then obtain f0 where lk0: "fmlookup (CM_Functions m) name = Some f0"
      and f: "f = match_compile_function f0"
      by (auto simp: match_compile_module_fun_lookup)
    from funs lk0 obtain info where
      info: "fmlookup (TE_Functions ?env) name = Some info" and
      len: "length (CF_Args f0) = length (FI_TmArgs info)" and
      dist: "distinct (CF_Args f0)" and
      body: "case CF_Body f0 of
               None \<Rightarrow> True
             | Some body \<Rightarrow> core_statement_list_type (module_body_env_for ?env (CF_Args f0) info)
                             (FI_Ghost info) body \<noteq> None" and
      contracts: "fun_contracts_well_typed ?env info"
      unfolding module_functions_well_typed_def by blast
    have body': "case CF_Body f of
                   None \<Rightarrow> True
                 | Some body \<Rightarrow> core_statement_list_type (module_body_env_for ?env (CF_Args f) info)
                                 (FI_Ghost info) body \<noteq> None"
    proof (cases "CF_Body f0")
      case None
      with f show ?thesis by simp
    next
      case (Some body0)
      with body obtain env' where
        t: "core_statement_list_type (module_body_env_for ?env (CF_Args f0) info)
              (FI_Ghost info) body0 = Some env'"
        by auto
      have wf_body: "tyenv_well_formed (module_body_env_for ?env (CF_Args f0) info)"
        by (rule module_body_env_for_well_formed[OF wf info len])
      from ok lk0 Some have ok0: "core_statement_list_match_scrutinees_ok body0"
        unfolding core_module_match_scrutinees_ok_iff by blast
      have "core_statement_list_type (module_body_env_for ?env (CF_Args f0) info)
              (FI_Ghost info) (match_compile_statement_list body0) = Some env'"
        by (rule match_compile_statement_list_type[OF t wf_body ok0])
      with f Some show ?thesis by simp
    qed
    show "\<exists>info. fmlookup (TE_Functions ?env) name = Some info \<and>
               length (CF_Args f) = length (FI_TmArgs info) \<and>
               distinct (CF_Args f) \<and>
               (case CF_Body f of
                  None \<Rightarrow> True
                | Some body \<Rightarrow> core_statement_list_type (module_body_env_for ?env (CF_Args f) info)
                                (FI_Ghost info) body \<noteq> None) \<and>
               fun_contracts_well_typed ?env info"
      using info len dist body' contracts f by auto
  qed
  have nwt': "normalized_module_well_typed ?m'"
    unfolding normalized_module_well_typed_def
    using wf scope glob funs' by simp
  have norm': "CM_TypeSubst ?m' = fmempty" using norm by simp
  show ?thesis
    using core_module_well_typed_on_normalized[OF norm'] nwt' by simp
qed

end
