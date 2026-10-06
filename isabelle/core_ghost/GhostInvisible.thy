theory GhostInvisible
  imports ErasedState "../interpreter/CoreInterpFrame" "../interpreter/CoreInterpWorld"
begin

(* Ghost statements are invisible to the erased program.

   A statement that is well-typed in Ghost mode, when run in the full state, does
   not return, and leaves the full state related to the *unchanged* erased
   state. The reasons:

    - it declares only ghost variables, in store cells outside the embedding;
    - it writes only through lvalues whose base variable is ghost
      (ghost_lvalue_ok), so only to cells outside the embedding;
    - a call that it makes changes only the cells passed as Ref arguments (the
      frame lemma), and those arguments are again ghost lvalues;
    - a call that it makes is a call of a pure function, which leaves the
      world unchanged;
    - it contains no Return, because the enclosing function is not ghost.

   This is what the simulation proof needs for each statement that
   erase_ghost_statement deletes: see erased_statement_invisible at the end. *)


(* ========================================================================== *)
(* A fact about the function table *)
(* ========================================================================== *)

(* The function table of the state agrees with the signatures of the
   environment about which parameters are Var and which are Ref. This is the
   one fact about the function table that this file needs. It follows from
   funs_exist_in_state (see funs_exist_in_state_var_ref_agree below). *)
definition fun_var_ref_agree ::
    "(string, FunInfo) fmap \<Rightarrow> (string, 'w InterpFun) fmap \<Rightarrow> bool" where
  "fun_var_ref_agree funInfos funs \<equiv>
    \<forall>fnName info f.
      fmlookup funInfos fnName = Some info \<longrightarrow> fmlookup funs fnName = Some f \<longrightarrow>
        map (fst \<circ> snd) (IF_Args f) = map (fst \<circ> snd) (FI_TmArgs info)"

lemma fun_var_ref_agree_Ref:
  assumes "fun_var_ref_agree funInfos funs"
    and "fmlookup funInfos fnName = Some info"
    and "fmlookup funs fnName = Some f"
    and "i < length (IF_Args f)"
    and "fst (snd (IF_Args f ! i)) = Ref"
  shows "fst (snd (FI_TmArgs info ! i)) = Ref"
proof -
  from assms(1,2,3)
  have eq: "map (fst \<circ> snd) (IF_Args f) = map (fst \<circ> snd) (FI_TmArgs info)"
    unfolding fun_var_ref_agree_def by blast
  from eq have len: "length (IF_Args f) = length (FI_TmArgs info)"
    by (rule map_eq_imp_length_eq)
  from assms(4) len have i_lt: "i < length (FI_TmArgs info)" by simp
  from eq
  have "map (fst \<circ> snd) (IF_Args f) ! i = map (fst \<circ> snd) (FI_TmArgs info) ! i"
    by simp
  with assms(4) i_lt
  have "fst (snd (IF_Args f ! i)) = fst (snd (FI_TmArgs info ! i))" by simp
  with assms(5) show ?thesis by simp
qed

lemma funs_exist_in_state_var_ref_agree:
  assumes "funs_exist_in_state state env"
  shows "fun_var_ref_agree (TE_Functions env) (IS_Functions state)"
  unfolding fun_var_ref_agree_def
proof (intro allI impI)
  fix fnName info f
  assume info: "fmlookup (TE_Functions env) fnName = Some info"
    and f: "fmlookup (IS_Functions state) fnName = Some f"
  from assms info
  have "case fmlookup (IS_Functions state) fnName of
          None \<Rightarrow> False
        | Some interpFun \<Rightarrow> fun_info_matches_interp_fun env info interpFun"
    unfolding funs_exist_in_state_def by blast
  with f have "fun_info_matches_interp_fun env info f" by simp
  then have la: "list_all2 (\<lambda>(_, vor1, gh1) (_, vor2, gh2). vor1 = vor2 \<and> gh1 = gh2)
                           (FI_TmArgs info) (IF_Args f)"
    by (simp add: fun_info_matches_interp_fun_def)
  have "map (fst \<circ> snd) (FI_TmArgs info) = map (fst \<circ> snd) (IF_Args f)"
    using la by (induction rule: list_all2_induct) (auto simp: case_prod_beta)
  then show "map (fst \<circ> snd) (IF_Args f) = map (fst \<circ> snd) (FI_TmArgs info)" by simp
qed


(* ========================================================================== *)
(* Taking the state relation apart *)
(* ========================================================================== *)

lemma store_erasedD:
  assumes "store_erased emb full erased"
  shows "length emb = length (IS_Store erased)"
    and "distinct emb"
    and "\<And>i. i < length emb \<Longrightarrow> emb ! i < length (IS_Store full)"
    and "\<And>i. i < length emb \<Longrightarrow> IS_Store erased ! i = IS_Store full ! (emb ! i)"
  using assms unfolding store_erased_def by blast+

(* Every address in the embedding is inside the full store. *)
lemma store_erased_emb_bound:
  assumes "store_erased emb full erased" and "a \<in> set emb"
  shows "a < length (IS_Store full)"
proof -
  from assms(2) obtain i where i: "i < length emb" and e: "emb ! i = a"
    by (auto simp: in_set_conv_nth)
  from store_erasedD(3)[OF assms(1) i] e show ?thesis by simp
qed

lemma locals_erasedD:
  assumes "locals_erased env emb full erased" and "\<not> tyenv_var_ghost env name"
  shows "rel_option (\<lambda>i addr. i < length emb \<and> addr = emb ! i)
                    (fmlookup (IS_Locals erased) name) (fmlookup (IS_Locals full) name)"
    and "rel_option (\<lambda>(i, path) (addr, path'). i < length emb \<and> addr = emb ! i \<and> path = path')
                    (fmlookup (IS_Refs erased) name) (fmlookup (IS_Refs full) name)"
    and "name |\<in>| IS_ConstLocals erased \<longleftrightarrow> name |\<in>| IS_ConstLocals full"
proof -
  note x = assms(1)[unfolded locals_erased_def, rule_format, OF assms(2)]
  show "rel_option (\<lambda>i addr. i < length emb \<and> addr = emb ! i)
                   (fmlookup (IS_Locals erased) name) (fmlookup (IS_Locals full) name)"
    by (rule x[THEN conjunct1])
  show "rel_option (\<lambda>(i, path) (addr, path'). i < length emb \<and> addr = emb ! i \<and> path = path')
                   (fmlookup (IS_Refs erased) name) (fmlookup (IS_Refs full) name)"
    by (rule x[THEN conjunct2, THEN conjunct1])
  show "name |\<in>| IS_ConstLocals erased \<longleftrightarrow> name |\<in>| IS_ConstLocals full"
    by (rule x[THEN conjunct2, THEN conjunct2])
qed

lemma ghost_locals_separateI:
  assumes "\<And>name addr. tyenv_var_ghost env name
              \<Longrightarrow> fmlookup (IS_Locals full) name = Some addr
              \<Longrightarrow> addr < length (IS_Store full) \<and> addr \<notin> set emb"
    and "\<And>name addr path. tyenv_var_ghost env name
              \<Longrightarrow> fmlookup (IS_Refs full) name = Some (addr, path)
              \<Longrightarrow> addr < length (IS_Store full) \<and> addr \<notin> set emb"
  shows "ghost_locals_separate env emb full"
  unfolding ghost_locals_separate_def using assms by blast

lemma ghost_locals_separateD:
  assumes "ghost_locals_separate env emb full" and "tyenv_var_ghost env name"
  shows "\<And>addr. fmlookup (IS_Locals full) name = Some addr
              \<Longrightarrow> addr < length (IS_Store full) \<and> addr \<notin> set emb"
    and "\<And>addr path. fmlookup (IS_Refs full) name = Some (addr, path)
              \<Longrightarrow> addr < length (IS_Store full) \<and> addr \<notin> set emb"
  using assms unfolding ghost_locals_separate_def by blast+

(* The parts of the relation depend on the full state only through some of its
   fields, and on the environment only through TE_LocalVars, TE_GhostLocals
   and TE_Functions. *)

lemma funs_erased_cong:
  assumes "TE_Functions env2 = TE_Functions env"
    and "IS_Functions full2 = IS_Functions full"
  shows "funs_erased env2 full2 erased = funs_erased env full erased"
  using assms by (simp add: funs_erased_def)

lemma locals_erased_cong_state:
  assumes "IS_Locals full' = IS_Locals full"
    and "IS_Refs full' = IS_Refs full"
    and "IS_ConstLocals full' = IS_ConstLocals full"
  shows "locals_erased env emb full' erased = locals_erased env emb full erased"
  using assms by (simp add: locals_erased_def)

lemma ghost_locals_separate_cong_state:
  assumes "IS_Locals full' = IS_Locals full"
    and "IS_Refs full' = IS_Refs full"
    and "length (IS_Store full') = length (IS_Store full)"
  shows "ghost_locals_separate env emb full' = ghost_locals_separate env emb full"
  using assms by (simp add: ghost_locals_separate_def)

lemma state_erased_cong_env:
  assumes "TE_LocalVars env2 = TE_LocalVars env"
    and "TE_GhostLocals env2 = TE_GhostLocals env"
    and "TE_Functions env2 = TE_Functions env"
  shows "state_erased env2 emb full erased = state_erased env emb full erased"
  using assms
  by (simp add: state_erased_def heap_erased_def funs_erased_def locals_erased_def
                ghost_locals_separate_def tyenv_var_ghost_def)

lemma state_erased_TE_ProofTopLevel_irrelevant [simp]:
  "state_erased (env \<lparr> TE_ProofTopLevel := b \<rparr>) emb full erased
     = state_erased env emb full erased"
  by (rule state_erased_cong_env) simp_all


(* ========================================================================== *)
(* Ghost cells *)
(* ========================================================================== *)

(* The cell of a ghost variable is inside the full store and outside the
   embedding. *)
lemma ghost_var_addr_separate:
  assumes "ghost_locals_separate env emb full"
    and "tyenv_var_ghost env name"
    and "var_addr full name = Some addr"
  shows "addr < length (IS_Store full)" and "addr \<notin> set emb"
proof -
  have both: "addr < length (IS_Store full) \<and> addr \<notin> set emb"
  proof (cases "fmlookup (IS_Locals full) name")
    case (Some a)
    with assms(3) have "a = addr" by (simp add: var_addr_def)
    with Some have "fmlookup (IS_Locals full) name = Some addr" by simp
    then show ?thesis by (rule ghost_locals_separateD(1)[OF assms(1,2)])
  next
    case None
    with assms(3) obtain path where "fmlookup (IS_Refs full) name = Some (addr, path)"
      by (cases "fmlookup (IS_Refs full) name") (auto simp: var_addr_def)
    then show ?thesis by (rule ghost_locals_separateD(2)[OF assms(1,2)])
  qed
  from both show "addr < length (IS_Store full)" by simp
  from both show "addr \<notin> set emb" by simp
qed

(* So is the cell that an lvalue written by ghost code denotes: its address is
   the address of its base variable, which is ghost. *)
lemma ghost_lvalue_addr_separate:
  assumes "ghost_locals_separate env emb full"
    and "ghost_lvalue_ok env Ghost tm"
    and "interp_writable_lvalue d fuel full tm = Inr (addr, path)"
  shows "addr < length (IS_Store full)" and "addr \<notin> set emb"
proof -
  from interp_writable_lvalue_addr[OF assms(3)] obtain name where
    base: "lvalue_base_name tm = Some name" and va: "var_addr full name = Some addr"
    by blast
  from assms(2) base have g: "tyenv_var_ghost env name"
    by (simp add: ghost_lvalue_ok_def)
  show "addr < length (IS_Store full)"
    by (rule ghost_var_addr_separate(1)[OF assms(1) g va])
  show "addr \<notin> set emb"
    by (rule ghost_var_addr_separate(2)[OF assms(1) g va])
qed


(* ========================================================================== *)
(* Steps of the full state that keep it related to the same erased state *)
(* ========================================================================== *)

(* The general form. The full state goes from full to full', and the
   environment from env to env'. The relation to erased is kept if:

    - the globals, functions, type arguments, default constructors and world
      are unchanged;
    - the store has not shrunk, and its cells in the embedding are unchanged;
    - a name that is not ghost afterwards was not ghost before, and is bound
      as before;
    - the names that are ghost afterwards are bound to ghost cells. *)
lemma state_erased_stepI:
  assumes rel: "state_erased env emb full erased"
    and fns: "TE_Functions env' = TE_Functions env"
    and st: "static_parts_eq full full'"
    and world: "IS_World full' = IS_World full"
    and len: "length (IS_Store full) \<le> length (IS_Store full')"
    and cells: "\<And>a. a \<in> set emb \<Longrightarrow> IS_Store full' ! a = IS_Store full ! a"
    and nonghost: "\<And>name. \<not> tyenv_var_ghost env' name \<Longrightarrow>
            \<not> tyenv_var_ghost env name \<and>
            fmlookup (IS_Locals full') name = fmlookup (IS_Locals full) name \<and>
            fmlookup (IS_Refs full') name = fmlookup (IS_Refs full) name \<and>
            (name |\<in>| IS_ConstLocals full' \<longleftrightarrow> name |\<in>| IS_ConstLocals full)"
    and ghost': "ghost_locals_separate env' emb full'"
  shows "state_erased env' emb full' erased"
proof -
  from rel have heap: "heap_erased env emb full erased"
    and ty: "IS_TyArgs erased = IS_TyArgs full"
    and loc: "locals_erased env emb full erased"
    by (simp_all add: state_erased_def)
  from heap have se: "store_erased emb full erased" by (simp add: heap_erased_def)
  note stD = static_parts_eqD[OF st]

  have se': "store_erased emb full' erased"
    unfolding store_erased_def
  proof (intro conjI allI impI)
    show "length emb = length (IS_Store erased)" by (rule store_erasedD(1)[OF se])
    show "distinct emb" by (rule store_erasedD(2)[OF se])
  next
    fix i assume i_lt: "i < length emb"
    note b = store_erasedD(3)[OF se i_lt]
    note v = store_erasedD(4)[OF se i_lt]
    from i_lt have mem: "emb ! i \<in> set emb" by simp
    show "emb ! i < length (IS_Store full')" using b len by simp
    show "IS_Store erased ! i = IS_Store full' ! (emb ! i)" using v cells[OF mem] by simp
  qed

  have heap': "heap_erased env' emb full' erased"
    unfolding heap_erased_def
  proof (intro conjI)
    show "IS_Globals erased = IS_Globals full'"
      using heap stD(1) by (simp add: heap_erased_def)
    show "IS_DefaultCtors erased = IS_DefaultCtors full'"
      using heap stD(4) by (simp add: heap_erased_def)
    show "IS_World erased = IS_World full'"
      using heap world by (simp add: heap_erased_def)
    show "funs_erased env' full' erased"
    proof -
      have "funs_erased env' full' erased = funs_erased env full erased"
        by (rule funs_erased_cong[OF fns stD(2)])
      moreover from heap have "funs_erased env full erased" by (simp add: heap_erased_def)
      ultimately show ?thesis by (rule iffD2)
    qed
    show "store_erased emb full' erased" by (rule se')
  qed

  have ty': "IS_TyArgs erased = IS_TyArgs full'" using ty stD(3) by simp

  have loc': "locals_erased env' emb full' erased"
    unfolding locals_erased_def
  proof (intro allI impI)
    fix name assume ng': "\<not> tyenv_var_ghost env' name"
    note n = nonghost[OF ng']
    from n have ng: "\<not> tyenv_var_ghost env name" by simp
    from n have l: "fmlookup (IS_Locals full') name = fmlookup (IS_Locals full) name"
      and r: "fmlookup (IS_Refs full') name = fmlookup (IS_Refs full) name"
      and c: "(name |\<in>| IS_ConstLocals full') = (name |\<in>| IS_ConstLocals full)"
      by simp_all
    show "rel_option (\<lambda>i addr. i < length emb \<and> addr = emb ! i)
                     (fmlookup (IS_Locals erased) name) (fmlookup (IS_Locals full') name) \<and>
          rel_option (\<lambda>(i, path) (addr, path'). i < length emb \<and> addr = emb ! i \<and> path = path')
                     (fmlookup (IS_Refs erased) name) (fmlookup (IS_Refs full') name) \<and>
          (name |\<in>| IS_ConstLocals erased \<longleftrightarrow> name |\<in>| IS_ConstLocals full')"
      unfolding l r c by (intro conjI locals_erasedD[OF loc ng])
  qed

  show ?thesis
    unfolding state_erased_def by (intro conjI heap' ty' loc' ghost')
qed

(* What declaring a ghost variable does to the ghost-ness of names. *)
lemma ghost_decl_var_ghost:
  assumes "TE_LocalVars env' = fmupd varName ty (TE_LocalVars env)"
    and "TE_GhostLocals env' = finsert varName (TE_GhostLocals env)"
  shows "tyenv_var_ghost env' varName"
    and "\<And>name. name \<noteq> varName \<Longrightarrow> tyenv_var_ghost env' name = tyenv_var_ghost env name"
proof -
  show "tyenv_var_ghost env' varName"
    by (simp add: tyenv_var_ghost_def assms)
next
  fix name assume ne: "name \<noteq> varName"
  then have ne': "varName \<noteq> name" by blast
  show "tyenv_var_ghost env' name = tyenv_var_ghost env name"
    using ne ne' by (simp add: tyenv_var_ghost_def assms)
qed

(* Declaring a ghost variable in a freshly allocated cell. *)
lemma state_erased_bind_ghost_fresh:
  assumes rel: "state_erased env emb full erased"
    and gv: "tyenv_var_ghost env' varName"
    and others: "\<And>name. name \<noteq> varName
                    \<Longrightarrow> tyenv_var_ghost env' name = tyenv_var_ghost env name"
    and fns: "TE_Functions env' = TE_Functions env"
    and st: "static_parts_eq full full'"
    and world: "IS_World full' = IS_World full"
    and store': "IS_Store full' = IS_Store full @ [val]"
    and locals': "IS_Locals full' = fmupd varName (length (IS_Store full)) (IS_Locals full)"
    and refs': "IS_Refs full' = fmdrop varName (IS_Refs full)"
    and consts': "\<And>name. name \<noteq> varName \<Longrightarrow>
                    (name |\<in>| IS_ConstLocals full' \<longleftrightarrow> name |\<in>| IS_ConstLocals full)"
  shows "state_erased env' emb full' erased"
proof -
  from rel have gh: "ghost_locals_separate env emb full" by (simp add: state_erased_def)
  from rel have se: "store_erased emb full erased"
    by (simp add: state_erased_def heap_erased_def)
  \<comment> \<open>The new cell is not in the embedding. \<close>
  have fresh: "length (IS_Store full) \<notin> set emb"
  proof
    assume "length (IS_Store full) \<in> set emb"
    from store_erased_emb_bound[OF se this] show False by simp
  qed
  show ?thesis
  proof (rule state_erased_stepI[OF rel fns st world])
    show "length (IS_Store full) \<le> length (IS_Store full')" by (simp add: store')
  next
    fix a assume a_in: "a \<in> set emb"
    from store_erased_emb_bound[OF se a_in]
    show "IS_Store full' ! a = IS_Store full ! a" by (simp add: store' nth_append)
  next
    fix name assume ng': "\<not> tyenv_var_ghost env' name"
    from ng' gv have ne: "name \<noteq> varName" by auto
    from ne have ne': "varName \<noteq> name" by blast
    from ng' others[OF ne] have ng: "\<not> tyenv_var_ghost env name" by simp
    show "\<not> tyenv_var_ghost env name \<and>
          fmlookup (IS_Locals full') name = fmlookup (IS_Locals full) name \<and>
          fmlookup (IS_Refs full') name = fmlookup (IS_Refs full) name \<and>
          (name |\<in>| IS_ConstLocals full' \<longleftrightarrow> name |\<in>| IS_ConstLocals full)"
      using ng ne ne' consts'[OF ne] by (simp add: locals' refs')
  next
    show "ghost_locals_separate env' emb full'"
    proof (rule ghost_locals_separateI)
      fix name a
      assume g: "tyenv_var_ghost env' name"
        and l: "fmlookup (IS_Locals full') name = Some a"
      show "a < length (IS_Store full') \<and> a \<notin> set emb"
      proof (cases "name = varName")
        case True
        with l have "a = length (IS_Store full)" by (simp add: locals')
        with fresh show ?thesis by (simp add: store')
      next
        case False
        then have ne': "varName \<noteq> name" by blast
        from g others[OF False] have g0: "tyenv_var_ghost env name" by simp
        from l ne' have l0: "fmlookup (IS_Locals full) name = Some a"
          by (simp add: locals')
        from ghost_locals_separateD(1)[OF gh g0 l0] show ?thesis by (simp add: store')
      qed
    next
      fix name a p
      assume g: "tyenv_var_ghost env' name"
        and r: "fmlookup (IS_Refs full') name = Some (a, p)"
      show "a < length (IS_Store full') \<and> a \<notin> set emb"
      proof (cases "name = varName")
        case True
        with r show ?thesis by (simp add: refs')
      next
        case False
        then have ne': "varName \<noteq> name" by blast
        from g others[OF False] have g0: "tyenv_var_ghost env name" by simp
        from r ne' have r0: "fmlookup (IS_Refs full) name = Some (a, p)"
          by (simp add: refs')
        from ghost_locals_separateD(2)[OF gh g0 r0] show ?thesis by (simp add: store')
      qed
    qed
  qed
qed

(* Declaring a ghost variable as a ref into an existing ghost cell. *)
lemma state_erased_bind_ghost_ref:
  assumes rel: "state_erased env emb full erased"
    and gv: "tyenv_var_ghost env' varName"
    and others: "\<And>name. name \<noteq> varName
                    \<Longrightarrow> tyenv_var_ghost env' name = tyenv_var_ghost env name"
    and fns: "TE_Functions env' = TE_Functions env"
    and st: "static_parts_eq full full'"
    and world: "IS_World full' = IS_World full"
    and store': "IS_Store full' = IS_Store full"
    and locals': "IS_Locals full' = fmdrop varName (IS_Locals full)"
    and refs': "IS_Refs full' = fmupd varName (addr, path) (IS_Refs full)"
    and addr_lt: "addr < length (IS_Store full)"
    and addr_notin: "addr \<notin> set emb"
    and consts': "\<And>name. name \<noteq> varName \<Longrightarrow>
                    (name |\<in>| IS_ConstLocals full' \<longleftrightarrow> name |\<in>| IS_ConstLocals full)"
  shows "state_erased env' emb full' erased"
proof -
  from rel have gh: "ghost_locals_separate env emb full" by (simp add: state_erased_def)
  show ?thesis
  proof (rule state_erased_stepI[OF rel fns st world])
    show "length (IS_Store full) \<le> length (IS_Store full')" by (simp add: store')
  next
    fix a assume "a \<in> set emb"
    show "IS_Store full' ! a = IS_Store full ! a" by (simp add: store')
  next
    fix name assume ng': "\<not> tyenv_var_ghost env' name"
    from ng' gv have ne: "name \<noteq> varName" by auto
    from ne have ne': "varName \<noteq> name" by blast
    from ng' others[OF ne] have ng: "\<not> tyenv_var_ghost env name" by simp
    show "\<not> tyenv_var_ghost env name \<and>
          fmlookup (IS_Locals full') name = fmlookup (IS_Locals full) name \<and>
          fmlookup (IS_Refs full') name = fmlookup (IS_Refs full) name \<and>
          (name |\<in>| IS_ConstLocals full' \<longleftrightarrow> name |\<in>| IS_ConstLocals full)"
      using ng ne ne' consts'[OF ne] by (simp add: locals' refs')
  next
    show "ghost_locals_separate env' emb full'"
    proof (rule ghost_locals_separateI)
      fix name a
      assume g: "tyenv_var_ghost env' name"
        and l: "fmlookup (IS_Locals full') name = Some a"
      show "a < length (IS_Store full') \<and> a \<notin> set emb"
      proof (cases "name = varName")
        case True
        with l show ?thesis by (simp add: locals')
      next
        case False
        then have ne': "varName \<noteq> name" by blast
        from g others[OF False] have g0: "tyenv_var_ghost env name" by simp
        from l ne' have l0: "fmlookup (IS_Locals full) name = Some a"
          by (simp add: locals')
        from ghost_locals_separateD(1)[OF gh g0 l0] show ?thesis by (simp add: store')
      qed
    next
      fix name a p
      assume g: "tyenv_var_ghost env' name"
        and r: "fmlookup (IS_Refs full') name = Some (a, p)"
      show "a < length (IS_Store full') \<and> a \<notin> set emb"
      proof (cases "name = varName")
        case True
        with r have "a = addr" by (simp add: refs')
        with addr_lt addr_notin show ?thesis by (simp add: store')
      next
        case False
        then have ne': "varName \<noteq> name" by blast
        from g others[OF False] have g0: "tyenv_var_ghost env name" by simp
        from r ne' have r0: "fmlookup (IS_Refs full) name = Some (a, p)"
          by (simp add: refs')
        from ghost_locals_separateD(2)[OF gh g0 r0] show ?thesis by (simp add: store')
      qed
    qed
  qed
qed

(* A step that keeps the frame and the length of the store, and leaves the
   cells in the embedding as they were. *)
lemma state_erased_store_step:
  assumes rel: "state_erased env emb full erased"
    and st: "static_parts_eq full full'"
    and world: "IS_World full' = IS_World full"
    and len: "length (IS_Store full') = length (IS_Store full)"
    and locals': "IS_Locals full' = IS_Locals full"
    and refs': "IS_Refs full' = IS_Refs full"
    and consts': "IS_ConstLocals full' = IS_ConstLocals full"
    and cells: "\<And>a. a \<in> set emb \<Longrightarrow> IS_Store full' ! a = IS_Store full ! a"
  shows "state_erased env emb full' erased"
proof (rule state_erased_stepI[OF rel refl st world])
  show "length (IS_Store full) \<le> length (IS_Store full')" using len by simp
next
  fix a assume "a \<in> set emb"
  then show "IS_Store full' ! a = IS_Store full ! a" by (rule cells)
next
  fix name assume ng: "\<not> tyenv_var_ghost env name"
  show "\<not> tyenv_var_ghost env name \<and>
        fmlookup (IS_Locals full') name = fmlookup (IS_Locals full) name \<and>
        fmlookup (IS_Refs full') name = fmlookup (IS_Refs full) name \<and>
        (name |\<in>| IS_ConstLocals full' \<longleftrightarrow> name |\<in>| IS_ConstLocals full)"
    using ng by (simp add: locals' refs' consts')
next
  from rel have gh: "ghost_locals_separate env emb full" by (simp add: state_erased_def)
  have "ghost_locals_separate env emb full' = ghost_locals_separate env emb full"
    by (rule ghost_locals_separate_cong_state[OF locals' refs' len])
  then show "ghost_locals_separate env emb full'" using gh by (rule iffD2)
qed

(* Writing to one cell outside the embedding. *)
lemma state_erased_ghost_write:
  assumes rel: "state_erased env emb full erased"
    and st: "static_parts_eq full full'"
    and world: "IS_World full' = IS_World full"
    and store': "IS_Store full' = (IS_Store full)[addr := v]"
    and locals': "IS_Locals full' = IS_Locals full"
    and refs': "IS_Refs full' = IS_Refs full"
    and consts': "IS_ConstLocals full' = IS_ConstLocals full"
    and notin: "addr \<notin> set emb"
  shows "state_erased env emb full' erased"
proof (rule state_erased_store_step[OF rel st world _ locals' refs' consts'])
  show "length (IS_Store full') = length (IS_Store full)" by (simp add: store')
next
  fix a assume "a \<in> set emb"
  with notin have "addr \<noteq> a" by auto
  then show "IS_Store full' ! a = IS_Store full ! a" by (simp add: store')
qed

(* Leaving a scope. Given the relation for the state at the start of the scope
   and for the state at its end (in whatever environment the body ended in),
   the state after restore_scope is related as the starting state was: it has
   the starting state's frame, and the body's store cut back to the starting
   length. *)
lemma state_erased_restore_scope:
  assumes rel: "state_erased env emb full erased"
    and inner: "state_erased env1 emb full1 erased"
    and fns: "TE_Functions env1 = TE_Functions env"
    and len: "length (IS_Store full) \<le> length (IS_Store full1)"
  shows "state_erased env emb (restore_scope full full1) erased"
proof -
  let ?rs = "restore_scope full full1"
  from rel have heap: "heap_erased env emb full erased"
    and ty: "IS_TyArgs erased = IS_TyArgs full"
    and loc: "locals_erased env emb full erased"
    and gh: "ghost_locals_separate env emb full"
    by (simp_all add: state_erased_def)
  from inner have heap1: "heap_erased env1 emb full1 erased"
    by (simp add: state_erased_def)
  from heap have se: "store_erased emb full erased" by (simp add: heap_erased_def)
  from heap1 have se1: "store_erased emb full1 erased" by (simp add: heap_erased_def)
  have len_rs: "length (IS_Store ?rs) = length (IS_Store full)"
    using len by (simp add: min_absorb2)

  have se_rs: "store_erased emb ?rs erased"
    unfolding store_erased_def
  proof (intro conjI allI impI)
    show "length emb = length (IS_Store erased)" by (rule store_erasedD(1)[OF se])
    show "distinct emb" by (rule store_erasedD(2)[OF se])
  next
    fix i assume i_lt: "i < length emb"
    note b = store_erasedD(3)[OF se i_lt]
    note b1 = store_erasedD(3)[OF se1 i_lt]
    note v1 = store_erasedD(4)[OF se1 i_lt]
    show "emb ! i < length (IS_Store ?rs)" using b b1 by simp
    show "IS_Store erased ! i = IS_Store ?rs ! (emb ! i)" using b v1 by simp
  qed

  have heap_rs: "heap_erased env emb ?rs erased"
    unfolding heap_erased_def
  proof (intro conjI)
    show "IS_Globals erased = IS_Globals ?rs" using heap1 by (simp add: heap_erased_def)
    show "IS_DefaultCtors erased = IS_DefaultCtors ?rs"
      using heap1 by (simp add: heap_erased_def)
    show "IS_World erased = IS_World ?rs" using heap1 by (simp add: heap_erased_def)
    show "funs_erased env ?rs erased"
    proof -
      have "funs_erased env ?rs erased = funs_erased env1 full1 erased"
        by (rule funs_erased_cong) (simp_all add: fns)
      moreover from heap1 have "funs_erased env1 full1 erased"
        by (simp add: heap_erased_def)
      ultimately show ?thesis by (rule iffD2)
    qed
    show "store_erased emb ?rs erased" by (rule se_rs)
  qed

  have ty_rs: "IS_TyArgs erased = IS_TyArgs ?rs" using ty by simp

  have loc_rs: "locals_erased env emb ?rs erased"
  proof -
    have "locals_erased env emb ?rs erased = locals_erased env emb full erased"
      by (rule locals_erased_cong_state) simp_all
    then show ?thesis using loc by (rule iffD2)
  qed

  have gh_rs: "ghost_locals_separate env emb ?rs"
  proof -
    have "ghost_locals_separate env emb ?rs = ghost_locals_separate env emb full"
      by (rule ghost_locals_separate_cong_state[OF _ _ len_rs]) simp_all
    then show ?thesis using gh by (rule iffD2)
  qed

  show ?thesis
    unfolding state_erased_def by (intro conjI heap_rs ty_rs loc_rs gh_rs)
qed


(* ========================================================================== *)
(* Swap and calls *)
(* ========================================================================== *)

(* perform_swap changes only the store, keeps its length, and writes only to
   the two addresses given. *)
lemma perform_swap_effect:
  assumes "perform_swap state (addr1, path1) (addr2, path2) = Inr state'"
  shows "IS_Locals state' = IS_Locals state"
    and "IS_Refs state' = IS_Refs state"
    and "IS_ConstLocals state' = IS_ConstLocals state"
    and "IS_World state' = IS_World state"
    and "length (IS_Store state') = length (IS_Store state)"
    and "\<And>a. addr1 \<noteq> a \<Longrightarrow> addr2 \<noteq> a \<Longrightarrow> IS_Store state' ! a = IS_Store state ! a"
proof -
  from assms[symmetric] obtain new_val1 new_val2 where
    store': "IS_Store state' = (IS_Store state)[addr1 := new_val1, addr2 := new_val2]" and
    locals': "IS_Locals state' = IS_Locals state" and
    refs': "IS_Refs state' = IS_Refs state" and
    consts': "IS_ConstLocals state' = IS_ConstLocals state" and
    world': "IS_World state' = IS_World state"
    by (auto simp: Let_def split: sum.splits)
  show "IS_Locals state' = IS_Locals state" by (rule locals')
  show "IS_Refs state' = IS_Refs state" by (rule refs')
  show "IS_ConstLocals state' = IS_ConstLocals state" by (rule consts')
  show "IS_World state' = IS_World state" by (rule world')
  show "length (IS_Store state') = length (IS_Store state)" using store' by simp
  show "\<And>a. addr1 \<noteq> a \<Longrightarrow> addr2 \<noteq> a \<Longrightarrow> IS_Store state' ! a = IS_Store state ! a"
    using store' by simp
qed

(* A call made by ghost code. By the frame lemma it changes only the cells of
   the base variables of its Ref arguments, and those variables are ghost
   (the call is typed in Ghost mode, so each Ref argument is a ghost lvalue).

   The call leaves the world unchanged, because ghost code can only call a
   pure function. *)
lemma ghost_call_invisible:
  assumes rel: "state_erased env emb full erased"
    and agree: "fun_var_ref_agree (TE_Functions env) (IS_Functions full)"
    and pure: "funs_respect_purity (TE_Functions env) (IS_Functions full)"
    and callT: "core_impure_call_type env Ghost fnName argTys argTms = Some retTy"
    and call: "interp_function_call d fuel full fnName argTys argTms = Inr (newState, retVal)"
  shows "state_erased env emb newState erased"
proof -
  note cf = interp_function_call_frame[OF call]
  have st: "static_parts_eq full newState"
    by (rule interp_function_call_static[OF call])
  \<comment> \<open>Ghost code calls no impure function, and a call of a pure function
      keeps the world. \<close>
  from pure_context_callee_pure[OF callT disjI1[OF refl]] obtain pinfo where
    pinfo: "fmlookup (TE_Functions env) fnName = Some pinfo" and
    np: "\<not> FI_Impure pinfo"
    by blast
  have world: "IS_World newState = IS_World full"
    by (rule pure_function_call_keeps_world[OF pure pinfo np call])
  from rel have gh: "ghost_locals_separate env emb full" by (simp add: state_erased_def)
  from rel have se: "store_erased emb full erased"
    by (simp add: state_erased_def heap_erased_def)
  from core_impure_call_type_fn_facts[OF callT] obtain info where
    info: "fmlookup (TE_Functions env) fnName = Some info" and
    refs: "\<forall>i < length argTms.
             fst (snd (FI_TmArgs info ! i)) = Ref
               \<longrightarrow> is_writable_lvalue env (argTms ! i)
                   \<and> ghost_lvalue_ok env Ghost (argTms ! i)"
    by blast
  show ?thesis
  proof (rule state_erased_store_step[OF rel st world cf(5) cf(1) cf(2) cf(3)])
    fix a assume a_in: "a \<in> set emb"
    have a_lt: "a < length (IS_Store full)" by (rule store_erased_emb_bound[OF se a_in])
    have notin: "a \<notin> call_ref_addrs full fnName argTms"
    proof
      assume "a \<in> call_ref_addrs full fnName argTms"
      then obtain f i name where
        f: "fmlookup (IS_Functions full) fnName = Some f" and
        i1: "i < length argTms" and
        i2: "i < length (IF_Args f)" and
        is_ref: "fst (snd (IF_Args f ! i)) = Ref" and
        base: "lvalue_base_name (argTms ! i) = Some name" and
        va: "var_addr full name = Some a"
        unfolding call_ref_addrs_def by blast
      have r: "fst (snd (FI_TmArgs info ! i)) = Ref"
        by (rule fun_var_ref_agree_Ref[OF agree info f i2 is_ref])
      from refs i1 r have "ghost_lvalue_ok env Ghost (argTms ! i)" by blast
      with base have g: "tyenv_var_ghost env name"
        by (simp add: ghost_lvalue_ok_def)
      from ghost_var_addr_separate(2)[OF gh g va] a_in show False by simp
    qed
    show "IS_Store newState ! a = IS_Store full ! a" by (rule cf(6)[OF a_lt notin])
  qed
qed


(* ========================================================================== *)
(* The main lemma *)
(* ========================================================================== *)

fun is_continue :: "'w ExecResult \<Rightarrow> bool" where
  "is_continue (Continue _) = True"
| "is_continue (Return _ _) = False"

lemma ghost_resultI:
  assumes "res = Continue full'" and "state_erased env' emb full' erased"
  shows "is_continue res \<and> state_erased env' emb (result_state res) erased"
  using assms by simp

(* Leaving the scope of a While body, a Match arm or a Block. The state at the
   end of the body is related in the environment that the body ended in; the
   state after leaving the scope is related in the starting one. *)
lemma ghost_scope_exit:
  assumes rel: "state_erased env emb full erased"
    and bodyT: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) g body
                  = Some bodyEnv"
    and body: "interp_statement_list d fuel full body = Inr (Continue state1)"
    and rel1: "state_erased bodyEnv emb state1 erased"
  shows "state_erased env emb (restore_scope full state1) erased"
proof -
  have "tyenv_fixed_eq (env \<lparr> TE_ProofTopLevel := False \<rparr>) bodyEnv"
    by (rule core_statement_list_type_fixed_eq[OF bodyT])
  then have fnsB: "TE_Functions bodyEnv = TE_Functions env"
    by (simp add: tyenv_fixed_eq_def)
  have len1: "length (IS_Store full) \<le> length (IS_Store state1)"
    using frame_stepD(1)[OF interp_statement_list_frame[OF body]] by simp
  show ?thesis by (rule state_erased_restore_scope[OF rel rel1 fnsB len1])
qed

(* Both statements are proved together by induction on the fuel, at a fixed
   depth. Function calls need no induction of their own: ghost_call_invisible
   says all that is needed about them.

   The function signatures and the function table are fixed outside the
   induction (neither changes as statements run), so that the hypothesis
   about them need not be carried along. *)
lemma ghost_invisible_aux:
  fixes funInfos :: "(string, FunInfo) fmap"
    and funs :: "(string, 'w InterpFun) fmap"
  assumes agree: "fun_var_ref_agree funInfos funs"
    and pure: "funs_respect_purity funInfos funs"
  shows "\<forall>env env' emb (full :: 'w InterpState) (erased :: 'w InterpState) res.
           TE_Functions env = funInfos \<longrightarrow>
           IS_Functions full = funs \<longrightarrow>
           TE_FunctionGhost env = NotGhost \<longrightarrow>
           state_erased env emb full erased \<longrightarrow>
           core_statement_type env Ghost stmt = Some env' \<longrightarrow>
           interp_statement d fuel full stmt = Inr res \<longrightarrow>
             is_continue res
             \<and> state_erased env' emb (result_state res) erased"
    and "\<forall>env env' emb (full :: 'w InterpState) (erased :: 'w InterpState) res.
           TE_Functions env = funInfos \<longrightarrow>
           IS_Functions full = funs \<longrightarrow>
           TE_FunctionGhost env = NotGhost \<longrightarrow>
           state_erased env emb full erased \<longrightarrow>
           core_statement_list_type env Ghost stmts = Some env' \<longrightarrow>
           interp_statement_list d fuel full stmts = Inr res \<longrightarrow>
             is_continue res
             \<and> state_erased env' emb (result_state res) erased"
proof (induction fuel arbitrary: stmt stmts rule: nat.induct)
  case zero
  {
    case 1 show ?case by simp
  next
    case 2 show ?case by simp
  }
next
  case (Suc fuel)
  note IH_stmt = Suc.IH(1)[rule_format]
  note IH_list = Suc.IH(2)[rule_format]
  {
    case (1 stmt) show ?case
    proof (intro allI impI)
      fix env env' :: CoreTyEnv and emb :: "nat list"
        and full erased :: "'w InterpState" and res :: "'w ExecResult"
      assume fn_eq: "TE_Functions env = funInfos"
        and funs_eq: "IS_Functions full = funs"
        and fg: "TE_FunctionGhost env = NotGhost"
        and rel: "state_erased env emb full erased"
        and T: "core_statement_type env Ghost stmt = Some env'"
        and H: "interp_statement d (Suc fuel) full stmt = Inr res"

      have fx: "tyenv_fixed_eq env env'" by (rule core_statement_type_fixed_eq[OF T])
      have fns: "TE_Functions env' = TE_Functions env"
        using fx by (simp add: tyenv_fixed_eq_def)
      have st: "static_parts_eq full (result_state res)"
        by (rule interp_statement_static[OF H])
      have gh: "ghost_locals_separate env emb full"
        using rel by (simp add: state_erased_def)
      have agree': "fun_var_ref_agree (TE_Functions env) (IS_Functions full)"
        using agree by (simp add: fn_eq funs_eq)
      have pure': "funs_respect_purity (TE_Functions env) (IS_Functions full)"
        using pure by (simp add: fn_eq funs_eq)

      \<comment> \<open>The environment in which the body of a While, Match or Block is typed. \<close>
      have fnB: "TE_Functions (env \<lparr> TE_ProofTopLevel := False \<rparr>) = funInfos"
        using fn_eq by simp
      have fgB: "TE_FunctionGhost (env \<lparr> TE_ProofTopLevel := False \<rparr>) = NotGhost"
        using fg by simp
      have relB: "state_erased (env \<lparr> TE_ProofTopLevel := False \<rparr>) emb full erased"
        using rel by simp

      show "is_continue res \<and> state_erased env' emb (result_state res) erased"
      proof (cases stmt)
        case (CoreStmt_VarDecl g varName vr ty initTm)
        show ?thesis
        proof (cases vr)
          case Var
          from T CoreStmt_VarDecl Var have g_eq: "g = Ghost" by (auto split: if_splits)
          from T CoreStmt_VarDecl Var g_eq
          have tlv: "TE_LocalVars env' = fmupd varName ty (TE_LocalVars env)"
            and tgl: "TE_GhostLocals env' = finsert varName (TE_GhostLocals env)"
            by (auto split: if_splits)
          note decl = ghost_decl_var_ghost[OF tlv tgl]
          from Var H CoreStmt_VarDecl obtain initVal where
            iv: "interp_term d fuel full initTm = Inr initVal"
            by (auto split: sum.splits)
          from Var H[symmetric] CoreStmt_VarDecl iv have
            c: "is_continue res" and
            world: "IS_World (result_state res) = IS_World full" and
            store': "IS_Store (result_state res) = IS_Store full @ [initVal]" and
            locals': "IS_Locals (result_state res)
                        = fmupd varName (length (IS_Store full)) (IS_Locals full)" and
            refs': "IS_Refs (result_state res) = fmdrop varName (IS_Refs full)" and
            consts': "IS_ConstLocals (result_state res)
                        = fminus (IS_ConstLocals full) {|varName|}"
            by (simp_all add: Let_def)
          have rel': "state_erased env' emb (result_state res) erased"
            by (rule state_erased_bind_ghost_fresh
                       [OF rel decl(1) decl(2) fns st world store' locals' refs'])
               (simp_all add: consts')
          show ?thesis by (rule conjI[OF c rel'])
        next
          case Ref
          from T CoreStmt_VarDecl Ref have g_eq: "g = Ghost" by (auto split: if_splits)
          from T CoreStmt_VarDecl Ref g_eq
          have glv: "ghost_lvalue_ok env Ghost initTm" by (auto split: if_splits)
          from T CoreStmt_VarDecl Ref g_eq
          have tlv: "TE_LocalVars env' = fmupd varName ty (TE_LocalVars env)"
            and tgl: "TE_GhostLocals env' = finsert varName (TE_GhostLocals env)"
            by (auto split: if_splits)
          note decl = ghost_decl_var_ghost[OF tlv tgl]
          \<comment> \<open>Two branches: const-base (copy) or writable-base (alias). \<close>
          from Ref H CoreStmt_VarDecl obtain baseName where
            base: "lvalue_base_name initTm = Some baseName"
            by (cases "lvalue_base_name initTm") simp_all
          show ?thesis
          proof (cases "baseName |\<in>| IS_ConstLocals full
                        \<or> (fmlookup (IS_Locals full) baseName = None
                           \<and> fmlookup (IS_Refs full) baseName = None)")
            case True
            with Ref H CoreStmt_VarDecl base obtain val where
              iv: "interp_term d fuel full initTm = Inr val"
              by (auto split: sum.splits)
            from Ref H[symmetric] CoreStmt_VarDecl base True iv have
              c: "is_continue res" and
              world: "IS_World (result_state res) = IS_World full" and
              store': "IS_Store (result_state res) = IS_Store full @ [val]" and
              locals': "IS_Locals (result_state res)
                          = fmupd varName (length (IS_Store full)) (IS_Locals full)" and
              refs': "IS_Refs (result_state res) = fmdrop varName (IS_Refs full)" and
              consts': "IS_ConstLocals (result_state res)
                          = finsert varName (IS_ConstLocals full)"
              by (simp_all add: Let_def)
            have rel': "state_erased env' emb (result_state res) erased"
              by (rule state_erased_bind_ghost_fresh
                         [OF rel decl(1) decl(2) fns st world store' locals' refs'])
                 (simp_all add: consts')
            show ?thesis by (rule conjI[OF c rel'])
          next
            case False
            with Ref H CoreStmt_VarDecl base obtain addrPath where
              lv: "interp_writable_lvalue d fuel full initTm = Inr addrPath"
              by (auto split: sum.splits)
            obtain addr path where ap: "addrPath = (addr, path)" by (cases addrPath)
            from lv ap have wl: "interp_writable_lvalue d fuel full initTm = Inr (addr, path)"
              by simp
            \<comment> \<open>The new ref points into the cell of a ghost variable. \<close>
            note sep = ghost_lvalue_addr_separate[OF gh glv wl]
            from Ref H[symmetric] CoreStmt_VarDecl base False wl have
              c: "is_continue res" and
              world: "IS_World (result_state res) = IS_World full" and
              store': "IS_Store (result_state res) = IS_Store full" and
              locals': "IS_Locals (result_state res) = fmdrop varName (IS_Locals full)" and
              refs': "IS_Refs (result_state res) = fmupd varName (addr, path) (IS_Refs full)" and
              consts': "IS_ConstLocals (result_state res)
                          = fminus (IS_ConstLocals full) {|varName|}"
              by simp_all
            have rel': "state_erased env' emb (result_state res) erased"
              by (rule state_erased_bind_ghost_ref
                         [OF rel decl(1) decl(2) fns st world store' locals' refs' sep(1) sep(2)])
                 (simp_all add: consts')
            show ?thesis by (rule conjI[OF c rel'])
          qed
        qed
      next
        case (CoreStmt_VarDeclCall g varName varTy castOpt fnName argTys argTms)
        from T CoreStmt_VarDeclCall have g_eq: "g = Ghost" by (auto split: if_splits)
        from T CoreStmt_VarDeclCall g_eq obtain retTy where
          callT: "core_impure_call_type env Ghost fnName argTys argTms = Some retTy"
          by (auto split: if_splits option.splits)
        from T CoreStmt_VarDeclCall g_eq
        have tlv: "TE_LocalVars env' = fmupd varName varTy (TE_LocalVars env)"
          and tgl: "TE_GhostLocals env' = finsert varName (TE_GhostLocals env)"
          by (auto split: if_splits option.splits)
        note decl = ghost_decl_var_ghost[OF tlv tgl]
        \<comment> \<open>Run the call (giving newState), apply the cast, then alloc and bind. \<close>
        from H CoreStmt_VarDeclCall obtain newState retVal where
          call: "interp_function_call d fuel full fnName argTys argTms = Inr (newState, retVal)"
          by (auto split: sum.splits prod.splits)
        have rel1: "state_erased env emb newState erased"
          by (rule ghost_call_invisible[OF rel agree' pure' callT call])
        from H CoreStmt_VarDeclCall call obtain initVal where
          cast: "apply_cast_opt castOpt retVal = Inr initVal"
          by (auto split: sum.splits)
        from H[symmetric] CoreStmt_VarDeclCall call cast have
          c: "is_continue res" and
          st2: "static_parts_eq newState (result_state res)" and
          world: "IS_World (result_state res) = IS_World newState" and
          store': "IS_Store (result_state res) = IS_Store newState @ [initVal]" and
          locals': "IS_Locals (result_state res)
                      = fmupd varName (length (IS_Store newState)) (IS_Locals newState)" and
          refs': "IS_Refs (result_state res) = fmdrop varName (IS_Refs newState)" and
          consts': "IS_ConstLocals (result_state res)
                      = fminus (IS_ConstLocals newState) {|varName|}"
          by (simp_all add: Let_def static_parts_eq_def)
        have rel': "state_erased env' emb (result_state res) erased"
          by (rule state_erased_bind_ghost_fresh
                     [OF rel1 decl(1) decl(2) fns st2 world store' locals' refs'])
             (simp_all add: consts')
        show ?thesis by (rule conjI[OF c rel'])
      next
        case (CoreStmt_Fix _ _) with H show ?thesis by simp
      next
        case (CoreStmt_Obtain varName varTy condTm)
        from T CoreStmt_Obtain
        have tlv: "TE_LocalVars env' = fmupd varName varTy (TE_LocalVars env)"
          and tgl: "TE_GhostLocals env' = finsert varName (TE_GhostLocals env)"
          by (auto simp: Let_def split: if_splits)
        note decl = ghost_decl_var_ghost[OF tlv tgl]
        show ?thesis
        proof (cases d)
          case d_zero: 0
          with H CoreStmt_Obtain show ?thesis by simp
        next
          case d_Suc: (Suc d')
          from H[symmetric] CoreStmt_Obtain d_Suc obtain witness where
            res_eq: "res = Continue (bind_mutable_local varName witness full)"
            by (auto simp del: bind_mutable_local.simps split: sum.splits)
          have c: "is_continue res" by (simp add: res_eq)
          have world: "IS_World (result_state res) = IS_World full"
            and store': "IS_Store (result_state res) = IS_Store full @ [witness]"
            and locals': "IS_Locals (result_state res)
                            = fmupd varName (length (IS_Store full)) (IS_Locals full)"
            and refs': "IS_Refs (result_state res) = fmdrop varName (IS_Refs full)"
            and consts': "IS_ConstLocals (result_state res)
                            = fminus (IS_ConstLocals full) {|varName|}"
            by (simp_all add: res_eq Let_def)
          have rel': "state_erased env' emb (result_state res) erased"
            by (rule state_erased_bind_ghost_fresh
                       [OF rel decl(1) decl(2) fns st world store' locals' refs'])
               (simp_all add: consts')
          show ?thesis by (rule conjI[OF c rel'])
        qed
      next
        case (CoreStmt_Use _) with H show ?thesis by simp
      next
        case (CoreStmt_Assign g lhsLv rhsTm)
        from T CoreStmt_Assign have g_eq: "g = Ghost" by (auto split: if_splits)
        from T CoreStmt_Assign g_eq
        have glv: "ghost_lvalue_ok env Ghost lhsLv" by (auto split: if_splits)
        from T CoreStmt_Assign have env'_eq: "env' = env"
          by (auto split: if_splits option.splits)
        from H CoreStmt_Assign obtain addr path where
          wl: "interp_writable_lvalue d fuel full lhsLv = Inr (addr, path)"
          by (auto split: sum.splits)
        from H CoreStmt_Assign wl obtain rhsVal where
          rv: "interp_term d fuel full rhsTm = Inr rhsVal"
          by (auto split: sum.splits)
        from H CoreStmt_Assign wl rv obtain newVal where
          upd: "update_value_at_path (IS_Store full ! addr) path rhsVal = Inr newVal"
          by (auto simp: Let_def split: sum.splits)
        from H[symmetric] CoreStmt_Assign wl rv upd have
          c: "is_continue res" and
          world: "IS_World (result_state res) = IS_World full" and
          store': "IS_Store (result_state res) = (IS_Store full)[addr := newVal]" and
          locals': "IS_Locals (result_state res) = IS_Locals full" and
          refs': "IS_Refs (result_state res) = IS_Refs full" and
          consts': "IS_ConstLocals (result_state res) = IS_ConstLocals full"
          by (simp_all add: Let_def)
        \<comment> \<open>The cell written is the cell of a ghost variable. \<close>
        have rel': "state_erased env emb (result_state res) erased"
          by (rule state_erased_ghost_write
                     [OF rel st world store' locals' refs' consts'
                         ghost_lvalue_addr_separate(2)[OF gh glv wl]])
        show ?thesis unfolding env'_eq by (rule conjI[OF c rel'])
      next
        case (CoreStmt_AssignCall g lhsLv castOpt fnName argTys argTms)
        from T CoreStmt_AssignCall have g_eq: "g = Ghost" by (auto split: if_splits)
        from T CoreStmt_AssignCall g_eq
        have glv: "ghost_lvalue_ok env Ghost lhsLv" by (auto split: if_splits)
        from T CoreStmt_AssignCall g_eq obtain retTy where
          callT: "core_impure_call_type env Ghost fnName argTys argTms = Some retTy"
          by (auto split: if_splits option.splits)
        from T CoreStmt_AssignCall have env'_eq: "env' = env"
          by (auto split: if_splits option.splits)
        \<comment> \<open>Resolve lhs, run the call (newState), apply cast, store. \<close>
        from H CoreStmt_AssignCall obtain addr path where
          wl: "interp_writable_lvalue d fuel full lhsLv = Inr (addr, path)"
          by (auto split: sum.splits)
        from H CoreStmt_AssignCall wl obtain newState retVal where
          call: "interp_function_call d fuel full fnName argTys argTms = Inr (newState, retVal)"
          by (auto split: sum.splits prod.splits)
        have rel1: "state_erased env emb newState erased"
          by (rule ghost_call_invisible[OF rel agree' pure' callT call])
        from H CoreStmt_AssignCall wl call obtain rhsVal where
          cast: "apply_cast_opt castOpt retVal = Inr rhsVal"
          by (auto split: sum.splits)
        from H CoreStmt_AssignCall wl call cast obtain newVal where
          upd: "update_value_at_path (IS_Store newState ! addr) path rhsVal = Inr newVal"
          by (auto simp: Let_def split: sum.splits)
        from H[symmetric] CoreStmt_AssignCall wl call cast upd have
          c: "is_continue res" and
          st2: "static_parts_eq newState (result_state res)" and
          world: "IS_World (result_state res) = IS_World newState" and
          store': "IS_Store (result_state res) = (IS_Store newState)[addr := newVal]" and
          locals': "IS_Locals (result_state res) = IS_Locals newState" and
          refs': "IS_Refs (result_state res) = IS_Refs newState" and
          consts': "IS_ConstLocals (result_state res) = IS_ConstLocals newState"
          by (simp_all add: Let_def static_parts_eq_def)
        have rel': "state_erased env emb (result_state res) erased"
          by (rule state_erased_ghost_write
                     [OF rel1 st2 world store' locals' refs' consts'
                         ghost_lvalue_addr_separate(2)[OF gh glv wl]])
        show ?thesis unfolding env'_eq by (rule conjI[OF c rel'])
      next
        case (CoreStmt_Swap g lhsTm rhsTm)
        from T CoreStmt_Swap have g_eq: "g = Ghost" by (auto split: if_splits)
        from T CoreStmt_Swap g_eq
        have glvL: "ghost_lvalue_ok env Ghost lhsTm"
          and glvR: "ghost_lvalue_ok env Ghost rhsTm"
          by (auto split: if_splits)
        from T CoreStmt_Swap have env'_eq: "env' = env"
          by (auto split: if_splits option.splits)
        from H CoreStmt_Swap obtain lhsLv where
          lhs: "interp_writable_lvalue d fuel full lhsTm = Inr lhsLv"
          by (auto split: sum.splits)
        with H CoreStmt_Swap obtain rhsLv where
          rhs: "interp_writable_lvalue d fuel full rhsTm = Inr rhsLv"
          by (auto split: sum.splits)
        with H CoreStmt_Swap lhs obtain newState where
          sw: "perform_swap full lhsLv rhsLv = Inr newState"
          and res_eq: "res = Continue newState"
          by (auto split: sum.splits)
        obtain addr1 path1 where l_eq: "lhsLv = (addr1, path1)" by (cases lhsLv)
        obtain addr2 path2 where r_eq: "rhsLv = (addr2, path2)" by (cases rhsLv)
        \<comment> \<open>Both cells are cells of ghost variables. \<close>
        note n1 = ghost_lvalue_addr_separate(2)[OF gh glvL lhs[unfolded l_eq]]
        note n2 = ghost_lvalue_addr_separate(2)[OF gh glvR rhs[unfolded r_eq]]
        note sw' = perform_swap_effect[OF sw[unfolded l_eq r_eq]]
        from st res_eq have st1: "static_parts_eq full newState" by simp
        have rel': "state_erased env emb newState erased"
        proof (rule state_erased_store_step[OF rel st1 sw'(4) sw'(5) sw'(1) sw'(2) sw'(3)])
          fix a assume a_in: "a \<in> set emb"
          from a_in n1 have "addr1 \<noteq> a" by auto
          moreover from a_in n2 have "addr2 \<noteq> a" by auto
          ultimately show "IS_Store newState ! a = IS_Store full ! a" by (rule sw'(6))
        qed
        show ?thesis unfolding env'_eq by (rule ghost_resultI[OF res_eq rel'])
      next
        \<comment> \<open>A Return in Ghost mode needs a ghost function. \<close>
        case (CoreStmt_Return tm)
        with T fg show ?thesis by (auto split: if_splits)
      next
        case (CoreStmt_Assert condOpt proofBody)
        from T CoreStmt_Assert have env'_eq: "env' = env"
          by (auto simp: Let_def split: if_splits option.splits)
        have res_eq: "res = Continue full"
        proof (cases condOpt)
          case None
          with H CoreStmt_Assert show ?thesis by simp
        next
          case (Some condTm)
          from H CoreStmt_Assert Some obtain condVal where
            cv: "interp_term d fuel full condTm = Inr condVal"
            by (auto split: sum.splits)
          show ?thesis
          proof (cases condVal)
            case (CV_Bool b)
            with H CoreStmt_Assert Some cv show ?thesis by (cases b) simp_all
          next
            case CV_FiniteInt with H CoreStmt_Assert Some cv show ?thesis by simp
          next
            case CV_Variant with H CoreStmt_Assert Some cv show ?thesis by simp
          next
            case CV_Record with H CoreStmt_Assert Some cv show ?thesis by simp
          next
            case CV_Array with H CoreStmt_Assert Some cv show ?thesis by simp
          next
            case CV_Int with H CoreStmt_Assert Some cv show ?thesis by simp
          next
            case CV_Real with H CoreStmt_Assert Some cv show ?thesis by simp
          qed
        qed
        show ?thesis unfolding env'_eq by (rule ghost_resultI[OF res_eq rel])
      next
        case (CoreStmt_Assume _)
        from T CoreStmt_Assume have env'_eq: "env' = env" by (auto split: if_splits)
        from H CoreStmt_Assume have res_eq: "res = Continue full" by simp
        show ?thesis unfolding env'_eq by (rule ghost_resultI[OF res_eq rel])
      next
        case (CoreStmt_While g condTm invars decr bodyStmts)
        from T CoreStmt_While have env'_eq: "env' = env"
          by (auto split: if_splits option.splits CoreType.splits)
        from T CoreStmt_While have g_eq: "g = Ghost" by (auto split: if_splits)
        from T CoreStmt_While g_eq obtain bodyEnv where
          bodyT: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) Ghost bodyStmts
                    = Some bodyEnv"
          by (auto split: if_splits option.splits CoreType.splits)
        \<comment> \<open>The run succeeded, so the invariants were evaluated and all held. \<close>
        from H CoreStmt_While obtain invarVals where
          iv: "interp_term_list d fuel full invars = Inr invarVals" and
          ie: "invariants_error invarVals = None"
          by (auto split: sum.splits option.splits)
        note [simp] = iv ie
        from H CoreStmt_While obtain condVal where
          cv: "interp_term d fuel full condTm = Inr condVal"
          by (auto split: sum.splits)
        show ?thesis
        proof (cases condVal)
          case (CV_Bool b)
          show ?thesis
          proof (cases b)
            case False
            with CoreStmt_While H cv CV_Bool
            have res_eq: "res = Continue full" by simp
            show ?thesis unfolding env'_eq by (rule ghost_resultI[OF res_eq rel])
          next
            case True
            with CoreStmt_While H cv CV_Bool
            obtain bodyRes where
              body: "interp_statement_list d fuel full bodyStmts = Inr bodyRes"
              by (auto split: sum.splits)
            note bodyIH = IH_list[OF fnB funs_eq fgB relB bodyT body]
            show ?thesis
            proof (cases bodyRes)
              case (Return state1 v)
              with bodyIH show ?thesis by simp
            next
              case (Continue state1)
              let ?rs = "restore_scope full state1"
              from bodyIH Continue
              have rel1: "state_erased bodyEnv emb state1 erased"
                by simp
              have rel_rs: "state_erased env emb ?rs erased"
                by (rule ghost_scope_exit[OF rel bodyT body[unfolded Continue] rel1])
              have funs_rs: "IS_Functions ?rs = funs"
                using static_parts_eqD(2)[OF interp_statement_list_static[OF body]]
                      Continue funs_eq
                by simp
              \<comment> \<open>The loop runs again from the restored state. \<close>
              from CoreStmt_While H cv CV_Bool True body Continue
              have rec_eq: "interp_statement d fuel ?rs
                               (CoreStmt_While g condTm invars decr bodyStmts) = Inr res"
                by simp
              note T' = T[unfolded CoreStmt_While]
              show ?thesis
                by (rule IH_stmt[OF fn_eq funs_rs fg rel_rs T' rec_eq])
            qed
          qed
        next
          \<comment> \<open>Non-bool cond value: TypeError, contradicts H. \<close>
          case CV_FiniteInt with CoreStmt_While H cv show ?thesis by simp
        next
          case CV_Variant with CoreStmt_While H cv show ?thesis by simp
        next
          case CV_Record with CoreStmt_While H cv show ?thesis by simp
        next
          case CV_Array with CoreStmt_While H cv show ?thesis by simp
        next
          case CV_Int with CoreStmt_While H cv show ?thesis by simp
        next
          case CV_Real with CoreStmt_While H cv show ?thesis by simp
        qed
      next
        case (CoreStmt_Match g scrutTm arms)
        from T CoreStmt_Match have env'_eq: "env' = env"
          by (auto split: if_splits option.splits)
        from T CoreStmt_Match have g_eq: "g = Ghost" by (auto split: if_splits)
        from H CoreStmt_Match obtain scrutVal where
          sv: "interp_term d fuel full scrutTm = Inr scrutVal"
          by (auto split: sum.splits)
        from H CoreStmt_Match sv obtain armStmts where
          arm: "find_matching_arm scrutVal arms = Inr armStmts"
          by (auto split: sum.splits)
        note mem = find_matching_arm_in_arms[OF arm]
        from match_arm_typed[OF T[unfolded CoreStmt_Match] mem] g_eq obtain armEnv where
          armT: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) Ghost armStmts
                   = Some armEnv"
          by auto
        from H CoreStmt_Match sv arm obtain bodyRes where
          body: "interp_statement_list d fuel full armStmts = Inr bodyRes"
          by (auto split: sum.splits)
        note bodyIH = IH_list[OF fnB funs_eq fgB relB armT body]
        show ?thesis
        proof (cases bodyRes)
          case (Return state1 v)
          with bodyIH show ?thesis by simp
        next
          case (Continue state1)
          from bodyIH Continue
          have rel1: "state_erased armEnv emb state1 erased"
            by simp
          have rel_rs: "state_erased env emb (restore_scope full state1) erased"
            by (rule ghost_scope_exit[OF rel armT body[unfolded Continue] rel1])
          from CoreStmt_Match H sv arm body Continue
          have res_eq: "res = Continue (restore_scope full state1)" by simp
          show ?thesis unfolding env'_eq by (rule ghost_resultI[OF res_eq rel_rs])
        qed
      next
        case (CoreStmt_ShowHide _ _)
        from T CoreStmt_ShowHide have env'_eq: "env' = env" by simp
        from H CoreStmt_ShowHide have res_eq: "res = Continue full" by simp
        show ?thesis unfolding env'_eq by (rule ghost_resultI[OF res_eq rel])
      next
        case (CoreStmt_Block blockBody)
        from T CoreStmt_Block obtain bodyEnv where
          bodyT: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) Ghost blockBody
                    = Some bodyEnv"
          and env'_eq: "env' = env"
          by (auto split: option.splits)
        from H CoreStmt_Block obtain bodyRes where
          body: "interp_statement_list d fuel full blockBody = Inr bodyRes"
          by (auto split: sum.splits)
        note bodyIH = IH_list[OF fnB funs_eq fgB relB bodyT body]
        show ?thesis
        proof (cases bodyRes)
          case (Return state1 v)
          with bodyIH show ?thesis by simp
        next
          case (Continue state1)
          from bodyIH Continue
          have rel1: "state_erased bodyEnv emb state1 erased"
            by simp
          have rel_rs: "state_erased env emb (restore_scope full state1) erased"
            by (rule ghost_scope_exit[OF rel bodyT body[unfolded Continue] rel1])
          from CoreStmt_Block H body Continue
          have res_eq: "res = Continue (restore_scope full state1)" by simp
          show ?thesis unfolding env'_eq by (rule ghost_resultI[OF res_eq rel_rs])
        qed
      qed
    qed
  next
    case (2 stmts) show ?case
    proof (intro allI impI)
      fix env env' :: CoreTyEnv and emb :: "nat list"
        and full erased :: "'w InterpState" and res :: "'w ExecResult"
      assume fn_eq: "TE_Functions env = funInfos"
        and funs_eq: "IS_Functions full = funs"
        and fg: "TE_FunctionGhost env = NotGhost"
        and rel: "state_erased env emb full erased"
        and T: "core_statement_list_type env Ghost stmts = Some env'"
        and H: "interp_statement_list d (Suc fuel) full stmts = Inr res"
      show "is_continue res \<and> state_erased env' emb (result_state res) erased"
      proof (cases stmts)
        case Nil
        with H have res_eq: "res = Continue full" by simp
        from T Nil have env'_eq: "env' = env" by simp
        show ?thesis unfolding env'_eq by (rule ghost_resultI[OF res_eq rel])
      next
        case (Cons stmt1 rest)
        from T Cons obtain envMid where
          T1: "core_statement_type env Ghost stmt1 = Some envMid" and
          T2: "core_statement_list_type envMid Ghost rest = Some env'"
          by (auto split: option.splits)
        from Cons H obtain res1 where
          r1: "interp_statement d fuel full stmt1 = Inr res1"
          by (auto split: sum.splits)
        note h1 = IH_stmt[OF fn_eq funs_eq fg rel T1 r1]
        show ?thesis
        proof (cases res1)
          case (Return state1 v)
          with h1 show ?thesis by simp
        next
          case (Continue state1)
          from h1 Continue
          have rel1: "state_erased envMid emb state1 erased"
            by simp
          \<comment> \<open>The first statement changes neither the function signatures, nor the
              ghost-ness of the enclosing function, nor the function table. \<close>
          have fx: "tyenv_fixed_eq env envMid" by (rule core_statement_type_fixed_eq[OF T1])
          have fn1: "TE_Functions envMid = funInfos"
            using fx fn_eq by (simp add: tyenv_fixed_eq_def)
          have fg1: "TE_FunctionGhost envMid = NotGhost"
            using fx fg by (simp add: tyenv_fixed_eq_def)
          have funs1: "IS_Functions state1 = funs"
            using static_parts_eqD(2)[OF interp_statement_static[OF r1]] Continue funs_eq
            by simp
          from Cons H r1 Continue
          have rec: "interp_statement_list d fuel state1 rest = Inr res" by simp
          show ?thesis by (rule IH_list[OF fn1 funs1 fg1 rel1 T2 rec])
        qed
      qed
    qed
  }
qed


(* ========================================================================== *)
(* The results, in the form that callers use *)
(* ========================================================================== *)

(* A statement that is well-typed in Ghost mode, in a function that is not
   ghost: if it runs to completion in the full state, it does not return, and
   the state it leaves is related to the same erased state, by the same
   embedding, in the environment after the statement. *)
theorem ghost_statement_invisible:
  assumes T: "core_statement_type env Ghost stmt = Some env'"
    and fg: "TE_FunctionGhost env = NotGhost"
    and rel: "state_erased env emb full erased"
    and agree: "fun_var_ref_agree (TE_Functions env) (IS_Functions full)"
    and pure: "funs_respect_purity (TE_Functions env) (IS_Functions full)"
    and H: "interp_statement d fuel full stmt = Inr res"
  shows "\<exists>full'. res = Continue full' \<and> state_erased env' emb full' erased"
proof -
  from ghost_invisible_aux(1)[OF agree pure, rule_format, OF refl refl fg rel T H]
  have "is_continue res \<and> state_erased env' emb (result_state res) erased" .
  then show ?thesis by (cases res) simp_all
qed

theorem ghost_statement_list_invisible:
  assumes T: "core_statement_list_type env Ghost stmts = Some env'"
    and fg: "TE_FunctionGhost env = NotGhost"
    and rel: "state_erased env emb full erased"
    and agree: "fun_var_ref_agree (TE_Functions env) (IS_Functions full)"
    and pure: "funs_respect_purity (TE_Functions env) (IS_Functions full)"
    and H: "interp_statement_list d fuel full stmts = Inr res"
  shows "\<exists>full'. res = Continue full' \<and> state_erased env' emb full' erased"
proof -
  from ghost_invisible_aux(2)[OF agree pure, rule_format, OF refl refl fg rel T H]
  have "is_continue res \<and> state_erased env' emb (result_state res) erased" .
  then show ?thesis by (cases res) simp_all
qed


(* ========================================================================== *)
(* Statements that erase_ghost_statement deletes *)
(* ========================================================================== *)

(* A statement of executable code that erases to nothing is well-typed in
   Ghost mode too, with the same resulting environment. Such a statement
   either carries the Ghost marker, in which case its parts are typed in Ghost
   mode whatever the surrounding mode is, or is one of the forms (Obtain,
   Assert, Assume, ShowHide) whose typing does not look at the surrounding
   mode. Fix and Use are not well-typed in NotGhost mode. *)
lemma erased_statement_ghost_mode:
  assumes er: "erase_ghost_statement stmt = []"
    and T: "core_statement_type env NotGhost stmt = Some env'"
  shows "core_statement_type env Ghost stmt = Some env'"
proof (cases stmt)
  case (CoreStmt_VarDecl g varName vr varTy initTm)
  with er have g_eq: "g = Ghost" by (cases g) simp_all
  from T show ?thesis unfolding CoreStmt_VarDecl g_eq by (cases vr) simp_all
next
  case (CoreStmt_VarDeclCall g varName varTy castOpt fnName tyArgs argTms)
  with er have g_eq: "g = Ghost" by (cases g) simp_all
  from T show ?thesis unfolding CoreStmt_VarDeclCall g_eq by simp
next
  case (CoreStmt_Fix varName varTy)
  with T show ?thesis
    by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
next
  case (CoreStmt_Obtain varName varTy condTm)
  with T show ?thesis by simp
next
  case (CoreStmt_Use witnessTm)
  with T show ?thesis
    by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
next
  case (CoreStmt_Assign g lhsTm rhsTm)
  with er have g_eq: "g = Ghost" by (cases g) simp_all
  from T show ?thesis unfolding CoreStmt_Assign g_eq by simp
next
  case (CoreStmt_AssignCall g lhsTm castOpt fnName tyArgs argTms)
  with er have g_eq: "g = Ghost" by (cases g) simp_all
  from T show ?thesis unfolding CoreStmt_AssignCall g_eq by simp
next
  case (CoreStmt_Swap g lhsTm rhsTm)
  with er have g_eq: "g = Ghost" by (cases g) simp_all
  from T show ?thesis unfolding CoreStmt_Swap g_eq by simp
next
  case (CoreStmt_Return tm)
  with er show ?thesis by simp
next
  case (CoreStmt_Assert condOpt proofBody)
  with T show ?thesis by simp
next
  case (CoreStmt_Assume tm)
  with T show ?thesis by simp
next
  case (CoreStmt_While g condTm invars decrTm body)
  with er have g_eq: "g = Ghost" by (cases g) simp_all
  from T show ?thesis unfolding CoreStmt_While g_eq by simp
next
  case (CoreStmt_Match g scrut arms)
  with er have g_eq: "g = Ghost" by (cases g) simp_all
  from T show ?thesis unfolding CoreStmt_Match g_eq by simp
next
  case (CoreStmt_ShowHide sh name)
  with T show ?thesis by simp
next
  case (CoreStmt_Block body)
  with er show ?thesis by simp
qed

(* The form used by the simulation proof: a statement of well-typed executable
   code that erases to nothing leaves the full state related to the same
   erased state. *)
theorem erased_statement_invisible:
  assumes er: "erase_ghost_statement stmt = []"
    and T: "core_statement_type env NotGhost stmt = Some env'"
    and fg: "TE_FunctionGhost env = NotGhost"
    and rel: "state_erased env emb full erased"
    and agree: "fun_var_ref_agree (TE_Functions env) (IS_Functions full)"
    and pure: "funs_respect_purity (TE_Functions env) (IS_Functions full)"
    and H: "interp_statement d fuel full stmt = Inr res"
  shows "\<exists>full'. res = Continue full' \<and> state_erased env' emb full' erased"
  by (rule ghost_statement_invisible
             [OF erased_statement_ghost_mode[OF er T] fg rel agree pure H])

end
