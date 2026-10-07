theory ErasedSteps
  imports GhostInvisible
begin

(* Steps that the full state and the erased state take together.

   GhostInvisible.thy is about the statements that erase_ghost_statement
   deletes: the full state moves, and the erased state stays where it is.
   This file is about the code that is kept, which runs in both states. For
   each kind of step (reading a variable, declaring a variable, writing to a
   cell, leaving a scope, binding the arguments of a call, and so on) it shows
   that, if the full state takes the step, the erased state can take the
   corresponding step, and the two states are still related afterwards.

   The simulation proof puts these lemmas together by induction. Nothing here
   needs an induction over the interpreter. *)


(* ========================================================================== *)
(* Assembling the state relation and taking it apart *)
(* ========================================================================== *)

lemma state_erasedI:
  assumes "IS_Globals erased = IS_Globals full"
    and "IS_DataCtorsByType erased = IS_DataCtorsByType full"
    and "IS_World erased = IS_World full"
    and "funs_erased env full erased"
    and "store_erased emb full erased"
    and "IS_TyArgs erased = IS_TyArgs full"
    and "locals_erased env emb full erased"
    and "ghost_locals_separate env emb full"
    and "IS_DataCtors erased = IS_DataCtors full"
  shows "state_erased env emb full erased"
  unfolding state_erased_def heap_erased_def by (intro conjI assms)

lemma state_erasedD:
  assumes "state_erased env emb full erased"
  shows "IS_Globals erased = IS_Globals full"
    and "IS_DataCtorsByType erased = IS_DataCtorsByType full"
    and "IS_World erased = IS_World full"
    and "funs_erased env full erased"
    and "store_erased emb full erased"
    and "IS_TyArgs erased = IS_TyArgs full"
    and "locals_erased env emb full erased"
    and "ghost_locals_separate env emb full"
    and "IS_DataCtors erased = IS_DataCtors full"
  using assms unfolding state_erased_def heap_erased_def by blast+

lemma state_erased_heap:
  assumes "state_erased env emb full erased"
  shows "heap_erased env emb full erased"
  using assms by (simp add: state_erased_def)

(* Corresponding cells hold the same value. *)
lemma erased_cell:
  assumes "state_erased env emb full erased"
    and "i < length emb"
    and "emb ! i = addr"
  shows "IS_Store erased ! i = IS_Store full ! addr"
  using store_erasedD(4)[OF state_erasedD(5)[OF assms(1)] assms(2)] assms(3) by simp

(* The parts of the relation depend on the two states only through some of
   their fields, and on the environment only through some of its fields. *)

lemma funs_erased_cong_all:
  assumes "TE_Functions env2 = TE_Functions env"
    and "IS_Functions full2 = IS_Functions full"
    and "IS_Functions erased2 = IS_Functions erased"
  shows "funs_erased env2 full2 erased2 = funs_erased env full erased"
  using assms by (simp add: funs_erased_def)

lemma heap_erased_cong_env:
  assumes "TE_Functions env2 = TE_Functions env"
  shows "heap_erased env2 emb full erased = heap_erased env emb full erased"
  using assms by (simp add: heap_erased_def funs_erased_def)

lemma store_erased_cong:
  assumes "IS_Store full2 = IS_Store full"
    and "IS_Store erased2 = IS_Store erased"
  shows "store_erased emb full2 erased2 = store_erased emb full erased"
  using assms by (simp add: store_erased_def)

lemma locals_erased_cong_states:
  assumes "IS_Locals full2 = IS_Locals full"
    and "IS_Refs full2 = IS_Refs full"
    and "IS_ConstLocals full2 = IS_ConstLocals full"
    and "IS_Locals erased2 = IS_Locals erased"
    and "IS_Refs erased2 = IS_Refs erased"
    and "IS_ConstLocals erased2 = IS_ConstLocals erased"
  shows "locals_erased env emb full2 erased2 = locals_erased env emb full erased"
  using assms by (simp add: locals_erased_def)

(* Bindings that correspond under an embedding still correspond when the
   embedding is extended at the end. *)

lemma local_rel_extend:
  assumes "rel_option (\<lambda>i addr. i < length emb \<and> addr = emb ! i) x y"
  shows "rel_option (\<lambda>i addr. i < length (emb @ extra) \<and> addr = (emb @ extra) ! i) x y"
  using assms by (cases x; cases y) (auto simp: nth_append)

lemma ref_rel_extend:
  assumes "rel_option (\<lambda>(i, path) (addr, path'). i < length emb \<and> addr = emb ! i \<and> path = path')
                      x y"
  shows "rel_option (\<lambda>(i, path) (addr, path').
                        i < length (emb @ extra) \<and> addr = (emb @ extra) ! i \<and> path = path')
                    x y"
  using assms by (cases x; cases y) (auto simp: nth_append)


(* ========================================================================== *)
(* Looking up a name that is not ghost *)
(* ========================================================================== *)

(* What the full state binds the name to determines what the erased state
   binds it to. *)
lemma locals_erased_lookup:
  assumes le: "locals_erased env emb full erased"
    and ng: "\<not> tyenv_var_ghost env name"
  shows "fmlookup (IS_Locals full) name = None \<Longrightarrow> fmlookup (IS_Locals erased) name = None"
    and "\<And>addr. fmlookup (IS_Locals full) name = Some addr
            \<Longrightarrow> \<exists>i. fmlookup (IS_Locals erased) name = Some i \<and> i < length emb \<and> emb ! i = addr"
    and "fmlookup (IS_Refs full) name = None \<Longrightarrow> fmlookup (IS_Refs erased) name = None"
    and "\<And>addr path. fmlookup (IS_Refs full) name = Some (addr, path)
            \<Longrightarrow> \<exists>i. fmlookup (IS_Refs erased) name = Some (i, path)
                     \<and> i < length emb \<and> emb ! i = addr"
proof -
  note l = locals_erasedD(1)[OF le ng]
  note r = locals_erasedD(2)[OF le ng]
  show "fmlookup (IS_Locals full) name = None \<Longrightarrow> fmlookup (IS_Locals erased) name = None"
    using l by (cases "fmlookup (IS_Locals erased) name") auto
  show "\<And>addr. fmlookup (IS_Locals full) name = Some addr
          \<Longrightarrow> \<exists>i. fmlookup (IS_Locals erased) name = Some i \<and> i < length emb \<and> emb ! i = addr"
    using l by (cases "fmlookup (IS_Locals erased) name") auto
  show "fmlookup (IS_Refs full) name = None \<Longrightarrow> fmlookup (IS_Refs erased) name = None"
    using r by (cases "fmlookup (IS_Refs erased) name") auto
  show "\<And>addr path. fmlookup (IS_Refs full) name = Some (addr, path)
          \<Longrightarrow> \<exists>i. fmlookup (IS_Refs erased) name = Some (i, path)
                   \<and> i < length emb \<and> emb ! i = addr"
    using r by (cases "fmlookup (IS_Refs erased) name") (auto split: prod.splits)
qed

(* The test that CoreStmt_VarDecl (Ref) makes on the base variable of its
   lvalue comes out the same in both states. *)
lemma erased_base_readonly_iff:
  assumes le: "locals_erased env emb full erased"
    and ng: "\<not> tyenv_var_ghost env name"
  shows "(name |\<in>| IS_ConstLocals erased
            \<or> (fmlookup (IS_Locals erased) name = None \<and> fmlookup (IS_Refs erased) name = None))
       \<longleftrightarrow> (name |\<in>| IS_ConstLocals full
            \<or> (fmlookup (IS_Locals full) name = None \<and> fmlookup (IS_Refs full) name = None))"
proof -
  have l: "(fmlookup (IS_Locals erased) name = None) = (fmlookup (IS_Locals full) name = None)"
    using locals_erasedD(1)[OF le ng]
    by (cases "fmlookup (IS_Locals erased) name"; cases "fmlookup (IS_Locals full) name")
       simp_all
  have r: "(fmlookup (IS_Refs erased) name = None) = (fmlookup (IS_Refs full) name = None)"
    using locals_erasedD(2)[OF le ng]
    by (cases "fmlookup (IS_Refs erased) name"; cases "fmlookup (IS_Refs full) name")
       simp_all
  have c: "(name |\<in>| IS_ConstLocals erased) = (name |\<in>| IS_ConstLocals full)"
    by (rule locals_erasedD(3)[OF le ng])
  show ?thesis unfolding l r c by (rule refl)
qed

(* Reading a variable gives the same result in both states. *)
lemma erased_read_var:
  assumes rel: "state_erased env emb full erased"
    and ng: "\<not> tyenv_var_ghost env name"
  shows "interp_term d (Suc fuel) erased (CoreTm_Var name)
           = interp_term d (Suc fuel) full (CoreTm_Var name)"
proof -
  note D = state_erasedD[OF rel]
  note L = locals_erased_lookup[OF D(7) ng]
  show ?thesis
  proof (cases "fmlookup (IS_Locals full) name")
    case (Some addr)
    from L(2)[OF Some] obtain i where
      li: "fmlookup (IS_Locals erased) name = Some i" and
      i_lt: "i < length emb" and ei: "emb ! i = addr"
      by blast
    have "IS_Store erased ! i = IS_Store full ! addr" by (rule erased_cell[OF rel i_lt ei])
    with Some li show ?thesis by simp
  next
    case None
    note le = L(1)[OF None]
    show ?thesis
    proof (cases "fmlookup (IS_Refs full) name")
      case (Some addrPath)
      obtain addr path where ap: "addrPath = (addr, path)" by (cases addrPath)
      from Some ap have rf: "fmlookup (IS_Refs full) name = Some (addr, path)" by simp
      from L(4)[OF rf] obtain i where
        ri: "fmlookup (IS_Refs erased) name = Some (i, path)" and
        i_lt: "i < length emb" and ei: "emb ! i = addr"
        by blast
      have "IS_Store erased ! i = IS_Store full ! addr" by (rule erased_cell[OF rel i_lt ei])
      with None le rf ri show ?thesis by simp
    next
      case refsNone: None
      note re = L(3)[OF refsNone]
      from None le refsNone re D(1) show ?thesis by simp
    qed
  qed
qed

(* A variable, as a writable lvalue, denotes corresponding addresses in the
   two states, with the same path. *)
lemma erased_lvalue_var:
  assumes rel: "state_erased env emb full erased"
    and ng: "\<not> tyenv_var_ghost env name"
    and H: "interp_writable_lvalue d (Suc fuel) full (CoreTm_Var name) = Inr (addr, path)"
  shows "\<exists>i. interp_writable_lvalue d (Suc fuel) erased (CoreTm_Var name) = Inr (i, path)
             \<and> i < length emb \<and> emb ! i = addr"
proof -
  note D = state_erasedD[OF rel]
  note L = locals_erased_lookup[OF D(7) ng]
  from H have ncF: "name |\<notin>| IS_ConstLocals full" by (auto split: if_splits)
  with locals_erasedD(3)[OF D(7) ng] have ncE: "name |\<notin>| IS_ConstLocals erased" by simp
  show ?thesis
  proof (cases "fmlookup (IS_Locals full) name")
    case (Some a)
    from H ncF Some have a_eq: "a = addr" and p_eq: "path = []" by simp_all
    from L(2)[OF Some] a_eq obtain i where
      li: "fmlookup (IS_Locals erased) name = Some i" and
      i_lt: "i < length emb" and ei: "emb ! i = addr"
      by auto
    from ncE li p_eq
    have "interp_writable_lvalue d (Suc fuel) erased (CoreTm_Var name) = Inr (i, path)"
      by simp
    with i_lt ei show ?thesis by blast
  next
    case None
    note le = L(1)[OF None]
    from H ncF None have rf: "fmlookup (IS_Refs full) name = Some (addr, path)"
      by (cases "fmlookup (IS_Refs full) name") (auto split: prod.splits)
    from L(4)[OF rf] obtain i where
      ri: "fmlookup (IS_Refs erased) name = Some (i, path)" and
      i_lt: "i < length emb" and ei: "emb ! i = addr"
      by blast
    from ncE le ri
    have "interp_writable_lvalue d (Suc fuel) erased (CoreTm_Var name) = Inr (i, path)"
      by simp
    with i_lt ei show ?thesis by blast
  qed
qed


(* ========================================================================== *)
(* Three kinds of step that a single state can take *)
(* ========================================================================== *)

(* state' is state with a new cell holding val, and varName bound to it as a
   local. (The const-ness of varName itself is left open: some declarations
   make the new variable const, others do not.) *)
definition fresh_binding_step ::
    "string \<Rightarrow> CoreValue \<Rightarrow> 'w InterpState \<Rightarrow> 'w InterpState \<Rightarrow> bool" where
  "fresh_binding_step varName val state state' \<equiv>
    static_parts_eq state state' \<and>
    IS_World state' = IS_World state \<and>
    IS_Store state' = IS_Store state @ [val] \<and>
    IS_Locals state' = fmupd varName (length (IS_Store state)) (IS_Locals state) \<and>
    IS_Refs state' = fmdrop varName (IS_Refs state) \<and>
    (\<forall>name. name \<noteq> varName \<longrightarrow>
        (name |\<in>| IS_ConstLocals state' \<longleftrightarrow> name |\<in>| IS_ConstLocals state))"

lemma fresh_binding_stepD:
  assumes "fresh_binding_step varName val state state'"
  shows "static_parts_eq state state'"
    and "IS_World state' = IS_World state"
    and "IS_Store state' = IS_Store state @ [val]"
    and "IS_Locals state' = fmupd varName (length (IS_Store state)) (IS_Locals state)"
    and "IS_Refs state' = fmdrop varName (IS_Refs state)"
    and "\<And>name. name \<noteq> varName
            \<Longrightarrow> (name |\<in>| IS_ConstLocals state' \<longleftrightarrow> name |\<in>| IS_ConstLocals state)"
  using assms unfolding fresh_binding_step_def by blast+

(* state' is state with varName bound as a ref to (addr, path). *)
definition ref_binding_step ::
    "string \<Rightarrow> nat \<Rightarrow> LValuePath list \<Rightarrow> 'w InterpState \<Rightarrow> 'w InterpState \<Rightarrow> bool" where
  "ref_binding_step varName addr path state state' \<equiv>
    static_parts_eq state state' \<and>
    IS_World state' = IS_World state \<and>
    IS_Store state' = IS_Store state \<and>
    IS_Locals state' = fmdrop varName (IS_Locals state) \<and>
    IS_Refs state' = fmupd varName (addr, path) (IS_Refs state) \<and>
    (\<forall>name. name \<noteq> varName \<longrightarrow>
        (name |\<in>| IS_ConstLocals state' \<longleftrightarrow> name |\<in>| IS_ConstLocals state))"

lemma ref_binding_stepD:
  assumes "ref_binding_step varName addr path state state'"
  shows "static_parts_eq state state'"
    and "IS_World state' = IS_World state"
    and "IS_Store state' = IS_Store state"
    and "IS_Locals state' = fmdrop varName (IS_Locals state)"
    and "IS_Refs state' = fmupd varName (addr, path) (IS_Refs state)"
    and "\<And>name. name \<noteq> varName
            \<Longrightarrow> (name |\<in>| IS_ConstLocals state' \<longleftrightarrow> name |\<in>| IS_ConstLocals state)"
  using assms unfolding ref_binding_step_def by blast+

(* state' is state with the cell at addr overwritten by v. *)
definition store_write_step ::
    "nat \<Rightarrow> CoreValue \<Rightarrow> 'w InterpState \<Rightarrow> 'w InterpState \<Rightarrow> bool" where
  "store_write_step addr v state state' \<equiv>
    static_parts_eq state state' \<and>
    IS_World state' = IS_World state \<and>
    IS_Store state' = (IS_Store state)[addr := v] \<and>
    IS_Locals state' = IS_Locals state \<and>
    IS_Refs state' = IS_Refs state \<and>
    IS_ConstLocals state' = IS_ConstLocals state"

lemma store_write_stepD:
  assumes "store_write_step addr v state state'"
  shows "static_parts_eq state state'"
    and "IS_World state' = IS_World state"
    and "IS_Store state' = (IS_Store state)[addr := v]"
    and "IS_Locals state' = IS_Locals state"
    and "IS_Refs state' = IS_Refs state"
    and "IS_ConstLocals state' = IS_ConstLocals state"
  using assms unfolding store_write_step_def by blast+

(* What declaring a variable that is not ghost does to the ghost-ness of
   names. *)
lemma notghost_decl_var_ghost:
  assumes "TE_LocalVars env' = fmupd varName ty (TE_LocalVars env)"
    and "TE_GhostLocals env' = fminus (TE_GhostLocals env) {|varName|}"
  shows "\<not> tyenv_var_ghost env' varName"
    and "\<And>name. name \<noteq> varName \<Longrightarrow> tyenv_var_ghost env' name = tyenv_var_ghost env name"
proof -
  show "\<not> tyenv_var_ghost env' varName"
    by (simp add: tyenv_var_ghost_def assms)
next
  fix name assume ne: "name \<noteq> varName"
  then have ne': "varName \<noteq> name" by blast
  show "tyenv_var_ghost env' name = tyenv_var_ghost env name"
    using ne ne' by (simp add: tyenv_var_ghost_def assms)
qed


(* ========================================================================== *)
(* The same step taken in both states *)
(* ========================================================================== *)

(* Both states allocate a cell holding the same value and bind varName to it,
   and varName is not ghost afterwards. The embedding gains one entry: the new
   erased cell corresponds to the new full cell. *)
lemma state_erased_bind_both_fresh:
  assumes rel: "state_erased env emb full erased"
    and ng: "\<not> tyenv_var_ghost env' varName"
    and others: "\<And>name. name \<noteq> varName
                    \<Longrightarrow> tyenv_var_ghost env' name = tyenv_var_ghost env name"
    and fns: "TE_Functions env' = TE_Functions env"
    and stepF: "fresh_binding_step varName val full full'"
    and stepE: "fresh_binding_step varName val erased erased'"
    and constsV: "varName |\<in>| IS_ConstLocals erased' \<longleftrightarrow> varName |\<in>| IS_ConstLocals full'"
  shows "state_erased env' (emb @ [length (IS_Store full)]) full' erased'"
proof -
  note D = state_erasedD[OF rel]
  note F = fresh_binding_stepD[OF stepF]
  note E = fresh_binding_stepD[OF stepE]
  note stF = static_parts_eqD[OF F(1)]
  note stE = static_parts_eqD[OF E(1)]
  let ?n = "length (IS_Store full)"
  let ?emb' = "emb @ [?n]"
  have len_emb: "length (IS_Store erased) = length emb"
    using store_erasedD(1)[OF D(5)] by simp
  \<comment> \<open>The new full cell is not in the old embedding. \<close>
  have fresh: "?n \<notin> set emb"
  proof
    assume "?n \<in> set emb"
    from store_erased_emb_bound[OF D(5) this] show False by simp
  qed

  have se': "store_erased ?emb' full' erased'"
    unfolding store_erased_def
  proof (intro conjI allI impI)
    show "length ?emb' = length (IS_Store erased')" by (simp add: E(3) len_emb)
    show "distinct ?emb'" using store_erasedD(2)[OF D(5)] fresh by simp
  next
    fix i assume i_lt: "i < length ?emb'"
    show "?emb' ! i < length (IS_Store full')"
    proof (cases "i < length emb")
      case True
      from store_erasedD(3)[OF D(5) True] True
      show ?thesis by (simp add: nth_append F(3))
    next
      case False
      with i_lt have "i = length emb" by simp
      then show ?thesis by (simp add: F(3))
    qed
    show "IS_Store erased' ! i = IS_Store full' ! (?emb' ! i)"
    proof (cases "i < length emb")
      case True
      from store_erasedD(3)[OF D(5) True] store_erasedD(4)[OF D(5) True] True
      show ?thesis by (simp add: nth_append F(3) E(3) len_emb)
    next
      case False
      with i_lt have "i = length emb" by simp
      then show ?thesis by (simp add: nth_append F(3) E(3) len_emb)
    qed
  qed

  have g': "IS_Globals erased' = IS_Globals full'" using D(1) stF(1) stE(1) by simp
  have c': "IS_DataCtorsByType erased' = IS_DataCtorsByType full'" using D(2) stF(4) stE(4) by simp
  have dc': "IS_DataCtors erased' = IS_DataCtors full'" using D(9) stF(5) stE(5) by simp
  have w': "IS_World erased' = IS_World full'" using D(3) F(2) E(2) by simp
  have f': "funs_erased env' full' erased'"
  proof -
    have "funs_erased env' full' erased' = funs_erased env full erased"
      by (rule funs_erased_cong_all[OF fns stF(2) stE(2)])
    then show ?thesis using D(4) by (rule iffD2)
  qed
  have t': "IS_TyArgs erased' = IS_TyArgs full'" using D(6) stF(3) stE(3) by simp

  have l': "locals_erased env' ?emb' full' erased'"
    unfolding locals_erased_def
  proof (intro allI impI)
    fix name assume ng': "\<not> tyenv_var_ghost env' name"
    show "rel_option (\<lambda>i addr. i < length ?emb' \<and> addr = ?emb' ! i)
                     (fmlookup (IS_Locals erased') name) (fmlookup (IS_Locals full') name) \<and>
          rel_option (\<lambda>(i, path) (addr, path').
                         i < length ?emb' \<and> addr = ?emb' ! i \<and> path = path')
                     (fmlookup (IS_Refs erased') name) (fmlookup (IS_Refs full') name) \<and>
          (name |\<in>| IS_ConstLocals erased' \<longleftrightarrow> name |\<in>| IS_ConstLocals full')"
    proof (cases "name = varName")
      case True
      \<comment> \<open>The new variable: bound to the two new cells. \<close>
      show ?thesis using constsV by (simp add: True F(4) F(5) E(4) E(5) len_emb)
    next
      case False
      \<comment> \<open>Any other name: bound as before, and it was not ghost before. \<close>
      then have ne': "varName \<noteq> name" by blast
      from ng' others[OF False] have ng0: "\<not> tyenv_var_ghost env name" by simp
      note l = locals_erasedD[OF D(7) ng0]
      have le: "fmlookup (IS_Locals erased') name = fmlookup (IS_Locals erased) name"
        and lf: "fmlookup (IS_Locals full') name = fmlookup (IS_Locals full) name"
        and re: "fmlookup (IS_Refs erased') name = fmlookup (IS_Refs erased) name"
        and rf: "fmlookup (IS_Refs full') name = fmlookup (IS_Refs full) name"
        using False ne' by (simp_all add: F(4) F(5) E(4) E(5))
      have cs: "(name |\<in>| IS_ConstLocals erased') = (name |\<in>| IS_ConstLocals full')"
        using l(3) F(6)[OF False] E(6)[OF False] by simp
      show ?thesis
        unfolding le lf re rf
        by (intro conjI local_rel_extend[OF l(1)] ref_rel_extend[OF l(2)] cs)
    qed
  qed

  have s': "ghost_locals_separate env' ?emb' full'"
  proof (rule ghost_locals_separateI)
    fix name a
    assume g: "tyenv_var_ghost env' name"
      and l: "fmlookup (IS_Locals full') name = Some a"
    have ne: "name \<noteq> varName"
    proof
      assume "name = varName"
      with g ng show False by simp
    qed
    then have ne': "varName \<noteq> name" by blast
    from g others[OF ne] have g0: "tyenv_var_ghost env name" by simp
    from l ne ne' have l0: "fmlookup (IS_Locals full) name = Some a" by (simp add: F(4))
    from ghost_locals_separateD(1)[OF D(8) g0 l0]
    show "a < length (IS_Store full') \<and> a \<notin> set ?emb'" by (auto simp: F(3))
  next
    fix name a p
    assume g: "tyenv_var_ghost env' name"
      and r: "fmlookup (IS_Refs full') name = Some (a, p)"
    have ne: "name \<noteq> varName"
    proof
      assume "name = varName"
      with g ng show False by simp
    qed
    then have ne': "varName \<noteq> name" by blast
    from g others[OF ne] have g0: "tyenv_var_ghost env name" by simp
    from r ne ne' have r0: "fmlookup (IS_Refs full) name = Some (a, p)" by (simp add: F(5))
    from ghost_locals_separateD(2)[OF D(8) g0 r0]
    show "a < length (IS_Store full') \<and> a \<notin> set ?emb'" by (auto simp: F(3))
  qed

  show ?thesis by (rule state_erasedI[OF g' c' w' f' se' t' l' s' dc'])
qed

(* Both states bind varName as a ref, to corresponding addresses with the same
   path, and varName is not ghost afterwards. *)
lemma state_erased_bind_both_ref:
  assumes rel: "state_erased env emb full erased"
    and ng: "\<not> tyenv_var_ghost env' varName"
    and others: "\<And>name. name \<noteq> varName
                    \<Longrightarrow> tyenv_var_ghost env' name = tyenv_var_ghost env name"
    and fns: "TE_Functions env' = TE_Functions env"
    and stepF: "ref_binding_step varName addr path full full'"
    and stepE: "ref_binding_step varName i path erased erased'"
    and i_lt: "i < length emb"
    and addr_eq: "emb ! i = addr"
    and constsV: "varName |\<in>| IS_ConstLocals erased' \<longleftrightarrow> varName |\<in>| IS_ConstLocals full'"
  shows "state_erased env' emb full' erased'"
proof -
  note D = state_erasedD[OF rel]
  note F = ref_binding_stepD[OF stepF]
  note E = ref_binding_stepD[OF stepE]
  note stF = static_parts_eqD[OF F(1)]
  note stE = static_parts_eqD[OF E(1)]

  have se': "store_erased emb full' erased'"
  proof -
    have "store_erased emb full' erased' = store_erased emb full erased"
      by (rule store_erased_cong[OF F(3) E(3)])
    then show ?thesis using D(5) by (rule iffD2)
  qed

  have g': "IS_Globals erased' = IS_Globals full'" using D(1) stF(1) stE(1) by simp
  have c': "IS_DataCtorsByType erased' = IS_DataCtorsByType full'" using D(2) stF(4) stE(4) by simp
  have dc': "IS_DataCtors erased' = IS_DataCtors full'" using D(9) stF(5) stE(5) by simp
  have w': "IS_World erased' = IS_World full'" using D(3) F(2) E(2) by simp
  have f': "funs_erased env' full' erased'"
  proof -
    have "funs_erased env' full' erased' = funs_erased env full erased"
      by (rule funs_erased_cong_all[OF fns stF(2) stE(2)])
    then show ?thesis using D(4) by (rule iffD2)
  qed
  have t': "IS_TyArgs erased' = IS_TyArgs full'" using D(6) stF(3) stE(3) by simp

  have l': "locals_erased env' emb full' erased'"
    unfolding locals_erased_def
  proof (intro allI impI)
    fix name assume ng': "\<not> tyenv_var_ghost env' name"
    show "rel_option (\<lambda>i addr. i < length emb \<and> addr = emb ! i)
                     (fmlookup (IS_Locals erased') name) (fmlookup (IS_Locals full') name) \<and>
          rel_option (\<lambda>(i, path) (addr, path'). i < length emb \<and> addr = emb ! i \<and> path = path')
                     (fmlookup (IS_Refs erased') name) (fmlookup (IS_Refs full') name) \<and>
          (name |\<in>| IS_ConstLocals erased' \<longleftrightarrow> name |\<in>| IS_ConstLocals full')"
    proof (cases "name = varName")
      case True
      show ?thesis
        using constsV i_lt addr_eq by (simp add: True F(4) F(5) E(4) E(5))
    next
      case False
      then have ne': "varName \<noteq> name" by blast
      from ng' others[OF False] have ng0: "\<not> tyenv_var_ghost env name" by simp
      note l = locals_erasedD[OF D(7) ng0]
      have le: "fmlookup (IS_Locals erased') name = fmlookup (IS_Locals erased) name"
        and lf: "fmlookup (IS_Locals full') name = fmlookup (IS_Locals full) name"
        and re: "fmlookup (IS_Refs erased') name = fmlookup (IS_Refs erased) name"
        and rf: "fmlookup (IS_Refs full') name = fmlookup (IS_Refs full) name"
        using False ne' by (simp_all add: F(4) F(5) E(4) E(5))
      have cs: "(name |\<in>| IS_ConstLocals erased') = (name |\<in>| IS_ConstLocals full')"
        using l(3) F(6)[OF False] E(6)[OF False] by simp
      show ?thesis
        unfolding le lf re rf by (intro conjI l(1) l(2) cs)
    qed
  qed

  have s': "ghost_locals_separate env' emb full'"
  proof (rule ghost_locals_separateI)
    fix name a
    assume g: "tyenv_var_ghost env' name"
      and l: "fmlookup (IS_Locals full') name = Some a"
    have ne: "name \<noteq> varName"
    proof
      assume "name = varName"
      with g ng show False by simp
    qed
    then have ne': "varName \<noteq> name" by blast
    from g others[OF ne] have g0: "tyenv_var_ghost env name" by simp
    from l ne ne' have l0: "fmlookup (IS_Locals full) name = Some a" by (simp add: F(4))
    from ghost_locals_separateD(1)[OF D(8) g0 l0]
    show "a < length (IS_Store full') \<and> a \<notin> set emb" by (simp add: F(3))
  next
    fix name a p
    assume g: "tyenv_var_ghost env' name"
      and r: "fmlookup (IS_Refs full') name = Some (a, p)"
    have ne: "name \<noteq> varName"
    proof
      assume "name = varName"
      with g ng show False by simp
    qed
    then have ne': "varName \<noteq> name" by blast
    from g others[OF ne] have g0: "tyenv_var_ghost env name" by simp
    from r ne ne' have r0: "fmlookup (IS_Refs full) name = Some (a, p)" by (simp add: F(5))
    from ghost_locals_separateD(2)[OF D(8) g0 r0]
    show "a < length (IS_Store full') \<and> a \<notin> set emb" by (simp add: F(3))
  qed

  show ?thesis by (rule state_erasedI[OF g' c' w' f' se' t' l' s' dc'])
qed

(* Both states write the same value to corresponding cells. *)
lemma state_erased_write_both:
  assumes rel: "state_erased env emb full erased"
    and i_lt: "i < length emb"
    and addr_eq: "emb ! i = addr"
    and stepF: "store_write_step addr v full full'"
    and stepE: "store_write_step i v erased erased'"
  shows "state_erased env emb full' erased'"
proof -
  note D = state_erasedD[OF rel]
  note F = store_write_stepD[OF stepF]
  note E = store_write_stepD[OF stepE]
  note stF = static_parts_eqD[OF F(1)]
  note stE = static_parts_eqD[OF E(1)]
  have len_emb: "length (IS_Store erased) = length emb"
    using store_erasedD(1)[OF D(5)] by simp
  have dist: "distinct emb" by (rule store_erasedD(2)[OF D(5)])
  have addr_lt: "addr < length (IS_Store full)"
    using store_erasedD(3)[OF D(5) i_lt] addr_eq by simp

  have se': "store_erased emb full' erased'"
    unfolding store_erased_def
  proof (intro conjI allI impI)
    show "length emb = length (IS_Store erased')" by (simp add: E(3) len_emb)
    show "distinct emb" by (rule dist)
  next
    fix j assume j_lt: "j < length emb"
    note b = store_erasedD(3)[OF D(5) j_lt]
    note c = store_erasedD(4)[OF D(5) j_lt]
    show "emb ! j < length (IS_Store full')" using b by (simp add: F(3))
    show "IS_Store erased' ! j = IS_Store full' ! (emb ! j)"
    proof (cases "j = i")
      case True
      \<comment> \<open>The cell written, on both sides. \<close>
      show ?thesis
        using i_lt addr_lt by (simp add: True E(3) F(3) addr_eq len_emb)
    next
      case False
      \<comment> \<open>Another cell: the embedding is one-to-one, so it is untouched on
          both sides. \<close>
      then have ne_ij: "i \<noteq> j" by blast
      from nth_eq_iff_index_eq[OF dist i_lt j_lt] ne_ij have "emb ! i \<noteq> emb ! j" by simp
      with addr_eq have ne_a: "addr \<noteq> emb ! j" by simp
      show ?thesis using ne_ij ne_a c by (simp add: E(3) F(3))
    qed
  qed

  have g': "IS_Globals erased' = IS_Globals full'" using D(1) stF(1) stE(1) by simp
  have c': "IS_DataCtorsByType erased' = IS_DataCtorsByType full'" using D(2) stF(4) stE(4) by simp
  have dc': "IS_DataCtors erased' = IS_DataCtors full'" using D(9) stF(5) stE(5) by simp
  have w': "IS_World erased' = IS_World full'" using D(3) F(2) E(2) by simp
  have f': "funs_erased env full' erased'"
  proof -
    have "funs_erased env full' erased' = funs_erased env full erased"
      by (rule funs_erased_cong_all[OF refl stF(2) stE(2)])
    then show ?thesis using D(4) by (rule iffD2)
  qed
  have t': "IS_TyArgs erased' = IS_TyArgs full'" using D(6) stF(3) stE(3) by simp
  have l': "locals_erased env emb full' erased'"
  proof -
    have "locals_erased env emb full' erased' = locals_erased env emb full erased"
      by (rule locals_erased_cong_states[OF F(4) F(5) F(6) E(4) E(5) E(6)])
    then show ?thesis using D(7) by (rule iffD2)
  qed
  have s': "ghost_locals_separate env emb full'"
  proof -
    have len: "length (IS_Store full') = length (IS_Store full)" by (simp add: F(3))
    have "ghost_locals_separate env emb full' = ghost_locals_separate env emb full"
      by (rule ghost_locals_separate_cong_state[OF F(4) F(5) len])
    then show ?thesis using D(8) by (rule iffD2)
  qed

  show ?thesis by (rule state_erasedI[OF g' c' w' f' se' t' l' s' dc'])
qed

(* Both states get the same new world. *)
lemma state_erased_set_world:
  assumes rel: "state_erased env emb full erased"
  shows "state_erased env emb (full \<lparr> IS_World := w \<rparr>)
           (erased \<lparr> IS_World := w \<rparr>)"
proof -
  note D = state_erasedD[OF rel]
  let ?f = "full \<lparr> IS_World := w \<rparr>"
  let ?e = "erased \<lparr> IS_World := w \<rparr>"
  show ?thesis
  proof (rule state_erasedI)
    show "IS_Globals ?e = IS_Globals ?f" using D(1) by simp
    show "IS_DataCtorsByType ?e = IS_DataCtorsByType ?f" using D(2) by simp
    show "IS_DataCtors ?e = IS_DataCtors ?f" using D(9) by simp
    show "IS_World ?e = IS_World ?f" by simp
    show "funs_erased env ?f ?e"
    proof -
      have "funs_erased env ?f ?e = funs_erased env full erased"
        by (rule funs_erased_cong_all) simp_all
      then show ?thesis using D(4) by (rule iffD2)
    qed
    show "store_erased emb ?f ?e"
    proof -
      have "store_erased emb ?f ?e = store_erased emb full erased"
        by (rule store_erased_cong) simp_all
      then show ?thesis using D(5) by (rule iffD2)
    qed
    show "IS_TyArgs ?e = IS_TyArgs ?f" using D(6) by simp
    show "locals_erased env emb ?f ?e"
    proof -
      have "locals_erased env emb ?f ?e = locals_erased env emb full erased"
        by (rule locals_erased_cong_states) simp_all
      then show ?thesis using D(7) by (rule iffD2)
    qed
    show "ghost_locals_separate env emb ?f"
    proof -
      have "ghost_locals_separate env emb ?f = ghost_locals_separate env emb full"
        by (rule ghost_locals_separate_cong_state) simp_all
      then show ?thesis using D(8) by (rule iffD2)
    qed
  qed
qed


(* ========================================================================== *)
(* Leaving a scope in both states *)
(* ========================================================================== *)

(* Given the relation at the start of the scope, and the heap part of the
   relation at its end (under an extended embedding, in whatever environment
   the body ended in), the two states after restore_scope are related as the
   starting states were, by the starting embedding: each has its starting
   frame again, and its store cut back to the starting length. *)
lemma state_erased_restore_scope_both:
  assumes rel: "state_erased env emb full erased"
    and inner: "heap_erased env1 (emb @ extra) full1 erased1"
    and fns: "TE_Functions env1 = TE_Functions env"
    and len: "length (IS_Store full) \<le> length (IS_Store full1)"
  shows "state_erased env emb (restore_scope full full1) (restore_scope erased erased1)"
proof -
  let ?rsF = "restore_scope full full1"
  let ?rsE = "restore_scope erased erased1"
  note D = state_erasedD[OF rel]
  from inner have g1: "IS_Globals erased1 = IS_Globals full1"
    and c1: "IS_DataCtorsByType erased1 = IS_DataCtorsByType full1"
    and dc1: "IS_DataCtors erased1 = IS_DataCtors full1"
    and w1: "IS_World erased1 = IS_World full1"
    and f1: "funs_erased env1 full1 erased1"
    and se1: "store_erased (emb @ extra) full1 erased1"
    unfolding heap_erased_def by blast+
  note se = D(5)
  have len_emb: "length (IS_Store erased) = length emb"
    using store_erasedD(1)[OF se] by simp
  have len_emb1: "length (IS_Store erased1) = length emb + length extra"
    using store_erasedD(1)[OF se1] by simp
  have lenE0: "length (IS_Store erased) \<le> length (IS_Store erased1)"
    by (simp add: len_emb len_emb1)
  have lenE: "length (IS_Store ?rsE) = length emb"
    using lenE0 by (simp add: min_absorb2 len_emb)
  have lenF: "length (IS_Store ?rsF) = length (IS_Store full)"
    using len by (simp add: min_absorb2)

  have se_rs: "store_erased emb ?rsF ?rsE"
    unfolding store_erased_def
  proof (intro conjI allI impI)
    show "length emb = length (IS_Store ?rsE)" by (rule lenE[symmetric])
    show "distinct emb" by (rule store_erasedD(2)[OF se])
  next
    fix i assume i_lt: "i < length emb"
    then have i_lt1: "i < length (emb @ extra)" by simp
    have nth: "(emb @ extra) ! i = emb ! i" using i_lt by (simp add: nth_append)
    have i_ltE: "i < length (IS_Store erased)" using i_lt by (simp add: len_emb)
    note b = store_erasedD(3)[OF se i_lt]
    note b1 = store_erasedD(3)[OF se1 i_lt1, unfolded nth]
    note v1 = store_erasedD(4)[OF se1 i_lt1, unfolded nth]
    show "emb ! i < length (IS_Store ?rsF)" using b b1 by simp
    show "IS_Store ?rsE ! i = IS_Store ?rsF ! (emb ! i)" using b v1 i_ltE by simp
  qed

  show ?thesis
  proof (rule state_erasedI)
    show "IS_Globals ?rsE = IS_Globals ?rsF" using g1 by simp
    show "IS_DataCtorsByType ?rsE = IS_DataCtorsByType ?rsF" using c1 by simp
    show "IS_DataCtors ?rsE = IS_DataCtors ?rsF" using dc1 by simp
    show "IS_World ?rsE = IS_World ?rsF" using w1 by simp
    show "funs_erased env ?rsF ?rsE"
    proof -
      have "funs_erased env ?rsF ?rsE = funs_erased env1 full1 erased1"
        by (rule funs_erased_cong_all) (simp_all add: fns)
      then show ?thesis using f1 by (rule iffD2)
    qed
    show "store_erased emb ?rsF ?rsE" by (rule se_rs)
    show "IS_TyArgs ?rsE = IS_TyArgs ?rsF" using D(6) by simp
    show "locals_erased env emb ?rsF ?rsE"
    proof -
      have "locals_erased env emb ?rsF ?rsE = locals_erased env emb full erased"
        by (rule locals_erased_cong_states) simp_all
      then show ?thesis using D(7) by (rule iffD2)
    qed
    show "ghost_locals_separate env emb ?rsF"
    proof -
      have "ghost_locals_separate env emb ?rsF = ghost_locals_separate env emb full"
        by (rule ghost_locals_separate_cong_state[OF _ _ lenF]) simp_all
      then show ?thesis using D(8) by (rule iffD2)
    qed
  qed
qed


(* ========================================================================== *)
(* Related results *)
(* ========================================================================== *)

lemma result_erased_ContinueI:
  assumes "state_erased env (emb @ extra) full erased"
  shows "result_erased env emb (Continue full) (Continue erased)"
  using assms by auto

lemma result_erased_Continue_same:
  assumes "state_erased env emb full erased"
  shows "result_erased env emb (Continue full) (Continue erased)"
proof -
  from assms have "state_erased env (emb @ []) full erased" by simp
  then show ?thesis by (rule result_erased_ContinueI)
qed

lemma result_erased_ReturnI:
  assumes "heap_erased env (emb @ extra) full erased"
  shows "result_erased env emb (Return full v) (Return erased v)"
  using assms by auto

lemma result_erased_Return_same:
  assumes "heap_erased env emb full erased"
  shows "result_erased env emb (Return full v) (Return erased v)"
proof -
  from assms have "heap_erased env (emb @ []) full erased" by simp
  then show ?thesis by (rule result_erased_ReturnI)
qed

lemma result_erased_ContinueD:
  assumes "result_erased env emb (Continue full) resE"
  shows "\<exists>erased extra. resE = Continue erased
                       \<and> state_erased env (emb @ extra) full erased"
  using assms by (cases resE) auto

lemma result_erased_ReturnD:
  assumes "result_erased env emb (Return full v) resE"
  shows "\<exists>erased extra. resE = Return erased v \<and> heap_erased env (emb @ extra) full erased"
  using assms by (cases resE) auto

(* The form in which the results of a single statement are put together: both
   are Continue, and the final states are related. *)
lemma result_erased_stateI:
  assumes "is_continue res"
    and "is_continue resE"
    and "state_erased env (emb @ extra) (result_state res) (result_state resE)"
  shows "result_erased env emb res resE"
  using assms by (cases res; cases resE) auto

lemma result_erased_state_same:
  assumes "is_continue res"
    and "is_continue resE"
    and "state_erased env emb (result_state res) (result_state resE)"
  shows "result_erased env emb res resE"
proof -
  from assms(3) have "state_erased env (emb @ []) (result_state res) (result_state resE)"
    by simp
  then show ?thesis by (rule result_erased_stateI[OF assms(1,2)])
qed

(* Results related by an extension of the embedding are related by the
   embedding itself. *)
lemma result_erased_weaken:
  assumes "result_erased env (emb @ extra) res resE"
  shows "result_erased env emb res resE"
  using assms by (cases res; cases resE) auto

(* For a Return, the environment matters only through its function
   signatures. *)
lemma result_erased_Return_env:
  assumes "result_erased env1 emb (Return full v) resE"
    and "TE_Functions env2 = TE_Functions env1"
  shows "result_erased env2 emb (Return full v) resE"
proof -
  from result_erased_ReturnD[OF assms(1)] obtain erased extra where
    e: "resE = Return erased v" and h: "heap_erased env1 (emb @ extra) full erased"
    by blast
  have "heap_erased env2 (emb @ extra) full erased = heap_erased env1 (emb @ extra) full erased"
    by (rule heap_erased_cong_env[OF assms(2)])
  then have "heap_erased env2 (emb @ extra) full erased" using h by (rule iffD2)
  then have "result_erased env2 emb (Return full v) (Return erased v)"
    by (rule result_erased_ReturnI)
  then show ?thesis by (simp only: e)
qed

(* The result of a Block, a Match arm, or a While body that returns: the body's
   result, with the scope left. *)
fun scope_result :: "'w InterpState \<Rightarrow> 'w ExecResult \<Rightarrow> 'w ExecResult" where
  "scope_result old (Continue state) = Continue (restore_scope old state)"
| "scope_result old (Return state v) = Return (restore_scope old state) v"

lemma interp_Block_scope_result:
  assumes "interp_statement_list d fuel state body = Inr bodyRes"
  shows "interp_statement d (Suc fuel) state (CoreStmt_Block body)
           = Inr (scope_result state bodyRes)"
  using assms by (cases bodyRes) simp_all

lemma interp_Match_scope_result:
  assumes "interp_term d fuel state scrut = Inr scrutVal"
    and "find_matching_arm scrutVal arms = Inr armStmts"
    and "interp_statement_list d fuel state armStmts = Inr bodyRes"
  shows "interp_statement d (Suc fuel) state (CoreStmt_Match g scrut arms)
           = Inr (scope_result state bodyRes)"
  using assms by (cases bodyRes) simp_all

(* Leaving a scope preserves the relation between results. The results of the
   body may be related in a different environment (the one the body ended in);
   the results after leaving the scope are related in the starting one. *)
lemma result_erased_scope_exit:
  assumes rel: "state_erased env emb full erased"
    and inner: "result_erased env1 emb res1 res1E"
    and fns: "TE_Functions env1 = TE_Functions env"
    and len: "length (IS_Store full) \<le> length (IS_Store (result_state res1))"
  shows "result_erased env emb (scope_result full res1) (scope_result erased res1E)"
proof (cases res1)
  case (Continue full1)
  from result_erased_ContinueD[OF inner[unfolded Continue]] obtain erased1 extra where
    e: "res1E = Continue erased1" and r: "state_erased env1 (emb @ extra) full1 erased1"
    by blast
  have h: "heap_erased env1 (emb @ extra) full1 erased1" by (rule state_erased_heap[OF r])
  from len Continue have len': "length (IS_Store full) \<le> length (IS_Store full1)" by simp
  have "state_erased env emb (restore_scope full full1) (restore_scope erased erased1)"
    by (rule state_erased_restore_scope_both[OF rel h fns len'])
  then have "result_erased env emb (Continue (restore_scope full full1))
                                   (Continue (restore_scope erased erased1))"
    by (rule result_erased_Continue_same)
  then show ?thesis by (simp only: Continue e scope_result.simps)
next
  case (Return full1 v)
  from result_erased_ReturnD[OF inner[unfolded Return]] obtain erased1 extra where
    e: "res1E = Return erased1 v" and h: "heap_erased env1 (emb @ extra) full1 erased1"
    by blast
  from len Return have len': "length (IS_Store full) \<le> length (IS_Store full1)" by simp
  have "state_erased env emb (restore_scope full full1) (restore_scope erased erased1)"
    by (rule state_erased_restore_scope_both[OF rel h fns len'])
  then have "heap_erased env emb (restore_scope full full1) (restore_scope erased erased1)"
    by (rule state_erased_heap)
  then have "result_erased env emb (Return (restore_scope full full1) v)
                                   (Return (restore_scope erased erased1) v)"
    by (rule result_erased_Return_same)
  then show ?thesis by (simp only: Return e scope_result.simps)
qed


(* ========================================================================== *)
(* Swap *)
(* ========================================================================== *)

(* A swap of two lvalues, at corresponding addresses with the same paths. *)
lemma perform_swap_erased:
  assumes rel: "state_erased env emb full erased"
    and i1: "i1 < length emb" and a1: "emb ! i1 = addr1"
    and i2: "i2 < length emb" and a2: "emb ! i2 = addr2"
    and sw: "perform_swap full (addr1, path1) (addr2, path2) = Inr full'"
  shows "\<exists>erased'. perform_swap erased (i1, path1) (i2, path2) = Inr erased'
                   \<and> state_erased env emb full' erased'"
proof -
  \<comment> \<open>Name the four intermediate results of the swap in the full state. \<close>
  obtain val1 where g1: "get_value_at_path (IS_Store full ! addr1) path1 = Inr val1"
    using sw by (cases "get_value_at_path (IS_Store full ! addr1) path1") simp_all
  obtain val2 where g2: "get_value_at_path (IS_Store full ! addr2) path2 = Inr val2"
    using sw g1 by (cases "get_value_at_path (IS_Store full ! addr2) path2") simp_all
  obtain new_val1 where
    u1: "update_value_at_path (IS_Store full ! addr1) path1 val2 = Inr new_val1"
    using sw g1 g2
    by (cases "update_value_at_path (IS_Store full ! addr1) path1 val2") simp_all
  obtain new_val2 where
    u2: "update_value_at_path ((IS_Store full)[addr1 := new_val1] ! addr2) path2 val1
           = Inr new_val2"
    using sw g1 g2 u1
    by (cases "update_value_at_path ((IS_Store full)[addr1 := new_val1] ! addr2) path2 val1")
       (simp_all add: Let_def)
  from sw[symmetric] g1 g2 u1 u2
  have full'_eq: "full' = full \<lparr> IS_Store := (IS_Store full)[addr1 := new_val1,
                                                              addr2 := new_val2] \<rparr>"
    by (simp add: Let_def)

  \<comment> \<open>The two writes, one after the other, in both states. \<close>
  let ?fullM = "full \<lparr> IS_Store := (IS_Store full)[addr1 := new_val1] \<rparr>"
  let ?erasedM = "erased \<lparr> IS_Store := (IS_Store erased)[i1 := new_val1] \<rparr>"
  have relM: "state_erased env emb ?fullM ?erasedM"
    by (rule state_erased_write_both[where v = new_val1, OF rel i1 a1])
       (simp_all add: store_write_step_def static_parts_eq_def)
  let ?fullN = "?fullM \<lparr> IS_Store := (IS_Store ?fullM)[addr2 := new_val2] \<rparr>"
  let ?erasedN = "?erasedM \<lparr> IS_Store := (IS_Store ?erasedM)[i2 := new_val2] \<rparr>"
  have relN: "state_erased env emb ?fullN ?erasedN"
    by (rule state_erased_write_both[where v = new_val2, OF relM i2 a2])
       (simp_all add: store_write_step_def static_parts_eq_def)
  let ?erased' = "erased \<lparr> IS_Store := (IS_Store erased)[i1 := new_val1, i2 := new_val2] \<rparr>"
  have rel': "state_erased env emb full' ?erased'"
    using relN by (simp add: full'_eq)

  \<comment> \<open>The swap in the erased state reads and writes the same values. \<close>
  have c1: "IS_Store erased ! i1 = IS_Store full ! addr1" by (rule erased_cell[OF rel i1 a1])
  have c2: "IS_Store erased ! i2 = IS_Store full ! addr2" by (rule erased_cell[OF rel i2 a2])
  have c12: "(IS_Store erased)[i1 := new_val1] ! i2 = (IS_Store full)[addr1 := new_val1] ! addr2"
    using erased_cell[OF relM i2 a2] by simp
  have swE: "perform_swap erased (i1, path1) (i2, path2) = Inr ?erased'"
    using g1 g2 u1 u2 by (simp add: c1 c2 c12 Let_def)
  from swE rel' show ?thesis by blast
qed


(* ========================================================================== *)
(* Calls: the function table *)
(* ========================================================================== *)

lemma erase_ghost_interp_fun_simps [simp]:
  "IF_TyArgs (erase_ghost_interp_fun funInfos name f) = IF_TyArgs f"
  "IF_Args (erase_ghost_interp_fun funInfos name f)
     = erase_ghost_args funInfos name (IF_Args f)"
  "IF_Impure (erase_ghost_interp_fun funInfos name f) = IF_Impure f"
  "IF_Body (erase_ghost_interp_fun funInfos name f)
     = map_sum (erase_ghost_statement_list funInfos) id (IF_Body f)"
  by (simp_all add: erase_ghost_interp_fun_def)

(* A function that is not ghost is, in the erased state, the erased function:
   the same function without its ghost parameters, and with its body erased. *)
lemma funs_erased_lookup:
  assumes "funs_erased env full erased"
    and "fmlookup (TE_Functions env) fnName = Some info"
    and "FI_Ghost info = NotGhost"
    and "fmlookup (IS_Functions full) fnName = Some f"
  shows "fmlookup (IS_Functions erased) fnName
           = Some (erase_ghost_interp_fun (TE_Functions env) fnName f)"
proof -
  from assms(1,2,3)
  have "fmlookup (IS_Functions erased) fnName
          = map_option (erase_ghost_interp_fun (TE_Functions env) fnName)
                       (fmlookup (IS_Functions full) fnName)"
    unfolding funs_erased_def by blast
  with assms(4) show ?thesis by simp
qed

(* A function that is pure in the full state is pure in the erased state.
   (The converse fails: the full function may have a ghost Ref parameter, which
   the erased function does not have.) *)
lemma is_pure_fun_erased:
  assumes "funs_erased env full erased"
    and "fmlookup (TE_Functions env) fnName = Some info"
    and "FI_Ghost info = NotGhost"
    and "is_pure_fun full fnName"
  shows "is_pure_fun erased fnName"
proof (cases "fmlookup (IS_Functions full) fnName")
  case None
  with assms(4) show ?thesis by simp
next
  case (Some f)
  from assms(4) Some
  have noRef: "\<not> list_ex (\<lambda>(_, vr). vr = Ref) (IF_Args f)" and np: "\<not> IF_Impure f"
    by simp_all
  \<comment> \<open>The erased parameters are among the full ones. \<close>
  from noRef
  have noRefE: "\<not> list_ex (\<lambda>(_, vr). vr = Ref)
                    (erase_ghost_args (TE_Functions env) fnName (IF_Args f))"
    by (auto simp: list_ex_iff erase_ghost_args_def assms(2)
             dest: set_drop_ghost_subset[THEN subsetD])
  from funs_erased_lookup[OF assms(1,2,3) Some] noRefE np show ?thesis by simp
qed

(* The bodies of the functions typecheck, each in the environment of its own
   function and in the mode of that function. This is the part of
   funs_exist_in_state that the simulation proof uses.

   It is stated for a fixed environment genv. The environment changes as
   statements run, but body_env_for only looks at fields that do not. *)
definition fun_bodies_typed :: "CoreTyEnv \<Rightarrow> (string, 'w InterpFun) fmap \<Rightarrow> bool" where
  "fun_bodies_typed genv funs \<equiv>
    \<forall>fnName info f body.
      fmlookup (TE_Functions genv) fnName = Some info \<longrightarrow>
      fmlookup funs fnName = Some f \<longrightarrow>
      IF_Body f = Inl body \<longrightarrow>
        core_statement_list_type (body_env_for genv (map fst (IF_Args f)) info)
          (FI_Ghost info) body \<noteq> None"

lemma funs_exist_in_state_bodies_typed:
  assumes "funs_exist_in_state state env"
  shows "fun_bodies_typed env (IS_Functions state)"
  unfolding fun_bodies_typed_def
proof (intro allI impI)
  fix fnName info f body
  assume info: "fmlookup (TE_Functions env) fnName = Some info"
    and f: "fmlookup (IS_Functions state) fnName = Some f"
    and b: "IF_Body f = Inl body"
  from assms info
  have "case fmlookup (IS_Functions state) fnName of
          None \<Rightarrow> False
        | Some interpFun \<Rightarrow> fun_info_matches_interp_fun env info interpFun"
    unfolding funs_exist_in_state_def by blast
  with f have "fun_info_matches_interp_fun env info f" by simp
  with b show "core_statement_list_type (body_env_for env (map fst (IF_Args f)) info)
                 (FI_Ghost info) body \<noteq> None"
    by (simp add: fun_info_matches_interp_fun_def)
qed

(* The environment of a function body has the same function signatures. *)
lemma body_env_for_facts:
  "TE_Functions (body_env_for env names info) = TE_Functions env"
  by (simp add: body_env_for_def)

(* The environment of the body of a function that is not ghost belongs to a
   function that is not ghost. *)
lemma body_env_for_notghost:
  assumes "FI_Ghost info = NotGhost"
  shows "TE_FunctionGhost (body_env_for env names info) = NotGhost"
  using assms by (simp add: body_env_for_def)

(* In that environment, the ghost variables are the ghost parameters. Here
   names are the (distinct) parameter names, one for each parameter of the
   signature, and the flags are those of the signature. *)
lemma body_env_for_param_ghost:
  assumes ng: "FI_Ghost info = NotGhost"
    and dist: "distinct names"
    and len: "length names = length (FI_TmArgs info)"
    and mem: "(name, gh) \<in> set (zip names (param_ghost_flags info))"
  shows "tyenv_var_ghost (body_env_for env names info) name \<longleftrightarrow> gh = Ghost"
proof -
  let ?be = "body_env_for env names info"
  let ?z = "zip names (map snd (FI_TmArgs info))"
  from mem obtain i where ni: "names ! i = name" and gi: "param_ghost_flags info ! i = gh"
    and i_lt: "i < length names"
    by (auto simp: in_set_zip)
  from i_lt len have i_fi: "i < length (FI_TmArgs info)" by simp
  have gi': "snd (snd (FI_TmArgs info ! i)) = gh"
    using gi i_fi by (simp add: param_ghost_flags_def case_prod_unfold)

  \<comment> \<open>Every parameter is a local variable of the body. \<close>
  have lv: "fmlookup (TE_LocalVars ?be) name \<noteq> None"
  proof -
    have nin: "name \<in> set names" using ni i_lt by (metis nth_mem)
    have "length names = length (map fst (FI_TmArgs info))" using len by simp
    from map_of_zip_is_Some[OF this] nin obtain ty where
      "map_of (zip names (map fst (FI_TmArgs info))) name = Some ty"
      by blast
    then show ?thesis by (simp add: body_env_for_def fmlookup_of_list)
  qed

  \<comment> \<open>The ghost locals are the names of the ghost parameters. A name has one
      flag, because the names are distinct. \<close>
  have gl: "TE_GhostLocals ?be = fset_of_list (map fst (filter (\<lambda>(_, _, gh). gh = Ghost) ?z))"
    by (simp add: body_env_for_def ng)
  have gm: "name |\<in>| TE_GhostLocals ?be \<longleftrightarrow> gh = Ghost"
  proof
    assume "name |\<in>| TE_GhostLocals ?be"
    then have "name \<in> fst ` set (filter (\<lambda>(_, _, gh). gh = Ghost) ?z)"
      unfolding gl by (simp only: fset_of_list_elem set_map)
    then obtain p where pm: "p \<in> set ?z" and pg: "(\<lambda>(_, _, gh). gh = Ghost) p"
      and pn: "fst p = name"
      by (auto simp: image_iff)
    from pm obtain j where j_lt: "j < length names" and nj: "names ! j = fst p"
      and sj: "map snd (FI_TmArgs info) ! j = snd p"
      by (auto simp: in_set_zip)
    from j_lt len have j_fi: "j < length (FI_TmArgs info)" by simp
    from pg sj j_fi have gj: "snd (snd (FI_TmArgs info ! j)) = Ghost"
      by (auto simp: case_prod_unfold)
    from dist nj pn ni i_lt j_lt have "j = i" by (metis nth_eq_iff_index_eq)
    with gj gi' show "gh = Ghost" by simp
  next
    assume g: "gh = Ghost"
    have "(name, snd (FI_TmArgs info ! i)) \<in> set ?z"
      using ni i_lt i_fi by (auto simp: in_set_zip)
    moreover have "(\<lambda>(_, _, gh). gh = Ghost) (name, snd (FI_TmArgs info ! i))"
      using gi' g by (simp add: case_prod_unfold)
    ultimately have "name \<in> fst ` set (filter (\<lambda>(_, _, gh). gh = Ghost) ?z)" by force
    then show "name |\<in>| TE_GhostLocals ?be"
      unfolding gl by (simp only: fset_of_list_elem set_map)
  qed

  show ?thesis
    unfolding tyenv_var_ghost_def using lv gm by blast
qed


(* ========================================================================== *)
(* Calls: binding the arguments *)
(* ========================================================================== *)

(* The states in which the binding of arguments starts: the caller's states
   with empty frames. They are related in the environment of the callee's
   body. (Its ghost variables are the callee's ghost parameters, and none of
   them is bound yet.) *)
lemma state_erased_call_entry:
  assumes rel: "state_erased env emb full erased"
    and fns: "TE_Functions envB = TE_Functions env"
  shows "state_erased envB emb
           (full \<lparr> IS_Locals := fmempty, IS_Refs := fmempty,
                   IS_ConstLocals := {||}, IS_TyArgs := tyArgs \<rparr>)
           (erased \<lparr> IS_Locals := fmempty, IS_Refs := fmempty,
                     IS_ConstLocals := {||}, IS_TyArgs := tyArgs \<rparr>)"
proof -
  note D = state_erasedD[OF rel]
  let ?f = "full \<lparr> IS_Locals := fmempty, IS_Refs := fmempty,
                   IS_ConstLocals := {||}, IS_TyArgs := tyArgs \<rparr>"
  let ?e = "erased \<lparr> IS_Locals := fmempty, IS_Refs := fmempty,
                     IS_ConstLocals := {||}, IS_TyArgs := tyArgs \<rparr>"
  show ?thesis
  proof (rule state_erasedI)
    show "IS_Globals ?e = IS_Globals ?f" using D(1) by simp
    show "IS_DataCtorsByType ?e = IS_DataCtorsByType ?f" using D(2) by simp
    show "IS_DataCtors ?e = IS_DataCtors ?f" using D(9) by simp
    show "IS_World ?e = IS_World ?f" using D(3) by simp
    show "funs_erased envB ?f ?e"
    proof -
      have "funs_erased envB ?f ?e = funs_erased env full erased"
        by (rule funs_erased_cong_all[OF fns]) simp_all
      then show ?thesis using D(4) by (rule iffD2)
    qed
    show "store_erased emb ?f ?e"
    proof -
      have "store_erased emb ?f ?e = store_erased emb full erased"
        by (rule store_erased_cong) simp_all
      then show ?thesis using D(5) by (rule iffD2)
    qed
    show "IS_TyArgs ?e = IS_TyArgs ?f" by simp
    show "locals_erased envB emb ?f ?e" by (simp add: locals_erased_def)
    show "ghost_locals_separate envB emb ?f"
      by (simp add: ghost_locals_separate_def)
  qed
qed

(* Binding the argument of a parameter that is not ghost, in both states. The
   value result and the lvalue result of the argument in the erased state
   (vE, rE) correspond to those in the full state (vF, rF): the same value, and
   corresponding addresses under the caller's embedding emb.

   A Var parameter gets a new cell in both states, so the embedding grows at
   the end; a Ref parameter points to corresponding cells of the caller. *)
lemma process_one_arg_erased:
  assumes rel: "state_erased envB (emb @ extra) fullK erasedK"
    and ng: "\<not> tyenv_var_ghost envB (fst p)"
    and vals: "\<forall>v. vF = Inr v \<longrightarrow> vE = Inr v"
    and refs: "\<forall>addr path. rF = Inr (addr, path) \<longrightarrow>
                 (\<exists>i. rE = Inr (i, path) \<and> i < length emb \<and> emb ! i = addr)"
    and stepF: "process_one_arg (p, rF, vF) (Inr fullK) = Inr mid"
  shows "\<exists>midE extraM. process_one_arg (p, rE, vE) (Inr erasedK) = Inr midE \<and>
                         state_erased envB (emb @ extraM) mid midE \<and>
                         length (IS_Store fullK) \<le> length (IS_Store mid) \<and>
                         (extraM = extra \<or> extraM = extra @ [length (IS_Store fullK)])"
proof -
  obtain name vr where p_eq: "p = (name, vr)" by (cases p)
  from ng p_eq have ng: "\<not> tyenv_var_ghost envB name" by simp
  show ?thesis
  proof (cases vr)
    case Var
    show ?thesis
    proof (cases vF)
      case (Inl err)
      with p_eq Var stepF show ?thesis by simp
    next
      case (Inr val)
      with vals have vE_eq: "vE = Inr val" by simp
      from p_eq Var Inr stepF[symmetric]
      have sF: "fresh_binding_step name val fullK mid"
        and cF: "name |\<in>| IS_ConstLocals mid"
        by (simp_all add: fresh_binding_step_def static_parts_eq_def Let_def)
      have "\<exists>midE. process_one_arg (p, rE, vE) (Inr erasedK) = Inr midE"
        by (simp add: p_eq Var vE_eq Let_def)
      then obtain midE where
        stepE: "process_one_arg (p, rE, vE) (Inr erasedK) = Inr midE"
        by blast
      from p_eq Var vE_eq stepE[symmetric]
      have sE: "fresh_binding_step name val erasedK midE"
        and cE: "name |\<in>| IS_ConstLocals midE"
        by (simp_all add: fresh_binding_step_def static_parts_eq_def Let_def)
      have "state_erased envB ((emb @ extra) @ [length (IS_Store fullK)]) mid midE"
        by (rule state_erased_bind_both_fresh[OF rel ng refl refl sF sE]) (simp add: cF cE)
      then have rel': "state_erased envB (emb @ (extra @ [length (IS_Store fullK)]))
                         mid midE"
        by simp
      have len': "length (IS_Store fullK) \<le> length (IS_Store mid)"
        by (simp add: fresh_binding_stepD(3)[OF sF])
      show ?thesis
        by (rule exI[of _ midE], rule exI[of _ "extra @ [length (IS_Store fullK)]"])
           (use stepE rel' len' in simp)
    qed
  next
    case Ref
    show ?thesis
    proof (cases rF)
      case (Inl err)
      with p_eq Ref stepF show ?thesis by simp
    next
      case refInr: (Inr addrPath)
      obtain addr path where ap: "addrPath = (addr, path)" by (cases addrPath)
      from refs refInr ap obtain i where
        rE_eq: "rE = Inr (i, path)" and i_lt: "i < length emb" and ei: "emb ! i = addr"
        by auto
      show ?thesis
      proof (cases vF)
        case (Inl err)
        with p_eq Ref refInr ap stepF show ?thesis by simp
      next
        case (Inr val)
        with vals have vE_eq: "vE = Inr val" by simp
        from p_eq Ref refInr ap Inr stepF[symmetric]
        have sF: "ref_binding_step name addr path fullK mid"
          and cF: "name |\<notin>| IS_ConstLocals mid"
          by (simp_all add: ref_binding_step_def static_parts_eq_def)
        have "\<exists>midE. process_one_arg (p, rE, vE) (Inr erasedK) = Inr midE"
          by (simp add: p_eq Ref rE_eq vE_eq)
        then obtain midE where
          stepE: "process_one_arg (p, rE, vE) (Inr erasedK) = Inr midE"
          by blast
        from p_eq Ref rE_eq vE_eq stepE[symmetric]
        have sE: "ref_binding_step name i path erasedK midE"
          and cE: "name |\<notin>| IS_ConstLocals midE"
          by (simp_all add: ref_binding_step_def static_parts_eq_def)
        have i_lt': "i < length (emb @ extra)" using i_lt by simp
        have ei': "(emb @ extra) ! i = addr" using i_lt ei by (simp add: nth_append)
        have rel': "state_erased envB (emb @ extra) mid midE"
          by (rule state_erased_bind_both_ref[OF rel ng refl refl sF sE i_lt' ei'])
             (simp add: cF cE)
        have len': "length (IS_Store fullK) \<le> length (IS_Store mid)"
          by (simp add: ref_binding_stepD(3)[OF sF])
        show ?thesis
          by (rule exI[of _ midE], rule exI[of _ extra]) (use stepE rel' len' in simp)
      qed
    qed
  qed
qed

(* Binding the argument of a ghost parameter. Only the full state does this:
   the erased function does not have the parameter. The erased state stays
   where it is, as it does when a ghost variable is declared.

   A Var parameter gets a new cell, which is a ghost cell. A Ref parameter
   points to the cell of the caller's lvalue, which has to be a ghost cell
   already. *)
lemma process_one_arg_ghost:
  assumes rel: "state_erased envB embK fullK erasedK"
    and g: "tyenv_var_ghost envB (fst p)"
    and refs: "\<forall>addr path. snd p = Ref \<longrightarrow> rF = Inr (addr, path) \<longrightarrow>
                 addr < length (IS_Store fullK) \<and> addr \<notin> set embK"
    and stepF: "process_one_arg (p, rF, vF) (Inr fullK) = Inr mid"
  shows "state_erased envB embK mid erasedK"
    and "length (IS_Store fullK) \<le> length (IS_Store mid)"
proof -
  obtain name vr where p_eq: "p = (name, vr)" by (cases p)
  from g p_eq have gv: "tyenv_var_ghost envB name" by simp
  have both: "state_erased envB embK mid erasedK
              \<and> length (IS_Store fullK) \<le> length (IS_Store mid)"
  proof (cases vr)
    case Var
    show ?thesis
    proof (cases vF)
      case (Inl err)
      with p_eq Var stepF show ?thesis by simp
    next
      case (Inr val)
      from p_eq Var Inr stepF[symmetric]
      have sF: "fresh_binding_step name val fullK mid"
        by (simp add: fresh_binding_step_def static_parts_eq_def Let_def)
      note F = fresh_binding_stepD[OF sF]
      have rel': "state_erased envB embK mid erasedK"
      proof (rule state_erased_bind_ghost_fresh[OF rel gv refl refl F(1) F(2) F(3) F(4) F(5)])
        fix n assume "n \<noteq> name"
        then show "(n |\<in>| IS_ConstLocals mid) = (n |\<in>| IS_ConstLocals fullK)" by (rule F(6))
      qed
      have len': "length (IS_Store fullK) \<le> length (IS_Store mid)" by (simp add: F(3))
      show ?thesis by (rule conjI[OF rel' len'])
    qed
  next
    case Ref
    show ?thesis
    proof (cases rF)
      case (Inl err)
      with p_eq Ref stepF show ?thesis by simp
    next
      case refInr: (Inr addrPath)
      obtain addr path where ap: "addrPath = (addr, path)" by (cases addrPath)
      from refs p_eq Ref refInr ap
      have addr_lt: "addr < length (IS_Store fullK)" and addr_notin: "addr \<notin> set embK"
        by simp_all
      show ?thesis
      proof (cases vF)
        case (Inl err)
        with p_eq Ref refInr ap stepF show ?thesis by simp
      next
        case (Inr val)
        from p_eq Ref refInr ap Inr stepF[symmetric]
        have sF: "ref_binding_step name addr path fullK mid"
          by (simp add: ref_binding_step_def static_parts_eq_def)
        note F = ref_binding_stepD[OF sF]
        have rel': "state_erased envB embK mid erasedK"
        proof (rule state_erased_bind_ghost_ref
                      [OF rel gv refl refl F(1) F(2) F(3) F(4) F(5) addr_lt addr_notin])
          fix n assume "n \<noteq> name"
          then show "(n |\<in>| IS_ConstLocals mid) = (n |\<in>| IS_ConstLocals fullK)"
            by (rule F(6))
        qed
        have len': "length (IS_Store fullK) \<le> length (IS_Store mid)" by (simp add: F(3))
        show ?thesis by (rule conjI[OF rel' len'])
      qed
    qed
  qed
  from both show "state_erased envB embK mid erasedK" by (rule conjunct1)
  from both show "length (IS_Store fullK) \<le> length (IS_Store mid)" by (rule conjunct2)
qed

(* Binding all the arguments. The full state binds every parameter. The erased
   state binds only the parameters that are not ghost, to the arguments that
   erasure keeps.

   The parameters of the function in the state are params, and flags are their
   ghost flags, which come from the signature. The argument terms of the full
   call are tms. lvF and tmF give the lvalue result and the value result of
   an argument in the full state; lvE and tmE give those of the corresponding
   argument of the erased call in the erased state.

   The hypotheses, in order:
    - an argument of a parameter that is not ghost has corresponding results
      in the two states;
    - an lvalue passed to a ghost Ref parameter is a ghost cell of the caller
      (n0 is the length of the caller's store);
    - in the environment of the callee's body, the ghost variables are the
      ghost parameters;
    - the states so far are related, and the cells added to the embedding so
      far are new cells, beyond the caller's store. *)
lemma fold_process_one_arg_erased:
  assumes len: "length params = length flags"
    and vals: "\<forall>tm name vr. (tm, ((name, vr), NotGhost)) \<in> set (zip tms (zip params flags)) \<longrightarrow>
                   (\<forall>v. tmF tm = Inr v \<longrightarrow> tmE tm = Inr v)"
    and refs: "\<forall>tm name vr. (tm, ((name, vr), NotGhost)) \<in> set (zip tms (zip params flags)) \<longrightarrow>
                 (\<forall>addr path. lvF tm = Inr (addr, path) \<longrightarrow>
                    (\<exists>i. lvE tm = Inr (i, path) \<and> i < length emb \<and> emb ! i = addr))"
    and ghost_refs: "\<forall>tm name. (tm, ((name, Ref), Ghost)) \<in> set (zip tms (zip params flags)) \<longrightarrow>
                 (\<forall>addr path. lvF tm = Inr (addr, path) \<longrightarrow> addr < n0 \<and> addr \<notin> set emb)"
    and pg: "\<forall>name vr gh. ((name, vr), gh) \<in> set (zip params flags) \<longrightarrow>
               (tyenv_var_ghost envB name \<longleftrightarrow> gh = Ghost)"
    and rel: "state_erased envB (emb @ extra) fullK erasedK"
    and lo: "n0 \<le> length (IS_Store fullK)"
    and ex: "\<forall>a \<in> set extra. n0 \<le> a"
    and foldF: "fold process_one_arg (zip params (zip (map lvF tms) (map tmF tms))) (Inr fullK)
                  = Inr fullN"
  shows "\<exists>erasedN extraN.
           fold process_one_arg
                (zip (drop_ghost flags params)
                     (zip (map lvE (drop_ghost flags tms)) (map tmE (drop_ghost flags tms))))
                (Inr erasedK)
             = Inr erasedN \<and>
           state_erased envB (emb @ extraN) fullN erasedN"
  using assms
proof (induction params flags arbitrary: tms extra fullK erasedK rule: list_induct2)
  case Nil
  from Nil.prems(8) have "fullN = fullK" by simp
  with Nil.prems(5) show ?case by auto
next
  case (Cons p ps gh ghs)
  note vals = Cons.prems(1) and refs = Cons.prems(2) and ghost_refs = Cons.prems(3)
    and pg = Cons.prems(4) and rel = Cons.prems(5) and lo = Cons.prems(6)
    and ex = Cons.prems(7) and foldF = Cons.prems(8)
  note IH = Cons.IH
  show ?case
  proof (cases tms)
    case Nil
    from foldF Nil have "fullN = fullK" by simp
    with rel Nil show ?thesis by auto
  next
    case tms_eq: (Cons tm rest)
    obtain name vr where p_eq: "p = (name, vr)" by (cases p)
    let ?restF = "zip ps (zip (map lvF rest) (map tmF rest))"
    let ?restE = "zip (drop_ghost ghs ps)
                      (zip (map lvE (drop_ghost ghs rest)) (map tmE (drop_ghost ghs rest)))"
    from foldF tms_eq
    have foldF': "fold process_one_arg ?restF (process_one_arg (p, lvF tm, tmF tm) (Inr fullK))
                    = Inr fullN"
      by simp
    \<comment> \<open>The first argument is bound successfully in the full state. \<close>
    have "\<exists>mid. process_one_arg (p, lvF tm, tmF tm) (Inr fullK) = Inr mid"
    proof (cases "process_one_arg (p, lvF tm, tmF tm) (Inr fullK)")
      case (Inl err)
      with foldF' show ?thesis by (simp add: fold_process_one_arg_error)
    next
      case (Inr mid)
      then show ?thesis by blast
    qed
    then obtain mid where stepF: "process_one_arg (p, lvF tm, tmF tm) (Inr fullK) = Inr mid"
      by blast
    from foldF' stepF have restF: "fold process_one_arg ?restF (Inr mid) = Inr fullN"
      by simp
    \<comment> \<open>The hypotheses, for the remaining arguments. \<close>
    from vals tms_eq
    have vals': "\<forall>tm' name' vr'. (tm', ((name', vr'), NotGhost)) \<in> set (zip rest (zip ps ghs)) \<longrightarrow>
                   (\<forall>v. tmF tm' = Inr v \<longrightarrow> tmE tm' = Inr v)"
      by auto
    from refs tms_eq
    have refs': "\<forall>tm' name' vr'. (tm', ((name', vr'), NotGhost)) \<in> set (zip rest (zip ps ghs)) \<longrightarrow>
                   (\<forall>addr path. lvF tm' = Inr (addr, path) \<longrightarrow>
                      (\<exists>i. lvE tm' = Inr (i, path) \<and> i < length emb \<and> emb ! i = addr))"
      by auto
    from ghost_refs tms_eq
    have ghost_refs': "\<forall>tm' name'. (tm', ((name', Ref), Ghost)) \<in> set (zip rest (zip ps ghs)) \<longrightarrow>
                   (\<forall>addr path. lvF tm' = Inr (addr, path) \<longrightarrow> addr < n0 \<and> addr \<notin> set emb)"
      by auto
    from pg
    have pg': "\<forall>name' vr' gh'. ((name', vr'), gh') \<in> set (zip ps ghs) \<longrightarrow>
                 (tyenv_var_ghost envB name' \<longleftrightarrow> gh' = Ghost)"
      by auto
    from pg[rule_format, of name vr gh] p_eq
    have g_iff: "tyenv_var_ghost envB name \<longleftrightarrow> gh = Ghost" by simp
    show ?thesis
    proof (cases gh)
      case NotGhost
      \<comment> \<open>A parameter that is not ghost: both states bind it. \<close>
      from g_iff NotGhost p_eq have ng: "\<not> tyenv_var_ghost envB (fst p)" by simp
      have mem: "(tm, ((name, vr), NotGhost)) \<in> set (zip tms (zip (p # ps) (gh # ghs)))"
        using tms_eq p_eq NotGhost by simp
      from vals mem have v1: "\<forall>v. tmF tm = Inr v \<longrightarrow> tmE tm = Inr v" by blast
      from refs mem
      have r1: "\<forall>addr path. lvF tm = Inr (addr, path) \<longrightarrow>
                  (\<exists>i. lvE tm = Inr (i, path) \<and> i < length emb \<and> emb ! i = addr)"
        by blast
      from process_one_arg_erased[OF rel ng v1 r1 stepF]
      obtain midE extraM where
        stepE: "process_one_arg (p, lvE tm, tmE tm) (Inr erasedK) = Inr midE" and
        relM: "state_erased envB (emb @ extraM) mid midE" and
        lenM: "length (IS_Store fullK) \<le> length (IS_Store mid)" and
        exM: "extraM = extra \<or> extraM = extra @ [length (IS_Store fullK)]"
        by blast
      from lo lenM have lo': "n0 \<le> length (IS_Store mid)" by simp
      from ex exM lo have ex': "\<forall>a \<in> set extraM. n0 \<le> a" by auto
      from IH[OF vals' refs' ghost_refs' pg' relM lo' ex' restF]
      obtain erasedN extraN where
        restE: "fold process_one_arg ?restE (Inr midE) = Inr erasedN" and
        relN: "state_erased envB (emb @ extraN) fullN erasedN"
        by blast
      from restE stepE tms_eq p_eq NotGhost
      have "fold process_one_arg
              (zip (drop_ghost (gh # ghs) (p # ps))
                   (zip (map lvE (drop_ghost (gh # ghs) tms))
                        (map tmE (drop_ghost (gh # ghs) tms))))
              (Inr erasedK)
            = Inr erasedN"
        by simp
      with relN show ?thesis by blast
    next
      case Ghost
      \<comment> \<open>A ghost parameter: only the full state binds it, in a ghost cell. \<close>
      from g_iff Ghost p_eq have g: "tyenv_var_ghost envB (fst p)" by simp
      have refsG: "\<forall>addr path. snd p = Ref \<longrightarrow> lvF tm = Inr (addr, path) \<longrightarrow>
                     addr < length (IS_Store fullK) \<and> addr \<notin> set (emb @ extra)"
      proof (intro allI impI)
        fix addr path
        assume r: "snd p = Ref" and lv: "lvF tm = Inr (addr, path)"
        from r p_eq have vr_eq: "vr = Ref" by simp
        have mem: "(tm, ((name, Ref), Ghost)) \<in> set (zip tms (zip (p # ps) (gh # ghs)))"
          using tms_eq p_eq Ghost vr_eq by simp
        from ghost_refs mem lv have a: "addr < n0" and b: "addr \<notin> set emb" by blast+
        from a lo have c: "addr < length (IS_Store fullK)" by simp
        have d: "addr \<notin> set extra"
        proof
          assume "addr \<in> set extra"
          with ex have "n0 \<le> addr" by blast
          with a show False by simp
        qed
        from b c d show "addr < length (IS_Store fullK) \<and> addr \<notin> set (emb @ extra)" by simp
      qed
      note G = process_one_arg_ghost[OF rel g refsG stepF]
      from lo G(2) have lo': "n0 \<le> length (IS_Store mid)" by simp
      from IH[OF vals' refs' ghost_refs' pg' G(1) lo' ex restF]
      obtain erasedN extraN where
        restE: "fold process_one_arg ?restE (Inr erasedK) = Inr erasedN" and
        relN: "state_erased envB (emb @ extraN) fullN erasedN"
        by blast
      from restE tms_eq p_eq Ghost
      have "fold process_one_arg
              (zip (drop_ghost (gh # ghs) (p # ps))
                   (zip (map lvE (drop_ghost (gh # ghs) tms))
                        (map tmE (drop_ghost (gh # ghs) tms))))
              (Inr erasedK)
            = Inr erasedN"
        by simp
      with relN show ?thesis by blast
    qed
  qed
qed


(* ========================================================================== *)
(* Calls: the ref updates of an extern function *)
(* ========================================================================== *)

(* The lvalues that an extern function may update, in the two states, are at
   corresponding addresses with the same paths, provided that this holds for
   every argument term in a Ref position. *)
lemma extern_refs_erased:
  assumes "\<forall>tm name vr. (tm, (name, vr)) \<in> set (zip tms params) \<longrightarrow> vr = Ref \<longrightarrow>
             (\<exists>addr path i. lvF tm = Inr (addr, path) \<and> lvE tm = Inr (i, path) \<and>
                            i < length emb \<and> emb ! i = addr)"
  shows "list_all2 (\<lambda>(addr, path) (i, path'). i < length emb \<and> emb ! i = addr \<and> path' = path)
           (rights (map (\<lambda>((_, vr), refResult). if vr = Ref then refResult else Inl TypeError)
                        (zip params (map lvF tms))))
           (rights (map (\<lambda>((_, vr), refResult). if vr = Ref then refResult else Inl TypeError)
                        (zip params (map lvE tms))))"
  using assms
proof (induction params arbitrary: tms)
  case Nil
  show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases tms)
    case Nil
    then show ?thesis by simp
  next
    case tms_eq: (Cons tm rest)
    obtain name vr where p_eq: "p = (name, vr)" by (cases p)
    from Cons.prems tms_eq
    have rest_ok:
      "\<forall>tm' name' vr'. (tm', (name', vr')) \<in> set (zip rest ps) \<longrightarrow> vr' = Ref \<longrightarrow>
         (\<exists>addr path i. lvF tm' = Inr (addr, path) \<and> lvE tm' = Inr (i, path) \<and>
                        i < length emb \<and> emb ! i = addr)"
      by auto
    note tail = Cons.IH[OF rest_ok]
    show ?thesis
    proof (cases vr)
      case Var
      with tail p_eq tms_eq show ?thesis by simp
    next
      case Ref
      have mem: "(tm, (name, Ref)) \<in> set (zip tms (p # ps))"
        using tms_eq p_eq Ref by simp
      from Cons.prems[rule_format, OF mem refl] obtain addr path i where
        "lvF tm = Inr (addr, path)" and "lvE tm = Inr (i, path)" and
        "i < length emb" and "emb ! i = addr"
        by blast
      with tail p_eq tms_eq Ref show ?thesis by simp
    qed
  qed
qed

(* Applying the same updates to lvalues at corresponding addresses. *)
lemma apply_ref_updates_erased:
  assumes "list_all2 (\<lambda>(addr, path) (i, path'). i < length emb \<and> emb ! i = addr \<and> path' = path)
                     lvsF lvsE"
    and "state_erased env emb full erased"
    and "apply_ref_updates full lvsF vals = Inr full'"
  shows "\<exists>erased'. apply_ref_updates erased lvsE vals = Inr erased'
                   \<and> state_erased env emb full' erased'"
  using assms
proof (induction lvsF lvsE arbitrary: full erased vals rule: list_all2_induct)
  case Nil
  from Nil.prems(2) have "vals = [] \<and> full' = full" by (cases vals) simp_all
  with Nil.prems(1) show ?case by auto
next
  case (Cons lvF lvsF lvE lvsE)
  obtain addr path where lvF_eq: "lvF = (addr, path)" by (cases lvF)
  obtain i path' where lvE_eq: "lvE = (i, path')" by (cases lvE)
  from Cons.hyps(1) lvF_eq lvE_eq
  have i_lt: "i < length emb" and addr_eq: "emb ! i = addr" and p_eq: "path' = path"
    by simp_all
  from Cons.prems(2) obtain v vs where vals_eq: "vals = v # vs"
    by (cases vals) (simp_all add: lvF_eq)
  from Cons.prems(2) obtain updated where
    upd: "update_value_at_path (IS_Store full ! addr) path v = Inr updated" and
    restF: "apply_ref_updates (full \<lparr> IS_Store := (IS_Store full)[addr := updated] \<rparr>) lvsF vs
              = Inr full'"
    unfolding lvF_eq vals_eq by (auto simp: Let_def split: sum.splits)
  let ?fullM = "full \<lparr> IS_Store := (IS_Store full)[addr := updated] \<rparr>"
  let ?erasedM = "erased \<lparr> IS_Store := (IS_Store erased)[i := updated] \<rparr>"
  have cell: "IS_Store erased ! i = IS_Store full ! addr"
    by (rule erased_cell[OF Cons.prems(1) i_lt addr_eq])
  have relM: "state_erased env emb ?fullM ?erasedM"
    by (rule state_erased_write_both[where v = updated, OF Cons.prems(1) i_lt addr_eq])
       (simp_all add: store_write_step_def static_parts_eq_def)
  from Cons.IH[OF relM restF] obtain erased' where
    restE: "apply_ref_updates ?erasedM lvsE vs = Inr erased'" and
    rel': "state_erased env emb full' erased'"
    by blast
  have "apply_ref_updates erased (lvE # lvsE) vals = Inr erased'"
    using restE upd by (simp add: lvE_eq p_eq vals_eq cell Let_def)
  with rel' show ?case by blast
qed


(* ========================================================================== *)
(* Terms: Let, Match and Default *)
(* ========================================================================== *)

(* The defining equation of interp_term for a Let, with the binding of the
   variable kept folded (as bind_const_local). *)
lemma interp_term_Let:
  "interp_term d (Suc fuel) state (CoreTm_Let varName rhsTm bodyTm) =
    (case interp_term d fuel state rhsTm of
       Inl err \<Rightarrow> Inl err
     | Inr rhsVal \<Rightarrow> interp_term d fuel (bind_const_local varName rhsVal state) bodyTm)"
  by (simp del: bind_const_local.simps)

lemma bind_const_local_step:
  "fresh_binding_step varName val state (bind_const_local varName val state)"
  "varName |\<in>| IS_ConstLocals (bind_const_local varName val state)"
  by (simp_all add: fresh_binding_step_def static_parts_eq_def Let_def)

(* Erasing the arm bodies of a Match does not change which arm is chosen. *)
lemma find_matching_arm_map:
  assumes "find_matching_arm v arms = Inr rhs"
  shows "find_matching_arm v (map (\<lambda>(pat, body). (pat, f body)) arms) = Inr (f rhs)"
  using assms
  by (induction v arms rule: find_matching_arm.induct) (auto split: if_splits)

(* default_value looks at the state only through IS_DataCtorsByType and
   IS_DataCtors. *)
lemma default_value_cong_state:
  fixes s1 s2 :: "'w InterpState"
  assumes eq: "IS_DataCtorsByType s2 = IS_DataCtorsByType s1"
    and eq2: "IS_DataCtors s2 = IS_DataCtors s1"
  shows "\<forall>ty. default_value fuel s2 ty = default_value fuel s1 ty"
    and "\<forall>tys. default_value_list fuel s2 tys = default_value_list fuel s1 tys"
proof (induction fuel rule: nat.induct)
  case zero
  {
    case 1 show ?case by simp
  next
    case 2 show ?case by simp
  }
next
  case (Suc fuel)
  note IH1 = Suc.IH(1)[rule_format]
  note IH2 = Suc.IH(2)[rule_format]
  {
    case 1 show ?case
    proof (intro allI)
      fix ty
      show "default_value (Suc fuel) s2 ty = default_value (Suc fuel) s1 ty"
        by (cases ty)
           (auto simp: IH1 IH2 eq eq2 Let_def
                 split: option.splits list.splits prod.splits sum.splits)
    qed
  next
    case 2 show ?case
    proof (intro allI)
      fix tys
      show "default_value_list (Suc fuel) s2 tys = default_value_list (Suc fuel) s1 tys"
        by (cases tys) (auto simp: IH1 IH2 split: sum.splits)
    qed
  }
qed


(* ========================================================================== *)
(* What erase_ghost_statement gives *)
(* ========================================================================== *)

(* A statement erases to nothing or to one statement. *)
lemma erase_ghost_statement_shape:
  "erase_ghost_statement funInfos stmt = []
     \<or> (\<exists>stmt'. erase_ghost_statement funInfos stmt = [stmt'])"
proof (cases stmt)
  case (CoreStmt_VarDecl g varName vr varTy initTm)
  then show ?thesis by (cases g) simp_all
next
  case (CoreStmt_VarDeclCall g varName varTy castOpt fnName tyArgs argTms)
  then show ?thesis by (cases g) simp_all
next
  case (CoreStmt_Assign g lhsTm rhsTm)
  then show ?thesis by (cases g) simp_all
next
  case (CoreStmt_AssignCall g lhsTm castOpt fnName tyArgs argTms)
  then show ?thesis by (cases g) simp_all
next
  case (CoreStmt_Swap g lhsTm rhsTm)
  then show ?thesis by (cases g) simp_all
next
  case (CoreStmt_While g condTm invars decrTm body)
  then show ?thesis by (cases g) simp_all
next
  case (CoreStmt_Match g scrut arms)
  then show ?thesis by (cases g) simp_all
qed simp_all


(* ========================================================================== *)
(* Terms in executable position *)
(* ========================================================================== *)

(* A term is in executable position if it is well-typed in NotGhost mode. The
   simulation proof does not use the type, only that there is one: it is what
   says that the term reads no ghost variable and calls no ghost function.

   The lemmas below say, for each form of term, that its subterms are in
   executable position too. *)
definition notghost_typed :: "CoreTyEnv \<Rightarrow> CoreTerm \<Rightarrow> bool" where
  "notghost_typed env tm \<equiv> core_term_type env NotGhost tm \<noteq> None"

lemma notghost_typedI:
  assumes "core_term_type env NotGhost tm = Some ty"
  shows "notghost_typed env tm"
  using assms by (simp add: notghost_typed_def)

(* Quantifiers, `allocated` and `old` are ghost only. *)
lemma notghost_typed_ghost_only [simp]:
  "\<not> notghost_typed env (CoreTm_Quantifier q var varTy body)"
  "\<not> notghost_typed env (CoreTm_Allocated tm)"
  "\<not> notghost_typed env (CoreTm_Old tm)"
  by (simp_all add: notghost_typed_def)

lemma notghost_typed_Var:
  assumes "notghost_typed env (CoreTm_Var name)"
  shows "\<not> tyenv_var_ghost env name"
  using assms by (auto simp: notghost_typed_def split: option.splits if_splits)

lemma notghost_typed_LitArray:
  assumes "notghost_typed env (CoreTm_LitArray elemTy tms)"
  shows "list_all (notghost_typed env) tms"
  using assms by (auto simp: notghost_typed_def list_all_iff split: if_splits)

lemma notghost_typed_Cast:
  assumes "notghost_typed env (CoreTm_Cast targetTy operand)"
  shows "notghost_typed env operand"
  using assms
  by (cases "core_term_type env NotGhost operand") (simp_all add: notghost_typed_def)

lemma notghost_typed_Unop:
  assumes "notghost_typed env (CoreTm_Unop op operand)"
  shows "notghost_typed env operand"
  using assms
  by (cases "core_term_type env NotGhost operand") (simp_all add: notghost_typed_def)

lemma notghost_typed_Binop:
  assumes "notghost_typed env (CoreTm_Binop op lhs rhs)"
  shows "notghost_typed env lhs" and "notghost_typed env rhs"
proof -
  show "notghost_typed env lhs"
    using assms
    by (cases "core_term_type env NotGhost lhs") (simp_all add: notghost_typed_def)
  show "notghost_typed env rhs"
    using assms
    by (cases "core_term_type env NotGhost lhs"; cases "core_term_type env NotGhost rhs")
       (simp_all add: notghost_typed_def)
qed

(* The body of a Let is typed in the environment in which the new variable is
   a local that is not ghost. *)
lemma notghost_typed_Let:
  assumes "notghost_typed env (CoreTm_Let var rhs body)"
  shows "\<exists>rhsTy. core_term_type env NotGhost rhs = Some rhsTy \<and>
           notghost_typed
             (env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                    TE_GhostLocals := fminus (TE_GhostLocals env) {|var|},
                    TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>)
             body"
  using assms
  by (cases "core_term_type env NotGhost rhs") (simp_all add: notghost_typed_def Let_def)

(* What the simulation needs to know about the arguments of a call in
   executable code, given the signature of the function called.

   The argument of a parameter that is not ghost is in executable position.
   The argument of a ghost parameter is typed in Ghost mode, and erasure drops
   it; nothing is said about it, except that if the parameter is a Ref, the
   argument is an lvalue whose base variable is ghost. *)
definition call_args_notghost :: "CoreTyEnv \<Rightarrow> FunInfo \<Rightarrow> CoreTerm list \<Rightarrow> bool" where
  "call_args_notghost env info tmArgs \<equiv>
    list_all2 (\<lambda>tm (_, vr, gh).
                 (gh = NotGhost \<longrightarrow> notghost_typed env tm) \<and>
                 (gh = Ghost \<longrightarrow> vr = Ref \<longrightarrow> ghost_lvalue_ok env Ghost tm))
              tmArgs (FI_TmArgs info)"

lemma call_args_notghost_length:
  assumes "call_args_notghost env info tmArgs"
  shows "length tmArgs = length (FI_TmArgs info)"
  using assms unfolding call_args_notghost_def by (rule list_all2_lengthD)

(* The same facts for one argument, found by its position in the parameter
   list of the function in the state (params), whose Var/Ref flags are those
   of the signature, paired with the ghost flags of the signature. *)
lemma call_args_notghostD:
  assumes args: "call_args_notghost env info tmArgs"
    and flags: "map snd params = map (fst \<circ> snd) (FI_TmArgs info)"
    and mem: "(tm, ((name, vr), gh)) \<in> set (zip tmArgs (zip params (param_ghost_flags info)))"
  shows "gh = NotGhost \<Longrightarrow> notghost_typed env tm"
    and "gh = Ghost \<Longrightarrow> vr = Ref \<Longrightarrow> ghost_lvalue_ok env Ghost tm"
proof -
  from mem obtain i where ti: "tmArgs ! i = tm"
    and pi': "params ! i = (name, vr)" and gi: "param_ghost_flags info ! i = gh"
    and i1: "i < length tmArgs" and ip: "i < length params"
    by (auto simp: in_set_zip)
  from flags have len: "length params = length (FI_TmArgs info)"
    by (rule map_eq_imp_length_eq)
  from ip len have i3: "i < length (FI_TmArgs info)" by simp
  have vr_eq: "fst (snd (FI_TmArgs info ! i)) = vr"
  proof -
    have "fst (snd (FI_TmArgs info ! i)) = map (fst \<circ> snd) (FI_TmArgs info) ! i"
      using i3 by simp
    also have "\<dots> = map snd params ! i" by (simp only: flags)
    also have "\<dots> = vr" using ip pi' by simp
    finally show ?thesis .
  qed
  have gh_eq: "snd (snd (FI_TmArgs info ! i)) = gh"
    using gi i3 by (simp add: param_ghost_flags_def case_prod_unfold)
  obtain pty vr' gh' where fi0: "FI_TmArgs info ! i = (pty, vr', gh')"
    by (cases "FI_TmArgs info ! i")
  from fi0 vr_eq gh_eq have fi: "FI_TmArgs info ! i = (pty, vr, gh)" by simp
  from list_all2_nthD[OF args[unfolded call_args_notghost_def] i1]
  have both: "(gh = NotGhost \<longrightarrow> notghost_typed env tm) \<and>
              (gh = Ghost \<longrightarrow> vr = Ref \<longrightarrow> ghost_lvalue_ok env Ghost tm)"
    by (simp add: ti fi)
  from both show "gh = NotGhost \<Longrightarrow> notghost_typed env tm" by simp
  from both show "gh = Ghost \<Longrightarrow> vr = Ref \<Longrightarrow> ghost_lvalue_ok env Ghost tm" by simp
qed

(* A call in executable position is a call of a function that is not ghost,
   and its arguments are as above. (A function called in a term has no Ref
   parameter, so the fact about ghost lvalues holds for the trivial reason.) *)
lemma notghost_typed_FunctionCall:
  assumes "notghost_typed env (CoreTm_FunctionCall fnName tyArgs tmArgs)"
  shows "\<exists>info. fmlookup (TE_Functions env) fnName = Some info \<and>
                FI_Ghost info = NotGhost \<and>
                call_args_notghost env info tmArgs"
proof -
  from assms obtain ty where
    T: "core_term_type env NotGhost (CoreTm_FunctionCall fnName tyArgs tmArgs) = Some ty"
    unfolding notghost_typed_def by (auto simp only: not_None_eq)
  from T obtain info where
    info: "fmlookup (TE_Functions env) fnName = Some info" and
    ng: "FI_Ghost info \<noteq> Ghost" and
    len: "length tmArgs = length (FI_TmArgs info)" and
    all_var: "list_all (\<lambda>(_, vor, _). vor = Var) (FI_TmArgs info)" and
    la2: "list_all2 (\<lambda>tm (expectedTy, mode). core_term_type env mode tm = Some expectedTy) tmArgs
            (zip (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs info) tyArgs)) ty)
                      (FI_TmArgs info))
                 (map (\<lambda>(_, _, gh). param_mode NotGhost gh) (FI_TmArgs info)))"
    by (auto simp: Let_def split: option.splits if_splits)
  from ng have ng': "FI_Ghost info = NotGhost" by (cases "FI_Ghost info") simp_all
  have args: "call_args_notghost env info tmArgs"
    unfolding call_args_notghost_def
  proof (rule list_all2_all_nthI, goal_cases)
    case 1
    show ?case by (rule len)
  next
    case (2 i)
    note i_lt = 2
    from i_lt len have i_lt': "i < length (FI_TmArgs info)" by simp
    obtain pty vr gh where pi: "FI_TmArgs info ! i = (pty, vr, gh)"
      by (cases "FI_TmArgs info ! i")
    from all_var i_lt' have "case FI_TmArgs info ! i of (_, vor, _) \<Rightarrow> vor = Var"
      by (simp add: list_all_length)
    with pi have vr_eq: "vr = Var" by simp
    have ngt: "gh = NotGhost \<longrightarrow> notghost_typed env (tmArgs ! i)"
    proof
      assume g: "gh = NotGhost"
      from list_all2_case_prod_nthD[OF la2 i_lt] i_lt' pi g
      show "notghost_typed env (tmArgs ! i)" by (simp add: notghost_typed_def)
    qed
    show ?case using ngt vr_eq by (simp add: pi)
  qed
  from info ng' args show ?thesis by blast
qed

lemma notghost_typed_VariantCtor:
  assumes "notghost_typed env (CoreTm_VariantCtor ctorName tyArgs payload)"
  shows "notghost_typed env payload"
  using assms
  by (cases "core_term_type env NotGhost payload")
     (auto simp: notghost_typed_def Let_def split: option.splits prod.splits if_splits)

(* If every element of a list of options is defined... *)
lemma those_map_Some_all:
  "those (map f xs) = Some ys \<Longrightarrow> \<forall>x \<in> set xs. f x \<noteq> None"
  by (induction xs arbitrary: ys) (auto split: option.splits)

lemma notghost_typed_Record:
  assumes "notghost_typed env (CoreTm_Record flds)"
  shows "list_all (notghost_typed env) (map snd flds)"
proof -
  obtain tys where
    th: "those (map (\<lambda>(name, tm). core_term_type env NotGhost tm) flds) = Some tys"
  proof (cases "those (map (\<lambda>(name, tm). core_term_type env NotGhost tm) flds)")
    case None
    with assms show ?thesis by (auto simp: notghost_typed_def split: if_splits)
  next
    case (Some tys)
    then show ?thesis by (rule that)
  qed
  from those_map_Some_all[OF th] show ?thesis
    by (auto simp: notghost_typed_def list_all_iff case_prod_beta)
qed

lemma notghost_typed_RecordProj:
  assumes "notghost_typed env (CoreTm_RecordProj tm fldName)"
  shows "notghost_typed env tm"
  using assms
  by (cases "core_term_type env NotGhost tm") (simp_all add: notghost_typed_def)

lemma notghost_typed_VariantProj:
  assumes "notghost_typed env (CoreTm_VariantProj tm ctorName)"
  shows "notghost_typed env tm"
  using assms
  by (cases "core_term_type env NotGhost tm") (simp_all add: notghost_typed_def)

lemma notghost_typed_ArrayProj:
  assumes "notghost_typed env (CoreTm_ArrayProj arr idxTms)"
  shows "notghost_typed env arr" and "list_all (notghost_typed env) idxTms"
proof -
  show "notghost_typed env arr"
    using assms
    by (cases "core_term_type env NotGhost arr") (simp_all add: notghost_typed_def)
  show "list_all (notghost_typed env) idxTms"
    using assms
    by (auto simp: notghost_typed_def list_all_iff
             split: option.splits CoreType.splits if_splits)
qed

lemma notghost_typed_Match:
  assumes "notghost_typed env (CoreTm_Match scrut arms)"
  shows "notghost_typed env scrut"
    and "\<And>armTm. armTm \<in> snd ` set arms \<Longrightarrow> notghost_typed env armTm"
proof -
  show "notghost_typed env scrut"
    using assms
    by (cases "core_term_type env NotGhost scrut") (simp_all add: notghost_typed_def)
next
  fix armTm assume mem: "armTm \<in> snd ` set arms"
  from assms obtain scrutTy where sT: "core_term_type env NotGhost scrut = Some scrutTy"
    by (cases "core_term_type env NotGhost scrut") (simp_all add: notghost_typed_def)
  from mem obtain a rest where arms_eq: "arms = a # rest" by (cases arms) auto
  from assms sT arms_eq obtain resultTy where
    hdT: "core_term_type env NotGhost (snd a) = Some resultTy"
    by (cases "core_term_type env NotGhost (snd a)")
       (auto simp: notghost_typed_def Let_def split: if_splits)
  from assms sT arms_eq hdT
  have tlT: "\<forall>b \<in> set rest. core_term_type env NotGhost (snd b) = Some resultTy"
    by (auto simp: notghost_typed_def Let_def list_all_iff split: if_splits)
  from mem arms_eq hdT tlT show "notghost_typed env armTm"
    by (auto simp: notghost_typed_def)
qed

lemma notghost_typed_Sizeof:
  assumes "notghost_typed env (CoreTm_Sizeof tm)"
  shows "notghost_typed env tm"
  using assms
  by (cases "core_term_type env NotGhost tm") (simp_all add: notghost_typed_def)

(* The base variable of an lvalue in executable position is not ghost. *)
lemma notghost_lvalue_base_not_ghost:
  assumes "lvalue_base_name tm = Some name"
    and "notghost_typed env tm"
  shows "\<not> tyenv_var_ghost env name"
  using assms
proof (induction tm rule: lvalue_base_name.induct)
  case (1 varName)
  from "1.prems"(1) have "varName = name" by simp
  with notghost_typed_Var[OF "1.prems"(2)] show ?case by simp
next
  case (2 tm fldName)
  from "2.prems"(1) have base: "lvalue_base_name tm = Some name" by simp
  from "2.prems"(2) have wg: "notghost_typed env tm" by (rule notghost_typed_RecordProj)
  show ?case by (rule "2.IH"[OF base wg])
next
  case (3 tm ctorName)
  from "3.prems"(1) have base: "lvalue_base_name tm = Some name" by simp
  from "3.prems"(2) have wg: "notghost_typed env tm" by (rule notghost_typed_VariantProj)
  show ?case by (rule "3.IH"[OF base wg])
next
  case (4 tm idxTms)
  from "4.prems"(1) have base: "lvalue_base_name tm = Some name" by simp
  from "4.prems"(2) have wg: "notghost_typed env tm" by (rule notghost_typed_ArrayProj(1))
  show ?case by (rule "4.IH"[OF base wg])
next
  case (5 castTy tm)
  from "5.prems"(1) have arr: "is_array_type castTy"
    and base: "lvalue_base_name tm = Some name"
    by (auto split: if_splits)
  from "5.prems"(2) have wg: "notghost_typed env tm" by (rule notghost_typed_Cast)
  show ?case by (rule "5.IH"[OF arr base wg])
qed simp_all

(* A call in a statement of executable code: as for a call in a term. *)
lemma notghost_impure_call_typed:
  assumes "core_impure_call_type env NotGhost fnName tyArgs tmArgs = Some retTy"
  shows "\<exists>info. fmlookup (TE_Functions env) fnName = Some info \<and>
                FI_Ghost info = NotGhost \<and>
                call_args_notghost env info tmArgs"
proof -
  from core_impure_call_type_fn_facts[OF assms] obtain info where
    info: "fmlookup (TE_Functions env) fnName = Some info" and
    ng: "FI_Ghost info \<noteq> Ghost" and
    len: "length tmArgs = length (FI_TmArgs info)" and
    la2: "list_all2 (\<lambda>tm (expectedTy, mode). core_term_type env mode tm = Some expectedTy) tmArgs
            (zip (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs info) tyArgs)) ty)
                      (FI_TmArgs info))
                 (map (\<lambda>(_, _, gh). param_mode NotGhost gh) (FI_TmArgs info)))" and
    refs: "\<forall>i < length tmArgs.
             fst (snd (FI_TmArgs info ! i)) = Ref
               \<longrightarrow> is_writable_lvalue env (tmArgs ! i)
                   \<and> ghost_lvalue_ok env (param_mode NotGhost (snd (snd (FI_TmArgs info ! i))))
                                      (tmArgs ! i)"
    by blast
  from ng have ng': "FI_Ghost info = NotGhost" by (cases "FI_Ghost info") simp_all
  have args: "call_args_notghost env info tmArgs"
    unfolding call_args_notghost_def
  proof (rule list_all2_all_nthI, goal_cases)
    case 1
    show ?case by (rule len)
  next
    case (2 i)
    note i_lt = 2
    from i_lt len have i_lt': "i < length (FI_TmArgs info)" by simp
    obtain pty vr gh where pi: "FI_TmArgs info ! i = (pty, vr, gh)"
      by (cases "FI_TmArgs info ! i")
    have ngt: "gh = NotGhost \<longrightarrow> notghost_typed env (tmArgs ! i)"
    proof
      assume g: "gh = NotGhost"
      from list_all2_case_prod_nthD[OF la2 i_lt] i_lt' pi g
      show "notghost_typed env (tmArgs ! i)" by (simp add: notghost_typed_def)
    qed
    have glv: "gh = Ghost \<longrightarrow> vr = Ref \<longrightarrow> ghost_lvalue_ok env Ghost (tmArgs ! i)"
    proof (intro impI)
      assume g: "gh = Ghost" and r: "vr = Ref"
      from pi r have is_ref: "fst (snd (FI_TmArgs info ! i)) = Ref" by simp
      from refs[rule_format, OF i_lt is_ref] pi g
      show "ghost_lvalue_ok env Ghost (tmArgs ! i)" by simp
    qed
    show ?case using ngt glv by (simp add: pi)
  qed
  from info ng' args show ?thesis by blast
qed

end
