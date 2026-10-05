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
    and "IS_DefaultCtors erased = IS_DefaultCtors full"
    and "IS_World erased = IS_World full"
    and "funs_erased env full erased"
    and "store_erased emb full erased"
    and "IS_TyArgs erased = IS_TyArgs full"
    and "locals_erased env emb full erased"
    and "ghost_locals_separate env emb full"
  shows "state_erased env emb full erased"
  unfolding state_erased_def heap_erased_def by (intro conjI assms)

lemma state_erasedD:
  assumes "state_erased env emb full erased"
  shows "IS_Globals erased = IS_Globals full"
    and "IS_DefaultCtors erased = IS_DefaultCtors full"
    and "IS_World erased = IS_World full"
    and "funs_erased env full erased"
    and "store_erased emb full erased"
    and "IS_TyArgs erased = IS_TyArgs full"
    and "locals_erased env emb full erased"
    and "ghost_locals_separate env emb full"
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
  have c': "IS_DefaultCtors erased' = IS_DefaultCtors full'" using D(2) stF(4) stE(4) by simp
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

  show ?thesis by (rule state_erasedI[OF g' c' w' f' se' t' l' s'])
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
  have c': "IS_DefaultCtors erased' = IS_DefaultCtors full'" using D(2) stF(4) stE(4) by simp
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

  show ?thesis by (rule state_erasedI[OF g' c' w' f' se' t' l' s'])
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
  have c': "IS_DefaultCtors erased' = IS_DefaultCtors full'" using D(2) stF(4) stE(4) by simp
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

  show ?thesis by (rule state_erasedI[OF g' c' w' f' se' t' l' s'])
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
    show "IS_DefaultCtors ?e = IS_DefaultCtors ?f" using D(2) by simp
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
    and c1: "IS_DefaultCtors erased1 = IS_DefaultCtors full1"
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
    show "IS_DefaultCtors ?rsE = IS_DefaultCtors ?rsF" using c1 by simp
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
  "IF_TyArgs (erase_ghost_interp_fun f) = IF_TyArgs f"
  "IF_Args (erase_ghost_interp_fun f) = IF_Args f"
  "IF_Impure (erase_ghost_interp_fun f) = IF_Impure f"
  "IF_Body (erase_ghost_interp_fun f) = map_sum erase_ghost_statement_list id (IF_Body f)"
  by (simp_all add: erase_ghost_interp_fun_def)

(* A function that is not ghost is, in the erased state, the same function
   with its body erased. *)
lemma funs_erased_lookup:
  assumes "funs_erased env full erased"
    and "fmlookup (TE_Functions env) fnName = Some info"
    and "FI_Ghost info = NotGhost"
    and "fmlookup (IS_Functions full) fnName = Some f"
  shows "fmlookup (IS_Functions erased) fnName = Some (erase_ghost_interp_fun f)"
proof -
  from assms(1,2,3)
  have "fmlookup (IS_Functions erased) fnName
          = map_option erase_ghost_interp_fun (fmlookup (IS_Functions full) fnName)"
    unfolding funs_erased_def by blast
  with assms(4) show ?thesis by simp
qed

lemma is_pure_fun_erased:
  assumes "funs_erased env full erased"
    and "fmlookup (TE_Functions env) fnName = Some info"
    and "FI_Ghost info = NotGhost"
  shows "is_pure_fun erased fnName = is_pure_fun full fnName"
proof (cases "fmlookup (IS_Functions full) fnName")
  case None
  from assms
  have "fmlookup (IS_Functions erased) fnName
          = map_option erase_ghost_interp_fun (fmlookup (IS_Functions full) fnName)"
    unfolding funs_erased_def by blast
  with None show ?thesis by simp
next
  case (Some f)
  from funs_erased_lookup[OF assms Some] Some show ?thesis by simp
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

(* The environment of the body of a function that is not ghost: it belongs to
   a function that is not ghost, and none of its variables are ghost. *)
lemma body_env_for_notghost:
  assumes "FI_Ghost info = NotGhost"
  shows "TE_FunctionGhost (body_env_for env names info) = NotGhost"
    and "\<not> tyenv_var_ghost (body_env_for env names info) name"
  using assms by (simp_all add: body_env_for_def tyenv_var_ghost_def)


(* ========================================================================== *)
(* Calls: binding the arguments *)
(* ========================================================================== *)

(* The states in which the binding of arguments starts: the caller's states
   with empty frames. They are related in the environment of the callee's
   body, in which no variable is ghost. *)
lemma state_erased_call_entry:
  assumes rel: "state_erased env emb full erased"
    and fns: "TE_Functions envB = TE_Functions env"
    and noghost: "\<forall>name. \<not> tyenv_var_ghost envB name"
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
    show "IS_DefaultCtors ?e = IS_DefaultCtors ?f" using D(2) by simp
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
      using noghost by (simp add: ghost_locals_separate_def)
  qed
qed

(* Binding one argument. The value result and the lvalue result of the
   argument in the erased state (vE, rE) correspond to those in the full state
   (vF, rF): the same value, and corresponding addresses under the caller's
   embedding emb.

   A Var parameter gets a new cell in both states, so the embedding grows at
   the end; a Ref parameter points to corresponding cells of the caller. *)
lemma process_one_arg_erased:
  assumes rel: "state_erased envB (emb @ extra) fullK erasedK"
    and noghost: "\<forall>name. \<not> tyenv_var_ghost envB name"
    and vals: "\<forall>v. vF = Inr v \<longrightarrow> vE = Inr v"
    and refs: "\<forall>addr path. rF = Inr (addr, path) \<longrightarrow>
                 (\<exists>i. rE = Inr (i, path) \<and> i < length emb \<and> emb ! i = addr)"
    and stepF: "process_one_arg (p, rF, vF) (Inr fullK) = Inr mid"
  shows "\<exists>midE extraM. process_one_arg (p, rE, vE) (Inr erasedK) = Inr midE \<and>
                         state_erased envB (emb @ extraM) mid midE"
proof -
  obtain name vr gh where p_eq: "p = (name, vr, gh)" by (cases p)
  from noghost have ng: "\<not> tyenv_var_ghost envB name" by simp
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
      from stepE rel' show ?thesis by blast
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
        from stepE rel' show ?thesis by blast
      qed
    qed
  qed
qed

(* Binding all the arguments. The argument terms are tms; lvF and tmF give the
   lvalue result and the value result of a term in the full state, lvE and tmE
   in the erased state. *)
lemma fold_process_one_arg_erased:
  assumes vals: "\<forall>tm \<in> set tms. \<forall>v. tmF tm = Inr v \<longrightarrow> tmE tm = Inr v"
    and refs: "\<forall>tm \<in> set tms. \<forall>addr path. lvF tm = Inr (addr, path) \<longrightarrow>
                 (\<exists>i. lvE tm = Inr (i, path) \<and> i < length emb \<and> emb ! i = addr)"
    and noghost: "\<forall>name. \<not> tyenv_var_ghost envB name"
    and rel: "state_erased envB (emb @ extra) fullK erasedK"
    and foldF: "fold process_one_arg (zip params (zip (map lvF tms) (map tmF tms))) (Inr fullK)
                  = Inr fullN"
  shows "\<exists>erasedN extraN.
           fold process_one_arg (zip params (zip (map lvE tms) (map tmE tms))) (Inr erasedK)
             = Inr erasedN \<and>
           state_erased envB (emb @ extraN) fullN erasedN"
  using assms
proof (induction params arbitrary: tms extra fullK erasedK)
  case Nil
  from Nil.prems(5) have "fullN = fullK" by simp
  with Nil.prems(4) show ?case by auto
next
  case (Cons p ps)
  show ?case
  proof (cases tms)
    case Nil
    from Cons.prems(5) Nil have "fullN = fullK" by simp
    with Cons.prems(4) Nil show ?thesis by auto
  next
    case tms_eq: (Cons tm rest)
    let ?restF = "zip ps (zip (map lvF rest) (map tmF rest))"
    let ?restE = "zip ps (zip (map lvE rest) (map tmE rest))"
    from Cons.prems(5) tms_eq
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
    from Cons.prems(1) tms_eq
    have v1: "\<forall>v. tmF tm = Inr v \<longrightarrow> tmE tm = Inr v"
      and vals': "\<forall>tm' \<in> set rest. \<forall>v. tmF tm' = Inr v \<longrightarrow> tmE tm' = Inr v"
      by auto
    from Cons.prems(2) tms_eq
    have r1: "\<forall>addr path. lvF tm = Inr (addr, path) \<longrightarrow>
                (\<exists>i. lvE tm = Inr (i, path) \<and> i < length emb \<and> emb ! i = addr)"
      and refs': "\<forall>tm' \<in> set rest. \<forall>addr path. lvF tm' = Inr (addr, path) \<longrightarrow>
                    (\<exists>i. lvE tm' = Inr (i, path) \<and> i < length emb \<and> emb ! i = addr)"
      by auto
    \<comment> \<open>So it is in the erased state. \<close>
    from process_one_arg_erased[OF Cons.prems(4) Cons.prems(3) v1 r1 stepF]
    obtain midE extraM where
      stepE: "process_one_arg (p, lvE tm, tmE tm) (Inr erasedK) = Inr midE" and
      relM: "state_erased envB (emb @ extraM) mid midE"
      by blast
    \<comment> \<open>Then the rest. \<close>
    from foldF' stepF have restF: "fold process_one_arg ?restF (Inr mid) = Inr fullN"
      by simp
    from Cons.IH[OF vals' refs' Cons.prems(3) relM restF]
    obtain erasedN extraN where
      restE: "fold process_one_arg ?restE (Inr midE) = Inr erasedN" and
      relN: "state_erased envB (emb @ extraN) fullN erasedN"
      by blast
    from restE stepE tms_eq
    have "fold process_one_arg (zip (p # ps) (zip (map lvE tms) (map tmE tms))) (Inr erasedK)
            = Inr erasedN"
      by simp
    with relN show ?thesis by blast
  qed
qed


(* ========================================================================== *)
(* Calls: the ref updates of an extern function *)
(* ========================================================================== *)

(* The lvalues that an extern function may update, in the two states, are at
   corresponding addresses with the same paths, provided that this holds for
   every argument term in a Ref position. *)
lemma extern_refs_erased:
  assumes "\<forall>tm name vr gh. (tm, (name, vr, gh)) \<in> set (zip tms params) \<longrightarrow> vr = Ref \<longrightarrow>
             (\<exists>addr path i. lvF tm = Inr (addr, path) \<and> lvE tm = Inr (i, path) \<and>
                            i < length emb \<and> emb ! i = addr)"
  shows "list_all2 (\<lambda>(addr, path) (i, path'). i < length emb \<and> emb ! i = addr \<and> path' = path)
           (rights (map (\<lambda>((_, vr, _), refResult). if vr = Ref then refResult else Inl TypeError)
                        (zip params (map lvF tms))))
           (rights (map (\<lambda>((_, vr, _), refResult). if vr = Ref then refResult else Inl TypeError)
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
    obtain name vr gh where p_eq: "p = (name, vr, gh)" by (cases p)
    from Cons.prems tms_eq
    have rest_ok:
      "\<forall>tm' name' vr' gh'. (tm', (name', vr', gh')) \<in> set (zip rest ps) \<longrightarrow> vr' = Ref \<longrightarrow>
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
      have mem: "(tm, (name, Ref, gh)) \<in> set (zip tms (p # ps))"
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

(* The state in which the body of a Let is evaluated. *)
definition bind_let_var :: "string \<Rightarrow> CoreValue \<Rightarrow> 'w InterpState \<Rightarrow> 'w InterpState" where
  "bind_let_var varName val state =
    (let (state', addr) = alloc_store state val
     in state' \<lparr> IS_Locals := fmupd varName addr (IS_Locals state'),
                 IS_Refs := fmdrop varName (IS_Refs state'),
                 IS_ConstLocals := finsert varName (IS_ConstLocals state') \<rparr>)"

lemma interp_term_Let:
  "interp_term d (Suc fuel) state (CoreTm_Let varName rhsTm bodyTm) =
    (case interp_term d fuel state rhsTm of
       Inl err \<Rightarrow> Inl err
     | Inr rhsVal \<Rightarrow> interp_term d fuel (bind_let_var varName rhsVal state) bodyTm)"
  by (cases "interp_term d fuel state rhsTm") (simp_all add: bind_let_var_def Let_def)

lemma bind_let_var_step:
  "fresh_binding_step varName val state (bind_let_var varName val state)"
  "varName |\<in>| IS_ConstLocals (bind_let_var varName val state)"
  by (simp_all add: bind_let_var_def fresh_binding_step_def static_parts_eq_def Let_def)

(* Erasing the arm bodies of a Match does not change which arm is chosen. *)
lemma find_matching_arm_map:
  assumes "find_matching_arm v arms = Inr rhs"
  shows "find_matching_arm v (map (\<lambda>(pat, body). (pat, f body)) arms) = Inr (f rhs)"
  using assms
  by (induction v arms rule: find_matching_arm.induct) (auto split: if_splits)

(* default_value looks at the state only through IS_DefaultCtors. *)
lemma default_value_cong_state:
  fixes s1 s2 :: "'w InterpState"
  assumes eq: "IS_DefaultCtors s2 = IS_DefaultCtors s1"
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
           (auto simp: IH1 IH2 eq Let_def split: option.splits prod.splits sum.splits)
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
  "erase_ghost_statement stmt = [] \<or> (\<exists>stmt'. erase_ghost_statement stmt = [stmt'])"
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

(* A call in executable position is a call of a function that is not ghost,
   and its arguments are in executable position. *)
lemma notghost_typed_FunctionCall:
  assumes "notghost_typed env (CoreTm_FunctionCall fnName tyArgs tmArgs)"
  shows "\<exists>info. fmlookup (TE_Functions env) fnName = Some info \<and>
                FI_Ghost info = NotGhost \<and>
                list_all (notghost_typed env) tmArgs"
proof -
  from assms obtain info where info: "fmlookup (TE_Functions env) fnName = Some info"
    by (cases "fmlookup (TE_Functions env) fnName") (simp_all add: notghost_typed_def)
  have ng: "FI_Ghost info = NotGhost"
  proof (rule ccontr)
    assume "FI_Ghost info \<noteq> NotGhost"
    then have "FI_Ghost info = Ghost" by (cases "FI_Ghost info") simp_all
    with assms info show False by (auto simp: notghost_typed_def split: if_splits)
  qed
  let ?expected = "map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs info) tyArgs)) ty)
                       (FI_TmArgs info)"
  have la: "list_all2 (\<lambda>tm expectedTy.
                case core_term_type env NotGhost tm of
                  None \<Rightarrow> False
                | Some actualTy \<Rightarrow> actualTy = expectedTy)
              tmArgs ?expected"
  proof (rule ccontr)
    assume "\<not> list_all2 (\<lambda>tm expectedTy.
                case core_term_type env NotGhost tm of
                  None \<Rightarrow> False
                | Some actualTy \<Rightarrow> actualTy = expectedTy)
              tmArgs ?expected"
    with assms info show False by (auto simp: notghost_typed_def Let_def split: if_splits)
  qed
  have args: "list_all (notghost_typed env) tmArgs"
    using la
    by (fastforce simp: notghost_typed_def list_all_length list_all2_conv_all_nth
                  split: option.splits)
  from info ng args show ?thesis by blast
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
                list_all (notghost_typed env) tmArgs"
proof -
  from core_impure_call_type_fn_facts[OF assms] obtain info where
    info: "fmlookup (TE_Functions env) fnName = Some info" and
    ng: "FI_Ghost info \<noteq> Ghost"
    by blast
  from ng have ng': "FI_Ghost info = NotGhost" by (cases "FI_Ghost info") simp_all
  from core_impure_call_type_args_typed[OF assms]
  have args: "list_all (\<lambda>tm. \<exists>t. core_term_type env NotGhost tm = Some t) tmArgs"
    by blast
  from args have args': "list_all (notghost_typed env) tmArgs"
    by (auto simp: notghost_typed_def list_all_iff)
  from info ng' args' show ?thesis by blast
qed

end
