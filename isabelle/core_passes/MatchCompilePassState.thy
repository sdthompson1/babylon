theory MatchCompilePassState
  imports MatchCompilePassTyping MatchCompileSemantics
    "../ghost_erasure/ErasedSteps" "../interpreter/TypeSoundness" "../interpreter/CoreInterpFuelMono"
    "../core/TypeSubstHelpers"
begin

(* The semantics of the match compilation pass: the state relation and the
   bridge between the match compiler's own semantics (match_tree_eval,
   arms_first_match in MatchCompileSemantics.thy) and the interpreter.

   The pass only rewrites function bodies, so the state of a run of the
   compiled program is the state of the run of the original program with the
   bodies in its function table compiled (mc_state). Nothing else differs:
   the same addresses, the same values. This file proves that every
   operation of the interpreter other than a function call commutes with
   mc_state.

   The compiled program needs more fuel than the original (because it nests
   one CoreTm_Match / CoreStmt_Match per test of the tree, where the original
   had a single match); the simulation theorem (MatchCompilePassSimulation.thy)
   therefore quantifies the fuel of the compiled run existentially. This file
   provides the lemmas about fuel that the simulation needs: monotonicity (from
   CoreInterpFuelMono.thy) gives one fuel that works for a finite number of
   sub-evaluations. *)


section \<open>The compiled state\<close>

(* Compile the body of a function of the interpreter's function table. *)
definition mc_interp_fun :: "'w InterpFun \<Rightarrow> 'w InterpFun" where
  "mc_interp_fun f = f \<lparr> IF_Body := map_sum match_compile_statement_list id (IF_Body f) \<rparr>"

lemma mc_interp_fun_simps [simp]:
  "IF_TyArgs (mc_interp_fun f) = IF_TyArgs f"
  "IF_Args (mc_interp_fun f) = IF_Args f"
  "IF_Body (mc_interp_fun f) = map_sum match_compile_statement_list id (IF_Body f)"
  "IF_Impure (mc_interp_fun f) = IF_Impure f"
  "IF_Ghost (mc_interp_fun f) = IF_Ghost f"
  "IF_ReturnType (mc_interp_fun f) = IF_ReturnType f"
  "IF_Requires (mc_interp_fun f) = IF_Requires f"
  "IF_Ensures (mc_interp_fun f) = IF_Ensures f"
  by (simp_all add: mc_interp_fun_def)

(* The state of the compiled run: the same state with the function bodies
   compiled. *)
definition mc_state :: "'w InterpState \<Rightarrow> 'w InterpState" where
  "mc_state s = s \<lparr> IS_Functions := fmmap mc_interp_fun (IS_Functions s) \<rparr>"

lemma mc_state_simps [simp]:
  "IS_Globals (mc_state s) = IS_Globals s"
  "IS_Locals (mc_state s) = IS_Locals s"
  "IS_Refs (mc_state s) = IS_Refs s"
  "IS_Store (mc_state s) = IS_Store s"
  "IS_ConstLocals (mc_state s) = IS_ConstLocals s"
  "IS_TyArgs (mc_state s) = IS_TyArgs s"
  "IS_Datatypes (mc_state s) = IS_Datatypes s"
  "IS_DataCtors (mc_state s) = IS_DataCtors s"
  "IS_DataCtorsByType (mc_state s) = IS_DataCtorsByType s"
  "IS_Functions (mc_state s) = fmmap mc_interp_fun (IS_Functions s)"
  "IS_World (mc_state s) = IS_World s"
  "IS_ExternAlloc (mc_state s) = IS_ExternAlloc s"
  by (simp_all add: mc_state_def)

lemma mc_state_fun_lookup:
  "fmlookup (IS_Functions (mc_state s)) name = map_option mc_interp_fun (fmlookup (IS_Functions s) name)"
  by simp

(* Updates of the other fields commute with mc_state. *)
lemma mc_state_update_simps [simp]:
  "mc_state (s \<lparr> IS_Store := st \<rparr>) = (mc_state s) \<lparr> IS_Store := st \<rparr>"
  "mc_state (s \<lparr> IS_Locals := l \<rparr>) = (mc_state s) \<lparr> IS_Locals := l \<rparr>"
  "mc_state (s \<lparr> IS_Refs := r \<rparr>) = (mc_state s) \<lparr> IS_Refs := r \<rparr>"
  "mc_state (s \<lparr> IS_ConstLocals := c \<rparr>) = (mc_state s) \<lparr> IS_ConstLocals := c \<rparr>"
  "mc_state (s \<lparr> IS_TyArgs := t \<rparr>) = (mc_state s) \<lparr> IS_TyArgs := t \<rparr>"
  "mc_state (s \<lparr> IS_World := w \<rparr>) = (mc_state s) \<lparr> IS_World := w \<rparr>"
  by (simp_all add: mc_state_def)

(* The scope and binding operations commute with mc_state. *)
lemma alloc_store_mc:
  "alloc_store (mc_state s) v = (mc_state (fst (alloc_store s v)), snd (alloc_store s v))"
  by (simp add: mc_state_def)

lemma bind_local_mc [simp]:
  "bind_local x v (mc_state s) = mc_state (bind_local x v s)"
  by (simp add: mc_state_def Let_def)

lemma bind_const_local_mc [simp]:
  "bind_const_local x v (mc_state s) = mc_state (bind_const_local x v s)"
  by (simp add: mc_state_def Let_def)

lemma bind_mutable_local_mc [simp]:
  "bind_mutable_local x v (mc_state s) = mc_state (bind_mutable_local x v s)"
  by (simp add: mc_state_def Let_def)

lemma bind_ref_mc [simp]:
  "bind_ref x ap (mc_state s) = mc_state (bind_ref x ap s)"
  by (simp add: mc_state_def)

lemma restore_scope_mc [simp]:
  "restore_scope (mc_state old) (mc_state new) = mc_state (restore_scope old new)"
  by (simp add: mc_state_def)

lemma perform_swap_mc:
  "perform_swap (mc_state s) l r = map_sum id mc_state (perform_swap s l r)"
  by (cases l; cases r) (simp add: Let_def split: sum.splits)

lemma apply_ref_updates_mc:
  "apply_ref_updates (mc_state s) refs vals = map_sum id mc_state (apply_ref_updates s refs vals)"
proof (induction s refs vals rule: apply_ref_updates.induct)
  case (2 state addr path rest_lvals newVal rest_vals)
  then show ?case
    by (simp add: Let_def split: sum.splits)
qed simp_all

lemma is_pure_fun_mc [simp]:
  "is_pure_fun (mc_state s) fnName = is_pure_fun s fnName"
  by (simp split: option.splits)

lemma copy_check_mc [simp]:
  "copy_check g (mc_state s) ty v = copy_check g s ty v"
  by (rule copy_check_cong_state) simp_all

lemma default_value_mc [simp]:
  "default_value n (mc_state s) ty = default_value n s ty"
  using default_value_cong_state(1)[of "mc_state s" s n] by simp

(* The evaluation of a variable only reads the store and the variable
   bindings, which mc_state keeps; it uses no fuel beyond the first unit. *)
lemma interp_term_Var_mc [simp]:
  "interp_term d (Suc n) (mc_state s) (CoreTm_Var x) = interp_term d (Suc n) s (CoreTm_Var x)"
  by (simp split: option.splits)

lemma interp_term_Var_fuel:
  "interp_term d (Suc n) s (CoreTm_Var x) = interp_term d' (Suc n') s (CoreTm_Var x)"
  by simp

(* Processing one argument of a call commutes with mc_state. *)
lemma process_one_arg_mc:
  "process_one_arg t (Inr (mc_state s)) = map_sum id mc_state (process_one_arg t (Inr s))"
proof -
  obtain name vr r v where t_eq: "t = ((name, vr), r, v)" by (cases t) auto
  show ?thesis unfolding t_eq by (cases vr; cases r; cases v) auto
qed

(* The results of a statement list, with the function bodies compiled. *)
fun mc_result :: "'w ExecResult \<Rightarrow> 'w ExecResult" where
  "mc_result (Continue s) = Continue (mc_state s)"
| "mc_result (Return s v) = Return (mc_state s) v"

lemma mc_result_scope_result [simp]:
  "mc_result (scope_result s r) = scope_result (mc_state s) (mc_result r)"
  by (cases r) simp_all

lemma scope_result_idem [simp]:
  "scope_result s (scope_result s r) = scope_result s r"
  by (cases r) simp_all


section \<open>The function table\<close>

(* What the simulation needs of the function table of the state (and of the
   signatures in the type environment, genv):
    - no function is ghost and no parameter is ghost, so that every call is
      typed in NotGhost mode and no ghost code is ever evaluated;
    - no function has a contract, so that a call is just its body;
    - every function body is ghost-free and has variable scrutinees.
   All of this holds of the state built from a ghost-free module that
   satisfies core_module_match_scrutinees_ok (see the end of
   MatchCompilePassSimulation.thy). *)
definition funs_match_compilable :: "CoreTyEnv \<Rightarrow> (string, 'w InterpFun) fmap \<Rightarrow> bool" where
  "funs_match_compilable genv funs \<longleftrightarrow>
     (\<forall>name info. fmlookup (TE_Functions genv) name = Some info
                    \<longrightarrow> FI_Ghost info = NotGhost \<and> no_ghost_params info)
   \<and> (\<forall>name f. fmlookup funs name = Some f
                \<longrightarrow> IF_Requires f = [] \<and> IF_Ensures f = []
                  \<and> (\<forall>body. IF_Body f = Inl body
                             \<longrightarrow> core_statement_list_ghost_free body
                               \<and> core_statement_list_match_scrutinees_ok body))"

lemma funs_match_compilable_info:
  "funs_match_compilable genv funs \<Longrightarrow> fmlookup (TE_Functions genv) name = Some info
   \<Longrightarrow> FI_Ghost info = NotGhost \<and> no_ghost_params info"
  unfolding funs_match_compilable_def by blast

lemma funs_match_compilable_fun:
  "funs_match_compilable genv funs \<Longrightarrow> fmlookup funs name = Some f
   \<Longrightarrow> IF_Requires f = [] \<and> IF_Ensures f = []
       \<and> (\<forall>body. IF_Body f = Inl body
                  \<longrightarrow> core_statement_list_ghost_free body
                    \<and> core_statement_list_match_scrutinees_ok body)"
  unfolding funs_match_compilable_def by blast


section \<open>Fuel\<close>

(* One fuel for finitely many evaluations: if each of a finite number of
   properties holds at some fuel and is monotone in the fuel, they all hold
   at one fuel. *)
lemma ex_fuel_all:
  fixes P :: "nat \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "\<And>a. a \<in> set xs \<Longrightarrow> \<exists>n. P n a"
      and "\<And>n n' a. a \<in> set xs \<Longrightarrow> P n a \<Longrightarrow> n \<le> n' \<Longrightarrow> P n' a"
  shows "\<exists>n. \<forall>a \<in> set xs. P n a"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have x_in: "x \<in> set (x # xs)" by simp
  from Cons.prems(1)[OF x_in] obtain n1 where n1: "P n1 x" by blast
  have "\<exists>n. \<forall>a \<in> set xs. P n a"
  proof (rule Cons.IH)
    fix a assume "a \<in> set xs"
    hence "a \<in> set (x # xs)" by simp
    from Cons.prems(1)[OF this] show "\<exists>n. P n a" .
  next
    fix n n' a assume "a \<in> set xs" and pn: "P n a" and le: "n \<le> n'"
    hence "a \<in> set (x # xs)" by simp
    from Cons.prems(2)[OF this pn le] show "P n' a" .
  qed
  then obtain n2 where n2: "\<forall>a \<in> set xs. P n2 a" by blast
  have "\<forall>a \<in> set (x # xs). P (max n1 n2) a"
  proof
    fix a assume a_in: "a \<in> set (x # xs)"
    show "P (max n1 n2) a"
    proof (cases "a = x")
      case True
      with n1 have pa: "P n1 a" by simp
      show ?thesis by (rule Cons.prems(2)[OF a_in pa]) (rule max.cobounded1)
    next
      case False
      with a_in n2 have pa: "P n2 a" by simp
      show ?thesis by (rule Cons.prems(2)[OF a_in pa]) (rule max.cobounded2)
    qed
  qed
  thus ?case by blast
qed

lemma interp_term_Inr_more_fuel:
  assumes "interp_term d f s tm = Inr v" and "f \<le> f'"
  shows "interp_term d f' s tm = Inr v"
  by (rule interp_term_more_fuel[OF assms(1) _ assms(2)]) simp

lemma interp_term_list_Inr_more_fuel:
  assumes "interp_term_list d f s tms = Inr vs" and "f \<le> f'"
  shows "interp_term_list d f' s tms = Inr vs"
proof -
  have "interp_term_list d f s tms \<noteq> Inl InsufficientFuel" using assms(1) by simp
  from interp_term_list_fuel_mono[OF this, rule_format, OF assms(2)] assms(1)
  show ?thesis by simp
qed

lemma interp_writable_lvalue_Inr_more_fuel:
  assumes "interp_writable_lvalue d f s tm = Inr r" and "f \<le> f'"
  shows "interp_writable_lvalue d f' s tm = Inr r"
proof -
  have "interp_writable_lvalue d f s tm \<noteq> Inl InsufficientFuel" using assms(1) by simp
  from interp_writable_lvalue_fuel_mono[OF this, rule_format, OF assms(2)] assms(1)
  show ?thesis by simp
qed

lemma interp_statement_Inr_more_fuel:
  assumes "interp_statement d f s stmt = Inr r" and "f \<le> f'"
  shows "interp_statement d f' s stmt = Inr r"
  by (rule interp_statement_more_fuel[OF assms(1) _ assms(2)]) simp

lemma interp_statement_list_Inr_more_fuel:
  assumes "interp_statement_list d f s stmts = Inr r" and "f \<le> f'"
  shows "interp_statement_list d f' s stmts = Inr r"
  by (rule interp_statement_list_more_fuel[OF assms(1) _ assms(2)]) simp

lemma interp_function_call_Inr_more_fuel:
  assumes "interp_function_call d f s fn tys args = Inr r" and "f \<le> f'"
  shows "interp_function_call d f' s fn tys args = Inr r"
  by (rule interp_function_call_more_fuel[OF assms(1) _ assms(2)]) simp


section \<open>Arguments of a call\<close>

(* Binding the arguments of a call in the compiled state, from argument
   results that agree with the original ones wherever those succeeded, gives
   the compiled pre-call state. (An argument result that the original run
   does not need, e.g. the lvalue of a Var argument, may differ.) *)
lemma fold_process_one_arg_mc:
  assumes "fold process_one_arg (zip fnArgs (zip refs vals)) (Inr s) = Inr s1"
      and "length fnArgs = length refs" and "length refs = length vals"
      and "length refs' = length refs" and "length vals' = length vals"
      and "\<And>i v. i < length vals \<Longrightarrow> vals ! i = Inr v \<Longrightarrow> vals' ! i = Inr v"
      and "\<And>i l. i < length refs \<Longrightarrow> refs ! i = Inr l \<Longrightarrow> refs' ! i = Inr l"
  shows "fold process_one_arg (zip fnArgs (zip refs' vals')) (Inr (mc_state s)) = Inr (mc_state s1)"
  using assms
proof (induction fnArgs arbitrary: refs vals refs' vals' s)
  case Nil
  then show ?case by simp
next
  case (Cons a fnArgs)
  obtain name vr where a_eq: "a = (name, vr)" by (cases a)
  from Cons.prems(2,3,4,5) obtain r rs v vs r' rs' v' vs' where
    refs_eq: "refs = r # rs" and vals_eq: "vals = v # vs" and
    refs'_eq: "refs' = r' # rs'" and vals'_eq: "vals' = v' # vs'"
    by (cases refs; cases vals; cases refs'; cases vals') auto
  from Cons.prems(6)[of 0] vals_eq vals'_eq have v_agree: "\<And>w. v = Inr w \<Longrightarrow> v' = Inr w" by simp
  from Cons.prems(7)[of 0] refs_eq refs'_eq have r_agree: "\<And>l. r = Inr l \<Longrightarrow> r' = Inr l" by simp
  have vs_agree: "\<And>i w. i < length vs \<Longrightarrow> vs ! i = Inr w \<Longrightarrow> vs' ! i = Inr w"
    using Cons.prems(6)[of "Suc _"] vals_eq vals'_eq by simp
  have rs_agree: "\<And>i l. i < length rs \<Longrightarrow> rs ! i = Inr l \<Longrightarrow> rs' ! i = Inr l"
    using Cons.prems(7)[of "Suc _"] refs_eq refs'_eq by simp
  have lens: "length fnArgs = length rs" "length rs = length vs" "length rs' = length rs"
    "length vs' = length vs"
    using Cons.prems(2,3,4,5) refs_eq vals_eq refs'_eq vals'_eq by simp_all
  \<comment> \<open>The first argument succeeded in the original run.\<close>
  from Cons.prems(1) refs_eq vals_eq a_eq
  obtain s0 where step: "process_one_arg ((name, vr), r, v) (Inr s) = Inr s0"
    and rest: "fold process_one_arg (zip fnArgs (zip rs vs)) (Inr s0) = Inr s1"
    by (cases "process_one_arg ((name, vr), r, v) (Inr s)")
       (auto simp: fold_process_one_arg_error)
  have step': "process_one_arg ((name, vr), r', v') (Inr (mc_state s)) = Inr (mc_state s0)"
  proof (cases vr)
    case Var
    from step Var obtain w where v_eq: "v = Inr w" by (cases v) auto
    with step Var have "s0 = bind_const_local name w s" by simp
    with v_agree[OF v_eq] Var show ?thesis by simp
  next
    case Ref
    from step Ref obtain l w where r_eq: "r = Inr l" and v_eq: "v = Inr w"
      by (cases r; cases v) auto
    with step Ref have "s0 = bind_ref name l s" by (cases l) auto
    with r_agree[OF r_eq] v_agree[OF v_eq] Ref show ?thesis by (cases l) auto
  qed
  have "fold process_one_arg (zip fnArgs (zip rs' vs')) (Inr (mc_state s0)) = Inr (mc_state s1)"
    by (rule Cons.IH[OF rest lens vs_agree rs_agree])
  with step' a_eq refs'_eq vals'_eq show ?case by simp
qed


section \<open>Variables as a value environment\<close>

(* The value environment of MatchCompileSemantics.thy that corresponds to a
   state: the value of each variable, when it has one. A variable is
   evaluated with one unit of fuel and at any depth. *)
definition var_env :: "'w InterpState \<Rightarrow> string \<Rightarrow> CoreValue option" where
  "var_env s x = (case interp_term 0 (Suc 0) s (CoreTm_Var x) of Inr v \<Rightarrow> Some v | Inl _ \<Rightarrow> None)"

lemma var_env_SomeD:
  "var_env s x = Some v \<Longrightarrow> interp_term d (Suc n) s (CoreTm_Var x) = Inr v"
  unfolding var_env_def by (simp split: sum.splits)

lemma var_env_SomeI:
  "interp_term d (Suc n) s (CoreTm_Var x) = Inr v \<Longrightarrow> var_env s x = Some v"
  unfolding var_env_def by simp

lemma var_env_mc [simp]:
  "var_env (mc_state s) = var_env s"
  by (unfold var_env_def interp_term_Var_mc) (rule refl)

(* A test scrutinee (a variable with projections) that the match compiler's
   walker evaluates is evaluated to the same value by the interpreter, at
   some fuel. *)
lemma eval_match_scrut_interp:
  assumes "eval_match_scrut (var_env s) t = Some v"
  shows "\<exists>n. interp_term d n s t = Inr v"
  using assms
proof (induction t arbitrary: v)
  case (CoreTm_Var x)
  hence "var_env s x = Some v" by simp
  hence "interp_term d (Suc 0) s (CoreTm_Var x) = Inr v" by (rule var_env_SomeD)
  thus ?case by blast
next
  case (CoreTm_VariantProj t h)
  from CoreTm_VariantProj.prems obtain h' w where
    t_eval: "eval_match_scrut (var_env s) t = Some (CV_Variant h' w)" and
    h_eq: "h' = h" and v_eq: "v = w"
    by (auto split: option.splits CoreValue.splits if_splits)
  from CoreTm_VariantProj.IH[OF t_eval] obtain n where
    "interp_term d n s t = Inr (CV_Variant h' w)" by blast
  hence "interp_term d (Suc n) s (CoreTm_VariantProj t h) = Inr w" using h_eq by simp
  thus ?case using v_eq by blast
next
  case (CoreTm_RecordProj t f)
  from CoreTm_RecordProj.prems obtain flds where
    t_eval: "eval_match_scrut (var_env s) t = Some (CV_Record flds)" and
    f_eq: "map_of flds f = Some v"
    by (auto split: option.splits CoreValue.splits)
  from CoreTm_RecordProj.IH[OF t_eval] obtain n where
    "interp_term d n s t = Inr (CV_Record flds)" by blast
  hence "interp_term d (Suc n) s (CoreTm_RecordProj t f) = Inr v" using f_eq by simp
  thus ?case by blast
qed simp_all


section \<open>Pattern matching\<close>

(* The match compiler's `matches` is the interpreter's pattern_matches. *)
lemma matches_eq_pattern_matches:
  "matches v p = pattern_matches v p"
  "matches_fields vs ps = pattern_matches_fields vs ps"
  by (induction v p and vs ps rule: matches_matches_fields.induct) simp_all

lemma arms_first_match_find_matching_arm:
  "arms_first_match v arms = (case find_matching_arm v arms of Inr b \<Rightarrow> Some b | Inl _ \<Rightarrow> None)"
  by (induction v arms rule: arms_first_match.induct) (simp_all add: matches_eq_pattern_matches)

(* The arm that arms_find picks in a tree is the arm that the interpreter
   picks in the translated match. *)
lemma arms_find_find_matching_arm:
  assumes "arms_find v arms = Some t"
  shows "find_matching_arm v (map (\<lambda>(p, t). (p, f t)) arms) = Inr (f t)"
  using assms
  by (induction v arms rule: arms_find.induct)
     (auto simp: matches_eq_pattern_matches split: if_splits)


section \<open>Running a translated tree\<close>

(* A single statement, as a statement list. *)
lemma interp_statement_list_single:
  "interp_statement d (Suc f) s stmt = Inr res
   \<Longrightarrow> interp_statement_list d (Suc (Suc f)) s [stmt] = Inr res"
  by (cases res) simp_all

(* A term tree whose walk picks the leaf b evaluates, in the interpreter, as
   b does, at some fuel. *)
lemma match_tree_to_term_eval:
  assumes "match_tree_eval (var_env s) t = Some b"
      and "interp_term d fuel s b = Inr v"
  shows "\<exists>fuel'. interp_term d fuel' s (match_tree_to_term t) = Inr v"
  using assms
proof (induction t arbitrary: fuel)
  case (MT_Leaf body)
  then show ?case by auto
next
  case (MT_Test sc arms)
  from MT_Test.prems(1) obtain w t' where
    sc_eval: "eval_match_scrut (var_env s) sc = Some w" and
    arm: "arms_find w arms = Some t'" and
    t'_eval: "match_tree_eval (var_env s) t' = Some b"
    by (auto split: option.splits)
  from arms_find_in[OF arm] obtain p where arm_in: "(p, t') \<in> set arms" by auto
  have t'_in: "t' \<in> Basic_BNFs.snds (p, t')" by simp
  from MT_Test.IH[OF arm_in t'_in t'_eval MT_Test.prems(2)] obtain f1 where
    f1: "interp_term d f1 s (match_tree_to_term t') = Inr v" by blast
  from eval_match_scrut_interp[OF sc_eval] obtain n where
    n: "interp_term d n s sc = Inr w" by blast
  let ?F = "max f1 n"
  have sc': "interp_term d ?F s sc = Inr w" by (rule interp_term_Inr_more_fuel[OF n]) simp
  have t'': "interp_term d ?F s (match_tree_to_term t') = Inr v"
    by (rule interp_term_Inr_more_fuel[OF f1]) simp
  have "interp_term d (Suc ?F) s (match_tree_to_term (MT_Test sc arms)) = Inr v"
    using sc' arms_find_find_matching_arm[OF arm, of match_tree_to_term] t'' by simp
  thus ?case by blast
qed

(* A statement tree whose walk picks the leaf b runs, in the interpreter, as
   b does, at some fuel; a test (a CoreStmt_Match) runs its arm in a scope,
   so the result of a tree that is not a single leaf is scoped. *)
lemma match_tree_to_statements_exec:
  assumes "match_tree_eval (var_env s) t = Some b"
      and "interp_statement_list d fuel s b = Inr r"
  shows "\<exists>fuel'. interp_statement_list d fuel' s (match_tree_to_statements g t)
                   = Inr (case t of MT_Leaf _ \<Rightarrow> r | MT_Test _ _ \<Rightarrow> scope_result s r)"
  using assms
proof (induction t arbitrary: fuel)
  case (MT_Leaf body)
  then show ?case by auto
next
  case (MT_Test sc arms)
  from MT_Test.prems(1) obtain w t' where
    sc_eval: "eval_match_scrut (var_env s) sc = Some w" and
    arm: "arms_find w arms = Some t'" and
    t'_eval: "match_tree_eval (var_env s) t' = Some b"
    by (auto split: option.splits)
  from arms_find_in[OF arm] obtain p where arm_in: "(p, t') \<in> set arms" by auto
  have t'_in: "t' \<in> Basic_BNFs.snds (p, t')" by simp
  from MT_Test.IH[OF arm_in t'_in t'_eval MT_Test.prems(2)] obtain f1 where
    f1: "interp_statement_list d f1 s (match_tree_to_statements g t')
           = Inr (case t' of MT_Leaf _ \<Rightarrow> r | MT_Test _ _ \<Rightarrow> scope_result s r)" by blast
  from eval_match_scrut_interp[OF sc_eval] obtain n where
    n: "interp_term d n s sc = Inr w" by blast
  let ?F = "max f1 n"
  let ?r' = "case t' of MT_Leaf _ \<Rightarrow> r | MT_Test _ _ \<Rightarrow> scope_result s r"
  have sc': "interp_term d ?F s sc = Inr w" by (rule interp_term_Inr_more_fuel[OF n]) simp
  have t'': "interp_statement_list d ?F s (match_tree_to_statements g t') = Inr ?r'"
    by (rule interp_statement_list_Inr_more_fuel[OF f1]) simp
  have m: "interp_statement d (Suc ?F) s
             (CoreStmt_Match g sc (map (\<lambda>(p, t). (p, match_tree_to_statements g t)) arms))
           = Inr (scope_result s ?r')"
    by (rule interp_Match_scope_result[OF sc'
          arms_find_find_matching_arm[OF arm, where f = "match_tree_to_statements g"] t''])
  have sr: "scope_result s ?r' = scope_result s r" by (cases t') simp_all
  have X: "interp_statement_list d (Suc (Suc ?F)) s
             [CoreStmt_Match g sc (map (\<lambda>(p, t). (p, match_tree_to_statements g t)) arms)]
           = Inr (scope_result s r)"
    using interp_statement_list_single[OF m] unfolding sr .
  show ?case
    unfolding match_tree_to_statements.simps MatchTree.case
    by (rule exI[of _ "Suc (Suc ?F)"]) (rule X)
qed


section \<open>The compiled tree of a match on a variable\<close>

(* The hypotheses of compile_match_semantics for a match on a variable, in a
   state that matches the typing environment: the variable's value has the
   ground instance (through IS_TyArgs) of the variable's static type, and
   the patterns are compatible with that ground type. The theorem is applied
   in an environment in which the variable is re-declared at the ground type
   (as a ghost const local, which keeps the environment well-formed without
   asking for the type to be runtime). *)
lemma compile_match_tree_eval:
  fixes s :: "'w InterpState"
  assumes sme: "state_matches_env s env storeTyping"
      and wf: "tyenv_well_formed env"
      and ty: "core_term_type env g (CoreTm_Var x) = Some scrutTy"
      and pats: "list_all (\<lambda>(p, _). pattern_compatible env p scrutTy) arms"
      and ne: "arms \<noteq> []"
      and ev: "interp_term d (Suc n) s (CoreTm_Var x) = Inr v"
  shows "match_tree_eval (var_env s) (compile_match_tree (CoreTm_Var x) arms)
           = arms_first_match v arms"
proof -
  let ?T = "apply_subst (IS_TyArgs s) scrutTy"
  let ?envM = "env \<lparr> TE_LocalVars := fmupd x ?T (TE_LocalVars env),
                     TE_GhostLocals := finsert x (TE_GhostLocals env),
                     TE_ConstLocals := finsert x (TE_ConstLocals env) \<rparr>"
  have vt: "value_has_type env v ?T"
    using interp_term_sound[OF sme wf, THEN mp, OF ty, of d "Suc n"] ev by simp
  have abs_empty: "TE_AbstractTypes env = {||}"
    using sme unfolding state_matches_env_def by blast
  have wk: "is_well_kinded env scrutTy" by (rule core_term_type_well_kinded[OF ty wf])
  have wkT: "is_well_kinded env ?T" by (rule is_well_kinded_apply_IS_TyArgs[OF sme wk])
  have wfM: "tyenv_well_formed ?envM" by (rule tyenv_well_formed_declare_ghost[OF wf wkT])
  have tyM: "core_term_type ?envM Ghost (CoreTm_Var x) = Some ?T"
    by (simp add: tyenv_lookup_var_def)
  have patsM: "list_all (\<lambda>(p, _). pattern_compatible ?envM p ?T) arms"
  proof -
    have "pattern_compatible ?envM p ?T" if "pattern_compatible env p scrutTy" for p
    proof -
      have "pattern_compatible env p ?T"
        by (rule pattern_compatible_apply_subst[OF wf that]) (simp add: abs_empty)
      thus ?thesis by (subst pattern_compatible_cong_env[of ?envM env]) simp_all
    qed
    with pats show ?thesis by (auto simp: list_all_iff)
  qed
  have vtM: "value_has_type ?envM v ?T"
    using vt by (subst value_has_type_ground_cong_env[of ?envM env]) simp_all
  have scrut: "eval_match_scrut (var_env s) (CoreTm_Var x) = Some v"
    using var_env_SomeI[OF ev] by simp
  have "match_tree_eval (var_env s) (compile_match (CoreTm_Var x) ?T arms) = arms_first_match v arms"
    by (rule compile_match_semantics[OF tyM ne patsM wfM scrut vtM])
  thus ?thesis
    unfolding compile_match_tree_eq_compile_match[of "CoreTm_Var x" arms ?T] .
qed

end
