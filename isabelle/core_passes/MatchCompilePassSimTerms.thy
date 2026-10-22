theory MatchCompilePassSimTerms
  imports MatchCompilePassState
begin

(* The simulation for the match compilation pass, term by term.

   The simulation theorem (MatchCompilePassSimulation.thy) is proved by one
   induction on the fuel, for the six interpreter functions together. This
   file states the induction's six claims as predicates on the fuel
   (term_sim, terms_sim, lvalue_sim, stmt_sim, stmts_sim, call_sim) and
   proves the term, term list and lvalue cases of the induction step as
   separate lemmas, each taking the induction hypotheses it needs as
   assumptions. The statement and call cases are in
   MatchCompilePassSimStmts.thy.

   The setting is fixed in a locale: the depth d (which executable code never
   changes), the signatures genv of the program's functions, and the
   function table funs of the state, with funs_match_compilable genv funs.

   Each claim says: if the original run from a state `full` that matches a
   well-formed environment succeeds, at the given fuel, on a term (statement,
   ...) that is well-typed in NotGhost mode in that environment and has
   variable scrutinees, then the compiled run from mc_state full succeeds at
   some fuel with the same value (the compiled state). The hypotheses on the
   environment are what the type soundness theorem needs to tell us that the
   scrutinee of a compiled match is a well-typed value, which is what the
   match compiler's semantics (compile_match_semantics) is about. *)

(* With no ghost parameters, every argument of a call is typed in the ambient
   NotGhost mode. *)
lemma param_modes_no_ghost:
  "list_all (\<lambda>(_, _, gh). gh = NotGhost) params
   \<Longrightarrow> map (\<lambda>(_, _, gh). param_mode NotGhost gh) params = replicate (length params) NotGhost"
  by (induction params) (auto simp: case_prod_unfold)

locale match_compile_sim =
  fixes d :: nat
    and genv :: CoreTyEnv
    and funs :: "(string, 'w InterpFun) fmap"
  assumes fmc: "funs_match_compilable genv funs"
begin

section \<open>The claims\<close>

definition term_sim :: "nat \<Rightarrow> CoreTerm \<Rightarrow> bool" where
  "term_sim fuel tm \<longleftrightarrow>
    (\<forall>env storeTyping (full :: 'w InterpState) ty v.
       TE_Functions env = TE_Functions genv \<longrightarrow> IS_Functions full = funs \<longrightarrow>
       state_matches_env full env storeTyping \<longrightarrow> tyenv_well_formed env \<longrightarrow>
       core_term_type env NotGhost tm = Some ty \<longrightarrow> core_term_match_scrutinees_ok tm \<longrightarrow>
       interp_term d fuel full tm = Inr v \<longrightarrow>
       (\<exists>fuel'. interp_term d fuel' (mc_state full) (match_compile_term tm) = Inr v))"

definition terms_sim :: "nat \<Rightarrow> CoreTerm list \<Rightarrow> bool" where
  "terms_sim fuel tms \<longleftrightarrow>
    (\<forall>env storeTyping (full :: 'w InterpState) vs.
       TE_Functions env = TE_Functions genv \<longrightarrow> IS_Functions full = funs \<longrightarrow>
       state_matches_env full env storeTyping \<longrightarrow> tyenv_well_formed env \<longrightarrow>
       (\<forall>tm \<in> set tms. \<exists>ty. core_term_type env NotGhost tm = Some ty) \<longrightarrow>
       list_all core_term_match_scrutinees_ok tms \<longrightarrow>
       interp_term_list d fuel full tms = Inr vs \<longrightarrow>
       (\<exists>fuel'. interp_term_list d fuel' (mc_state full) (map match_compile_term tms) = Inr vs))"

definition lvalue_sim :: "nat \<Rightarrow> CoreTerm \<Rightarrow> bool" where
  "lvalue_sim fuel tm \<longleftrightarrow>
    (\<forall>env storeTyping (full :: 'w InterpState) ty r.
       TE_Functions env = TE_Functions genv \<longrightarrow> IS_Functions full = funs \<longrightarrow>
       state_matches_env full env storeTyping \<longrightarrow> tyenv_well_formed env \<longrightarrow>
       core_term_type env NotGhost tm = Some ty \<longrightarrow> core_term_match_scrutinees_ok tm \<longrightarrow>
       interp_writable_lvalue d fuel full tm = Inr r \<longrightarrow>
       (\<exists>fuel'. interp_writable_lvalue d fuel' (mc_state full) (match_compile_term tm) = Inr r))"

definition stmt_sim :: "nat \<Rightarrow> CoreStatement \<Rightarrow> bool" where
  "stmt_sim fuel stmt \<longleftrightarrow>
    (\<forall>env env' storeTyping (full :: 'w InterpState) res.
       TE_Functions env = TE_Functions genv \<longrightarrow> IS_Functions full = funs \<longrightarrow>
       state_matches_env full env storeTyping \<longrightarrow> tyenv_well_formed env \<longrightarrow>
       TE_ProofGoal env = None \<longrightarrow>
       core_statement_type env NotGhost stmt = Some env' \<longrightarrow>
       core_statement_ghost_free stmt \<longrightarrow> core_statement_match_scrutinees_ok stmt \<longrightarrow>
       interp_statement d fuel full stmt = Inr res \<longrightarrow>
       (\<exists>fuel'. interp_statement_list d fuel' (mc_state full) (match_compile_statement stmt)
                  = Inr (mc_result res)))"

definition stmts_sim :: "nat \<Rightarrow> CoreStatement list \<Rightarrow> bool" where
  "stmts_sim fuel stmts \<longleftrightarrow>
    (\<forall>env env' storeTyping (full :: 'w InterpState) res.
       TE_Functions env = TE_Functions genv \<longrightarrow> IS_Functions full = funs \<longrightarrow>
       state_matches_env full env storeTyping \<longrightarrow> tyenv_well_formed env \<longrightarrow>
       TE_ProofGoal env = None \<longrightarrow>
       core_statement_list_type env NotGhost stmts = Some env' \<longrightarrow>
       core_statement_list_ghost_free stmts \<longrightarrow> core_statement_list_match_scrutinees_ok stmts \<longrightarrow>
       interp_statement_list d fuel full stmts = Inr res \<longrightarrow>
       (\<exists>fuel'. interp_statement_list d fuel' (mc_state full) (match_compile_statement_list stmts)
                  = Inr (mc_result res)))"

(* The call claim takes the typing of the call apart, in the form that the
   type soundness theorem uses, so that it serves both a pure call in a term
   and an impure call in a statement. *)
definition call_sim :: "nat \<Rightarrow> string \<Rightarrow> CoreType list \<Rightarrow> CoreTerm list \<Rightarrow> bool" where
  "call_sim fuel fnName tyArgs argTms \<longleftrightarrow>
    (\<forall>env storeTyping (full :: 'w InterpState) funInfo newFull retVal.
       TE_Functions env = TE_Functions genv \<longrightarrow> IS_Functions full = funs \<longrightarrow>
       state_matches_env full env storeTyping \<longrightarrow> tyenv_well_formed env \<longrightarrow>
       fmlookup (TE_Functions env) fnName = Some funInfo \<longrightarrow>
       list_all2 (\<lambda>tm expectedTy. core_term_type env NotGhost tm = Some expectedTy)
         argTms (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo)) \<longrightarrow>
       length tyArgs = length (FI_TyArgs funInfo) \<longrightarrow>
       list_all (is_well_kinded env) tyArgs \<longrightarrow>
       (\<forall>i < length argTms.
          fst (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow> is_writable_lvalue env (argTms ! i)) \<longrightarrow>
       list_all core_term_match_scrutinees_ok argTms \<longrightarrow>
       interp_function_call d fuel full fnName tyArgs argTms = Inr (newFull, retVal) \<longrightarrow>
       (\<exists>fuel'. interp_function_call d fuel' (mc_state full) fnName tyArgs
                  (map match_compile_term argTms) = Inr (mc_state newFull, retVal)))"

lemma term_simI:
  assumes "\<And>env storeTyping (full :: 'w InterpState) ty v.
       TE_Functions env = TE_Functions genv \<Longrightarrow> IS_Functions full = funs \<Longrightarrow>
       state_matches_env full env storeTyping \<Longrightarrow> tyenv_well_formed env \<Longrightarrow>
       core_term_type env NotGhost tm = Some ty \<Longrightarrow> core_term_match_scrutinees_ok tm \<Longrightarrow>
       interp_term d fuel full tm = Inr v \<Longrightarrow>
       \<exists>fuel'. interp_term d fuel' (mc_state full) (match_compile_term tm) = Inr v"
  shows "term_sim fuel tm"
  unfolding term_sim_def using assms by blast

lemma term_simD:
  assumes "term_sim fuel tm"
      and "TE_Functions env = TE_Functions genv" and "IS_Functions full = funs"
      and "state_matches_env full env storeTyping" and "tyenv_well_formed env"
      and "core_term_type env NotGhost tm = Some ty" and "core_term_match_scrutinees_ok tm"
      and "interp_term d fuel full tm = Inr v"
  shows "\<exists>fuel'. interp_term d fuel' (mc_state full) (match_compile_term tm) = Inr v"
  using assms unfolding term_sim_def by blast

lemma terms_simI:
  assumes "\<And>env storeTyping (full :: 'w InterpState) vs.
       TE_Functions env = TE_Functions genv \<Longrightarrow> IS_Functions full = funs \<Longrightarrow>
       state_matches_env full env storeTyping \<Longrightarrow> tyenv_well_formed env \<Longrightarrow>
       (\<forall>tm \<in> set tms. \<exists>ty. core_term_type env NotGhost tm = Some ty) \<Longrightarrow>
       list_all core_term_match_scrutinees_ok tms \<Longrightarrow>
       interp_term_list d fuel full tms = Inr vs \<Longrightarrow>
       \<exists>fuel'. interp_term_list d fuel' (mc_state full) (map match_compile_term tms) = Inr vs"
  shows "terms_sim fuel tms"
  unfolding terms_sim_def using assms by blast

lemma terms_simD:
  assumes "terms_sim fuel tms"
      and "TE_Functions env = TE_Functions genv" and "IS_Functions full = funs"
      and "state_matches_env full env storeTyping" and "tyenv_well_formed env"
      and "\<forall>tm \<in> set tms. \<exists>ty. core_term_type env NotGhost tm = Some ty"
      and "list_all core_term_match_scrutinees_ok tms"
      and "interp_term_list d fuel full tms = Inr vs"
  shows "\<exists>fuel'. interp_term_list d fuel' (mc_state full) (map match_compile_term tms) = Inr vs"
  using assms unfolding terms_sim_def by blast

lemma lvalue_simI:
  assumes "\<And>env storeTyping (full :: 'w InterpState) ty r.
       TE_Functions env = TE_Functions genv \<Longrightarrow> IS_Functions full = funs \<Longrightarrow>
       state_matches_env full env storeTyping \<Longrightarrow> tyenv_well_formed env \<Longrightarrow>
       core_term_type env NotGhost tm = Some ty \<Longrightarrow> core_term_match_scrutinees_ok tm \<Longrightarrow>
       interp_writable_lvalue d fuel full tm = Inr r \<Longrightarrow>
       \<exists>fuel'. interp_writable_lvalue d fuel' (mc_state full) (match_compile_term tm) = Inr r"
  shows "lvalue_sim fuel tm"
  unfolding lvalue_sim_def using assms by blast

lemma lvalue_simD:
  assumes "lvalue_sim fuel tm"
      and "TE_Functions env = TE_Functions genv" and "IS_Functions full = funs"
      and "state_matches_env full env storeTyping" and "tyenv_well_formed env"
      and "core_term_type env NotGhost tm = Some ty" and "core_term_match_scrutinees_ok tm"
      and "interp_writable_lvalue d fuel full tm = Inr r"
  shows "\<exists>fuel'. interp_writable_lvalue d fuel' (mc_state full) (match_compile_term tm) = Inr r"
  using assms unfolding lvalue_sim_def by blast

lemma stmt_simI:
  assumes "\<And>env env' storeTyping (full :: 'w InterpState) res.
       TE_Functions env = TE_Functions genv \<Longrightarrow> IS_Functions full = funs \<Longrightarrow>
       state_matches_env full env storeTyping \<Longrightarrow> tyenv_well_formed env \<Longrightarrow>
       TE_ProofGoal env = None \<Longrightarrow>
       core_statement_type env NotGhost stmt = Some env' \<Longrightarrow>
       core_statement_ghost_free stmt \<Longrightarrow> core_statement_match_scrutinees_ok stmt \<Longrightarrow>
       interp_statement d fuel full stmt = Inr res \<Longrightarrow>
       \<exists>fuel'. interp_statement_list d fuel' (mc_state full) (match_compile_statement stmt)
                 = Inr (mc_result res)"
  shows "stmt_sim fuel stmt"
  unfolding stmt_sim_def using assms by blast

lemma stmt_simD:
  assumes "stmt_sim fuel stmt"
      and "TE_Functions env = TE_Functions genv" and "IS_Functions full = funs"
      and "state_matches_env full env storeTyping" and "tyenv_well_formed env"
      and "TE_ProofGoal env = None"
      and "core_statement_type env NotGhost stmt = Some env'"
      and "core_statement_ghost_free stmt" and "core_statement_match_scrutinees_ok stmt"
      and "interp_statement d fuel full stmt = Inr res"
  shows "\<exists>fuel'. interp_statement_list d fuel' (mc_state full) (match_compile_statement stmt)
                 = Inr (mc_result res)"
  using assms unfolding stmt_sim_def by blast

lemma stmts_simI:
  assumes "\<And>env env' storeTyping (full :: 'w InterpState) res.
       TE_Functions env = TE_Functions genv \<Longrightarrow> IS_Functions full = funs \<Longrightarrow>
       state_matches_env full env storeTyping \<Longrightarrow> tyenv_well_formed env \<Longrightarrow>
       TE_ProofGoal env = None \<Longrightarrow>
       core_statement_list_type env NotGhost stmts = Some env' \<Longrightarrow>
       core_statement_list_ghost_free stmts \<Longrightarrow> core_statement_list_match_scrutinees_ok stmts \<Longrightarrow>
       interp_statement_list d fuel full stmts = Inr res \<Longrightarrow>
       \<exists>fuel'. interp_statement_list d fuel' (mc_state full) (match_compile_statement_list stmts)
                 = Inr (mc_result res)"
  shows "stmts_sim fuel stmts"
  unfolding stmts_sim_def using assms by blast

lemma stmts_simD:
  assumes "stmts_sim fuel stmts"
      and "TE_Functions env = TE_Functions genv" and "IS_Functions full = funs"
      and "state_matches_env full env storeTyping" and "tyenv_well_formed env"
      and "TE_ProofGoal env = None"
      and "core_statement_list_type env NotGhost stmts = Some env'"
      and "core_statement_list_ghost_free stmts" and "core_statement_list_match_scrutinees_ok stmts"
      and "interp_statement_list d fuel full stmts = Inr res"
  shows "\<exists>fuel'. interp_statement_list d fuel' (mc_state full) (match_compile_statement_list stmts)
                 = Inr (mc_result res)"
  using assms unfolding stmts_sim_def by blast

lemma call_simI:
  assumes "\<And>env storeTyping (full :: 'w InterpState) funInfo newFull retVal.
       TE_Functions env = TE_Functions genv \<Longrightarrow> IS_Functions full = funs \<Longrightarrow>
       state_matches_env full env storeTyping \<Longrightarrow> tyenv_well_formed env \<Longrightarrow>
       fmlookup (TE_Functions env) fnName = Some funInfo \<Longrightarrow>
       list_all2 (\<lambda>tm expectedTy. core_term_type env NotGhost tm = Some expectedTy)
         argTms (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo)) \<Longrightarrow>
       length tyArgs = length (FI_TyArgs funInfo) \<Longrightarrow>
       list_all (is_well_kinded env) tyArgs \<Longrightarrow>
       (\<forall>i < length argTms.
          fst (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow> is_writable_lvalue env (argTms ! i)) \<Longrightarrow>
       list_all core_term_match_scrutinees_ok argTms \<Longrightarrow>
       interp_function_call d fuel full fnName tyArgs argTms = Inr (newFull, retVal) \<Longrightarrow>
       \<exists>fuel'. interp_function_call d fuel' (mc_state full) fnName tyArgs
                 (map match_compile_term argTms) = Inr (mc_state newFull, retVal)"
  shows "call_sim fuel fnName tyArgs argTms"
  unfolding call_sim_def using assms by blast

lemma call_simD:
  assumes "call_sim fuel fnName tyArgs argTms"
      and "TE_Functions env = TE_Functions genv" and "IS_Functions full = funs"
      and "state_matches_env full env storeTyping" and "tyenv_well_formed env"
      and "fmlookup (TE_Functions env) fnName = Some funInfo"
      and "list_all2 (\<lambda>tm expectedTy. core_term_type env NotGhost tm = Some expectedTy)
             argTms (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                         (FI_TmArgs funInfo))"
      and "length tyArgs = length (FI_TyArgs funInfo)"
      and "list_all (is_well_kinded env) tyArgs"
      and "\<forall>i < length argTms.
             fst (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow> is_writable_lvalue env (argTms ! i)"
      and "list_all core_term_match_scrutinees_ok argTms"
      and "interp_function_call d fuel full fnName tyArgs argTms = Inr (newFull, retVal)"
  shows "\<exists>fuel'. interp_function_call d fuel' (mc_state full) fnName tyArgs
                 (map match_compile_term argTms) = Inr (mc_state newFull, retVal)"
  using assms unfolding call_sim_def by blast

(* With no fuel, nothing succeeds. *)
lemma sim_zero:
  "term_sim 0 tm" "terms_sim 0 tms" "lvalue_sim 0 lv" "stmt_sim 0 stmt" "stmts_sim 0 stmts"
  "call_sim 0 fnName tyArgs argTms"
  unfolding term_sim_def terms_sim_def lvalue_sim_def stmt_sim_def stmts_sim_def call_sim_def
  by simp_all


section \<open>Terms without sub-evaluations\<close>

lemma sim_LitBool: "term_sim (Suc fuel) (CoreTm_LitBool b)"
proof (rule term_simI)
  fix full :: "'w InterpState" and v
  assume "interp_term d (Suc fuel) full (CoreTm_LitBool b) = Inr v"
  hence "interp_term d (Suc fuel) (mc_state full) (match_compile_term (CoreTm_LitBool b)) = Inr v"
    by simp
  thus "\<exists>fuel'. interp_term d fuel' (mc_state full) (match_compile_term (CoreTm_LitBool b)) = Inr v"
    by blast
qed

lemma sim_LitInt: "term_sim (Suc fuel) (CoreTm_LitInt i)"
proof (rule term_simI)
  fix full :: "'w InterpState" and v
  assume "interp_term d (Suc fuel) full (CoreTm_LitInt i) = Inr v"
  hence "interp_term d (Suc fuel) (mc_state full) (match_compile_term (CoreTm_LitInt i)) = Inr v"
    by simp
  thus "\<exists>fuel'. interp_term d fuel' (mc_state full) (match_compile_term (CoreTm_LitInt i)) = Inr v"
    by blast
qed

lemma sim_Var: "term_sim (Suc fuel) (CoreTm_Var x)"
proof (rule term_simI)
  fix full :: "'w InterpState" and v
  assume "interp_term d (Suc fuel) full (CoreTm_Var x) = Inr v"
  hence "interp_term d (Suc fuel) (mc_state full) (match_compile_term (CoreTm_Var x)) = Inr v"
    by (simp only: match_compile_term.simps interp_term_Var_mc)
  thus "\<exists>fuel'. interp_term d fuel' (mc_state full) (match_compile_term (CoreTm_Var x)) = Inr v"
    by blast
qed

lemma sim_Default: "term_sim (Suc fuel) (CoreTm_Default ty)"
proof (rule term_simI)
  fix full :: "'w InterpState" and v
  assume "interp_term d (Suc fuel) full (CoreTm_Default ty) = Inr v"
  hence "interp_term d (Suc fuel) (mc_state full) (match_compile_term (CoreTm_Default ty)) = Inr v"
    by simp
  thus "\<exists>fuel'. interp_term d fuel' (mc_state full) (match_compile_term (CoreTm_Default ty)) = Inr v"
    by blast
qed

(* Ghost-only terms are not typed in NotGhost mode. *)
lemma sim_Quantifier: "term_sim fuel (CoreTm_Quantifier q x ty body)"
  by (rule term_simI) simp

lemma sim_Allocated: "term_sim fuel (CoreTm_Allocated ty tm)"
  by (rule term_simI) simp


section \<open>Terms with one sub-term\<close>

lemma sim_Cast:
  assumes IH: "term_sim fuel tm"
  shows "term_sim (Suc fuel) (CoreTm_Cast ty tm)"
proof (rule term_simI)
  fix env storeTyping and full :: "'w InterpState" and ty' v
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_term_type env NotGhost (CoreTm_Cast ty tm) = Some ty'"
    and ok: "core_term_match_scrutinees_ok (CoreTm_Cast ty tm)"
    and ev: "interp_term d (Suc fuel) full (CoreTm_Cast ty tm) = Inr v"
  from typing obtain opTy where t: "core_term_type env NotGhost tm = Some opTy"
    by (auto split: option.splits if_splits)
  from ev obtain w where w: "interp_term d fuel full tm = Inr w" and c: "cast_value ty w = Inr v"
    by (auto split: sum.splits)
  from term_simD[OF IH fe fs sme wf t _ w] ok obtain f1 where
    f1: "interp_term d f1 (mc_state full) (match_compile_term tm) = Inr w" by auto
  have "interp_term d (Suc f1) (mc_state full) (match_compile_term (CoreTm_Cast ty tm)) = Inr v"
    using f1 c by simp
  thus "\<exists>fuel'. interp_term d fuel' (mc_state full) (match_compile_term (CoreTm_Cast ty tm)) = Inr v"
    by blast
qed

lemma sim_Unop:
  assumes IH: "term_sim fuel tm"
  shows "term_sim (Suc fuel) (CoreTm_Unop op tm)"
proof (rule term_simI)
  fix env storeTyping and full :: "'w InterpState" and ty' v
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_term_type env NotGhost (CoreTm_Unop op tm) = Some ty'"
    and ok: "core_term_match_scrutinees_ok (CoreTm_Unop op tm)"
    and ev: "interp_term d (Suc fuel) full (CoreTm_Unop op tm) = Inr v"
  from typing obtain opTy where t: "core_term_type env NotGhost tm = Some opTy"
    by (auto split: option.splits)
  from ev obtain w where w: "interp_term d fuel full tm = Inr w" and c: "eval_unop op w = Inr v"
    by (auto split: sum.splits)
  from term_simD[OF IH fe fs sme wf t _ w] ok obtain f1 where
    f1: "interp_term d f1 (mc_state full) (match_compile_term tm) = Inr w" by auto
  have "interp_term d (Suc f1) (mc_state full) (match_compile_term (CoreTm_Unop op tm)) = Inr v"
    using f1 c by simp
  thus "\<exists>fuel'. interp_term d fuel' (mc_state full) (match_compile_term (CoreTm_Unop op tm)) = Inr v"
    by blast
qed

lemma sim_VariantCtor:
  assumes IH: "term_sim fuel tm"
  shows "term_sim (Suc fuel) (CoreTm_VariantCtor c tys tm)"
proof (rule term_simI)
  fix env storeTyping and full :: "'w InterpState" and ty' v
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_term_type env NotGhost (CoreTm_VariantCtor c tys tm) = Some ty'"
    and ok: "core_term_match_scrutinees_ok (CoreTm_VariantCtor c tys tm)"
    and ev: "interp_term d (Suc fuel) full (CoreTm_VariantCtor c tys tm) = Inr v"
  from typing obtain pTy where t: "core_term_type env NotGhost tm = Some pTy"
    by (auto simp: Let_def split: option.splits if_splits)
  from ev obtain w where w: "interp_term d fuel full tm = Inr w" and v_eq: "v = CV_Variant c w"
    by (auto split: sum.splits)
  from term_simD[OF IH fe fs sme wf t _ w] ok obtain f1 where
    f1: "interp_term d f1 (mc_state full) (match_compile_term tm) = Inr w" by auto
  have "interp_term d (Suc f1) (mc_state full) (match_compile_term (CoreTm_VariantCtor c tys tm)) = Inr v"
    using f1 v_eq by simp
  thus "\<exists>fuel'. interp_term d fuel' (mc_state full) (match_compile_term (CoreTm_VariantCtor c tys tm))
                 = Inr v"
    by blast
qed

lemma sim_RecordProj:
  assumes IH: "term_sim fuel tm"
  shows "term_sim (Suc fuel) (CoreTm_RecordProj tm f)"
proof (rule term_simI)
  fix env storeTyping and full :: "'w InterpState" and ty' v
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_term_type env NotGhost (CoreTm_RecordProj tm f) = Some ty'"
    and ok: "core_term_match_scrutinees_ok (CoreTm_RecordProj tm f)"
    and ev: "interp_term d (Suc fuel) full (CoreTm_RecordProj tm f) = Inr v"
  from typing obtain fTys where t: "core_term_type env NotGhost tm = Some (CoreTy_Record fTys)"
    by (auto split: option.splits CoreType.splits)
  from ev obtain flds where w: "interp_term d fuel full tm = Inr (CV_Record flds)"
    and fv: "map_of flds f = Some v"
    by (auto split: sum.splits CoreValue.splits option.splits)
  from term_simD[OF IH fe fs sme wf t _ w] ok obtain f1 where
    f1: "interp_term d f1 (mc_state full) (match_compile_term tm) = Inr (CV_Record flds)" by auto
  have "interp_term d (Suc f1) (mc_state full) (match_compile_term (CoreTm_RecordProj tm f)) = Inr v"
    using f1 fv by simp
  thus "\<exists>fuel'. interp_term d fuel' (mc_state full) (match_compile_term (CoreTm_RecordProj tm f))
                 = Inr v"
    by blast
qed

lemma sim_VariantProj:
  assumes IH: "term_sim fuel tm"
  shows "term_sim (Suc fuel) (CoreTm_VariantProj tm c)"
proof (rule term_simI)
  fix env storeTyping and full :: "'w InterpState" and ty' v
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_term_type env NotGhost (CoreTm_VariantProj tm c) = Some ty'"
    and ok: "core_term_match_scrutinees_ok (CoreTm_VariantProj tm c)"
    and ev: "interp_term d (Suc fuel) full (CoreTm_VariantProj tm c) = Inr v"
  from typing obtain dt tys where t: "core_term_type env NotGhost tm = Some (CoreTy_Datatype dt tys)"
    by (auto split: option.splits CoreType.splits)
  from ev obtain c' where w: "interp_term d fuel full tm = Inr (CV_Variant c' v)" and c_eq: "c' = c"
    by (auto split: sum.splits CoreValue.splits if_splits)
  from term_simD[OF IH fe fs sme wf t _ w] ok obtain f1 where
    f1: "interp_term d f1 (mc_state full) (match_compile_term tm) = Inr (CV_Variant c' v)" by auto
  have "interp_term d (Suc f1) (mc_state full) (match_compile_term (CoreTm_VariantProj tm c)) = Inr v"
    using f1 c_eq by simp
  thus "\<exists>fuel'. interp_term d fuel' (mc_state full) (match_compile_term (CoreTm_VariantProj tm c))
                 = Inr v"
    by blast
qed

lemma sim_Sizeof:
  assumes IH: "term_sim fuel tm"
  shows "term_sim (Suc fuel) (CoreTm_Sizeof tm)"
proof (rule term_simI)
  fix env storeTyping and full :: "'w InterpState" and ty' v
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_term_type env NotGhost (CoreTm_Sizeof tm) = Some ty'"
    and ok: "core_term_match_scrutinees_ok (CoreTm_Sizeof tm)"
    and ev: "interp_term d (Suc fuel) full (CoreTm_Sizeof tm) = Inr v"
  from typing obtain eTy dims where t: "core_term_type env NotGhost tm = Some (CoreTy_Array eTy dims)"
    by (auto split: option.splits CoreType.splits)
  from ev obtain sizes m where w: "interp_term d fuel full tm = Inr (CV_Array sizes m)"
    and v_eq: "v = array_size_to_value sizes"
    by (auto split: sum.splits CoreValue.splits)
  from term_simD[OF IH fe fs sme wf t _ w] ok obtain f1 where
    f1: "interp_term d f1 (mc_state full) (match_compile_term tm) = Inr (CV_Array sizes m)" by auto
  have "interp_term d (Suc f1) (mc_state full) (match_compile_term (CoreTm_Sizeof tm)) = Inr v"
    using f1 v_eq by simp
  thus "\<exists>fuel'. interp_term d fuel' (mc_state full) (match_compile_term (CoreTm_Sizeof tm)) = Inr v"
    by blast
qed


section \<open>Terms with several sub-evaluations\<close>

lemma sim_Binop:
  assumes IH1: "term_sim fuel tm1" and IH2: "term_sim fuel tm2"
  shows "term_sim (Suc fuel) (CoreTm_Binop op tm1 tm2)"
proof (rule term_simI)
  fix env storeTyping and full :: "'w InterpState" and ty' v
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_term_type env NotGhost (CoreTm_Binop op tm1 tm2) = Some ty'"
    and ok: "core_term_match_scrutinees_ok (CoreTm_Binop op tm1 tm2)"
    and ev: "interp_term d (Suc fuel) full (CoreTm_Binop op tm1 tm2) = Inr v"
  from typing obtain ty1 ty2 where t1: "core_term_type env NotGhost tm1 = Some ty1"
    and t2: "core_term_type env NotGhost tm2 = Some ty2"
    by (auto split: option.splits)
  from ok have ok1: "core_term_match_scrutinees_ok tm1" and ok2: "core_term_match_scrutinees_ok tm2"
    by simp_all
  from ev obtain w1 where w1: "interp_term d fuel full tm1 = Inr w1" by (auto split: sum.splits)
  from term_simD[OF IH1 fe fs sme wf t1 ok1 w1] obtain f1 where
    f1: "interp_term d f1 (mc_state full) (match_compile_term tm1) = Inr w1" by auto
  show "\<exists>fuel'. interp_term d fuel' (mc_state full) (match_compile_term (CoreTm_Binop op tm1 tm2)) = Inr v"
  proof (cases "short_circuit op w1")
    case (Some r)
    with ev w1 have "v = r" by simp
    hence "interp_term d (Suc f1) (mc_state full) (match_compile_term (CoreTm_Binop op tm1 tm2)) = Inr v"
      using f1 Some by simp
    thus ?thesis by blast
  next
    case None
    from ev w1 None obtain w2 where w2: "interp_term d fuel full tm2 = Inr w2"
      and r: "eval_binop op w1 w2 = Inr v"
      by (auto split: sum.splits)
    from term_simD[OF IH2 fe fs sme wf t2 ok2 w2] obtain f2 where
      f2: "interp_term d f2 (mc_state full) (match_compile_term tm2) = Inr w2" by auto
    let ?F = "max f1 f2"
    have f1': "interp_term d ?F (mc_state full) (match_compile_term tm1) = Inr w1"
      by (rule interp_term_Inr_more_fuel[OF f1]) simp
    have f2': "interp_term d ?F (mc_state full) (match_compile_term tm2) = Inr w2"
      by (rule interp_term_Inr_more_fuel[OF f2]) simp
    have "interp_term d (Suc ?F) (mc_state full) (match_compile_term (CoreTm_Binop op tm1 tm2)) = Inr v"
      using f1' f2' None r by simp
    thus ?thesis by blast
  qed
qed

lemma sim_Let:
  assumes IH: "\<And>tm. term_sim fuel tm"
  shows "term_sim (Suc fuel) (CoreTm_Let x rhs body)"
proof (rule term_simI)
  fix env storeTyping and full :: "'w InterpState" and ty v
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_term_type env NotGhost (CoreTm_Let x rhs body) = Some ty"
    and ok: "core_term_match_scrutinees_ok (CoreTm_Let x rhs body)"
    and ev: "interp_term d (Suc fuel) full (CoreTm_Let x rhs body) = Inr v"
  from typing obtain rhsTy where
    t_rhs: "core_term_type env NotGhost rhs = Some rhsTy" and
    t_body: "core_term_type (env \<lparr> TE_LocalVars := fmupd x rhsTy (TE_LocalVars env),
                                  TE_GhostLocals := fminus (TE_GhostLocals env) {|x|},
                                  TE_ConstLocals := finsert x (TE_ConstLocals env) \<rparr>)
                NotGhost body = Some ty"
    by (auto simp: Let_def split: option.splits)
  let ?env' = "env \<lparr> TE_LocalVars := fmupd x rhsTy (TE_LocalVars env),
                     TE_GhostLocals := fminus (TE_GhostLocals env) {|x|},
                     TE_ConstLocals := finsert x (TE_ConstLocals env) \<rparr>"
  from ok have ok_rhs: "core_term_match_scrutinees_ok rhs"
    and ok_body: "core_term_match_scrutinees_ok body" by simp_all
  from ev obtain w where w: "interp_term d fuel full rhs = Inr w"
    and body_ev: "interp_term d fuel (bind_const_local x w full) body = Inr v"
    by (auto simp: interp_term_Let split: sum.splits)
  from term_simD[OF IH fe fs sme wf t_rhs ok_rhs w] obtain f1 where
    f1: "interp_term d f1 (mc_state full) (match_compile_term rhs) = Inr w" by auto
  \<comment> \<open>The state after binding the variable matches the extended environment.\<close>
  have w_typed: "value_has_type env w (apply_subst (IS_TyArgs full) rhsTy)"
    using interp_term_sound[OF sme wf, THEN mp, OF t_rhs, of d fuel] w by simp
  obtain full1 addr where alloc_eq: "(full1, addr) = alloc_store full w"
    by (cases "alloc_store full w") auto
  let ?full'' = "full1 \<lparr> IS_Locals := fmupd x addr (IS_Locals full1),
                          IS_Refs := fmdrop x (IS_Refs full1),
                          IS_ConstLocals := finsert x (IS_ConstLocals full1) \<rparr>"
  have bind_eq: "bind_const_local x w full = ?full''"
    using alloc_eq by (simp add: case_prod_beta split: prod.splits)
  let ?env2 = "env \<lparr> TE_LocalVars := fmupd x rhsTy (TE_LocalVars env),
                     TE_ConstLocals := finsert x (TE_ConstLocals env) \<rparr>"
  have sme2: "state_matches_env ?full'' ?env2 (storeTyping @ [apply_subst (IS_TyArgs full) rhsTy])"
    by (rule state_matches_env_add_const_local[OF sme w_typed alloc_eq refl refl])
  have sme': "state_matches_env (bind_const_local x w full) ?env'
                (storeTyping @ [apply_subst (IS_TyArgs full) rhsTy])"
    unfolding bind_eq
  proof -
    have "state_matches_env s ?env' st = state_matches_env s ?env2 st" for s :: "'w InterpState" and st
      by (rule state_matches_env_cong_env) simp_all
    with sme2 show "state_matches_env ?full'' ?env' (storeTyping @ [apply_subst (IS_TyArgs full) rhsTy])"
      by simp
  qed
  have wf': "tyenv_well_formed ?env'"
    using tyenv_well_formed_declare_var[OF wf core_term_type_well_kinded[OF t_rhs wf],
            where g = NotGhost and var = x and c = "finsert x (TE_ConstLocals env)"]
          core_term_type_notghost_runtime[OF t_rhs wf]
    by simp
  have fe': "TE_Functions ?env' = TE_Functions genv" using fe by simp
  have fs': "IS_Functions (bind_const_local x w full) = funs" using fs by simp
  from term_simD[OF IH fe' fs' sme' wf' t_body ok_body body_ev] obtain f2 where
    f2: "interp_term d f2 (mc_state (bind_const_local x w full)) (match_compile_term body) = Inr v"
    by auto
  let ?F = "max f1 f2"
  have f1': "interp_term d ?F (mc_state full) (match_compile_term rhs) = Inr w"
    by (rule interp_term_Inr_more_fuel[OF f1]) simp
  have f2': "interp_term d ?F (bind_const_local x w (mc_state full)) (match_compile_term body) = Inr v"
    using interp_term_Inr_more_fuel[OF f2, of ?F] by simp
  have "interp_term d (Suc ?F) (mc_state full) (match_compile_term (CoreTm_Let x rhs body)) = Inr v"
    using f1' f2' by (simp add: interp_term_Let)
  thus "\<exists>fuel'. interp_term d fuel' (mc_state full) (match_compile_term (CoreTm_Let x rhs body)) = Inr v"
    by blast
qed

lemma sim_LitArray:
  assumes IH: "terms_sim fuel tms"
  shows "term_sim (Suc fuel) (CoreTm_LitArray eTy tms)"
proof (rule term_simI)
  fix env storeTyping and full :: "'w InterpState" and ty v
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_term_type env NotGhost (CoreTm_LitArray eTy tms) = Some ty"
    and ok: "core_term_match_scrutinees_ok (CoreTm_LitArray eTy tms)"
    and ev: "interp_term d (Suc fuel) full (CoreTm_LitArray eTy tms) = Inr v"
  from typing have t: "\<forall>tm \<in> set tms. \<exists>ty. core_term_type env NotGhost tm = Some ty"
    by (auto simp: list_all_iff split: if_splits)
  from ok have ok': "list_all core_term_match_scrutinees_ok tms" by simp
  from ev obtain vs where vs: "interp_term_list d fuel full tms = Inr vs"
    and v_eq: "v = make_1d_array vs"
    by (auto split: sum.splits)
  from terms_simD[OF IH fe fs sme wf t ok' vs] obtain f1 where
    f1: "interp_term_list d f1 (mc_state full) (map match_compile_term tms) = Inr vs" by auto
  have "interp_term d (Suc f1) (mc_state full) (match_compile_term (CoreTm_LitArray eTy tms)) = Inr v"
    using f1 v_eq by simp
  thus "\<exists>fuel'. interp_term d fuel' (mc_state full) (match_compile_term (CoreTm_LitArray eTy tms))
                 = Inr v"
    by blast
qed

lemma sim_Record:
  assumes IH: "terms_sim fuel (map snd flds)"
  shows "term_sim (Suc fuel) (CoreTm_Record flds)"
proof (rule term_simI)
  fix env storeTyping and full :: "'w InterpState" and ty v
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_term_type env NotGhost (CoreTm_Record flds) = Some ty"
    and ok: "core_term_match_scrutinees_ok (CoreTm_Record flds)"
    and ev: "interp_term d (Suc fuel) full (CoreTm_Record flds) = Inr v"
  from typing obtain tys where
    those: "those (map (\<lambda>(name, tm). core_term_type env NotGhost tm) flds) = Some tys"
    by (auto split: option.splits if_splits)
  from those_map_Some_all[OF those]
  have t: "\<forall>tm \<in> set (map snd flds). \<exists>ty. core_term_type env NotGhost tm = Some ty"
    by (auto simp: case_prod_unfold)
  from ok have ok': "list_all core_term_match_scrutinees_ok (map snd flds)"
    by (auto simp: list_all_iff)
  from ev obtain vs where vs: "interp_term_list d fuel full (map snd flds) = Inr vs"
    and v_eq: "v = CV_Record (zip (map fst flds) vs)"
    by (auto split: sum.splits)
  from terms_simD[OF IH fe fs sme wf t ok' vs] obtain f1 where
    f1: "interp_term_list d f1 (mc_state full) (map match_compile_term (map snd flds)) = Inr vs"
    by auto
  have "interp_term d (Suc f1) (mc_state full) (match_compile_term (CoreTm_Record flds)) = Inr v"
    using f1 v_eq by (simp add: case_prod_unfold comp_def)
  thus "\<exists>fuel'. interp_term d fuel' (mc_state full) (match_compile_term (CoreTm_Record flds)) = Inr v"
    by blast
qed

lemma sim_ArrayProj:
  assumes IH: "term_sim fuel arr" and IHs: "terms_sim fuel idxs"
  shows "term_sim (Suc fuel) (CoreTm_ArrayProj arr idxs)"
proof (rule term_simI)
  fix env storeTyping and full :: "'w InterpState" and ty v
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_term_type env NotGhost (CoreTm_ArrayProj arr idxs) = Some ty"
    and ok: "core_term_match_scrutinees_ok (CoreTm_ArrayProj arr idxs)"
    and ev: "interp_term d (Suc fuel) full (CoreTm_ArrayProj arr idxs) = Inr v"
  from typing obtain eTy dims where t: "core_term_type env NotGhost arr = Some (CoreTy_Array eTy dims)"
    and ti: "\<forall>tm \<in> set idxs. \<exists>ty. core_term_type env NotGhost tm = Some ty"
    by (auto simp: list_all_iff split: option.splits CoreType.splits if_splits)
  from ok have ok1: "core_term_match_scrutinees_ok arr"
    and ok2: "list_all core_term_match_scrutinees_ok idxs" by simp_all
  from ev obtain sizes m ivs where
    w: "interp_term d fuel full arr = Inr (CV_Array sizes m)" and
    ivs: "interp_term_list d fuel full idxs = Inr ivs" and
    rest: "(case interpret_index_vals ivs of
              Inr indices \<Rightarrow> (case fmlookup m indices of Some r \<Rightarrow> Inr r | None \<Rightarrow> Inl RuntimeError)
            | Inl err \<Rightarrow> Inl err) = Inr v"
    by (auto split: sum.splits CoreValue.splits)
  from term_simD[OF IH fe fs sme wf t ok1 w] obtain f1 where
    f1: "interp_term d f1 (mc_state full) (match_compile_term arr) = Inr (CV_Array sizes m)" by auto
  from terms_simD[OF IHs fe fs sme wf ti ok2 ivs] obtain f2 where
    f2: "interp_term_list d f2 (mc_state full) (map match_compile_term idxs) = Inr ivs" by auto
  let ?F = "max f1 f2"
  have f1': "interp_term d ?F (mc_state full) (match_compile_term arr) = Inr (CV_Array sizes m)"
    by (rule interp_term_Inr_more_fuel[OF f1]) simp
  have f2': "interp_term_list d ?F (mc_state full) (map match_compile_term idxs) = Inr ivs"
    by (rule interp_term_list_Inr_more_fuel[OF f2]) simp
  have "interp_term d (Suc ?F) (mc_state full) (match_compile_term (CoreTm_ArrayProj arr idxs)) = Inr v"
    using f1' f2' rest by simp
  thus "\<exists>fuel'. interp_term d fuel' (mc_state full) (match_compile_term (CoreTm_ArrayProj arr idxs))
                 = Inr v"
    by blast
qed

lemma sim_FunctionCall:
  assumes IH: "call_sim fuel fnName tyArgs args"
  shows "term_sim (Suc fuel) (CoreTm_FunctionCall fnName tyArgs args)"
proof (rule term_simI)
  fix env storeTyping and full :: "'w InterpState" and ty v
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_term_type env NotGhost (CoreTm_FunctionCall fnName tyArgs args) = Some ty"
    and ok: "core_term_match_scrutinees_ok (CoreTm_FunctionCall fnName tyArgs args)"
    and ev: "interp_term d (Suc fuel) full (CoreTm_FunctionCall fnName tyArgs args) = Inr v"
  from typing obtain funInfo where fi: "fmlookup (TE_Functions env) fnName = Some funInfo"
    by (auto split: option.splits)
  from funs_match_compilable_info[OF fmc fi[unfolded fe]]
  have ngp: "no_ghost_params funInfo" by simp
  let ?tySubst = "fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)"
  let ?expected = "map (\<lambda>(ty, _). apply_subst ?tySubst ty) (FI_TmArgs funInfo)"
  let ?modes = "map (\<lambda>(_, _, gh). param_mode NotGhost gh) (FI_TmArgs funInfo)"
  from typing fi have
    len_ty: "length tyArgs = length (FI_TyArgs funInfo)" and
    wk: "list_all (is_well_kinded env) tyArgs" and
    all_var: "list_all (\<lambda>(_, vor, _). vor = Var) (FI_TmArgs funInfo)" and
    len_args: "length args = length (FI_TmArgs funInfo)" and
    args_typed: "list_all2 (\<lambda>tm (expectedTy, mode). core_term_type env mode tm = Some expectedTy)
                   args (zip ?expected ?modes)"
    by (auto simp: Let_def split: if_splits)
  \<comment> \<open>No parameter is ghost, so every argument is typed in NotGhost mode.\<close>
  have modes: "?modes = replicate (length (FI_TmArgs funInfo)) NotGhost"
    using param_modes_no_ghost[OF ngp[unfolded no_ghost_params_def]] .

  have args_typed': "list_all2 (\<lambda>tm expectedTy. core_term_type env NotGhost tm = Some expectedTy)
                       args ?expected"
  proof (rule list_all2_all_nthI)
    show "length args = length ?expected" using len_args by simp
    fix i assume i_lt: "i < length args"
    hence i_lt_f: "i < length (FI_TmArgs funInfo)" using len_args by simp
    have "zip ?expected ?modes ! i = (?expected ! i, NotGhost)"
      using i_lt_f by (simp add: modes)
    with list_all2_nthD[OF args_typed i_lt]
    show "core_term_type env NotGhost (args ! i) = Some (?expected ! i)" by simp
  qed
  have refs: "\<forall>i < length args. fst (snd (FI_TmArgs funInfo ! i)) = Ref
                \<longrightarrow> is_writable_lvalue env (args ! i)"
  proof (intro allI impI)
    fix i assume "i < length args" and "fst (snd (FI_TmArgs funInfo ! i)) = Ref"
    with all_var len_args show "is_writable_lvalue env (args ! i)"
      by (auto simp: list_all_length case_prod_unfold)
  qed
  from ok have ok': "list_all core_term_match_scrutinees_ok args" by simp
  from ev have pure: "is_pure_fun full fnName" by (auto split: if_splits)
  from ev pure obtain newFull where
    call: "interp_function_call d fuel full fnName tyArgs args = Inr (newFull, v)"
    by (auto split: sum.splits)
  from call_simD[OF IH fe fs sme wf fi args_typed' len_ty wk refs ok' call] obtain f1 where
    f1: "interp_function_call d f1 (mc_state full) fnName tyArgs (map match_compile_term args)
           = Inr (mc_state newFull, v)" by auto
  have "interp_term d (Suc f1) (mc_state full)
          (match_compile_term (CoreTm_FunctionCall fnName tyArgs args)) = Inr v"
    using f1 pure by (simp split: option.splits)
  thus "\<exists>fuel'. interp_term d fuel' (mc_state full)
                  (match_compile_term (CoreTm_FunctionCall fnName tyArgs args)) = Inr v"
    by blast
qed


section \<open>Match terms\<close>

lemma sim_Match:
  assumes IH: "\<And>tm. term_sim fuel tm"
  shows "term_sim (Suc fuel) (CoreTm_Match scrut arms)"
proof (rule term_simI)
  fix env storeTyping and full :: "'w InterpState" and ty v
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_term_type env NotGhost (CoreTm_Match scrut arms) = Some ty"
    and ok: "core_term_match_scrutinees_ok (CoreTm_Match scrut arms)"
    and ev: "interp_term d (Suc fuel) full (CoreTm_Match scrut arms) = Inr v"
  let ?arms' = "map (\<lambda>(p, b). (p, match_compile_term b)) arms"
  from typing obtain scrutTy where s_ty: "core_term_type env NotGhost scrut = Some scrutTy"
    by (auto split: option.splits)
  from typing s_ty have
    ne: "arms \<noteq> []" and
    pats: "list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst arms)" and
    hd_ty: "core_term_type env NotGhost (snd (hd arms)) = Some ty" and
    tl_ty: "list_all (\<lambda>body. core_term_type env NotGhost body = Some ty) (tl (map snd arms))"
    by (auto simp: Let_def split: option.splits if_splits)
  have bodies: "core_term_type env NotGhost b = Some ty" if arm_in: "(p, b) \<in> set arms" for p b
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
  from ok have ok_s: "core_term_match_scrutinees_ok scrut"
    and ok_arms: "list_all (\<lambda>(_, body). core_term_match_scrutinees_ok body) arms"
    and var_or_flat: "arms_flat arms \<or> (\<exists>x. scrut = CoreTm_Var x)" by simp_all
  from ev obtain sv body where
    sv: "interp_term d fuel full scrut = Inr sv" and
    arm: "find_matching_arm sv arms = Inr body" and
    body_ev: "interp_term d fuel full body = Inr v"
    by (auto split: sum.splits)
  from find_matching_arm_in_arms[OF arm] obtain p where arm_in: "(p, body) \<in> set arms" by auto
  have t_body: "core_term_type env NotGhost body = Some ty" by (rule bodies[OF arm_in])
  from ok_arms arm_in have ok_body: "core_term_match_scrutinees_ok body" by (auto simp: list_all_iff)
  from term_simD[OF IH fe fs sme wf t_body ok_body body_ev] obtain f2 where
    f2: "interp_term d f2 (mc_state full) (match_compile_term body) = Inr v" by auto
  show "\<exists>fuel'. interp_term d fuel' (mc_state full) (match_compile_term (CoreTm_Match scrut arms)) = Inr v"
  proof (cases "arms_flat arms")
    case True
    \<comment> \<open>The match is kept; only its scrutinee and arm bodies are compiled.\<close>
    from term_simD[OF IH fe fs sme wf s_ty ok_s sv] obtain f1 where
      f1: "interp_term d f1 (mc_state full) (match_compile_term scrut) = Inr sv" by auto
    let ?F = "max f1 f2"
    have f1': "interp_term d ?F (mc_state full) (match_compile_term scrut) = Inr sv"
      by (rule interp_term_Inr_more_fuel[OF f1]) simp
    have f2': "interp_term d ?F (mc_state full) (match_compile_term body) = Inr v"
      by (rule interp_term_Inr_more_fuel[OF f2]) simp
    have arm': "find_matching_arm sv ?arms' = Inr (match_compile_term body)"
      by (rule find_matching_arm_map[OF arm])
    have "interp_term d (Suc ?F) (mc_state full) (CoreTm_Match (match_compile_term scrut) ?arms') = Inr v"
      using f1' arm' f2' by simp
    hence "interp_term d (Suc ?F) (mc_state full) (match_compile_term (CoreTm_Match scrut arms)) = Inr v"
      using True by (simp add: Let_def)
    thus ?thesis by blast
  next
    case False
    \<comment> \<open>The match is compiled. Its scrutinee is a variable, whose value the
       compiled tree tests; the tree picks the arm the original match picks.\<close>
    with var_or_flat obtain x where scrut_eq: "scrut = CoreTm_Var x" by auto
    have ne': "?arms' \<noteq> []" using ne by simp
    have pats': "list_all (\<lambda>(p, _). pattern_compatible env p scrutTy) ?arms'"
      using pats by (auto simp: list_all_iff)
    from sv scrut_eq obtain n where sv': "interp_term d (Suc n) full (CoreTm_Var x) = Inr sv"
      by (cases fuel) auto
    have s_ty': "core_term_type env NotGhost (CoreTm_Var x) = Some scrutTy"
      using s_ty scrut_eq by simp
    have tree: "match_tree_eval (var_env full) (compile_match_tree (CoreTm_Var x) ?arms')
                  = arms_first_match sv ?arms'"
      by (rule compile_match_tree_eval[OF sme wf s_ty' pats' ne' sv'])
    have "arms_first_match sv ?arms' = Some (match_compile_term body)"
      unfolding arms_first_match_find_matching_arm find_matching_arm_map[OF arm] by simp
    with tree have tree': "match_tree_eval (var_env (mc_state full))
                             (compile_match_tree (CoreTm_Var x) ?arms') = Some (match_compile_term body)"
      by simp
    from match_tree_to_term_eval[OF tree' f2] obtain f3 where
      "interp_term d f3 (mc_state full)
         (match_tree_to_term (compile_match_tree (CoreTm_Var x) ?arms')) = Inr v" by blast
    hence "interp_term d f3 (mc_state full) (match_compile_term (CoreTm_Match scrut arms)) = Inr v"
      using False scrut_eq by (simp add: compile_match_term_def Let_def)
    thus ?thesis by blast
  qed
qed
section \<open>Term lists\<close>

lemma sim_terms_Nil: "terms_sim (Suc fuel) []"
proof (rule terms_simI)
  fix full :: "'w InterpState" and vs
  assume "interp_term_list d (Suc fuel) full [] = Inr vs"
  hence "interp_term_list d (Suc fuel) (mc_state full) (map match_compile_term []) = Inr vs" by simp
  thus "\<exists>fuel'. interp_term_list d fuel' (mc_state full) (map match_compile_term []) = Inr vs" by blast
qed

lemma sim_terms_Cons:
  assumes IH: "term_sim fuel tm" and IHs: "terms_sim fuel tms"
  shows "terms_sim (Suc fuel) (tm # tms)"
proof (rule terms_simI)
  fix env storeTyping and full :: "'w InterpState" and vs
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "\<forall>tm \<in> set (tm # tms). \<exists>ty. core_term_type env NotGhost tm = Some ty"
    and ok: "list_all core_term_match_scrutinees_ok (tm # tms)"
    and ev: "interp_term_list d (Suc fuel) full (tm # tms) = Inr vs"
  from typing obtain ty where t: "core_term_type env NotGhost tm = Some ty" by auto
  from typing have ts: "\<forall>tm \<in> set tms. \<exists>ty. core_term_type env NotGhost tm = Some ty" by auto
  from ok have ok1: "core_term_match_scrutinees_ok tm" and oks: "list_all core_term_match_scrutinees_ok tms"
    by simp_all
  from ev obtain v vs' where v: "interp_term d fuel full tm = Inr v"
    and vs': "interp_term_list d fuel full tms = Inr vs'" and vs_eq: "vs = v # vs'"
    by (auto split: sum.splits)
  from term_simD[OF IH fe fs sme wf t ok1 v] obtain f1 where
    f1: "interp_term d f1 (mc_state full) (match_compile_term tm) = Inr v" by auto
  from terms_simD[OF IHs fe fs sme wf ts oks vs'] obtain f2 where
    f2: "interp_term_list d f2 (mc_state full) (map match_compile_term tms) = Inr vs'" by auto
  let ?F = "max f1 f2"
  have f1': "interp_term d ?F (mc_state full) (match_compile_term tm) = Inr v"
    by (rule interp_term_Inr_more_fuel[OF f1]) simp
  have f2': "interp_term_list d ?F (mc_state full) (map match_compile_term tms) = Inr vs'"
    by (rule interp_term_list_Inr_more_fuel[OF f2]) simp
  have "interp_term_list d (Suc ?F) (mc_state full) (map match_compile_term (tm # tms)) = Inr vs"
    using f1' f2' vs_eq by simp
  thus "\<exists>fuel'. interp_term_list d fuel' (mc_state full) (map match_compile_term (tm # tms)) = Inr vs"
    by blast
qed


section \<open>Lvalues\<close>

lemma sim_lvalue:
  assumes IH: "\<And>tm. lvalue_sim fuel tm" and IHs: "\<And>tms. terms_sim fuel tms"
  shows "lvalue_sim (Suc fuel) tm"
proof (rule lvalue_simI)
  fix env storeTyping and full :: "'w InterpState" and ty r
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_term_type env NotGhost tm = Some ty"
    and ok: "core_term_match_scrutinees_ok tm"
    and ev: "interp_writable_lvalue d (Suc fuel) full tm = Inr r"
  show "\<exists>fuel'. interp_writable_lvalue d fuel' (mc_state full) (match_compile_term tm) = Inr r"
  proof (cases tm)
    case (CoreTm_Var x)
    with ev have "interp_writable_lvalue d (Suc fuel) (mc_state full) (match_compile_term tm) = Inr r"
      by (simp split: option.splits if_splits)
    thus ?thesis by blast
  next
    case (CoreTm_RecordProj tm' f)
    from typing CoreTm_RecordProj obtain fTys where
      t: "core_term_type env NotGhost tm' = Some (CoreTy_Record fTys)"
      by (auto split: option.splits CoreType.splits)
    from ok CoreTm_RecordProj have ok': "core_term_match_scrutinees_ok tm'" by simp
    from ev CoreTm_RecordProj obtain addr path where
      r': "interp_writable_lvalue d fuel full tm' = Inr (addr, path)" and
      r_eq: "r = (addr, path @ [LVPath_RecordProj f])"
      by (auto split: sum.splits)
    from lvalue_simD[OF IH fe fs sme wf t ok' r'] obtain f1 where
      f1: "interp_writable_lvalue d f1 (mc_state full) (match_compile_term tm') = Inr (addr, path)" by auto
    have "interp_writable_lvalue d (Suc f1) (mc_state full) (match_compile_term tm) = Inr r"
      using f1 r_eq CoreTm_RecordProj by simp
    thus ?thesis by blast
  next
    case (CoreTm_VariantProj tm' c)
    from typing CoreTm_VariantProj obtain dt tys where
      t: "core_term_type env NotGhost tm' = Some (CoreTy_Datatype dt tys)"
      by (auto split: option.splits CoreType.splits)
    from ok CoreTm_VariantProj have ok': "core_term_match_scrutinees_ok tm'" by simp
    from ev CoreTm_VariantProj obtain addr path where
      r': "interp_writable_lvalue d fuel full tm' = Inr (addr, path)" and
      r_eq: "r = (addr, path @ [LVPath_VariantProj c])"
      by (auto split: sum.splits)
    from lvalue_simD[OF IH fe fs sme wf t ok' r'] obtain f1 where
      f1: "interp_writable_lvalue d f1 (mc_state full) (match_compile_term tm') = Inr (addr, path)" by auto
    have "interp_writable_lvalue d (Suc f1) (mc_state full) (match_compile_term tm) = Inr r"
      using f1 r_eq CoreTm_VariantProj by simp
    thus ?thesis by blast
  next
    case (CoreTm_ArrayProj tm' idxs)
    from typing CoreTm_ArrayProj obtain eTy dims where
      t: "core_term_type env NotGhost tm' = Some (CoreTy_Array eTy dims)" and
      ti: "\<forall>i \<in> set idxs. \<exists>ty. core_term_type env NotGhost i = Some ty"
      by (auto simp: list_all_iff split: option.splits CoreType.splits if_splits)
    from ok CoreTm_ArrayProj have ok': "core_term_match_scrutinees_ok tm'"
      and oki: "list_all core_term_match_scrutinees_ok idxs" by simp_all
    from ev CoreTm_ArrayProj obtain addr path ivs indices where
      r': "interp_writable_lvalue d fuel full tm' = Inr (addr, path)" and
      ivs: "interp_term_list d fuel full idxs = Inr ivs" and
      ind: "interpret_index_vals ivs = Inr indices" and
      r_eq: "r = (addr, path @ [LVPath_ArrayProj indices])"
      by (auto split: sum.splits)
    from lvalue_simD[OF IH fe fs sme wf t ok' r'] obtain f1 where
      f1: "interp_writable_lvalue d f1 (mc_state full) (match_compile_term tm') = Inr (addr, path)" by auto
    from terms_simD[OF IHs fe fs sme wf ti oki ivs] obtain f2 where
      f2: "interp_term_list d f2 (mc_state full) (map match_compile_term idxs) = Inr ivs" by auto
    let ?F = "max f1 f2"
    have f1': "interp_writable_lvalue d ?F (mc_state full) (match_compile_term tm') = Inr (addr, path)"
      by (rule interp_writable_lvalue_Inr_more_fuel[OF f1]) simp
    have f2': "interp_term_list d ?F (mc_state full) (map match_compile_term idxs) = Inr ivs"
      by (rule interp_term_list_Inr_more_fuel[OF f2]) simp
    have "interp_writable_lvalue d (Suc ?F) (mc_state full) (match_compile_term tm) = Inr r"
      using f1' f2' ind r_eq CoreTm_ArrayProj by simp
    thus ?thesis by blast
  next
    case (CoreTm_Cast cty tm')
    from typing CoreTm_Cast obtain opTy where t: "core_term_type env NotGhost tm' = Some opTy"
      by (auto split: option.splits if_splits)
    from ok CoreTm_Cast have ok': "core_term_match_scrutinees_ok tm'" by simp
    from ev CoreTm_Cast obtain eTy dims addr path where
      cty_eq: "cty = CoreTy_Array eTy dims" and
      r': "interp_writable_lvalue d fuel full tm' = Inr (addr, path)" and
      r_eq: "r = (addr, path @ [LVPath_ArrayCast dims])"
      by (auto split: CoreType.splits sum.splits)
    from lvalue_simD[OF IH fe fs sme wf t ok' r'] obtain f1 where
      f1: "interp_writable_lvalue d f1 (mc_state full) (match_compile_term tm') = Inr (addr, path)" by auto
    have "interp_writable_lvalue d (Suc f1) (mc_state full) (match_compile_term tm) = Inr r"
      using f1 r_eq CoreTm_Cast cty_eq by simp
    thus ?thesis by blast
  qed (use ev in simp_all)
qed

end

end
