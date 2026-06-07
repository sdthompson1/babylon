theory ExtendEnvWithTyvars
  imports CoreStmtTypecheck
begin

(* Extend a type environment with a half-open range of type variables.
   In NotGhost mode, the new vars are assumed to represent runtime types (they are
   added to TE_RuntimeTypeVars); in Ghost mode, they can represent any type. *)
definition extend_env_with_tyvars :: "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> CoreTyEnv" where
  "extend_env_with_tyvars env ghost lo hi =
     env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list [lo..<hi],
           TE_RuntimeTypeVars := (if ghost = NotGhost
                                   then TE_RuntimeTypeVars env |\<union>| fset_of_list [lo..<hi]
                                   else TE_RuntimeTypeVars env) \<rparr>"

(* Identity: when the interval is empty, the env is unchanged. *)
lemma extend_env_with_tyvars_empty [simp]:
  assumes "lo \<ge> hi"
  shows "extend_env_with_tyvars env ghost lo hi = env"
  using assms unfolding extend_env_with_tyvars_def by simp

(* Splitting a contiguous interval of fresh type variables. *)
lemma fset_of_list_upt_split:
  assumes "lo \<le> mid" and "mid \<le> hi"
  shows "fset_of_list [lo..<mid] |\<union>| fset_of_list [mid..<hi] = fset_of_list [lo..<hi]"
proof -
  have "[lo..<hi] = [lo..<mid] @ [mid..<hi]"
    using assms le_Suc_ex upt_add_eq_append by blast
  thus ?thesis by simp
qed

(* Helper: extend_env_with_tyvars with a wider interval can be viewed as extending
   the narrower version further. Used to lift well-kindedness / runtime facts. *)
lemma extend_env_with_tyvars_widen_eq:
  assumes "lo' \<le> lo" and "hi \<le> hi'"
  shows "\<exists>extraTV extraRT. extend_env_with_tyvars env ghost lo' hi' =
           (extend_env_with_tyvars env ghost lo hi)
             \<lparr> TE_TypeVars := TE_TypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| extraTV,
               TE_RuntimeTypeVars := TE_RuntimeTypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| extraRT \<rparr>"
proof -
  let ?diff = "fset_of_list [lo'..<hi'] |-| fset_of_list [lo..<hi]"
  have contained: "fset_of_list [lo..<hi] |\<subseteq>| fset_of_list [lo'..<hi']"
    using assms by (auto simp: fset_of_list_elem)
  have union_eq: "fset_of_list [lo..<hi] |\<union>| ?diff = fset_of_list [lo'..<hi']"
    using contained by auto
  show ?thesis
  proof (cases "ghost = NotGhost")
    case True
    have "extend_env_with_tyvars env ghost lo' hi' =
            (extend_env_with_tyvars env ghost lo hi)
              \<lparr> TE_TypeVars := TE_TypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| ?diff,
                TE_RuntimeTypeVars := TE_RuntimeTypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| ?diff \<rparr>"
      unfolding extend_env_with_tyvars_def using True union_eq by (simp add: funion_assoc)
    thus ?thesis by blast
  next
    case False
    have "extend_env_with_tyvars env ghost lo' hi' =
            (extend_env_with_tyvars env ghost lo hi)
              \<lparr> TE_TypeVars := TE_TypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| ?diff,
                TE_RuntimeTypeVars := TE_RuntimeTypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| {||} \<rparr>"
      unfolding extend_env_with_tyvars_def using False union_eq by (simp add: funion_assoc)
    thus ?thesis by blast
  qed
qed

(* is_well_kinded is preserved when widening the type-variable interval *)
lemma is_well_kinded_extend_env_with_tyvars_mono:
  assumes "is_well_kinded (extend_env_with_tyvars env ghost lo hi) ty"
    and "lo' \<le> lo" and "hi \<le> hi'"
  shows "is_well_kinded (extend_env_with_tyvars env ghost lo' hi') ty"
proof -
  obtain extraTV extraRT where env_eq:
    "extend_env_with_tyvars env ghost lo' hi' =
       (extend_env_with_tyvars env ghost lo hi)
         \<lparr> TE_TypeVars := TE_TypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| extraTV,
           TE_RuntimeTypeVars := TE_RuntimeTypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| extraRT \<rparr>"
    using extend_env_with_tyvars_widen_eq[OF assms(2,3)] by blast
  show ?thesis
    using assms(1) is_well_kinded_extend_tyvars by (simp add: env_eq)
qed

(* is_runtime_type is preserved when widening the type-variable interval *)
lemma is_runtime_type_extend_env_with_tyvars_mono:
  assumes "is_runtime_type (extend_env_with_tyvars env ghost lo hi) ty"
    and "lo' \<le> lo" and "hi \<le> hi'"
  shows "is_runtime_type (extend_env_with_tyvars env ghost lo' hi') ty"
proof -
  obtain extraTV extraRT where env_eq:
    "extend_env_with_tyvars env ghost lo' hi' =
       (extend_env_with_tyvars env ghost lo hi)
         \<lparr> TE_TypeVars := TE_TypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| extraTV,
           TE_RuntimeTypeVars := TE_RuntimeTypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| extraRT \<rparr>"
    using extend_env_with_tyvars_widen_eq[OF assms(2,3)] by blast
  show ?thesis
    using assms(1) is_runtime_type_extend_runtime_tyvars by (simp add: env_eq)
qed

(* Well-formedness is preserved under extend_env_with_tyvars. *)
lemma tyenv_well_formed_extend_env_with_tyvars:
  assumes "tyenv_well_formed env"
  shows "tyenv_well_formed (extend_env_with_tyvars env ghost lo hi)"
proof (cases "ghost = NotGhost")
  case True
  thus ?thesis
    using assms tyenv_well_formed_extend_tyvars[where extraTV="fset_of_list [lo..<hi]"
                                                    and extraRT="fset_of_list [lo..<hi]"]
    unfolding extend_env_with_tyvars_def by simp
next
  case False
  have "tyenv_well_formed (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list [lo..<hi],
                                  TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| {||} \<rparr>)"
    using assms tyenv_well_formed_extend_tyvars[where extraTV="fset_of_list [lo..<hi]"
                                                    and extraRT="{||}"] by blast
  thus ?thesis using False unfolding extend_env_with_tyvars_def by simp
qed


(* ========================================================================== *)
(* Interval widening for the core typecheck functions                         *)
(*                                                                            *)
(* Widening the half-open interval [lo, hi) of fresh type variables outward    *)
(* preserves what core_term_type / core_statement_type accept. Both rest on    *)
(* the irrelevant-tyvar lemmas: the wider env is the narrower one with the     *)
(* extra interval added, and those lemmas say that addition is harmless.       *)
(* These live here (rather than in the typecheck theories) because they are    *)
(* phrased with extend_env_with_tyvars, which is defined in this theory.       *)
(* ========================================================================== *)

(* The wider extend_env_with_tyvars is the narrower one with the extra interval
   added to the tyvar sets (and, in NotGhost mode, the runtime tyvars too). *)
lemma extend_env_with_tyvars_widen_as_irrelevant:
  assumes "lo' \<le> lo" and "hi \<le> hi'"
  shows "extend_env_with_tyvars env ghost lo' hi' =
           (extend_env_with_tyvars env ghost lo hi)
             \<lparr> TE_TypeVars := TE_TypeVars (extend_env_with_tyvars env ghost lo hi)
                                |\<union>| (fset_of_list [lo'..<hi'] |-| fset_of_list [lo..<hi]),
               TE_RuntimeTypeVars := TE_RuntimeTypeVars (extend_env_with_tyvars env ghost lo hi)
                                |\<union>| (if ghost = NotGhost
                                     then fset_of_list [lo'..<hi'] |-| fset_of_list [lo..<hi]
                                     else {||}) \<rparr>"
proof -
  let ?diff = "fset_of_list [lo'..<hi'] |-| fset_of_list [lo..<hi]"
  have contained: "fset_of_list [lo..<hi] |\<subseteq>| fset_of_list [lo'..<hi']"
    using assms by (auto simp: fset_of_list_elem)
  have union_eq: "fset_of_list [lo..<hi] |\<union>| ?diff = fset_of_list [lo'..<hi']"
    using contained by auto
  show ?thesis
    unfolding extend_env_with_tyvars_def
    using union_eq by (cases "ghost = NotGhost") (auto simp: funion_assoc)
qed

(* Weakening: extending the interval further preserves core_term_type.
   Both endpoints may move outward (lo' \<le> lo, hi' \<ge> hi). *)
lemma core_term_type_extend_env_with_tyvars_mono:
  assumes "core_term_type (extend_env_with_tyvars env ghost lo hi) ghost tm = Some ty"
    and "lo' \<le> lo" and "hi \<le> hi'"
  shows "core_term_type (extend_env_with_tyvars env ghost lo' hi') ghost tm = Some ty"
  using assms(1) core_term_type_irrelevant_tyvar
  by (simp add: extend_env_with_tyvars_widen_as_irrelevant[OF assms(2,3)])

(* Impure-call version: widening the fresh interval preserves core_impure_call_type. *)
lemma core_impure_call_type_extend_env_with_tyvars_mono:
  assumes "core_impure_call_type (extend_env_with_tyvars env ghost lo hi) ghost fnName tyArgs argTms = Some ty"
    and "lo' \<le> lo" and "hi \<le> hi'"
  shows "core_impure_call_type (extend_env_with_tyvars env ghost lo' hi') ghost fnName tyArgs argTms = Some ty"
  using assms(1) core_impure_call_type_irrelevant_tyvar
  by (simp add: extend_env_with_tyvars_widen_as_irrelevant[OF assms(2,3)])

(* Statement version: widening the interval preserves core_statement_type and
   carries the result environment through the same widening. *)
lemma core_statement_type_extend_env_with_tyvars_mono:
  assumes "core_statement_type (extend_env_with_tyvars env ghost lo hi) g stmt
             = Some (extend_env_with_tyvars env_out ghost lo hi)"
    and "TE_TypeVars env_out = TE_TypeVars env"
    and "TE_RuntimeTypeVars env_out = TE_RuntimeTypeVars env"
    and "lo' \<le> lo" and "hi \<le> hi'"
  shows "core_statement_type (extend_env_with_tyvars env ghost lo' hi') g stmt
           = Some (extend_env_with_tyvars env_out ghost lo' hi')"
proof -
  let ?diff = "fset_of_list [lo'..<hi'] |-| fset_of_list [lo..<hi]"
  let ?dRT = "if ghost = NotGhost then ?diff else {||}"
  \<comment> \<open>Source and target envs differ only by the extra interval, on both env and env_out.\<close>
  have src: "extend_env_with_tyvars env ghost lo' hi' =
               (extend_env_with_tyvars env ghost lo hi)
                 \<lparr> TE_TypeVars := TE_TypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| ?diff,
                   TE_RuntimeTypeVars := TE_RuntimeTypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| ?dRT \<rparr>"
    using extend_env_with_tyvars_widen_as_irrelevant[OF assms(4,5)] .
  have tgt: "extend_env_with_tyvars env_out ghost lo' hi' =
               (extend_env_with_tyvars env_out ghost lo hi)
                 \<lparr> TE_TypeVars := TE_TypeVars (extend_env_with_tyvars env_out ghost lo hi) |\<union>| ?diff,
                   TE_RuntimeTypeVars := TE_RuntimeTypeVars (extend_env_with_tyvars env_out ghost lo hi) |\<union>| ?dRT \<rparr>"
    using extend_env_with_tyvars_widen_as_irrelevant[OF assms(4,5)] .
  from core_statement_type_irrelevant_tyvar[OF assms(1), where extraTV = ?diff and extraRT = ?dRT]
  show ?thesis
    by (simp add: src tgt)
qed

(* Statement-list version of the interval-widening lemma. *)
lemma core_statement_list_type_extend_env_with_tyvars_mono:
  assumes "core_statement_list_type (extend_env_with_tyvars env ghost lo hi) g stmts
             = Some (extend_env_with_tyvars env_out ghost lo hi)"
    and "lo' \<le> lo" and "hi \<le> hi'"
  shows "core_statement_list_type (extend_env_with_tyvars env ghost lo' hi') g stmts
           = Some (extend_env_with_tyvars env_out ghost lo' hi')"
proof -
  let ?diff = "fset_of_list [lo'..<hi'] |-| fset_of_list [lo..<hi]"
  let ?dRT = "if ghost = NotGhost then ?diff else {||}"
  have src: "extend_env_with_tyvars env ghost lo' hi' =
               (extend_env_with_tyvars env ghost lo hi)
                 \<lparr> TE_TypeVars := TE_TypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| ?diff,
                   TE_RuntimeTypeVars := TE_RuntimeTypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| ?dRT \<rparr>"
    using extend_env_with_tyvars_widen_as_irrelevant[OF assms(2,3)] .
  have tgt: "extend_env_with_tyvars env_out ghost lo' hi' =
               (extend_env_with_tyvars env_out ghost lo hi)
                 \<lparr> TE_TypeVars := TE_TypeVars (extend_env_with_tyvars env_out ghost lo hi) |\<union>| ?diff,
                   TE_RuntimeTypeVars := TE_RuntimeTypeVars (extend_env_with_tyvars env_out ghost lo hi) |\<union>| ?dRT \<rparr>"
    using extend_env_with_tyvars_widen_as_irrelevant[OF assms(2,3)] .
  from core_statement_list_type_irrelevant_tyvar[OF assms(1), where extraTV = ?diff and extraRT = ?dRT]
  show ?thesis
    by (simp add: src tgt)
qed

(* extend_env_with_tyvars commutes with local-variable record updates: it only
   touches the tyvar sets, so updates to TE_LocalVars / TE_GhostLocals /
   TE_ConstLocals / TE_ProofGoal / TE_ProofTopLevel pass through unchanged. *)
lemma extend_env_with_tyvars_TE_LocalVars_commute:
  "extend_env_with_tyvars
      (env \<lparr> TE_LocalVars := lv, TE_GhostLocals := gl, TE_ConstLocals := cl \<rparr>) ghost lo hi
   = (extend_env_with_tyvars env ghost lo hi)
        \<lparr> TE_LocalVars := lv, TE_GhostLocals := gl, TE_ConstLocals := cl \<rparr>"
  unfolding extend_env_with_tyvars_def by simp

end
