theory UnifyCompose
  imports Unify3
begin

section \<open>Unify-and-compose\<close>

(* try_unify_compose is the specific kind of unification the elaborator
   performs: unify two types under the accumulator substitution, treating
   exactly the env-fixed type variables (TE_TypeVars env) as rigid, and
   compose the resulting substitution back on top of the accumulator.
   The flex predicate is "env-baked" on purpose -- it expresses the
   elaborator's fixed policy, unlike the general unify in Unify1-3 which
   takes is_flex as a parameter. Returns None on failure. *)
definition try_unify_compose ::
  "CoreTyEnv \<Rightarrow> CoreType \<Rightarrow> CoreType \<Rightarrow> TypeSubst \<Rightarrow> TypeSubst option" where
  "try_unify_compose env actualTy expectedTy accSubst =
    (let a = apply_subst accSubst actualTy;
         e = apply_subst accSubst expectedTy in
     case unify (\<lambda>n. n |\<notin>| TE_TypeVars env) a e of
       None \<Rightarrow> None
     | Some s \<Rightarrow> Some (compose_subst s accSubst))"

(* try_unify_compose, when successful, returns a substitution of compose-shape
   on top of accSubst, and that substitution makes actualTy and expectedTy equal. *)
lemma try_unify_compose_correct:
  assumes "try_unify_compose env actualTy expectedTy accSubst = Some s'"
  shows "(\<exists>s. s' = compose_subst s accSubst)
       \<and> apply_subst s' actualTy = apply_subst s' expectedTy"
proof -
  from assms obtain s where
    unif: "unify (\<lambda>n. n |\<notin>| TE_TypeVars env)
            (apply_subst accSubst actualTy) (apply_subst accSubst expectedTy) = Some s" and
    s'_eq: "s' = compose_subst s accSubst"
    unfolding try_unify_compose_def by (auto simp: Let_def split: option.splits)
  have "apply_subst s (apply_subst accSubst actualTy)
         = apply_subst s (apply_subst accSubst expectedTy)"
    using unify_sound[OF unif] .
  hence eq: "apply_subst s' actualTy = apply_subst s' expectedTy"
    using s'_eq by (simp add: compose_subst_correct)
  show ?thesis using s'_eq eq by blast
qed

lemma try_unify_compose_makes_equal:
  assumes "try_unify_compose env actualTy expectedTy accSubst = Some s'"
  shows "apply_subst s' actualTy = apply_subst s' expectedTy"
  using try_unify_compose_correct[OF assms] by simp

lemma try_unify_compose_compose_shape:
  assumes "try_unify_compose env actualTy expectedTy accSubst = Some s'"
  shows "\<exists>s. s' = compose_subst s accSubst"
  using try_unify_compose_correct[OF assms] by simp

(* compose_subst chains: if A = compose_subst T1 B and B = compose_subst T2 C,
   then A = compose_subst (compose_subst T1 T2) C. *)
lemma compose_subst_chain_exists:
  assumes "\<exists>T. b = compose_subst T c"
      and "\<exists>T. a = compose_subst T b"
  shows "\<exists>T. a = compose_subst T c"
  using assms compose_subst_assoc by metis

(* Factoring relation between substitutions. subst' "factors through" subst
   if applying subst before subst' is the same as just applying subst'.
   This is the precise way the elaborator's accSubst chain refines: each later
   accSubst' subsumes the effect of the earlier accSubst. *)
definition subst_factors_through :: "TypeSubst \<Rightarrow> TypeSubst \<Rightarrow> bool" where
  "subst_factors_through subst' subst =
     (\<forall>ty. apply_subst subst' (apply_subst subst ty) = apply_subst subst' ty)"

(* Reflexive: any subst factors through fmempty. *)
lemma subst_factors_through_fmempty:
  "subst_factors_through subst fmempty"
  unfolding subst_factors_through_def by simp

(* Transitive composition: if subst1 factors through subst0 and
   subst2 = compose_subst T subst1, then subst2 factors through subst0. *)
lemma subst_factors_through_compose:
  assumes "subst_factors_through subst1 subst0"
      and "subst2 = compose_subst T subst1"
  shows "subst_factors_through subst2 subst0"
proof -
  have "\<And>ty. apply_subst subst2 (apply_subst subst0 ty) = apply_subst subst2 ty"
  proof -
    fix ty
    have "apply_subst subst2 (apply_subst subst0 ty)
          = apply_subst T (apply_subst subst1 (apply_subst subst0 ty))"
      using assms(2) by (simp add: compose_subst_correct)
    also have "\<dots> = apply_subst T (apply_subst subst1 ty)"
      using assms(1) unfolding subst_factors_through_def by simp
    also have "\<dots> = apply_subst subst2 ty"
      using assms(2) by (simp add: compose_subst_correct)
    finally show "apply_subst subst2 (apply_subst subst0 ty) = apply_subst subst2 ty" .
  qed
  thus ?thesis unfolding subst_factors_through_def by blast
qed

(* Try_unify_compose result factors through input accSubst. *)
lemma try_unify_compose_factors_through:
  assumes "try_unify_compose env actualTy expectedTy accSubst = Some s'"
      and "subst_factors_through accSubst accSubst"  \<comment> \<open>accSubst is idempotent\<close>
  shows "subst_factors_through s' accSubst"
proof -
  from assms(1) obtain s where
    unif: "unify (\<lambda>n. n |\<notin>| TE_TypeVars env)
            (apply_subst accSubst actualTy) (apply_subst accSubst expectedTy) = Some s" and
    s'_eq: "s' = compose_subst s accSubst"
    unfolding try_unify_compose_def by (auto simp: Let_def split: option.splits)
  \<comment> \<open>s is itself a unifier of the equation; by unify_mgu, any unifier (including s)
      factors through s. Apply with subst' = s gives idempotence of s. \<close>
  have s_unifies:
    "apply_subst s (apply_subst accSubst actualTy) = apply_subst s (apply_subst accSubst expectedTy)"
    using unify_sound[OF unif] .
  \<comment> \<open>For any ty: apply_subst s' (apply_subst accSubst ty)
        = apply_subst s (apply_subst accSubst (apply_subst accSubst ty))
        = apply_subst s (apply_subst accSubst ty)  (by accSubst idempotence)
        = apply_subst s' ty. \<close>
  have "\<And>ty. apply_subst s' (apply_subst accSubst ty) = apply_subst s' ty"
  proof -
    fix ty
    have "apply_subst s' (apply_subst accSubst ty)
          = apply_subst s (apply_subst accSubst (apply_subst accSubst ty))"
      using s'_eq by (simp add: compose_subst_correct)
    also have "\<dots> = apply_subst s (apply_subst accSubst ty)"
      using assms(2) unfolding subst_factors_through_def by simp
    also have "\<dots> = apply_subst s' ty"
      using s'_eq by (simp add: compose_subst_correct)
    finally show "apply_subst s' (apply_subst accSubst ty) = apply_subst s' ty" .
  qed
  thus ?thesis unfolding subst_factors_through_def by blast
qed

(* Try_unify_compose result is idempotent if accSubst was. *)
lemma try_unify_compose_idem:
  assumes "try_unify_compose env actualTy expectedTy accSubst = Some s'"
      and "subst_factors_through accSubst accSubst"
  shows "subst_factors_through s' s'"
proof -
  from assms(1) obtain s where
    unif: "unify (\<lambda>n. n |\<notin>| TE_TypeVars env)
            (apply_subst accSubst actualTy) (apply_subst accSubst expectedTy) = Some s" and
    s'_eq: "s' = compose_subst s accSubst"
    unfolding try_unify_compose_def by (auto simp: Let_def split: option.splits)
  \<comment> \<open>s' factors through accSubst (proved above). \<close>
  have s'_factors_acc: "subst_factors_through s' accSubst"
    using try_unify_compose_factors_through[OF assms] .
  \<comment> \<open>s' is itself a unifier of (apply_subst accSubst actualTy, apply_subst accSubst expectedTy):
        apply_subst s' (apply_subst accSubst actualTy)
          = apply_subst s' actualTy        (by s'_factors_acc)
          = apply_subst s (apply_subst accSubst actualTy)   (definition)
          = apply_subst s (apply_subst accSubst expectedTy) (by unify_sound)
          = apply_subst s' expectedTy        (definition)
          = apply_subst s' (apply_subst accSubst expectedTy) (by s'_factors_acc, reversed)
      So by unify_mgu, apply_subst s' x = apply_subst s' (apply_subst s x) for all x. \<close>
  have s_unifies_under_acc:
    "apply_subst s (apply_subst accSubst actualTy) = apply_subst s (apply_subst accSubst expectedTy)"
    using unify_sound[OF unif] .
  have s'_unifies:
    "apply_subst s' (apply_subst accSubst actualTy) = apply_subst s' (apply_subst accSubst expectedTy)"
    using s'_eq s_unifies_under_acc compose_subst_correct s'_factors_acc subst_factors_through_def
    by auto
  \<comment> \<open>To use unify_mgu, we need s' to unify the args of unify, i.e.
      apply_subst accSubst actualTy and apply_subst accSubst expectedTy. \<checkmark> \<close>
  have s'_factors_s: "\<And>ty. apply_subst s' ty = apply_subst s' (apply_subst s ty)"
    using unify_mgu[OF unif s'_unifies] .

  have "\<And>ty. apply_subst s' (apply_subst s' ty) = apply_subst s' ty"
  proof -
    fix ty
    have "apply_subst s' (apply_subst s' ty)
          = apply_subst s' (apply_subst s (apply_subst accSubst ty))"
      using s'_eq by (simp add: compose_subst_correct)
    also have "\<dots> = apply_subst s' (apply_subst accSubst ty)"
      using s'_factors_s[symmetric] .
    also have "\<dots> = apply_subst s' ty"
      using s'_factors_acc unfolding subst_factors_through_def by simp
    finally show "apply_subst s' (apply_subst s' ty) = apply_subst s' ty" .
  qed
  thus ?thesis unfolding subst_factors_through_def by blast
qed

(* When try_unify_compose succeeds, the resulting substitution's domain is contained
   in flex tyvars (i.e., not in TE_TypeVars env), provided accSubst's domain already
   was. This follows from unify_dom_flex + fmdom_compose_subst. *)
lemma try_unify_compose_dom_flex:
  assumes tuc: "try_unify_compose env actualTy expectedTy accSubst = Some s'"
      and acc_flex: "fmdom accSubst |\<inter>| TE_TypeVars env = {||}"
  shows "fmdom s' |\<inter>| TE_TypeVars env = {||}"
proof -
  from tuc obtain s where
    unif: "unify (\<lambda>n. n |\<notin>| TE_TypeVars env)
            (apply_subst accSubst actualTy) (apply_subst accSubst expectedTy) = Some s" and
    s'_eq: "s' = compose_subst s accSubst"
    unfolding try_unify_compose_def by (auto simp: Let_def split: option.splits)
  have s_flex: "\<forall>n. n |\<in>| fmdom s \<longrightarrow> n |\<notin>| TE_TypeVars env"
    using unify_dom_flex[OF unif] .
  hence s_disj: "fmdom s |\<inter>| TE_TypeVars env = {||}" by auto
  have "fmdom s' = fmdom s |\<union>| fmdom accSubst"
    using s'_eq by (simp add: fmdom_compose_subst)
  thus ?thesis using s_disj acc_flex by auto
qed

(* Helper: apply_subst preserves runtime when the substitution's range is runtime
   under the same env. (Specialisation of apply_subst_preserves_runtime with src = tgt.) *)
lemma apply_subst_preserves_runtime_same_env:
  assumes ty_rt: "is_runtime_type env ty"
      and acc_rt: "\<forall>ty' \<in> fmran' subst. is_runtime_type env ty'"
  shows "is_runtime_type env (apply_subst subst ty)"
proof (rule apply_subst_preserves_runtime[OF ty_rt refl])
  fix n assume n_in: "n |\<in>| TE_RuntimeTypeVars env"
  show "case fmlookup subst n of
          Some ty' \<Rightarrow> is_runtime_type env ty'
        | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars env"
  proof (cases "fmlookup subst n")
    case None
    thus ?thesis using n_in by simp
  next
    case (Some ty')
    hence "ty' \<in> fmran' subst" by (auto simp: fmran'I)
    thus ?thesis using acc_rt Some by simp
  qed
qed

(* Like try_unify_compose_preserves_well_kinded but for runtime types. *)
lemma try_unify_compose_preserves_runtime:
  assumes tuc: "try_unify_compose env actualTy expectedTy accSubst = Some s'"
      and acc_rt: "\<forall>ty \<in> fmran' accSubst. is_runtime_type wkEnv ty"
      and act_rt: "is_runtime_type wkEnv actualTy"
      and exp_rt: "is_runtime_type wkEnv expectedTy"
  shows "\<forall>ty \<in> fmran' s'. is_runtime_type wkEnv ty"
proof -
  from tuc obtain s where
    unif: "unify (\<lambda>n. n |\<notin>| TE_TypeVars env)
            (apply_subst accSubst actualTy) (apply_subst accSubst expectedTy) = Some s" and
    s'_eq: "s' = compose_subst s accSubst"
    unfolding try_unify_compose_def by (auto simp: Let_def split: option.splits)
  have act'_rt: "is_runtime_type wkEnv (apply_subst accSubst actualTy)"
    using apply_subst_preserves_runtime_same_env[OF act_rt acc_rt] .
  have exp'_rt: "is_runtime_type wkEnv (apply_subst accSubst expectedTy)"
    using apply_subst_preserves_runtime_same_env[OF exp_rt acc_rt] .
  have s_rt: "\<forall>ty \<in> fmran' s. is_runtime_type wkEnv ty"
    using unify_preserves_runtime[OF unif act'_rt exp'_rt] .
  show ?thesis
    using compose_subst_preserves_runtime[OF acc_rt s_rt] s'_eq by simp
qed

(* Helper: apply_subst preserves well-kindedness when the substitution's range is
   well-kinded under the same env. (Specialisation of apply_subst_preserves_well_kinded
   with src = tgt.) *)
lemma apply_subst_preserves_well_kinded_same_env:
  assumes ty_wk: "is_well_kinded env ty"
      and acc_wk: "\<forall>ty' \<in> fmran' subst. is_well_kinded env ty'"
  shows "is_well_kinded env (apply_subst subst ty)"
proof (rule apply_subst_preserves_well_kinded[OF ty_wk refl])
  fix n assume n_in: "n |\<in>| TE_TypeVars env"
  show "case fmlookup subst n of
          Some ty' \<Rightarrow> is_well_kinded env ty'
        | None \<Rightarrow> n |\<in>| TE_TypeVars env"
  proof (cases "fmlookup subst n")
    case None
    thus ?thesis using n_in by simp
  next
    case (Some ty')
    hence "ty' \<in> fmran' subst" by (auto simp: fmran'I)
    thus ?thesis using acc_wk Some by simp
  qed
qed

(* When try_unify_compose succeeds, the resulting substitution's range is
   well-kinded under wkEnv if accSubst's range, actualTy, and expectedTy are all
   well-kinded under wkEnv. (wkEnv may differ from the env passed to try_unify_compose,
   which is only used to compute the unifier's flex predicate; well-kindedness is a
   range-of-substitution property and doesn't care about that predicate.) *)
lemma try_unify_compose_preserves_well_kinded:
  assumes tuc: "try_unify_compose env actualTy expectedTy accSubst = Some s'"
      and acc_wk: "\<forall>ty \<in> fmran' accSubst. is_well_kinded wkEnv ty"
      and act_wk: "is_well_kinded wkEnv actualTy"
      and exp_wk: "is_well_kinded wkEnv expectedTy"
  shows "\<forall>ty \<in> fmran' s'. is_well_kinded wkEnv ty"
proof -
  from tuc obtain s where
    unif: "unify (\<lambda>n. n |\<notin>| TE_TypeVars env)
            (apply_subst accSubst actualTy) (apply_subst accSubst expectedTy) = Some s" and
    s'_eq: "s' = compose_subst s accSubst"
    unfolding try_unify_compose_def by (auto simp: Let_def split: option.splits)
  \<comment> \<open>apply_subst accSubst actualTy is well-kinded under wkEnv. \<close>
  have act'_wk: "is_well_kinded wkEnv (apply_subst accSubst actualTy)"
    using apply_subst_preserves_well_kinded_same_env[OF act_wk acc_wk] .
  have exp'_wk: "is_well_kinded wkEnv (apply_subst accSubst expectedTy)"
    using apply_subst_preserves_well_kinded_same_env[OF exp_wk acc_wk] .
  \<comment> \<open>unify produces a range-wk substitution. \<close>
  have s_wk: "\<forall>ty \<in> fmran' s. is_well_kinded wkEnv ty"
    using unify_preserves_well_kinded[OF unif act'_wk exp'_wk] .
  \<comment> \<open>compose_subst preserves range-wk. \<close>
  show ?thesis
    using compose_subst_preserves_well_kinded[OF acc_wk s_wk] s'_eq by simp
qed

end
