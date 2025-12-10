theory MetaSubst
  imports CoreSyntax CoreTypeProps "HOL-Library.Finite_Map"
begin

(* ========================================================================== *)
(* MetaSubst definitions *)
(* ========================================================================== *)

(* A MetaSubst maps metavariable IDs (nats) to types. *)
type_synonym MetaSubst = "(nat, CoreType) fmap"

(* The singleton substitution: maps n to ty. *)
definition singleton_subst :: "nat \<Rightarrow> CoreType \<Rightarrow> MetaSubst" where
  "singleton_subst n ty = fmupd n ty fmempty"

(* Apply a metavariable substitution to a type.
   This replaces CoreTy_Meta n with subst(n) if defined, otherwise leaves it. *)
fun apply_subst :: "MetaSubst \<Rightarrow> CoreType \<Rightarrow> CoreType" where
  "apply_subst subst (CoreTy_Name name tyargs) =
    CoreTy_Name name (map (apply_subst subst) tyargs)"
| "apply_subst subst CoreTy_Bool = CoreTy_Bool"
| "apply_subst subst (CoreTy_FiniteInt sign bits) = CoreTy_FiniteInt sign bits"
| "apply_subst subst CoreTy_MathInt = CoreTy_MathInt"
| "apply_subst subst CoreTy_MathReal = CoreTy_MathReal"
| "apply_subst subst (CoreTy_Record flds) =
    CoreTy_Record (map (\<lambda>(name, ty). (name, apply_subst subst ty)) flds)"
| "apply_subst subst (CoreTy_Array elemTy dims) = CoreTy_Array (apply_subst subst elemTy) dims"
| "apply_subst subst (CoreTy_Meta n) =
    (case fmlookup subst n of
      Some ty \<Rightarrow> ty
    | None \<Rightarrow> CoreTy_Meta n)"

(* Find all metavariables appearing in the range of a substitution *)
definition subst_range_mvs :: "MetaSubst \<Rightarrow> nat set" where
  "subst_range_mvs subst = \<Union>(type_metavars ` fmran' subst)"


(* ========================================================================== *)
(* General properties of substitutions *)
(* ========================================================================== *)

(* Effect of applying the empty subst *)
lemma apply_subst_empty [simp]:
  "apply_subst fmempty ty = ty"
proof (induction ty)
  case (CoreTy_Record flds)
  have "\<And>name ty. (name, ty) \<in> set flds \<Longrightarrow> apply_subst fmempty ty = ty"
    using CoreTy_Record.IH by auto
  hence "map (\<lambda>(name, ty). (name, apply_subst fmempty ty)) flds = flds"
    by (induction flds) auto
  thus ?case by simp
qed (auto simp: list.map_ident_strong)

lemma map_apply_subst_empty [simp]:
  "map (apply_subst fmempty) tys = tys"
  by (induction tys) auto

(* Effect of applying a singleton subst *)
lemma apply_subst_singleton:
  "apply_subst (singleton_subst n ty') (CoreTy_Meta n) = ty'"
  by (simp add: singleton_subst_def)

lemma apply_subst_singleton_other:
  "n \<noteq> m \<Longrightarrow> apply_subst (singleton_subst n ty') (CoreTy_Meta m) = CoreTy_Meta m"
  by (simp add: singleton_subst_def)

(* If n doesn't occur in ty, then applying singleton_subst n ty' leaves ty unchanged *)
lemma apply_subst_singleton_no_occurs:
  "\<not> occurs n ty \<Longrightarrow> apply_subst (singleton_subst n ty') ty = ty"
proof (induction ty)
  case (CoreTy_Record flds)
  have "\<And>name ty. (name, ty) \<in> set flds \<Longrightarrow> \<not> occurs n ty \<Longrightarrow>
        apply_subst (singleton_subst n ty') ty = ty"
    using CoreTy_Record.IH by auto
  moreover have "\<And>name ty. (name, ty) \<in> set flds \<Longrightarrow> \<not> occurs n ty"
    using CoreTy_Record.prems by (auto simp: occurs_def)
  ultimately have "map (\<lambda>(name, ty). (name, apply_subst (singleton_subst n ty') ty)) flds = flds"
    by (induction flds) auto
  thus ?case by simp
qed (auto simp: occurs_def singleton_subst_def map_idI)

(* The range of a singleton subst is just the given type. *)
lemma fmran'_singleton_subst: "fmran' (singleton_subst n ty) = {ty}"
  by (auto simp: singleton_subst_def fmran'_def split: if_splits)

(* Type predicates (int, signed int, finite int) are preserved by apply_subst *)
lemma is_integer_type_apply_subst:
  "is_integer_type ty \<Longrightarrow> is_integer_type (apply_subst subst ty)"
  by (cases ty) auto
lemma is_signed_integer_type_apply_subst:
  "is_signed_integer_type ty \<Longrightarrow> is_signed_integer_type (apply_subst subst ty)"
  by (cases ty) auto
lemma is_finite_integer_type_apply_subst:
  "is_finite_integer_type ty \<Longrightarrow> is_finite_integer_type (apply_subst subst ty)"
  by (cases ty) auto

(* Metavars after applying a substitution come from:
   - metavars in ty that are not in dom(subst), OR
   - metavars in the range of subst (for substituted vars) *)
lemma apply_subst_metavars_result:
  "type_metavars (apply_subst subst ty) \<subseteq>
   (type_metavars ty - fset (fmdom subst)) \<union> subst_range_mvs subst"
proof (induction ty)
  case (CoreTy_Record flds)
  show ?case
  proof
    fix x assume "x \<in> type_metavars (apply_subst subst (CoreTy_Record flds))"
    then obtain name ty where mem: "(name, ty) \<in> set flds"
      and x_in: "x \<in> type_metavars (apply_subst subst ty)"
      by auto
    from CoreTy_Record.IH mem
    have "type_metavars (apply_subst subst ty) \<subseteq>
          (type_metavars ty - fset (fmdom subst)) \<union> subst_range_mvs subst"
      by auto
    with x_in have "x \<in> (type_metavars ty - fset (fmdom subst)) \<union> subst_range_mvs subst"
      by auto
    moreover have "type_metavars ty \<subseteq> type_metavars (CoreTy_Record flds)"
      using mem by auto
    ultimately show "x \<in> (type_metavars (CoreTy_Record flds) - fset (fmdom subst)) \<union> subst_range_mvs subst"
      by auto
  qed
next
  case (CoreTy_Meta n)
  then show ?case by (cases "fmlookup subst n"; auto simp: subst_range_mvs_def fmran'I)
qed (auto)

(* Corollary: If n is in dom(subst) and not in range(subst), it's eliminated from result *)
corollary apply_subst_eliminates_dom:
  assumes "n \<in> fset (fmdom subst)"
      and "n \<notin> subst_range_mvs subst"
  shows "n \<notin> type_metavars (apply_subst subst ty)"
proof -
  have "type_metavars (apply_subst subst ty) \<subseteq>
        (type_metavars ty - fset (fmdom subst)) \<union> subst_range_mvs subst"
    by (rule apply_subst_metavars_result)
  thus ?thesis using assms by auto
qed

(* Another corollary: If all metavars in ty are in dom(subst), and all types in range(subst)
   are ground, then applying subst to ty results in a ground type *)
corollary apply_subst_makes_ground:
  assumes "type_metavars ty \<subseteq> fset (fmdom subst)"
      and "\<forall>ty' \<in> fmran' subst. is_ground ty'"
  shows "is_ground (apply_subst subst ty)"
proof -
  have "type_metavars (apply_subst subst ty) \<subseteq>
        (type_metavars ty - fset (fmdom subst)) \<union> subst_range_mvs subst"
    by (rule apply_subst_metavars_result)
  also have "... \<subseteq> subst_range_mvs subst"
    using assms(1) by auto
  also have "... = {}"
    using assms(2) is_ground_no_metavars
    by (auto simp: subst_range_mvs_def)
  finally show ?thesis
    using is_ground_no_metavars by blast
qed

(* Substitution is identity when domain is disjoint from type's metavariables *)
lemma apply_subst_disjoint_id:
  "type_metavars ty \<inter> fset (fmdom subst) = {} \<Longrightarrow> apply_subst subst ty = ty"
proof (induction ty)
  case (CoreTy_Name name tyargs)
  hence "\<forall>arg \<in> set tyargs. apply_subst subst arg = arg" by auto
  thus ?case using CoreTy_Name by (simp add: map_idI)
next
  case (CoreTy_Record flds)
  have disjoint: "\<And>name ty. (name, ty) \<in> set flds \<Longrightarrow> type_metavars ty \<inter> fset (fmdom subst) = {}"
  proof -
    fix name ty assume "(name, ty) \<in> set flds"
    hence "type_metavars ty \<subseteq> type_metavars (CoreTy_Record flds)" by auto
    thus "type_metavars ty \<inter> fset (fmdom subst) = {}"
      using CoreTy_Record.prems by auto
  qed
  hence "\<And>name ty. (name, ty) \<in> set flds \<Longrightarrow> apply_subst subst ty = ty"
    using CoreTy_Record.IH by auto
  hence "map (\<lambda>(name, ty). (name, apply_subst subst ty)) flds = flds"
    by (induction flds) auto
  thus ?case by simp
next
  case (CoreTy_Meta n)
  thus ?case by (simp add: fmdom_notD)
qed (simp_all)

(* Substitution on ground types is identity *)
corollary apply_subst_ground:
  "is_ground ty \<Longrightarrow> apply_subst subst ty = ty"
  using is_ground_no_metavars apply_subst_disjoint_id by blast

(* Substituting runtime types preserves runtime-ness *)
(* See also: apply_subst_preserves_well_kinded in CoreKindcheck.thy *)
lemma apply_subst_preserves_runtime:
  assumes "is_runtime_type ty"
    and "\<forall>ty' \<in> fmran' subst. is_runtime_type ty'"
  shows "is_runtime_type (apply_subst subst ty)"
using assms proof (induction ty)
  case (CoreTy_Name name tyArgs)
  have "list_all is_runtime_type tyArgs"
    using CoreTy_Name.prems(1) by simp
  hence "list_all is_runtime_type (map (apply_subst subst) tyArgs)"
    using CoreTy_Name.IH CoreTy_Name.prems(2)
    by (simp add: list_all_iff)
  thus ?case by simp
next
  case (CoreTy_Record flds)
  have "list_all is_runtime_type (map snd flds)"
    using CoreTy_Record.prems(1) by simp
  hence "list_all is_runtime_type (map (apply_subst subst \<circ> snd) flds)"
    using CoreTy_Record.IH CoreTy_Record.prems(2)
    by (simp add: comp_def list.pred_map list.pred_mono_strong snds.intros)
  moreover have "map (apply_subst subst \<circ> snd) flds =
                 map (snd \<circ> (\<lambda>(name, ty). (name, apply_subst subst ty))) flds"
    by (simp add: comp_def case_prod_beta)
  ultimately show ?case by simp
next
  case (CoreTy_Meta n)
  show ?case
  proof (cases "fmlookup subst n")
    case None
    thus ?thesis by simp
  next
    case (Some ty')
    hence "ty' \<in> fmran' subst"
      by (simp add: fmran'I)
    hence "is_runtime_type ty'"
      using CoreTy_Meta.prems(2) by blast
    thus ?thesis using Some by simp
  qed
qed simp_all


(* ========================================================================== *)
(* Composition of substitutions *)
(* ========================================================================== *)

(* Compose two substitutions *)
definition compose_subst :: "MetaSubst \<Rightarrow> MetaSubst \<Rightarrow> MetaSubst" where
  "compose_subst s2 s1 = s2 ++\<^sub>f fmmap (apply_subst s2) s1"

(* Composition of substitutions is correct *)
lemma compose_subst_correct:
  "apply_subst (compose_subst s2 s1) ty = apply_subst s2 (apply_subst s1 ty)"
  by (induction ty; auto simp: compose_subst_def split: option.splits)

(* How lookup works on composed substitution *)
lemma fmlookup_compose_subst:
  "fmlookup (compose_subst s2 s1) n =
   (case fmlookup s1 n of
      Some ty \<Rightarrow> Some (apply_subst s2 ty)
    | None \<Rightarrow> fmlookup s2 n)"
  using compose_subst_def by auto

lemma fmlookup_compose_subst_Some1:
  "fmlookup s1 n = Some ty1 \<Longrightarrow>
   fmlookup (compose_subst s2 s1) n = Some (apply_subst s2 ty1)"
  by (simp add: fmlookup_compose_subst)

lemma fmlookup_compose_subst_None1:
  "fmlookup s1 n = None \<Longrightarrow>
   fmlookup (compose_subst s2 s1) n = fmlookup s2 n"
  by (simp add: fmlookup_compose_subst)

(* The range of the composed substitution *)
lemma compose_subst_range:
  "ty \<in> fmran' (compose_subst s2 s1) \<Longrightarrow>
   ty \<in> fmran' s2 \<or> (\<exists>ty1 \<in> fmran' s1. ty = apply_subst s2 ty1)"
proof -
  assume "ty \<in> fmran' (compose_subst s2 s1)"
  then obtain n where lookup: "fmlookup (compose_subst s2 s1) n = Some ty"
    by (auto simp: fmran'_def)
  show ?thesis
  proof (cases "fmlookup s1 n")
    case None
    hence "fmlookup s2 n = Some ty"
      using lookup by (simp add: fmlookup_compose_subst_None1)
    thus ?thesis by (auto simp: fmran'_def)
  next
    case (Some ty1)
    hence "ty = apply_subst s2 ty1"
      using lookup by (simp add: fmlookup_compose_subst_Some1)
    moreover have "ty1 \<in> fmran' s1" using Some by (auto simp: fmran'_def)
    ultimately show ?thesis by auto
  qed
qed

(* Empty substitution is identity for composition *)
lemma compose_subst_empty_left [simp]:
  "compose_subst fmempty s = s"
  unfolding compose_subst_def
  by (simp add: fmap.map_ident_strong)

lemma compose_subst_empty_right [simp]:
  "compose_subst s fmempty = s"
  unfolding compose_subst_def
  by (simp add: fmap.map_ident_strong)

(* Composition of substitutions is associative *)
lemma compose_subst_assoc:
  "compose_subst s3 (compose_subst s2 s1) = compose_subst (compose_subst s3 s2) s1"
proof (intro fmap_ext)
  fix n
  show "fmlookup (compose_subst s3 (compose_subst s2 s1)) n =
        fmlookup (compose_subst (compose_subst s3 s2) s1) n"
  proof (cases "fmlookup s1 n")
    case None
    \<comment> \<open>LHS: lookup in compose_subst s3 (compose_subst s2 s1)\<close>
    have lhs: "fmlookup (compose_subst s3 (compose_subst s2 s1)) n =
               (case fmlookup s2 n of
                  Some ty \<Rightarrow> Some (apply_subst s3 ty)
                | None \<Rightarrow> fmlookup s3 n)"
      using None by (simp add: fmlookup_compose_subst)
    \<comment> \<open>RHS: lookup in compose_subst (compose_subst s3 s2) s1\<close>
    have rhs: "fmlookup (compose_subst (compose_subst s3 s2) s1) n =
               fmlookup (compose_subst s3 s2) n"
      using None by (simp add: fmlookup_compose_subst)
    have rhs': "fmlookup (compose_subst s3 s2) n =
                (case fmlookup s2 n of
                   Some ty \<Rightarrow> Some (apply_subst s3 ty)
                 | None \<Rightarrow> fmlookup s3 n)"
      by (simp add: fmlookup_compose_subst)
    show ?thesis using lhs rhs rhs' by simp
  next
    case (Some ty1)
    \<comment> \<open>LHS: first lookup in compose_subst s2 s1, then apply s3\<close>
    have step1: "fmlookup (compose_subst s2 s1) n = Some (apply_subst s2 ty1)"
      using Some by (simp add: fmlookup_compose_subst)
    have lhs: "fmlookup (compose_subst s3 (compose_subst s2 s1)) n =
               Some (apply_subst s3 (apply_subst s2 ty1))"
      using step1 by (simp add: fmlookup_compose_subst)
    \<comment> \<open>RHS: lookup in s1, then apply compose_subst s3 s2\<close>
    have rhs: "fmlookup (compose_subst (compose_subst s3 s2) s1) n =
               Some (apply_subst (compose_subst s3 s2) ty1)"
      using Some by (simp add: fmlookup_compose_subst)
    \<comment> \<open>Now show these are equal using compose_subst_correct\<close>
    have eq: "apply_subst s3 (apply_subst s2 ty1) = apply_subst (compose_subst s3 s2) ty1"
      by (simp add: compose_subst_correct)
    show ?thesis using lhs rhs eq by simp
  qed
qed

(* Once a type becomes ground (under some substitution), it will remain ground even
   after composing further substitutions *)
lemma compose_subst_preserves_ground:
  assumes "(apply_subst \<theta> ty1) = ty2"
      and "is_ground ty2"
    shows "(apply_subst (compose_subst \<eta> \<theta>) ty1) = ty2"
  by (simp add: apply_subst_ground assms(1,2) compose_subst_correct)

(* Composition of substitutions preserves "runtime-ness" *)
lemma compose_subst_preserves_runtime:
  assumes "\<forall>ty \<in> fmran' s1. is_runtime_type ty"
      and "\<forall>ty \<in> fmran' s2. is_runtime_type ty"
    shows "\<forall>ty \<in> fmran' (compose_subst s2 s1). is_runtime_type ty"
proof
  fix ty assume "ty \<in> fmran' (compose_subst s2 s1)"
  from compose_subst_range[OF this] show "is_runtime_type ty"
  proof
    assume "ty \<in> fmran' s2"
    thus ?thesis using assms(2) by blast
  next
    assume "\<exists>ty1 \<in> fmran' s1. ty = apply_subst s2 ty1"
    then obtain ty1 where "ty1 \<in> fmran' s1" and "ty = apply_subst s2 ty1" by auto
    from \<open>ty1 \<in> fmran' s1\<close> assms(1) have "is_runtime_type ty1" by blast
    thus ?thesis
      using \<open>ty \<in> fmran' s2 \<or> (\<exists>ty1\<in>fmran' s1. ty = apply_subst s2 ty1)\<close>
        apply_subst_preserves_runtime assms(1,2) by auto
  qed
qed


end
