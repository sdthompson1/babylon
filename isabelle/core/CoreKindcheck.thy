theory CoreKindcheck
  imports CoreSyntax CoreTyEnv CoreTypeProps MetaSubst
begin

(* Defines kind-checking for Core types *)

(* Helper: classify dimensions into categories for uniformity checking *)
datatype DimCategory = DimCat_Unknown | DimCat_Allocatable | DimCat_Fixed

fun dim_category :: "CoreDimension \<Rightarrow> DimCategory" where
  "dim_category CoreDim_Unknown = DimCat_Unknown"
| "dim_category CoreDim_Allocatable = DimCat_Allocatable"
| "dim_category (CoreDim_Fixed _) = DimCat_Fixed"

(* Helper: check if all dimensions have the same category
   (and that there is at least one dimension) *)
fun dims_uniform :: "CoreDimension list \<Rightarrow> bool" where
  "dims_uniform [] = False"
| "dims_uniform [d] = True"
| "dims_uniform (d1 # d2 # ds) =
    (dim_category d1 = dim_category d2 \<and> dims_uniform (d2 # ds))"

(* Helper: check if a CoreDim_Fixed value is within uint64 range *)
fun dim_in_range :: "CoreDimension \<Rightarrow> bool" where
  "dim_in_range (CoreDim_Fixed n) = int_in_range (int_range Unsigned IntBits_64) n"
| "dim_in_range _ = True"

(* Check if array dimensions are well-kinded:
   - There must be at least one dimension
   - If multiple dimensions, they must all have the same category
   - All Fixed dimensions must be within uint64 range *)
definition array_dims_well_kinded :: "CoreDimension list \<Rightarrow> bool" where
  "array_dims_well_kinded dims \<equiv> dims \<noteq> [] \<and> dims_uniform dims \<and> list_all dim_in_range dims"

(* Definition of well-kindedness *)
fun is_well_kinded :: "CoreTyEnv \<Rightarrow> CoreType \<Rightarrow> bool" where
  "is_well_kinded env (CoreTy_Datatype typeName argTypes) =
    (case fmlookup (TE_Datatypes env) typeName of
       Some numTyVars \<Rightarrow> length argTypes = numTyVars
                         \<and> list_all (is_well_kinded env) argTypes
     | None \<Rightarrow> False)"
| "is_well_kinded env CoreTy_Bool = True"
| "is_well_kinded env (CoreTy_FiniteInt sign bits) = True"
| "is_well_kinded env CoreTy_MathInt = True"
| "is_well_kinded env CoreTy_MathReal = True"
| "is_well_kinded env (CoreTy_Record flds) = list_all (is_well_kinded env) (map snd flds)"
| "is_well_kinded env (CoreTy_Array elemTy dims) =
    (is_well_kinded env elemTy \<and> array_dims_well_kinded dims)"
| "is_well_kinded env (CoreTy_Meta n) = (n |\<in>| TE_TypeVars env)"

(* Integer types are always well-kinded *)
lemma is_integer_type_well_kinded:
  "is_integer_type ty \<Longrightarrow> is_well_kinded env ty"
  by (cases ty) auto

(* A list of metavariables is well-kinded, provided the metavars are all in scope. *)
lemma list_all_meta_is_well_kinded:
  assumes "\<forall>n \<in> set nums. n |\<in>| TE_TypeVars env"
  shows "list_all (is_well_kinded env) (map CoreTy_Meta nums)"
  using assms by (induction nums) auto


(* Adding type variables to the environment preserves well-kindedness. Type variables
   are nat-keyed and datatypes are string-keyed, so no shadowing is possible. *)
lemma is_well_kinded_extend_tyvars:
  assumes "is_well_kinded env ty"
  shows "is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extra \<rparr>) ty"
using assms proof (induction ty)
  case (CoreTy_Datatype name argTypes)
  then obtain numTyVars where
    dt_lookup: "fmlookup (TE_Datatypes env) name = Some numTyVars" and
    len_eq: "length argTypes = numTyVars" and
    args_wk: "list_all (is_well_kinded env) argTypes"
    by (auto split: option.splits)
  have args_wk_ext: "list_all (is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extra \<rparr>)) argTypes"
    using CoreTy_Datatype.IH args_wk by (simp add: list_all_iff)
  thus ?case using dt_lookup len_eq by simp
next
  case (CoreTy_Record flds)
  have "\<And>a b. (a, b) \<in> set flds \<Longrightarrow>
              is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extra \<rparr>) b"
  proof -
    fix a b assume mem: "(a, b) \<in> set flds"
    from mem CoreTy_Record.prems have "is_well_kinded env b"
      by (auto simp: list_all_iff)
    with CoreTy_Record.IH[OF mem] show "is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extra \<rparr>) b"
      by (simp add: snds.intros)
  qed
  thus ?case by (auto simp: list_all_iff)
next
  case (CoreTy_Array elemTy dims)
  thus ?case by auto
next
  case (CoreTy_Meta n)
  thus ?case by simp
qed (simp_all)


(* is_well_kinded only depends on TE_TypeVars and TE_Datatypes.
   Changing other fields of the environment (e.g. TE_TermVars, TE_GhostVars)
   does not affect well-kindedness. *)
lemma is_well_kinded_cong_env:
  assumes "TE_TypeVars env' = TE_TypeVars env"
    and "TE_Datatypes env' = TE_Datatypes env"
  shows "is_well_kinded env' ty = is_well_kinded env ty"
using assms proof (induction ty)
  case (CoreTy_Datatype name argTypes)
  hence IH: "\<And>x. x \<in> set argTypes \<Longrightarrow> is_well_kinded env' x = is_well_kinded env x" by simp
  hence "list_all (is_well_kinded env') argTypes = list_all (is_well_kinded env) argTypes"
    by (induction argTypes) auto
  then show ?case using CoreTy_Datatype.prems by (auto split: option.splits)
next
  case (CoreTy_Record flds)
  hence IH: "\<And>x. x \<in> snd ` set flds \<Longrightarrow> is_well_kinded env' x = is_well_kinded env x" by auto
  hence "list_all (is_well_kinded env') (map snd flds) = list_all (is_well_kinded env) (map snd flds)"
    by (induction flds) auto
  then show ?case by auto
next
  case (CoreTy_Array elemTy dims)
  then show ?case by auto
qed auto

lemma is_well_kinded_TE_ConstNames_irrelevant [simp]:
  "is_well_kinded (env \<lparr> TE_ConstNames := c \<rparr>) ty = is_well_kinded env ty"
  using is_well_kinded_cong_env[of "env \<lparr> TE_ConstNames := c \<rparr>" env] by simp

(* This predicate says that all types in the range of a MetaSubst are well-kinded. *)
definition metasubst_well_kinded :: "CoreTyEnv \<Rightarrow> MetaSubst \<Rightarrow> bool" where 
  "metasubst_well_kinded env subst =
    (\<forall>n ty. fmlookup subst n = Some ty \<longrightarrow> is_well_kinded env ty)"

(* Substitutions built from zip (on a list of well-kinded types) satisfy the above predicate. *)
lemma metasubst_well_kinded_from_zip:
  assumes "list_all (is_well_kinded env) tys"
  shows "metasubst_well_kinded env (fmap_of_list (zip metavars tys))"
  unfolding metasubst_well_kinded_def
proof (intro allI impI)
  fix n ty
  assume "fmlookup (fmap_of_list (zip metavars tys)) n = Some ty"
  then have "(n, ty) \<in> set (zip metavars tys)"
    by (simp add: fmap_of_list_SomeD)
  then have "ty \<in> set tys"
    by (metis in_set_zipE)
  thus "is_well_kinded env ty"
    using assms by (simp add: list_all_iff)
qed

(* Substitution of well-kinded types preserves well-kindedness. *)
(* See also: apply_subst_preserves_runtime in MetaSubst.thy. *)
lemma apply_subst_preserves_well_kinded:
  assumes "is_well_kinded env ty"
    and "metasubst_well_kinded env subst"
  shows "is_well_kinded env (apply_subst subst ty)"
using assms proof (induction ty)
  case (CoreTy_Datatype name tyargs)
  then obtain numTyVars where
    dt_lookup: "fmlookup (TE_Datatypes env) name = Some numTyVars" and
    len_eq: "length tyargs = numTyVars" and
    args_wk: "list_all (is_well_kinded env) tyargs"
    by (auto split: option.splits)
  have "list_all (is_well_kinded env) (map (apply_subst subst) tyargs)"
    using CoreTy_Datatype.IH args_wk CoreTy_Datatype.prems(2)
    by (simp add: list_all_iff)
  thus ?case using dt_lookup len_eq by simp
next
  case (CoreTy_Record flds)
  have "list_all (is_well_kinded env) (map snd flds)"
    using CoreTy_Record.prems(1) by simp
  hence "list_all (is_well_kinded env) (map (apply_subst subst \<circ> snd) flds)"
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
    (* substitution doesn't touch n, so the result is still CoreTy_Meta n,
       which is well-kinded because n |\<in>| TE_TypeVars env by the input assumption *)
    thus ?thesis using CoreTy_Meta.prems(1) by simp
  next
    case (Some ty)
    hence "is_well_kinded env ty"
      using CoreTy_Meta.prems(2) metasubst_well_kinded_def by blast
    thus ?thesis using Some by simp
  qed
qed (simp_all)

(* Composition of substitutions preserves well-kindedness *)
(* See also: compose_subst_preserves_runtime in MetaSubst.thy *)
lemma compose_subst_preserves_well_kinded:
  assumes "\<forall>ty \<in> fmran' s1. is_well_kinded env ty"
      and "\<forall>ty \<in> fmran' s2. is_well_kinded env ty"
    shows "\<forall>ty \<in> fmran' (compose_subst s2 s1). is_well_kinded env ty"
proof
  fix ty assume "ty \<in> fmran' (compose_subst s2 s1)"
  from compose_subst_range[OF this] show "is_well_kinded env ty"
  proof
    assume "ty \<in> fmran' s2"
    thus ?thesis using assms(2) by blast
  next
    assume "\<exists>ty1 \<in> fmran' s1. ty = apply_subst s2 ty1"
    then obtain ty1 where "ty1 \<in> fmran' s1" and "ty = apply_subst s2 ty1" by auto
    from \<open>ty1 \<in> fmran' s1\<close> assms(1) have "is_well_kinded env ty1" by blast
    thus ?thesis
      by (simp add: \<open>ty = apply_subst s2 ty1\<close> apply_subst_preserves_well_kinded assms(2) fmran'I
          metasubst_well_kinded_def)
  qed
qed

end
