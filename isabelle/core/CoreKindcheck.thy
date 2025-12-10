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
  "is_well_kinded env (CoreTy_Name typeName argTypes) =
    (if typeName |\<in>| TE_TypeVars env then
      argTypes = []
    else
      (case fmlookup (TE_Datatypes env) typeName of
        Some numTyVars \<Rightarrow> length argTypes = numTyVars
                          \<and> list_all (is_well_kinded env) argTypes
      | None \<Rightarrow> False))"
| "is_well_kinded env CoreTy_Bool = True"
| "is_well_kinded env (CoreTy_FiniteInt sign bits) = True"
| "is_well_kinded env CoreTy_MathInt = True"
| "is_well_kinded env CoreTy_MathReal = True"
| "is_well_kinded env (CoreTy_Record flds) = list_all (is_well_kinded env) (map snd flds)"
| "is_well_kinded env (CoreTy_Array elemTy dims) =
    (is_well_kinded env elemTy \<and> array_dims_well_kinded dims)"
| "is_well_kinded env (CoreTy_Meta _) = True"

(* Integer types are always well-kinded *)
lemma is_integer_type_well_kinded:
  "is_integer_type ty \<Longrightarrow> is_well_kinded env ty"
  by (cases ty) auto

(* List of metavariables is always well-kinded *)
lemma list_all_meta_is_well_kinded:
  "list_all (is_well_kinded env) (map CoreTy_Meta nums)"
  by (induction nums) auto


(* Adding type variables to the environment preserves well-kindedness,
   provided the new type variables don't shadow datatype names *)
lemma is_well_kinded_extend_tyvars:
  assumes "is_well_kinded env ty"
   and "extra |\<inter>| fmdom (TE_Datatypes env) = {||}"
  shows "is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extra \<rparr>) ty"
using assms proof (induction ty)
  case (CoreTy_Name name argTypes)
  define extEnv where "extEnv = env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extra \<rparr>"
  show ?case proof (cases "name |\<in>| TE_TypeVars env")
    case True
    (* name is a type variable in env, so also in extended env *)
    hence "argTypes = []" using assms(1) CoreTy_Name by simp
    hence "name |\<in>| TE_TypeVars extEnv"
      using True extEnv_def by simp
    thus ?thesis using extEnv_def \<open>argTypes = []\<close> by simp
  next
    case False
    (* name is not a type variable in env, so must be a datatype in env *)
    then obtain numTyVars where
      dt_lookup: "fmlookup (TE_Datatypes env) name = Some numTyVars" and
      len_eq: "length argTypes = numTyVars" and
      args_wk: "list_all (is_well_kinded env) argTypes"
      using CoreTy_Name(2) by (auto split: option.splits)
    (* name is a datatype, so it's not in extra (by the non-shadowing assumption) *)
    have "name |\<notin>| extra"
      using assms(2) dt_lookup fmlookup_dom_iff by fastforce
    (* name is neither in extra, nor in the original env's type variables; therefore it
       is not in the new env's type variables (by definition of the new env) *)
    hence name_not_tyvar_in_ext: "name |\<notin>| TE_TypeVars extEnv"
      using False extEnv_def by simp
    (* By IH, args are well-kinded in extended env *)
    have args_wk_ext: "list_all (is_well_kinded extEnv) argTypes"
      using CoreTy_Name.IH args_wk assms(2) extEnv_def list.pred_mono_strong by auto
    (* TE_Datatypes is unchanged between env and extEnv *)
    have "fmlookup (TE_Datatypes extEnv) name = Some numTyVars"
      using dt_lookup extEnv_def by simp
    thus ?thesis 
      using name_not_tyvar_in_ext args_wk_ext extEnv_def len_eq by auto
  qed
next
  case (CoreTy_Record flds)
  have "list_all (is_well_kinded env) (map snd flds)"
    using CoreTy_Record.prems(1) by auto
  thus ?case
    by (smt (verit, del_insts) CoreTy_Record.IH assms(2) imageE is_well_kinded.simps(6)
        list.pred_mono_strong list.set_map snds.intros)
next
  case (CoreTy_Array elemTy dims)
  have "is_well_kinded env elemTy"
    using CoreTy_Array.prems(1) by auto
  thus ?case
    using CoreTy_Array.IH CoreTy_Array.prems(1) assms(2) by auto
qed (simp_all)


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
  case (CoreTy_Name name tyargs)
  show ?case
  proof (cases "name |\<in>| TE_TypeVars env")
    case True
    hence "tyargs = []" using CoreTy_Name.prems(1) by simp
    thus ?thesis using True by auto
  next
    case False
    then obtain numTyVars where
      dt_lookup: "fmlookup (TE_Datatypes env) name = Some numTyVars" and
      len_eq: "length tyargs = numTyVars" and
      args_wk: "list_all (is_well_kinded env) tyargs"
      using CoreTy_Name.prems(1) by (auto split: option.splits)
    have "list_all (is_well_kinded env) (map (apply_subst subst) tyargs)"
      using CoreTy_Name.IH args_wk CoreTy_Name.prems(2)
      by (simp add: list_all_iff)
    thus ?thesis using False dt_lookup len_eq by simp
  qed
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
    thus ?thesis by simp
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
