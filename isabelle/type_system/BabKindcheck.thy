theory BabKindcheck
  imports "TypeEnv" "../base/IntRange" TypeProps
begin

(* This file defines well-kindedness for types. We only have one kind, *, because
   all our type constructors are fully applied (see BabTy_Name). Therefore, we
   just need an is_well_kinded function. *)

(* Helper: check if a dimension is valid (not BabDim_Fixed, which is pre-elaboration) *)
fun is_valid_dimension :: "BabDimension \<Rightarrow> bool" where
  "is_valid_dimension BabDim_Unknown = True"
| "is_valid_dimension BabDim_Allocatable = True"
| "is_valid_dimension (BabDim_FixedInt _) = True"
| "is_valid_dimension (BabDim_Fixed _) = False"

(* Helper: classify dimensions into categories for uniformity checking *)
datatype DimCategory = DimCat_Unknown | DimCat_Allocatable | DimCat_FixedInt

fun dim_category :: "BabDimension \<Rightarrow> DimCategory option" where
  "dim_category BabDim_Unknown = Some DimCat_Unknown"
| "dim_category BabDim_Allocatable = Some DimCat_Allocatable"
| "dim_category (BabDim_FixedInt _) = Some DimCat_FixedInt"
| "dim_category (BabDim_Fixed _) = None"

(* Helper: check if all dimensions have the same category *)
fun dims_uniform :: "BabDimension list \<Rightarrow> bool" where
  "dims_uniform [] = True"
| "dims_uniform [d] = is_valid_dimension d"
| "dims_uniform (d1 # d2 # ds) =
    (case (dim_category d1, dim_category d2) of
      (Some c1, Some c2) \<Rightarrow> c1 = c2 \<and> dims_uniform (d2 # ds)
    | _ \<Rightarrow> False)"

(* Helper: check if a BabDim_FixedInt value is within uint64 range *)
fun dim_in_uint64_range :: "BabDimension \<Rightarrow> bool" where
  "dim_in_uint64_range (BabDim_FixedInt n) = int_in_range (int_range Unsigned IntBits_64) n"
| "dim_in_uint64_range _ = True"

(* Helper: check if all dimensions are within uint64 range *)
definition dims_in_range :: "BabDimension list \<Rightarrow> bool" where
  "dims_in_range dims \<equiv> list_all dim_in_uint64_range dims"

(* Check if array dimensions are well-kinded:
   - All dimensions must be Unknown, Allocatable, or FixedInt (no Fixed)
   - If multiple dimensions, they must all have the same category
   - All FixedInt dimensions must be within uint64 range *)
definition array_dims_well_kinded :: "BabDimension list \<Rightarrow> bool" where
  "array_dims_well_kinded dims \<equiv> dims_uniform dims \<and> dims_in_range dims"

(* Definition: ty is well-kinded in env. *)
fun is_well_kinded :: "BabTyEnv \<Rightarrow> BabType \<Rightarrow> bool" where
  "is_well_kinded env (BabTy_Name loc typeName argTypes) =
    (if typeName |\<in>| TE_TypeVars env then
       argTypes = []
     else
       (case fmlookup (TE_Datatypes env) typeName of
         Some tyVars \<Rightarrow> length argTypes = length tyVars
                        \<and> list_all (is_well_kinded env) argTypes
       | None \<Rightarrow> False))"

| "is_well_kinded env (BabTy_Bool loc) = True"
| "is_well_kinded env (BabTy_FiniteInt loc sign bits) = True"
| "is_well_kinded env (BabTy_MathInt loc) = True"
| "is_well_kinded env (BabTy_MathReal loc) = True"
| "is_well_kinded env (BabTy_Tuple loc tys) = list_all (is_well_kinded env) tys"
| "is_well_kinded env (BabTy_Record loc flds) = list_all (is_well_kinded env \<circ> snd) flds"
| "is_well_kinded env (BabTy_Array loc elemTy dims) =
    (is_well_kinded env elemTy \<and> array_dims_well_kinded dims)"
| "is_well_kinded env (BabTy_Meta n) = True"


(* Integer types are always well-kinded *)
lemma is_integer_type_well_kinded:
  assumes "is_integer_type ty"
  shows "is_well_kinded env ty"
using assms by (cases ty) auto

(* List of metavariables is always well-kinded *)
lemma list_all_is_well_kinded_meta:
  "list_all (is_well_kinded env) (map BabTy_Meta xs)"
  by (induction xs) simp_all


(* Adding type variables to the environment preserves well-kindedness,
   provided the new type variables don't shadow datatype names *)
lemma is_well_kinded_extend_tyvars:
  assumes "is_well_kinded env ty"
      and "extra |\<inter>| fmdom (TE_Datatypes env) = {||}"
  shows "is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extra \<rparr>) ty"
using assms proof (induction ty rule: measure_induct_rule[where f=bab_type_size])
  case (less ty)
  let ?extEnv = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extra \<rparr>"
  show ?case
  proof (cases ty)
    case (BabTy_Name loc name argTypes)
    from less.prems(1) BabTy_Name show ?thesis
    proof (cases "name |\<in>| TE_TypeVars env")
      case True
      (* name is a type variable in env, so also in extended env *)
      with less.prems(1) BabTy_Name have "argTypes = []" by simp
      moreover have "name |\<in>| TE_TypeVars ?extEnv"
        using True by simp
      ultimately show ?thesis using BabTy_Name by simp
    next
      case False
      (* name is not a type variable in env, so must be a datatype in env *)
      with less.prems(1) BabTy_Name obtain dtTyVars where
        dt_lookup: "fmlookup (TE_Datatypes env) name = Some dtTyVars" and
        len_eq: "length argTypes = length dtTyVars" and
        args_wk: "list_all (is_well_kinded env) argTypes"
        by (auto split: option.splits)
      (* name is a datatype, so it's not in extra (by the non-shadowing assumption) *)
      from dt_lookup have "name |\<in>| fmdom (TE_Datatypes env)"
        by (simp add: fmdomI)
      with less.prems(2) have "name |\<notin>| extra"
        by auto
      with False have not_tyvar_ext: "name |\<notin>| TE_TypeVars ?extEnv"
        by simp
      (* By IH, args are well-kinded in extended env *)
      have args_wk_ext: "list_all (is_well_kinded ?extEnv) argTypes"
      proof (simp add: list_all_iff, intro ballI)
        fix t assume t_in: "t \<in> set argTypes"
        from t_in BabTy_Name have "bab_type_size t < bab_type_size ty"
          using bab_type_smaller_than_list by simp
        moreover from args_wk t_in have "is_well_kinded env t"
          by (simp add: list_all_iff)
        ultimately show "is_well_kinded ?extEnv t"
          using less.IH less.prems(2) by blast
      qed
      (* TE_Datatypes is unchanged between env and extEnv *)
      have dt_lookup_ext: "fmlookup (TE_Datatypes ?extEnv) name = Some dtTyVars"
        using dt_lookup by simp
      with not_tyvar_ext len_eq args_wk_ext BabTy_Name show ?thesis by simp
    qed
  next
    case (BabTy_Tuple loc tys)
    from less.prems(1) BabTy_Tuple have tys_wk: "list_all (is_well_kinded env) tys"
      by simp
    have "list_all (is_well_kinded ?extEnv) tys"
    proof (simp add: list_all_iff, intro ballI)
      fix t assume t_in: "t \<in> set tys"
      from t_in BabTy_Tuple have "bab_type_size t < bab_type_size ty"
        using bab_type_smaller_than_list by simp
      moreover from tys_wk t_in have "is_well_kinded env t"
        by (simp add: list_all_iff)
      ultimately show "is_well_kinded ?extEnv t"
        using less.IH less.prems(2) by blast
    qed
    with BabTy_Tuple show ?thesis by simp
  next
    case (BabTy_Record loc flds)
    from less.prems(1) BabTy_Record have flds_wk: "list_all (is_well_kinded env \<circ> snd) flds"
      by simp
    have "list_all (is_well_kinded ?extEnv \<circ> snd) flds"
    proof (simp add: list_all_iff, intro ballI)
      fix fld assume fld_in: "fld \<in> set flds"
      from fld_in BabTy_Record have "bab_type_size (snd fld) < bab_type_size ty"
        using bab_type_smaller_than_fieldlist
        by (metis bab_type_size.simps(7) plus_1_eq_Suc prod.exhaust_sel)
      moreover from flds_wk fld_in have "is_well_kinded env (snd fld)"
        by (simp add: list_all_iff)
      ultimately show "is_well_kinded ?extEnv (snd fld)"
        using less.IH less.prems(2) by blast
    qed
    with BabTy_Record show ?thesis by simp
  next
    case (BabTy_Array loc elemTy dims)
    from less.prems(1) BabTy_Array have elem_wk: "is_well_kinded env elemTy"
      and dims_wk: "array_dims_well_kinded dims"
      by simp_all
    from BabTy_Array have "bab_type_size elemTy < bab_type_size ty"
      by simp
    with elem_wk less.IH less.prems(2) have "is_well_kinded ?extEnv elemTy"
      by blast
    with dims_wk BabTy_Array show ?thesis by simp
  qed simp_all
qed


(* Definition: all types in the range of a substitution are well-kinded *)
definition subst_types_well_kinded :: "BabTyEnv \<Rightarrow> (string, BabType) fmap \<Rightarrow> bool" where
  "subst_types_well_kinded env subst \<equiv>
    \<forall>name ty. fmlookup subst name = Some ty \<longrightarrow> is_well_kinded env ty"

(* Convenient form for substitutions built from zip *)
lemma subst_types_well_kinded_from_zip:
  assumes "list_all (is_well_kinded env) tys"
  shows "subst_types_well_kinded env (fmap_of_list (zip names tys))"
  unfolding subst_types_well_kinded_def
proof (intro allI impI)
  fix name ty
  assume "fmlookup (fmap_of_list (zip names tys)) name = Some ty"
  then have "(name, ty) \<in> set (zip names tys)"
    by (metis fmap_of_list.rep_eq map_of_SomeD)
  then have "ty \<in> set tys"
    by (meson set_zip_rightD)
  with assms show "is_well_kinded env ty"
    by (simp add: list_all_iff)
qed


(* Well-kindedness after substitution across environment extension.
   If ty is well-kinded in env extended with extra type variables (that are not also datatype names),
   and the substitution covers those extra type variables (i.e., extra \<subseteq> fmdom subst),
   and all types in the range of subst are well-kinded in the original env,
   then the result is well-kinded in env. *)
lemma is_well_kinded_substitute_across_ext:
  assumes "is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extra \<rparr>) ty"
      and "extra |\<inter>| fmdom (TE_Datatypes env) = {||}"
      and "extra |\<subseteq>| fmdom subst"
      and "subst_types_well_kinded env subst"
  shows "is_well_kinded env (substitute_bab_type subst ty)"
using assms proof (induction ty rule: measure_induct_rule[where f=bab_type_size])
  case (less ty)
  let ?extEnv = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extra \<rparr>"
  show ?case
  proof (cases ty)
    case (BabTy_Name loc name argTypes)
    show ?thesis
    proof (cases argTypes)
      case Nil
      (* argTypes = [], could be a type variable *)
      show ?thesis
      proof (cases "fmlookup subst name")
        case None
        (* Not substituted - must be well-kinded in env (not one of the extra tyvars) *)
        from "less.prems"(1) BabTy_Name Nil have wk_ext: "is_well_kinded ?extEnv (BabTy_Name loc name [])"
          by simp
        from wk_ext have "name |\<in>| TE_TypeVars ?extEnv \<or>
          (\<exists>dtTyVars. fmlookup (TE_Datatypes ?extEnv) name = Some dtTyVars \<and> dtTyVars = [])"
          by (auto split: if_splits option.splits)
        hence cases: "name |\<in>| TE_TypeVars env |\<union>| extra \<or>
          (\<exists>dtTyVars. fmlookup (TE_Datatypes env) name = Some dtTyVars \<and> dtTyVars = [])"
          by simp
        (* name is not in extra, because extra \<subseteq> fmdom subst and fmlookup subst name = None *)
        from None have "name |\<notin>| fmdom subst"
          by (simp add: fmdom_notI)
        with "less.prems"(3) have "name |\<notin>| extra"
          by auto
        with cases have "name |\<in>| TE_TypeVars env \<or>
          (\<exists>dtTyVars. fmlookup (TE_Datatypes env) name = Some dtTyVars \<and> dtTyVars = [])"
          by auto
        hence "is_well_kinded env (BabTy_Name loc name [])"
          by (auto split: if_splits option.splits)
        with None Nil BabTy_Name show ?thesis by simp
      next
        case (Some substTy)
        (* Substituted - substTy is well-kinded in env by subst_types_well_kinded *)
        from "less.prems"(4) Some have "is_well_kinded env substTy"
          unfolding subst_types_well_kinded_def by blast
        with Some Nil BabTy_Name show ?thesis by simp
      qed
    next
      case (Cons a list)
      (* argTypes non-empty, not a type variable reference, recurse on args *)
      from "less.prems"(1) BabTy_Name Cons have
        not_tyvar: "\<not> (name |\<in>| TE_TypeVars ?extEnv)" and
        dt_lookup: "\<exists>dtTyVars. fmlookup (TE_Datatypes ?extEnv) name = Some dtTyVars \<and>
                    length (a # list) = length dtTyVars" and
        args_wk: "list_all (is_well_kinded ?extEnv) (a # list)"
        by (auto split: if_splits option.splits)
      from dt_lookup obtain dtTyVars where
        dt: "fmlookup (TE_Datatypes env) name = Some dtTyVars" and
        len_eq: "length (a # list) = length dtTyVars"
        by auto
      (* name is a datatype, so it's not in extra (by the non-shadowing assumption) *)
      from dt have "name |\<in>| fmdom (TE_Datatypes env)"
        by (simp add: fmdomI)
      with "less.prems"(2) have "name |\<notin>| extra"
        by auto
      (* name is not a type variable in env either *)
      with not_tyvar have not_tyvar_env: "name |\<notin>| TE_TypeVars env"
        by simp
      (* By IH, substituted args are well-kinded in env *)
      have subst_args_wk: "list_all (is_well_kinded env) (map (substitute_bab_type subst) (a # list))"
      proof -
        have "\<forall>t \<in> set (a # list). is_well_kinded env (substitute_bab_type subst t)"
        proof
          fix t assume t_in: "t \<in> set (a # list)"
          from t_in BabTy_Name Cons have "bab_type_size t < bab_type_size ty"
            using bab_type_smaller_than_list bab_type_size.simps(1) plus_1_eq_Suc by presburger
          moreover from args_wk t_in have "is_well_kinded ?extEnv t"
            unfolding list.pred_set by blast
          ultimately show "is_well_kinded env (substitute_bab_type subst t)"
            using "less.IH" "less.prems"(2) "less.prems"(3) "less.prems"(4) by blast
        qed
        thus ?thesis by (simp add: list_all_iff)
      qed
      have len_eq': "length (map (substitute_bab_type subst) (a # list)) = length dtTyVars"
        using len_eq by simp
      with dt not_tyvar_env len_eq' subst_args_wk BabTy_Name Cons show ?thesis
        by auto
    qed
  next
    case (BabTy_Bool loc)
    then show ?thesis by simp
  next
    case (BabTy_FiniteInt loc sign bits)
    then show ?thesis by simp
  next
    case (BabTy_MathInt loc)
    then show ?thesis by simp
  next
    case (BabTy_MathReal loc)
    then show ?thesis by simp
  next
    case (BabTy_Tuple loc tys)
    from "less.prems"(1) BabTy_Tuple have tys_wk: "list_all (is_well_kinded ?extEnv) tys"
      by simp
    have "list_all (is_well_kinded env) (map (substitute_bab_type subst) tys)"
    proof (simp add: list_all_iff, intro ballI)
      fix t assume t_in: "t \<in> set tys"
      from t_in BabTy_Tuple have "bab_type_size t < bab_type_size ty"
        using bab_type_smaller_than_list by simp
      moreover from tys_wk t_in have "is_well_kinded ?extEnv t"
        by (simp add: list_all_iff)
      ultimately show "is_well_kinded env (substitute_bab_type subst t)"
        using "less.IH" "less.prems"(2) "less.prems"(3) "less.prems"(4) by blast
    qed
    with BabTy_Tuple show ?thesis by simp
  next
    case (BabTy_Record loc flds)
    from "less.prems"(1) BabTy_Record have flds_wk: "list_all (is_well_kinded ?extEnv \<circ> snd) flds"
      by simp
    have "list_all (is_well_kinded env \<circ> snd) (map (\<lambda>(name, ty). (name, substitute_bab_type subst ty)) flds)"
    proof -
      have "\<forall>fld \<in> set flds. is_well_kinded env (substitute_bab_type subst (snd fld))"
      proof
        fix fld assume fld_in: "fld \<in> set flds"
        from fld_in BabTy_Record have "bab_type_size (snd fld) < bab_type_size ty"
          using bab_type_smaller_than_fieldlist
          by (metis bab_type_size.simps(7) plus_1_eq_Suc prod.exhaust_sel)
        moreover from flds_wk fld_in have "is_well_kinded ?extEnv (snd fld)"
          unfolding list.pred_set by auto
        ultimately show "is_well_kinded env (substitute_bab_type subst (snd fld))"
          using "less.IH" "less.prems"(2) "less.prems"(3) "less.prems"(4) by blast
      qed
      thus ?thesis by (auto simp: list_all_iff)
    qed
    with BabTy_Record show ?thesis by auto
  next
    case (BabTy_Array loc elemTy dims)
    from "less.prems"(1) BabTy_Array have elem_wk: "is_well_kinded ?extEnv elemTy"
      and dims_wk: "array_dims_well_kinded dims"
      by simp_all
    from BabTy_Array have "bab_type_size elemTy < bab_type_size ty"
      by simp
    with elem_wk "less.IH" "less.prems"(2) "less.prems"(3) "less.prems"(4)
    have "is_well_kinded env (substitute_bab_type subst elemTy)"
      by blast
    with dims_wk BabTy_Array show ?thesis by simp
  next
    case (BabTy_Meta n)
    then show ?thesis by simp
  qed
qed

(* Substitution preserves well-kindedness when all substituted types are well-kinded.
   This is a corollary of is_well_kinded_substitute_across_ext with extra = {||} *)
corollary substitute_bab_type_well_kinded:
  assumes "is_well_kinded env ty"
      and "subst_types_well_kinded env subst"
  shows "is_well_kinded env (substitute_bab_type subst ty)"
proof -
  (* ty is well-kinded in env, which equals env with empty extension *)
  have "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| {||} \<rparr> = env"
    by simp
  with assms(1) have wk_ext: "is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| {||} \<rparr>) ty"
    by simp
  (* The conditions for is_well_kinded_substitute_across_ext are trivially satisfied *)
  have disjoint: "{||} |\<inter>| fmdom (TE_Datatypes env) = {||}"
    by simp
  have subset: "{||} |\<subseteq>| fmdom subst"
    by simp
  from is_well_kinded_substitute_across_ext[OF wk_ext disjoint subset assms(2)]
  show ?thesis by simp
qed


end
