theory Unify
  imports "../type_system/TypesEqual"
begin

(* Unification for BabTypes.

   This module defines:
   - Metavariable substitutions (mapping nat to BabType)
   - Application of substitutions to types
   - Composition of substitutions
   - The unification algorithm
  
   Proofs of correctness (soundness, most general unifier, completeness) are in Unify2.thy.

   Note that the "unify" function provided here does not descend into types inside
   BabDim_Fixed terms. It is intended for use on types where any BabDim_Fixed have
   already been elaborated to BabDim_FixedInt.
*)


(* ========================================================================== *)
(* Metavariables                                                              *)
(* ========================================================================== *)

(* Collect all metavariables in a type *)
fun type_metavars :: "BabType \<Rightarrow> nat set" where
  "type_metavars (BabTy_Meta n) = {n}"
| "type_metavars (BabTy_Name _ _ tyargs) = \<Union>(set (map type_metavars tyargs))"
| "type_metavars (BabTy_Bool _) = {}"
| "type_metavars (BabTy_FiniteInt _ _ _) = {}"
| "type_metavars (BabTy_MathInt _) = {}"
| "type_metavars (BabTy_MathReal _) = {}"
| "type_metavars (BabTy_Tuple _ types) = \<Union>(set (map type_metavars types))"
| "type_metavars (BabTy_Record _ flds) = \<Union>(set (map (type_metavars \<circ> snd) flds))"
| "type_metavars (BabTy_Array _ ty _) = type_metavars ty"

(* Collect all metavariables in a list of types *)
definition list_metavars :: "BabType list \<Rightarrow> nat set" where
  "list_metavars tys = \<Union>(set (map type_metavars tys))"

(* Check if metavariable n occurs in type ty *)
definition occurs :: "nat \<Rightarrow> BabType \<Rightarrow> bool" where
  "occurs n ty = (n \<in> type_metavars ty)"

(* Metavariables in a type are finite *)
lemma finite_type_metavars: "finite (type_metavars ty)"
proof (induction ty rule: measure_induct_rule[where f=bab_type_size])
  case (less ty)
  show ?case
  proof (cases ty)
    case (BabTy_Meta n)
    then show ?thesis by simp
  next
    case (BabTy_Name loc name tyargs)
    have "\<forall>arg \<in> set tyargs. finite (type_metavars arg)"
    proof
      fix arg assume "arg \<in> set tyargs"
      hence "bab_type_size arg < bab_type_size ty"
        using BabTy_Name bab_type_smaller_than_list by fastforce
      thus "finite (type_metavars arg)" using less.IH by blast
    qed
    then show ?thesis using BabTy_Name by auto
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
    case (BabTy_Tuple loc types)
    have "\<forall>t \<in> set types. finite (type_metavars t)"
    proof
      fix t assume "t \<in> set types"
      hence "bab_type_size t < bab_type_size ty"
        using BabTy_Tuple bab_type_smaller_than_list by fastforce
      thus "finite (type_metavars t)" using less.IH by blast
    qed
    then show ?thesis using BabTy_Tuple by auto
  next
    case (BabTy_Record loc flds)
    have "\<forall>f \<in> set flds. finite (type_metavars (snd f))"
    proof
      fix f assume "f \<in> set flds"
      hence "bab_type_size (snd f) < bab_type_size ty"
        using BabTy_Record bab_type_smaller_than_fieldlist[of "fst f" "snd f" flds] by simp
      thus "finite (type_metavars (snd f))" using less.IH by blast
    qed
    then show ?thesis using BabTy_Record by auto
  next
    case (BabTy_Array loc elem dims)
    have "bab_type_size elem < bab_type_size ty"
      using BabTy_Array by simp
    hence "finite (type_metavars elem)" using less.IH by blast
    then show ?thesis using BabTy_Array by auto
  qed
qed

(* Metavariables in a list of types are finite *)
lemma finite_list_metavars: "finite (list_metavars tys)"
  unfolding list_metavars_def using finite_type_metavars by auto


(* ========================================================================== *)
(* Substitutions                                                              *)
(* ========================================================================== *)

(* A substitution maps metavariable IDs (nat) to types *)
type_synonym MetaSubst = "(nat, BabType) fmap"

(* The empty substitution *)
definition empty_subst :: MetaSubst where
  "empty_subst = fmempty"

(* The singleton substitution: maps n to ty *)
definition singleton_subst :: "nat \<Rightarrow> BabType \<Rightarrow> MetaSubst" where
  "singleton_subst n ty = fmupd n ty fmempty"

(* Apply a metavariable substitution to a type.
   This replaces BabTy_Meta n with subst(n) if defined, otherwise leaves it. *)
fun apply_subst :: "MetaSubst \<Rightarrow> BabType \<Rightarrow> BabType" where
  "apply_subst subst (BabTy_Meta n) =
    (case fmlookup subst n of
      Some ty \<Rightarrow> ty
    | None \<Rightarrow> BabTy_Meta n)"
| "apply_subst subst (BabTy_Name loc name tyargs) =
    BabTy_Name loc name (map (apply_subst subst) tyargs)"
| "apply_subst subst (BabTy_Bool loc) = BabTy_Bool loc"
| "apply_subst subst (BabTy_FiniteInt loc sign bits) = BabTy_FiniteInt loc sign bits"
| "apply_subst subst (BabTy_MathInt loc) = BabTy_MathInt loc"
| "apply_subst subst (BabTy_MathReal loc) = BabTy_MathReal loc"
| "apply_subst subst (BabTy_Tuple loc types) =
    BabTy_Tuple loc (map (apply_subst subst) types)"
| "apply_subst subst (BabTy_Record loc flds) =
    BabTy_Record loc (map (\<lambda>(name, ty). (name, apply_subst subst ty)) flds)"
| "apply_subst subst (BabTy_Array loc ty dims) =
    BabTy_Array loc (apply_subst subst ty) dims"

(* Apply empty substitution is identity. *)
lemma apply_subst_empty [simp]:
  "apply_subst fmempty ty = ty"
proof (induction ty rule: measure_induct_rule[where f=bab_type_size])
  case (less ty)
  show ?case
  proof (cases ty)
    case (BabTy_Meta n)
    then show ?thesis by simp
  next
    case (BabTy_Name loc name tyargs)
    have "\<forall>arg \<in> set tyargs. apply_subst fmempty arg = arg"
    proof
      fix arg assume "arg \<in> set tyargs"
      hence "bab_type_size arg < bab_type_size ty"
        using BabTy_Name bab_type_smaller_than_list by fastforce
      thus "apply_subst fmempty arg = arg" using less.IH by blast
    qed
    then show ?thesis using BabTy_Name by (simp add: map_idI)
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
    case (BabTy_Tuple loc types)
    have "\<forall>t \<in> set types. apply_subst fmempty t = t"
    proof
      fix t assume "t \<in> set types"
      hence "bab_type_size t < bab_type_size ty"
        using BabTy_Tuple bab_type_smaller_than_list by fastforce
      thus "apply_subst fmempty t = t" using less.IH by blast
    qed
    then show ?thesis using BabTy_Tuple by (simp add: map_idI)
  next
    case (BabTy_Record loc flds)
    have "\<forall>f \<in> set flds. apply_subst fmempty (snd f) = snd f"
    proof
      fix f assume "f \<in> set flds"
      hence "bab_type_size (snd f) < bab_type_size ty"
        using BabTy_Record bab_type_smaller_than_fieldlist[of "fst f" "snd f" flds] by simp
      thus "apply_subst fmempty (snd f) = snd f" using less.IH by blast
    qed
    then show ?thesis using BabTy_Record
      by (auto simp: map_idI intro!: map_idI)
  next
    case (BabTy_Array loc elem dims)
    have "bab_type_size elem < bab_type_size ty"
      using BabTy_Array by simp
    hence "apply_subst fmempty elem = elem" using less.IH by blast
    then show ?thesis using BabTy_Array by simp
  qed
qed

(* List version of apply_subst_empty. *)
lemma map_apply_subst_empty [simp]:
  "map (apply_subst fmempty) tys = tys"
  by (induction tys) auto

(* Effect of applying a singleton subst *)
lemma apply_subst_singleton:
  "apply_subst (singleton_subst n ty') (BabTy_Meta n) = ty'"
  by (simp add: singleton_subst_def)

lemma apply_subst_singleton_other:
  "n \<noteq> m \<Longrightarrow> apply_subst (singleton_subst n ty') (BabTy_Meta m) = BabTy_Meta m"
  by (simp add: singleton_subst_def)

(* If n doesn't occur in ty, then applying singleton_subst n ty' leaves ty unchanged *)
lemma apply_subst_singleton_no_occurs:
  "\<not> occurs n ty \<Longrightarrow> apply_subst (singleton_subst n ty') ty = ty"
proof (induction "singleton_subst n ty'" ty rule: apply_subst.induct)
  case (1 m)
  hence "n \<noteq> m" by (simp add: occurs_def)
  then show ?case by (simp add: singleton_subst_def)
next
  case (2 loc name tyargs)
  then show ?case
    by (simp add: occurs_def map_idI)
next
  case (3 loc)
  then show ?case by simp
next
  case (4 loc sign bits)
  then show ?case by simp
next
  case (5 loc)
  then show ?case by simp
next
  case (6 loc)
  then show ?case by simp
next
  case (7 loc types)
  then show ?case
    by (simp add: occurs_def map_idI)
next
  case (8 loc flds)
  then show ?case
    by (auto simp: occurs_def intro!: map_idI)
next
  case (9 loc elem dims)
  then show ?case
    by (simp add: occurs_def)
qed

(* The range of a singleton subst is just the given type. *)
lemma fmran'_singleton_subst: "fmran' (singleton_subst n ty) = {ty}"
  by (auto simp: singleton_subst_def fmran'_def split: if_splits)

(* Applying the same substitution to equal types preserves equality *)
lemma types_equal_apply_subst:
  "types_equal ty1 ty2 \<Longrightarrow> types_equal (apply_subst s ty1) (apply_subst s ty2)"
proof (induction ty1 arbitrary: ty2 rule: measure_induct_rule[where f=bab_type_size])
  case (less ty1)
  then show ?case
  proof (cases ty1)
    case (BabTy_Meta n)
    then have "ty2 = BabTy_Meta n" using less.prems by (cases ty2; simp)
    then show ?thesis using BabTy_Meta types_equal_reflexive by simp
  next
    case (BabTy_Name loc name tyargs)
    from less.prems BabTy_Name obtain loc2 name2 tyargs2 where ty2_eq: "ty2 = BabTy_Name loc2 name2 tyargs2"
      by (cases ty2; simp)
    from less.prems BabTy_Name ty2_eq have name_eq: "name = name2"
      and len_eq: "length tyargs = length tyargs2"
      and args_eq: "list_all (\<lambda>(t1, t2). types_equal t1 t2) (zip tyargs tyargs2)"
      by (simp_all add: types_equal_Name del: types_equal.simps)
    have "\<forall>i < length tyargs. types_equal (apply_subst s (tyargs ! i)) (apply_subst s (tyargs2 ! i))"
    proof (intro allI impI)
      fix i assume i_bound: "i < length tyargs"
      hence "bab_type_size (tyargs ! i) < bab_type_size ty1"
        using BabTy_Name bab_type_smaller_than_list nth_mem by fastforce
      moreover have "types_equal (tyargs ! i) (tyargs2 ! i)"
        using args_eq i_bound len_eq by (simp add: list_all_length)
      ultimately show "types_equal (apply_subst s (tyargs ! i)) (apply_subst s (tyargs2 ! i))"
        using less.IH by blast
    qed
    hence "list_all (\<lambda>(t1, t2). types_equal (apply_subst s t1) (apply_subst s t2)) (zip tyargs tyargs2)"
      using len_eq by (simp add: list_all_length)
    then show ?thesis using BabTy_Name ty2_eq len_eq name_eq
      by (simp add: list_all_length types_equal_Name del: types_equal.simps)
  next
    case (BabTy_Bool loc)
    then have "\<exists>loc'. ty2 = BabTy_Bool loc'" using less.prems by (cases ty2; simp)
    then show ?thesis using BabTy_Bool by (auto simp add: types_equal_reflexive)
  next
    case (BabTy_FiniteInt loc sign bits)
    then have "\<exists>loc'. ty2 = BabTy_FiniteInt loc' sign bits" using less.prems by (cases ty2; auto)
    then show ?thesis using BabTy_FiniteInt by (auto simp add: types_equal_reflexive)
  next
    case (BabTy_MathInt loc)
    then have "\<exists>loc'. ty2 = BabTy_MathInt loc'" using less.prems by (cases ty2; simp)
    then show ?thesis using BabTy_MathInt by (auto simp add: types_equal_reflexive)
  next
    case (BabTy_MathReal loc)
    then have "\<exists>loc'. ty2 = BabTy_MathReal loc'" using less.prems by (cases ty2; simp)
    then show ?thesis using BabTy_MathReal by (auto simp add: types_equal_reflexive)
  next
    case (BabTy_Tuple loc types)
    from less.prems BabTy_Tuple obtain loc2 types2 where ty2_eq: "ty2 = BabTy_Tuple loc2 types2"
      by (cases ty2; simp)
    from less.prems BabTy_Tuple ty2_eq have len_eq: "length types = length types2"
      and elems_eq: "list_all (\<lambda>(t1, t2). types_equal t1 t2) (zip types types2)"
      by (simp_all add: types_equal_Tuple del: types_equal.simps)
    have "\<forall>i < length types. types_equal (apply_subst s (types ! i)) (apply_subst s (types2 ! i))"
    proof (intro allI impI)
      fix i assume i_bound: "i < length types"
      hence "bab_type_size (types ! i) < bab_type_size ty1"
        using BabTy_Tuple bab_type_smaller_than_list nth_mem by fastforce
      moreover have "types_equal (types ! i) (types2 ! i)"
        using elems_eq i_bound len_eq by (simp add: list_all_length)
      ultimately show "types_equal (apply_subst s (types ! i)) (apply_subst s (types2 ! i))"
        using less.IH by blast
    qed
    hence "list_all (\<lambda>(t1, t2). types_equal (apply_subst s t1) (apply_subst s t2)) (zip types types2)"
      using len_eq by (simp add: list_all_length)
    then show ?thesis using BabTy_Tuple ty2_eq len_eq
      by (simp add: list_all_length types_equal_Tuple del: types_equal.simps)
  next
    case (BabTy_Record loc flds)
    from less.prems BabTy_Record obtain loc2 flds2 where ty2_eq: "ty2 = BabTy_Record loc2 flds2"
      by (cases ty2; simp)
    from less.prems BabTy_Record ty2_eq have len_eq: "length flds = length flds2"
      and flds_eq: "list_all (\<lambda>(f1, f2). fst f1 = fst f2 \<and> types_equal (snd f1) (snd f2)) (zip flds flds2)"
      by (simp_all add: types_equal_Record del: types_equal.simps)
    have "\<forall>i < length flds2. fst (flds ! i) = fst (flds2 ! i) \<and>
           types_equal (apply_subst s (snd (flds ! i))) (apply_subst s (snd (flds2 ! i)))"
    proof (intro allI impI conjI)
      fix i assume i_bound: "i < length flds2"
      from flds_eq len_eq i_bound show "fst (flds ! i) = fst (flds2 ! i)"
        by (simp add: list_all_length)
    next
      fix i assume i_bound: "i < length flds2"
      hence i_bound': "i < length flds" using len_eq by simp
      from flds_eq len_eq i_bound have teq: "types_equal (snd (flds ! i)) (snd (flds2 ! i))"
        by (simp add: list_all_length)
      have "flds ! i \<in> set flds" using i_bound' by simp
      hence "snd (flds ! i) \<in> snd ` set flds" by force
      hence "bab_type_size (snd (flds ! i)) < bab_type_size ty1"
        using BabTy_Record bab_type_smaller_than_fieldlist by fastforce
      thus "types_equal (apply_subst s (snd (flds ! i))) (apply_subst s (snd (flds2 ! i)))"
        using less.IH teq by blast
    qed
    then show ?thesis using BabTy_Record ty2_eq len_eq
      by (simp add: list_all_length types_equal_Record case_prod_beta del: types_equal.simps)
  next
    case (BabTy_Array loc elem dims)
    from less.prems BabTy_Array obtain loc2 elem2 where ty2_eq: "ty2 = BabTy_Array loc2 elem2 dims"
      by (cases ty2; simp)
    from less.prems BabTy_Array ty2_eq have elem_eq: "types_equal elem elem2"
      by simp
    have "bab_type_size elem < bab_type_size ty1"
      using BabTy_Array by simp
    hence "types_equal (apply_subst s elem) (apply_subst s elem2)"
      using less.IH elem_eq by blast
    then show ?thesis using BabTy_Array ty2_eq by simp
  qed
qed


(* ========================================================================== *)
(* Effect of substitutions on metavariables                                   *)
(* ========================================================================== *)

(* Find all metavariables appearing in the range of a substitution *)
definition subst_range_mvs :: "MetaSubst \<Rightarrow> nat set" where
  "subst_range_mvs subst = \<Union>(type_metavars ` fmran' subst)"

(* Metavars after applying a substitution come from:
   - metavars in ty that are not in dom(subst), OR
   - metavars in the range of subst (for substituted vars) *)
lemma apply_subst_metavars_result:
  "type_metavars (apply_subst subst ty) \<subseteq>
   (type_metavars ty - fset (fmdom subst)) \<union> subst_range_mvs subst"
proof (induction ty rule: apply_subst.induct)
  case (1 subst n)
  show ?case
  proof (cases "fmlookup subst n")
    case None
    then show ?thesis by auto
  next
    case (Some ty')
    then have "ty' \<in> fmran' subst"
      by (simp add: fmran'I)
    then show ?thesis
      using Some by (auto simp: subst_range_mvs_def)
  qed
next
  case (2 subst loc name tyargs)
  then show ?case
    by (auto simp: subst_range_mvs_def)
next
  case (3 subst loc)
  then show ?case by simp
next
  case (4 subst loc sign bits)
  then show ?case by simp
next
  case (5 subst loc)
  then show ?case by simp
next
  case (6 subst loc)
  then show ?case by simp
next
  case (7 subst loc types)
  then show ?case
    by (auto simp: subst_range_mvs_def)
next
  case (8 subst loc flds)
  (* BabTy_Record: need to show result for each field type *)
  show ?case
  proof
    fix x
    assume "x \<in> type_metavars (apply_subst subst (BabTy_Record loc flds))"
    then obtain a b where ab_in: "(a, b) \<in> set flds"
      and x_in: "x \<in> type_metavars (apply_subst subst b)"
      by auto
    from "8.IH"[OF ab_in refl] x_in
    have "x \<in> type_metavars b - fset (fmdom subst) \<union> subst_range_mvs subst"
      by auto
    then show "x \<in> type_metavars (BabTy_Record loc flds) - fset (fmdom subst) \<union> subst_range_mvs subst"
      using ab_in by (auto intro: bexI[of _ "(a, b)"])
  qed
next
  case (9 subst loc ty dims)
  (* BabTy_Array: just the element type *)
  then show ?case
    by auto
qed

(* Corollary: if n is in dom(subst) and not in range, it's eliminated from result *)
lemma apply_subst_eliminates_dom:
  assumes "n \<in> fset (fmdom subst)"
      and "n \<notin> subst_range_mvs subst"
  shows "n \<notin> type_metavars (apply_subst subst ty)"
proof -
  have "type_metavars (apply_subst subst ty) \<subseteq>
        (type_metavars ty - fset (fmdom subst)) \<union> subst_range_mvs subst"
    by (rule apply_subst_metavars_result)
  thus ?thesis using assms by auto
qed

(* Substitution on ground types is identity. *)
lemma apply_subst_ground:
  "is_ground ty \<Longrightarrow> apply_subst subst ty = ty"
proof (induction ty rule: is_ground.induct)
  case (1 n)
  then show ?case by simp
next
  case (2 loc name tyargs)
  then show ?case
    by (simp add: list_all_iff map_idI)
next
  case (3 loc)
  then show ?case by simp
next
  case (4 loc sign bits)
  then show ?case by simp
next
  case (5 loc)
  then show ?case by simp
next
  case (6 loc)
  then show ?case by simp
next
  case (7 loc types)
  then show ?case
    by (simp add: list_all_iff map_idI)
next
  case (8 loc flds)
  then show ?case
    by (auto simp: list_all_iff intro!: map_idI)
next
  case (9 loc ty dims)
  then show ?case by simp
qed


(* ========================================================================== *)
(* Substitution equality (up to types_equal)                                  *)
(* ========================================================================== *)

(* Two substitutions are equal if they produce types_equal results on all types *)
definition subst_equal :: "MetaSubst \<Rightarrow> MetaSubst \<Rightarrow> bool" where
  "subst_equal \<sigma>1 \<sigma>2 \<equiv> \<forall>ty. types_equal (apply_subst \<sigma>1 ty) (apply_subst \<sigma>2 ty)"

lemma subst_equal_refl: "subst_equal \<sigma> \<sigma>"
  by (simp add: subst_equal_def types_equal_reflexive del: types_equal.simps)

lemma subst_equal_sym: "subst_equal \<sigma>1 \<sigma>2 \<Longrightarrow> subst_equal \<sigma>2 \<sigma>1"
  by (simp add: subst_equal_def types_equal_symmetric del: types_equal.simps)

lemma subst_equal_trans: "subst_equal \<sigma>1 \<sigma>2 \<Longrightarrow> subst_equal \<sigma>2 \<sigma>3 \<Longrightarrow> subst_equal \<sigma>1 \<sigma>3"
  by (meson subst_equal_def types_equal_transitive)


(* ========================================================================== *)
(* Composition of substitutions                                                *)
(* ========================================================================== *)

(* Compose two substitutions: (compose_subst s2 s1) first applies s1, then s2.

   For a metavariable n:
   - If s1(n) = ty, then (s2 \<circ> s1)(n) = s2(ty) (apply s2 to the result)
   - If s1(n) is undefined but s2(n) = ty, then (s2 \<circ> s1)(n) = ty
   - Otherwise undefined

   This ensures: apply_subst (compose_subst s2 s1) ty = apply_subst s2 (apply_subst s1 ty)
*)
definition compose_subst :: "MetaSubst \<Rightarrow> MetaSubst \<Rightarrow> MetaSubst" where
  "compose_subst s2 s1 = s2 ++\<^sub>f fmmap (apply_subst s2) s1"

(* Composition of substitutions is correct *)
lemma compose_subst_correct:
  "apply_subst (compose_subst s2 s1) ty = apply_subst s2 (apply_subst s1 ty)"
proof (induction ty rule: apply_subst.induct)
  case (1 subst n)
  then show ?case
    by (auto simp: compose_subst_def split: option.splits)
next
  case (2 subst loc name tyargs)
  then show ?case by simp
next
  case (3 subst loc)
  then show ?case by simp
next
  case (4 subst loc sign bits)
  then show ?case by simp
next
  case (5 subst loc)
  then show ?case by simp
next
  case (6 subst loc)
  then show ?case by simp
next
  case (7 subst loc types)
  then show ?case by simp
next
  case (8 subst loc flds)
  then show ?case by (auto simp: case_prod_beta)
next
  case (9 subst loc elem dims)
  then show ?case by simp
qed

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

(* "Groundness is preserved under composition": 
   Once a type becomes ground (under some substitution), it will remain ground even
   after composing further substitutions. *)
lemma compose_subst_preserves_ground:
  assumes "types_equal (apply_subst \<theta> ty1) ty2"
      and "is_ground ty2"
    shows "types_equal (apply_subst (compose_subst \<eta> \<theta>) ty1) ty2"
proof -
  have "apply_subst (compose_subst \<eta> \<theta>) ty1 = apply_subst \<eta> (apply_subst \<theta> ty1)"
    by (simp add: compose_subst_correct)
  also have "types_equal (apply_subst \<eta> (apply_subst \<theta> ty1)) (apply_subst \<eta> ty2)"
    using types_equal_apply_subst[OF assms(1)] .
  also have "apply_subst \<eta> ty2 = ty2"
    using apply_subst_ground[OF assms(2)] .
  finally show ?thesis by simp
qed


(* ========================================================================== *)
(* Unification algorithm                                                      *)
(* ========================================================================== *)

(* Unify two types, returning a most general unifier if one exists.
   Returns None if unification fails (incompatible types or occurs check).

   The algorithm:
   - If both types are identical ground types, return empty substitution
   - If one is a metavariable, check occurs and return singleton substitution
   - If both are compound types of the same constructor, unify components
   - Otherwise, fail (return None)
*)

function (domintros) unify :: "BabType \<Rightarrow> BabType \<Rightarrow> MetaSubst option"
and unify_list :: "BabType list \<Rightarrow> BabType list \<Rightarrow> MetaSubst option" where
  (* Metavariable cases *)
  "unify (BabTy_Meta n) (BabTy_Meta m) =
    (if n = m then Some fmempty
     else Some (singleton_subst n (BabTy_Meta m)))"

| "unify (BabTy_Meta n) (BabTy_Name loc name tyargs) =
    (if occurs n (BabTy_Name loc name tyargs) then None
     else Some (singleton_subst n (BabTy_Name loc name tyargs)))"

| "unify (BabTy_Meta n) (BabTy_Bool loc) =
    Some (singleton_subst n (BabTy_Bool loc))"

| "unify (BabTy_Meta n) (BabTy_FiniteInt loc sign bits) =
    Some (singleton_subst n (BabTy_FiniteInt loc sign bits))"

| "unify (BabTy_Meta n) (BabTy_MathInt loc) =
    Some (singleton_subst n (BabTy_MathInt loc))"

| "unify (BabTy_Meta n) (BabTy_MathReal loc) =
    Some (singleton_subst n (BabTy_MathReal loc))"

| "unify (BabTy_Meta n) (BabTy_Tuple loc tys) =
    (if occurs n (BabTy_Tuple loc tys) then None
     else Some (singleton_subst n (BabTy_Tuple loc tys)))"

| "unify (BabTy_Meta n) (BabTy_Record loc flds) =
    (if occurs n (BabTy_Record loc flds) then None
     else Some (singleton_subst n (BabTy_Record loc flds)))"

| "unify (BabTy_Meta n) (BabTy_Array loc elem dims) =
    (if occurs n (BabTy_Array loc elem dims) then None
     else Some (singleton_subst n (BabTy_Array loc elem dims)))"

  (* Symmetric metavariable cases - ty on left, meta on right *)
| "unify (BabTy_Name loc name tyargs) (BabTy_Meta n) =
    (if occurs n (BabTy_Name loc name tyargs) then None
     else Some (singleton_subst n (BabTy_Name loc name tyargs)))"

| "unify (BabTy_Bool loc) (BabTy_Meta n) =
    Some (singleton_subst n (BabTy_Bool loc))"

| "unify (BabTy_FiniteInt loc sign bits) (BabTy_Meta n) =
    Some (singleton_subst n (BabTy_FiniteInt loc sign bits))"

| "unify (BabTy_MathInt loc) (BabTy_Meta n) =
    Some (singleton_subst n (BabTy_MathInt loc))"

| "unify (BabTy_MathReal loc) (BabTy_Meta n) =
    Some (singleton_subst n (BabTy_MathReal loc))"

| "unify (BabTy_Tuple loc tys) (BabTy_Meta n) =
    (if occurs n (BabTy_Tuple loc tys) then None
     else Some (singleton_subst n (BabTy_Tuple loc tys)))"

| "unify (BabTy_Record loc flds) (BabTy_Meta n) =
    (if occurs n (BabTy_Record loc flds) then None
     else Some (singleton_subst n (BabTy_Record loc flds)))"

| "unify (BabTy_Array loc elem dims) (BabTy_Meta n) =
    (if occurs n (BabTy_Array loc elem dims) then None
     else Some (singleton_subst n (BabTy_Array loc elem dims)))"

  (* Base types - must match exactly *)
| "unify (BabTy_Bool _) (BabTy_Bool _) = Some fmempty"
| "unify (BabTy_FiniteInt _ s1 b1) (BabTy_FiniteInt _ s2 b2) =
    (if s1 = s2 \<and> b1 = b2 then Some fmempty else None)"
| "unify (BabTy_MathInt _) (BabTy_MathInt _) = Some fmempty"
| "unify (BabTy_MathReal _) (BabTy_MathReal _) = Some fmempty"

  (* Named types - name must match, then unify type arguments *)
| "unify (BabTy_Name _ n1 args1) (BabTy_Name _ n2 args2) =
    (if n1 = n2 \<and> length args1 = length args2 then
       unify_list args1 args2
     else None)"

  (* Tuples - unify componentwise *)
| "unify (BabTy_Tuple _ tys1) (BabTy_Tuple _ tys2) =
    (if length tys1 = length tys2 then
       unify_list tys1 tys2
     else None)"

  (* Records - field names must match, unify types *)
| "unify (BabTy_Record _ flds1) (BabTy_Record _ flds2) =
    (if length flds1 = length flds2 \<and> map fst flds1 = map fst flds2 then
       unify_list (map snd flds1) (map snd flds2)
     else None)"

  (* Arrays - unify element types, dimensions must match *)
| "unify (BabTy_Array _ elem1 dims1) (BabTy_Array _ elem2 dims2) =
    (if dims1 = dims2 then unify elem1 elem2 else None)"

  (* Mismatched constructors - all remaining cases fail *)
| "unify (BabTy_Name _ _ _) (BabTy_Bool _) = None"
| "unify (BabTy_Name _ _ _) (BabTy_FiniteInt _ _ _) = None"
| "unify (BabTy_Name _ _ _) (BabTy_MathInt _) = None"
| "unify (BabTy_Name _ _ _) (BabTy_MathReal _) = None"
| "unify (BabTy_Name _ _ _) (BabTy_Tuple _ _) = None"
| "unify (BabTy_Name _ _ _) (BabTy_Record _ _) = None"
| "unify (BabTy_Name _ _ _) (BabTy_Array _ _ _) = None"

| "unify (BabTy_Bool _) (BabTy_Name _ _ _) = None"
| "unify (BabTy_Bool _) (BabTy_FiniteInt _ _ _) = None"
| "unify (BabTy_Bool _) (BabTy_MathInt _) = None"
| "unify (BabTy_Bool _) (BabTy_MathReal _) = None"
| "unify (BabTy_Bool _) (BabTy_Tuple _ _) = None"
| "unify (BabTy_Bool _) (BabTy_Record _ _) = None"
| "unify (BabTy_Bool _) (BabTy_Array _ _ _) = None"

| "unify (BabTy_FiniteInt _ _ _) (BabTy_Name _ _ _) = None"
| "unify (BabTy_FiniteInt _ _ _) (BabTy_Bool _) = None"
| "unify (BabTy_FiniteInt _ _ _) (BabTy_MathInt _) = None"
| "unify (BabTy_FiniteInt _ _ _) (BabTy_MathReal _) = None"
| "unify (BabTy_FiniteInt _ _ _) (BabTy_Tuple _ _) = None"
| "unify (BabTy_FiniteInt _ _ _) (BabTy_Record _ _) = None"
| "unify (BabTy_FiniteInt _ _ _) (BabTy_Array _ _ _) = None"

| "unify (BabTy_MathInt _) (BabTy_Name _ _ _) = None"
| "unify (BabTy_MathInt _) (BabTy_Bool _) = None"
| "unify (BabTy_MathInt _) (BabTy_FiniteInt _ _ _) = None"
| "unify (BabTy_MathInt _) (BabTy_MathReal _) = None"
| "unify (BabTy_MathInt _) (BabTy_Tuple _ _) = None"
| "unify (BabTy_MathInt _) (BabTy_Record _ _) = None"
| "unify (BabTy_MathInt _) (BabTy_Array _ _ _) = None"

| "unify (BabTy_MathReal _) (BabTy_Name _ _ _) = None"
| "unify (BabTy_MathReal _) (BabTy_Bool _) = None"
| "unify (BabTy_MathReal _) (BabTy_FiniteInt _ _ _) = None"
| "unify (BabTy_MathReal _) (BabTy_MathInt _) = None"
| "unify (BabTy_MathReal _) (BabTy_Tuple _ _) = None"
| "unify (BabTy_MathReal _) (BabTy_Record _ _) = None"
| "unify (BabTy_MathReal _) (BabTy_Array _ _ _) = None"

| "unify (BabTy_Tuple _ _) (BabTy_Name _ _ _) = None"
| "unify (BabTy_Tuple _ _) (BabTy_Bool _) = None"
| "unify (BabTy_Tuple _ _) (BabTy_FiniteInt _ _ _) = None"
| "unify (BabTy_Tuple _ _) (BabTy_MathInt _) = None"
| "unify (BabTy_Tuple _ _) (BabTy_MathReal _) = None"
| "unify (BabTy_Tuple _ _) (BabTy_Record _ _) = None"
| "unify (BabTy_Tuple _ _) (BabTy_Array _ _ _) = None"

| "unify (BabTy_Record _ _) (BabTy_Name _ _ _) = None"
| "unify (BabTy_Record _ _) (BabTy_Bool _) = None"
| "unify (BabTy_Record _ _) (BabTy_FiniteInt _ _ _) = None"
| "unify (BabTy_Record _ _) (BabTy_MathInt _) = None"
| "unify (BabTy_Record _ _) (BabTy_MathReal _) = None"
| "unify (BabTy_Record _ _) (BabTy_Tuple _ _) = None"
| "unify (BabTy_Record _ _) (BabTy_Array _ _ _) = None"

| "unify (BabTy_Array _ _ _) (BabTy_Name _ _ _) = None"
| "unify (BabTy_Array _ _ _) (BabTy_Bool _) = None"
| "unify (BabTy_Array _ _ _) (BabTy_FiniteInt _ _ _) = None"
| "unify (BabTy_Array _ _ _) (BabTy_MathInt _) = None"
| "unify (BabTy_Array _ _ _) (BabTy_MathReal _) = None"
| "unify (BabTy_Array _ _ _) (BabTy_Tuple _ _) = None"
| "unify (BabTy_Array _ _ _) (BabTy_Record _ _) = None"

  (* Unify a list of type pairs, threading the substitution through *)
| "unify_list [] [] = Some fmempty"
| "unify_list (ty1 # tys1) (ty2 # tys2) =
    (case unify ty1 ty2 of
      None \<Rightarrow> None
    | Some subst1 \<Rightarrow>
        (case unify_list (map (apply_subst subst1) tys1) (map (apply_subst subst1) tys2) of
          None \<Rightarrow> None
        | Some subst2 \<Rightarrow> Some (compose_subst subst2 subst1)))"
| "unify_list [] (_ # _) = None"
| "unify_list (_ # _) [] = None"
  by pat_completeness auto


(* ========================================================================== *)
(* Termination proof                                                          *)
(* ========================================================================== *)

(* Size lemmas *)
lemma list_metavars_cons:
  "list_metavars (ty # tys) = type_metavars ty \<union> list_metavars tys"
  by (simp add: list_metavars_def)

lemma list_type_size_cons:
  "list_type_size (ty # tys) = bab_type_size ty + list_type_size tys"
  by (simp add: list_type_size_def)

lemma type_args_size_smaller:
  "list_type_size args < bab_type_size (BabTy_Name loc name args)"
  by (simp add: list_type_size_def)

lemma tuple_size_smaller:
  "list_type_size tys < bab_type_size (BabTy_Tuple loc tys)"
  by (simp add: list_type_size_def)

lemma record_size_smaller:
  "list_type_size (map snd flds) < bab_type_size (BabTy_Record loc flds)"
proof -
  have "list_type_size (map snd flds) = sum_list (map bab_type_size (map snd flds))"
    by (simp add: list_type_size_def)
  also have "... = sum_list (map (bab_type_size \<circ> snd) flds)"
    by (simp add: comp_def)
  also have "... < 1 + sum_list (map (bab_type_size \<circ> snd) flds)"
    by simp
  also have "... = bab_type_size (BabTy_Record loc flds)"
    by simp
  finally show ?thesis .
qed

lemma array_size_smaller:
  "bab_type_size elem < bab_type_size (BabTy_Array loc elem dims)"
  by simp

lemma type_metavars_tuple_eq:
  "type_metavars (BabTy_Tuple loc tys) = list_metavars tys"
  by (simp add: list_metavars_def)


(* The termination relation: lexicographic on (card of metavars, size, tag)
   where tag is 0 for Inl (unify) and 1 for Inr (unify_list).
   This ensures that unify ty1 ty2 < unify_list [ty1] [ty2] even when sizes are equal. *)
definition unify_rel :: "((BabType \<times> BabType) + (BabType list \<times> BabType list)) rel" where
  "unify_rel = inv_image (less_than <*lex*> less_than <*lex*> less_than)
    (\<lambda>x. case x of
      Inl (ty1, ty2) \<Rightarrow> (card (type_metavars ty1 \<union> type_metavars ty2),
                         bab_type_size ty1 + bab_type_size ty2,
                         0::nat)
    | Inr (tys1, tys2) \<Rightarrow> (card (list_metavars tys1 \<union> list_metavars tys2),
                           list_type_size tys1 + list_type_size tys2,
                           1::nat))"

lemma wf_unify_rel: "wf unify_rel"
  unfolding unify_rel_def by auto


(* Lemmas about when recursive calls are in unify_rel *)

(* Calling unify_list args1 args2 from unify (Name n1 args1) (Name n2 args2) is smaller *)
lemma unify_rel_name_to_list:
  "(Inr (args1, args2), Inl (BabTy_Name loc1 n1 args1, BabTy_Name loc2 n2 args2)) \<in> unify_rel"
proof -
  have "list_type_size args1 + list_type_size args2 <
        bab_type_size (BabTy_Name loc1 n1 args1) + bab_type_size (BabTy_Name loc2 n2 args2)"
    by (meson add_less_mono type_args_size_smaller)
  moreover have "list_metavars args1 \<union> list_metavars args2 =
                 type_metavars (BabTy_Name loc1 n1 args1) \<union> type_metavars (BabTy_Name loc2 n2 args2)"
    by (auto simp: list_metavars_def)
  ultimately show ?thesis
    unfolding unify_rel_def by auto
qed

(* Calling unify_list tys1 tys2 from unify (Tuple tys1) (Tuple tys2) is smaller *)
lemma unify_rel_tuple_to_list:
  "(Inr (tys1, tys2), Inl (BabTy_Tuple loc1 tys1, BabTy_Tuple loc2 tys2)) \<in> unify_rel"
proof -
  have "list_type_size tys1 + list_type_size tys2 <
        bab_type_size (BabTy_Tuple loc1 tys1) + bab_type_size (BabTy_Tuple loc2 tys2)"
    by (meson add_less_mono tuple_size_smaller)
  moreover have "list_metavars tys1 \<union> list_metavars tys2 =
                 type_metavars (BabTy_Tuple loc1 tys1) \<union> type_metavars (BabTy_Tuple loc2 tys2)"
    by (auto simp: list_metavars_def)
  ultimately show ?thesis
    unfolding unify_rel_def by auto
qed

(* Calling unify_list (map snd flds1) (map snd flds2) from unify (Record flds1) (Record flds2) is smaller *)
lemma unify_rel_record_to_list:
  "(Inr (map snd flds1, map snd flds2), Inl (BabTy_Record loc1 flds1, BabTy_Record loc2 flds2)) \<in> unify_rel"
proof -
  have "list_type_size (map snd flds1) + list_type_size (map snd flds2) <
        bab_type_size (BabTy_Record loc1 flds1) + bab_type_size (BabTy_Record loc2 flds2)"
    by (auto simp: list_type_size_def)
  moreover have "list_metavars (map snd flds1) \<union> list_metavars (map snd flds2) =
                 type_metavars (BabTy_Record loc1 flds1) \<union> type_metavars (BabTy_Record loc2 flds2)"
    by (auto simp: list_metavars_def)
  ultimately show ?thesis
    unfolding unify_rel_def by auto
qed

(* Calling unify elem1 elem2 from unify (Array elem1 dims1) (Array elem2 dims2) is smaller *)
lemma unify_rel_array_to_elem:
  "(Inl (elem1, elem2), Inl (BabTy_Array loc1 elem1 dims1, BabTy_Array loc2 elem2 dims2)) \<in> unify_rel"
proof -
  have "bab_type_size elem1 + bab_type_size elem2 <
        bab_type_size (BabTy_Array loc1 elem1 dims1) + bab_type_size (BabTy_Array loc2 elem2 dims2)"
    by auto
  moreover have "type_metavars elem1 \<union> type_metavars elem2 =
                 type_metavars (BabTy_Array loc1 elem1 dims1) \<union> type_metavars (BabTy_Array loc2 elem2 dims2)"
    by auto
  ultimately show ?thesis
    unfolding unify_rel_def by auto
qed

(* Calling unify head1 head2 from unify_list (head1 # rest1) (head2 # rest2) is smaller *)
lemma unify_rel_list_to_head:
  "(Inl (head1, head2), Inr (head1 # rest1, head2 # rest2)) \<in> unify_rel"
proof -
  have mv_subset: "type_metavars head1 \<union> type_metavars head2 \<subseteq>
        list_metavars (head1 # rest1) \<union> list_metavars (head2 # rest2)"
    by (auto simp: list_metavars_def)
  hence mv_card: "card (type_metavars head1 \<union> type_metavars head2) \<le>
            card (list_metavars (head1 # rest1) \<union> list_metavars (head2 # rest2))"
    by (simp add: card_mono finite_list_metavars)
  have size_le: "bab_type_size head1 + bab_type_size head2 \<le>
                 list_type_size (head1 # rest1) + list_type_size (head2 # rest2)"
    by (simp add: list_type_size_def)
  show ?thesis
    unfolding unify_rel_def
    using mv_card size_le by auto
qed


(* Properties that a substitution from unify/unify_list must satisfy:
   - Domain is contained in the input metavars
   - For each binding n -> ty: ty's metavars are in input metavars
   - Domain and range metavars are disjoint (idempotent substitution)

   These properties ensure that applying the substitution decreases the metavar count. *)

definition subst_props :: "nat set \<Rightarrow> MetaSubst \<Rightarrow> bool" where
  "subst_props mvs subst \<equiv>
    fset (fmdom subst) \<subseteq> mvs \<and>
    (\<forall>n ty. fmlookup subst n = Some ty \<longrightarrow> type_metavars ty \<subseteq> mvs) \<and>
    fset (fmdom subst) \<inter> subst_range_mvs subst = {}"

definition unify_input_mvs :: "BabType \<Rightarrow> BabType \<Rightarrow> nat set" where
  "unify_input_mvs ty1 ty2 = type_metavars ty1 \<union> type_metavars ty2"

definition unify_list_input_mvs :: "BabType list \<Rightarrow> BabType list \<Rightarrow> nat set" where
  "unify_list_input_mvs tys1 tys2 = list_metavars tys1 \<union> list_metavars tys2"

(* Empty substitution trivially satisfies the properties *)
lemma subst_props_empty [simp]: "subst_props mvs fmempty"
  by (simp add: subst_props_def)

(* Singleton substitution satisfies properties when constructed correctly *)
lemma subst_props_singleton:
  assumes "n \<in> mvs"
      and "type_metavars ty \<subseteq> mvs"
      and "\<not> occurs n ty"
  shows "subst_props mvs (singleton_subst n ty)"
  using assms
  by (auto simp: subst_props_def singleton_subst_def subst_range_mvs_def occurs_def fmran'_def)

(* If subst satisfies props for mvs, applying it to types with metavars in mvs
   results in types whose metavars are still in mvs *)
lemma apply_subst_metavars_subset:
  assumes "subst_props mvs subst"
      and "type_metavars ty \<subseteq> mvs"
  shows "type_metavars (apply_subst subst ty) \<subseteq> mvs"
proof -
  (* From subst_props: dom \<subseteq> mvs and range metavars \<subseteq> mvs *)
  from assms(1) have dom_sub: "fset (fmdom subst) \<subseteq> mvs"
    by (simp add: subst_props_def)
  from assms(1) have range_sub: "subst_range_mvs subst \<subseteq> mvs"
    by (auto simp: subst_props_def subst_range_mvs_def fmran'_def)

  (* Result metavars are subset of (ty metavars - dom) \<union> range *)
  have "type_metavars (apply_subst subst ty) \<subseteq>
        (type_metavars ty - fset (fmdom subst)) \<union> subst_range_mvs subst"
    by (rule apply_subst_metavars_result)

  (* Both parts are subsets of mvs *)
  also have "... \<subseteq> mvs"
    using assms(2) range_sub by auto

  finally show ?thesis .
qed

(* Composition preserves properties when domains are disjoint and
   range of subst2 doesn't mention domain of subst1 *)
lemma subst_props_compose:
  assumes props1: "subst_props mvs subst1"
      and props2: "subst_props mvs subst2"
      and dom_disj: "fset (fmdom subst2) \<inter> fset (fmdom subst1) = {}"
      and range2_disj: "subst_range_mvs subst2 \<inter> fset (fmdom subst1) = {}"
  shows "subst_props mvs (compose_subst subst2 subst1)"
  unfolding subst_props_def
proof (intro conjI)
  (* Domain of composition is union of domains, both subsets of mvs *)
  show "fset (fmdom (compose_subst subst2 subst1)) \<subseteq> mvs"
  proof -
    have "fmdom (compose_subst subst2 subst1) = fmdom subst2 |\<union>| fmdom subst1"
      by (simp add: compose_subst_def)
    moreover have "fset (fmdom subst1) \<subseteq> mvs" and "fset (fmdom subst2) \<subseteq> mvs"
      using props1 props2 by (auto simp: subst_props_def)
    ultimately show ?thesis by auto
  qed
next
  (* For each binding in the composition, range metavars are in mvs *)
  show "\<forall>n ty. fmlookup (compose_subst subst2 subst1) n = Some ty \<longrightarrow>
               type_metavars ty \<subseteq> mvs"
  proof (intro allI impI)
    fix n ty
    assume lookup: "fmlookup (compose_subst subst2 subst1) n = Some ty"

    show "type_metavars ty \<subseteq> mvs"
    proof (cases "fmlookup subst1 n")
      case None
      hence "fmlookup subst2 n = Some ty"
        using lookup by (simp add: fmlookup_compose_subst_None1)
      thus ?thesis
        using props2 by (auto simp: subst_props_def)
    next
      case (Some ty1)
      hence ty_eq: "ty = apply_subst subst2 ty1"
        using lookup by (simp add: fmlookup_compose_subst_Some1)
      from Some props1 have ty1_mvs: "type_metavars ty1 \<subseteq> mvs"
        by (auto simp: subst_props_def)
      show ?thesis
        using ty_eq ty1_mvs props2 by (simp add: apply_subst_metavars_subset)
    qed
  qed
next
  (* Domain and range of composition are disjoint *)
  show "fset (fmdom (compose_subst subst2 subst1)) \<inter> subst_range_mvs (compose_subst subst2 subst1) = {}"
  proof -
    have dom_eq: "fmdom (compose_subst subst2 subst1) = fmdom subst2 |\<union>| fmdom subst1"
      by (simp add: compose_subst_def)
    (* Range of compose_subst subst2 subst1:
       For n in dom(subst1): apply_subst subst2 (subst1 n)
       For n in dom(subst2) \ dom(subst1): subst2 n *)
    have range_sub: "subst_range_mvs (compose_subst subst2 subst1) \<subseteq>
                     subst_range_mvs subst2 \<union> subst_range_mvs subst1"
    proof
      fix x assume "x \<in> subst_range_mvs (compose_subst subst2 subst1)"
      then obtain ty where ty_in: "ty \<in> fmran' (compose_subst subst2 subst1)"
                       and x_in: "x \<in> type_metavars ty"
        by (auto simp: subst_range_mvs_def)
      from ty_in obtain n where lookup: "fmlookup (compose_subst subst2 subst1) n = Some ty"
        by (auto simp: fmran'_def)
      show "x \<in> subst_range_mvs subst2 \<union> subst_range_mvs subst1"
      proof (cases "fmlookup subst1 n")
        case None
        hence "fmlookup subst2 n = Some ty"
          using lookup by (simp add: fmlookup_compose_subst_None1)
        hence "ty \<in> fmran' subst2" by (auto simp: fmran'_def)
        thus ?thesis using x_in by (auto simp: subst_range_mvs_def)
      next
        case (Some ty1)
        hence ty_eq: "ty = apply_subst subst2 ty1"
          using lookup by (simp add: fmlookup_compose_subst_Some1)
        have ty1_in: "ty1 \<in> fmran' subst1" using Some by (auto simp: fmran'_def)
        from x_in[unfolded ty_eq] have "x \<in> type_metavars (apply_subst subst2 ty1)" .
        hence "x \<in> (type_metavars ty1 - fset (fmdom subst2)) \<union> subst_range_mvs subst2"
          using apply_subst_metavars_result by auto
        thus ?thesis
        proof
          assume "x \<in> type_metavars ty1 - fset (fmdom subst2)"
          hence "x \<in> type_metavars ty1" by auto
          thus ?thesis using ty1_in by (auto simp: subst_range_mvs_def)
        next
          assume "x \<in> subst_range_mvs subst2"
          thus ?thesis by auto
        qed
      qed
    qed
    (* Show disjointness directly *)
    have no_overlap: "\<And>n. n \<in> fset (fmdom (compose_subst subst2 subst1)) \<Longrightarrow>
                          n \<notin> subst_range_mvs (compose_subst subst2 subst1)"
    proof -
      fix n
      assume n_in_dom: "n \<in> fset (fmdom (compose_subst subst2 subst1))"
      from n_in_dom have n_cases: "n \<in> fset (fmdom subst1) \<or> n \<in> fset (fmdom subst2)"
        using dom_eq by auto
      show "n \<notin> subst_range_mvs (compose_subst subst2 subst1)"
      proof (cases "n \<in> fset (fmdom subst1)")
        case True
        (* n is in dom(subst1), so n \<notin> range(subst1) and n \<notin> range(subst2) by range2_disj *)
        have n_not_in_range1: "n \<notin> subst_range_mvs subst1"
          using props1 True by (auto simp: subst_props_def)
        have n_not_in_range2: "n \<notin> subst_range_mvs subst2"
          using range2_disj True by auto
        from range_sub n_not_in_range1 n_not_in_range2
        show ?thesis by auto
      next
        case False
        (* n \<in> dom(subst2) but n \<notin> dom(subst1) *)
        with n_cases have n_in_dom2: "n \<in> fset (fmdom subst2)" by auto
        have n_not_in_range2: "n \<notin> subst_range_mvs subst2"
          using props2 n_in_dom2 by (auto simp: subst_props_def)
        (* Show n is not in range of composition *)
        show ?thesis
        proof
          assume n_in_range: "n \<in> subst_range_mvs (compose_subst subst2 subst1)"
          from n_in_range obtain ty where ty_in: "ty \<in> fmran' (compose_subst subst2 subst1)"
                                      and n_in_ty: "n \<in> type_metavars ty"
            by (auto simp: subst_range_mvs_def)
          from ty_in obtain m where lookup: "fmlookup (compose_subst subst2 subst1) m = Some ty"
            by (auto simp: fmran'_def)
          show False
          proof (cases "fmlookup subst1 m")
            case None
            hence "fmlookup subst2 m = Some ty"
              using lookup by (simp add: fmlookup_compose_subst_None1)
            hence "ty \<in> fmran' subst2" by (auto simp: fmran'_def)
            hence "n \<in> subst_range_mvs subst2" using n_in_ty by (auto simp: subst_range_mvs_def)
            thus False using n_not_in_range2 by simp
          next
            case (Some ty1)
            hence ty_eq: "ty = apply_subst subst2 ty1"
              using lookup by (simp add: fmlookup_compose_subst_Some1)
            from n_in_ty[unfolded ty_eq]
            have "n \<in> (type_metavars ty1 - fset (fmdom subst2)) \<union> subst_range_mvs subst2"
              using apply_subst_metavars_result by auto
            thus False
            proof
              assume "n \<in> type_metavars ty1 - fset (fmdom subst2)"
              thus False using n_in_dom2 by auto
            next
              assume "n \<in> subst_range_mvs subst2"
              thus False using n_not_in_range2 by simp
            qed
          qed
        qed
      qed
    qed
    show ?thesis using no_overlap by auto
  qed
qed

(* The recursive unify_list call after unifying heads is smaller *)
lemma unify_rel_list_recursive:
  assumes "subst_props (type_metavars ty1 \<union> type_metavars ty2) subst"
  shows "(Inr (map (apply_subst subst) rest1, map (apply_subst subst) rest2),
          Inr (ty1 # rest1, ty2 # rest2)) \<in> unify_rel"
proof (cases "subst = fmempty")
  case True
  (* Empty subst: size decreases since we removed heads *)
  have "list_type_size (map (apply_subst subst) rest1) + list_type_size (map (apply_subst subst) rest2)
        < list_type_size (ty1 # rest1) + list_type_size (ty2 # rest2)"
    using True by (simp add: list_type_size_def bab_type_size_pos)
  moreover have "list_metavars (map (apply_subst subst) rest1) \<union> list_metavars (map (apply_subst subst) rest2)
                 \<subseteq> list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
    using True by (auto simp: list_metavars_def)
  hence "card (list_metavars (map (apply_subst subst) rest1) \<union> list_metavars (map (apply_subst subst) rest2))
         \<le> card (list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2))"
    by (simp add: card_mono finite_list_metavars)
  ultimately show ?thesis
    unfolding unify_rel_def by auto
next
  case False
  (* Non-empty subst: metavar count decreases *)
  from False obtain n ty where binding: "fmlookup subst n = Some ty"
    by (metis fmap_ext fmempty_lookup option.exhaust)
  have n_in_heads: "n \<in> type_metavars ty1 \<union> type_metavars ty2"
    using assms binding unfolding subst_props_def
    by (meson fmdomI in_mono)
  have ty_mvs: "type_metavars ty \<subseteq> type_metavars ty1 \<union> type_metavars ty2"
    using assms binding unfolding subst_props_def by auto
  (* n is eliminated from results - domain and range are disjoint *)
  have n_in_dom: "n \<in> fset (fmdom subst)"
    using binding by (simp add: fmlookup_dom_iff)
  have n_not_in_range: "n \<notin> subst_range_mvs subst"
    using assms n_in_dom unfolding subst_props_def by auto
  have n_not_in_result: "n \<notin> list_metavars (map (apply_subst subst) rest1) \<union>
                              list_metavars (map (apply_subst subst) rest2)"
    using apply_subst_eliminates_dom[OF n_in_dom n_not_in_range]
    by (auto simp: list_metavars_def)
  (* Result metavars are subset of original *)
  have result_subset: "list_metavars (map (apply_subst subst) rest1) \<union>
                       list_metavars (map (apply_subst subst) rest2)
                       \<subseteq> list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
  proof -
    have dom_sub: "fset (fmdom subst) \<subseteq> type_metavars ty1 \<union> type_metavars ty2"
      using assms unfolding subst_props_def by auto
    have range_sub: "subst_range_mvs subst \<subseteq> type_metavars ty1 \<union> type_metavars ty2"
      using assms unfolding subst_props_def subst_range_mvs_def
      by fastforce
    have "\<And>t. t \<in> set rest1 \<Longrightarrow> type_metavars (apply_subst subst t) \<subseteq>
              list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
    proof -
      fix t assume "t \<in> set rest1"
      have "type_metavars (apply_subst subst t) \<subseteq>
            (type_metavars t - fset (fmdom subst)) \<union> subst_range_mvs subst"
        by (rule apply_subst_metavars_result)
      also have "... \<subseteq> type_metavars t \<union> subst_range_mvs subst" by auto
      also have "... \<subseteq> list_metavars rest1 \<union> (type_metavars ty1 \<union> type_metavars ty2)"
        using \<open>t \<in> set rest1\<close> range_sub by (auto simp: list_metavars_def)
      also have "... \<subseteq> list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
        by (auto simp: list_metavars_def)
      finally show "type_metavars (apply_subst subst t) \<subseteq>
                    list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)" .
    qed
    moreover have "\<And>t. t \<in> set rest2 \<Longrightarrow> type_metavars (apply_subst subst t) \<subseteq>
              list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
    proof -
      fix t assume "t \<in> set rest2"
      have "type_metavars (apply_subst subst t) \<subseteq>
            (type_metavars t - fset (fmdom subst)) \<union> subst_range_mvs subst"
        by (rule apply_subst_metavars_result)
      also have "... \<subseteq> type_metavars t \<union> subst_range_mvs subst" by auto
      also have "... \<subseteq> list_metavars rest2 \<union> (type_metavars ty1 \<union> type_metavars ty2)"
        using \<open>t \<in> set rest2\<close> range_sub by (auto simp: list_metavars_def)
      also have "... \<subseteq> list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
        by (auto simp: list_metavars_def)
      finally show "type_metavars (apply_subst subst t) \<subseteq>
                    list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)" .
    qed
    ultimately show ?thesis by (auto simp: list_metavars_def)
  qed
  have n_in_orig: "n \<in> list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
    using n_in_heads by (auto simp: list_metavars_def)
  have strict_subset: "list_metavars (map (apply_subst subst) rest1) \<union>
                       list_metavars (map (apply_subst subst) rest2)
                       \<subset> list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
    using result_subset n_not_in_result n_in_orig by auto
  hence "card (list_metavars (map (apply_subst subst) rest1) \<union>
               list_metavars (map (apply_subst subst) rest2))
         < card (list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2))"
    using finite_list_metavars psubset_card_mono
    by (metis finite_Un) 
  thus ?thesis
    unfolding unify_rel_def by auto
qed

(* The main inductive property we need to prove:
   For any input in unify_rel, both:
   1. The domain predicate holds (termination)
   2. If the result is Some subst, then subst_props holds *)

definition unify_terminates_with_props ::
    "((BabType \<times> BabType) + (BabType list \<times> BabType list)) \<Rightarrow> bool" where
  "unify_terminates_with_props x \<equiv>
    unify_unify_list_dom x \<and>
    (case x of
      Inl (ty1, ty2) \<Rightarrow>
        (\<forall>subst. unify ty1 ty2 = Some subst \<longrightarrow>
                 subst_props (unify_input_mvs ty1 ty2) subst)
    | Inr (tys1, tys2) \<Rightarrow>
        (\<forall>subst. unify_list tys1 tys2 = Some subst \<longrightarrow>
                 subst_props (unify_list_input_mvs tys1 tys2) subst))"

(* The main theorem: all inputs satisfy unify_terminates_with_props *)
lemma unify_terminates_with_props_all:
  "unify_terminates_with_props x"
proof (induction x rule: wf_induct_rule[OF wf_unify_rel])
  case (1 x)
  (* IH: for all y with (y, x) \<in> unify_rel, unify_terminates_with_props y *)
  show ?case
  proof (cases x)
    case (Inl pair)
    obtain ty1 ty2 where pair_eq: "pair = (ty1, ty2)" by (cases pair)

    (* Need to show domain holds and props hold for unify ty1 ty2 *)
    show ?thesis
    proof (cases ty1)
      case (BabTy_Meta n)
      (* When ty1 is a metavar, unify returns singleton or fmempty *)
      show ?thesis
        using Inl pair_eq BabTy_Meta
      proof (cases ty2)
        case (BabTy_Meta m)
        (* unify (Meta n) (Meta m) = if n=m then fmempty else singleton n (Meta m) *)
        have dom: "unify_unify_list_dom (Inl (BabTy_Meta n, BabTy_Meta m))"
          by (rule unify_unify_list.domintros)
        show ?thesis
        proof (cases "n = m")
          case True
          have result: "unify (BabTy_Meta n) (BabTy_Meta m) = Some fmempty"
            using dom True by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Meta n\<close> BabTy_Meta dom result True
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have result: "unify (BabTy_Meta n) (BabTy_Meta m) = Some (singleton_subst n (BabTy_Meta m))"
            using dom False by (simp add: unify.psimps)
          have props: "subst_props (unify_input_mvs (BabTy_Meta n) (BabTy_Meta m)) (singleton_subst n (BabTy_Meta m))"
            using False by (auto simp: unify_input_mvs_def intro: subst_props_singleton simp: occurs_def)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Meta n\<close> BabTy_Meta dom result props
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case (BabTy_Name loc2 name2 args2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Meta n, BabTy_Name loc2 name2 args2))"
          by (rule unify_unify_list.domintros)
        show ?thesis
        proof (cases "occurs n (BabTy_Name loc2 name2 args2)")
          case True
          have result: "unify (BabTy_Meta n) (BabTy_Name loc2 name2 args2) = None"
            using dom True by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Meta n\<close> BabTy_Name dom result
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have result: "unify (BabTy_Meta n) (BabTy_Name loc2 name2 args2) = Some (singleton_subst n (BabTy_Name loc2 name2 args2))"
            using dom False by (simp add: unify.psimps)
          have props: "subst_props (unify_input_mvs (BabTy_Meta n) (BabTy_Name loc2 name2 args2)) (singleton_subst n (BabTy_Name loc2 name2 args2))"
            using False by (auto simp: unify_input_mvs_def intro: subst_props_singleton)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Meta n\<close> BabTy_Name dom result props
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case (BabTy_Bool loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Meta n, BabTy_Bool loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Meta n) (BabTy_Bool loc2) = Some (singleton_subst n (BabTy_Bool loc2))"
          using dom by (simp add: unify.psimps)
        have props: "subst_props (unify_input_mvs (BabTy_Meta n) (BabTy_Bool loc2)) (singleton_subst n (BabTy_Bool loc2))"
          by (auto simp: unify_input_mvs_def intro: subst_props_singleton simp: occurs_def)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Meta n\<close> BabTy_Bool dom result props
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_FiniteInt loc2 sign2 bits2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Meta n, BabTy_FiniteInt loc2 sign2 bits2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Meta n) (BabTy_FiniteInt loc2 sign2 bits2) = Some (singleton_subst n (BabTy_FiniteInt loc2 sign2 bits2))"
          using dom by (simp add: unify.psimps)
        have props: "subst_props (unify_input_mvs (BabTy_Meta n) (BabTy_FiniteInt loc2 sign2 bits2)) (singleton_subst n (BabTy_FiniteInt loc2 sign2 bits2))"
          by (auto simp: unify_input_mvs_def intro: subst_props_singleton simp: occurs_def)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Meta n\<close> BabTy_FiniteInt dom result props
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_MathInt loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Meta n, BabTy_MathInt loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Meta n) (BabTy_MathInt loc2) = Some (singleton_subst n (BabTy_MathInt loc2))"
          using dom by (simp add: unify.psimps)
        have props: "subst_props (unify_input_mvs (BabTy_Meta n) (BabTy_MathInt loc2)) (singleton_subst n (BabTy_MathInt loc2))"
          by (auto simp: unify_input_mvs_def intro: subst_props_singleton simp: occurs_def)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Meta n\<close> BabTy_MathInt dom result props
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_MathReal loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Meta n, BabTy_MathReal loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Meta n) (BabTy_MathReal loc2) = Some (singleton_subst n (BabTy_MathReal loc2))"
          using dom by (simp add: unify.psimps)
        have props: "subst_props (unify_input_mvs (BabTy_Meta n) (BabTy_MathReal loc2)) (singleton_subst n (BabTy_MathReal loc2))"
          by (auto simp: unify_input_mvs_def intro: subst_props_singleton simp: occurs_def)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Meta n\<close> BabTy_MathReal dom result props
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Tuple loc2 tys2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Meta n, BabTy_Tuple loc2 tys2))"
          by (rule unify_unify_list.domintros)
        show ?thesis
        proof (cases "occurs n (BabTy_Tuple loc2 tys2)")
          case True
          have result: "unify (BabTy_Meta n) (BabTy_Tuple loc2 tys2) = None"
            using dom True by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Meta n\<close> BabTy_Tuple dom result
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have result: "unify (BabTy_Meta n) (BabTy_Tuple loc2 tys2) = Some (singleton_subst n (BabTy_Tuple loc2 tys2))"
            using dom False by (simp add: unify.psimps)
          have props: "subst_props (unify_input_mvs (BabTy_Meta n) (BabTy_Tuple loc2 tys2)) (singleton_subst n (BabTy_Tuple loc2 tys2))"
            using False by (auto simp: unify_input_mvs_def intro: subst_props_singleton)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Meta n\<close> BabTy_Tuple dom result props
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case (BabTy_Record loc2 flds2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Meta n, BabTy_Record loc2 flds2))"
          by (rule unify_unify_list.domintros)
        show ?thesis
        proof (cases "occurs n (BabTy_Record loc2 flds2)")
          case True
          have result: "unify (BabTy_Meta n) (BabTy_Record loc2 flds2) = None"
            using dom True by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Meta n\<close> BabTy_Record dom result
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have result: "unify (BabTy_Meta n) (BabTy_Record loc2 flds2) = Some (singleton_subst n (BabTy_Record loc2 flds2))"
            using dom False by (simp add: unify.psimps)
          have props: "subst_props (unify_input_mvs (BabTy_Meta n) (BabTy_Record loc2 flds2)) (singleton_subst n (BabTy_Record loc2 flds2))"
            using False by (auto simp: unify_input_mvs_def intro: subst_props_singleton)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Meta n\<close> BabTy_Record dom result props
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case (BabTy_Array loc2 elem2 dims2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Meta n, BabTy_Array loc2 elem2 dims2))"
          by (rule unify_unify_list.domintros)
        show ?thesis
        proof (cases "occurs n (BabTy_Array loc2 elem2 dims2)")
          case True
          have result: "unify (BabTy_Meta n) (BabTy_Array loc2 elem2 dims2) = None"
            using dom True by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Meta n\<close> BabTy_Array dom result
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have result: "unify (BabTy_Meta n) (BabTy_Array loc2 elem2 dims2) = Some (singleton_subst n (BabTy_Array loc2 elem2 dims2))"
            using dom False by (simp add: unify.psimps)
          have props: "subst_props (unify_input_mvs (BabTy_Meta n) (BabTy_Array loc2 elem2 dims2)) (singleton_subst n (BabTy_Array loc2 elem2 dims2))"
            using False by (auto simp: unify_input_mvs_def intro: subst_props_singleton)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Meta n\<close> BabTy_Array dom result props
            by (auto simp: unify_terminates_with_props_def)
        qed
      qed
    next
      case BabTy_Name1: (BabTy_Name loc1 name1 args1)
      show ?thesis
        using Inl pair_eq BabTy_Name1
      proof (cases ty2)
        case (BabTy_Meta m)
        have dom: "unify_unify_list_dom (Inl (BabTy_Name loc1 name1 args1, BabTy_Meta m))"
          by (rule unify_unify_list.domintros)
        show ?thesis
        proof (cases "occurs m (BabTy_Name loc1 name1 args1)")
          case True
          have result: "unify (BabTy_Name loc1 name1 args1) (BabTy_Meta m) = None"
            using dom True by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Name loc1 name1 args1\<close> BabTy_Meta dom result
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have result: "unify (BabTy_Name loc1 name1 args1) (BabTy_Meta m) = Some (singleton_subst m (BabTy_Name loc1 name1 args1))"
            using dom False by (simp add: unify.psimps)
          have props: "subst_props (unify_input_mvs (BabTy_Name loc1 name1 args1) (BabTy_Meta m)) (singleton_subst m (BabTy_Name loc1 name1 args1))"
            using False by (auto simp: unify_input_mvs_def intro: subst_props_singleton)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Name loc1 name1 args1\<close> BabTy_Meta dom result props
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case BabTy_Name2: (BabTy_Name loc2 name2 args2)
        (* This is the recursive case - need IH *)
        have in_rel: "(Inr (args1, args2), Inl (BabTy_Name loc1 name1 args1, BabTy_Name loc2 name2 args2)) \<in> unify_rel"
          by (rule unify_rel_name_to_list)
        have IH: "unify_terminates_with_props (Inr (args1, args2))"
          using "1.IH" in_rel Inl pair_eq BabTy_Name1 BabTy_Name2 by auto
        show ?thesis
        proof (cases "name1 = name2 \<and> length args1 = length args2")
          case True
          (* unify calls unify_list *)
          have list_dom: "unify_unify_list_dom (Inr (args1, args2))"
            using IH unfolding unify_terminates_with_props_def by simp
          have dom: "unify_unify_list_dom (Inl (BabTy_Name loc1 name1 args1, BabTy_Name loc2 name2 args2))"
            using list_dom True by (auto intro: unify_unify_list.domintros)
          have result: "unify (BabTy_Name loc1 name1 args1) (BabTy_Name loc2 name2 args2) = unify_list args1 args2"
            using dom True by (simp add: unify.psimps)
          (* Props transfer from unify_list *)
          have list_props: "\<And>subst. unify_list args1 args2 = Some subst \<Longrightarrow>
                           subst_props (unify_list_input_mvs args1 args2) subst"
            using IH unfolding unify_terminates_with_props_def by simp
          have mvs_eq: "unify_list_input_mvs args1 args2 = unify_input_mvs (BabTy_Name loc1 name1 args1) (BabTy_Name loc2 name2 args2)"
            by (auto simp: unify_list_input_mvs_def unify_input_mvs_def list_metavars_def)
          have props: "\<And>subst. unify (BabTy_Name loc1 name1 args1) (BabTy_Name loc2 name2 args2) = Some subst \<Longrightarrow>
                       subst_props (unify_input_mvs (BabTy_Name loc1 name1 args1) (BabTy_Name loc2 name2 args2)) subst"
            using list_props result mvs_eq by simp
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Name loc1 name1 args1\<close> BabTy_Name2 dom props
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have dom: "unify_unify_list_dom (Inl (BabTy_Name loc1 name1 args1, BabTy_Name loc2 name2 args2))"
            using False unify_unify_list.domintros(22) by presburger
          have result: "unify (BabTy_Name loc1 name1 args1) (BabTy_Name loc2 name2 args2) = None"
            using dom False unify.psimps(22) by auto 
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Name loc1 name1 args1\<close> BabTy_Name2 dom result
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case (BabTy_Bool loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Name loc1 name1 args1, BabTy_Bool loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Name loc1 name1 args1) (BabTy_Bool loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Name loc1 name1 args1\<close> BabTy_Bool dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_FiniteInt loc2 sign2 bits2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Name loc1 name1 args1, BabTy_FiniteInt loc2 sign2 bits2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Name loc1 name1 args1) (BabTy_FiniteInt loc2 sign2 bits2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Name loc1 name1 args1\<close> BabTy_FiniteInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_MathInt loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Name loc1 name1 args1, BabTy_MathInt loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Name loc1 name1 args1) (BabTy_MathInt loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Name loc1 name1 args1\<close> BabTy_MathInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_MathReal loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Name loc1 name1 args1, BabTy_MathReal loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Name loc1 name1 args1) (BabTy_MathReal loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Name loc1 name1 args1\<close> BabTy_MathReal dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Tuple loc2 tys2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Name loc1 name1 args1, BabTy_Tuple loc2 tys2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Name loc1 name1 args1) (BabTy_Tuple loc2 tys2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Name loc1 name1 args1\<close> BabTy_Tuple dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Record loc2 flds2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Name loc1 name1 args1, BabTy_Record loc2 flds2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Name loc1 name1 args1) (BabTy_Record loc2 flds2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Name loc1 name1 args1\<close> BabTy_Record dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Array loc2 elem2 dims2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Name loc1 name1 args1, BabTy_Array loc2 elem2 dims2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Name loc1 name1 args1) (BabTy_Array loc2 elem2 dims2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Name loc1 name1 args1\<close> BabTy_Array dom result
          by (auto simp: unify_terminates_with_props_def)
      qed
    next
      case (BabTy_Bool loc)
      (* When ty1 is Bool, we need to case on ty2 *)
      show ?thesis
        using Inl pair_eq BabTy_Bool
      proof (cases ty2)
        case (BabTy_Meta m)
        (* unify Bool (Meta m) = singleton_subst m Bool *)
        have dom: "unify_unify_list_dom (Inl (BabTy_Bool loc, BabTy_Meta m))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Bool loc) (BabTy_Meta m) = Some (singleton_subst m (BabTy_Bool loc))"
          using dom by (simp add: unify.psimps)
        have props: "subst_props (unify_input_mvs (BabTy_Bool loc) (BabTy_Meta m)) (singleton_subst m (BabTy_Bool loc))"
          by (auto simp: unify_input_mvs_def intro: subst_props_singleton simp: occurs_def)
        show ?thesis
          using Inl pair_eq BabTy_Bool BabTy_Meta dom result props
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Bool loc2)
        (* unify Bool Bool = fmempty *)
        have dom: "unify_unify_list_dom (Inl (BabTy_Bool loc, BabTy_Bool loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Bool loc) (BabTy_Bool loc2) = Some fmempty"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Bool loc\<close> BabTy_Bool dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Name loc2 name2 args2)
        (* unify Bool (Name ...) = None *)
        have dom: "unify_unify_list_dom (Inl (BabTy_Bool loc, BabTy_Name loc2 name2 args2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Bool loc) (BabTy_Name loc2 name2 args2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Bool loc\<close> BabTy_Name dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_FiniteInt loc2 sign2 bits2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Bool loc, BabTy_FiniteInt loc2 sign2 bits2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Bool loc) (BabTy_FiniteInt loc2 sign2 bits2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Bool loc\<close> BabTy_FiniteInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_MathInt loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Bool loc, BabTy_MathInt loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Bool loc) (BabTy_MathInt loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Bool loc\<close> BabTy_MathInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_MathReal loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Bool loc, BabTy_MathReal loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Bool loc) (BabTy_MathReal loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Bool loc\<close> BabTy_MathReal dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Tuple loc2 tys2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Bool loc, BabTy_Tuple loc2 tys2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Bool loc) (BabTy_Tuple loc2 tys2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Bool loc\<close> BabTy_Tuple dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Record loc2 flds2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Bool loc, BabTy_Record loc2 flds2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Bool loc) (BabTy_Record loc2 flds2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Bool loc\<close> BabTy_Record dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Array loc2 elem2 dims2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Bool loc, BabTy_Array loc2 elem2 dims2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Bool loc) (BabTy_Array loc2 elem2 dims2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Bool loc\<close> BabTy_Array dom result
          by (auto simp: unify_terminates_with_props_def)
      qed
    next
      case (BabTy_FiniteInt loc sign bits)
      (* Similar pattern to BabTy_Bool *)
      show ?thesis
        using Inl pair_eq BabTy_FiniteInt
      proof (cases ty2)
        case (BabTy_Meta m)
        have dom: "unify_unify_list_dom (Inl (BabTy_FiniteInt loc sign bits, BabTy_Meta m))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_FiniteInt loc sign bits) (BabTy_Meta m) = Some (singleton_subst m (BabTy_FiniteInt loc sign bits))"
          using dom by (simp add: unify.psimps)
        have props: "subst_props (unify_input_mvs (BabTy_FiniteInt loc sign bits) (BabTy_Meta m)) (singleton_subst m (BabTy_FiniteInt loc sign bits))"
          by (auto simp: unify_input_mvs_def intro: subst_props_singleton simp: occurs_def)
        show ?thesis
          using Inl pair_eq BabTy_FiniteInt BabTy_Meta dom result props
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_FiniteInt loc2 sign2 bits2)
        have dom: "unify_unify_list_dom (Inl (BabTy_FiniteInt loc sign bits, BabTy_FiniteInt loc2 sign2 bits2))"
          by (rule unify_unify_list.domintros)
        show ?thesis
        proof (cases "sign = sign2 \<and> bits = bits2")
          case True
          have result: "unify (BabTy_FiniteInt loc sign bits) (BabTy_FiniteInt loc2 sign2 bits2) = Some fmempty"
            using dom True by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_FiniteInt loc sign bits\<close> BabTy_FiniteInt dom result
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have result: "unify (BabTy_FiniteInt loc sign bits) (BabTy_FiniteInt loc2 sign2 bits2) = None"
            using dom False by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_FiniteInt loc sign bits\<close> BabTy_FiniteInt dom result
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case (BabTy_Bool loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_FiniteInt loc sign bits, BabTy_Bool loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_FiniteInt loc sign bits) (BabTy_Bool loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_FiniteInt loc sign bits\<close> BabTy_Bool dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Name loc2 name2 args2)
        have dom: "unify_unify_list_dom (Inl (BabTy_FiniteInt loc sign bits, BabTy_Name loc2 name2 args2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_FiniteInt loc sign bits) (BabTy_Name loc2 name2 args2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_FiniteInt loc sign bits\<close> BabTy_Name dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_MathInt loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_FiniteInt loc sign bits, BabTy_MathInt loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_FiniteInt loc sign bits) (BabTy_MathInt loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_FiniteInt loc sign bits\<close> BabTy_MathInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_MathReal loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_FiniteInt loc sign bits, BabTy_MathReal loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_FiniteInt loc sign bits) (BabTy_MathReal loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_FiniteInt loc sign bits\<close> BabTy_MathReal dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Tuple loc2 tys2)
        have dom: "unify_unify_list_dom (Inl (BabTy_FiniteInt loc sign bits, BabTy_Tuple loc2 tys2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_FiniteInt loc sign bits) (BabTy_Tuple loc2 tys2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_FiniteInt loc sign bits\<close> BabTy_Tuple dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Record loc2 flds2)
        have dom: "unify_unify_list_dom (Inl (BabTy_FiniteInt loc sign bits, BabTy_Record loc2 flds2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_FiniteInt loc sign bits) (BabTy_Record loc2 flds2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_FiniteInt loc sign bits\<close> BabTy_Record dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Array loc2 elem2 dims2)
        have dom: "unify_unify_list_dom (Inl (BabTy_FiniteInt loc sign bits, BabTy_Array loc2 elem2 dims2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_FiniteInt loc sign bits) (BabTy_Array loc2 elem2 dims2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_FiniteInt loc sign bits\<close> BabTy_Array dom result
          by (auto simp: unify_terminates_with_props_def)
      qed
    next
      case (BabTy_MathInt loc)
      show ?thesis
        using Inl pair_eq BabTy_MathInt
      proof (cases ty2)
        case (BabTy_Meta m)
        have dom: "unify_unify_list_dom (Inl (BabTy_MathInt loc, BabTy_Meta m))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_MathInt loc) (BabTy_Meta m) = Some (singleton_subst m (BabTy_MathInt loc))"
          using dom by (simp add: unify.psimps)
        have props: "subst_props (unify_input_mvs (BabTy_MathInt loc) (BabTy_Meta m)) (singleton_subst m (BabTy_MathInt loc))"
          by (auto simp: unify_input_mvs_def intro: subst_props_singleton simp: occurs_def)
        show ?thesis
          using Inl pair_eq BabTy_MathInt BabTy_Meta dom result props
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_MathInt loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_MathInt loc, BabTy_MathInt loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_MathInt loc) (BabTy_MathInt loc2) = Some fmempty"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_MathInt loc\<close> BabTy_MathInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Bool loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_MathInt loc, BabTy_Bool loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_MathInt loc) (BabTy_Bool loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_MathInt loc\<close> BabTy_Bool dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Name loc2 name2 args2)
        have dom: "unify_unify_list_dom (Inl (BabTy_MathInt loc, BabTy_Name loc2 name2 args2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_MathInt loc) (BabTy_Name loc2 name2 args2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_MathInt loc\<close> BabTy_Name dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_FiniteInt loc2 sign2 bits2)
        have dom: "unify_unify_list_dom (Inl (BabTy_MathInt loc, BabTy_FiniteInt loc2 sign2 bits2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_MathInt loc) (BabTy_FiniteInt loc2 sign2 bits2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_MathInt loc\<close> BabTy_FiniteInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_MathReal loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_MathInt loc, BabTy_MathReal loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_MathInt loc) (BabTy_MathReal loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_MathInt loc\<close> BabTy_MathReal dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Tuple loc2 tys2)
        have dom: "unify_unify_list_dom (Inl (BabTy_MathInt loc, BabTy_Tuple loc2 tys2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_MathInt loc) (BabTy_Tuple loc2 tys2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_MathInt loc\<close> BabTy_Tuple dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Record loc2 flds2)
        have dom: "unify_unify_list_dom (Inl (BabTy_MathInt loc, BabTy_Record loc2 flds2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_MathInt loc) (BabTy_Record loc2 flds2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_MathInt loc\<close> BabTy_Record dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Array loc2 elem2 dims2)
        have dom: "unify_unify_list_dom (Inl (BabTy_MathInt loc, BabTy_Array loc2 elem2 dims2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_MathInt loc) (BabTy_Array loc2 elem2 dims2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_MathInt loc\<close> BabTy_Array dom result
          by (auto simp: unify_terminates_with_props_def)
      qed
    next
      case (BabTy_MathReal loc)
      show ?thesis
        using Inl pair_eq BabTy_MathReal
      proof (cases ty2)
        case (BabTy_Meta m)
        have dom: "unify_unify_list_dom (Inl (BabTy_MathReal loc, BabTy_Meta m))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_MathReal loc) (BabTy_Meta m) = Some (singleton_subst m (BabTy_MathReal loc))"
          using dom by (simp add: unify.psimps)
        have props: "subst_props (unify_input_mvs (BabTy_MathReal loc) (BabTy_Meta m)) (singleton_subst m (BabTy_MathReal loc))"
          by (auto simp: unify_input_mvs_def intro: subst_props_singleton simp: occurs_def)
        show ?thesis
          using Inl pair_eq BabTy_MathReal BabTy_Meta dom result props
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_MathReal loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_MathReal loc, BabTy_MathReal loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_MathReal loc) (BabTy_MathReal loc2) = Some fmempty"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_MathReal loc\<close> BabTy_MathReal dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Bool loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_MathReal loc, BabTy_Bool loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_MathReal loc) (BabTy_Bool loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_MathReal loc\<close> BabTy_Bool dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Name loc2 name2 args2)
        have dom: "unify_unify_list_dom (Inl (BabTy_MathReal loc, BabTy_Name loc2 name2 args2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_MathReal loc) (BabTy_Name loc2 name2 args2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_MathReal loc\<close> BabTy_Name dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_FiniteInt loc2 sign2 bits2)
        have dom: "unify_unify_list_dom (Inl (BabTy_MathReal loc, BabTy_FiniteInt loc2 sign2 bits2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_MathReal loc) (BabTy_FiniteInt loc2 sign2 bits2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_MathReal loc\<close> BabTy_FiniteInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_MathInt loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_MathReal loc, BabTy_MathInt loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_MathReal loc) (BabTy_MathInt loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_MathReal loc\<close> BabTy_MathInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Tuple loc2 tys2)
        have dom: "unify_unify_list_dom (Inl (BabTy_MathReal loc, BabTy_Tuple loc2 tys2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_MathReal loc) (BabTy_Tuple loc2 tys2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_MathReal loc\<close> BabTy_Tuple dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Record loc2 flds2)
        have dom: "unify_unify_list_dom (Inl (BabTy_MathReal loc, BabTy_Record loc2 flds2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_MathReal loc) (BabTy_Record loc2 flds2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_MathReal loc\<close> BabTy_Record dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Array loc2 elem2 dims2)
        have dom: "unify_unify_list_dom (Inl (BabTy_MathReal loc, BabTy_Array loc2 elem2 dims2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_MathReal loc) (BabTy_Array loc2 elem2 dims2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_MathReal loc\<close> BabTy_Array dom result
          by (auto simp: unify_terminates_with_props_def)
      qed
    next
      case BabTy_Tuple1: (BabTy_Tuple loc1 tys1)
      show ?thesis
        using Inl pair_eq BabTy_Tuple1
      proof (cases ty2)
        case (BabTy_Meta m)
        have dom: "unify_unify_list_dom (Inl (BabTy_Tuple loc1 tys1, BabTy_Meta m))"
          by (rule unify_unify_list.domintros)
        show ?thesis
        proof (cases "occurs m (BabTy_Tuple loc1 tys1)")
          case True
          have result: "unify (BabTy_Tuple loc1 tys1) (BabTy_Meta m) = None"
            using dom True by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Tuple loc1 tys1\<close> BabTy_Meta dom result
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have result: "unify (BabTy_Tuple loc1 tys1) (BabTy_Meta m) = Some (singleton_subst m (BabTy_Tuple loc1 tys1))"
            using dom False by (simp add: unify.psimps)
          have props: "subst_props (unify_input_mvs (BabTy_Tuple loc1 tys1) (BabTy_Meta m)) (singleton_subst m (BabTy_Tuple loc1 tys1))"
            using False by (auto simp: unify_input_mvs_def intro: subst_props_singleton)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Tuple loc1 tys1\<close> BabTy_Meta dom result props
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case BabTy_Tuple2: (BabTy_Tuple loc2 tys2')
        have in_rel: "(Inr (tys1, tys2'), Inl (BabTy_Tuple loc1 tys1, BabTy_Tuple loc2 tys2')) \<in> unify_rel"
          by (rule unify_rel_tuple_to_list)
        have IH: "unify_terminates_with_props (Inr (tys1, tys2'))"
          using "1.IH" in_rel Inl pair_eq BabTy_Tuple1 BabTy_Tuple2 by auto
        show ?thesis
        proof (cases "length tys1 = length tys2'")
          case True
          have list_dom: "unify_unify_list_dom (Inr (tys1, tys2'))"
            using IH unfolding unify_terminates_with_props_def by simp
          have dom: "unify_unify_list_dom (Inl (BabTy_Tuple loc1 tys1, BabTy_Tuple loc2 tys2'))"
            using list_dom True by (auto intro: unify_unify_list.domintros)
          have result: "unify (BabTy_Tuple loc1 tys1) (BabTy_Tuple loc2 tys2') = unify_list tys1 tys2'"
            using dom True by (simp add: unify.psimps)
          have list_props: "\<And>subst. unify_list tys1 tys2' = Some subst \<Longrightarrow>
                           subst_props (unify_list_input_mvs tys1 tys2') subst"
            using IH unfolding unify_terminates_with_props_def by simp
          have mvs_eq: "unify_list_input_mvs tys1 tys2' = unify_input_mvs (BabTy_Tuple loc1 tys1) (BabTy_Tuple loc2 tys2')"
            by (auto simp: unify_list_input_mvs_def unify_input_mvs_def list_metavars_def)
          have props: "\<And>subst. unify (BabTy_Tuple loc1 tys1) (BabTy_Tuple loc2 tys2') = Some subst \<Longrightarrow>
                       subst_props (unify_input_mvs (BabTy_Tuple loc1 tys1) (BabTy_Tuple loc2 tys2')) subst"
            using list_props result mvs_eq by simp
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Tuple loc1 tys1\<close> BabTy_Tuple2 dom props
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have dom: "unify_unify_list_dom (Inl (BabTy_Tuple loc1 tys1, BabTy_Tuple loc2 tys2'))"
            using False unify_unify_list.domintros(23) by blast
          have result: "unify (BabTy_Tuple loc1 tys1) (BabTy_Tuple loc2 tys2') = None"
            using dom False by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Tuple loc1 tys1\<close> BabTy_Tuple2 dom result
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case (BabTy_Name loc2 name2 args2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Tuple loc1 tys1, BabTy_Name loc2 name2 args2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Tuple loc1 tys1) (BabTy_Name loc2 name2 args2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Tuple loc1 tys1\<close> BabTy_Name dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Bool loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Tuple loc1 tys1, BabTy_Bool loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Tuple loc1 tys1) (BabTy_Bool loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Tuple loc1 tys1\<close> BabTy_Bool dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_FiniteInt loc2 sign2 bits2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Tuple loc1 tys1, BabTy_FiniteInt loc2 sign2 bits2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Tuple loc1 tys1) (BabTy_FiniteInt loc2 sign2 bits2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Tuple loc1 tys1\<close> BabTy_FiniteInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_MathInt loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Tuple loc1 tys1, BabTy_MathInt loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Tuple loc1 tys1) (BabTy_MathInt loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Tuple loc1 tys1\<close> BabTy_MathInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_MathReal loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Tuple loc1 tys1, BabTy_MathReal loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Tuple loc1 tys1) (BabTy_MathReal loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Tuple loc1 tys1\<close> BabTy_MathReal dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Record loc2 flds2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Tuple loc1 tys1, BabTy_Record loc2 flds2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Tuple loc1 tys1) (BabTy_Record loc2 flds2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Tuple loc1 tys1\<close> BabTy_Record dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Array loc2 elem2 dims2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Tuple loc1 tys1, BabTy_Array loc2 elem2 dims2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Tuple loc1 tys1) (BabTy_Array loc2 elem2 dims2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Tuple loc1 tys1\<close> BabTy_Array dom result
          by (auto simp: unify_terminates_with_props_def)
      qed
    next
      case BabTy_Record1: (BabTy_Record loc1 flds1)
      show ?thesis
        using Inl pair_eq BabTy_Record1
      proof (cases ty2)
        case (BabTy_Meta m)
        have dom: "unify_unify_list_dom (Inl (BabTy_Record loc1 flds1, BabTy_Meta m))"
          by (rule unify_unify_list.domintros)
        show ?thesis
        proof (cases "occurs m (BabTy_Record loc1 flds1)")
          case True
          have result: "unify (BabTy_Record loc1 flds1) (BabTy_Meta m) = None"
            using dom True by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Record loc1 flds1\<close> BabTy_Meta dom result
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have result: "unify (BabTy_Record loc1 flds1) (BabTy_Meta m) = Some (singleton_subst m (BabTy_Record loc1 flds1))"
            using dom False by (simp add: unify.psimps)
          have props: "subst_props (unify_input_mvs (BabTy_Record loc1 flds1) (BabTy_Meta m)) (singleton_subst m (BabTy_Record loc1 flds1))"
            using False by (auto simp: unify_input_mvs_def intro: subst_props_singleton)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Record loc1 flds1\<close> BabTy_Meta dom result props
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case BabTy_Record2: (BabTy_Record loc2 flds2)
        have in_rel: "(Inr (map snd flds1, map snd flds2), Inl (BabTy_Record loc1 flds1, BabTy_Record loc2 flds2)) \<in> unify_rel"
          by (rule unify_rel_record_to_list)
        have IH: "unify_terminates_with_props (Inr (map snd flds1, map snd flds2))"
          using "1.IH" in_rel Inl pair_eq BabTy_Record1 BabTy_Record2 by auto
        show ?thesis
        proof (cases "length flds1 = length flds2 \<and> map fst flds1 = map fst flds2")
          case True
          have list_dom: "unify_unify_list_dom (Inr (map snd flds1, map snd flds2))"
            using IH unfolding unify_terminates_with_props_def by simp
          have dom: "unify_unify_list_dom (Inl (BabTy_Record loc1 flds1, BabTy_Record loc2 flds2))"
            using list_dom True by (auto intro: unify_unify_list.domintros)
          have result: "unify (BabTy_Record loc1 flds1) (BabTy_Record loc2 flds2) = unify_list (map snd flds1) (map snd flds2)"
            using dom True by (simp add: unify.psimps)
          have list_props: "\<And>subst. unify_list (map snd flds1) (map snd flds2) = Some subst \<Longrightarrow>
                           subst_props (unify_list_input_mvs (map snd flds1) (map snd flds2)) subst"
            using IH unfolding unify_terminates_with_props_def by simp
          have mvs_eq: "unify_list_input_mvs (map snd flds1) (map snd flds2) = unify_input_mvs (BabTy_Record loc1 flds1) (BabTy_Record loc2 flds2)"
            by (auto simp: unify_list_input_mvs_def unify_input_mvs_def list_metavars_def)
          have props: "\<And>subst. unify (BabTy_Record loc1 flds1) (BabTy_Record loc2 flds2) = Some subst \<Longrightarrow>
                       subst_props (unify_input_mvs (BabTy_Record loc1 flds1) (BabTy_Record loc2 flds2)) subst"
            using list_props result mvs_eq by simp
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Record loc1 flds1\<close> BabTy_Record2 dom props
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have dom: "unify_unify_list_dom (Inl (BabTy_Record loc1 flds1, BabTy_Record loc2 flds2))"
            using False unify_unify_list.domintros(24) by auto
          have result: "unify (BabTy_Record loc1 flds1) (BabTy_Record loc2 flds2) = None"
            using dom False
            using unify.psimps(24) by presburger 
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Record loc1 flds1\<close> BabTy_Record2 dom result
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case (BabTy_Name loc2 name2 args2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Record loc1 flds1, BabTy_Name loc2 name2 args2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Record loc1 flds1) (BabTy_Name loc2 name2 args2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Record loc1 flds1\<close> BabTy_Name dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Bool loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Record loc1 flds1, BabTy_Bool loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Record loc1 flds1) (BabTy_Bool loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Record loc1 flds1\<close> BabTy_Bool dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_FiniteInt loc2 sign2 bits2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Record loc1 flds1, BabTy_FiniteInt loc2 sign2 bits2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Record loc1 flds1) (BabTy_FiniteInt loc2 sign2 bits2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Record loc1 flds1\<close> BabTy_FiniteInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_MathInt loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Record loc1 flds1, BabTy_MathInt loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Record loc1 flds1) (BabTy_MathInt loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Record loc1 flds1\<close> BabTy_MathInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_MathReal loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Record loc1 flds1, BabTy_MathReal loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Record loc1 flds1) (BabTy_MathReal loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Record loc1 flds1\<close> BabTy_MathReal dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Tuple loc2 tys2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Record loc1 flds1, BabTy_Tuple loc2 tys2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Record loc1 flds1) (BabTy_Tuple loc2 tys2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Record loc1 flds1\<close> BabTy_Tuple dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Array loc2 elem2 dims2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Record loc1 flds1, BabTy_Array loc2 elem2 dims2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Record loc1 flds1) (BabTy_Array loc2 elem2 dims2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Record loc1 flds1\<close> BabTy_Array dom result
          by (auto simp: unify_terminates_with_props_def)
      qed
    next
      case BabTy_Array1: (BabTy_Array loc1 elem1 dims1)
      show ?thesis
        using Inl pair_eq BabTy_Array1
      proof (cases ty2)
        case (BabTy_Meta m)
        have dom: "unify_unify_list_dom (Inl (BabTy_Array loc1 elem1 dims1, BabTy_Meta m))"
          by (rule unify_unify_list.domintros)
        show ?thesis
        proof (cases "occurs m (BabTy_Array loc1 elem1 dims1)")
          case True
          have result: "unify (BabTy_Array loc1 elem1 dims1) (BabTy_Meta m) = None"
            using dom True by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Array loc1 elem1 dims1\<close> BabTy_Meta dom result
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have result: "unify (BabTy_Array loc1 elem1 dims1) (BabTy_Meta m) = Some (singleton_subst m (BabTy_Array loc1 elem1 dims1))"
            using dom False by (simp add: unify.psimps)
          have props: "subst_props (unify_input_mvs (BabTy_Array loc1 elem1 dims1) (BabTy_Meta m)) (singleton_subst m (BabTy_Array loc1 elem1 dims1))"
            using False by (auto simp: unify_input_mvs_def intro: subst_props_singleton)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Array loc1 elem1 dims1\<close> BabTy_Meta dom result props
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case BabTy_Array2: (BabTy_Array loc2 elem2 dims2)
        have in_rel: "(Inl (elem1, elem2), Inl (BabTy_Array loc1 elem1 dims1, BabTy_Array loc2 elem2 dims2)) \<in> unify_rel"
          by (rule unify_rel_array_to_elem)
        have IH: "unify_terminates_with_props (Inl (elem1, elem2))"
          using "1.IH" in_rel Inl pair_eq BabTy_Array1 BabTy_Array2 by auto
        show ?thesis
        proof (cases "dims1 = dims2")
          case True
          have elem_dom: "unify_unify_list_dom (Inl (elem1, elem2))"
            using IH unfolding unify_terminates_with_props_def by simp
          have dom: "unify_unify_list_dom (Inl (BabTy_Array loc1 elem1 dims1, BabTy_Array loc2 elem2 dims2))"
            using elem_dom True by (auto intro: unify_unify_list.domintros)
          have result: "unify (BabTy_Array loc1 elem1 dims1) (BabTy_Array loc2 elem2 dims2) = unify elem1 elem2"
            using dom True by (simp add: unify.psimps)
          have elem_props: "\<And>subst. unify elem1 elem2 = Some subst \<Longrightarrow>
                           subst_props (unify_input_mvs elem1 elem2) subst"
            using IH unfolding unify_terminates_with_props_def by simp
          have mvs_eq: "unify_input_mvs elem1 elem2 = unify_input_mvs (BabTy_Array loc1 elem1 dims1) (BabTy_Array loc2 elem2 dims2)"
            by (auto simp: unify_input_mvs_def)
          have props: "\<And>subst. unify (BabTy_Array loc1 elem1 dims1) (BabTy_Array loc2 elem2 dims2) = Some subst \<Longrightarrow>
                       subst_props (unify_input_mvs (BabTy_Array loc1 elem1 dims1) (BabTy_Array loc2 elem2 dims2)) subst"
            using elem_props result mvs_eq by simp
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Array loc1 elem1 dims1\<close> BabTy_Array2 dom props
            by (auto simp: unify_terminates_with_props_def)
        next
          case False
          have dom: "unify_unify_list_dom (Inl (BabTy_Array loc1 elem1 dims1, BabTy_Array loc2 elem2 dims2))"
            by (metis False unify_unify_list.domintros(25))
          have result: "unify (BabTy_Array loc1 elem1 dims1) (BabTy_Array loc2 elem2 dims2) = None"
            using dom False by (simp add: unify.psimps)
          show ?thesis
            using Inl pair_eq \<open>ty1 = BabTy_Array loc1 elem1 dims1\<close> BabTy_Array2 dom result
            by (auto simp: unify_terminates_with_props_def)
        qed
      next
        case (BabTy_Name loc2 name2 args2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Array loc1 elem1 dims1, BabTy_Name loc2 name2 args2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Array loc1 elem1 dims1) (BabTy_Name loc2 name2 args2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Array loc1 elem1 dims1\<close> BabTy_Name dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Bool loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Array loc1 elem1 dims1, BabTy_Bool loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Array loc1 elem1 dims1) (BabTy_Bool loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Array loc1 elem1 dims1\<close> BabTy_Bool dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_FiniteInt loc2 sign2 bits2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Array loc1 elem1 dims1, BabTy_FiniteInt loc2 sign2 bits2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Array loc1 elem1 dims1) (BabTy_FiniteInt loc2 sign2 bits2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Array loc1 elem1 dims1\<close> BabTy_FiniteInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_MathInt loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Array loc1 elem1 dims1, BabTy_MathInt loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Array loc1 elem1 dims1) (BabTy_MathInt loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Array loc1 elem1 dims1\<close> BabTy_MathInt dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_MathReal loc2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Array loc1 elem1 dims1, BabTy_MathReal loc2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Array loc1 elem1 dims1) (BabTy_MathReal loc2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Array loc1 elem1 dims1\<close> BabTy_MathReal dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Tuple loc2 tys2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Array loc1 elem1 dims1, BabTy_Tuple loc2 tys2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Array loc1 elem1 dims1) (BabTy_Tuple loc2 tys2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Array loc1 elem1 dims1\<close> BabTy_Tuple dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (BabTy_Record loc2 flds2)
        have dom: "unify_unify_list_dom (Inl (BabTy_Array loc1 elem1 dims1, BabTy_Record loc2 flds2))"
          by (rule unify_unify_list.domintros)
        have result: "unify (BabTy_Array loc1 elem1 dims1) (BabTy_Record loc2 flds2) = None"
          using dom by (simp add: unify.psimps)
        show ?thesis
          using Inl pair_eq \<open>ty1 = BabTy_Array loc1 elem1 dims1\<close> BabTy_Record dom result
          by (auto simp: unify_terminates_with_props_def)
      qed
    qed
  next
    case (Inr pair)
    obtain tys1 tys2 where pair_eq: "pair = (tys1, tys2)" by (cases pair)

    (* Need to show domain holds and props hold for unify_list tys1 tys2 *)
    show ?thesis
    proof (cases tys1)
      case Nil
      show ?thesis
      proof (cases tys2)
        case Nil
        have dom: "unify_unify_list_dom (Inr ([], []))"
          by (rule unify_unify_list.domintros)
        have result: "unify_list [] [] = Some fmempty"
          using dom by (simp add: unify_list.psimps)
        show ?thesis
          using Inr pair_eq \<open>tys1 = []\<close> Nil dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case (Cons ty2 rest2)
        have dom: "unify_unify_list_dom (Inr ([], ty2 # rest2))"
          by (rule unify_unify_list.domintros)
        have result: "unify_list [] (ty2 # rest2) = None"
          using dom by (simp add: unify_list.psimps)
        show ?thesis
          using Inr pair_eq \<open>tys1 = []\<close> Cons dom result
          by (auto simp: unify_terminates_with_props_def)
      qed
    next
      case Cons1: (Cons ty1 rest1)
      show ?thesis
      proof (cases tys2)
        case Nil
        have dom: "unify_unify_list_dom (Inr (ty1 # rest1, []))"
          by (rule unify_unify_list.domintros)
        have result: "unify_list (ty1 # rest1) [] = None"
          using dom by (simp add: unify_list.psimps)
        show ?thesis
          using Inr pair_eq Cons1 Nil dom result
          by (auto simp: unify_terminates_with_props_def)
      next
        case Cons2: (Cons ty2 rest2)
        (* This is the recursive case - unify head, then unify_list on tails *)
        have head_in_rel: "(Inl (ty1, ty2), Inr (ty1 # rest1, ty2 # rest2)) \<in> unify_rel"
          by (rule unify_rel_list_to_head)
        have head_IH: "unify_terminates_with_props (Inl (ty1, ty2))"
          using "1.IH" head_in_rel Inr pair_eq \<open>tys1 = ty1 # rest1\<close> Cons2 by auto
        have head_dom: "unify_unify_list_dom (Inl (ty1, ty2))"
          using head_IH unfolding unify_terminates_with_props_def by simp
        show ?thesis
        proof (cases "unify ty1 ty2")
          case None
          have dom: "unify_unify_list_dom (Inr (ty1 # rest1, ty2 # rest2))"
            using head_dom
            using None unify_unify_list.domintros(83) by force 
          have result: "unify_list (ty1 # rest1) (ty2 # rest2) = None"
            using dom None by (simp add: unify_list.psimps)
          show ?thesis
            using Inr pair_eq \<open>tys1 = ty1 # rest1\<close> Cons2 dom result
            by (auto simp: unify_terminates_with_props_def)
        next
          case (Some subst1)
          have head_props: "subst_props (unify_input_mvs ty1 ty2) subst1"
            using head_IH Some unfolding unify_terminates_with_props_def by simp
          have head_props': "subst_props (type_metavars ty1 \<union> type_metavars ty2) subst1"
            using head_props by (simp add: unify_input_mvs_def)
          (* The recursive call is in the relation *)
          have rec_in_rel: "(Inr (map (apply_subst subst1) rest1, map (apply_subst subst1) rest2),
                            Inr (ty1 # rest1, ty2 # rest2)) \<in> unify_rel"
            by (rule unify_rel_list_recursive[OF head_props'])
          have rec_IH: "unify_terminates_with_props (Inr (map (apply_subst subst1) rest1, map (apply_subst subst1) rest2))"
            using "1.IH" rec_in_rel Inr pair_eq \<open>tys1 = ty1 # rest1\<close> Cons2 by auto
          have rec_dom: "unify_unify_list_dom (Inr (map (apply_subst subst1) rest1, map (apply_subst subst1) rest2))"
            using rec_IH unfolding unify_terminates_with_props_def by simp
          have dom: "unify_unify_list_dom (Inr (ty1 # rest1, ty2 # rest2))"
            using head_dom rec_dom Some by (auto intro: unify_unify_list.domintros)
          show ?thesis
          proof (cases "unify_list (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2)")
            case None
            have result: "unify_list (ty1 # rest1) (ty2 # rest2) = None"
              using dom Some None by (simp add: unify_list.psimps)
            show ?thesis
              using Inr pair_eq \<open>tys1 = ty1 # rest1\<close> Cons2 dom result
              by (auto simp: unify_terminates_with_props_def)
          next
            case (Some subst2)
            have result: "unify_list (ty1 # rest1) (ty2 # rest2) = Some (compose_subst subst2 subst1)"
              using dom \<open>unify ty1 ty2 = Some subst1\<close> Some by (simp add: unify_list.psimps)
            (* Need to show props hold for the composed substitution *)
            have rec_props: "subst_props (unify_list_input_mvs (map (apply_subst subst1) rest1)
                                                               (map (apply_subst subst1) rest2)) subst2"
              using rec_IH Some unfolding unify_terminates_with_props_def by simp
            (* The input mvs for the full call *)
            have full_mvs: "unify_list_input_mvs (ty1 # rest1) (ty2 # rest2) =
                           list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
              by (simp add: unify_list_input_mvs_def)
            (* Props for composed substitution - this requires showing domain/range disjointness *)
            (* First, establish the mvs relationships *)
            have head_mvs: "type_metavars ty1 \<union> type_metavars ty2 \<subseteq>
                           list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
              by (auto simp: list_metavars_def)
            have rec_mvs: "unify_list_input_mvs (map (apply_subst subst1) rest1) (map (apply_subst subst1) rest2)
                          \<subseteq> list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
            proof -
              (* After applying subst1, metavars come from (original - dom) \<union> range, all \<subseteq> head_mvs \<union> rest_mvs *)
              have rest1_mvs: "list_metavars rest1 \<subseteq> list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
                by (auto simp: list_metavars_def)
              have rest2_mvs: "list_metavars rest2 \<subseteq> list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
                by (auto simp: list_metavars_def)
              have range1_mvs: "subst_range_mvs subst1 \<subseteq> type_metavars ty1 \<union> type_metavars ty2"
              proof -
                have "\<And>ty. ty \<in> fmran' subst1 \<Longrightarrow> type_metavars ty \<subseteq> type_metavars ty1 \<union> type_metavars ty2"
                proof -
                  fix ty assume "ty \<in> fmran' subst1"
                  then obtain n where "fmlookup subst1 n = Some ty" by (auto simp: fmran'_def)
                  thus "type_metavars ty \<subseteq> type_metavars ty1 \<union> type_metavars ty2"
                    using head_props' by (auto simp: subst_props_def)
                qed
                thus ?thesis by (auto simp: subst_range_mvs_def)
              qed
              have applied1: "list_metavars (map (apply_subst subst1) rest1) \<subseteq>
                    list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
              proof
                fix x assume "x \<in> list_metavars (map (apply_subst subst1) rest1)"
                then obtain t where t_in: "t \<in> set rest1" and x_in: "x \<in> type_metavars (apply_subst subst1 t)"
                  by (auto simp: list_metavars_def)
                from x_in have "x \<in> (type_metavars t - fset (fmdom subst1)) \<union> subst_range_mvs subst1"
                  using apply_subst_metavars_result by auto
                thus "x \<in> list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
                  using t_in rest1_mvs range1_mvs head_mvs by (auto simp: list_metavars_def)
              qed
              moreover have applied2: "list_metavars (map (apply_subst subst1) rest2) \<subseteq>
                    list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
              proof
                fix x assume "x \<in> list_metavars (map (apply_subst subst1) rest2)"
                then obtain t where t_in: "t \<in> set rest2" and x_in: "x \<in> type_metavars (apply_subst subst1 t)"
                  by (auto simp: list_metavars_def)
                from x_in have "x \<in> (type_metavars t - fset (fmdom subst1)) \<union> subst_range_mvs subst1"
                  using apply_subst_metavars_result by auto
                thus "x \<in> list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)"
                  using t_in rest2_mvs range1_mvs head_mvs by (auto simp: list_metavars_def)
              qed
              ultimately show ?thesis by (auto simp: unify_list_input_mvs_def)
            qed
            (* Lift subst1 props to full mvs *)
            have props1: "subst_props (list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)) subst1"
              using head_props' head_mvs unfolding subst_props_def subst_range_mvs_def
              by blast 
            (* Lift subst2 props to full mvs *)
            have props2: "subst_props (list_metavars (ty1 # rest1) \<union> list_metavars (ty2 # rest2)) subst2"
              using rec_props rec_mvs unfolding subst_props_def subst_range_mvs_def by blast
            (* Domain disjointness: dom(subst2) \<subseteq> rec_mvs which is disjoint from dom(subst1) \<subseteq> head_mvs after applying subst1 *)
            have dom_disj: "fset (fmdom subst2) \<inter> fset (fmdom subst1) = {}"
            proof -
              (* dom(subst1) \<subseteq> type_metavars ty1 \<union> type_metavars ty2 *)
              have dom1_sub: "fset (fmdom subst1) \<subseteq> type_metavars ty1 \<union> type_metavars ty2"
                using head_props' by (auto simp: subst_props_def)
              (* dom(subst2) \<subseteq> list_metavars (map (apply_subst subst1) rest1) \<union> ... *)
              have dom2_sub: "fset (fmdom subst2) \<subseteq> list_metavars (map (apply_subst subst1) rest1) \<union>
                                                     list_metavars (map (apply_subst subst1) rest2)"
                using rec_props by (auto simp: subst_props_def unify_list_input_mvs_def)
              (* After applying subst1, no var from dom(subst1) appears in the result *)
              have "\<And>n. n \<in> fset (fmdom subst1) \<Longrightarrow>
                        n \<notin> list_metavars (map (apply_subst subst1) rest1) \<union>
                             list_metavars (map (apply_subst subst1) rest2)"
              proof -
                fix n assume n_in: "n \<in> fset (fmdom subst1)"
                have "n \<notin> subst_range_mvs subst1"
                  using head_props' n_in by (auto simp: subst_props_def)
                thus "n \<notin> list_metavars (map (apply_subst subst1) rest1) \<union>
                           list_metavars (map (apply_subst subst1) rest2)"
                  using apply_subst_eliminates_dom[OF n_in] by (auto simp: list_metavars_def)
              qed
              thus ?thesis using dom2_sub by auto
            qed
            (* range(subst2) \<inter> dom(subst1) = {} because range(subst2) \<subseteq> rec_mvs which has no dom(subst1) vars *)
            have range2_disj: "subst_range_mvs subst2 \<inter> fset (fmdom subst1) = {}"
            proof -
              have range2_sub: "subst_range_mvs subst2 \<subseteq> list_metavars (map (apply_subst subst1) rest1) \<union>
                                                         list_metavars (map (apply_subst subst1) rest2)"
              proof -
                have "\<And>ty. ty \<in> fmran' subst2 \<Longrightarrow> type_metavars ty \<subseteq>
                      list_metavars (map (apply_subst subst1) rest1) \<union>
                      list_metavars (map (apply_subst subst1) rest2)"
                proof -
                  fix ty assume "ty \<in> fmran' subst2"
                  then obtain n where "fmlookup subst2 n = Some ty"
                    by (auto simp: fmran'_def)
                  thus "type_metavars ty \<subseteq> list_metavars (map (apply_subst subst1) rest1) \<union>
                        list_metavars (map (apply_subst subst1) rest2)"
                    using rec_props by (auto simp: subst_props_def unify_list_input_mvs_def)
                qed
                thus ?thesis by (auto simp: subst_range_mvs_def)
              qed
              have "\<And>n. n \<in> fset (fmdom subst1) \<Longrightarrow>
                        n \<notin> list_metavars (map (apply_subst subst1) rest1) \<union>
                             list_metavars (map (apply_subst subst1) rest2)"
              proof -
                fix n assume n_in: "n \<in> fset (fmdom subst1)"
                have "n \<notin> subst_range_mvs subst1"
                  using head_props' n_in by (auto simp: subst_props_def)
                thus "n \<notin> list_metavars (map (apply_subst subst1) rest1) \<union>
                           list_metavars (map (apply_subst subst1) rest2)"
                  using apply_subst_eliminates_dom[OF n_in] by (auto simp: list_metavars_def)
              qed
              thus ?thesis using range2_sub by auto
            qed
            have props: "subst_props (unify_list_input_mvs (ty1 # rest1) (ty2 # rest2)) (compose_subst subst2 subst1)"
              using subst_props_compose[OF props1 props2 dom_disj range2_disj]
              by (simp add: full_mvs)
            show ?thesis
              using Inr pair_eq \<open>tys1 = ty1 # rest1\<close> Cons2 dom result props
              by (auto simp: unify_terminates_with_props_def)
          qed
        qed
      qed
    qed
  qed
qed

(* Extract termination from the combined proof *)
lemma unify_dom_all: "unify_unify_list_dom x"
  using unify_terminates_with_props_all
  unfolding unify_terminates_with_props_def by simp

(* Termination follows from unify_dom_all *)
termination unify
  using unify_dom_all by auto


end
