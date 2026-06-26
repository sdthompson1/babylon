theory TypeSubst
  imports CoreSyntax CoreTypeProps
begin

(* ========================================================================== *)
(* Type substitution definition and properties. *)
(* ========================================================================== *)

(* A TypeSubst maps type variable names to types. *)
type_synonym TypeSubst = "(string, CoreType) fmap"

(* The singleton substitution: maps n to ty. *)
definition singleton_subst :: "string \<Rightarrow> CoreType \<Rightarrow> TypeSubst" where
  "singleton_subst n ty = fmupd n ty fmempty"

(* Apply a type variable substitution to a type.
   This replaces CoreTy_Var n with subst(n) if defined, otherwise leaves it. *)
fun apply_subst :: "TypeSubst \<Rightarrow> CoreType \<Rightarrow> CoreType" where
  "apply_subst subst (CoreTy_Datatype name tyargs) =
    CoreTy_Datatype name (map (apply_subst subst) tyargs)"
| "apply_subst subst CoreTy_Bool = CoreTy_Bool"
| "apply_subst subst (CoreTy_FiniteInt sign bits) = CoreTy_FiniteInt sign bits"
| "apply_subst subst CoreTy_MathInt = CoreTy_MathInt"
| "apply_subst subst CoreTy_MathReal = CoreTy_MathReal"
| "apply_subst subst (CoreTy_Record flds) =
    CoreTy_Record (map (\<lambda>(name, ty). (name, apply_subst subst ty)) flds)"
| "apply_subst subst (CoreTy_Array elemTy dims) = CoreTy_Array (apply_subst subst elemTy) dims"
| "apply_subst subst (CoreTy_Var n) =
    (case fmlookup subst n of
      Some ty \<Rightarrow> ty
    | None \<Rightarrow> CoreTy_Var n)"

(* Find all type variables appearing in the range of a substitution *)
definition subst_range_tyvars :: "TypeSubst \<Rightarrow> string set" where
  "subst_range_tyvars subst = \<Union>(type_tyvars ` fmran' subst)"


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
  "apply_subst (singleton_subst n ty') (CoreTy_Var n) = ty'"
  by (simp add: singleton_subst_def)

lemma apply_subst_singleton_other:
  "n \<noteq> m \<Longrightarrow> apply_subst (singleton_subst n ty') (CoreTy_Var m) = CoreTy_Var m"
  by (simp add: singleton_subst_def)

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
lemma is_signed_numeric_type_apply_subst:
  "is_signed_numeric_type ty \<Longrightarrow> is_signed_numeric_type (apply_subst subst ty)"
  by (cases ty) auto
lemma is_finite_integer_type_apply_subst:
  "is_finite_integer_type ty \<Longrightarrow> is_finite_integer_type (apply_subst subst ty)"
  by (cases ty) auto
lemma is_numeric_type_apply_subst:
  "is_numeric_type ty \<Longrightarrow> is_numeric_type (apply_subst subst ty)"
  by (cases ty) auto

(* Type variables after applying a substitution come from:
   - type variables in ty that are not in dom(subst), OR
   - type variables in the range of subst (for substituted vars) *)
lemma apply_subst_tyvars_result:
  "type_tyvars (apply_subst subst ty) \<subseteq>
   (type_tyvars ty - fset (fmdom subst)) \<union> subst_range_tyvars subst"
proof (induction ty)
  case (CoreTy_Record flds)
  show ?case
  proof
    fix x assume "x \<in> type_tyvars (apply_subst subst (CoreTy_Record flds))"
    then obtain name ty where mem: "(name, ty) \<in> set flds"
      and x_in: "x \<in> type_tyvars (apply_subst subst ty)"
      by auto
    from CoreTy_Record.IH mem
    have "type_tyvars (apply_subst subst ty) \<subseteq>
          (type_tyvars ty - fset (fmdom subst)) \<union> subst_range_tyvars subst"
      by auto
    with x_in have "x \<in> (type_tyvars ty - fset (fmdom subst)) \<union> subst_range_tyvars subst"
      by auto
    moreover have "type_tyvars ty \<subseteq> type_tyvars (CoreTy_Record flds)"
      using mem by auto
    ultimately show "x \<in> (type_tyvars (CoreTy_Record flds) - fset (fmdom subst)) \<union> subst_range_tyvars subst"
      by auto
  qed
next
  case (CoreTy_Var n)
  then show ?case by (cases "fmlookup subst n"; auto simp: subst_range_tyvars_def fmran'I)
qed (auto)

(* Monotonicity: applying subst to a type variable contained in ty produces a type
   whose type variables are all contained in the result of substituting ty. *)
lemma type_tyvars_apply_subst_mono:
  assumes "a \<in> type_tyvars ty"
  shows "type_tyvars (apply_subst subst (CoreTy_Var a)) \<subseteq> type_tyvars (apply_subst subst ty)"
  using assms
proof (induction ty)
  case (CoreTy_Datatype name tyargs)
  then obtain arg where "arg \<in> set tyargs" "a \<in> type_tyvars arg" by auto
  thus ?case using CoreTy_Datatype.IH by fastforce
next
  case (CoreTy_Record flds)
  then obtain nm t where mem: "(nm, t) \<in> set flds" and a_in: "a \<in> type_tyvars t" by auto
  have "t \<in> Basic_BNFs.snds (nm, t)" by simp
  with mem a_in CoreTy_Record.IH
  have sub: "type_tyvars (apply_subst subst (CoreTy_Var a)) \<subseteq> type_tyvars (apply_subst subst t)"
    by blast
  have "type_tyvars (apply_subst subst t) \<subseteq> type_tyvars (apply_subst subst (CoreTy_Record flds))"
    using mem by force
  thus ?case using sub by blast
next
  case (CoreTy_Array elemTy dims)
  thus ?case by auto
qed auto

(* Corollary: If n is in dom(subst) and not in range(subst), it's eliminated from result *)
corollary apply_subst_eliminates_dom:
  assumes "n \<in> fset (fmdom subst)"
      and "n \<notin> subst_range_tyvars subst"
  shows "n \<notin> type_tyvars (apply_subst subst ty)"
proof -
  have "type_tyvars (apply_subst subst ty) \<subseteq>
        (type_tyvars ty - fset (fmdom subst)) \<union> subst_range_tyvars subst"
    by (rule apply_subst_tyvars_result)
  thus ?thesis using assms by auto
qed

(* Substitution is identity when domain is disjoint from the type's type variables *)
lemma apply_subst_disjoint_id:
  "type_tyvars ty \<inter> fset (fmdom subst) = {} \<Longrightarrow> apply_subst subst ty = ty"
proof (induction ty)
  case (CoreTy_Datatype name tyargs)
  hence "\<forall>arg \<in> set tyargs. apply_subst subst arg = arg" by auto
  thus ?case using CoreTy_Datatype by (simp add: map_idI)
next
  case (CoreTy_Record flds)
  have disjoint: "\<And>name ty. (name, ty) \<in> set flds \<Longrightarrow> type_tyvars ty \<inter> fset (fmdom subst) = {}"
  proof -
    fix name ty assume "(name, ty) \<in> set flds"
    hence "type_tyvars ty \<subseteq> type_tyvars (CoreTy_Record flds)" by auto
    thus "type_tyvars ty \<inter> fset (fmdom subst) = {}"
      using CoreTy_Record.prems by auto
  qed
  hence "\<And>name ty. (name, ty) \<in> set flds \<Longrightarrow> apply_subst subst ty = ty"
    using CoreTy_Record.IH by auto
  hence "map (\<lambda>(name, ty). (name, apply_subst subst ty)) flds = flds"
    by (induction flds) auto
  thus ?case by simp
next
  case (CoreTy_Var n)
  thus ?case by (simp add: fmdom_notD)
qed (simp_all)

(* Special case: If n doesn't occur in ty, then applying singleton_subst n ty'
   leaves ty unchanged *)
corollary apply_subst_singleton_no_occurs:
  "\<not> occurs n ty \<Longrightarrow> apply_subst (singleton_subst n ty') ty = ty"
  using apply_subst_disjoint_id occurs_def singleton_subst_def by simp

(* If s1 and s2 have the same *effect* on each type variable of ty - that is,
   apply_subst s1 (Var v) = apply_subst s2 (Var v) - then they agree on ty. This is
   the most general congruence; note it does NOT require their fmlookups to agree
   (e.g. fmlookup None and fmlookup (Some (Var v)) differ but have the same effect). *)
lemma apply_subst_cong_on_tyvars_val:
  assumes "\<And>v. v \<in> type_tyvars ty \<Longrightarrow>
                apply_subst s1 (CoreTy_Var v) = apply_subst s2 (CoreTy_Var v)"
  shows "apply_subst s1 ty = apply_subst s2 ty"
  using assms
proof (induction ty)
  case (CoreTy_Datatype name tyargs)
  have "\<And>arg. arg \<in> set tyargs \<Longrightarrow> apply_subst s1 arg = apply_subst s2 arg"
    using CoreTy_Datatype.IH CoreTy_Datatype.prems by auto
  thus ?case by simp
next
  case (CoreTy_Record flds)
  have "\<And>nm t. (nm, t) \<in> set flds \<Longrightarrow> apply_subst s1 t = apply_subst s2 t"
  proof -
    fix nm t assume mem: "(nm, t) \<in> set flds"
    have "\<And>v. v \<in> type_tyvars t \<Longrightarrow>
              apply_subst s1 (CoreTy_Var v) = apply_subst s2 (CoreTy_Var v)"
      using CoreTy_Record.prems mem by force
    thus "apply_subst s1 t = apply_subst s2 t"
      using CoreTy_Record.IH mem by simp
  qed
  hence "map (\<lambda>(nm, t). (nm, apply_subst s1 t)) flds
       = map (\<lambda>(nm, t). (nm, apply_subst s2 t)) flds"
    by (induction flds) auto
  thus ?case by simp
next
  case (CoreTy_Array elemTy dims)
  thus ?case by simp
qed auto

(* If s1 and s2 agree (as fmaps) on every type variable that occurs in ty, then
   apply_subst s1 ty = apply_subst s2 ty. A corollary of the effect-based congruence
   above, since equal lookups give equal effect on each Var. *)
lemma apply_subst_cong_on_tyvars:
  assumes "\<And>v. v \<in> type_tyvars ty \<Longrightarrow> fmlookup s1 v = fmlookup s2 v"
  shows "apply_subst s1 ty = apply_subst s2 ty"
proof (rule apply_subst_cong_on_tyvars_val)
  fix v assume "v \<in> type_tyvars ty"
  thus "apply_subst s1 (CoreTy_Var v) = apply_subst s2 (CoreTy_Var v)"
    using assms by simp
qed

(* Substituting runtime types preserves runtime-ness.
   The source env (where ty lives) and target env (where the result lives) may differ:
   the substitution must map every runtime type variable in src that is not also in tgt
   to a type runtime in tgt, and any runtime type variables left over must still be in tgt.
   TE_GhostDatatypes must be the same across src and tgt. *)
(* See also: apply_subst_preserves_well_kinded in CoreKindcheck.thy *)
lemma apply_subst_preserves_runtime:
  assumes "is_runtime_type src ty"
    and "TE_GhostDatatypes tgt = TE_GhostDatatypes src"
    and "\<And>n. n |\<in>| TE_RuntimeTypeVars src \<Longrightarrow>
             (case fmlookup subst n of
                Some ty' \<Rightarrow> is_runtime_type tgt ty'
              | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars tgt)"
  shows "is_runtime_type tgt (apply_subst subst ty)"
using assms proof (induction ty)
  case (CoreTy_Datatype name tyArgs)
  have not_ghost: "name |\<notin>| TE_GhostDatatypes tgt"
    using CoreTy_Datatype.prems(1,2) by simp
  have "list_all (is_runtime_type src) tyArgs"
    using CoreTy_Datatype.prems(1) by simp
  hence "list_all (is_runtime_type tgt) (map (apply_subst subst) tyArgs)"
    using CoreTy_Datatype.IH CoreTy_Datatype.prems(2,3)
    by (simp add: list_all_iff)
  thus ?case using not_ghost by simp
next
  case (CoreTy_Record flds)
  have "list_all (is_runtime_type src) (map snd flds)"
    using CoreTy_Record.prems(1) by simp
  hence "list_all (is_runtime_type tgt) (map (apply_subst subst \<circ> snd) flds)"
    using CoreTy_Record.IH CoreTy_Record.prems(2,3)
    by (simp add: comp_def list.pred_map list.pred_mono_strong snds.intros)
  moreover have "map (apply_subst subst \<circ> snd) flds =
                 map (snd \<circ> (\<lambda>(name, ty). (name, apply_subst subst ty))) flds"
    by (simp add: comp_def case_prod_beta)
  ultimately show ?case by simp
next
  case (CoreTy_Var n)
  from CoreTy_Var.prems(1) have n_in_src: "n |\<in>| TE_RuntimeTypeVars src" by simp
  show ?case
  proof (cases "fmlookup subst n")
    case None
    from CoreTy_Var.prems(3)[OF n_in_src] None have "n |\<in>| TE_RuntimeTypeVars tgt" by simp
    thus ?thesis using None by simp
  next
    case (Some ty')
    from CoreTy_Var.prems(3)[OF n_in_src] Some have "is_runtime_type tgt ty'" by simp
    thus ?thesis using Some by simp
  qed
qed simp_all

(* Specialization lemma:
   When substituting a type runtime-valid in "env with TypeVars/RuntimeTypeVars set to the
   module's abstract types together with the type parameters" by a fully-populated zip
   substitution mapping each type parameter to a runtime type in env, the result is
   runtime-valid in env. The abstract runtime tyvars (TE_AbstractTypes env |\<inter>|
   TE_RuntimeTypeVars env) remain in scope after substitution because they are runtime
   tyvars of env. *)
lemma apply_subst_specializes_runtime:
  assumes src_rt: "is_runtime_type (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyvars,
                                           TE_RuntimeTypeVars := (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                                                  |\<union>| fset_of_list tyvars \<rparr>) ty"
    and tys_rt: "list_all (is_runtime_type env) tys"
    and len_eq: "length tyvars = length tys"
  shows "is_runtime_type env (apply_subst (fmap_of_list (zip tyvars tys)) ty)"
proof (rule apply_subst_preserves_runtime[OF src_rt])
  show "TE_GhostDatatypes env =
          TE_GhostDatatypes (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyvars,
                                    TE_RuntimeTypeVars := (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                                           |\<union>| fset_of_list tyvars \<rparr>)" by simp
next
  fix n assume "n |\<in>| TE_RuntimeTypeVars (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyvars,
                  TE_RuntimeTypeVars := (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                         |\<union>| fset_of_list tyvars \<rparr>)"
  hence n_in: "n |\<in>| TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env \<or> n \<in> set tyvars"
    by (simp add: fset_of_list.rep_eq)
  show "case fmlookup (fmap_of_list (zip tyvars tys)) n of
          Some ty' \<Rightarrow> is_runtime_type env ty'
        | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars env"
  proof (cases "fmlookup (fmap_of_list (zip tyvars tys)) n")
    case None
    \<comment> \<open>n is not a substituted type parameter, so it is an abstract runtime tyvar, which
        is in TE_RuntimeTypeVars env. \<close>
    hence "n \<notin> fst ` set (zip tyvars tys)"
      by (simp add: fmap_of_list.rep_eq map_of_eq_None_iff)
    hence "n \<notin> set tyvars" using len_eq by (meson map_of_eq_None_iff map_of_zip_is_None)
    with n_in have "n |\<in>| TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env" by simp
    hence "n |\<in>| TE_RuntimeTypeVars env" by simp
    thus ?thesis using None by simp
  next
    case (Some ty')
    hence "ty' \<in> set tys"
      using fmap_of_list_SomeD by (metis in_set_zipE)
    with tys_rt have "is_runtime_type env ty'" by (simp add: list_all_iff)
    with Some show ?thesis by simp
  qed
qed

(* Helper: map_of on zipped lists with mapped second component *)
lemma map_of_zip_map:
  assumes "length vars = length tys"
  shows "map_of (zip vars (map f tys)) = map_option f \<circ> map_of (zip vars tys)"
proof
  fix n
  show "map_of (zip vars (map f tys)) n = (map_option f \<circ> map_of (zip vars tys)) n"
    using assms by (induction vars tys rule: list_induct2) auto
qed

lemma fmlookup_zip_map:
  assumes "length vars = length tys"
      and "fmlookup (fmap_of_list (zip vars tys)) n = Some ty"
  shows "fmlookup (fmap_of_list (zip vars (map f tys))) n = Some (f ty)"
  using assms map_of_zip_map[OF assms(1), of f]
  by (simp add: fmlookup_of_list)

(* Applying a substitution built from (vars -> map (apply_subst s) tys) is the same
   as first applying the (vars -> tys) substitution, then applying s.

   This is the capture-avoiding form: the type may mention type variables outside `vars`,
   provided `s` is the identity on them (they are not in s's domain). Concretely, a
   payload/signature type may mention module-level abstract types (outside the function/ctor's
   own type parameters `vars`), and as long as the outer substitution `s` does not touch those
   abstract types, the two substitution orders still commute.

   See also the specialized form, apply_subst_compose_zip, below. *)
lemma apply_subst_compose_zip_extra:
  assumes len_eq: "length vars = length tys"
      and tyvars_ok: "\<And>n. n \<in> type_tyvars ty \<Longrightarrow> n \<in> set vars \<or> n |\<notin>| fmdom s"
      and distinct_vars: "distinct vars"
  shows "apply_subst (fmap_of_list (zip vars (map (apply_subst s) tys))) ty
       = apply_subst s (apply_subst (fmap_of_list (zip vars tys)) ty)"
  using assms
proof (induction ty)
  case (CoreTy_Var n)
  show ?case
  proof (cases "n \<in> set vars")
    case True
    then obtain i where i_bound: "i < length vars" and vars_i: "vars ! i = n"
      by (metis in_set_conv_nth)
    with len_eq have i_bound_tys: "i < length tys" by simp
    have lookup_eq: "fmlookup (fmap_of_list (zip vars tys)) n = Some (tys ! i)"
      using i_bound i_bound_tys vars_i distinct_vars
      by (metis fmap_of_list.rep_eq len_eq map_of_zip_nth)
    hence "fmlookup (fmap_of_list (zip vars (map (apply_subst s) tys))) n
         = Some (apply_subst s (tys ! i))"
      by (simp add: len_eq fmlookup_zip_map)
    thus ?thesis using lookup_eq by simp
  next
    case False
    \<comment> \<open>n not among vars: not in either zip's domain, and s fixes it. \<close>
    from False have not_in_zip: "fmlookup (fmap_of_list (zip vars tys)) n = None"
      by (simp add: fmlookup_of_list len_eq)
    from False have not_in_zip2: "fmlookup (fmap_of_list (zip vars (map (apply_subst s) tys))) n = None"
      by (simp add: fmlookup_of_list len_eq)
    from CoreTy_Var.prems(2)[of n] False have "n |\<notin>| fmdom s" by simp
    hence "fmlookup s n = None" by (simp add: fmdom_notD)
    thus ?thesis using not_in_zip not_in_zip2 by simp
  qed
next
  case (CoreTy_Datatype name tyargs)
  have "\<And>arg. arg \<in> set tyargs \<Longrightarrow>
          apply_subst (fmap_of_list (zip vars (map (apply_subst s) tys))) arg
        = apply_subst s (apply_subst (fmap_of_list (zip vars tys)) arg)"
    using CoreTy_Datatype.IH CoreTy_Datatype.prems(2) distinct_vars len_eq by auto
  thus ?case by simp
next
  case (CoreTy_Record flds)
  have "\<And>nm t. (nm, t) \<in> set flds \<Longrightarrow>
          apply_subst (fmap_of_list (zip vars (map (apply_subst s) tys))) t
        = apply_subst s (apply_subst (fmap_of_list (zip vars tys)) t)"
  proof -
    fix nm t assume mem: "(nm, t) \<in> set flds"
    have "\<And>n. n \<in> type_tyvars t \<Longrightarrow> n \<in> set vars \<or> n |\<notin>| fmdom s"
      using CoreTy_Record.prems(2) mem by force
    thus "apply_subst (fmap_of_list (zip vars (map (apply_subst s) tys))) t
        = apply_subst s (apply_subst (fmap_of_list (zip vars tys)) t)"
      using CoreTy_Record.IH mem distinct_vars len_eq by simp
  qed
  hence "map (\<lambda>(nm, t). (nm, apply_subst (fmap_of_list (zip vars (map (apply_subst s) tys))) t)) flds
       = map (\<lambda>(nm, t). (nm, apply_subst s (apply_subst (fmap_of_list (zip vars tys)) t))) flds"
    by (induction flds) auto
  also have "... = map ((\<lambda>(nm, t). (nm, apply_subst s t)) \<circ>
                        (\<lambda>(nm, t). (nm, apply_subst (fmap_of_list (zip vars tys)) t))) flds"
    by (simp add: case_prod_unfold comp_def)
  finally show ?case by simp
next
  case (CoreTy_Array elemTy dims)
  thus ?case by simp
qed simp_all

(* Corollary of apply_subst_compose_zip_extra for mapping over a list of types: each
   type may mention variables outside `vars` provided `s` fixes them. *)
lemma map_apply_subst_compose_zip_extra:
  assumes len_eq: "length vars = length tys"
      and tyvars_ok: "\<And>t n. t \<in> set ts \<Longrightarrow> n \<in> type_tyvars t \<Longrightarrow> n \<in> set vars \<or> n |\<notin>| fmdom s"
      and distinct_vars: "distinct vars"
  shows "map (apply_subst (fmap_of_list (zip vars (map (apply_subst s) tys)))) ts
       = map (apply_subst s) (map (apply_subst (fmap_of_list (zip vars tys))) ts)"
proof -
  have "\<And>t. t \<in> set ts \<Longrightarrow>
          apply_subst (fmap_of_list (zip vars (map (apply_subst s) tys))) t
          = apply_subst s (apply_subst (fmap_of_list (zip vars tys)) t)"
  proof -
    fix t assume t_in: "t \<in> set ts"
    have "\<And>n. n \<in> type_tyvars t \<Longrightarrow> n \<in> set vars \<or> n |\<notin>| fmdom s"
      using tyvars_ok t_in by blast
    thus "apply_subst (fmap_of_list (zip vars (map (apply_subst s) tys))) t
          = apply_subst s (apply_subst (fmap_of_list (zip vars tys)) t)"
      using apply_subst_compose_zip_extra[OF len_eq _ distinct_vars] by blast
  qed
  thus ?thesis by simp
qed

(* Specialization of apply_subst_compose_zip_extra: when all type variables of ty are in vars,
   the side condition on s's domain is trivially satisfied. *)
lemma apply_subst_compose_zip:
  assumes "length vars = length tys"
      and "type_tyvars ty \<subseteq> set vars"
      and "distinct vars"
  shows "apply_subst (fmap_of_list (zip vars (map (apply_subst s) tys))) ty
       = apply_subst s (apply_subst (fmap_of_list (zip vars tys)) ty)"
  using assms apply_subst_compose_zip_extra[where vars = vars and tys = tys and ty = ty and s = s]
  by blast

(* Corollary for mapping over a list of types *)
lemma map_apply_subst_compose_zip:
  assumes "length vars = length tys"
      and "\<forall>t \<in> set ts. type_tyvars t \<subseteq> set vars"
      and "distinct vars"
  shows "map (apply_subst (fmap_of_list (zip vars (map (apply_subst s) tys)))) ts
       = map (apply_subst s) (map (apply_subst (fmap_of_list (zip vars tys))) ts)"
  using assms by (induction ts) (auto simp: apply_subst_compose_zip)


(* ========================================================================== *)
(* Composition of substitutions *)
(* ========================================================================== *)

(* Compose two substitutions *)
definition compose_subst :: "TypeSubst \<Rightarrow> TypeSubst \<Rightarrow> TypeSubst" where
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

(* The domain of the composed substitution is the union of the two component domains. *)
lemma fmdom_compose_subst:
  "fmdom (compose_subst s2 s1) = fmdom s2 |\<union>| fmdom s1"
proof (rule fset_eqI)
  fix n
  show "n |\<in>| fmdom (compose_subst s2 s1) \<longleftrightarrow> n |\<in>| fmdom s2 |\<union>| fmdom s1"
  proof (cases "fmlookup s1 n")
    case None
    hence "fmlookup (compose_subst s2 s1) n = fmlookup s2 n"
      by (rule fmlookup_compose_subst_None1)
    thus ?thesis using None
      by (auto simp: fmlookup_dom_iff)
  next
    case (Some ty1)
    hence "fmlookup (compose_subst s2 s1) n = Some (apply_subst s2 ty1)"
      by (rule fmlookup_compose_subst_Some1)
    thus ?thesis using Some
      by (auto simp: fmlookup_dom_iff)
  qed
qed

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

(* Composition of substitutions preserves "runtime-ness" *)
lemma compose_subst_preserves_runtime:
  assumes "\<forall>ty \<in> fmran' s1. is_runtime_type env ty"
      and "\<forall>ty \<in> fmran' s2. is_runtime_type env ty"
    shows "\<forall>ty \<in> fmran' (compose_subst s2 s1). is_runtime_type env ty"
proof
  fix ty assume "ty \<in> fmran' (compose_subst s2 s1)"
  from compose_subst_range[OF this] show "is_runtime_type env ty"
  proof
    assume "ty \<in> fmran' s2"
    thus ?thesis using assms(2) by blast
  next
    assume "\<exists>ty1 \<in> fmran' s1. ty = apply_subst s2 ty1"
    then obtain ty1 where "ty1 \<in> fmran' s1" and "ty = apply_subst s2 ty1" by auto
    from \<open>ty1 \<in> fmran' s1\<close> assms(1) have "is_runtime_type env ty1" by blast
    thus ?thesis
      using \<open>ty \<in> fmran' s2 \<or> (\<exists>ty1\<in>fmran' s1. ty = apply_subst s2 ty1)\<close>
        apply_subst_preserves_runtime assms(1,2)
      by (metis fmran'I option.case_eq_if option.collapse)
  qed
qed


(* ========================================================================== *)
(* General fmap helpers about fmap_of_list and zip *)
(* ========================================================================== *)

lemma fmdom_fmap_of_list_zip:
  "length xs = length ys \<Longrightarrow> fset (fmdom (fmap_of_list (zip xs ys))) = set xs"
  by (induction xs ys rule: list_induct2) auto

lemma fmran'_fmupd_notin:
  "k |\<notin>| fmdom m \<Longrightarrow> fmran' (fmupd k v m) = insert v (fmran' m)"
proof (intro set_eqI iffI)
  fix x
  assume notin: "k |\<notin>| fmdom m"
  { assume "x \<in> fmran' (fmupd k v m)"
    then obtain a where "fmlookup (fmupd k v m) a = Some x"
      by (auto simp: fmran'_def)
    then have "x = v \<or> x \<in> fmran' m"
      by (cases "k = a") (auto simp: fmran'_def)
    thus "x \<in> insert v (fmran' m)" by auto
  }
  { assume "x \<in> insert v (fmran' m)"
    then have "x = v \<or> x \<in> fmran' m" by auto
    then show "x \<in> fmran' (fmupd k v m)"
    proof
      assume "x = v"
      thus ?thesis by (auto simp: fmran'_def)
    next
      assume "x \<in> fmran' m"
      then obtain a where lookup: "fmlookup m a = Some x"
        by (auto simp: fmran'_def)
      hence "a \<noteq> k" using notin by (auto dest: fmdomI)
      hence "fmlookup (fmupd k v m) a = Some x" using lookup by simp
      thus ?thesis
        by (simp add: fmran'I)
    qed
  }
qed

(* The range of fmap_of_list (zip xs ys) is exactly set ys when xs has distinct
   keys and the lengths match. Used downstream for substitution-range conditions
   over zip-built substitutions. *)
lemma fmran'_fmap_of_list_zip:
  "length xs = length ys \<Longrightarrow> distinct xs \<Longrightarrow> fmran' (fmap_of_list (zip xs ys)) = set ys"
proof (induction xs ys rule: list_induct2)
  case Nil
  then show ?case by (simp add: fmran'_def)
next
  case (Cons x xs y ys)
  from Cons.prems have x_notin: "x \<notin> set xs" and distinct_xs: "distinct xs" by simp_all
  from x_notin have x_notin_dom: "x |\<notin>| fmdom (fmap_of_list (zip xs ys))"
    using fmdom_fmap_of_list_zip[OF Cons.hyps] by simp
  have "fmran' (fmap_of_list (zip (x # xs) (y # ys))) =
        fmran' (fmupd x y (fmap_of_list (zip xs ys)))"
    by simp
  also have "... = insert y (fmran' (fmap_of_list (zip xs ys)))"
    using x_notin_dom by (rule fmran'_fmupd_notin)
  also have "... = insert y (set ys)"
    using Cons.IH distinct_xs by simp
  finally show ?case by simp
qed


(* ========================================================================== *)
(* Idempotent substitutions                                                   *)
(*                                                                            *)
(* We define an "idempotent" substitution as one where no domain variable     *)
(* occurs in any range type.                                                  *)
(*                                                                            *)
(* This is strictly stronger than the "applying twice = applying once"        *)
(* definition, because it also rules out a redundant mapping T \<mapsto> T.          *)
(* ========================================================================== *)

definition idempotent_subst :: "TypeSubst \<Rightarrow> bool" where
  "idempotent_subst s \<equiv> subst_range_tyvars s \<inter> fset (fmdom s) = {}"

(* fmempty is trivially idempotent (empty range). *)
lemma idempotent_subst_empty [simp]:
  "idempotent_subst fmempty"
  unfolding idempotent_subst_def subst_range_tyvars_def by simp

(* Applying an idempotent substitution produces a type whose type variables
   avoid the substitution's domain. *)
lemma apply_subst_idem_dom_free:
  assumes "idempotent_subst s"
  shows "type_tyvars (apply_subst s ty) \<inter> fset (fmdom s) = {}"
proof -
  have "type_tyvars (apply_subst s ty) \<subseteq>
        (type_tyvars ty - fset (fmdom s)) \<union> subst_range_tyvars s"
    by (rule apply_subst_tyvars_result)
  moreover have "subst_range_tyvars s \<inter> fset (fmdom s) = {}"
    using assms unfolding idempotent_subst_def .
  ultimately show ?thesis by auto
qed

(* Applying an idempotent substitution twice is the same as applying it once.
   (This is the "other" definition of idempotency.) *)
lemma idempotent_subst_twice:
  assumes "idempotent_subst s"
  shows "apply_subst s (apply_subst s ty) = apply_subst s ty"
  by (simp add: apply_subst_disjoint_id apply_subst_idem_dom_free assms)

(* Note: the converse, "s(s(T)) = s(T) \<Longrightarrow> idempotent_subst s", is true under the
   additional assumption that s has no "self-mappings" (s(T) = T), but the proof
   is a bit tricky so we omit it here. *)

(* Corollary of idempotent_subst_twice: if s maps T to ty, then s has no
   further effect on ty. *)
corollary idempotent_subst_fixes_range:
  assumes "idempotent_subst s"
      and "fmlookup s T = Some ty"
    shows "apply_subst s ty = ty"
proof -
  have "apply_subst s (CoreTy_Var T) = ty"
    using assms(2) by fastforce
  then show ?thesis
    using assms(1) idempotent_subst_twice by blast
qed

end
