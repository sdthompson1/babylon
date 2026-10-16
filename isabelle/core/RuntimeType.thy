theory RuntimeType
  imports CoreTyEnv CoreFreeVars "HOL-Library.While_Combinator"
begin

(* ========================================================================== *)
(* Datatypes mentioned by a type                                              *)
(* ========================================================================== *)

fun type_datatypes :: "CoreType \<Rightarrow> string set" where
  "type_datatypes (CoreTy_Datatype dt args) = insert dt (\<Union>(set (map type_datatypes args)))"
| "type_datatypes CoreTy_Bool = {}"
| "type_datatypes (CoreTy_FiniteInt _ _) = {}"
| "type_datatypes CoreTy_MathInt = {}"
| "type_datatypes CoreTy_MathReal = {}"
| "type_datatypes (CoreTy_Record flds) = \<Union>(set (map (type_datatypes \<circ> snd) flds))"
| "type_datatypes (CoreTy_Array elemTy dims) = type_datatypes elemTy"
| "type_datatypes (CoreTy_Var n) = {}"
| "type_datatypes (CoreTy_Extern _ _) = {}"


(* ========================================================================== *)
(* Runtime types                                                              *)
(* ========================================================================== *)

(* Runtime types are the ones that can be used in executable code.

   MathInt and MathReal are not runtime types, nor is any type containing them
   (e.g. in a record field or a datatype payload).

   Also, any datatype with a non-runtime type argument (e.g. "Maybe<int>") is
   considered non-runtime, regardless of whether the type argument actually
   appears in any of the payloads.

   Type variables are runtime if they appear in TE_RuntimeTypeVars, and
   non-runtime otherwise.

   Given that datatype payloads may contain other datatypes, the above definition
   is recursive, and the recursion might not even terminate (nothing prevents a
   CoreTyEnv from defining recursive datatypes). To sidestep this issue, we
   calculate up front the set of "ghost datatypes" - that is, the set of datatypes that
   contain one or more non-runtime types in at least one of their payloads - by an
   iterative method; see ghost_datatypes below. To determine whether a datatype is
   runtime or not, we then (after checking the type arguments) just have to look it up
   in that set - there is no need to inspect the actual payloads at that point. *)


(* This function determines whether a CoreType is runtime, given G (the set of
   ghost datatype names) and R (the set of runtime type variable names). *)
fun is_runtime_type_g :: "string set \<Rightarrow> string fset \<Rightarrow> CoreType \<Rightarrow> bool" where
  "is_runtime_type_g G R (CoreTy_Datatype nm tyargs) =
     (nm \<notin> G \<and> list_all (is_runtime_type_g G R) tyargs)"
| "is_runtime_type_g G R CoreTy_Bool = True"
| "is_runtime_type_g G R (CoreTy_FiniteInt _ _) = True"
| "is_runtime_type_g G R CoreTy_MathInt = False"
| "is_runtime_type_g G R CoreTy_MathReal = False"
| "is_runtime_type_g G R (CoreTy_Record flds) = list_all (is_runtime_type_g G R) (map snd flds)"
| "is_runtime_type_g G R (CoreTy_Array elemTy dims) = is_runtime_type_g G R elemTy"
| "is_runtime_type_g G R (CoreTy_Var n) = (n |\<in>| R)"
| "is_runtime_type_g G R (CoreTy_Extern _ _) = True"


(* ---- Ghost datatypes ---- *)

(* This section explains how the ghost_datatypes calculation, alluded to above, works. *)

(* Given a type env, and a datatype name, this returns a list of (tyvars, payload type) pairs,
   one per data constructor of that datatype. *)
definition datatype_ctor_entries :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> (string list \<times> CoreType) list" where
  "datatype_ctor_entries env dt =
     (case fmlookup (TE_DataCtorsByType env) dt of
        None \<Rightarrow> []
      | Some cns \<Rightarrow>
          concat (map (\<lambda>cn. case fmlookup (TE_DataCtors env) cn of
                               None \<Rightarrow> []
                             | Some (_, tyvars, payload) \<Rightarrow> [(tyvars, payload)]) cns))"

(* A data constructor is considered to be runtime (given sets G and R) if its payload
   type is runtime, under the assumption that all of the datatype's own type variables
   are runtime. *)
definition payload_runtime :: "string set \<Rightarrow> string fset \<Rightarrow> string list \<Rightarrow> CoreType \<Rightarrow> bool" where
  "payload_runtime G R tyvars payload =
     is_runtime_type_g G (R |\<union>| fset_of_list tyvars) payload"

(* A datatype is runtime (given sets G and R) if all of its payloads are runtime under
   the above definition. *)
definition datatype_payloads_runtime :: "string set \<Rightarrow> string fset \<Rightarrow> CoreTyEnv \<Rightarrow> string \<Rightarrow> bool" where
  "datatype_payloads_runtime G R env dt =
     list_all (\<lambda>(tyvars, payload). payload_runtime G R tyvars payload)
              (datatype_ctor_entries env dt)"

(* This is one round of the fixpoint iteration for calculating the ghost datatype set. *)
definition ghost_step :: "CoreTyEnv \<Rightarrow> string fset \<Rightarrow> string set \<Rightarrow> string set" where
  "ghost_step env R S =
     {dt \<in> fset (fmdom (TE_Datatypes env)). \<not> datatype_payloads_runtime S R env dt}"

(* The set of ghost datatypes of an env (given the runtime type variable set R)
   is the least set S such that every datatype with a non-runtime payload (as defined
   above, with S as the ghost_datatypes set) is in S.

   This means that a datatype is ghost only when forced to be; a cycle of datatypes
   that only mention each other is runtime.

   This is computed by iterating ghost_step from the empty set. The lemma
   ghost_datatypes_r, below, proves that this is the least fixpoint. *)
definition ghost_datatypes_r :: "CoreTyEnv \<Rightarrow> string fset \<Rightarrow> string set" where
  "ghost_datatypes_r env R =
     the (while_option (\<lambda>S. ghost_step env R S \<noteq> S) (ghost_step env R) {})"

(* ghost_datatypes is then just ghost_datatypes_r with an appropriate "R" set.

   The type variables found in datatype definitions would always be abstract types from
   the current env (i.e. elements of TE_AbstractTypes env), *not* local type variables
   of the current function. Therefore, we pass the intersection of TE_AbstractTypes env
   nd TE_RuntimeTypeVars env as the "R" set for ghost_datatypes_r.

   This means that the type variables of an enclosing function (i.e., variable names
   in TE_RuntimeTypeVars but not in TE_AbstractTypes) do not influence the ghost
   datatype set of an env. *)
abbreviation ghost_datatypes :: "CoreTyEnv \<Rightarrow> string set" where
  "ghost_datatypes env \<equiv>
     ghost_datatypes_r env (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)"


(* ---- is_runtime_type definition ---- *)

(* Determine whether a type is runtime. 
   (If used in executable code, this recomputes `ghost_datatypes env` every time it is
   called. Consider using is_runtime_type_g instead.) *)
definition is_runtime_type :: "CoreTyEnv \<Rightarrow> CoreType \<Rightarrow> bool" where
  "is_runtime_type env ty =
     is_runtime_type_g (ghost_datatypes env) (TE_RuntimeTypeVars env) ty"

(* The equations of is_runtime_type, one per type constructor. *)
lemma is_runtime_type_simps [simp]:
  "is_runtime_type env (CoreTy_Datatype nm tyargs) =
     (nm \<notin> ghost_datatypes env \<and> list_all (is_runtime_type env) tyargs)"
  "is_runtime_type env CoreTy_Bool = True"
  "is_runtime_type env (CoreTy_FiniteInt sign bits) = True"
  "is_runtime_type env CoreTy_MathInt = False"
  "is_runtime_type env CoreTy_MathReal = False"
  "is_runtime_type env (CoreTy_Record flds) = list_all (is_runtime_type env) (map snd flds)"
  "is_runtime_type env (CoreTy_Array elemTy dims) = is_runtime_type env elemTy"
  "is_runtime_type env (CoreTy_Var n) = (n |\<in>| TE_RuntimeTypeVars env)"
  "is_runtime_type env (CoreTy_Extern name level) = True"
  by (simp_all add: is_runtime_type_def list_all_iff)

lemma is_runtime_type_g_eq:
  "is_runtime_type_g (ghost_datatypes env) (TE_RuntimeTypeVars env) = is_runtime_type env"
  by (rule ext) (simp add: is_runtime_type_def)

(* A list of type variables (as types) satisfies list_all is_runtime_type, provided
   the variables are all declared runtime in the env *)
lemma list_all_tyvar_is_runtime:
  assumes "\<forall>n \<in> set ns. n |\<in>| TE_RuntimeTypeVars env"
  shows "list_all (is_runtime_type env) (map CoreTy_Var ns)"
  using assms by (induction ns) auto


(* ---- The runtime judgement with explicit inputs ---- *)

(* Runtime-ness is antitone in the ghost set and monotone in the runtime
   type variables. *)
lemma is_runtime_type_g_mono:
  assumes rt: "is_runtime_type_g G R ty" and G: "G' \<subseteq> G" and R: "R |\<subseteq>| R'"
  shows "is_runtime_type_g G' R' ty"
  using rt
proof (induction ty)
  case (CoreTy_Datatype name argTypes)
  from CoreTy_Datatype.prems have
    ng: "name \<notin> G" and
    args_rt: "list_all (is_runtime_type_g G R) argTypes"
    by auto
  have ng': "name \<notin> G'" using ng G by blast
  have args_rt': "list_all (is_runtime_type_g G' R') argTypes"
    using CoreTy_Datatype.IH args_rt by (auto simp: list_all_iff)
  show ?case using ng' args_rt' by simp
next
  case (CoreTy_Record flds)
  have each: "\<And>nm t. (nm, t) \<in> set flds \<Longrightarrow> is_runtime_type_g G' R' t"
  proof -
    fix nm t assume mem: "(nm, t) \<in> set flds"
    from mem CoreTy_Record.prems have "is_runtime_type_g G R t"
      by (auto simp: list_all_iff)
    then show "is_runtime_type_g G' R' t"
      using CoreTy_Record.IH[OF mem] by (simp add: snds.intros)
  qed
  then show ?case by (auto simp: list_all_iff)
next
  case (CoreTy_Array elemTy dims)
  then show ?case by auto
next
  case (CoreTy_Var n)
  then show ?case using R by auto
qed simp_all

(* The ghost set matters only at the datatype heads the type mentions
   (is_runtime_type_g_cong_datatypes); so the antitonicity in the ghost set
   need only hold at those heads (is_runtime_type_g_mono_heads). *)
lemma is_runtime_type_g_cong_datatypes:
  assumes "\<forall>d \<in> type_datatypes ty. (d \<in> G') = (d \<in> G)"
  shows "is_runtime_type_g G' R ty = is_runtime_type_g G R ty"
  using assms
proof (induction ty)
  case (CoreTy_Datatype name argTypes)
  have args: "\<And>t. t \<in> set argTypes \<Longrightarrow> is_runtime_type_g G' R t = is_runtime_type_g G R t"
    using CoreTy_Datatype.IH CoreTy_Datatype.prems by auto
  have hd: "(name \<in> G') = (name \<in> G)"
    using CoreTy_Datatype.prems by auto
  show ?case using hd args by (simp add: list_all_iff)
next
  case (CoreTy_Record flds)
  have flds_gd: "\<forall>(nm, t) \<in> set flds. \<forall>d \<in> type_datatypes t. (d \<in> G') = (d \<in> G)"
    using CoreTy_Record.prems by (auto simp: case_prod_beta comp_def)
  have each: "\<And>t. t \<in> snd ` set flds \<Longrightarrow> is_runtime_type_g G' R t = is_runtime_type_g G R t"
    using CoreTy_Record.IH flds_gd by auto
  then show ?case by (auto simp: list_all_iff)
next
  case (CoreTy_Array elemTy dims)
  then show ?case by auto
qed simp_all

lemma is_runtime_type_g_mono_heads:
  assumes rt: "is_runtime_type_g G R ty"
      and heads: "\<And>d. d \<in> type_datatypes ty \<Longrightarrow> d \<notin> G \<Longrightarrow> d \<notin> G'"
      and R: "R |\<subseteq>| R'"
  shows "is_runtime_type_g G' R' ty"
proof -
  have "is_runtime_type_g (G' \<inter> G) R' ty"
    using is_runtime_type_g_mono[OF rt _ R] by blast
  moreover have "is_runtime_type_g G' R' ty = is_runtime_type_g (G' \<inter> G) R' ty"
    by (rule is_runtime_type_g_cong_datatypes) (use heads in auto)
  ultimately show ?thesis by simp
qed

(* A runtime type has all its type variables among the runtime type
   variables. *)
lemma is_runtime_type_g_tyvars_subset:
  assumes "is_runtime_type_g G R ty"
  shows "type_tyvars ty \<subseteq> fset R"
using assms proof (induction ty)
  case (CoreTy_Datatype name argTypes)
  from CoreTy_Datatype.prems have
    args_rt: "list_all (is_runtime_type_g G R) argTypes" by simp
  show ?case
  proof
    fix x assume "x \<in> type_tyvars (CoreTy_Datatype name argTypes)"
    then obtain arg where arg_in: "arg \<in> set argTypes" and x_in: "x \<in> type_tyvars arg" by auto
    from arg_in args_rt have "is_runtime_type_g G R arg" by (simp add: list_all_iff)
    with CoreTy_Datatype.IH arg_in x_in show "x \<in> fset R" by blast
  qed
next
  case (CoreTy_Record flds)
  from CoreTy_Record.prems have flds_rt: "\<forall>(nm, ty) \<in> set flds. is_runtime_type_g G R ty"
    by (auto simp: list_all_iff)
  show ?case
  proof
    fix x assume "x \<in> type_tyvars (CoreTy_Record flds)"
    then obtain nm ty where nm_ty_in: "(nm, ty) \<in> set flds" and x_in: "x \<in> type_tyvars ty"
      by auto
    from nm_ty_in flds_rt have ty_rt: "is_runtime_type_g G R ty" by blast
    from CoreTy_Record.IH[OF nm_ty_in] ty_rt x_in
    show "x \<in> fset R" by (simp add: subsetD)
  qed
next
  case (CoreTy_Array elemTy dims)
  thus ?case by auto
next
  case (CoreTy_Var n)
  thus ?case by force
qed simp_all

(* If ty is runtime with ghost set G and runtime type variables R, and every
   type variable of ty is in R', then ty is runtime with any smaller ghost
   set and R'. *)
lemma is_runtime_type_g_transfer:
  assumes rt: "is_runtime_type_g G R ty"
    and tv: "type_tyvars ty \<subseteq> fset R'"
    and G: "G' \<subseteq> G"
  shows "is_runtime_type_g G' R' ty"
  using rt tv
proof (induction ty)
  case (CoreTy_Datatype name argTypes)
  from CoreTy_Datatype.prems(1) have
    dt_nonghost: "name \<notin> G" and
    args_rt: "list_all (is_runtime_type_g G R) argTypes"
    by auto
  from CoreTy_Datatype.prems(2) have
    args_tyvars: "\<And>arg. arg \<in> set argTypes \<Longrightarrow> type_tyvars arg \<subseteq> fset R'"
    by auto
  have args_rt': "list_all (is_runtime_type_g G' R') argTypes"
    using CoreTy_Datatype.IH args_rt args_tyvars
    by (induction argTypes) (auto simp: list_all_iff)
  show ?case using dt_nonghost args_rt' G by auto
next
  case (CoreTy_Record flds)
  from CoreTy_Record.prems(1) have flds_rt: "list_all (is_runtime_type_g G R) (map snd flds)"
    by simp
  have "\<And>nm ty. (nm, ty) \<in> set flds \<Longrightarrow> is_runtime_type_g G' R' ty"
  proof -
    fix nm ty assume mem: "(nm, ty) \<in> set flds"
    from mem flds_rt have ty_rt: "is_runtime_type_g G R ty" by (auto simp: list_all_iff)
    have ty_tyvars: "type_tyvars ty \<subseteq> fset R'"
      using mem CoreTy_Record.prems(2) by force
    show "is_runtime_type_g G' R' ty"
      using CoreTy_Record.IH mem ty_tyvars ty_rt by auto
  qed
  thus ?case by (auto simp: list_all_iff)
next
  case (CoreTy_Array elemTy dims)
  thus ?case by auto
next
  case (CoreTy_Var n)
  thus ?case by auto
qed simp_all

(* For ground types (no type variables) the runtime type variables are never
   consulted. *)
lemma is_runtime_type_g_ground:
  assumes "type_tyvars ty = {}"
  shows "is_runtime_type_g G R' ty = is_runtime_type_g G R ty"
using assms proof (induction ty)
  case (CoreTy_Datatype nm tyargs)
  from CoreTy_Datatype.prems have args_ground: "\<forall>t \<in> set tyargs. type_tyvars t = {}"
    by auto
  have IH: "\<And>t. t \<in> set tyargs \<Longrightarrow> is_runtime_type_g G R' t = is_runtime_type_g G R t"
    using CoreTy_Datatype.IH args_ground by auto
  hence "list_all (is_runtime_type_g G R') tyargs = list_all (is_runtime_type_g G R) tyargs"
    by (induction tyargs) auto
  thus ?case by auto
next
  case (CoreTy_Record flds)
  from CoreTy_Record.prems have flds_ground: "\<forall>(nm, t) \<in> set flds. type_tyvars t = {}"
    by (auto simp: case_prod_beta)
  have IH: "\<And>t. t \<in> snd ` set flds \<Longrightarrow> is_runtime_type_g G R' t = is_runtime_type_g G R t"
    using CoreTy_Record.IH flds_ground by auto
  hence "list_all (is_runtime_type_g G R') (map snd flds)
           = list_all (is_runtime_type_g G R) (map snd flds)"
    by (induction flds) auto
  thus ?case by auto
next
  case (CoreTy_Var n) thus ?case by simp
qed auto

lemma is_runtime_type_g_cong:
  "G' = G \<Longrightarrow> R' = R \<Longrightarrow> is_runtime_type_g G' R' ty = is_runtime_type_g G R ty"
  by simp


(* ---- The ghost set: monotonicity, the fixpoint, congruence ---- *)

lemma payload_runtime_mono:
  assumes "payload_runtime G R tyvars payload" and "G' \<subseteq> G" and "R |\<subseteq>| R'"
  shows "payload_runtime G' R' tyvars payload"
proof -
  have "R |\<union>| fset_of_list tyvars |\<subseteq>| R' |\<union>| fset_of_list tyvars"
    using assms(3) by (rule funion_mono) (rule fsubset_refl)
  with assms show ?thesis
    unfolding payload_runtime_def by (blast intro: is_runtime_type_g_mono)
qed

lemma datatype_payloads_runtime_mono:
  assumes "datatype_payloads_runtime G R env dt" and "G' \<subseteq> G" and "R |\<subseteq>| R'"
  shows "datatype_payloads_runtime G' R' env dt"
  using assms unfolding datatype_payloads_runtime_def
  by (auto simp: list_all_iff case_prod_beta intro: payload_runtime_mono)

(* The ghost_step function is monotone (a bigger ghost set makes fewer payloads
   runtime, so more datatypes ghost) and bounded by the datatype domain, so
   its least fixpoint is reached by iteration from the empty set. *)
lemma ghost_step_mono: "mono (ghost_step env R)"
proof (rule monoI)
  fix S S' :: "string set"
  assume sub: "S \<subseteq> S'"
  show "ghost_step env R S \<subseteq> ghost_step env R S'"
  proof
    fix dt assume "dt \<in> ghost_step env R S"
    then have dt_in: "dt \<in> fset (fmdom (TE_Datatypes env))"
          and nrt: "\<not> datatype_payloads_runtime S R env dt"
      unfolding ghost_step_def by auto
    have "\<not> datatype_payloads_runtime S' R env dt"
      using nrt datatype_payloads_runtime_mono[OF _ sub fsubset_refl] by blast
    with dt_in show "dt \<in> ghost_step env R S'"
      unfolding ghost_step_def by simp
  qed
qed

lemma ghost_step_bounded: "ghost_step env R S \<subseteq> fset (fmdom (TE_Datatypes env))"
  unfolding ghost_step_def by auto

lemma ghost_datatypes_r_lfp: "ghost_datatypes_r env R = lfp (ghost_step env R)"
  unfolding ghost_datatypes_r_def
  by (rule lfp_the_while_option[OF ghost_step_mono _ finite_fset, symmetric])
     (rule ghost_step_bounded)

lemma ghost_datatypes_r_unfold:
  "ghost_step env R (ghost_datatypes_r env R) = ghost_datatypes_r env R"
  unfolding ghost_datatypes_r_lfp by (rule lfp_unfold[OF ghost_step_mono, symmetric])

lemma ghost_datatypes_r_subset:
  "ghost_datatypes_r env R \<subseteq> fset (fmdom (TE_Datatypes env))"
  using ghost_step_bounded ghost_datatypes_r_unfold by metis

lemma ghost_datatypes_r_lowerbound:
  "ghost_step env R S \<subseteq> S \<Longrightarrow> ghost_datatypes_r env R \<subseteq> S"
  unfolding ghost_datatypes_r_lfp by (rule lfp_lowerbound)

(* Membership in the ghost set, unfolded once: a datatype is ghost iff some
   payload is not runtime with respect to the ghost set itself. *)
lemma ghost_datatypes_r_iff:
  "dt \<in> ghost_datatypes_r env R \<longleftrightarrow>
     dt |\<in>| fmdom (TE_Datatypes env)
     \<and> \<not> datatype_payloads_runtime (ghost_datatypes_r env R) R env dt"
proof -
  have "dt \<in> ghost_datatypes_r env R \<longleftrightarrow> dt \<in> ghost_step env R (ghost_datatypes_r env R)"
    using ghost_datatypes_r_unfold[of env R] by simp
  then show ?thesis unfolding ghost_step_def by simp
qed

(* A datatype outside the ghost set has runtime payloads, with respect to the
   ghost set. *)
lemma ghost_datatypes_r_payload_runtime:
  assumes "dt |\<in>| fmdom (TE_Datatypes env)"
      and "dt \<notin> ghost_datatypes_r env R"
      and "(tyvars, payload) \<in> set (datatype_ctor_entries env dt)"
  shows "is_runtime_type_g (ghost_datatypes_r env R) (R |\<union>| fset_of_list tyvars) payload"
proof -
  have "datatype_payloads_runtime (ghost_datatypes_r env R) R env dt"
    using assms(1,2) ghost_datatypes_r_iff[of dt env R] by blast
  then show ?thesis
    using assms(3) unfolding datatype_payloads_runtime_def payload_runtime_def
    by (auto simp: list_all_iff)
qed

(* More runtime abstract types make fewer datatypes ghost. *)
lemma ghost_datatypes_r_antitone:
  assumes "R |\<subseteq>| R'"
  shows "ghost_datatypes_r env R' \<subseteq> ghost_datatypes_r env R"
proof (rule ghost_datatypes_r_lowerbound)
  show "ghost_step env R' (ghost_datatypes_r env R) \<subseteq> ghost_datatypes_r env R"
  proof
    fix dt assume "dt \<in> ghost_step env R' (ghost_datatypes_r env R)"
    then have dt_in: "dt \<in> fset (fmdom (TE_Datatypes env))"
          and nrt: "\<not> datatype_payloads_runtime (ghost_datatypes_r env R) R' env dt"
      unfolding ghost_step_def by auto
    have "\<not> datatype_payloads_runtime (ghost_datatypes_r env R) R env dt"
      using nrt datatype_payloads_runtime_mono[OF _ subset_refl assms] by blast
    with dt_in have "dt \<in> ghost_step env R (ghost_datatypes_r env R)"
      unfolding ghost_step_def by simp
    then show "dt \<in> ghost_datatypes_r env R"
      using ghost_datatypes_r_unfold[of env R] by simp
  qed
qed

(* The ghost set reads only the three datatype tables of the env. *)
lemma datatype_ctor_entries_cong:
  assumes "TE_DataCtorsByType env' = TE_DataCtorsByType env"
      and "TE_DataCtors env' = TE_DataCtors env"
  shows "datatype_ctor_entries env' dt = datatype_ctor_entries env dt"
  unfolding datatype_ctor_entries_def assms ..

(* Every constructor entry of a datatype comes from TE_DataCtors. *)
lemma datatype_ctor_entries_source:
  assumes "(tyvars, payload) \<in> set (datatype_ctor_entries env dt)"
  shows "\<exists>ctorName dtName.
           fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payload)"
  using assms unfolding datatype_ctor_entries_def
  by (auto split: option.splits prod.splits) metis

lemma ghost_step_cong:
  assumes "TE_Datatypes env' = TE_Datatypes env"
      and "TE_DataCtors env' = TE_DataCtors env"
      and "TE_DataCtorsByType env' = TE_DataCtorsByType env"
  shows "ghost_step env' R S = ghost_step env R S"
  unfolding ghost_step_def datatype_payloads_runtime_def
            datatype_ctor_entries_cong[OF assms(3,2)] assms(1) ..

lemma ghost_datatypes_r_cong:
  assumes "TE_Datatypes env' = TE_Datatypes env"
      and "TE_DataCtors env' = TE_DataCtors env"
      and "TE_DataCtorsByType env' = TE_DataCtorsByType env"
  shows "ghost_datatypes_r env' R = ghost_datatypes_r env R"
proof -
  have "ghost_step env' R = ghost_step env R"
    by (rule ext) (rule ghost_step_cong[OF assms])
  then show ?thesis unfolding ghost_datatypes_r_def by simp
qed

(* Every field other than the three datatype tables is irrelevant to the
   ghost set. With these, simp reduces ghost_datatypes_r applied to a
   record update to ghost_datatypes_r applied to the base env, and so decides
   the equality of the ghost sets of any two envs that differ only in
   scope-local fields (and in TE_RuntimeTypeVars, when the runtime abstract
   types agree). *)
lemma ghost_datatypes_r_simps [simp]:
  "ghost_datatypes_r (TE_LocalVars_update f1 env) R = ghost_datatypes_r env R"
  "ghost_datatypes_r (TE_GlobalVars_update f2 env) R = ghost_datatypes_r env R"
  "ghost_datatypes_r (TE_GhostLocals_update f3 env) R = ghost_datatypes_r env R"
  "ghost_datatypes_r (TE_ConstLocals_update f4 env) R = ghost_datatypes_r env R"
  "ghost_datatypes_r (TE_TypeVars_update f5 env) R = ghost_datatypes_r env R"
  "ghost_datatypes_r (TE_RuntimeTypeVars_update f6 env) R = ghost_datatypes_r env R"
  "ghost_datatypes_r (TE_ReturnType_update f7 env) R = ghost_datatypes_r env R"
  "ghost_datatypes_r (TE_FunctionGhost_update f8 env) R = ghost_datatypes_r env R"
  "ghost_datatypes_r (TE_FunctionImpure_update f9 env) R = ghost_datatypes_r env R"
  "ghost_datatypes_r (TE_ProofGoal_update f10 env) R = ghost_datatypes_r env R"
  "ghost_datatypes_r (TE_ProofTopLevel_update f11 env) R = ghost_datatypes_r env R"
  "ghost_datatypes_r (TE_Functions_update f12 env) R = ghost_datatypes_r env R"
  "ghost_datatypes_r (TE_AbstractAllocLevels_update f13 env) R = ghost_datatypes_r env R"
  by (rule ghost_datatypes_r_cong; simp)+

(* Extending the runtime type variables by names none of which is a ghost
   abstract type leaves the ghost set unchanged. The first form is what simp
   leaves after stripping the record update; the others are for use by rule. *)
lemma ghost_datatypes_r_extend_eq:
  assumes "TE_AbstractTypes env |\<inter>| extraRT |\<subseteq>| TE_RuntimeTypeVars env"
  shows "ghost_datatypes_r env (TE_AbstractTypes env |\<inter>| (TE_RuntimeTypeVars env |\<union>| extraRT))
           = ghost_datatypes env"
proof -
  have eq: "TE_AbstractTypes env |\<inter>| (TE_RuntimeTypeVars env |\<union>| extraRT)
              = TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env"
    using assms by (intro fset_eqI) (auto dest: fsubsetD)
  show ?thesis unfolding eq ..
qed

lemma ghost_datatypes_extend_eq:
  assumes "TE_AbstractTypes env |\<inter>| extraRT |\<subseteq>| TE_RuntimeTypeVars env"
  shows "ghost_datatypes (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                                TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>)
           = ghost_datatypes env"
  by (simp add: ghost_datatypes_r_extend_eq[OF assms])

lemma ghost_datatypes_extend_subset:
  assumes "TE_AbstractTypes env |\<inter>| extraRT |\<subseteq>| TE_RuntimeTypeVars env"
  shows "ghost_datatypes env
           \<subseteq> ghost_datatypes (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                                      TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>)"
  unfolding ghost_datatypes_extend_eq[OF assms] by (rule subset_refl)

(* The scope of a function signature or a constructor payload: the type
   parameters are in scope and runtime. The ghost set is unchanged provided
   no type parameter shadows an abstract type. *)
lemma ghost_datatypes_scope_eq:
  assumes "fset_of_list tyvars |\<inter>| TE_AbstractTypes env = {||}"
  shows "ghost_datatypes (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyvars,
                                TE_RuntimeTypeVars := (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                                       |\<union>| fset_of_list tyvars \<rparr>)
           = ghost_datatypes env"
proof -
  have notin: "\<And>x. x |\<in>| fset_of_list tyvars \<Longrightarrow> x |\<notin>| TE_AbstractTypes env"
    using assms by (metis fempty_iff finter_iff)
  have eq: "TE_AbstractTypes env
              |\<inter>| ((TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env) |\<union>| fset_of_list tyvars)
              = TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env"
    using notin by (intro fset_eqI) auto
  show ?thesis by (simp add: eq)
qed

(* The same, in the form simp leaves after stripping the record update, and
   for any finite set T of type parameters. *)
lemma ghost_datatypes_r_scope_eq:
  assumes "T |\<inter>| TE_AbstractTypes env = {||}"
  shows "ghost_datatypes_r env
           (TE_AbstractTypes env |\<inter>| ((TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env) |\<union>| T))
           = ghost_datatypes env"
proof -
  have notin: "\<And>x. x |\<in>| T \<Longrightarrow> x |\<notin>| TE_AbstractTypes env"
    using assms by (metis fempty_iff finter_iff)
  have eq: "TE_AbstractTypes env |\<inter>| ((TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env) |\<union>| T)
              = TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env"
    using notin by (intro fset_eqI) auto
  show ?thesis unfolding eq ..
qed

(* Replacing the runtime type variables by a set containing the runtime
   abstract types can only shrink the ghost set; by a set whose abstract
   types are runtime already, only grow it. *)
lemma ghost_datatypes_rtv_upd_subset:
  assumes "TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env |\<subseteq>| r"
  shows "ghost_datatypes (env \<lparr> TE_TypeVars := t, TE_RuntimeTypeVars := r \<rparr>) \<subseteq> ghost_datatypes env"
proof -
  have "ghost_datatypes_r env (TE_AbstractTypes env |\<inter>| r) \<subseteq> ghost_datatypes env"
    using assms by (intro ghost_datatypes_r_antitone) (auto dest: fsubsetD)
  then show ?thesis by simp
qed

lemma ghost_datatypes_rtv_upd_supset:
  assumes "TE_AbstractTypes env |\<inter>| r |\<subseteq>| TE_RuntimeTypeVars env"
  shows "ghost_datatypes env \<subseteq> ghost_datatypes (env \<lparr> TE_TypeVars := t, TE_RuntimeTypeVars := r \<rparr>)"
proof -
  have "ghost_datatypes env \<subseteq> ghost_datatypes_r env (TE_AbstractTypes env |\<inter>| r)"
    using assms by (intro ghost_datatypes_r_antitone) (auto dest: fsubsetD)
  then show ?thesis by simp
qed


(* ---- is_runtime_type, further properties ---- *)

(* is_runtime_type depends on the env only through its ghost set and its
   runtime type variables. *)
lemma is_runtime_type_cong_env:
  assumes "ghost_datatypes env' = ghost_datatypes env"
      and "TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env"
  shows "is_runtime_type env' ty = is_runtime_type env ty"
  using assms unfolding is_runtime_type_def by (rule is_runtime_type_g_cong)

(* The same, in terms of the fields the ghost set is computed from. *)
lemma is_runtime_type_cong_fields:
  assumes "TE_Datatypes env' = TE_Datatypes env"
      and "TE_DataCtors env' = TE_DataCtors env"
      and "TE_DataCtorsByType env' = TE_DataCtorsByType env"
      and "TE_AbstractAllocLevels env' = TE_AbstractAllocLevels env"
      and "TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env"
  shows "is_runtime_type env' ty = is_runtime_type env ty"
proof (rule is_runtime_type_cong_env)
  show "ghost_datatypes env' = ghost_datatypes env"
    unfolding assms(4,5) by (rule ghost_datatypes_r_cong[OF assms(1,2,3)])
qed (rule assms(5))

(* For ground types (no type variables), is_runtime_type doesn't consult
   TE_RuntimeTypeVars at all - the CoreTy_Var case is unreachable. Only the
   ghost set still matters. *)
lemma is_runtime_type_ground_cong_env:
  assumes ground: "type_tyvars ty = {}"
      and gd_eq: "ghost_datatypes env' = ghost_datatypes env"
  shows "is_runtime_type env' ty = is_runtime_type env ty"
  unfolding is_runtime_type_def gd_eq by (rule is_runtime_type_g_ground[OF ground])

lemma is_runtime_type_TE_ConstLocals_irrelevant [simp]:
  "is_runtime_type (env \<lparr> TE_ConstLocals := c \<rparr>) ty = is_runtime_type env ty"
  by (rule is_runtime_type_cong_env) simp_all

(* The fixed fields of a statement-typing environment determine the ghost
   set. The first form is the one to give simp (its left-hand side is a
   normal form); the second is for use by rule. *)
lemma tyenv_fixed_eq_ghost_datatypes_r:
  assumes "tyenv_fixed_eq env1 env2"
  shows "ghost_datatypes_r env1 R = ghost_datatypes_r env2 R"
  using assms unfolding tyenv_fixed_eq_def
  by (intro ghost_datatypes_r_cong) simp_all

lemma tyenv_fixed_eq_ghost_datatypes:
  assumes "tyenv_fixed_eq env1 env2"
  shows "ghost_datatypes env1 = ghost_datatypes env2"
proof -
  from assms have
    "TE_AbstractAllocLevels env1 = TE_AbstractAllocLevels env2"
    "TE_RuntimeTypeVars env1 = TE_RuntimeTypeVars env2"
    unfolding tyenv_fixed_eq_def by simp_all
  then show ?thesis
    by (simp add: tyenv_fixed_eq_ghost_datatypes_r[OF assms])
qed

(* If ty is runtime in an env, then every type variable in ty is in the env's
   TE_RuntimeTypeVars. *)
lemma is_runtime_type_tyvars_subset:
  assumes "is_runtime_type env ty"
  shows "type_tyvars ty \<subseteq> fset (TE_RuntimeTypeVars env)"
  using assms unfolding is_runtime_type_def by (rule is_runtime_type_g_tyvars_subset)

(* Growing TE_RuntimeTypeVars preserves is_runtime_type: it can only shrink
   the ghost set. The TE_TypeVars field may also be extended at the same
   time; is_runtime_type doesn't depend on it, but the combined form is
   convenient for callers. *)
lemma is_runtime_type_extend_runtime_tyvars:
  assumes "is_runtime_type env ty"
  shows "is_runtime_type
           (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                  TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>) ty"
proof -
  have "ghost_datatypes_r env (TE_AbstractTypes env |\<inter>| (TE_RuntimeTypeVars env |\<union>| extraRT))
          \<subseteq> ghost_datatypes env"
    by (rule ghost_datatypes_r_antitone) auto
  then have gd: "ghost_datatypes (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                                      TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>)
                   \<subseteq> ghost_datatypes env"
    by simp
  show ?thesis
    using assms unfolding is_runtime_type_def
    by (rule is_runtime_type_g_mono[OF _ gd]) simp
qed

(* If ty is runtime in one env, every type variable of ty is a runtime tyvar
   in a second env, and the second env's ghost set is no bigger, then ty is
   runtime in the second env. *)
lemma is_runtime_type_transfer:
  assumes rt: "is_runtime_type env1 ty"
    and mvs_in_env2: "type_tyvars ty \<subseteq> fset (TE_RuntimeTypeVars env2)"
    and gd: "ghost_datatypes env2 \<subseteq> ghost_datatypes env1"
  shows "is_runtime_type env2 ty"
  using is_runtime_type_g_transfer[OF rt[unfolded is_runtime_type_def] mvs_in_env2 gd]
  unfolding is_runtime_type_def .

(* The heads-only form of is_runtime_type_transfer: the second env may have
   more ghost datatypes, as long as none of them is a datatype the type
   mentions and runtime in the first env. *)
lemma is_runtime_type_mono_heads:
  assumes rt: "is_runtime_type env1 ty"
      and heads: "\<And>d. d \<in> type_datatypes ty \<Longrightarrow> d \<notin> ghost_datatypes env1
                    \<Longrightarrow> d \<notin> ghost_datatypes env2"
      and rtv: "fset (TE_RuntimeTypeVars env1) \<subseteq> fset (TE_RuntimeTypeVars env2)"
  shows "is_runtime_type env2 ty"
proof -
  have "TE_RuntimeTypeVars env1 |\<subseteq>| TE_RuntimeTypeVars env2"
    using rtv by (simp add: less_eq_fset.rep_eq)
  then show ?thesis
    using is_runtime_type_g_mono_heads[OF rt[unfolded is_runtime_type_def] heads]
    unfolding is_runtime_type_def by blast
qed

(* Growing TE_RuntimeTypeVars (with the ghost set not growing) preserves
   is_runtime_type: a runtime type's tyvars all sit in the source env's
   runtime set. *)
lemma is_runtime_type_mono_rtv:
  assumes rt: "is_runtime_type env1 ty"
      and rtv: "fset (TE_RuntimeTypeVars env1) \<subseteq> fset (TE_RuntimeTypeVars env2)"
      and gd: "ghost_datatypes env2 \<subseteq> ghost_datatypes env1"
  shows "is_runtime_type env2 ty"
proof -
  have "type_tyvars ty \<subseteq> fset (TE_RuntimeTypeVars env2)"
    using is_runtime_type_tyvars_subset[OF rt] rtv by blast
  then show ?thesis using is_runtime_type_transfer[OF rt _ gd] by blast
qed

end
