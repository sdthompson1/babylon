theory AllocLevelSubst
  imports CoreAllocLevel CoreKindcheck TypeSubstEnv
begin

(* Properties of alloc levels (CoreAllocLevel.thy) under changes of the type
   environment:

    - congruence: the level of a type depends only on the four alloc-relevant
      fields of the env (TE_Datatypes, TE_DataCtors, TE_DataCtorsByType,
      TE_AbstractAllocLevels);

    - monotonicity under a realization: substituting an abstract type by a
      type of compatible level, in the env's constructor payloads and in the
      type, can only lower the level;

    - locality: the level of a type is unchanged when the env grows, provided
      the datatypes and abstract types the type reaches keep their entries.

   The second is what carries the elaborator's realization-time alloc-level
   check through later realizations to the end of a module (and so to the
   link-time check link_alloc_ok); the third is what transfers link_alloc_ok
   from a whole-program link to a realization-closed sub-link, and what shows
   that adding a fresh datatype leaves the levels of existing types alone. *)


(* ========================================================================== *)
(* Theorems about type_datatypes (RuntimeType.thy) *)
(* ========================================================================== *)

(* A well-kinded type mentions only declared datatypes. *)
lemma is_well_kinded_type_datatypes_subset:
  assumes "is_well_kinded env ty"
  shows "type_datatypes ty \<subseteq> fset (fmdom (TE_Datatypes env))"
  using assms
proof (induction ty)
  case (CoreTy_Datatype name argTypes)
  from CoreTy_Datatype.prems obtain n where
      lk: "fmlookup (TE_Datatypes env) name = Some n"
      and args_wk: "list_all (is_well_kinded env) argTypes"
    by (auto split: option.splits)
  have "name \<in> fset (fmdom (TE_Datatypes env))"
    using fmdomI[OF lk] by simp
  moreover have "\<And>arg. arg \<in> set argTypes
                   \<Longrightarrow> type_datatypes arg \<subseteq> fset (fmdom (TE_Datatypes env))"
    using CoreTy_Datatype.IH args_wk unfolding list_all_iff by blast
  ultimately show ?case by auto
next
  case (CoreTy_Record flds)
  have wk: "\<And>fld. fld \<in> set flds \<Longrightarrow> is_well_kinded env (snd fld)"
    using CoreTy_Record.prems by (auto simp: list_all_iff)
  have "\<And>fld. fld \<in> set flds
          \<Longrightarrow> type_datatypes (snd fld) \<subseteq> fset (fmdom (TE_Datatypes env))"
    using CoreTy_Record.IH wk by (simp add: snds.intros)
  then show ?case by (auto simp: comp_def)
qed auto

(* Substitution can only add datatypes, and the ones it adds come from the
   ranges of the substituted variables. *)
lemma type_datatypes_subset_apply_subst:
  "type_datatypes ty \<subseteq> type_datatypes (apply_subst s ty)"
proof (induction ty)
  case (CoreTy_Record flds)
  show ?case
  proof
    fix x assume "x \<in> type_datatypes (CoreTy_Record flds)"
    then obtain nm ty where in_f: "(nm, ty) \<in> set flds" and x_ty: "x \<in> type_datatypes ty"
      by auto
    have "x \<in> (type_datatypes \<circ> snd) (nm, apply_subst s ty)"
      using CoreTy_Record.IH[OF in_f] x_ty by auto
    moreover have "(nm, apply_subst s ty) \<in> (\<lambda>(name, ty). (name, apply_subst s ty)) ` set flds"
      using in_f by force
    ultimately show "x \<in> type_datatypes (apply_subst s (CoreTy_Record flds))"
      unfolding apply_subst.simps type_datatypes.simps set_map by blast
  qed
qed auto

lemma type_datatypes_apply_subst_bound:
  "type_datatypes (apply_subst s ty)
     \<subseteq> type_datatypes ty \<union> (\<Union>v \<in> type_tyvars ty. type_datatypes (apply_subst s (CoreTy_Var v)))"
proof (induction ty)
  case (CoreTy_Record flds)
  show ?case
  proof
    fix x assume "x \<in> type_datatypes (apply_subst s (CoreTy_Record flds))"
    then obtain fld where fld_in: "fld \<in> set flds"
        and x_in: "x \<in> type_datatypes (apply_subst s (snd fld))"
      by (auto simp: comp_def case_prod_beta)
    have in2: "(fst fld, snd fld) \<in> set flds" using fld_in by simp
    have "x \<in> type_datatypes (snd fld)
            \<union> (\<Union>v \<in> type_tyvars (snd fld). type_datatypes (apply_subst s (CoreTy_Var v)))"
      using CoreTy_Record.IH[OF in2] x_in
      by (metis (no_types, lifting) CoreTy_Record fld_in in_mono snds.intros)
    then show "x \<in> type_datatypes (CoreTy_Record flds)
                 \<union> (\<Union>v \<in> type_tyvars (CoreTy_Record flds).
                      type_datatypes (apply_subst s (CoreTy_Var v)))"
      using fld_in by (auto simp: comp_def)
  qed
next
  case (CoreTy_Datatype dt args)
  show ?case
  proof
    fix x assume "x \<in> type_datatypes (apply_subst s (CoreTy_Datatype dt args))"
    then consider "x = dt"
      | arg where "arg \<in> set args" and "x \<in> type_datatypes (apply_subst s arg)"
      by auto
    then show "x \<in> type_datatypes (CoreTy_Datatype dt args)
                 \<union> (\<Union>v \<in> type_tyvars (CoreTy_Datatype dt args).
                      type_datatypes (apply_subst s (CoreTy_Var v)))"
    proof cases
      case 1
      then show ?thesis by simp
    next
      case (2 arg)
      have "x \<in> type_datatypes arg
              \<union> (\<Union>v \<in> type_tyvars arg. type_datatypes (apply_subst s (CoreTy_Var v)))"
        using CoreTy_Datatype.IH[OF 2(1)] 2(2) by blast
      then show ?thesis using 2(1) by auto
    qed
  qed
qed auto

(* The variables of a type are variables of the substituted type, or
   substituted away. *)
lemma type_tyvars_subset_apply_subst:
  "type_tyvars ty \<subseteq> type_tyvars (apply_subst s ty) \<union> fset (fmdom s)"
proof (induction ty)
  case (CoreTy_Record flds)
  show ?case
  proof
    fix x assume "x \<in> type_tyvars (CoreTy_Record flds)"
    then obtain nm ty where in_f: "(nm, ty) \<in> set flds" and x_ty: "x \<in> type_tyvars ty"
      by auto
    have "x \<in> (type_tyvars \<circ> snd) (nm, apply_subst s ty) \<union> fset (fmdom s)"
      using CoreTy_Record.IH[OF in_f] x_ty by auto
    moreover have "(nm, apply_subst s ty) \<in> (\<lambda>(name, ty). (name, apply_subst s ty)) ` set flds"
      using in_f by force
    ultimately show "x \<in> type_tyvars (apply_subst s (CoreTy_Record flds)) \<union> fset (fmdom s)"
      unfolding apply_subst.simps type_tyvars.simps set_map by blast
  qed
next
  case (CoreTy_Var n)
  then show ?case by (cases "fmlookup s n") (auto intro: fmdomI)
qed auto


(* ========================================================================== *)
(* Projections of summaries                                                   *)
(* ========================================================================== *)

lemma fst_summary_const [simp]: "fst (summary_const l n) = l"
  by (simp add: summary_const_def)

lemma snd_summary_const [simp]: "snd (summary_const l n) = replicate n Mode_Never"
  by (simp add: summary_const_def)

lemma fst_summary_max [simp]:
  "fst (summary_max s1 s2) = alloc_level_max (fst s1) (fst s2)"
  by (simp add: summary_max_def)

lemma snd_summary_max [simp]:
  "snd (summary_max s1 s2) = map2 mode_max (snd s1) (snd s2)"
  by (simp add: summary_max_def)

lemma fst_summary_compose [simp]:
  "fst (summary_compose m s) = apply_mode m (fst s)"
  by (simp add: summary_compose_def)

lemma snd_summary_compose [simp]:
  "snd (summary_compose m s) = map (mode_min m) (snd s)"
  by (simp add: summary_compose_def)

lemma fst_summary_max_list:
  "fst (summary_max_list n ss) = alloc_level_max_list (map fst ss)"
  unfolding summary_max_list_def alloc_level_max_list_def
  by (induction ss) simp_all

lemma fst_apply_summary:
  "fst (apply_summary n e ss)
     = alloc_level_max_list (fst e # map2 (\<lambda>m s. apply_mode m (fst s)) (snd e) ss)"
  unfolding apply_summary_def fst_summary_max_list
  by (simp add: comp_def case_prod_unfold)

lemma mode_min_Never [simp]: "mode_min m Mode_Never = Mode_Never"
  by (cases m) (simp_all add: mode_min_def mode_le_def)

lemma mode_max_Never_Never [simp]: "mode_max Mode_Never Mode_Never = Mode_Never"
  by (simp add: mode_max_def)

lemma summary_const_le:
  "alloc_level_le a b \<Longrightarrow> summary_le (summary_const a n) (summary_const b n)"
  by (simp add: summary_le_def summary_const_def list_all2_conv_all_nth)

lemma summary_le_fst:
  "summary_le s1 s2 \<Longrightarrow> alloc_level_le (fst s1) (fst s2)"
  by (simp add: summary_le_def)

(* A max of summaries with no parameter contribution has none either. *)
lemma snd_summary_max_list_Never:
  assumes "\<And>s. s \<in> set ss \<Longrightarrow> snd s = replicate n Mode_Never"
  shows "snd (summary_max_list n ss) = replicate n Mode_Never"
  using assms unfolding summary_max_list_def
proof (induction ss)
  case Nil
  show ?case by simp
next
  case (Cons s ss)
  have IH: "snd (foldr summary_max ss (summary_const CoreAlloc_Never n)) = replicate n Mode_Never"
    by (rule Cons.IH) (simp add: Cons.prems)
  have "snd s = replicate n Mode_Never" by (simp add: Cons.prems)
  then show ?case by (simp add: IH)
qed

lemma summary_max_list_const:
  "summary_max_list n (map (\<lambda>a. summary_const (b a) n) as)
     = summary_const (alloc_level_max_list (map b as)) n"
proof (rule prod_eqI)
  show "fst (summary_max_list n (map (\<lambda>a. summary_const (b a) n) as))
          = fst (summary_const (alloc_level_max_list (map b as)) n)"
    by (simp add: fst_summary_max_list comp_def)
  have "snd (summary_max_list n (map (\<lambda>a. summary_const (b a) n) as)) = replicate n Mode_Never"
    by (rule snd_summary_max_list_Never) auto
  then show "snd (summary_max_list n (map (\<lambda>a. summary_const (b a) n) as))
               = snd (summary_const (alloc_level_max_list (map b as)) n)"
    by simp
qed

lemma fst_apply_summary_const:
  "fst (apply_summary n e (map (\<lambda>a. summary_const (b a) n) as))
     = alloc_level_max_list (fst e # map2 (\<lambda>m a. apply_mode m (b a)) (snd e) as)"
  unfolding fst_apply_summary by (simp add: zip_map2 comp_def case_prod_unfold)

lemma snd_apply_summary_const:
  "snd (apply_summary n e (map (\<lambda>a. summary_const (b a) n) as)) = replicate n Mode_Never"
  unfolding apply_summary_def
proof (rule snd_summary_max_list_Never)
  fix s assume "s \<in> set (summary_const (fst e) n
                        # map2 summary_compose (snd e) (map (\<lambda>a. summary_const (b a) n) as))"
  then show "snd s = replicate n Mode_Never"
    by (auto simp: set_zip summary_compose_def)
qed

lemma apply_summary_const:
  "apply_summary n e (map (\<lambda>a. summary_const (b a) n) as)
     = summary_const (fst (apply_summary 0 e (map (\<lambda>a. summary_const (b a) 0) as))) n"
  by (rule prod_eqI) (simp_all add: fst_apply_summary_const snd_apply_summary_const)

(* A type that mentions none of the parameters has a constant summary, whose
   base is its level. *)
lemma summarize_fresh_params:
  assumes "type_tyvars ty \<inter> set params = {}"
  shows "summarize env info params ty
           = summary_const (fst (summarize env info [] ty)) (length params)"
  using assms
proof (induction ty arbitrary: params)
  case (CoreTy_Datatype dt args)
  let ?b = "\<lambda>a. fst (summarize env info [] a)"
  have a1: "map (summarize env info params) args
              = map (\<lambda>a. summary_const (?b a) (length params)) args"
  proof (rule map_cong[OF refl])
    fix a assume a_in: "a \<in> set args"
    have "type_tyvars a \<inter> set params = {}"
      using CoreTy_Datatype.prems a_in by auto
    then show "summarize env info params a = summary_const (?b a) (length params)"
      by (rule CoreTy_Datatype.IH[OF a_in])
  qed
  have a2: "map (summarize env info []) args = map (\<lambda>a. summary_const (?b a) 0) args"
  proof (rule map_cong[OF refl])
    fix a assume a_in: "a \<in> set args"
    show "summarize env info [] a = summary_const (?b a) 0"
      by (metis CoreTy_Datatype.IH a_in boolean_algebra.conj_zero_right empty_set
          list.size(3))
  qed
  show ?case
  proof (rule prod_eqI)
    show "fst (summarize env info params (CoreTy_Datatype dt args))
            = fst (summary_const (fst (summarize env info [] (CoreTy_Datatype dt args)))
                                 (length params))"
      by (simp add: a1 a2 fst_apply_summary_const)
    show "snd (summarize env info params (CoreTy_Datatype dt args))
            = snd (summary_const (fst (summarize env info [] (CoreTy_Datatype dt args)))
                                 (length params))"
      by (simp add: a1 snd_apply_summary_const)
  qed
next
  case (CoreTy_Record flds)
  let ?b = "\<lambda>fld. fst (summarize env info [] (snd fld))"
  have r1: "map (\<lambda>fld. summarize env info params (snd fld)) flds
              = map (\<lambda>fld. summary_const (?b fld) (length params)) flds"
  proof (rule map_cong[OF refl])
    fix fld assume f_in: "fld \<in> set flds"
    have fr: "type_tyvars (snd fld) \<inter> set params = {}"
      using CoreTy_Record.prems f_in by (auto simp: comp_def)
    show "summarize env info params (snd fld) = summary_const (?b fld) (length params)"
      by (rule CoreTy_Record.IH[OF f_in snds.intros fr])
  qed
  have r2: "map (\<lambda>fld. summarize env info [] (snd fld)) flds
              = map (\<lambda>fld. summary_const (?b fld) 0) flds"
  proof (rule map_cong[OF refl])
    fix fld assume f_in: "fld \<in> set flds"
    show "summarize env info [] (snd fld) = summary_const (?b fld) 0"
      by (metis CoreTy_Record.IH Int_empty_right empty_set f_in list.size(3) snds.intros)
  qed
  show ?case by (simp add: r1 r2 summary_max_list_const)
next
  case (CoreTy_Array elemTy dims)
  have IH: "summarize env info params elemTy
              = summary_const (fst (summarize env info [] elemTy)) (length params)"
    by (rule CoreTy_Array.IH) (use CoreTy_Array.prems in simp)
  show ?case
    by (cases "list_ex (\<lambda>d. d = CoreDim_Allocatable) dims") (simp_all add: IH)
next
  case (CoreTy_Var v)
  show ?case using CoreTy_Var.prems by simp
qed simp_all


(* ========================================================================== *)
(* Congruence: summarize reads only what the type reaches                     *)
(* ========================================================================== *)

(* The summary of a type depends on the datatype summaries only at the
   datatypes it mentions, and on the level map only at its free (non-parameter)
   type variables. *)
lemma summarize_cong:
  assumes info: "\<And>dt. dt \<in> type_datatypes ty \<Longrightarrow> info1 dt = info2 dt"
      and lv: "\<And>v. v \<in> type_tyvars ty \<Longrightarrow> v \<notin> set params \<Longrightarrow>
                 fmlookup (TE_AbstractAllocLevels env1) v = fmlookup (TE_AbstractAllocLevels env2) v"
  shows "summarize env1 info1 params ty = summarize env2 info2 params ty"
  using assms
proof (induction ty)
  case (CoreTy_Datatype dt args)
  have args_eq: "map (summarize env1 info1 params) args = map (summarize env2 info2 params) args"
  proof (rule map_cong[OF refl])
    fix x assume x_in: "x \<in> set args"
    show "summarize env1 info1 params x = summarize env2 info2 params x"
    proof (rule CoreTy_Datatype.IH[OF x_in])
      fix d assume "d \<in> type_datatypes x"
      then have "d \<in> type_datatypes (CoreTy_Datatype dt args)" using x_in by auto
      then show "info1 d = info2 d" by (rule CoreTy_Datatype.prems(1))
    next
      fix v assume "v \<in> type_tyvars x" and nv: "v \<notin> set params"
      then have "v \<in> type_tyvars (CoreTy_Datatype dt args)" using x_in by auto
      then show "fmlookup (TE_AbstractAllocLevels env1) v = fmlookup (TE_AbstractAllocLevels env2) v"
        using nv by (rule CoreTy_Datatype.prems(2))
    qed
  qed
  have "info1 dt = info2 dt" by (rule CoreTy_Datatype.prems(1)) simp
  then show ?case by (simp add: args_eq)
next
  case (CoreTy_Record flds)
  have "map (\<lambda>fld. summarize env1 info1 params (snd fld)) flds
          = map (\<lambda>fld. summarize env2 info2 params (snd fld)) flds"
  proof (rule map_cong[OF refl])
    fix fld assume f_in: "fld \<in> set flds"
    show "summarize env1 info1 params (snd fld) = summarize env2 info2 params (snd fld)"
    proof (rule CoreTy_Record.IH[OF f_in snds.intros])
      fix d assume "d \<in> type_datatypes (snd fld)"
      then have "d \<in> type_datatypes (CoreTy_Record flds)" using f_in by (auto simp: comp_def)
      then show "info1 d = info2 d" by (rule CoreTy_Record.prems(1))
    next
      fix v assume "v \<in> type_tyvars (snd fld)" and nv: "v \<notin> set params"
      then have "v \<in> type_tyvars (CoreTy_Record flds)" using f_in by (auto simp: comp_def)
      then show "fmlookup (TE_AbstractAllocLevels env1) v = fmlookup (TE_AbstractAllocLevels env2) v"
        using nv by (rule CoreTy_Record.prems(2))
    qed
  qed
  then show ?case using summarize.simps(6) by presburger
next
  case (CoreTy_Array elemTy dims)
  have "summarize env1 info1 params elemTy = summarize env2 info2 params elemTy"
  proof (rule CoreTy_Array.IH)
    fix d assume "d \<in> type_datatypes elemTy"
    then have "d \<in> type_datatypes (CoreTy_Array elemTy dims)" by simp
    then show "info1 d = info2 d" by (rule CoreTy_Array.prems(1))
  next
    fix v assume "v \<in> type_tyvars elemTy" and nv: "v \<notin> set params"
    then have "v \<in> type_tyvars (CoreTy_Array elemTy dims)" by simp
    then show "fmlookup (TE_AbstractAllocLevels env1) v = fmlookup (TE_AbstractAllocLevels env2) v"
      using nv by (rule CoreTy_Array.prems(2))
  qed
  then show ?case by simp
next
  case (CoreTy_Var v)
  have "fmlookup (TE_AbstractAllocLevels env1) v = fmlookup (TE_AbstractAllocLevels env2) v"
    if "v \<notin> set params"
    using CoreTy_Var.prems(2)[of v] that by simp
  then show ?case by (cases "v \<in> set params") simp_all
qed simp_all

(* The four fields the level computation reads. *)
definition alloc_fields_eq :: "CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "alloc_fields_eq env1 env2 \<longleftrightarrow>
     TE_Datatypes env1 = TE_Datatypes env2
     \<and> TE_DataCtors env1 = TE_DataCtors env2
     \<and> TE_DataCtorsByType env1 = TE_DataCtorsByType env2
     \<and> TE_AbstractAllocLevels env1 = TE_AbstractAllocLevels env2"

lemma summarize_cong_env:
  assumes "TE_AbstractAllocLevels env1 = TE_AbstractAllocLevels env2"
  shows "summarize env1 info params ty = summarize env2 info params ty"
  by (rule summarize_cong) (simp_all add: assms)

lemma ctor_summary_cong_env:
  assumes "alloc_fields_eq env1 env2"
  shows "ctor_summary env1 info arity c = ctor_summary env2 info arity c"
proof -
  have dc: "TE_DataCtors env1 = TE_DataCtors env2"
   and lv: "TE_AbstractAllocLevels env1 = TE_AbstractAllocLevels env2"
    using assms unfolding alloc_fields_eq_def by blast+
  show ?thesis
    unfolding ctor_summary_def dc summarize_cong_env[OF lv] ..
qed

lemma datatype_summary_cong_env:
  assumes "alloc_fields_eq env1 env2"
  shows "datatype_summary env1 info dt = datatype_summary env2 info dt"
proof -
  have dts: "TE_Datatypes env1 = TE_Datatypes env2"
   and bt: "TE_DataCtorsByType env1 = TE_DataCtorsByType env2"
    using assms unfolding alloc_fields_eq_def by blast+
  show ?thesis
    unfolding datatype_summary_def dts bt ctor_summary_cong_env[OF assms] ..
qed

lemma decode_info_cong_env:
  assumes "TE_Datatypes env1 = TE_Datatypes env2"
  shows "decode_info env1 = decode_info env2"
  by (rule ext)+ (simp add: decode_info_def assms)

lemma alloc_step_cong_env:
  assumes "alloc_fields_eq env1 env2"
  shows "alloc_step env1 = alloc_step env2"
proof -
  have dts: "TE_Datatypes env1 = TE_Datatypes env2"
    using assms unfolding alloc_fields_eq_def by blast
  show ?thesis
    by (rule ext)
       (simp add: alloc_step_def dts decode_info_cong_env[OF dts]
                  datatype_summary_cong_env[OF assms])
qed

lemma datatype_alloc_info_cong_env:
  assumes "alloc_fields_eq env1 env2"
  shows "datatype_alloc_info env1 = datatype_alloc_info env2"
proof -
  have dts: "TE_Datatypes env1 = TE_Datatypes env2"
    using assms unfolding alloc_fields_eq_def by blast
  show ?thesis
    unfolding datatype_alloc_info_def datatype_alloc_atoms_def
              alloc_step_cong_env[OF assms] decode_info_cong_env[OF dts] ..
qed

lemma alloc_level_of_type_cong_env:
  assumes "alloc_fields_eq env1 env2"
  shows "alloc_level_of_type env1 ty = alloc_level_of_type env2 ty"
proof -
  have lv: "TE_AbstractAllocLevels env1 = TE_AbstractAllocLevels env2"
    using assms unfolding alloc_fields_eq_def by blast
  show ?thesis
    unfolding alloc_level_of_type_def alloc_level_of_type_info_def
              datatype_alloc_info_cong_env[OF assms] summarize_cong_env[OF lv] ..
qed

lemma alloc_level_compatible_cong_env:
  assumes "alloc_fields_eq env1 env2"
  shows "alloc_level_compatible env1 l ty = alloc_level_compatible env2 l ty"
  unfolding alloc_level_compatible_def alloc_level_of_type_cong_env[OF assms] ..


(* ========================================================================== *)
(* Monotonicity under a realization                                           *)
(* ========================================================================== *)

(* The env after a realization name := target, as far as the level
   computation is concerned: the datatype tables are unchanged except that the
   singleton substitution is applied to every constructor payload, and the
   level map agrees with the old one away from name (whose entry is dropped). *)
definition subst_env_rel :: "string \<Rightarrow> CoreType \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "subst_env_rel name target env env' \<longleftrightarrow>
     TE_Datatypes env' = TE_Datatypes env
     \<and> TE_DataCtorsByType env' = TE_DataCtorsByType env
     \<and> TE_DataCtors env'
         = fmmap (apply_subst_to_datactor (fmupd name target fmempty)) (TE_DataCtors env)
     \<and> (\<forall>v. v \<noteq> name \<longrightarrow>
           fmlookup (TE_AbstractAllocLevels env') v = fmlookup (TE_AbstractAllocLevels env) v)"

(* The capture-avoidance the realization needs: neither the realized name nor
   a variable of the target is a bound type parameter of any constructor. *)
definition realization_ctor_fresh :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> CoreType \<Rightarrow> bool" where
  "realization_ctor_fresh env name target \<longleftrightarrow>
     (\<forall>c dt tyvars p. fmlookup (TE_DataCtors env) c = Some (dt, tyvars, p) \<longrightarrow>
        name \<notin> set tyvars \<and> type_tyvars target \<inter> set tyvars = {})"

(* The structural half: under fixed datatype summaries, substituting the
   target for name can only lower a type's summary, provided the target's level
   (under those summaries) is compatible with name's declared level. *)
lemma summarize_singleton_subst_le:
  assumes s_def: "s = fmupd name target fmempty"
      and lv: "\<And>v. v \<noteq> name \<Longrightarrow>
                 fmlookup (TE_AbstractAllocLevels env') v = fmlookup (TE_AbstractAllocLevels env) v"
      and tgt: "alloc_level_le (fst (summarize env info [] target)) (declared_alloc_level env name)"
      and noself: "name \<notin> type_tyvars target"
      and p1: "name \<notin> set params"
      and p2: "type_tyvars target \<inter> set params = {}"
  shows "summary_le (summarize env' info params (apply_subst s ty)) (summarize env info params ty)"
proof (induction ty)
  case (CoreTy_Datatype dt args)
  have "list_all2 summary_le (map (summarize env' info params) (map (apply_subst s) args))
                             (map (summarize env info params) args)"
    using CoreTy_Datatype.IH by (auto simp: list_all2_conv_all_nth)
  then have "summary_le
      (apply_summary (length params) (info dt) (map (summarize env' info params) (map (apply_subst s) args)))
      (apply_summary (length params) (info dt) (map (summarize env info params) args))"
    by (rule apply_summary_mono[OF summary_le_refl])
  then show ?case by simp
next
  case (CoreTy_Record flds)
  let ?flds' = "map (\<lambda>(nm, ty). (nm, apply_subst s ty)) flds"
  have "list_all2 summary_le (map (\<lambda>fld. summarize env' info params (snd fld)) ?flds')
                             (map (\<lambda>fld. summarize env info params (snd fld)) flds)"
  proof -
    have elem: "summary_le (summarize env' info params (snd (?flds' ! i)))
                           (summarize env info params (snd (flds ! i)))"
      if i: "i < length flds" for i
    proof -
      have in2: "flds ! i \<in> set flds" using i by simp
      have "snd (?flds' ! i) = apply_subst s (snd (flds ! i))"
        using i by (simp add: case_prod_beta)
      then show ?thesis using CoreTy_Record.IH[OF in2 snds.intros] by simp
    qed
    show ?thesis
      using elem by (auto simp: list_all2_conv_all_nth)
  qed
  then have "summary_le
      (summary_max_list (length params) (map (\<lambda>fld. summarize env' info params (snd fld)) ?flds'))
      (summary_max_list (length params) (map (\<lambda>fld. summarize env info params (snd fld)) flds))"
    by (rule summary_max_list_mono)
  then show ?case by simp
next
  case (CoreTy_Array elemTy dims)
  then show ?case by simp
next
  case (CoreTy_Var v)
  show ?case
  proof (cases "v = name")
    case True
    have lhs: "apply_subst s (CoreTy_Var v) = target"
      using True by (simp add: s_def)
    have cong: "summarize env' info params target = summarize env info params target"
    proof (rule summarize_cong)
      show "\<And>d. d \<in> type_datatypes target \<Longrightarrow> info d = info d" by simp
    next
      fix u assume "u \<in> type_tyvars target"
      then have "u \<noteq> name" using noself by blast
      then show "fmlookup (TE_AbstractAllocLevels env') u = fmlookup (TE_AbstractAllocLevels env) u"
        by (rule lv)
    qed
    have fresh: "summarize env info params target
                   = summary_const (fst (summarize env info [] target)) (length params)"
      by (rule summarize_fresh_params[OF p2])
    have rhs: "summarize env info params (CoreTy_Var v)
                 = summary_const (declared_alloc_level env name) (length params)"
      using True p1 by (simp add: declared_alloc_level_def)
    show ?thesis
      unfolding lhs cong fresh rhs by (rule summary_const_le[OF tgt])
  next
    case False
    have lhs: "apply_subst s (CoreTy_Var v) = CoreTy_Var v"
      using False by (simp add: s_def)
    show ?thesis
      unfolding lhs using lv[OF False] by simp
  qed
qed simp_all

lemma ctor_summary_singleton_subst_le:
  assumes rel: "subst_env_rel name target env env'"
      and tgt: "alloc_level_le (fst (summarize env info [] target)) (declared_alloc_level env name)"
      and noself: "name \<notin> type_tyvars target"
      and fresh: "realization_ctor_fresh env name target"
  shows "summary_le (ctor_summary env' info arity c) (ctor_summary env info arity c)"
proof -
  let ?s = "fmupd name target fmempty"
  have dc: "TE_DataCtors env' = fmmap (apply_subst_to_datactor ?s) (TE_DataCtors env)"
   and lv: "\<And>v. v \<noteq> name \<Longrightarrow>
              fmlookup (TE_AbstractAllocLevels env') v = fmlookup (TE_AbstractAllocLevels env) v"
    using rel unfolding subst_env_rel_def by blast+
  show ?thesis
  proof (cases "fmlookup (TE_DataCtors env) c")
    case None
    then show ?thesis by (simp add: ctor_summary_def dc)
  next
    case (Some entry)
    obtain dt tyvars p where e: "entry = (dt, tyvars, p)"
      using prod_cases3 by blast
    have lk': "fmlookup (TE_DataCtors env') c = Some (dt, tyvars, apply_subst ?s p)"
      using Some e by (simp add: dc apply_subst_to_datactor_def)
    have f1: "name \<notin> set tyvars" and f2: "type_tyvars target \<inter> set tyvars = {}"
      using fresh Some e unfolding realization_ctor_fresh_def by blast+
    show ?thesis
    proof (cases "length tyvars = arity")
      case True
      have "summary_le (summarize env' info tyvars (apply_subst ?s p))
                       (summarize env info tyvars p)"
        by (rule summarize_singleton_subst_le[OF refl lv tgt noself f1 f2])
      then show ?thesis
        using Some e lk' True by (simp add: ctor_summary_def)
    next
      case False
      then show ?thesis
        using Some e lk' by (simp add: ctor_summary_def)
    qed
  qed
qed

lemma datatype_summary_singleton_subst_le:
  assumes rel: "subst_env_rel name target env env'"
      and tgt: "alloc_level_le (fst (summarize env info [] target)) (declared_alloc_level env name)"
      and noself: "name \<notin> type_tyvars target"
      and fresh: "realization_ctor_fresh env name target"
  shows "summary_le (datatype_summary env' info dt) (datatype_summary env info dt)"
proof -
  have dts: "TE_Datatypes env' = TE_Datatypes env"
   and bt: "TE_DataCtorsByType env' = TE_DataCtorsByType env"
    using rel unfolding subst_env_rel_def by blast+
  note cs = ctor_summary_singleton_subst_le[OF rel tgt noself fresh]
  show ?thesis
  proof (cases "fmlookup (TE_Datatypes env) dt")
    case None
    then show ?thesis by (simp add: datatype_summary_def dts)
  next
    case (Some arity)
    show ?thesis
    proof (cases "fmlookup (TE_DataCtorsByType env) dt")
      case None
      with Some show ?thesis by (simp add: datatype_summary_def dts bt)
    next
      case (Some ctors)
      show ?thesis
      proof (cases ctors)
        case Nil
        with \<open>fmlookup (TE_Datatypes env) dt = Some arity\<close> Some show ?thesis
          by (simp add: datatype_summary_def dts bt)
      next
        case (Cons c cs')
        have tl: "list_all2 summary_le
                (map (\<lambda>c'. summary_compose Mode_Downgrade (ctor_summary env' info arity c')) cs')
                (map (\<lambda>c'. summary_compose Mode_Downgrade (ctor_summary env info arity c')) cs')"
          unfolding list_all2_conv_all_nth
          by (auto intro: summary_compose_mono cs)
        have "list_all2 summary_le
                (ctor_summary env' info arity c
                 # map (\<lambda>c'. summary_compose Mode_Downgrade (ctor_summary env' info arity c')) cs')
                (ctor_summary env info arity c
                 # map (\<lambda>c'. summary_compose Mode_Downgrade (ctor_summary env info arity c')) cs')"
          using tl cs by simp
        then have "summary_le
                (summary_max_list arity (ctor_summary env' info arity c
                 # map (\<lambda>c'. summary_compose Mode_Downgrade (ctor_summary env' info arity c')) cs'))
                (summary_max_list arity (ctor_summary env info arity c
                 # map (\<lambda>c'. summary_compose Mode_Downgrade (ctor_summary env info arity c')) cs'))"
          by (rule summary_max_list_mono)
        with \<open>fmlookup (TE_Datatypes env) dt = Some arity\<close> Some Cons show ?thesis
          by (simp add: datatype_summary_def dts bt)
      qed
    qed
  qed
qed

(* The fixpoint half: the datatype summaries of the substituted env are
   bounded by those of the old env. (The old fixpoint is a pre-fixpoint of the
   new operator, by the structural half at the old summaries.) *)
lemma datatype_alloc_info_singleton_subst_le:
  assumes rel: "subst_env_rel name target env env'"
      and tgt: "alloc_level_le (alloc_level_of_type env target) (declared_alloc_level env name)"
      and noself: "name \<notin> type_tyvars target"
      and fresh: "realization_ctor_fresh env name target"
  shows "summary_le (datatype_alloc_info env' dt) (datatype_alloc_info env dt)"
proof -
  have dts: "TE_Datatypes env' = TE_Datatypes env"
    using rel unfolding subst_env_rel_def by blast
  have dec: "decode_info env' = decode_info env"
    by (rule decode_info_cong_env[OF dts])
  have tgt': "alloc_level_le (fst (summarize env (decode_info env (datatype_alloc_atoms env)) [] target))
                             (declared_alloc_level env name)"
    using tgt unfolding alloc_level_of_type_def alloc_level_of_type_info_def datatype_alloc_info_def .
  have step: "alloc_step env' (datatype_alloc_atoms env) \<subseteq> alloc_step env (datatype_alloc_atoms env)"
    unfolding alloc_step_def dts dec
    by (intro UN_mono subset_refl encode_entry_mono
              datatype_summary_singleton_subst_le[OF rel tgt' noself fresh])
  have fx: "alloc_step env (datatype_alloc_atoms env) = datatype_alloc_atoms env"
    by (rule datatype_alloc_atoms_fixpoint)
  have sub: "lfp (alloc_step env') \<subseteq> lfp (alloc_step env)"
  proof (rule lfp_lowerbound)
    show "alloc_step env' (lfp (alloc_step env)) \<subseteq> lfp (alloc_step env)"
      using step fx unfolding datatype_alloc_atoms_lfp by simp
  qed
  have "summary_le (decode_info env' (lfp (alloc_step env')) dt)
                   (decode_info env' (lfp (alloc_step env)) dt)"
    by (rule decode_info_mono[OF sub])
  then show ?thesis
    unfolding datatype_alloc_info_def datatype_alloc_atoms_lfp dec .
qed

(* The theorem: a realization name := target of compatible level can only
   lower the level of any type, computed before and after. *)
lemma alloc_level_of_type_singleton_subst_le:
  assumes rel: "subst_env_rel name target env env'"
      and tgt: "alloc_level_le (alloc_level_of_type env target) (declared_alloc_level env name)"
      and noself: "name \<notin> type_tyvars target"
      and fresh: "realization_ctor_fresh env name target"
  shows "alloc_level_le (alloc_level_of_type env' (apply_subst (fmupd name target fmempty) ty))
                        (alloc_level_of_type env ty)"
proof -
  let ?ty' = "apply_subst (fmupd name target fmempty) ty"
  have lv: "\<And>v. v \<noteq> name \<Longrightarrow>
              fmlookup (TE_AbstractAllocLevels env') v = fmlookup (TE_AbstractAllocLevels env) v"
    using rel unfolding subst_env_rel_def by blast
  have info_le: "\<And>dt. summary_le (datatype_alloc_info env' dt) (datatype_alloc_info env dt)"
    by (rule datatype_alloc_info_singleton_subst_le[OF rel tgt noself fresh])
  have s1: "summary_le (summarize env' (datatype_alloc_info env') [] ?ty')
                       (summarize env' (datatype_alloc_info env) [] ?ty')"
    by (rule summarize_mono[OF info_le])
  have tgt': "alloc_level_le (fst (summarize env (datatype_alloc_info env) [] target))
                             (declared_alloc_level env name)"
    using tgt unfolding alloc_level_of_type_def alloc_level_of_type_info_def .
  have s2: "summary_le (summarize env' (datatype_alloc_info env) [] ?ty')
                       (summarize env (datatype_alloc_info env) [] ty)"
    by (rule summarize_singleton_subst_le[OF refl lv tgt' noself]) simp_all
  show ?thesis
    unfolding alloc_level_of_type_def alloc_level_of_type_info_def
    using summary_le_fst[OF s1] summary_le_fst[OF s2]
    by (rule alloc_level_le_trans)
qed


(* ========================================================================== *)
(* Locality: the level of a type reads only what it reaches                   *)
(* ========================================================================== *)

(* env2 agrees with env1 on everything env1's datatypes reach: for each
   datatype of env1 its arity, constructor list and constructor entries are the
   same in env2; and each payload of env1 mentions only datatypes of env1 and
   only free type variables whose level entries agree. *)
definition env_local_agree :: "CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "env_local_agree env1 env2 \<longleftrightarrow>
     (\<forall>dt. dt |\<in>| fmdom (TE_Datatypes env1) \<longrightarrow>
        fmlookup (TE_Datatypes env2) dt = fmlookup (TE_Datatypes env1) dt
        \<and> fmlookup (TE_DataCtorsByType env2) dt = fmlookup (TE_DataCtorsByType env1) dt
        \<and> (\<forall>cs c. fmlookup (TE_DataCtorsByType env1) dt = Some cs \<longrightarrow> c \<in> set cs \<longrightarrow>
             fmlookup (TE_DataCtors env2) c = fmlookup (TE_DataCtors env1) c))
     \<and> (\<forall>c dt tyvars p. fmlookup (TE_DataCtors env1) c = Some (dt, tyvars, p) \<longrightarrow>
          type_datatypes p \<subseteq> fset (fmdom (TE_Datatypes env1))
          \<and> (\<forall>v \<in> type_tyvars p. v \<notin> set tyvars \<longrightarrow>
               fmlookup (TE_AbstractAllocLevels env2) v = fmlookup (TE_AbstractAllocLevels env1) v))"

lemma env_local_agreeD:
  assumes "env_local_agree env1 env2"
      and "dt |\<in>| fmdom (TE_Datatypes env1)"
  shows "fmlookup (TE_Datatypes env2) dt = fmlookup (TE_Datatypes env1) dt"
    and "fmlookup (TE_DataCtorsByType env2) dt = fmlookup (TE_DataCtorsByType env1) dt"
  using assms unfolding env_local_agree_def by blast+

(* One round of the operator agrees on env1's datatypes, under summaries that
   agree there. *)
lemma datatype_summary_local:
  assumes agree: "env_local_agree env1 env2"
      and dt_in: "dt |\<in>| fmdom (TE_Datatypes env1)"
      and info: "\<And>d. d |\<in>| fmdom (TE_Datatypes env1) \<Longrightarrow> info2 d = info1 d"
  shows "datatype_summary env2 info2 dt = datatype_summary env1 info1 dt"
proof -
  note dts = env_local_agreeD(1)[OF agree dt_in]
  note bt = env_local_agreeD(2)[OF agree dt_in]
  have ctor: "ctor_summary env2 info2 arity c = ctor_summary env1 info1 arity c"
    if cs: "fmlookup (TE_DataCtorsByType env1) dt = Some cs" and c_in: "c \<in> set cs"
    for arity cs c
  proof -
    have lk: "fmlookup (TE_DataCtors env2) c = fmlookup (TE_DataCtors env1) c"
      using agree dt_in cs c_in unfolding env_local_agree_def by blast
    show ?thesis
    proof (cases "fmlookup (TE_DataCtors env1) c")
      case None
      then show ?thesis by (simp add: ctor_summary_def lk)
    next
      case (Some entry)
      obtain d tyvars p where e: "entry = (d, tyvars, p)"
        using prod_cases3 by blast
      have pd: "type_datatypes p \<subseteq> fset (fmdom (TE_Datatypes env1))"
       and plv: "\<And>v. v \<in> type_tyvars p \<Longrightarrow> v \<notin> set tyvars \<Longrightarrow>
                   fmlookup (TE_AbstractAllocLevels env2) v = fmlookup (TE_AbstractAllocLevels env1) v"
        using agree Some e unfolding env_local_agree_def by blast+
      have "summarize env2 info2 tyvars p = summarize env1 info1 tyvars p"
      proof (rule summarize_cong)
        fix d' assume "d' \<in> type_datatypes p"
        then have "d' |\<in>| fmdom (TE_Datatypes env1)" using pd by auto
        then show "info2 d' = info1 d'" by (rule info)
      next
        fix v assume "v \<in> type_tyvars p" "v \<notin> set tyvars"
        then show "fmlookup (TE_AbstractAllocLevels env2) v = fmlookup (TE_AbstractAllocLevels env1) v"
          by (rule plv)
      qed
      then show ?thesis using Some e by (simp add: ctor_summary_def lk)
    qed
  qed
  show ?thesis
  proof (cases "fmlookup (TE_Datatypes env1) dt")
    case None
    then show ?thesis using dt_in by (simp add: fmlookup_dom_iff)
  next
    case (Some arity)
    show ?thesis
    proof (cases "fmlookup (TE_DataCtorsByType env1) dt")
      case None
      with Some show ?thesis by (simp add: datatype_summary_def dts bt)
    next
      case (Some ctors)
      show ?thesis
      proof (cases ctors)
        case Nil
        with \<open>fmlookup (TE_Datatypes env1) dt = Some arity\<close> Some show ?thesis
          by (simp add: datatype_summary_def dts bt)
      next
        case (Cons c cs')
        have hd: "ctor_summary env2 info2 arity c = ctor_summary env1 info1 arity c"
          using ctor[OF Some] Cons by simp
        have tl: "map (\<lambda>c'. summary_compose Mode_Downgrade (ctor_summary env2 info2 arity c')) cs'
                    = map (\<lambda>c'. summary_compose Mode_Downgrade (ctor_summary env1 info1 arity c')) cs'"
          by (rule map_cong[OF refl]) (simp add: ctor[OF Some] Cons)
        from \<open>fmlookup (TE_Datatypes env1) dt = Some arity\<close> Some Cons show ?thesis
          by (simp add: datatype_summary_def dts bt hd tl)
      qed
    qed
  qed
qed

(* The fixpoints agree on env1's datatypes: env1's fixpoint is a pre-fixpoint
   of env2's operator (so it lies below env2's), and env2's fixpoint restricted
   to env1's names is a pre-fixpoint of env1's operator (so it lies below
   env1's). *)
lemma datatype_alloc_info_local:
  assumes agree: "env_local_agree env1 env2"
      and dt_in: "dt |\<in>| fmdom (TE_Datatypes env1)"
  shows "datatype_alloc_info env2 dt = datatype_alloc_info env1 dt"
proof -
  let ?D = "fmdom (TE_Datatypes env1)"
  let ?F1 = "alloc_step env1" and ?F2 = "alloc_step env2"
  let ?A1 = "lfp (alloc_step env1)" and ?A2 = "lfp (alloc_step env2)"
  have dts_eq: "\<And>d. d |\<in>| ?D \<Longrightarrow> fmlookup (TE_Datatypes env2) d = fmlookup (TE_Datatypes env1) d"
    by (rule env_local_agreeD(1)[OF agree])
  have in2: "\<And>d. d |\<in>| ?D \<Longrightarrow> d |\<in>| fmdom (TE_Datatypes env2)"
    by (metis dts_eq fmlookup_dom_iff)
  have ar: "\<And>d. d |\<in>| ?D \<Longrightarrow> the (fmlookup (TE_Datatypes env2) d) = the (fmlookup (TE_Datatypes env1) d)"
    by (simp add: dts_eq)
  have dec_agree: "\<And>B d. d |\<in>| ?D \<Longrightarrow> decode_info env2 B d = decode_info env1 B d"
    by (simp add: decode_info_def dts_eq)
  \<comment> \<open>One round of env1's operator is contained in one round of env2's.\<close>
  have F1_sub_F2: "?F1 B \<subseteq> ?F2 B" for B
  proof
    fix x assume "x \<in> ?F1 B"
    then obtain d where d_in: "d \<in> fset ?D"
        and x_in: "x \<in> set (encode_entry d (the (fmlookup (TE_Datatypes env1) d))
                                         (datatype_summary env1 (decode_info env1 B) d))"
      unfolding alloc_step_def by blast
    have d_in': "d |\<in>| ?D" using d_in by simp
    have eq: "datatype_summary env2 (decode_info env2 B) d
                = datatype_summary env1 (decode_info env1 B) d"
      by (simp add: agree d_in' datatype_summary_local dec_agree)
    show "x \<in> ?F2 B"
      unfolding alloc_step_def
    proof (rule UN_I)
      show "d \<in> fset (fmdom (TE_Datatypes env2))" using in2[OF d_in'] by simp
      show "x \<in> set (encode_entry d (the (fmlookup (TE_Datatypes env2) d))
                                  (datatype_summary env2 (decode_info env2 B) d))"
        unfolding eq ar[OF d_in'] using x_in .
    qed
  qed
  have A1_fix: "?F1 ?A1 = ?A1"
    by (rule lfp_unfold[OF alloc_step_mono, symmetric])
  have A2_fix: "?F2 ?A2 = ?A2"
    by (rule lfp_unfold[OF alloc_step_mono, symmetric])
  \<comment> \<open>env1's fixpoint lies below env2's.\<close>
  have sub1: "?A1 \<subseteq> ?A2"
  proof (rule lfp_lowerbound)
    have "?F1 ?A2 \<subseteq> ?F2 ?A2" by (rule F1_sub_F2)
    then show "?F1 ?A2 \<subseteq> ?A2" using A2_fix by simp
  qed
  \<comment> \<open>env2's fixpoint, on env1's names, lies below env1's.\<close>
  let ?S = "?A1 \<union> {a. atom_name a |\<notin>| ?D}"
  have sub2: "?A2 \<subseteq> ?S"
  proof (rule lfp_lowerbound)
    show "?F2 ?S \<subseteq> ?S"
    proof
      fix x assume "x \<in> ?F2 ?S"
      then obtain d where d2: "d \<in> fset (fmdom (TE_Datatypes env2))"
          and x_in: "x \<in> set (encode_entry d (the (fmlookup (TE_Datatypes env2) d))
                                           (datatype_summary env2 (decode_info env2 ?S) d))"
        unfolding alloc_step_def by blast
      have nm: "atom_name x = d" using encode_entry_name[OF x_in] .
      show "x \<in> ?S"
      proof (cases "d |\<in>| ?D")
        case False
        then show ?thesis using nm by simp
      next
        case True
        have dec_S: "\<And>d'. d' |\<in>| ?D \<Longrightarrow> decode_info env2 ?S d' = decode_info env1 ?A1 d'"
        proof -
          fix d' assume d': "d' |\<in>| ?D"
          have dec: "decode_entry ?S d' n = decode_entry ?A1 d' n" for n
            by (rule decode_entry_cong) (use d' in auto)
          show "decode_info env2 ?S d' = decode_info env1 ?A1 d'"
            unfolding decode_info_def dts_eq[OF d'] dec ..
        qed
        have eq: "datatype_summary env2 (decode_info env2 ?S) d
                    = datatype_summary env1 (decode_info env1 ?A1) d"
          by (rule datatype_summary_local[OF agree True dec_S])
        have "x \<in> ?F1 ?A1"
          unfolding alloc_step_def[of env1 ?A1]
        proof (rule UN_I)
          show "d \<in> fset ?D" using True by simp
          show "x \<in> set (encode_entry d (the (fmlookup (TE_Datatypes env1) d))
                                      (datatype_summary env1 (decode_info env1 ?A1) d))"
            using x_in unfolding eq ar[OF True] .
        qed
        then show ?thesis using A1_fix by blast
      qed
    qed
  qed
  \<comment> \<open>So the two fixpoints have the same atoms at every name of env1.\<close>
  have dec: "decode_entry ?A2 dt n = decode_entry ?A1 dt n" for n
  proof (rule decode_entry_cong)
    fix x assume nm: "atom_name x = dt"
    show "x \<in> ?A2 \<longleftrightarrow> x \<in> ?A1"
    proof
      assume "x \<in> ?A2"
      then have "x \<in> ?S" using sub2 by blast
      then show "x \<in> ?A1" using nm dt_in by auto
    next
      assume "x \<in> ?A1"
      then show "x \<in> ?A2" using sub1 by blast
    qed
  qed
  show ?thesis
    unfolding datatype_alloc_info_def datatype_alloc_atoms_lfp decode_info_def dts_eq[OF dt_in] dec ..
qed

(* The theorem: the level of a type that reaches only env1's datatypes, and
   whose free variables have the same level entries, is the same in env2. *)
lemma alloc_level_of_type_local:
  assumes agree: "env_local_agree env1 env2"
      and tyd: "type_datatypes ty \<subseteq> fset (fmdom (TE_Datatypes env1))"
      and tyv: "\<And>v. v \<in> type_tyvars ty \<Longrightarrow>
                  fmlookup (TE_AbstractAllocLevels env2) v = fmlookup (TE_AbstractAllocLevels env1) v"
  shows "alloc_level_of_type env2 ty = alloc_level_of_type env1 ty"
  unfolding alloc_level_of_type_def alloc_level_of_type_info_def
proof (rule arg_cong[where f = fst], rule summarize_cong)
  fix d assume "d \<in> type_datatypes ty"
  then have "d |\<in>| fmdom (TE_Datatypes env1)" using tyd by auto
  then show "datatype_alloc_info env2 d = datatype_alloc_info env1 d"
    by (rule datatype_alloc_info_local[OF agree])
next
  fix v assume v_in: "v \<in> type_tyvars ty" and "v \<notin> set []"
  show "fmlookup (TE_AbstractAllocLevels env2) v = fmlookup (TE_AbstractAllocLevels env1) v"
    by (rule tyv[OF v_in])
qed

end
