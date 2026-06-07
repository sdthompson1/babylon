theory ElabEnv
  imports "../core/CoreKindcheck" "../core/ExtendEnvWithTyvars" 
    "../util/NatToString" "HOL-Library.Finite_Map" 
begin

(* This maps a typedef name to a list of type parameters (distinct tyvars)
   and a target type *)
type_synonym Typedefs = "(string, nat list \<times> CoreType) fmap"

(* Typedefs are well-formed if:
   - All type variable lists are distinct
   - The target types are well-kinded
   - The tyvars in the target types are a subset of the stated nat list *)
definition typedefs_well_formed :: "CoreTyEnv \<Rightarrow> Typedefs \<Rightarrow> bool" where
  "typedefs_well_formed env typedefs =
    (\<forall>name tyvars targetTy.
      fmlookup typedefs name = Some (tyvars, targetTy) \<longrightarrow>
        distinct tyvars \<and>
        is_well_kinded env targetTy \<and>
        type_tyvars targetTy \<subseteq> set tyvars)"

(* The elaborator environment extends the core type environment with
   information that only the elaborator needs:
   - Babylon-level typedefs (resolved to their underlying types before entering Core)
   - The Babylon-level arity of each data constructor (Core always has a single payload;
     the arity tells us how to decompose/construct it)
   - The set of function names that were declared void at the Babylon level.
     (In Core, these are represented as functions returning CoreTy_Record [] (unit),
     but they cannot be called in term position, only statement position.)
   - Whether the function currently being elaborated was declared void at the
     Babylon level. (Used to decide whether a bare `return;` is legal.) *)
record ElabEnv =
  EE_Typedefs :: Typedefs
  EE_DataCtorArity :: "(string, nat) fmap"
  EE_VoidFunctions :: "string fset"
  EE_CurrentFunctionVoid :: bool

(* The arity of a data constructor is consistent with the Core payload type:
   * Arity 0: payload type is CoreTy_Record [] (unit)
   * Arity 1: any payload type (single argument)
   * Arity n >= 2: payload type is a tuple record with n fields *)
definition data_ctor_arity_consistent :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> nat \<Rightarrow> bool" where
  "data_ctor_arity_consistent env name arity =
    (\<exists>dtName tyvars payloadTy.
       fmlookup (TE_DataCtors env) name = Some (dtName, tyvars, payloadTy)
     \<and> (arity = 0 \<longrightarrow> payloadTy = CoreTy_Record [])
     \<and> (arity \<ge> 2 \<longrightarrow> (\<exists>fieldTys. payloadTy = CoreTy_Record (zip (tuple_field_names arity) fieldTys)
                                 \<and> length fieldTys = arity)))"

(* Well-formedness of the elaborator environment:
   - Typedefs are well-formed
   - Every data constructor arity entry is consistent with TE_DataCtors
   - If the current function is void then its Core return type is unit *)
definition elabenv_well_formed :: "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> bool" where
  "elabenv_well_formed env ee =
    (typedefs_well_formed env (EE_Typedefs ee)
   \<and> (\<forall>name arity. fmlookup (EE_DataCtorArity ee) name = Some arity \<longrightarrow>
        data_ctor_arity_consistent env name arity)
   \<and> (EE_CurrentFunctionVoid ee \<longrightarrow> TE_ReturnType env = CoreTy_Record []))"


(* elabenv_well_formed depends on env only through TE_TypeVars, TE_Datatypes,
   TE_DataCtors (the first two via is_well_kinded in typedefs_well_formed, the third
   in data_ctor_arity_consistent) and TE_ReturnType (in the void clause). Any two
   envs agreeing on those four fields are equally well-formed. In particular the
   local-variable / proof-field updates that statement elaboration performs
   (TE_LocalVars / TE_GhostLocals / TE_ConstLocals / TE_ProofGoal / TE_ProofTopLevel)
   leave all four fields - hence elabenv_well_formed - unchanged. *)
lemma elabenv_well_formed_cong_env:
  assumes "TE_TypeVars env' = TE_TypeVars env"
    and "TE_Datatypes env' = TE_Datatypes env"
    and "TE_DataCtors env' = TE_DataCtors env"
    and "TE_ReturnType env' = TE_ReturnType env"
  shows "elabenv_well_formed env' elabEnv = elabenv_well_formed env elabEnv"
proof -
  have wk_cong: "\<And>ty. is_well_kinded env' ty = is_well_kinded env ty"
    using is_well_kinded_cong_env[OF assms(1,2)] by blast
  show ?thesis
    unfolding elabenv_well_formed_def typedefs_well_formed_def
              data_ctor_arity_consistent_def
    using wk_cong assms(3,4) by simp
qed

(* elabenv_well_formed is preserved under extend_env_with_tyvars: it depends on env
   only through TE_DataCtors (in data_ctor_arity_consistent — unchanged) and
   is_well_kinded (in typedefs_well_formed — preserved by adding tyvars). *)
lemma elabenv_well_formed_extend_env_with_tyvars:
  assumes "elabenv_well_formed env elabEnv"
  shows "elabenv_well_formed (extend_env_with_tyvars env ghost lo hi) elabEnv"
proof -
  let ?env' = "extend_env_with_tyvars env ghost lo hi"
  have td_eq: "TE_Datatypes ?env' = TE_Datatypes env"
    unfolding extend_env_with_tyvars_def by simp
  have dc_eq: "TE_DataCtors ?env' = TE_DataCtors env"
    unfolding extend_env_with_tyvars_def by simp
  have rt_eq: "TE_ReturnType ?env' = TE_ReturnType env"
    unfolding extend_env_with_tyvars_def by simp
  have void_clause: "EE_CurrentFunctionVoid elabEnv \<longrightarrow> TE_ReturnType ?env' = CoreTy_Record []"
    using assms rt_eq unfolding elabenv_well_formed_def by simp
  have td_wf: "typedefs_well_formed ?env' (EE_Typedefs elabEnv)"
  proof -
    have "\<forall>name tyvars targetTy.
            fmlookup (EE_Typedefs elabEnv) name = Some (tyvars, targetTy) \<longrightarrow>
              distinct tyvars \<and>
              is_well_kinded ?env' targetTy \<and>
              type_tyvars targetTy \<subseteq> set tyvars"
    proof clarify
      fix name tyvars targetTy
      assume look: "fmlookup (EE_Typedefs elabEnv) name = Some (tyvars, targetTy)"
      from assms have orig: "typedefs_well_formed env (EE_Typedefs elabEnv)"
        unfolding elabenv_well_formed_def by simp
      from orig look have
        d: "distinct tyvars" and
        wk: "is_well_kinded env targetTy" and
        sub: "type_tyvars targetTy \<subseteq> set tyvars"
        unfolding typedefs_well_formed_def by auto
      have wk': "is_well_kinded ?env' targetTy"
        by (metis extend_env_with_tyvars_empty is_well_kinded_extend_env_with_tyvars_mono
            linorder_le_cases wk)
      show "distinct tyvars \<and>
            is_well_kinded ?env' targetTy \<and>
            type_tyvars targetTy \<subseteq> set tyvars"
        using d wk' sub by blast
    qed
    thus ?thesis unfolding typedefs_well_formed_def by simp
  qed
  have ctor_arity:
    "\<forall>name arity. fmlookup (EE_DataCtorArity elabEnv) name = Some arity \<longrightarrow>
       data_ctor_arity_consistent ?env' name arity"
  proof clarify
    fix name arity
    assume look: "fmlookup (EE_DataCtorArity elabEnv) name = Some arity"
    from assms look have "data_ctor_arity_consistent env name arity"
      unfolding elabenv_well_formed_def by simp
    thus "data_ctor_arity_consistent ?env' name arity"
      unfolding data_ctor_arity_consistent_def using dc_eq by simp
  qed
  show ?thesis
    unfolding elabenv_well_formed_def
    using td_wf ctor_arity void_clause by simp
qed

end
