theory ElabEnv
  imports "../core/CoreKindcheck" ExtendEnvWithTyvars
    "../util/NatToString" "HOL-Library.Finite_Map" 
begin

(* ========================================================================== *)
(* ElabEnv type definitions *)
(* ========================================================================== *)

(* This maps a typedef name to a list of type parameters (distinct tyvars)
   and a target type *)
type_synonym Typedefs = "(string, string list \<times> CoreType) fmap"

(* The elaborator environment extends the core type environment with
   information that only the elaborator needs:

   - Babylon-level typedefs (resolved to their underlying types before entering Core).

   - The set of "nullary" data constructor names (those with no payload).
     (Core doesn't have nullary constructors -- we use a constructor with a
     CoreTy_Record [] (unit) payload, instead -- but in Babylon, there is a distinction
     between a genuinely nullary constructor, `Foo`, and a constructor with a unit payload,
     `Foo{}`.)

   - The set of function names that were declared void at the Babylon level.
     (In Core, these are represented as functions returning CoreTy_Record [] (unit),
     but in the Babylon syntax, they cannot be called in term position, only statement
     position.)

   - Whether the function currently being elaborated was declared void at the
     Babylon level. (Used to decide whether a bare `return;` is legal.) 
*)
record ElabEnv =
  EE_Typedefs :: Typedefs
  EE_NullaryDataCtors :: "string fset"
  EE_VoidFunctions :: "string fset"
  EE_CurrentFunctionVoid :: bool


(* ========================================================================== *)
(* ElabEnv well-formedness definitions *)
(* ========================================================================== *)

(* Typedefs are well-formed if:
   - All type variable lists are distinct
   - The target types are well-kinded, when the typedef's type parameters are
     added to the env as type variables. *)
definition typedefs_well_formed :: "CoreTyEnv \<Rightarrow> Typedefs \<Rightarrow> bool" where
  "typedefs_well_formed env typedefs =
    (\<forall>name tyvars targetTy.
      fmlookup typedefs name = Some (tyvars, targetTy) \<longrightarrow>
        distinct tyvars \<and>
        is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list tyvars \<rparr>)
                       targetTy)"

(* EE_NullaryDataCtors is consistent if: every nullary data constructor has a Core
   payload type of CoreTy_Record [] (unit). *)
definition nullary_data_ctors_consistent :: "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> bool" where
  "nullary_data_ctors_consistent env ee =
    (\<forall>name. name |\<in>| EE_NullaryDataCtors ee \<longrightarrow>
       (\<exists>dtName tyvars.
          fmlookup (TE_DataCtors env) name = Some (dtName, tyvars, CoreTy_Record [])))"

(* Well-formedness of the elaborator environment:
   - Typedefs are well-formed
   - Every nullary data constructor has a unit payload type in TE_DataCtors
   - If the current function is void then its Core return type is unit *)
definition elabenv_well_formed :: "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> bool" where
  "elabenv_well_formed env ee =
    (typedefs_well_formed env (EE_Typedefs ee)
   \<and> nullary_data_ctors_consistent env ee
   \<and> (EE_CurrentFunctionVoid ee \<longrightarrow> TE_ReturnType env = CoreTy_Record []))"


(* ========================================================================== *)
(* Properties *)
(* ========================================================================== *)

(* In a typedef, the target's type variables are among the entry's own parameters
   or the ambient type variables. *)
lemma typedefs_well_formed_tyvars_subset:
  assumes "typedefs_well_formed env typedefs"
      and "fmlookup typedefs name = Some (tyvars, targetTy)"
  shows "type_tyvars targetTy \<subseteq> set tyvars \<union> fset (TE_TypeVars env)"
proof -
  have "is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list tyvars \<rparr>)
                       targetTy"
    using assms unfolding typedefs_well_formed_def by blast
  from is_well_kinded_type_tyvars_subset[OF this]
  show ?thesis by (auto simp: fset_of_list_elem)
qed

(* elabenv_well_formed depends on env only through TE_TypeVars, TE_Datatypes,
   TE_DataCtors (the first two via is_well_kinded in typedefs_well_formed, the third
   in nullary_data_ctors_consistent) and TE_ReturnType (in the void clause). Any two
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
  have wk_cong: "\<And>tvs ty. is_well_kinded (env' \<lparr> TE_TypeVars := tvs \<rparr>) ty
                        = is_well_kinded (env \<lparr> TE_TypeVars := tvs \<rparr>) ty"
    by (rule is_well_kinded_cong_env) (simp_all add: assms(2))
  show ?thesis
    unfolding elabenv_well_formed_def typedefs_well_formed_def
              nullary_data_ctors_consistent_def
    using wk_cong assms(1,3,4) by simp
qed

(* elabenv_well_formed is preserved under extend_env_with_tyvars: it depends on env
   only through TE_DataCtors (in nullary_data_ctors_consistent — unchanged) and
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
              is_well_kinded
                (?env' \<lparr> TE_TypeVars := TE_TypeVars ?env' |\<union>| fset_of_list tyvars \<rparr>)
                targetTy"
    proof clarify
      fix name tyvars targetTy
      assume look: "fmlookup (EE_Typedefs elabEnv) name = Some (tyvars, targetTy)"
      from assms have orig: "typedefs_well_formed env (EE_Typedefs elabEnv)"
        unfolding elabenv_well_formed_def by simp
      from orig look have
        d: "distinct tyvars" and
        wk: "is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list tyvars \<rparr>)
                            targetTy"
        unfolding typedefs_well_formed_def by auto
      \<comment> \<open>Widen with the metavariable interval; the two extended envs agree on
          TE_TypeVars (up to reassociation) and TE_Datatypes.\<close>
      have tv_eq: "TE_TypeVars ?env' |\<union>| fset_of_list tyvars
                 = (TE_TypeVars env |\<union>| fset_of_list tyvars) |\<union>| mv_fset lo hi"
        unfolding extend_env_with_tyvars_def
        by (rule fset_eqI) auto
      have step: "is_well_kinded
             ((env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list tyvars \<rparr>)
                \<lparr> TE_TypeVars := (TE_TypeVars env |\<union>| fset_of_list tyvars) |\<union>| mv_fset lo hi,
                  TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| {||} \<rparr>) targetTy"
        using is_well_kinded_extend_tyvars[OF wk, where extraTV = "mv_fset lo hi"
                                                   and extraRT = "{||}"]
        by simp
      have wk': "is_well_kinded
             (?env' \<lparr> TE_TypeVars := TE_TypeVars ?env' |\<union>| fset_of_list tyvars \<rparr>) targetTy"
      proof -
        have "is_well_kinded
                (?env' \<lparr> TE_TypeVars := TE_TypeVars ?env' |\<union>| fset_of_list tyvars \<rparr>) targetTy
            = is_well_kinded
                ((env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list tyvars \<rparr>)
                   \<lparr> TE_TypeVars := (TE_TypeVars env |\<union>| fset_of_list tyvars) |\<union>| mv_fset lo hi,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| {||} \<rparr>) targetTy"
          by (rule is_well_kinded_cong_env)
             (simp add: tv_eq, simp add: extend_env_with_tyvars_def)
        thus ?thesis using step by simp
      qed
      show "distinct tyvars \<and>
            is_well_kinded
              (?env' \<lparr> TE_TypeVars := TE_TypeVars ?env' |\<union>| fset_of_list tyvars \<rparr>)
              targetTy"
        using d wk' by blast
    qed
    thus ?thesis unfolding typedefs_well_formed_def by simp
  qed
  have nullary_ctors: "nullary_data_ctors_consistent ?env' elabEnv"
    using assms dc_eq
    unfolding elabenv_well_formed_def nullary_data_ctors_consistent_def by simp
  show ?thesis
    unfolding elabenv_well_formed_def
    using td_wf nullary_ctors void_clause by simp
qed

end
