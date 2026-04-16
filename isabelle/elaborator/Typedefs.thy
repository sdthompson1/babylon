theory Typedefs
  imports "../core/CoreKindcheck" "HOL-Library.Finite_Map"
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
   - The set of nullary data constructor names (Core doesn't track this) *)
record ElabEnv =
  EE_Typedefs :: Typedefs
  EE_NullaryDataCtors :: "string fset"

(* Well-formedness of the elaborator environment:
   - Typedefs are well-formed
   - Every nullary data constructor name actually exists in TE_DataCtors
     with payload type CoreTy_Record [] (the unit type) *)
definition elabenv_well_formed :: "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> bool" where
  "elabenv_well_formed env ee =
    (typedefs_well_formed env (EE_Typedefs ee)
   \<and> (\<forall>name. name |\<in>| EE_NullaryDataCtors ee \<longrightarrow>
        (\<exists>dtName tyvars. fmlookup (TE_DataCtors env) name
                         = Some (dtName, tyvars, CoreTy_Record []))))"

end
