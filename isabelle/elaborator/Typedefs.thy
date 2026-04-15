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

end
