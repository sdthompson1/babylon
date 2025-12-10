theory Typedefs
  imports "../core/CoreKindcheck" "HOL-Library.Finite_Map"
begin

(* This maps a typedef name to a list of type parameters (distinct metavars)
   and a target type *)
type_synonym Typedefs = "(string, nat list \<times> CoreType) fmap"

(* Typedefs are well-formed if:
   - All metavar lists are distinct
   - The target types are well-kinded
   - The metavars in the target types are a subset of the stated nat list *)
definition typedefs_well_formed :: "CoreTyEnv \<Rightarrow> Typedefs \<Rightarrow> bool" where
  "typedefs_well_formed env typedefs =
    (\<forall>name metavars targetTy.
      fmlookup typedefs name = Some (metavars, targetTy) \<longrightarrow>
        distinct metavars \<and>
        is_well_kinded env targetTy \<and>
        type_metavars targetTy \<subseteq> set metavars)"

end
