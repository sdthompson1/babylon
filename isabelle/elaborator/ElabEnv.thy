theory ElabEnv
  imports "../core/CoreKindcheck" "HOL-Library.Finite_Map" "../util/NatToString"
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
     In Core, these are represented as functions returning CoreTy_Record [] (unit),
     but they must not be callable in term position — only in statement position. *)
record ElabEnv =
  EE_Typedefs :: Typedefs
  EE_DataCtorArity :: "(string, nat) fmap"
  EE_VoidFunctions :: "string fset"

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
   - Every data constructor arity entry is consistent with TE_DataCtors *)
definition elabenv_well_formed :: "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> bool" where
  "elabenv_well_formed env ee =
    (typedefs_well_formed env (EE_Typedefs ee)
   \<and> (\<forall>name arity. fmlookup (EE_DataCtorArity ee) name = Some arity \<longrightarrow>
        data_ctor_arity_consistent env name arity))"

end
