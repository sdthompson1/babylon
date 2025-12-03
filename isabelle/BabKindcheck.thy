theory BabKindcheck
  imports TypeEnv IntRange
begin

(* This file defines well-kindedness for types. We only have one kind, *, because
   all our type constructors are fully applied (see BabTy_Name). Therefore, we
   just need an is_well_kinded function. *)

(* Helper: check if a dimension is valid (not BabDim_Fixed, which is pre-elaboration) *)
fun is_valid_dimension :: "BabDimension \<Rightarrow> bool" where
  "is_valid_dimension BabDim_Unknown = True"
| "is_valid_dimension BabDim_Allocatable = True"
| "is_valid_dimension (BabDim_FixedInt _) = True"
| "is_valid_dimension (BabDim_Fixed _) = False"

(* Helper: classify dimensions into categories for uniformity checking *)
datatype DimCategory = DimCat_Unknown | DimCat_Allocatable | DimCat_FixedInt

fun dim_category :: "BabDimension \<Rightarrow> DimCategory option" where
  "dim_category BabDim_Unknown = Some DimCat_Unknown"
| "dim_category BabDim_Allocatable = Some DimCat_Allocatable"
| "dim_category (BabDim_FixedInt _) = Some DimCat_FixedInt"
| "dim_category (BabDim_Fixed _) = None"

(* Helper: check if all dimensions have the same category *)
fun dims_uniform :: "BabDimension list \<Rightarrow> bool" where
  "dims_uniform [] = True"
| "dims_uniform [d] = is_valid_dimension d"
| "dims_uniform (d1 # d2 # ds) =
    (case (dim_category d1, dim_category d2) of
      (Some c1, Some c2) \<Rightarrow> c1 = c2 \<and> dims_uniform (d2 # ds)
    | _ \<Rightarrow> False)"

(* Helper: check if a BabDim_FixedInt value is within uint64 range *)
fun dim_in_uint64_range :: "BabDimension \<Rightarrow> bool" where
  "dim_in_uint64_range (BabDim_FixedInt n) = int_in_range (int_range Unsigned IntBits_64) n"
| "dim_in_uint64_range _ = True"

(* Helper: check if all dimensions are within uint64 range *)
definition dims_in_range :: "BabDimension list \<Rightarrow> bool" where
  "dims_in_range dims \<equiv> list_all dim_in_uint64_range dims"

(* Check if array dimensions are well-kinded:
   - All dimensions must be Unknown, Allocatable, or FixedInt (no Fixed)
   - If multiple dimensions, they must all have the same category
   - All FixedInt dimensions must be within uint64 range *)
definition array_dims_well_kinded :: "BabDimension list \<Rightarrow> bool" where
  "array_dims_well_kinded dims \<equiv> dims_uniform dims \<and> dims_in_range dims"

fun is_well_kinded :: "BabTyEnv \<Rightarrow> BabType \<Rightarrow> bool" where
  "is_well_kinded env (BabTy_Name loc typeName argTypes) =
    (if typeName |\<in>| TE_TypeVars env then
       argTypes = []
     else
       (case fmlookup (TE_Datatypes env) typeName of
         Some dt \<Rightarrow> length argTypes = length (DD_TyArgs dt)
                    \<and> list_all (is_well_kinded env) argTypes
       | None \<Rightarrow> False))"

| "is_well_kinded env (BabTy_Bool loc) = True"
| "is_well_kinded env (BabTy_FiniteInt loc sign bits) = True"
| "is_well_kinded env (BabTy_MathInt loc) = True"
| "is_well_kinded env (BabTy_MathReal loc) = True"
| "is_well_kinded env (BabTy_Tuple loc tys) = list_all (is_well_kinded env) tys"
| "is_well_kinded env (BabTy_Record loc flds) = list_all (is_well_kinded env \<circ> snd) flds"
| "is_well_kinded env (BabTy_Array loc elemTy dims) =
    (is_well_kinded env elemTy \<and> array_dims_well_kinded dims)"
| "is_well_kinded env (BabTy_Meta n) = True"


(* Integer types are always well-kinded *)
lemma is_integer_type_well_kinded:
  assumes "is_integer_type ty"
  shows "is_well_kinded env ty"
using assms by (cases ty) auto

(* List of metavariables is always well-kinded *)
lemma list_all_is_well_kinded_meta:
  "list_all (is_well_kinded env) (map BabTy_Meta xs)"
  by (induction xs) simp_all

end
