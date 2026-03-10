theory CoreTypeProps
  imports CoreSyntax
begin

(* ========================================================================== *)
(* Type Properties *)
(* ========================================================================== *)

(* Check if a type is a runtime-compatible type (no MathInt/MathReal) *)
(* Note: Metavariables are considered runtime types, since they could be substituted
   as {} or i32 or some other runtime type *)
fun is_runtime_type :: "CoreType \<Rightarrow> bool" where
  "is_runtime_type (CoreTy_Name _ tyargs) = list_all is_runtime_type tyargs"
| "is_runtime_type CoreTy_Bool = True"
| "is_runtime_type (CoreTy_FiniteInt _ _) = True"
| "is_runtime_type CoreTy_MathInt = False"
| "is_runtime_type CoreTy_MathReal = False"
| "is_runtime_type (CoreTy_Record flds) = list_all is_runtime_type (map snd flds)"
| "is_runtime_type (CoreTy_Array elemTy dims) = is_runtime_type elemTy"
| "is_runtime_type (CoreTy_Meta _) = True"

(* Check if a type is a numeric type *)
fun is_numeric_type :: "CoreType \<Rightarrow> bool" where
  "is_numeric_type (CoreTy_FiniteInt _ _) = True"
| "is_numeric_type CoreTy_MathInt = True"
| "is_numeric_type CoreTy_MathReal = True"
| "is_numeric_type _ = False"

(* Check if a type is an integer type *)
fun is_integer_type :: "CoreType \<Rightarrow> bool" where
  "is_integer_type (CoreTy_FiniteInt _ _) = True"
| "is_integer_type CoreTy_MathInt = True"
| "is_integer_type _ = False"

(* Check if a type is a signed numeric type (signed finite int, MathInt, or MathReal) *)
fun is_signed_numeric_type :: "CoreType \<Rightarrow> bool" where
  "is_signed_numeric_type (CoreTy_FiniteInt Signed _) = True"
| "is_signed_numeric_type CoreTy_MathInt = True"
| "is_signed_numeric_type CoreTy_MathReal = True"
| "is_signed_numeric_type _ = False"

(* Check if a type is a signed integer type (signed finite int or MathInt) *)
fun is_signed_integer_type :: "CoreType \<Rightarrow> bool" where
  "is_signed_integer_type (CoreTy_FiniteInt Signed _) = True"
| "is_signed_integer_type CoreTy_MathInt = True"
| "is_signed_integer_type _ = False"

(* Check if a type is a finite integer type *)
fun is_finite_integer_type :: "CoreType \<Rightarrow> bool" where
  "is_finite_integer_type (CoreTy_FiniteInt _ _) = True"
| "is_finite_integer_type _ = False"

(* Check if a type is ground (no metavars) *)
fun is_ground :: "CoreType \<Rightarrow> bool" where
  "is_ground (CoreTy_Name _ tyargs) = list_all is_ground tyargs"
| "is_ground CoreTy_Bool = True"
| "is_ground (CoreTy_FiniteInt _ _) = True"
| "is_ground CoreTy_MathInt = True"
| "is_ground CoreTy_MathReal = True"
| "is_ground (CoreTy_Record flds) = list_all is_ground (map snd flds)"
| "is_ground (CoreTy_Array elemTy dims) = is_ground elemTy"
| "is_ground (CoreTy_Meta _) = False"

(* Collect all metavariables in a type *)
fun type_metavars :: "CoreType \<Rightarrow> nat set" where
  "type_metavars (CoreTy_Name _ tyargs) = \<Union>(set (map type_metavars tyargs))"
| "type_metavars CoreTy_Bool = {}"
| "type_metavars (CoreTy_FiniteInt _ _) = {}"
| "type_metavars CoreTy_MathInt = {}"
| "type_metavars CoreTy_MathReal = {}"
| "type_metavars (CoreTy_Record flds) = \<Union>(set (map (type_metavars \<circ> snd) flds))"
| "type_metavars (CoreTy_Array elemTy dims) = type_metavars elemTy"
| "type_metavars (CoreTy_Meta n) = {n}"

(* Collect all metavariables in a list of types *)
definition list_metavars :: "CoreType list \<Rightarrow> nat set" where
  "list_metavars tys = \<Union>(set (map type_metavars tys))"

(* Check if metavariable n occurs in type ty *)
definition occurs :: "nat \<Rightarrow> CoreType \<Rightarrow> bool" where
  "occurs n ty = (n \<in> type_metavars ty)"


(* ========================================================================== *)
(* Lemmas about type properties *)
(* ========================================================================== *)

(* Signed and finite integer types are integer types *)
lemma signed_integer_type_is_integer_type:
  "is_signed_integer_type ty \<Longrightarrow> is_integer_type ty"
  by (cases ty) auto

lemma finite_integer_type_is_integer_type:
  "is_finite_integer_type ty \<Longrightarrow> is_integer_type ty"
  by (cases ty) auto

(* Integer types are either FiniteInt or MathInt *)
lemma is_integer_type_cases:
  assumes "is_integer_type ty"
  obtains (FiniteInt) sign bits where "ty = CoreTy_FiniteInt sign bits"
        | (MathInt) "ty = CoreTy_MathInt"
  using assms by (cases ty) auto

(* Integer types are ground *)
lemma integer_type_is_ground:
  "is_integer_type ty \<Longrightarrow> is_ground ty"
  by (cases ty) auto

(* Metavariables in a type are finite *)
lemma finite_type_metavars: "finite (type_metavars ty)"
  by (induct ty) auto

(* Metavariables in a list of types are finite *)
lemma finite_list_metavars: "finite (list_metavars tys)"
  using list_metavars_def finite_type_metavars by auto

(* A type is ground iff it has no metavars *)
lemma is_ground_no_metavars:
  "is_ground ty \<longleftrightarrow> type_metavars ty = {}"
  by (induct ty) (auto simp: list_all_iff)

(* A list of metavariables satisfies list_all is_runtime_type *)
lemma list_all_meta_is_runtime:
  "list_all is_runtime_type (map CoreTy_Meta ns)"
  by (simp add: list_all_iff)


(* ========================================================================== *)
(* Binary operator classification *)
(* ========================================================================== *)

(* Arithmetic: +, -, *, / - work on any numeric type *)
fun is_arithmetic_binop :: "CoreBinop \<Rightarrow> bool" where
  "is_arithmetic_binop CoreBinop_Add = True"
| "is_arithmetic_binop CoreBinop_Subtract = True"
| "is_arithmetic_binop CoreBinop_Multiply = True"
| "is_arithmetic_binop CoreBinop_Divide = True"
| "is_arithmetic_binop _ = False"

(* Modulo: works on integer types only (not real) *)
fun is_modulo_binop :: "CoreBinop \<Rightarrow> bool" where
  "is_modulo_binop CoreBinop_Modulo = True"
| "is_modulo_binop _ = False"

(* Bitwise (non-shift): &, |, ^ - work on finite ints, require same type *)
fun is_bitwise_binop :: "CoreBinop \<Rightarrow> bool" where
  "is_bitwise_binop CoreBinop_BitAnd = True"
| "is_bitwise_binop CoreBinop_BitOr = True"
| "is_bitwise_binop CoreBinop_BitXor = True"
| "is_bitwise_binop _ = False"

(* Shift: <<, >> - work on finite ints, operands can have different types *)
fun is_shift_binop :: "CoreBinop \<Rightarrow> bool" where
  "is_shift_binop CoreBinop_ShiftLeft = True"
| "is_shift_binop CoreBinop_ShiftRight = True"
| "is_shift_binop _ = False"

(* Ordering: <, <=, >, >= - work on numeric types, result is bool *)
fun is_ordering_binop :: "CoreBinop \<Rightarrow> bool" where
  "is_ordering_binop CoreBinop_Less = True"
| "is_ordering_binop CoreBinop_LessEqual = True"
| "is_ordering_binop CoreBinop_Greater = True"
| "is_ordering_binop CoreBinop_GreaterEqual = True"
| "is_ordering_binop _ = False"

(* Equality/inequality: ==, != - work on any type (ghost) or bool/numeric (non-ghost) *)
fun is_eq_neq_binop :: "CoreBinop \<Rightarrow> bool" where
  "is_eq_neq_binop CoreBinop_Equal = True"
| "is_eq_neq_binop CoreBinop_NotEqual = True"
| "is_eq_neq_binop _ = False"

(* Logical: &&, ||, ==> - work on booleans only *)
fun is_logical_binop :: "CoreBinop \<Rightarrow> bool" where
  "is_logical_binop CoreBinop_And = True"
| "is_logical_binop CoreBinop_Or = True"
| "is_logical_binop CoreBinop_Implies = True"
| "is_logical_binop _ = False"

end
