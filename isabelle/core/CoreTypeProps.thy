theory CoreTypeProps
  imports RuntimeType
begin

(* ========================================================================== *)
(* Type Properties *)
(* ========================================================================== *)

(* Check if a type is complete. An incomplete type is one that mentions an array with
   a dimension of unknown size (T[]): values of such a type only exist as views onto
   storage owned by someone else, so they cannot be stored, assigned or swapped in
   executable code.
   An allocatable dimension (T[*]) is complete: the variable itself owns the storage.
   A type variable is complete because a type argument is always required to be a
   complete type, so a type variable can only ever stand for one. This makes the
   predicate purely syntactic (no env needed). *)
fun is_complete_type :: "CoreType \<Rightarrow> bool" where
  "is_complete_type (CoreTy_Datatype _ tyargs) = list_all is_complete_type tyargs"
| "is_complete_type CoreTy_Bool = True"
| "is_complete_type (CoreTy_FiniteInt _ _) = True"
| "is_complete_type CoreTy_MathInt = True"
| "is_complete_type CoreTy_MathReal = True"
| "is_complete_type (CoreTy_Record flds) = list_all is_complete_type (map snd flds)"
| "is_complete_type (CoreTy_Array elemTy dims) =
     (list_all (\<lambda>d. d \<noteq> CoreDim_Unknown) dims \<and> is_complete_type elemTy)"
| "is_complete_type (CoreTy_Var _) = True"
| "is_complete_type (CoreTy_Extern _ _) = True"

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

(* Integer types are numeric types *)
lemma integer_type_is_numeric_type:
  "is_integer_type ty \<Longrightarrow> is_numeric_type ty"
  by (cases ty) auto

(* Integer types are either FiniteInt or MathInt *)
lemma is_integer_type_cases:
  assumes "is_integer_type ty"
  obtains (FiniteInt) sign bits where "ty = CoreTy_FiniteInt sign bits"
        | (MathInt) "ty = CoreTy_MathInt"
  using assms by (cases ty) auto

(* Integer types have no free type variables *)
lemma integer_type_no_tyvars:
  "is_integer_type ty \<Longrightarrow> type_tyvars ty = {}"
  by (cases ty) auto

(* Numeric types have no free type variables *)
lemma numeric_type_no_tyvars:
  "is_numeric_type ty \<Longrightarrow> type_tyvars ty = {}"
  by (cases ty) auto

(* Numeric types are complete *)
lemma numeric_type_is_complete:
  "is_numeric_type ty \<Longrightarrow> is_complete_type ty"
  by (cases ty) auto

(* A list of type variables (as types) is always complete *)
lemma list_all_tyvar_is_complete [simp]:
  "list_all is_complete_type (map CoreTy_Var ns)"
  by (induction ns) auto

(* ========================================================================== *)
(* Term Properties *)
(* ========================================================================== *)

(* Like is_lvalue, but also checks that the base variable is writable.
   A variable is writable iff it is a non-const local. (Globals are always read-only.) *)
fun is_writable_lvalue :: "CoreTyEnv \<Rightarrow> CoreTerm \<Rightarrow> bool" where
  "is_writable_lvalue env (CoreTm_Var name) = tyenv_var_writable env name"
| "is_writable_lvalue env (CoreTm_RecordProj tm _) = is_writable_lvalue env tm"
| "is_writable_lvalue env (CoreTm_VariantProj tm _) = is_writable_lvalue env tm"
| "is_writable_lvalue env (CoreTm_ArrayProj tm _) = is_writable_lvalue env tm"
| "is_writable_lvalue env (CoreTm_Cast ty tm) = (is_array_type ty \<and> is_writable_lvalue env tm)"
| "is_writable_lvalue _ _ = False"

(* is_writable_lvalue depends on the environment only through TE_LocalVars and
   TE_ConstLocals (via tyenv_var_writable), so it is unaffected by adding type
   variables to the environment. *)
lemma is_writable_lvalue_irrelevant_tyvar [simp]:
  "is_writable_lvalue
     (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
            TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>) tm
   = is_writable_lvalue env tm"
  by (induction tm rule: is_writable_lvalue.induct)
     (auto simp: tyenv_var_writable_def)

(* Ghost-write discipline: in Ghost mode, writing to an lvalue is only allowed if
   the lvalue points to a Ghost variable. This enforces the rule that ghost code cannot
   write to non-ghost variables.
   (In NotGhost mode, this function always returns True. Instead, a separate check is made in
   the typechecker - references to Ghost vars won't even typecheck in NotGhost mode.) *)
definition ghost_lvalue_ok :: "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> CoreTerm \<Rightarrow> bool" where
  "ghost_lvalue_ok env ghost tm =
     (ghost = Ghost \<longrightarrow> (case lvalue_base_name tm of
                           Some name \<Rightarrow> tyenv_var_ghost env name
                         | None \<Rightarrow> False))"

lemma ghost_lvalue_ok_NotGhost [simp]:
  "ghost_lvalue_ok env NotGhost tm"
  by (simp add: ghost_lvalue_ok_def)

(* ghost_lvalue_ok only looks at the base variable name. *)
lemma ghost_lvalue_ok_base_name_cong:
  "lvalue_base_name tm1 = lvalue_base_name tm2
     \<Longrightarrow> ghost_lvalue_ok env ghost tm1 = ghost_lvalue_ok env ghost tm2"
  by (simp add: ghost_lvalue_ok_def)

(* ghost_lvalue_ok depends on the environment only through TE_LocalVars
   and TE_GhostLocals (via tyenv_var_ghost). *)
lemma ghost_lvalue_ok_cong_env:
  assumes "TE_LocalVars env1 = TE_LocalVars env2"
    and "TE_GhostLocals env1 = TE_GhostLocals env2"
  shows "ghost_lvalue_ok env1 ghost tm = ghost_lvalue_ok env2 ghost tm"
  using assms
  by (simp add: ghost_lvalue_ok_def tyenv_var_ghost_def split: option.splits)

lemma ghost_lvalue_ok_irrelevant_tyvar [simp]:
  "ghost_lvalue_ok
     (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
            TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>) ghost tm
   = ghost_lvalue_ok env ghost tm"
  by (rule ghost_lvalue_ok_cong_env) simp_all


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

(* Every CoreBinop falls into exactly one category *)
lemma binop_category_exhaustive:
  "is_arithmetic_binop op \<or> is_modulo_binop op \<or> is_bitwise_binop op \<or>
   is_shift_binop op \<or> is_ordering_binop op \<or> is_eq_neq_binop op \<or>
   is_logical_binop op"
  by (cases op) auto

(* The binop categories are disjoint: no operator belongs to more than one. *)
lemma binop_categories_disjoint:
  "is_arithmetic_binop op \<Longrightarrow> \<not> is_modulo_binop op"
  "is_arithmetic_binop op \<Longrightarrow> \<not> is_bitwise_binop op"
  "is_arithmetic_binop op \<Longrightarrow> \<not> is_shift_binop op"
  "is_arithmetic_binop op \<Longrightarrow> \<not> is_ordering_binop op"
  "is_arithmetic_binop op \<Longrightarrow> \<not> is_eq_neq_binop op"
  "is_arithmetic_binop op \<Longrightarrow> \<not> is_logical_binop op"
  "is_modulo_binop op \<Longrightarrow> \<not> is_arithmetic_binop op"
  "is_modulo_binop op \<Longrightarrow> \<not> is_bitwise_binop op"
  "is_modulo_binop op \<Longrightarrow> \<not> is_shift_binop op"
  "is_modulo_binop op \<Longrightarrow> \<not> is_ordering_binop op"
  "is_modulo_binop op \<Longrightarrow> \<not> is_eq_neq_binop op"
  "is_modulo_binop op \<Longrightarrow> \<not> is_logical_binop op"
  "is_bitwise_binop op \<Longrightarrow> \<not> is_arithmetic_binop op"
  "is_bitwise_binop op \<Longrightarrow> \<not> is_modulo_binop op"
  "is_bitwise_binop op \<Longrightarrow> \<not> is_shift_binop op"
  "is_bitwise_binop op \<Longrightarrow> \<not> is_ordering_binop op"
  "is_bitwise_binop op \<Longrightarrow> \<not> is_eq_neq_binop op"
  "is_bitwise_binop op \<Longrightarrow> \<not> is_logical_binop op"
  "is_shift_binop op \<Longrightarrow> \<not> is_arithmetic_binop op"
  "is_shift_binop op \<Longrightarrow> \<not> is_modulo_binop op"
  "is_shift_binop op \<Longrightarrow> \<not> is_bitwise_binop op"
  "is_shift_binop op \<Longrightarrow> \<not> is_ordering_binop op"
  "is_shift_binop op \<Longrightarrow> \<not> is_eq_neq_binop op"
  "is_shift_binop op \<Longrightarrow> \<not> is_logical_binop op"
  "is_ordering_binop op \<Longrightarrow> \<not> is_arithmetic_binop op"
  "is_ordering_binop op \<Longrightarrow> \<not> is_modulo_binop op"
  "is_ordering_binop op \<Longrightarrow> \<not> is_bitwise_binop op"
  "is_ordering_binop op \<Longrightarrow> \<not> is_shift_binop op"
  "is_ordering_binop op \<Longrightarrow> \<not> is_eq_neq_binop op"
  "is_ordering_binop op \<Longrightarrow> \<not> is_logical_binop op"
  "is_eq_neq_binop op \<Longrightarrow> \<not> is_arithmetic_binop op"
  "is_eq_neq_binop op \<Longrightarrow> \<not> is_modulo_binop op"
  "is_eq_neq_binop op \<Longrightarrow> \<not> is_bitwise_binop op"
  "is_eq_neq_binop op \<Longrightarrow> \<not> is_shift_binop op"
  "is_eq_neq_binop op \<Longrightarrow> \<not> is_ordering_binop op"
  "is_eq_neq_binop op \<Longrightarrow> \<not> is_logical_binop op"
  "is_logical_binop op \<Longrightarrow> \<not> is_arithmetic_binop op"
  "is_logical_binop op \<Longrightarrow> \<not> is_modulo_binop op"
  "is_logical_binop op \<Longrightarrow> \<not> is_bitwise_binop op"
  "is_logical_binop op \<Longrightarrow> \<not> is_shift_binop op"
  "is_logical_binop op \<Longrightarrow> \<not> is_ordering_binop op"
  "is_logical_binop op \<Longrightarrow> \<not> is_eq_neq_binop op"
  by (cases op; simp)+

end
