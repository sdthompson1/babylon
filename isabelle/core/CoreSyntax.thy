theory CoreSyntax
  imports "../util/IntRange" "../util/Quantifier"
begin

(* Abstract syntax for the "Core" language *)

(* Array dimension *)
datatype CoreDimension =
  CoreDim_Unknown
  | CoreDim_Allocatable
  | CoreDim_Fixed int

(* Type *)
datatype CoreType =
  CoreTy_Name string "CoreType list"   (* Datatype or abstract/extern type *)
  | CoreTy_Bool
  | CoreTy_FiniteInt Signedness IntBits
  | CoreTy_MathInt
  | CoreTy_MathReal
  | CoreTy_Record "(string \<times> CoreType) list"
  | CoreTy_Array CoreType "CoreDimension list"
  | CoreTy_Meta nat   (* Metavariable for unification *)

(* Pattern *)
datatype CorePattern =
  CorePat_Bool bool
  | CorePat_Int int
  | CorePat_Variant string
  | CorePat_Wildcard

(* Unary operator *)
datatype CoreUnop =
  CoreUnop_Negate
  | CoreUnop_Complement
  | CoreUnop_Not

(* Binary operator *)
datatype CoreBinop =
  CoreBinop_Add
  | CoreBinop_Subtract
  | CoreBinop_Multiply
  | CoreBinop_Divide
  | CoreBinop_Modulo

  | CoreBinop_BitAnd
  | CoreBinop_BitOr
  | CoreBinop_BitXor
  | CoreBinop_ShiftLeft
  | CoreBinop_ShiftRight
  
  | CoreBinop_Equal
  | CoreBinop_NotEqual
  | CoreBinop_Less
  | CoreBinop_LessEqual
  | CoreBinop_Greater
  | CoreBinop_GreaterEqual
  
  | CoreBinop_And
  | CoreBinop_Or
  | CoreBinop_Implies

(* Term *)
datatype CoreTerm =
  CoreTm_LitBool bool
  | CoreTm_LitInt int
  | CoreTm_LitArray "CoreTerm list"  (* one-dimensional array *)
  | CoreTm_Var string
  | CoreTm_Cast CoreType CoreTerm
  | CoreTm_Unop CoreUnop CoreTerm
  | CoreTm_Binop CoreBinop CoreTerm CoreTerm
  | CoreTm_Let string CoreTerm CoreTerm
  | CoreTm_Quantifier Quantifier string CoreType CoreTerm
  | CoreTm_FunctionCall string "CoreType list" "CoreTerm list"
  | CoreTm_VariantCtor string "CoreType list" CoreTerm
  | CoreTm_Record "(string \<times> CoreTerm) list"
  | CoreTm_RecordProj CoreTerm string
  | CoreTm_VariantProj CoreTerm string  (* name of data ctor to get payload of *)
  | CoreTm_ArrayProj CoreTerm "CoreTerm list"
  | CoreTm_Match CoreTerm "(CorePattern \<times> CoreTerm) list"
  | CoreTm_Sizeof CoreTerm
  | CoreTm_Allocated CoreTerm
  | CoreTm_Old CoreTerm

fun is_lvalue :: "CoreTerm \<Rightarrow> bool" where
  "is_lvalue (CoreTm_Var _) = True"
| "is_lvalue (CoreTm_RecordProj tm _) = is_lvalue tm"
| "is_lvalue (CoreTm_VariantProj tm _) = is_lvalue tm"
| "is_lvalue (CoreTm_ArrayProj tm _) = is_lvalue tm"
| "is_lvalue _ = False"

datatype CoreStatement =
  CoreStmt_VarDecl GhostOrNot string VarOrRef CoreType CoreTerm
  | CoreStmt_Fix string CoreType
  | CoreStmt_Obtain string CoreType CoreTerm
  | CoreStmt_Use CoreTerm
  | CoreStmt_Assign GhostOrNot CoreTerm CoreTerm  (* lhs must be lvalue *)
  | CoreStmt_Swap GhostOrNot CoreTerm CoreTerm    (* both terms must be lvalues *)
  | CoreStmt_Return CoreTerm
  | CoreStmt_Assert CoreTerm "CoreStatement list"
  | CoreStmt_Assume CoreTerm
  | CoreStmt_While GhostOrNot CoreTerm "CoreTerm list" CoreTerm "CoreStatement list"  
         (* ghost flag, condition, invariants, decreases-term, loop body *)
  | CoreStmt_Match GhostOrNot CoreTerm "(CorePattern \<times> CoreStatement list) list"
  | CoreStmt_ShowHide ShowOrHide string

(* TODO: Decls, etc. *)

end
