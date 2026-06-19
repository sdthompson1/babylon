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
  CoreTy_Datatype string "CoreType list"   (* Datatype name with type arguments *)
  | CoreTy_Bool
  | CoreTy_FiniteInt Signedness IntBits
  | CoreTy_MathInt
  | CoreTy_MathReal
  | CoreTy_Record "(string \<times> CoreType) list"
  | CoreTy_Array CoreType "CoreDimension list"
  | CoreTy_Var string   (* Type variable (with its name) *)

(* Pattern *)
datatype CorePattern =
  CorePat_Bool bool
  | CorePat_Int int
  | CorePat_Variant string CorePattern
  | CorePat_Record "(string \<times> CorePattern) list"
  | CorePat_Wildcard

(* A pattern is "flat" if it tests only at its top level: variant payloads
   must be wildcards, and record patterns are disallowed entirely. The
   match-compilation pass (core_passes/MatchCompile.thy) guarantees that
   every pattern in its output is flat; downstream consumers (code
   generation, etc.) may rely on this. *)
fun flat_pattern :: "CorePattern \<Rightarrow> bool" where
  "flat_pattern (CorePat_Variant _ p) = (p = CorePat_Wildcard)"
| "flat_pattern (CorePat_Record _) = False"
| "flat_pattern _ = True"

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
  | CoreTm_LitArray CoreType "CoreTerm list"  (* one-dimensional array, with element type *)
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
  | CoreTm_Old CoreTerm  (* in postcondition, returns "old" value of term; elsewhere, just returns the term *)
  | CoreTm_Default CoreType  (* default value of the given (well-kinded) type *)

(* Extract the base variable name from a syntactic lvalue *)
fun lvalue_base_name :: "CoreTerm \<Rightarrow> string option" where
  "lvalue_base_name (CoreTm_Var name) = Some name"
| "lvalue_base_name (CoreTm_RecordProj tm _) = lvalue_base_name tm"
| "lvalue_base_name (CoreTm_VariantProj tm _) = lvalue_base_name tm"
| "lvalue_base_name (CoreTm_ArrayProj tm _) = lvalue_base_name tm"
| "lvalue_base_name _ = None"

(* A term is a syntactic lvalue if it has a base variable name *)
definition is_lvalue :: "CoreTerm \<Rightarrow> bool" where
  "is_lvalue tm = (lvalue_base_name tm \<noteq> None)"

lemma is_lvalue_simps [simp]:
  "is_lvalue (CoreTm_Var x) = True"
  "is_lvalue (CoreTm_RecordProj tm f) = is_lvalue tm"
  "is_lvalue (CoreTm_VariantProj tm c) = is_lvalue tm"
  "is_lvalue (CoreTm_ArrayProj tm idxs) = is_lvalue tm"
  "is_lvalue (CoreTm_LitBool b) = False"
  "is_lvalue (CoreTm_LitInt i) = False"
  "is_lvalue (CoreTm_LitArray ty tms) = False"
  "is_lvalue (CoreTm_Unop uop tm) = False"
  "is_lvalue (CoreTm_Binop bop t1 t2) = False"
  "is_lvalue (CoreTm_Let v rhs body) = False"
  "is_lvalue (CoreTm_FunctionCall fn tys args) = False"
  "is_lvalue (CoreTm_VariantCtor cn tys arg) = False"
  "is_lvalue (CoreTm_Record flds) = False"
  "is_lvalue (CoreTm_Match scrut arms) = False"
  "is_lvalue (CoreTm_Cast ty tm) = False"
  "is_lvalue (CoreTm_Quantifier q v ty body) = False"
  "is_lvalue (CoreTm_Allocated tm) = False"
  "is_lvalue (CoreTm_Old tm) = False"
  "is_lvalue (CoreTm_Sizeof tm) = False"
  "is_lvalue (CoreTm_Default ty) = False"
  by (simp_all add: is_lvalue_def)

datatype CoreStatement =
  (* Declare a new variable, initialized by a pure term *)
    CoreStmt_VarDecl GhostOrNot string VarOrRef CoreType CoreTerm
  
  (* Declare a new variable, initialized from an impure function call.
     Parameters: declGhost, varName, variable type, optional cast type for the return value, 
     fnName, type args, term args. (If cast type present, it must match the var type.) *)
  | CoreStmt_VarDeclCall GhostOrNot string CoreType "CoreType option" string "CoreType list" "CoreTerm list"
  
  (* Fix: introduce a universally quantified variable in a proof. *)
  | CoreStmt_Fix string CoreType
  
  (* Obtain: create a ghost variable of the given type, satisfying the given boolean condition. *)
  | CoreStmt_Obtain string CoreType CoreTerm
  
  (* Use: specify a witness for an existential variable in a proof. *)
  | CoreStmt_Use CoreTerm
  
  (* Assignment. Rhs must be a pure term; lhs must be an lvalue. *)
  | CoreStmt_Assign GhostOrNot CoreTerm CoreTerm
  
  (* Assignment whose rhs is an impure function call.
     assignGhost, lhs (must be lvalue), optional cast type for the return value,
     fnName, type args, term args. *)
  | CoreStmt_AssignCall GhostOrNot CoreTerm "CoreType option" string "CoreType list" "CoreTerm list"
  
  (* Swap two lvalues in place. *)
  | CoreStmt_Swap GhostOrNot CoreTerm CoreTerm
  
  (* Return a value from the current function. *)
  | CoreStmt_Return CoreTerm
  
  (* Assert that a condition is true (creates a proof obligation).
     If condition = None, this is "assert *" i.e. assert the current proof goal.
     The statement list is the proof body (contains fix, asserts, etc., to help the SMT solver;
     can be empty). *)
  | CoreStmt_Assert "CoreTerm option" "CoreStatement list"
  
  (* Assume that a given boolean term is True. May be unsound; use carefully. *)
  | CoreStmt_Assume CoreTerm
  
  (* While-loop with: ghost flag, condition, invariants, decreases-term, loop body.
     The loop body runs inside its own scope, i.e. it is implicitly inside a CoreStmt_Block. *)
  | CoreStmt_While GhostOrNot CoreTerm "CoreTerm list" CoreTerm "CoreStatement list"  
  
  (* Match-stmt with: ghost flag, scrutinee, list of arms. Each arm is a pattern and a 
     statement-list (which runs inside its own scope, i.e. is implicitly inside a CoreStmt_Block). *)
  | CoreStmt_Match GhostOrNot CoreTerm "(CorePattern \<times> CoreStatement list) list"
  
  (* Show or hide a name from the SMT solvers. Has no semantic effect; this just impacts how the
     proof obligations are verified. *)
  | CoreStmt_ShowHide ShowOrHide string
  
  (* Execute a list of statements in a fresh runtime scope, discarded on exit (an analogue 
     of C's `{ ... }`). *)
  | CoreStmt_Block "CoreStatement list"

(* TODO: Decls, etc. *)

end
