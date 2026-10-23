theory MiniCSyntax
  imports "Babylon.IntRange"
begin

(* ========================================================================== *)
(* MiniC: abstract syntax                                                     *)
(* ========================================================================== *)

(* MiniC is the small fragment of C that the verified code generator targets.
   See minic/DESIGN.md for the rationale. In brief:

    - Every variable (local, parameter or global) is an object in byte-addressed
      memory. A "scalar" variable holds one C scalar (an exact-width integer,
      or a pointer) and is printed as e.g. `int32_t x;`; a "buffer" variable is
      a byte array `char x[N];` (N may be a run-time expression: a VLA).
    - Expressions are pure: they may read memory (ME_Load, ME_Var) but cannot
      call functions, assign, store or allocate. Expression evaluation can
      still fail (undefined behaviour), e.g. a load from a dead block.
    - Everything with an effect is a statement.
    - Names are plain strings; the (unverified) printer mangles them. Extern
      functions carry their C name and are printed under it. *)


section \<open>C types\<close>

(* The scalar C types of MiniC: the eight exact-width integer types, `char *`
   and `void *`. Babylon's bool is CTy_Int Unsigned IntBits_8 (a uint8_t holding
   0 or 1). Semantically the two pointer types are the same; the distinction
   only matters to the printer (extern prototypes use `void *` for extern
   types, everything else is `char *`). *)
datatype CTy =
  CTy_Int Signedness IntBits
  | CTy_CharPtr
  | CTy_VoidPtr

abbreviation "CTy_U8 \<equiv> CTy_Int Unsigned IntBits_8"
abbreviation "CTy_U64 \<equiv> CTy_Int Unsigned IntBits_64"
abbreviation "CTy_I32 \<equiv> CTy_Int Signed IntBits_32"

fun is_ptr_ty :: "CTy \<Rightarrow> bool" where
  "is_ptr_ty CTy_CharPtr = True"
| "is_ptr_ty CTy_VoidPtr = True"
| "is_ptr_ty _ = False"


section \<open>Expressions\<close>

datatype CUnop =
  CU_Neg          (* -e, integer negation; UB if the result does not fit *)
  | CU_Compl      (* ~e, bitwise complement at the operand's type *)
  | CU_Not        (* !e, logical not: 1 if e = 0, else 0; result is u8 *)

(* Binary operators on two integers of the same type. Arithmetic computes the
   mathematical result and is UB unless the result fits the operand type (this
   is stricter than C, which is what we want: everything MiniC defines, C
   defines in the same way). Comparisons yield a u8 0/1. The shifts have
   exactly Core's semantics (count in [0, width) at any integer type, result
   has the left operand's type and must fit) and are printed as the idiom
   described in DESIGN.md. CB_Max is max (used in the size of a variant:
   tag + max payload size, and for max(1, n) buffer sizes); printed as a
   helper. *)
datatype CBinop =
  CB_Add | CB_Sub | CB_Mul | CB_Div | CB_Mod
  | CB_BitAnd | CB_BitOr | CB_BitXor | CB_Shl | CB_Shr
  | CB_Eq | CB_Ne | CB_Lt | CB_Le | CB_Gt | CB_Ge
  | CB_Max

datatype MExpr =
  ME_Int Signedness IntBits int        (* integer literal of the given type *)
  | ME_PtrSize                          (* the size of a pointer, as a u64: sizeof of a void pointer *)
  | ME_Var string                       (* value of a scalar variable *)
  | ME_AddrOf string                    (* the address of variable x, as a char pointer *)
  | ME_Load CTy MExpr                   (* load a scalar of the given type from an address *)
  | ME_Unop CUnop MExpr
  | ME_Binop CBinop MExpr MExpr
  | ME_Cast CTy MExpr                   (* integer conversion; UB if out of range *)
  | ME_PtrAdd MExpr MExpr               (* p + i (i an integer; result must stay in the block) *)


section \<open>Statements\<close>

datatype MStmt =
  MS_DeclScalar string CTy              (* T x;  (uninitialised) *)
  | MS_DeclBuf string MExpr             (* char x[n];  n a u64 expression; the block has max 1 n bytes *)
  | MS_Assign string MExpr              (* x = e;  (x a scalar variable) *)
  | MS_Store CTy MExpr MExpr            (* store a scalar of type T at an address: store_T(p, e) *)
  | MS_Copy MExpr MExpr MExpr           (* memmove(dst, src, n) *)
  | MS_Zero MExpr MExpr                 (* memset(p, 0, n) *)
  | MS_If MExpr "MStmt list" "MStmt list"
  | MS_Loop "MStmt list"                (* while (1) { ... }; left by MS_Break or MS_Return *)
  | MS_Break
  | MS_Block "MStmt list"               (* { ... }: a scope; variables declared inside die at the end *)
  | MS_Call "string option" string "MExpr list"
                                        (* [x =] f(args);  x receives a scalar result *)
  | MS_Return "MExpr option"


section \<open>Functions and programs\<close>

record MFun =
  MF_Name   :: string
  MF_Params :: "(string \<times> CTy) list"
  MF_Ret    :: "CTy option"              (* None: void *)
  MF_Body   :: "MStmt list"              (* ignored for an extern function *)
  MF_Extern :: "string option"           (* Some cname: an extern function, printed as cname *)

(* A global variable has static storage: its bytes are all zero initially
   (C guarantees this for static storage). Generated code initialises
   non-zero globals by explicit stores from main (see DESIGN.md). The size of
   a buffer global is a closed expression (it may mention ME_PtrSize). *)
datatype MGlobal =
  MG_Scalar CTy
  | MG_Buf MExpr

record MProgram =
  MP_Globals :: "(string \<times> MGlobal) list"
  MP_Funcs   :: "MFun list"

(* Function lookup by name. *)
definition lookup_fun :: "MProgram \<Rightarrow> string \<Rightarrow> MFun option" where
  "lookup_fun prog name = find (\<lambda>f. MF_Name f = name) (MP_Funcs prog)"


section \<open>Syntactic well-formedness\<close>

(* The small amount of static well-formedness that the interpreter and the
   printer rely on. A full typing predicate is later work (stage 3b).
    - function names are distinct, and `main` exists, taking no parameters and
      returning an int (so that the printer can emit `int main(void)`);
    - every call names a function of the program, with the right number of
      arguments;
    - MS_Break only occurs inside a loop;
    - integer literals fit their type. *)

fun expr_wf :: "MExpr \<Rightarrow> bool" where
  "expr_wf (ME_Int s b i) = int_fits s b i"
| "expr_wf ME_PtrSize = True"
| "expr_wf (ME_Var _) = True"
| "expr_wf (ME_AddrOf _) = True"
| "expr_wf (ME_Load _ e) = expr_wf e"
| "expr_wf (ME_Unop _ e) = expr_wf e"
| "expr_wf (ME_Binop _ e1 e2) = (expr_wf e1 \<and> expr_wf e2)"
| "expr_wf (ME_Cast _ e) = expr_wf e"
| "expr_wf (ME_PtrAdd e1 e2) = (expr_wf e1 \<and> expr_wf e2)"

(* `inLoop` says whether a break is permitted here. *)
fun stmt_wf :: "MProgram \<Rightarrow> bool \<Rightarrow> MStmt \<Rightarrow> bool"
and stmts_wf :: "MProgram \<Rightarrow> bool \<Rightarrow> MStmt list \<Rightarrow> bool" where
  "stmt_wf prog inLoop (MS_DeclScalar _ _) = True"
| "stmt_wf prog inLoop (MS_DeclBuf _ e) = expr_wf e"
| "stmt_wf prog inLoop (MS_Assign _ e) = expr_wf e"
| "stmt_wf prog inLoop (MS_Store _ p e) = (expr_wf p \<and> expr_wf e)"
| "stmt_wf prog inLoop (MS_Copy d s n) = (expr_wf d \<and> expr_wf s \<and> expr_wf n)"
| "stmt_wf prog inLoop (MS_Zero p n) = (expr_wf p \<and> expr_wf n)"
| "stmt_wf prog inLoop (MS_If c t e) = (expr_wf c \<and> stmts_wf prog inLoop t \<and> stmts_wf prog inLoop e)"
| "stmt_wf prog inLoop (MS_Loop body) = stmts_wf prog True body"
| "stmt_wf prog inLoop MS_Break = inLoop"
| "stmt_wf prog inLoop (MS_Block body) = stmts_wf prog inLoop body"
| "stmt_wf prog inLoop (MS_Call _ f args) =
    (list_all expr_wf args
     \<and> (case lookup_fun prog f of
          None \<Rightarrow> False
        | Some fn \<Rightarrow> length args = length (MF_Params fn)))"
| "stmt_wf prog inLoop (MS_Return None) = True"
| "stmt_wf prog inLoop (MS_Return (Some e)) = expr_wf e"

| "stmts_wf prog inLoop [] = True"
| "stmts_wf prog inLoop (s # ss) = (stmt_wf prog inLoop s \<and> stmts_wf prog inLoop ss)"

definition fun_wf :: "MProgram \<Rightarrow> MFun \<Rightarrow> bool" where
  "fun_wf prog f =
    (distinct (map fst (MF_Params f))
     \<and> (MF_Extern f = None \<longrightarrow> stmts_wf prog False (MF_Body f)))"

definition program_wf :: "MProgram \<Rightarrow> bool" where
  "program_wf prog =
    (distinct (map MF_Name (MP_Funcs prog))
     \<and> distinct (map fst (MP_Globals prog))
     \<and> list_all (fun_wf prog) (MP_Funcs prog)
     \<and> (case lookup_fun prog ''main'' of
          None \<Rightarrow> False
        | Some m \<Rightarrow> MF_Params m = [] \<and> MF_Ret m = Some CTy_I32 \<and> MF_Extern m = None))"

end
