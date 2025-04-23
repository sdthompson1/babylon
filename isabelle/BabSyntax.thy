theory BabSyntax
  imports Main Location
begin

(* Keywords *)
datatype Keyword = 
  KW_ALLOCATED
  | KW_ASSERT
  | KW_ASSUME
  | KW_BOOL
  | KW_CASE
  | KW_CAST
  | KW_CONST
  | KW_DATATYPE
  | KW_DECREASES
  | KW_ELSE
  | KW_ENSURES
  | KW_EXISTS
  | KW_EXTERN
  | KW_FALSE
  | KW_FIX
  | KW_FORALL
  | KW_FUNCTION
  | KW_GHOST
  | KW_HIDE
  | KW_I8
  | KW_I16
  | KW_I32
  | KW_I64
  | KW_IF
  | KW_IMPORT
  | KW_IMPURE
  | KW_IN
  | KW_INT
  | KW_INTERFACE
  | KW_INVARIANT
  | KW_LET
  | KW_MATCH
  | KW_MODULE
  | KW_OBTAIN
  | KW_OLD
  | KW_REAL
  | KW_REF
  | KW_REQUIRES
  | KW_RETURN
  | KW_SHOW
  | KW_SIZEOF
  | KW_SWAP
  | KW_THEN
  | KW_TRUE
  | KW_TYPE
  | KW_U8
  | KW_U16
  | KW_U32
  | KW_U64
  | KW_USE
  | KW_VAR
  | KW_WHILE
  | KW_WITH
  

(* Tokens *)
datatype Token =
  (* Literals *)
  NAT_NUM nat
  | STRING string
  
    (* Identifiers *)
  | NAME string
  
    (* Keywords *)
  | KEYWORD Keyword
  
    (* Various punctuation symbols *)  
  | PLUS
  | MINUS
  | STAR
  | SLASH
  | MODULO
  
  | AND
  | AND_AND
  | BAR
  | BAR_BAR
  | HAT
  | EXCLAM
  | TILDE

  | LESS
  | LESS_LESS
  | LESS_EQUAL
  | LESS_EQUAL_EQUAL
  | LESS_EQUAL_EQUAL_GREATER

  | GREATER
  | GREATER_GREATER
  | GREATER_EQUAL
  
  | EQUAL
  | EQUAL_GREATER
  | EQUAL_EQUAL
  | EQUAL_EQUAL_GREATER
  
  | EXCLAM_EQUAL
  
  | COLON
  | SEMICOLON
  | COMMA
  | DOT
  
  | LPAREN
  | RPAREN
  | LBRACE
  | RBRACE
  | LBRACKET
  | RBRACKET
  
  | UNDERSCORE


(* Helper functions for tokens *)
fun is_nat_num_token :: "Token \<Rightarrow> bool" where
  "is_nat_num_token (NAT_NUM _) = True"
| "is_nat_num_token _ = False"

fun is_string_token :: "Token \<Rightarrow> bool" where
  "is_string_token (STRING _) = True"
| "is_string_token _ = False"

fun is_name_token :: "Token \<Rightarrow> bool" where
  "is_name_token (NAME _) = True"
| "is_name_token _ = False"


(* Abstract syntax for the Babylon language *)

datatype Signedness = Signed | Unsigned
datatype IntBits = IntBits_8 | IntBits_16 | IntBits_32 | IntBits_64
datatype Quantifier = Quant_Forall | Quant_Exists

datatype BabUnop =
  BabUnop_Negate
  | BabUnop_Complement
  | BabUnop_Not

datatype BabBinop =
  BabBinop_Add
  | BabBinop_Subtract
  | BabBinop_Multiply
  | BabBinop_Divide
  | BabBinop_Modulo

  | BabBinop_BitAnd
  | BabBinop_BitOr
  | BabBinop_BitXor
  | BabBinop_ShiftLeft
  | BabBinop_ShiftRight

  | BabBinop_Equal
  | BabBinop_NotEqual
  | BabBinop_Less
  | BabBinop_LessEqual
  | BabBinop_Greater
  | BabBinop_GreaterEqual

  | BabBinop_And
  | BabBinop_Or
  | BabBinop_Implies
  | BabBinop_ImpliedBy
  | BabBinop_Iff

datatype BabLiteral =
  BabLit_Bool bool
  | BabLit_Int int
  | BabLit_String string
  | BabLit_Array "BabTerm list"

(* array dimension *)
and BabDimension = 
  BabDim_Unknown 
  | BabDim_Allocatable 
  | BabDim_Fixed BabTerm

and BabType =
    BabTy_Name Location string "BabType list"
  | BabTy_Bool Location
  | BabTy_FiniteInt Location Signedness IntBits
  | BabTy_MathInt Location
  | BabTy_MathReal Location
  | BabTy_Tuple Location "BabType list"
  | BabTy_Record Location "(string * BabType) list"
  | BabTy_Array Location BabType "BabDimension list"

and BabTerm =
  BabTm_Literal Location BabLiteral
  | BabTm_Name Location string "BabType list"
  | BabTm_Cast Location BabType BabTerm
  | BabTm_If Location BabTerm BabTerm BabTerm
  | BabTm_Unop Location BabUnop BabTerm
  | BabTm_Binop Location BabBinop BabTerm BabTerm
  | BabTm_Let Location string BabTerm BabTerm
  | BabTm_Quantifier Location Quantifier string BabType BabTerm
  | BabTm_Call Location BabTerm "BabTerm list"
  | BabTm_Tuple Location "BabTerm list"
  | BabTm_Record Location "(string * BabTerm) list"
  | BabTm_RecordUpdate Location BabTerm "(string * BabTerm) list"
  | BabTm_TupleProj Location BabTerm nat
  | BabTm_RecordProj Location BabTerm string
  | BabTm_ArrayProj Location BabTerm "BabTerm list"
  (* omitted for now: BabTerm_Match *)
  | BabTm_Sizeof Location BabTerm
  | BabTm_Allocated Location BabTerm


(* Helper functions for the abstract syntax *)

fun bab_type_location :: "BabType \<Rightarrow> Location" where
  "bab_type_location (BabTy_Name loc _ _) = loc"
| "bab_type_location (BabTy_Bool loc) = loc"
| "bab_type_location (BabTy_FiniteInt loc _ _) = loc"
| "bab_type_location (BabTy_MathInt loc) = loc"
| "bab_type_location (BabTy_MathReal loc) = loc"
| "bab_type_location (BabTy_Tuple loc _) = loc"
| "bab_type_location (BabTy_Record loc _) = loc"
| "bab_type_location (BabTy_Array loc _ _) = loc"

fun bab_term_location :: "BabTerm \<Rightarrow> Location" where
  "bab_term_location (BabTm_Literal loc _) = loc"
| "bab_term_location (BabTm_Name loc _ _) = loc"
| "bab_term_location (BabTm_Cast loc _ _) = loc"
| "bab_term_location (BabTm_If loc _ _ _) = loc"
| "bab_term_location (BabTm_Unop loc _ _) = loc"
| "bab_term_location (BabTm_Binop loc _ _ _) = loc"
| "bab_term_location (BabTm_Let loc _ _ _) = loc"
| "bab_term_location (BabTm_Quantifier loc _ _ _ _) = loc"
| "bab_term_location (BabTm_Call loc _ _) = loc"
| "bab_term_location (BabTm_Tuple loc _) = loc"
| "bab_term_location (BabTm_Record loc _) = loc"
| "bab_term_location (BabTm_RecordUpdate loc _ _) = loc"
| "bab_term_location (BabTm_TupleProj loc _ _) = loc"
| "bab_term_location (BabTm_RecordProj loc _ _) = loc"
| "bab_term_location (BabTm_ArrayProj loc _ _) = loc"
| "bab_term_location (BabTm_Sizeof loc _) = loc"
| "bab_term_location (BabTm_Allocated loc _) = loc"



end
