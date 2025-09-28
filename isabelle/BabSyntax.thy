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

datatype VarOrRef = Var | Ref

datatype BabPattern = 
    BabPat_Var Location VarOrRef string
  | BabPat_Bool Location bool
  | BabPat_Int Location int
  | BabPat_Tuple Location "BabPattern list"
  | BabPat_Record Location "(string \<times> BabPattern) list"
  | BabPat_Variant Location string "BabPattern option"
  | BabPat_Wildcard Location

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
  | BabTm_Binop Location BabTerm "(BabBinop \<times> BabTerm) list"  (* all ops have same precedence *)
  | BabTm_Let Location string BabTerm BabTerm
  | BabTm_Quantifier Location Quantifier string BabType BabTerm
  | BabTm_Call Location BabTerm "BabTerm list"
  | BabTm_Tuple Location "BabTerm list"
  | BabTm_Record Location "(string \<times> BabTerm) list"
  | BabTm_RecordUpdate Location BabTerm "(string \<times> BabTerm) list"
  | BabTm_TupleProj Location BabTerm nat
  | BabTm_RecordProj Location BabTerm string
  | BabTm_ArrayProj Location BabTerm "BabTerm list"
  | BabTm_Match Location BabTerm "(BabPattern \<times> BabTerm) list"
  | BabTm_Sizeof Location BabTerm
  | BabTm_Allocated Location BabTerm
  | BabTm_Old Location BabTerm

datatype BabAttribute = 
  BabAttr_Requires Location BabTerm
  | BabAttr_Ensures Location BabTerm
  | BabAttr_Invariant Location BabTerm
  | BabAttr_Decreases Location BabTerm

datatype ShowOrHide = Show | Hide
datatype GhostOrNot = Ghost | NotGhost

datatype BabStatement =
  BabStmt_VarDecl Location GhostOrNot string VarOrRef "BabType option" "BabTerm option"
  | BabStmt_Fix Location string BabType
  | BabStmt_Obtain Location string BabType BabTerm
  | BabStmt_Use Location BabTerm
  | BabStmt_Assign Location GhostOrNot BabTerm BabTerm
  | BabStmt_Swap Location GhostOrNot BabTerm BabTerm
  | BabStmt_Return Location GhostOrNot "BabTerm option"
  | BabStmt_Assert Location "BabTerm option" "BabStatement list"
  | BabStmt_Assume Location BabTerm
  | BabStmt_If Location GhostOrNot BabTerm "BabStatement list" "BabStatement list"
  | BabStmt_While Location GhostOrNot BabTerm "BabAttribute list" "BabStatement list"
  | BabStmt_Call Location GhostOrNot BabTerm   (* BabTm_Call term *)
  | BabStmt_Match Location GhostOrNot BabTerm "(BabPattern \<times> BabStatement list) list"
  | BabStmt_ShowHide Location ShowOrHide string

datatype AllocLevel = AllocNever | AllocIfNotDefault | AllocAlways

record DeclConst =
  DC_Location :: Location
  DC_Name :: string
  DC_Type :: "BabType option"
  DC_Value :: "BabTerm option"
  DC_Ghost :: GhostOrNot

record DeclFun =
  DF_Location :: Location
  DF_Name :: string
  DF_TyArgs :: "string list"
  DF_TmArgs :: "(string \<times> VarOrRef \<times> BabType) list"
  DF_ReturnType :: "BabType option"
  DF_Body :: "(BabStatement list) option"
  DF_Attributes :: "BabAttribute list"
  DF_Ghost :: GhostOrNot
  DF_Extern :: bool
  DF_Impure :: bool

type_synonym DataCtor = "Location \<times> string \<times> (BabType option)"

record DeclDatatype =
  DD_Location :: Location
  DD_Name :: string
  DD_TyArgs :: "string list"
  DD_Ctors :: "DataCtor list"

record DeclTypedef = 
  DT_Location :: Location
  DT_Name :: string
  DT_TyArgs :: "string list"
  DT_Definition :: "BabType option"   (* `None` for abstract or extern type *)
  DT_Extern :: bool
  DT_AllocLevel :: AllocLevel   (* Only relevant if DT_Definition is None *)

datatype BabDeclaration = 
  BabDecl_Const DeclConst
  | BabDecl_Function DeclFun
  | BabDecl_Datatype DeclDatatype
  | BabDecl_Typedef DeclTypedef

record BabImport =
  Imp_Location :: Location
  Imp_ModuleName :: string
  Imp_AliasName :: string
  Imp_Qualified :: bool

record BabModule =
  Mod_Name :: string
  Mod_InterfaceImports :: "BabImport list"
  Mod_Interface :: "BabDeclaration list"
  Mod_ImplementationImports :: "BabImport list"
  Mod_Implementation :: "BabDeclaration list"

record BabPackage =
  Pkg_Name :: string
  Pkg_Dependencies :: "string list"
  Pkg_ExportedModules :: "BabModule list"
  Pkg_OtherModules :: "BabModule list"



(* Helper functions *)

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
| "bab_term_location (BabTm_Binop loc _ _) = loc"
| "bab_term_location (BabTm_Let loc _ _ _) = loc"
| "bab_term_location (BabTm_Quantifier loc _ _ _ _) = loc"
| "bab_term_location (BabTm_Call loc _ _) = loc"
| "bab_term_location (BabTm_Tuple loc _) = loc"
| "bab_term_location (BabTm_Record loc _) = loc"
| "bab_term_location (BabTm_RecordUpdate loc _ _) = loc"
| "bab_term_location (BabTm_TupleProj loc _ _) = loc"
| "bab_term_location (BabTm_RecordProj loc _ _) = loc"
| "bab_term_location (BabTm_ArrayProj loc _ _) = loc"
| "bab_term_location (BabTm_Match loc _ _) = loc"
| "bab_term_location (BabTm_Sizeof loc _) = loc"
| "bab_term_location (BabTm_Allocated loc _) = loc"
| "bab_term_location (BabTm_Old loc _) = loc"

fun bab_attribute_location :: "BabAttribute \<Rightarrow> Location" where
  "bab_attribute_location (BabAttr_Requires loc _) = loc"
| "bab_attribute_location (BabAttr_Ensures loc _) = loc"
| "bab_attribute_location (BabAttr_Invariant loc _) = loc"
| "bab_attribute_location (BabAttr_Decreases loc _) = loc"

fun bab_statement_location :: "BabStatement \<Rightarrow> Location" where
  "bab_statement_location (BabStmt_VarDecl loc _ _ _ _ _) = loc"
| "bab_statement_location (BabStmt_Fix loc _ _) = loc"
| "bab_statement_location (BabStmt_Obtain loc _ _ _) = loc"
| "bab_statement_location (BabStmt_Use loc _) = loc"
| "bab_statement_location (BabStmt_Assign loc _ _ _) = loc"
| "bab_statement_location (BabStmt_Swap loc _ _ _) = loc"
| "bab_statement_location (BabStmt_Return loc _ _) = loc"
| "bab_statement_location (BabStmt_Assert loc _ _) = loc"
| "bab_statement_location (BabStmt_Assume loc _) = loc"
| "bab_statement_location (BabStmt_If loc _ _ _ _) = loc"
| "bab_statement_location (BabStmt_Match loc _ _ _) = loc"
| "bab_statement_location (BabStmt_While loc _ _ _ _) = loc"
| "bab_statement_location (BabStmt_Call loc _ _) = loc"
| "bab_statement_location (BabStmt_ShowHide loc _ _) = loc"

fun array_dim_terms :: "BabDimension \<Rightarrow> BabTerm list" where
  "array_dim_terms (BabDim_Fixed tm) = [tm]"
| "array_dim_terms _ = []"

fun get_decl_name :: "BabDeclaration \<Rightarrow> string"
  where
"get_decl_name (BabDecl_Const dc) = DC_Name dc"
| "get_decl_name (BabDecl_Function df) = DF_Name df"
| "get_decl_name (BabDecl_Datatype dd) = DD_Name dd"
| "get_decl_name (BabDecl_Typedef dt) = DT_Name dt"

fun is_type_decl :: "BabDeclaration \<Rightarrow> bool"
  where
"is_type_decl (BabDecl_Const _) = False"
| "is_type_decl (BabDecl_Function _) = False"
| "is_type_decl (BabDecl_Datatype _) = True"
| "is_type_decl (BabDecl_Typedef _) = True"


(* Size functions *)

fun bab_literal_size :: "BabLiteral \<Rightarrow> nat"
  and bab_dimension_size :: "BabDimension \<Rightarrow> nat"
  and bab_type_size :: "BabType \<Rightarrow> nat"
  and bab_term_size :: "BabTerm \<Rightarrow> nat"
where
"bab_literal_size (BabLit_Array terms) = 1 + sum_list (map bab_term_size terms)"
| "bab_literal_size _ = 1"
| "bab_dimension_size (BabDim_Fixed tm) = 1 + bab_term_size tm"
| "bab_dimension_size _ = 1"
| "bab_type_size (BabTy_Name _ _ tyargs) = 1 + sum_list (map bab_type_size tyargs)"
| "bab_type_size (BabTy_Bool _) = 1"
| "bab_type_size (BabTy_FiniteInt _ _ _) = 1"
| "bab_type_size (BabTy_MathInt _) = 1"
| "bab_type_size (BabTy_MathReal _) = 1"
| "bab_type_size (BabTy_Tuple _ types) = 1 + sum_list (map bab_type_size types)"
| "bab_type_size (BabTy_Record _ flds) = 1 + sum_list (map (bab_type_size \<circ> snd) flds)"
| "bab_type_size (BabTy_Array _ ty dims) = 1 + bab_type_size ty + sum_list (map bab_dimension_size dims)"
| "bab_term_size (BabTm_Literal _ lit) = 1 + bab_literal_size lit"
| "bab_term_size (BabTm_Name _ _ types) = 1 + sum_list (map bab_type_size types)"
| "bab_term_size (BabTm_Cast _ ty tm) = 1 + bab_type_size ty + bab_term_size tm"
| "bab_term_size (BabTm_If _ tm1 tm2 tm3) = 
    1 + bab_term_size tm1 + bab_term_size tm2 + bab_term_size tm3"
| "bab_term_size (BabTm_Unop _ _ tm) = 1 + bab_term_size tm"
| "bab_term_size (BabTm_Binop _ tm items) = 
    1 + bab_term_size tm + sum_list (map (bab_term_size \<circ> snd) items)"
| "bab_term_size (BabTm_Let _ _ tm1 tm2) = 1 + bab_term_size tm1 + bab_term_size tm2"
| "bab_term_size (BabTm_Quantifier _ _ _ ty tm) = 1 + bab_type_size ty + bab_term_size tm"
| "bab_term_size (BabTm_Call _ tm args) = 1 + bab_term_size tm + sum_list (map bab_term_size args)"
| "bab_term_size (BabTm_Tuple _ terms) = 1 + sum_list (map bab_term_size terms)"
| "bab_term_size (BabTm_Record _ flds) = 1 + sum_list (map (bab_term_size \<circ> snd) flds)"
| "bab_term_size (BabTm_RecordUpdate _ tm flds) = 
    1 + bab_term_size tm + sum_list (map (bab_term_size \<circ> snd) flds)"
| "bab_term_size (BabTm_TupleProj _ tm _) = 1 + bab_term_size tm"
| "bab_term_size (BabTm_RecordProj _ tm _) = 1 + bab_term_size tm"
| "bab_term_size (BabTm_ArrayProj _ tm indices) = 
    1 + bab_term_size tm + sum_list (map bab_term_size indices)"
| "bab_term_size (BabTm_Match _ scrut arms) =
    1 + bab_term_size scrut + sum_list (map (bab_term_size \<circ> snd) arms)"
| "bab_term_size (BabTm_Sizeof _ tm) = 1 + bab_term_size tm"
| "bab_term_size (BabTm_Allocated _ tm) = 1 + bab_term_size tm"
| "bab_term_size (BabTm_Old _ tm) = 1 + bab_term_size tm"


lemma bab_type_smaller_than_list:
  "ty \<in> set types \<Longrightarrow> bab_type_size ty < Suc (sum_list (map bab_type_size types))"
  by (induction types, auto)

lemma bab_type_smaller_than_fieldlist:
  "(name, ty) \<in> set fieldTypes \<Longrightarrow> 
    bab_type_size ty < Suc (sum_list (map (bab_type_size \<circ> snd) fieldTypes))"
  by (induction fieldTypes, auto)

lemma bab_term_smaller_than_list:
  "tm \<in> set terms \<Longrightarrow> bab_term_size tm < Suc (sum_list (map bab_term_size terms))"
  by (induction terms, auto)

lemma bab_term_smaller_than_fieldlist:
  "(name, tm) \<in> set flds \<Longrightarrow>
    bab_term_size tm < Suc (sum_list (map (bab_term_size \<circ> snd) flds))"
  by (induction flds, auto)

lemma bab_term_smaller_than_arraydim:
  assumes "dim \<in> set dims"
    and "tm \<in> set (array_dim_terms dim)"
  shows "bab_term_size tm < Suc (sum_list (map bab_dimension_size dims))"
using assms
proof (induction dims)
  case Nil
  then show ?case by auto
next
  case (Cons dim1 dimRest)
  then show ?case proof (cases "dim = dim1")
    case True
    have "array_dim_terms dim = [tm]" using assms(2)
      by (metis array_dim_terms.elims distinct.simps(2) distinct_singleton set_ConsD)
    hence "bab_dimension_size dim1 = 1 + bab_term_size tm"
      by (metis BabDimension.distinct(3,5) BabDimension.inject True array_dim_terms.elims
          bab_dimension_size.elims list.distinct(1) list.inject)
    thus ?thesis
      by simp
  next
    case False
    then show ?thesis using Cons by auto
  qed
qed

end
