(* Lexical syntax of the language (tokens, keywords etc.) *)

theory BabToken
  imports Main
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

end
