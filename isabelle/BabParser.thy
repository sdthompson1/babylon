theory BabParser
  imports Main "HOL-Library.Char_ord" Location BabSyntax BasicParser
begin

(* Specializing BasicParser for our parser *)

(* list of located tokens, and length of list *)
type_synonym ParserStream = "(Location \<times> Token) list \<times> nat"

type_synonym ParserState = "(ParserStream, Token) BasicParserState"

type_synonym 'a Parser = "('a, ParserStream, Token) BasicParser"

type_synonym 'a ParseResult = "('a, ParserStream, Token) BasicParseResult"

fun parser_next_fn :: "ParserStream \<Rightarrow> (Token \<times> Location \<times> ParserStream) option" where
  "parser_next_fn (str, count) =
    (case str of
      [] \<Rightarrow> None
    | (loc, tok) # ts \<Rightarrow> Some (tok, loc, (ts, count - 1)))"

fun parser_fuel_fn :: "ParserStream \<Rightarrow> nat" where
  "parser_fuel_fn (str, count) = count"

fun initial_parser_state :: "string \<Rightarrow> (Location \<times> Token) list \<Rightarrow> ParserState" where
  "initial_parser_state filename tokens =
    ((tokens, length tokens), parser_next_fn, parser_fuel_fn, Location filename 1 1 1 1)"


(* General helper functions *)

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse sep [] = []"
| "intersperse sep [x] = [x]"
| "intersperse sep (x#y#ys) = x # sep # intersperse sep (y # ys)"

definition with_loc :: "(Location \<Rightarrow> 'a) Parser \<Rightarrow> 'a Parser" where
  "with_loc p = do {
    (loc, result) \<leftarrow> located p;
    return (result loc)
  }"

definition parens :: "'a Parser \<Rightarrow> 'a Parser" where
  "parens = between (expect LPAREN) (expect RPAREN)"

definition braces :: "'a Parser \<Rightarrow> 'a Parser" where
  "braces = between (expect LBRACE) (expect RBRACE)"

definition brackets :: "'a Parser \<Rightarrow> 'a Parser" where
  "brackets = between (expect LBRACKET) (expect RBRACKET)"

(* parsing angle brackets is hard because we need to break apart
   the '<<' and '>>' tokens where applicable *)
(* replace assumes that the new token is one character shorter than the old, and updates
   locations accordingly *)
fun replace :: "Token \<Rightarrow> ParserStream \<Rightarrow> ParserStream"
  where
"replace newTok ((Location file line1 col1 line2 col2, tok) # rest, len) 
    = ((Location file line1 (col1 + 1) line2 col2, newTok) # rest, len)"
| "replace _ other = other"

definition left_angle :: "unit Parser" where
  "left_angle = (expect LESS \<then> return ()) 
    <|> (look_ahead (expect LESS_LESS) \<then> modify_stream (replace LESS))"

definition right_angle :: "unit Parser" where
  "right_angle = (expect GREATER \<then> return ())
    <|> (look_ahead (expect GREATER_GREATER) \<then> modify_stream (replace GREATER))"

definition angles :: "'a Parser \<Rightarrow> 'a Parser" where
  "angles = between left_angle right_angle"


definition optional_braces :: "'a Parser \<Rightarrow> 'a option Parser" where
  "optional_braces = optional_between (expect LBRACE) (expect RBRACE)"

definition optional_angles :: "'a Parser \<Rightarrow> 'a option Parser" where
  "optional_angles = optional_between left_angle right_angle"


definition comma_list :: "'a Parser \<Rightarrow> 'a list Parser" where
  "comma_list p = sep_end_by p (expect COMMA)"


definition parse_name :: "string Parser" where
  "parse_name = do {
    tok \<leftarrow> satisfy is_name_token;
    case tok of
      NAME n \<Rightarrow> return n
    | _ \<Rightarrow> undefined
  }"

(* This can be used in contexts where names can only be interpreted
as dotted, e.g. names in types (as opposed to names in terms where
a dotted name could also be a field projection). *)
definition parse_dotted_name :: "string Parser" where
  "parse_dotted_name = do {
    names \<leftarrow> sep_by_1 parse_name (expect DOT);
    return (concat (intersperse ''.'' names))
  }"


(* TYPE AND TERM PARSING *)

(* Type parsing helpers: *)

(* helper to make an array type *)
fun make_array_type :: "(Location \<times> BabDimension list) \<Rightarrow> BabType \<Rightarrow> BabType" where
  "make_array_type (loc, dims) ty =
    BabTy_Array (merge_locations (bab_type_location ty) loc) ty dims"

(* Parse a type that can be used in a numeric cast expression (like `i8(x)`) *)
definition parse_numeric_type :: "BabType Parser" where
  "parse_numeric_type = with_loc (
    (expect (KEYWORD KW_I8) \<then> return (\<lambda>loc. BabTy_FiniteInt loc Signed IntBits_8))
    <|> (expect (KEYWORD KW_I16) \<then> return (\<lambda>loc. BabTy_FiniteInt loc Signed IntBits_16))
    <|> (expect (KEYWORD KW_I32) \<then> return (\<lambda>loc. BabTy_FiniteInt loc Signed IntBits_32))
    <|> (expect (KEYWORD KW_I64) \<then> return (\<lambda>loc. BabTy_FiniteInt loc Signed IntBits_64))
    <|> (expect (KEYWORD KW_U8) \<then> return (\<lambda>loc. BabTy_FiniteInt loc Unsigned IntBits_8))
    <|> (expect (KEYWORD KW_U16) \<then> return (\<lambda>loc. BabTy_FiniteInt loc Unsigned IntBits_16))
    <|> (expect (KEYWORD KW_U32) \<then> return (\<lambda>loc. BabTy_FiniteInt loc Unsigned IntBits_32))
    <|> (expect (KEYWORD KW_U64) \<then> return (\<lambda>loc. BabTy_FiniteInt loc Unsigned IntBits_64))
    <|> (expect (KEYWORD KW_INT) \<then> return BabTy_MathInt)
    <|> (expect (KEYWORD KW_REAL) \<then> return BabTy_MathReal))"


(* Term parsing helpers: *)

(* Parse an int literal token *)
definition int_literal :: "BabLiteral Parser" where
  "int_literal = do {
    t \<leftarrow> satisfy is_nat_num_token;
    case t of NAT_NUM n \<Rightarrow> return (BabLit_Int (of_nat n))
  }"

(* Parse a string literal token *)
definition string_literal :: "BabLiteral Parser" where
  "string_literal = do {
    t \<leftarrow> satisfy is_string_token;
    case t of STRING s \<Rightarrow> return (BabLit_String s)
  }"

(* Parse a binop token *)
(* If successful, returns a precedence and the corresponding binop *)
definition parse_binop :: "(nat \<times> BabBinop) Parser" where
  "parse_binop = 
    (expect STAR \<then> return (7, BabBinop_Multiply))
  <|> (expect SLASH \<then> return (7, BabBinop_Divide))
  <|> (expect MODULO \<then> return (7, BabBinop_Modulo))
  <|> (expect AND \<then> return (7, BabBinop_BitAnd))
  <|> (expect LESS_LESS \<then> return (7, BabBinop_ShiftLeft))
  <|> (expect GREATER_GREATER \<then> return (7, BabBinop_ShiftRight))

  <|> (expect PLUS \<then> return (6, BabBinop_Add))
  <|> (expect MINUS \<then> return (6, BabBinop_Subtract))
  <|> (expect BAR \<then> return (6, BabBinop_BitOr))
  <|> (expect HAT \<then> return (6, BabBinop_BitXor))

  <|> (expect GREATER \<then> return (5, BabBinop_Greater))
  <|> (expect GREATER_EQUAL \<then> return (5, BabBinop_GreaterEqual))
  <|> (expect LESS \<then> return (5, BabBinop_Less))
  <|> (expect LESS_EQUAL \<then> return (5, BabBinop_LessEqual))
  <|> (expect EQUAL_EQUAL \<then> return (5, BabBinop_Equal))
  <|> (expect EXCLAM_EQUAL \<then> return (5, BabBinop_NotEqual))

  <|> (expect AND_AND \<then> return (4, BabBinop_And))

  <|> (expect BAR_BAR \<then> return (3, BabBinop_Or))

  <|> (expect EQUAL_EQUAL_GREATER \<then> return (2, BabBinop_Implies))
  <|> (expect LESS_EQUAL_EQUAL \<then> return (2, BabBinop_ImpliedBy))

  <|> (expect LESS_EQUAL_EQUAL_GREATER \<then> return (1, BabBinop_Iff))"

(* Parse a binop token of at least the given precedence *)
fun binop_of_at_least_prec :: "nat \<Rightarrow> (nat \<times> BabBinop) Parser" where
  "binop_of_at_least_prec min_prec = do {
    p \<leftarrow> parse_binop;
    (if fst p \<ge> min_prec then
      return p
    else
      fail)
    }"

(* unary operators *)
fun unary_operator :: "Token \<Rightarrow> BabUnop option" where
  "unary_operator MINUS = Some BabUnop_Negate"
| "unary_operator TILDE = Some BabUnop_Complement"
| "unary_operator EXCLAM = Some BabUnop_Not"
| "unary_operator _ = None"

definition parse_unop :: "BabUnop Parser" where
  "parse_unop = do {
    tok \<leftarrow> satisfy (\<lambda>tok. unary_operator tok \<noteq> None);
    return (the (unary_operator tok))
  }"

(* helper to make unop term *)
(* note: '-' followed by an int literal is combined into a single
   int literal. This avoids problems with the most negative integer. *)
fun make_unop_term :: "Location \<times> BabUnop \<Rightarrow> BabTerm \<Rightarrow> BabTerm" where
  "make_unop_term (loc1, BabUnop_Negate) (BabTm_Literal loc2 (BabLit_Int i))
    = BabTm_Literal (merge_locations loc1 loc2) (BabLit_Int (-i))"
| "make_unop_term (loc, op) tm
    = BabTm_Unop (merge_locations loc (bab_term_location tm)) op tm"

(* Note: a "restricted" term is one that cannot contain the curly-brace function
   call syntax (e.g. `f{1,2,3}`). This is used to avoid ambiguities in certain
   contexts e.g. if-conditions. It is our equivalent of the following Rust issue:
   https://github.com/rust-lang/rust/issues/50090. *)
datatype Restrict = Restricted | Unrestricted


(* Mutually recursive type and term parsing functions *)

fun parse_type_fuelled :: "nat \<Rightarrow> BabType Parser"
  and parse_basic_type :: "nat \<Rightarrow> BabType Parser"
  and parse_optional_tyargs :: "nat \<Rightarrow> BabType list Parser"
  and parse_name_type_pair :: "nat \<Rightarrow> (string \<times> BabType) Parser"
  and parse_array_suffix :: "nat \<Rightarrow> BabDimension list Parser"
  and parse_array_dimension :: "nat \<Rightarrow> BabDimension Parser"
  and parse_term_min :: "nat \<Rightarrow> nat \<Rightarrow> Restrict \<Rightarrow> BabTerm Parser"
  and parse_operator_and_term :: "nat \<Rightarrow> nat \<Rightarrow> Restrict \<Rightarrow> (BabBinop \<times> BabTerm) Parser"
  and parse_unop_expr :: "nat \<Rightarrow> Restrict \<Rightarrow> BabTerm Parser"
  and parse_call_or_proj_expr :: "nat \<Rightarrow> Restrict \<Rightarrow> BabTerm Parser"
  and parse_call_or_proj_suffix :: "nat \<Rightarrow> Restrict \<Rightarrow> (BabTerm \<Rightarrow> BabTerm) Parser"
  and parse_primary_expr :: "nat \<Rightarrow> Restrict \<Rightarrow> BabTerm Parser"
where

(* Parse a type *)
  "parse_type_fuelled 0 = undefined"  (* out of fuel *)
| "parse_type_fuelled (Suc fuel) = do {
    base \<leftarrow> parse_basic_type fuel;
    dims \<leftarrow> many (located (parse_array_suffix fuel));
    return (foldr make_array_type dims base)
   }"

(* Parse a "basic" type (not array) *)
(* Note: parens around type allowed, because this is sometimes useful for
   array types, e.g. i32[2][3] vs. (i32[3])[2] *)
(* Note: in a type, Foo.Bar is always a qualified name, not a
   field projection (i.e. there is no ambiguity with dots) *)
| "parse_basic_type fuel =
  (parens (delay (\<lambda>_. parse_type_fuelled fuel)))
  <|> parse_numeric_type
  <|> with_loc (
        (expect (KEYWORD KW_BOOL) \<then> return BabTy_Bool)
    <|> (do {
          name \<leftarrow> parse_dotted_name;
          args \<leftarrow> parse_optional_tyargs fuel;
          return (\<lambda>loc. BabTy_Name loc name args)
        })
    <|> (do {
          fieldTypes \<leftarrow> braces (comma_list (delay (\<lambda>_. parse_type_fuelled fuel)));
          return (\<lambda>loc. BabTy_Tuple loc fieldTypes)
         })
    <|> (do {
          fieldTypes \<leftarrow> braces (comma_list (delay (\<lambda>_. parse_name_type_pair fuel)));
          return (\<lambda>loc. BabTy_Record loc fieldTypes)
         })
    )"

(* Parse optional angle-brackets-type-list *)
| "parse_optional_tyargs fuel = do {
    tyargs \<leftarrow> optional_angles (comma_list (delay (\<lambda>_. parse_type_fuelled fuel)));
    case tyargs of
      Some list \<Rightarrow> return list
      | None \<Rightarrow> return []
    }"

(* Parse a "name : type" pair *)
| "parse_name_type_pair fuel = do {
    name \<leftarrow> parse_name;
    expect COLON;
    ty \<leftarrow> delay (\<lambda>_. parse_type_fuelled fuel);
    return (name, ty)
   }"


(* Parse an array-dimension-list in brackets *)
| "parse_array_suffix fuel = 
    brackets (comma_list (parse_array_dimension fuel))"

(* Parse a single array dimension *)
| "parse_array_dimension fuel =
    (expect STAR \<then> return BabDim_Allocatable)
    <|> (delay (\<lambda>_. parse_term_min fuel 0 Unrestricted) \<bind> (return \<circ> BabDim_Fixed))
    <|> (return BabDim_Unknown)"

(* Parse a term, followed by zero or more operator-term pairs at given precedence or higher *)
| "parse_term_min 0 _ _ = undefined"   (* out of fuel *)
| "parse_term_min (Suc fuel) min_prec restrict = with_loc (do {
    left \<leftarrow> parse_unop_expr fuel restrict;
    others \<leftarrow> many (parse_operator_and_term fuel min_prec restrict);
    return (if others = [] then (\<lambda>_. left) else (\<lambda>loc. BabTm_Binop loc left others))
  })"

(* Parse operator-term pair at given precedence or higher *)
| "parse_operator_and_term fuel min_prec restrict =
    do {
      p \<leftarrow> binop_of_at_least_prec min_prec;
      term \<leftarrow> parse_term_min fuel (Suc (fst p)) restrict;
      return (snd p, term)
    }"

(* Parse unary operator expression *)
| "parse_unop_expr fuel restrict = do {
    ops \<leftarrow> many (located parse_unop);
    tm \<leftarrow> parse_call_or_proj_expr fuel restrict;
    return (foldr make_unop_term ops tm)
  }"

(* Parse function call, field projection or array projection *)
| "parse_call_or_proj_expr fuel restrict = do {
    tm \<leftarrow> parse_primary_expr fuel restrict;
    suffixes \<leftarrow> many (parse_call_or_proj_suffix fuel restrict);
    return (foldl (\<lambda>tm f. f tm) tm suffixes)
  }"

| "parse_call_or_proj_suffix fuel restrict =
    (do {
      loc_and_args \<leftarrow> located (parens (comma_list (delay (\<lambda>_. parse_term_min fuel 0 Unrestricted))));
      return (\<lambda>tm. BabTm_Call (merge_locations (bab_term_location tm) (fst loc_and_args))
                              tm
                              (snd loc_and_args))
    })
  <|> (if restrict = Unrestricted then
        (do {
          look_ahead (expect LBRACE);
          loc_and_arg \<leftarrow> located (delay (\<lambda>_. parse_primary_expr fuel Unrestricted));
          return (\<lambda>tm. BabTm_Call (merge_locations (bab_term_location tm) (fst loc_and_arg))
                                  tm
                                  [snd loc_and_arg])
        })
       else fail)
  <|> (do {
        expect DOT;
        loc_and_fld \<leftarrow> located (satisfy is_nat_num_token);
        (case loc_and_fld of
          (loc, NAT_NUM n) \<Rightarrow>
            return (\<lambda>tm. BabTm_TupleProj (merge_locations (bab_term_location tm) loc)
                                         tm
                                         n))
      })
  <|> (do {
        expect DOT;
        loc_and_fld \<leftarrow> located (satisfy is_name_token);
        (case loc_and_fld of
          (loc, NAME n) \<Rightarrow>
            return (\<lambda>tm. BabTm_RecordProj (merge_locations (bab_term_location tm) loc)
                                          tm
                                          n))
      })
  <|> (do {
        loc_and_idxs \<leftarrow> located (brackets (comma_list (delay (\<lambda>_. parse_term_min fuel 0 Unrestricted))));
        return (\<lambda>tm. BabTm_ArrayProj (merge_locations (bab_term_location tm) (fst loc_and_idxs))
                                     tm
                                     (snd loc_and_idxs))
      })"

(* Parse a primary expression, e.g. variable name, literal, parenthesized expression *)
| "parse_primary_expr fuel restrict =
    (parens (delay (\<lambda>_. parse_term_min fuel 0 Unrestricted)))
  <|> with_loc (
        (int_literal \<bind> (\<lambda>lit. return (\<lambda>loc. BabTm_Literal loc lit)))
    <|> (string_literal \<bind> (\<lambda>lit. return (\<lambda>loc. BabTm_Literal loc lit)))
    <|> (expect (KEYWORD KW_FALSE) \<then> return (\<lambda>loc. BabTm_Literal loc (BabLit_Bool False)))
    <|> (expect (KEYWORD KW_TRUE) \<then> return (\<lambda>loc. BabTm_Literal loc (BabLit_Bool True)))
    <|> (do {
          name \<leftarrow> parse_name;
          args \<leftarrow> parse_optional_tyargs fuel;
          return (\<lambda>loc. BabTm_Name loc name args) 
        })
    <|> (do {
          expect (KEYWORD KW_IF);
          tm1 \<leftarrow> delay (\<lambda>_. parse_term_min fuel 0 Unrestricted);
          expect (KEYWORD KW_THEN);
          tm2 \<leftarrow> delay (\<lambda>_. parse_term_min fuel 0 Unrestricted);
          expect (KEYWORD KW_ELSE);
          tm3 \<leftarrow> delay (\<lambda>_. parse_term_min fuel 0 restrict);
          return (\<lambda>loc. BabTm_If loc tm1 tm2 tm3)
        })
    <|> (do {
          expect (KEYWORD KW_LET);
          name \<leftarrow> parse_name;
          expect EQUAL;
          tm1 \<leftarrow> delay (\<lambda>_. parse_term_min fuel 0 Unrestricted);
          expect (KEYWORD KW_IN);
          tm2 \<leftarrow> delay (\<lambda>_. parse_term_min fuel 0 restrict);
          return (\<lambda>loc. BabTm_Let loc name tm1 tm2)
        })
    <|> (do {
          quant \<leftarrow> (expect (KEYWORD KW_FORALL) <|> expect (KEYWORD KW_EXISTS));
          name_ty \<leftarrow> parens (delay (\<lambda>_. parse_name_type_pair fuel));
          tm \<leftarrow> delay (\<lambda>_. parse_term_min fuel 0 Unrestricted);
          let q = (if quant = KEYWORD KW_FORALL then Quant_Forall else Quant_Exists);
          return (\<lambda>loc. BabTm_Quantifier loc q (fst name_ty) (snd name_ty) tm)
        })
    <|> (do {
          ty \<leftarrow> parse_numeric_type;
          operand \<leftarrow> parens (delay (\<lambda>_. parse_term_min fuel 0 Unrestricted));
          return (\<lambda>loc. BabTm_Cast loc ty operand)
        })
    <|> (do { 
          expect (KEYWORD KW_CAST);
          ty \<leftarrow> angles (delay (\<lambda>_. parse_type_fuelled fuel));
          operand \<leftarrow> parens (delay (\<lambda>_. parse_term_min fuel 0 Unrestricted));
          return (\<lambda>loc. BabTm_Cast loc ty operand)
        })
    <|> (do {
          expect (KEYWORD KW_SIZEOF);
          operand \<leftarrow> parens (delay (\<lambda>_. parse_term_min fuel 0 Unrestricted));
          return (\<lambda>loc. BabTm_Sizeof loc operand)
        })
    <|> (do {
          expect (KEYWORD KW_ALLOCATED);
          operand \<leftarrow> parens (delay (\<lambda>_. parse_term_min fuel 0 Unrestricted));
          return (\<lambda>loc. BabTm_Allocated loc operand)
        })
    <|> (do {
          expect (KEYWORD KW_OLD);
          operand \<leftarrow> parens (delay (\<lambda>_. parse_term_min fuel 0 Unrestricted));
          return (\<lambda>loc. BabTm_Old loc operand)
        })
    <|> (do {
          expect (KEYWORD KW_RETURN);
          return (\<lambda>loc. BabTm_Name loc ''return'' [])
        })
    <|> (do {
          terms \<leftarrow> brackets (comma_list (delay (\<lambda>_. parse_term_min fuel 0 Unrestricted)));
          return (\<lambda>loc. BabTm_Literal loc (BabLit_Array terms))
        })
    <|> (do {
          terms \<leftarrow> braces (comma_list (delay (\<lambda>_. parse_term_min fuel 0 Unrestricted)));
          return (\<lambda>loc. BabTm_Tuple loc terms)
        })
    <|> braces (delay (\<lambda>_. (do {
          baseTermOption \<leftarrow> optional
            (not_parser (parse_name \<then> expect EQUAL))
            (do {
              term \<leftarrow> parse_term_min fuel 0 Unrestricted;
              expect (KEYWORD KW_WITH);
              return term });
          namesTerms \<leftarrow> comma_list (delay (\<lambda>_. 
            (do {
              name \<leftarrow> parse_name;
              expect EQUAL;
              value \<leftarrow> parse_term_min fuel 0 Unrestricted;
              return (name, value)
            })));
          return (\<lambda>loc. case baseTermOption of
            None \<Rightarrow> BabTm_Record loc namesTerms
            | Some baseTerm \<Rightarrow> BabTm_RecordUpdate loc baseTerm namesTerms)
        })))
   )"


(* Top-level type and term parsers *)
definition parse_type :: "BabType Parser" where
  "parse_type = do {
    count \<leftarrow> get_num_tokens;
    parse_type_fuelled (Suc count)
  }"

definition parse_term :: "BabTerm Parser" where
  "parse_term = do {
    count \<leftarrow> get_num_tokens;
    parse_term_min (Suc count) 0 Unrestricted
  }"

definition parse_restricted_term :: "BabTerm Parser" where
  "parse_restricted_term = do {
    count \<leftarrow> get_num_tokens;
    parse_term_min (Suc count) 0 Restricted
  }"



(* ATTRIBUTE PARSING *)

definition parse_attribute :: "BabAttribute Parser" where
  "parse_attribute = with_loc (do {
    attrib \<leftarrow> 
      (expect (KEYWORD KW_REQUIRES) \<then> return BabAttr_Requires)
       <|> (expect (KEYWORD KW_ENSURES) \<then> return BabAttr_Ensures)
       <|> (expect (KEYWORD KW_INVARIANT) \<then> return BabAttr_Invariant)
       <|> (expect (KEYWORD KW_DECREASES) \<then> return BabAttr_Decreases);
    term \<leftarrow> parse_term;
    expect SEMICOLON;
    return (\<lambda>loc. attrib loc term)
  })"



(* STATEMENT PARSING *)

definition parse_var_decl_stmt :: "BabStatement Parser" where
  "parse_var_decl_stmt = with_loc (do {
    varOrRef \<leftarrow> (expect (KEYWORD KW_REF) \<then> return Ref)
                <|> (expect (KEYWORD KW_VAR) \<then> return Var);
    name \<leftarrow> parse_name;
    maybeType \<leftarrow> optional (expect COLON) parse_type;
    maybeRhs \<leftarrow> (do {
      expect EQUAL;
      tm \<leftarrow> parse_term;
      return (Some tm)
    }) <|> (if varOrRef = Ref then fail else return None);
    expect SEMICOLON;
    return (\<lambda>loc. BabStmt_VarDecl loc name varOrRef maybeType maybeRhs)
  })"

definition parse_fix_stmt :: "BabStatement Parser" where
  "parse_fix_stmt = with_loc (do {
    expect (KEYWORD KW_FIX);
    name \<leftarrow> parse_name;
    expect COLON;
    ty \<leftarrow> parse_type;
    expect SEMICOLON;
    return (\<lambda>loc. BabStmt_Fix loc name ty)
  })"

definition parse_obtain_stmt :: "BabStatement Parser" where
  "parse_obtain_stmt = with_loc (do {
    expect (KEYWORD KW_OBTAIN);
    expect LPAREN;
    name \<leftarrow> parse_name;
    expect COLON;
    ty \<leftarrow> parse_type;
    expect RPAREN;
    cond \<leftarrow> parse_term;
    expect SEMICOLON;
    return (\<lambda>loc. BabStmt_Obtain loc name ty cond)
  })"

definition parse_use_stmt :: "BabStatement Parser" where
  "parse_use_stmt = with_loc (do {
    expect (KEYWORD KW_USE);
    tm \<leftarrow> parse_term;
    expect SEMICOLON;
    return (\<lambda>loc. BabStmt_Use loc tm)
  })"

definition parse_swap_stmt :: "BabStatement Parser" where
  "parse_swap_stmt = with_loc (do {
    expect (KEYWORD KW_SWAP);
    lhs \<leftarrow> parse_term;
    expect COMMA;
    rhs \<leftarrow> parse_term;
    expect SEMICOLON;
    return (\<lambda>loc. BabStmt_Swap loc lhs rhs)
  })"

definition parse_return_stmt :: "BabStatement Parser" where
  "parse_return_stmt = with_loc (do {
    expect (KEYWORD KW_RETURN);
    maybeTerm \<leftarrow> optional (not_parser (expect SEMICOLON)) parse_term;
    expect SEMICOLON;
    return (\<lambda>loc. BabStmt_Return loc maybeTerm)
  })"

(* both of these begin with a term (as opposed to a keyword) *)
definition parse_assignment_or_call_stmt :: "BabStatement Parser" where
  "parse_assignment_or_call_stmt = with_loc (do {
    lhs \<leftarrow> parse_term;
    result \<leftarrow> (do {
      expect EQUAL;
      rhs \<leftarrow> parse_term;
      return (\<lambda>loc. BabStmt_Assign loc lhs rhs)
    }) <|> 
      (case lhs of
        BabTm_Call _ _ _ \<Rightarrow> return (\<lambda>loc. BabStmt_Call loc lhs)
        | _ \<Rightarrow> fail);
    expect SEMICOLON;
    return result
  })"

definition parse_assume_stmt :: "BabStatement Parser" where
  "parse_assume_stmt = with_loc (do {
    expect (KEYWORD KW_ASSUME);
    cond \<leftarrow> parse_term;
    expect SEMICOLON;
    return (\<lambda>loc. BabStmt_Assume loc cond)
  })"

definition parse_show_hide_stmt :: "BabStatement Parser" where
  "parse_show_hide_stmt = with_loc (do {
    showOrHide \<leftarrow> 
      (expect (KEYWORD KW_SHOW) \<then> return Show)
      <|> (expect (KEYWORD KW_HIDE) \<then> return Hide);
    name \<leftarrow> parse_dotted_name;
    expect SEMICOLON;
    return (\<lambda>loc. BabStmt_ShowHide loc showOrHide name)
  })"

fun parse_assert_stmt :: "nat \<Rightarrow> BabStatement Parser"
  and parse_if_stmt :: "nat \<Rightarrow> BabStatement Parser"
  and parse_while_stmt :: "nat \<Rightarrow> BabStatement Parser"
  and parse_stmt_fuelled :: "nat \<Rightarrow> BabStatement Parser"
where
  "parse_assert_stmt fuel = with_loc (do {
    expect (KEYWORD KW_ASSERT);
    maybeCond \<leftarrow> 
      (parse_restricted_term \<bind> return \<circ> Some) 
      <|> (expect STAR \<then> return None);
    proof \<leftarrow> 
      braces (many (delay (\<lambda>_. parse_stmt_fuelled fuel)))
      <|> (expect SEMICOLON \<then> return []);
    return (\<lambda>loc. BabStmt_Assert loc maybeCond proof)
  })"

| "parse_if_stmt fuel = with_loc (do {
    expect (KEYWORD KW_IF);
    cond \<leftarrow> parse_restricted_term;
    thenBlock \<leftarrow> braces (many (delay (\<lambda>_. parse_stmt_fuelled fuel)));
    elseBlock \<leftarrow>
      (do {
        expect (KEYWORD KW_ELSE);
        braces (many (delay (\<lambda>_. parse_stmt_fuelled fuel))) 
      })
      <|> (do {
        expect (KEYWORD KW_ELSE);
        look_ahead (expect (KEYWORD KW_IF));
        ifStmt \<leftarrow> parse_stmt_fuelled fuel;
        return [ifStmt]
      })
      <|> (return []);
    return (\<lambda>loc. BabStmt_If loc cond thenBlock elseBlock)
  })"

| "parse_while_stmt fuel = with_loc (do {
    expect (KEYWORD KW_WHILE);
    cond \<leftarrow> parse_restricted_term;
    attrs \<leftarrow> many parse_attribute;
    body \<leftarrow> many (delay (\<lambda>_. parse_stmt_fuelled fuel));
    return (\<lambda>loc. BabStmt_While loc cond attrs body)
  })"

| "parse_stmt_fuelled 0 = undefined"   (* out of fuel *)
| "parse_stmt_fuelled (Suc fuel) = 
    parse_var_decl_stmt
    <|> parse_fix_stmt
    <|> parse_obtain_stmt
    <|> parse_use_stmt
    <|> parse_swap_stmt
    <|> parse_return_stmt
    <|> parse_assignment_or_call_stmt
    <|> parse_assume_stmt
    <|> parse_show_hide_stmt
    <|> parse_assert_stmt fuel
    <|> parse_if_stmt fuel
    <|> parse_while_stmt fuel"


(* Top-level statement parser *)
definition parse_statement :: "BabStatement Parser" where
  "parse_statement = do {
    count \<leftarrow> get_num_tokens;
    parse_stmt_fuelled (Suc count)
  }"


(* DECLARATION PARSING *)

datatype EIG = Extern | Impure | Ghost

definition parse_const_decl :: "BabDeclaration Parser" where
  "parse_const_decl = with_loc (do {
    ghost \<leftarrow> (do {
      ghosts \<leftarrow> many (expect (KEYWORD KW_GHOST));
      return (ghosts \<noteq> [])
    });
    expect (KEYWORD KW_CONST);
    name \<leftarrow> parse_name;
    type \<leftarrow> optional (expect COLON) parse_type;
    rhs \<leftarrow> optional (expect EQUAL) parse_term;
    expect SEMICOLON;
    return (\<lambda>loc. BabDecl_Const \<lparr> DC_Location = loc,
                                  DC_Name = name,
                                  DC_Type = type,
                                  DC_Value = rhs,
                                  DC_Ghost = ghost \<rparr>)
  })"

definition parse_fun_arg :: "(string \<times> VarOrRef \<times> BabType) Parser" where
  "parse_fun_arg = do {
    ref0 \<leftarrow> optional (expect (KEYWORD KW_REF)) (return ());
    name \<leftarrow> parse_name;
    expect COLON;
    ref \<leftarrow> (if ref0 = None then optional (expect (KEYWORD KW_REF)) (return ()) else return ref0);
    type \<leftarrow> parse_type;
    return (name, if ref = None then Var else Ref, type)
  }"

definition parse_function_decl :: "BabDeclaration Parser" where
  "parse_function_decl = with_loc (do {
    markers \<leftarrow> many
      ((expect (KEYWORD KW_GHOST) \<then> return Ghost)
       <|> (expect (KEYWORD KW_EXTERN) \<then> return Extern)
       <|> (expect (KEYWORD KW_IMPURE) \<then> return Impure));
    let markerSet = set markers;
    expect (KEYWORD KW_FUNCTION);
    name \<leftarrow> parse_name;
    tyvars \<leftarrow> (angles (comma_list parse_name)) <|> (return []);
    args \<leftarrow> parens (comma_list parse_fun_arg);
    retType \<leftarrow> optional (expect COLON) parse_type;
    externName \<leftarrow> (if Extern \<in> markerSet then
      (optional (expect EQUAL) (do {
        t \<leftarrow> satisfy is_string_token;
        case t of STRING s \<Rightarrow> return s }))
      else return None);
    optional (expect SEMICOLON) (return ());
    attrs \<leftarrow> many parse_attribute;
    body \<leftarrow> optional_braces (many parse_statement);
    return (\<lambda>loc. BabDecl_Function \<lparr> DF_Location = loc,
                                     DF_Name = name,
                                     DF_TyArgs = tyvars,
                                     DF_TmArgs = args,
                                     DF_ReturnType = retType,
                                     DF_Body = body,
                                     DF_Attributes = attrs,
                                     DF_Ghost = (Ghost \<in> markerSet),
                                     DF_Extern = (Extern \<in> markerSet),
                                     DF_Impure = (Impure \<in> markerSet) \<rparr>)
  })"

definition parse_data_ctor :: "DataCtor Parser" where
  "parse_data_ctor = with_loc (do {
    name \<leftarrow> parse_name;
    payload \<leftarrow> optional (look_ahead (expect LPAREN <|> expect LBRACE)) parse_type;
    return (\<lambda>loc. (loc, name, payload))
  })"

definition parse_datatype_decl :: "BabDeclaration Parser" where
  "parse_datatype_decl = with_loc (do {
    expect (KEYWORD KW_DATATYPE);
    name \<leftarrow> parse_name;
    tyvars \<leftarrow> (angles (comma_list parse_name)) <|> (return []);
    expect EQUAL;
    ctors \<leftarrow> sep_by_1 parse_data_ctor (expect BAR);
    expect SEMICOLON;
    return (\<lambda>loc. BabDecl_Datatype \<lparr> DD_Location = loc,
                                     DD_Name = name,
                                     DD_TyArgs = tyvars,
                                     DD_Ctors = ctors \<rparr>)
  })"

definition parse_typedef_rhs :: "(BabType option \<times> AllocLevel) Parser" where
  "parse_typedef_rhs = do {
    expect EQUAL;
    ty \<leftarrow> parse_type;
    return (Some ty, AllocNever)
  }"

definition parse_typedef_alloc :: "(BabType option \<times> AllocLevel) Parser" where
  "parse_typedef_alloc = parens (
    (expect (KEYWORD KW_ALLOCATED) \<then> return (None, AllocIfNotDefault))
    <|> (expect (NAME ''allocated_always'') \<then> return (None, AllocAlways))
  )"

definition parse_typedef_decl :: "BabDeclaration Parser" where
  "parse_typedef_decl = with_loc (do {
    extern \<leftarrow> (do {
      externs \<leftarrow> many (expect (KEYWORD KW_EXTERN));
      return (externs \<noteq> [])
    });
    expect (KEYWORD KW_TYPE);
    name \<leftarrow> parse_name;
    tyvars \<leftarrow> (angles (comma_list parse_name)) <|> (return []);
    defnAlloc \<leftarrow> (if \<not>extern then parse_typedef_rhs else fail)
      <|> (parse_typedef_alloc)
      <|> (return (None, AllocNever));
    expect SEMICOLON;
    return (\<lambda>loc. BabDecl_Typedef \<lparr> DT_Location = loc,
                                    DT_Name = name,
                                    DT_TyArgs = tyvars,
                                    DT_Definition = fst defnAlloc,
                                    DT_Extern = extern,
                                    DT_AllocLevel = snd defnAlloc \<rparr>)
  })"

definition parse_decl :: "BabDeclaration Parser" where
  "parse_decl = parse_const_decl 
    <|> parse_function_decl 
    <|> parse_datatype_decl
    <|> parse_typedef_decl"


(* MODULE PARSING *)

definition parse_import :: "BabImport Parser" where
  "parse_import = with_loc (do {
    expect (KEYWORD KW_IMPORT);
    qualified \<leftarrow> (expect (NAME ''qualified'') \<then> return True) <|> (return False);
    name \<leftarrow> parse_dotted_name;
    alias \<leftarrow> (expect (NAME ''as'') \<then> parse_name) <|> (return name);
    expect SEMICOLON;
    return (\<lambda>loc. \<lparr> Imp_Location = loc,
                    Imp_ModuleName = name,
                    Imp_AliasName = alias,
                    Imp_Qualified = qualified \<rparr>)
  })"

(* this parses a complete module including the following eof *)
definition parse_module :: "BabModule Parser" where
  "parse_module = do {
    expect (KEYWORD KW_MODULE);
    name \<leftarrow> parse_dotted_name;
    interface_imports \<leftarrow> many parse_import;
    expect (KEYWORD KW_INTERFACE);
    interface \<leftarrow> braces (many parse_decl);
    impl_imports \<leftarrow> many parse_import;
    impl \<leftarrow> many parse_decl;
    eof;
    return \<lparr> Mod_Name = name,
             Mod_InterfaceImports = interface_imports,
             Mod_Interface = interface,
             Mod_ImplementationImports = impl_imports,
             Mod_Implementation = impl \<rparr>
  }"


(* FUNCTION TO RUN A PARSER *)

definition run_parser :: "'a Parser \<Rightarrow> string \<Rightarrow> (Location \<times> Token) list \<Rightarrow> 'a ParseResult" where
  "run_parser parser filename lexerResult =
    (let initialState = initial_parser_state filename lexerResult in
     parser initialState)"


(* POST-PARSING CHECKS *)

datatype PostParseError = 
  PPE_MixedArrayDimension
  | PPE_OldOutsidePostcondition
  | PPE_ReturnOutsidePostcondition
  | PPE_DataCtorWrongCase

fun array_dims_valid :: "BabDimension list \<Rightarrow> bool" where
  "array_dims_valid [] = True"
| "array_dims_valid (BabDim_Unknown # dims) = list_all (\<lambda>x. x = BabDim_Unknown) dims"
| "array_dims_valid (BabDim_Allocatable # dims) = list_all (\<lambda>x. x = BabDim_Allocatable) dims"
| "array_dims_valid (BabDim_Fixed _ # dims) = list_all (\<lambda>x. case x of
                                                 BabDim_Fixed _ \<Rightarrow> True
                                                 | _ \<Rightarrow> False) dims"

definition ttsize :: "BabType + BabTerm \<Rightarrow> nat"
  where "ttsize = case_sum bab_type_size bab_term_size"

(* note: these functions return PPE_OldOutsidePostcondition and/or 
   PPE_ReturnOutsidePostcondition if applicable. These must be filtered out
   afterwards if the term actually is part of a postcondition. *)
function post_parse_type :: "BabType \<Rightarrow> (Location \<times> PostParseError) list"
  and post_parse_term :: "BabTerm \<Rightarrow> (Location \<times> PostParseError) list"
where
  "post_parse_type (BabTy_Name _ _ types) = concat (map post_parse_type types)"
| "post_parse_type (BabTy_Bool _) = []"
| "post_parse_type (BabTy_FiniteInt _ _ _) = []"
| "post_parse_type (BabTy_MathInt _) = []"
| "post_parse_type (BabTy_MathReal _) = []"
| "post_parse_type (BabTy_Tuple _ types) = concat (map post_parse_type types)"
| "post_parse_type (BabTy_Record _ fieldTypes) = concat (map (post_parse_type \<circ> snd) fieldTypes)"
| "post_parse_type (BabTy_Array loc eltType dims) =
    post_parse_type eltType
    @ (if array_dims_valid dims then [] else [(loc, PPE_MixedArrayDimension)])
    @ (concat (map post_parse_term (concat (map array_dim_terms dims))))"

| "post_parse_term (BabTm_Literal _ lit) = 
    (case lit of
      BabLit_Array tms \<Rightarrow> concat (map post_parse_term tms)
      | _ \<Rightarrow> [])"
| "post_parse_term (BabTm_Name loc name types) = 
     (if name = ''return'' then [(loc, PPE_ReturnOutsidePostcondition)] else [])
     @ concat (map post_parse_type types)"
| "post_parse_term (BabTm_Cast _ ty tm) = post_parse_type ty @ post_parse_term tm"
| "post_parse_term (BabTm_If _ tm1 tm2 tm3) = 
    post_parse_term tm1 @ post_parse_term tm2 @ post_parse_term tm3"
| "post_parse_term (BabTm_Unop _ _ tm) = post_parse_term tm"
| "post_parse_term (BabTm_Binop _ tm lst) = post_parse_term tm
      @ concat (map (post_parse_term \<circ> snd) lst)"
| "post_parse_term (BabTm_Let _ _ tm1 tm2) = post_parse_term tm1 @ post_parse_term tm2"
| "post_parse_term (BabTm_Quantifier _ _ _ ty tm) = post_parse_type ty @ post_parse_term tm"
| "post_parse_term (BabTm_Call _ tm tms) = post_parse_term tm @ concat (map post_parse_term tms)"
| "post_parse_term (BabTm_Tuple _ tms) = concat (map post_parse_term tms)"
| "post_parse_term (BabTm_Record _ flds) = concat (map (post_parse_term \<circ> snd) flds)"
| "post_parse_term (BabTm_RecordUpdate _ tm flds) = post_parse_term tm
      @ concat (map (post_parse_term \<circ> snd) flds)"
| "post_parse_term (BabTm_TupleProj _ tm _) = post_parse_term tm"
| "post_parse_term (BabTm_RecordProj _ tm _) = post_parse_term tm"
| "post_parse_term (BabTm_ArrayProj _ tm tms) = post_parse_term tm 
      @ concat (map post_parse_term tms)"
| "post_parse_term (BabTm_Sizeof _ tm) = post_parse_term tm"
| "post_parse_term (BabTm_Allocated _ tm) = post_parse_term tm"
| "post_parse_term (BabTm_Old loc tm) = (loc, PPE_OldOutsidePostcondition) # post_parse_term tm"

  by pat_completeness auto

termination
proof (relation "measure ttsize")
  show "wf (measure ttsize)" by auto

next
  fix x loc name types
  show "x \<in> set types \<Longrightarrow>
       (Inl x, Inl (BabTy_Name loc name types)) \<in> measure ttsize"
    unfolding ttsize_def using bab_type_smaller_than_list
    by auto

next
  fix loc types x
  show "x \<in> set types \<Longrightarrow>
       (Inl x, Inl (BabTy_Tuple loc types)) \<in> measure ttsize"
    unfolding ttsize_def using bab_type_smaller_than_list by auto

next
  fix loc fieldTypes x
  show "x \<in> set fieldTypes \<Longrightarrow>
       (Inl (snd x), Inl (BabTy_Record loc fieldTypes)) \<in> measure ttsize"
    unfolding ttsize_def using bab_type_smaller_than_fieldlist
    by (metis bab_type_size.simps(7) eq_snd_iff in_measure old.sum.simps(5)
        plus_1_eq_Suc) 

next
  fix loc eltType dims
  show "(Inl eltType, Inl (BabTy_Array loc eltType dims)) \<in> measure ttsize"
    unfolding ttsize_def by auto

next
  fix loc eltType dims x
  show "x \<in> set (concat (map array_dim_terms dims)) \<Longrightarrow>
       (Inr x, Inl (BabTy_Array loc eltType dims)) \<in> measure ttsize"
    unfolding ttsize_def using bab_term_smaller_than_arraydim by force

next
  fix loc lit tms tm
  show "lit = BabLit_Array tms \<Longrightarrow>
       tm \<in> set tms \<Longrightarrow> 
       (Inr tm, Inr (BabTm_Literal loc lit)) \<in> measure ttsize"
    unfolding ttsize_def using bab_term_smaller_than_list by force

next
  fix ty types loc name
  show "ty \<in> set types \<Longrightarrow> (Inl ty, Inr (BabTm_Name loc name types)) \<in> measure ttsize"
    unfolding ttsize_def using bab_type_smaller_than_list by force

next
  fix loc ty tm
  show "(Inl ty, Inr (BabTm_Cast loc ty tm)) \<in> measure ttsize"
    unfolding ttsize_def by auto

next
  fix loc ty tm
  show "(Inr tm, Inr (BabTm_Cast loc ty tm)) \<in> measure ttsize"
    unfolding ttsize_def by auto

next
  fix loc tm1 tm2 tm3
  show "(Inr tm1, Inr (BabTm_If loc tm1 tm2 tm3)) \<in> measure ttsize"
    unfolding ttsize_def by auto

next
  fix loc tm1 tm2 tm3
  show "(Inr tm2, Inr (BabTm_If loc tm1 tm2 tm3)) \<in> measure ttsize"
    unfolding ttsize_def by auto

next
  fix loc tm1 tm2 tm3
  show "(Inr tm3, Inr (BabTm_If loc tm1 tm2 tm3)) \<in> measure ttsize"
    unfolding ttsize_def by auto

next
  fix loc op tm
  show "(Inr tm, Inr (BabTm_Unop loc op tm)) \<in> measure ttsize"
    unfolding ttsize_def by auto

next
  fix loc tm lst
  show "(Inr tm, Inr (BabTm_Binop loc tm lst)) \<in> measure ttsize"
    unfolding ttsize_def by auto

next
  fix loc tm
  fix lst :: "(BabBinop \<times> BabTerm) list"
  fix x :: "BabBinop \<times> BabTerm"
  assume Elem: "x \<in> set lst"
  show "(Inr (snd x), Inr (BabTm_Binop loc tm lst)) \<in> measure ttsize"
  proof (cases x)
    case (Pair op rhs)
    have "bab_term_size rhs < Suc (sum_list (map (bab_term_size \<circ> snd) lst))"
      unfolding ttsize_def using bab_term_smaller_than_fieldlist Pair Elem by auto
    thus ?thesis
      by (simp add: Pair ttsize_def)
  qed

next
  fix loc name tm1 tm2
  show "(Inr tm1, Inr (BabTm_Let loc name tm1 tm2)) \<in> measure ttsize"
    unfolding ttsize_def by auto

next
  fix loc name tm1 tm2
  show "(Inr tm2, Inr (BabTm_Let loc name tm1 tm2)) \<in> measure ttsize"
    unfolding ttsize_def by auto

next
  fix loc quant name ty tm
  show "(Inl ty, Inr (BabTm_Quantifier loc quant name ty tm)) \<in> measure ttsize"
    unfolding ttsize_def by auto

next
  fix loc quant name ty tm
  show "(Inr tm, Inr (BabTm_Quantifier loc quant name ty tm)) \<in> measure ttsize"
    unfolding ttsize_def by auto

next
  fix loc tm tms
  show "(Inr tm, Inr (BabTm_Call loc tm tms)) \<in> measure ttsize"
    unfolding ttsize_def by auto

next
  fix loc tm tms x
  show "x \<in> set tms \<Longrightarrow> (Inr x, Inr (BabTm_Call loc tm tms)) \<in> measure ttsize"
    unfolding ttsize_def using bab_term_smaller_than_list by force

next
  fix loc tms x
  show "x \<in> set tms \<Longrightarrow> (Inr x, Inr (BabTm_Tuple loc tms)) \<in> measure ttsize"
    unfolding ttsize_def using bab_term_smaller_than_list by force

next
  fix loc flds x
  show "x \<in> set flds \<Longrightarrow> (Inr (snd x), Inr (BabTm_Record loc flds)) \<in> measure ttsize"
    unfolding ttsize_def using bab_term_smaller_than_fieldlist
    by (metis bab_term_size.simps(11) in_measure old.sum.simps(6) plus_1_eq_Suc
        prod.exhaust_sel)

next
  fix loc tm flds 
  show "(Inr tm, Inr (BabTm_RecordUpdate loc tm flds)) \<in> measure ttsize"
    unfolding ttsize_def using bab_term_smaller_than_fieldlist by force

next
  fix loc tm flds x
  show "x \<in> set flds \<Longrightarrow> (Inr (snd x), Inr (BabTm_RecordUpdate loc tm flds)) \<in> measure ttsize"
    unfolding ttsize_def using bab_term_smaller_than_fieldlist
    by (metis add_Suc_shift bab_term_size.simps(12) in_measure old.sum.simps(6) plus_1_eq_Suc
        surjective_pairing trans_less_add2) 

next
  fix loc tm idx
  show "(Inr tm, Inr (BabTm_TupleProj loc tm idx)) \<in> measure ttsize"
    unfolding ttsize_def by auto

next
  fix loc tm name
  show "(Inr tm, Inr (BabTm_RecordProj loc tm name)) \<in> measure ttsize"
    unfolding ttsize_def by auto

next
  fix loc tm tms
  show "(Inr tm, Inr (BabTm_ArrayProj loc tm tms)) \<in> measure ttsize"
    unfolding ttsize_def by auto

next
  fix loc tm tms x
  show "x \<in> set tms \<Longrightarrow> (Inr x, Inr (BabTm_ArrayProj loc tm tms)) \<in> measure ttsize"
    unfolding ttsize_def using bab_term_smaller_than_list by force

next
  fix loc tm
  show "(Inr tm, Inr (BabTm_Sizeof loc tm)) \<in> measure ttsize"
    unfolding ttsize_def by auto

next
  fix loc tm
  show "(Inr tm, Inr (BabTm_Allocated loc tm)) \<in> measure ttsize"
    unfolding ttsize_def by auto

next
  fix loc tm
  show "(Inr tm, Inr (BabTm_Old loc tm)) \<in> measure ttsize"
    unfolding ttsize_def by auto

qed


fun post_parse_attribute :: "BabAttribute \<Rightarrow> (Location \<times> PostParseError) list" where
  "post_parse_attribute (BabAttr_Requires _ tm) = post_parse_term tm"
| "post_parse_attribute (BabAttr_Ensures _ tm) = 
    filter (\<lambda>(_, err). err \<notin> {PPE_ReturnOutsidePostcondition, PPE_OldOutsidePostcondition})
      (post_parse_term tm)"
| "post_parse_attribute (BabAttr_Invariant _ tm) = post_parse_term tm"
| "post_parse_attribute (BabAttr_Decreases _ tm) = post_parse_term tm"


fun post_parse_statement :: "BabStatement \<Rightarrow> (Location \<times> PostParseError) list" where
  "post_parse_statement (BabStmt_VarDecl _ _ _ maybeType maybeTerm) =
    case_option [] post_parse_type maybeType 
    @ case_option [] post_parse_term maybeTerm"
| "post_parse_statement (BabStmt_Fix _ _ ty) = post_parse_type ty"
| "post_parse_statement (BabStmt_Obtain _ _ ty tm) = post_parse_type ty @ post_parse_term tm"
| "post_parse_statement (BabStmt_Use _ tm) = post_parse_term tm"
| "post_parse_statement (BabStmt_Assign _ tm1 tm2) = post_parse_term tm1 @ post_parse_term tm2"
| "post_parse_statement (BabStmt_Swap _ tm1 tm2) = post_parse_term tm1 @ post_parse_term tm2"
| "post_parse_statement (BabStmt_Return _ maybeTm) = case_option [] post_parse_term maybeTm"
| "post_parse_statement (BabStmt_Assert _ maybeTm stmts) =
    case_option [] post_parse_term maybeTm
    @ concat (map post_parse_statement stmts)"
| "post_parse_statement (BabStmt_Assume _ tm) = post_parse_term tm"
| "post_parse_statement (BabStmt_If _ tm stmts1 stmts2) =
    post_parse_term tm
    @ concat (map post_parse_statement stmts1)
    @ concat (map post_parse_statement stmts2)"
| "post_parse_statement (BabStmt_While _ tm attrs stmts) =
    post_parse_term tm
    @ concat (map post_parse_attribute attrs)
    @ concat (map post_parse_statement stmts)"
| "post_parse_statement (BabStmt_Call _ tm) = post_parse_term tm"
| "post_parse_statement (BabStmt_ShowHide _ _ _) = []"


fun begins_with_capital :: "string \<Rightarrow> bool" where
  "begins_with_capital [] = False"
| "begins_with_capital (c # cs) = (CHR ''A'' \<le> c \<and> c \<le> CHR ''Z'')"


fun post_parse_data_ctor :: "Location \<times> string \<times> (BabType option) 
    \<Rightarrow> (Location \<times> PostParseError) list" where
"post_parse_data_ctor (loc, name, maybeTy) =
   (if begins_with_capital name then [] else [(loc, PPE_DataCtorWrongCase)])
   @ case_option [] post_parse_type maybeTy"


fun post_parse_declaration :: "BabDeclaration \<Rightarrow> (Location \<times> PostParseError) list" where
  "post_parse_declaration (BabDecl_Const cst) =
    case_option [] post_parse_type (DC_Type cst)
    @ case_option [] post_parse_term (DC_Value cst)"
| "post_parse_declaration (BabDecl_Function fun) =
    concat (map (\<lambda>(_,_,ty). post_parse_type ty) (DF_TmArgs fun))
    @ case_option [] post_parse_type (DF_ReturnType fun)
    @ case_option [] (concat \<circ> map post_parse_statement) (DF_Body fun)
    @ concat (map post_parse_attribute (DF_Attributes fun))"
| "post_parse_declaration (BabDecl_Datatype dtype) =
    concat (map post_parse_data_ctor (DD_Ctors dtype))"
| "post_parse_declaration (BabDecl_Typedef tydef) =
    case_option [] post_parse_type (DT_Definition tydef)"


fun post_parse_module :: "BabModule \<Rightarrow> (Location \<times> PostParseError) list" where
  "post_parse_module module =
    concat (map post_parse_declaration (Mod_Interface module))
    @ concat (map post_parse_declaration (Mod_Implementation module))"


(* Some basic tests *)

definition parser_fails :: "'a Parser \<Rightarrow> (Location \<times> Token) list \<Rightarrow> bool" where
  "parser_fails p toks = (case run_parser p ''Test.b'' toks of
    PR_Success _ _ _ \<Rightarrow> False
    | PR_Error _ \<Rightarrow> True)"

lemma parse_empty_term:
  shows "parser_fails parse_term []"
  by eval

lemma parse_empty_statement:
  shows "parser_fails parse_statement []"
  by eval


end
