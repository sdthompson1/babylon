theory BabParser
  imports Main Location BabSyntax BasicParser
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

(* helper to make an array type *)
fun make_array_type :: "(Location \<times> BabDimension list) \<Rightarrow> BabType \<Rightarrow> BabType" where
  "make_array_type (loc, dims) ty =
    BabTy_Array (merge_locations (bab_type_location ty) loc) ty dims"

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

(* Binop parsing *)
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

(* parse a binop of at least the given precedence *)
fun binop_of_at_least_prec :: "nat \<Rightarrow> (nat \<times> BabBinop) Parser" where
  "binop_of_at_least_prec min_prec = do {
    p \<leftarrow> parse_binop;
    (if fst p \<ge> min_prec then
      return p
    else
      fail)
    }"

(* helper to make a binop term *)
fun make_binop_term :: "BabTerm \<Rightarrow> BabBinop \<times> BabTerm \<Rightarrow> BabTerm" where
  "make_binop_term lhs (op, rhs) =
    BabTm_Binop (merge_locations (bab_term_location lhs) (bab_term_location rhs)) op lhs rhs"

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

(* Mutually recursive type and term parsing functions *)
fun parse_type_fuelled :: "nat \<Rightarrow> BabType Parser"
  and parse_basic_type :: "nat \<Rightarrow> BabType Parser"
  and parse_optional_tyargs :: "nat \<Rightarrow> BabType list Parser"
  and parse_name_type_pair :: "nat \<Rightarrow> (string \<times> BabType) Parser"
  and parse_array_suffix :: "nat \<Rightarrow> BabDimension list Parser"
  and parse_array_dimension :: "nat \<Rightarrow> BabDimension Parser"
  and parse_term_min :: "nat \<Rightarrow> nat \<Rightarrow> BabTerm Parser"
  and parse_operator_and_term :: "nat \<Rightarrow> nat \<Rightarrow> (BabBinop \<times> BabTerm) Parser"
  and parse_unop_expr :: "nat \<Rightarrow> BabTerm Parser"
  and parse_call_or_proj_expr :: "nat \<Rightarrow> BabTerm Parser"
  and parse_call_or_proj_suffix :: "nat \<Rightarrow> (BabTerm \<Rightarrow> BabTerm) Parser"
  and parse_primary_expr :: "nat \<Rightarrow> BabTerm Parser"
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
  <|> with_loc (     
        (expect (KEYWORD KW_BOOL) \<then> return BabTy_Bool)
    <|> (do {
          name \<leftarrow> parse_dotted_name;
          args \<leftarrow> parse_optional_tyargs fuel;
          return (\<lambda>loc. BabTy_Name loc name args)
        })
    <|> (expect (KEYWORD KW_I8) \<then> return (\<lambda>loc. BabTy_FiniteInt loc Signed IntBits_8))
    <|> (expect (KEYWORD KW_I16) \<then> return (\<lambda>loc. BabTy_FiniteInt loc Signed IntBits_16))
    <|> (expect (KEYWORD KW_I32) \<then> return (\<lambda>loc. BabTy_FiniteInt loc Signed IntBits_32))
    <|> (expect (KEYWORD KW_I64) \<then> return (\<lambda>loc. BabTy_FiniteInt loc Signed IntBits_64))
    <|> (expect (KEYWORD KW_U8) \<then> return (\<lambda>loc. BabTy_FiniteInt loc Unsigned IntBits_8))
    <|> (expect (KEYWORD KW_U16) \<then> return (\<lambda>loc. BabTy_FiniteInt loc Unsigned IntBits_16))
    <|> (expect (KEYWORD KW_U32) \<then> return (\<lambda>loc. BabTy_FiniteInt loc Unsigned IntBits_32))
    <|> (expect (KEYWORD KW_U64) \<then> return (\<lambda>loc. BabTy_FiniteInt loc Unsigned IntBits_64))
    <|> (expect (KEYWORD KW_INT) \<then> return BabTy_MathInt)
    <|> (expect (KEYWORD KW_REAL) \<then> return BabTy_MathReal)
    <|> (do {
          fieldTypes \<leftarrow> braces (comma_list (delay (\<lambda>_. parse_type_fuelled fuel)));
          return (\<lambda>loc. BabTy_Tuple loc fieldTypes)
         })
    <|> (do {
          fieldTypes \<leftarrow> braces (comma_list (parse_name_type_pair fuel));
          return (\<lambda>loc. BabTy_Record loc fieldTypes)
         })
    )"

(* Parse optional angle-brackets-type-list *)
| "parse_optional_tyargs fuel = 
    angles (comma_list (delay (\<lambda>_. parse_type_fuelled fuel)))
    <|> return []"

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
    <|> (delay (\<lambda>_. parse_term_min fuel 0) \<bind> (return \<circ> BabDim_Fixed))
    <|> (return BabDim_Unknown)"

(* Parse a term, followed by zero or more operator-term pairs at given precedence or higher *)
| "parse_term_min 0 _ = undefined"   (* out of fuel *)
| "parse_term_min (Suc fuel) min_prec = do {
    left \<leftarrow> parse_unop_expr fuel;
    others \<leftarrow> many (parse_operator_and_term fuel min_prec);
    return (foldl make_binop_term left others)
  }"

(* Parse operator-term pair at given precedence or higher *)
| "parse_operator_and_term fuel min_prec =
    do {
      p \<leftarrow> binop_of_at_least_prec min_prec;
      term \<leftarrow> parse_term_min fuel (Suc (fst p));
      return (snd p, term)
    }"

(* Parse unary operator expression *)
| "parse_unop_expr fuel = do {
    ops \<leftarrow> many (located parse_unop);
    tm \<leftarrow> parse_call_or_proj_expr fuel;
    return (foldr make_unop_term ops tm)
  }"

(* Parse function call, field projection or array projection *)
| "parse_call_or_proj_expr fuel = do {
    tm \<leftarrow> parse_primary_expr fuel;
    suffixes \<leftarrow> many (parse_call_or_proj_suffix fuel);
    return (foldl (\<lambda>tm f. f tm) tm suffixes)
  }"

| "parse_call_or_proj_suffix fuel =
    (do {
      loc_and_args \<leftarrow> located (parens (comma_list (delay (\<lambda>_. parse_term_min fuel 0))));
      return (\<lambda>tm. BabTm_Call (merge_locations (bab_term_location tm) (fst loc_and_args))
                              tm
                              (snd loc_and_args))
    })
  <|> (do {
        look_ahead (expect LBRACE);
        loc_and_arg \<leftarrow> located (delay (\<lambda>_. parse_primary_expr fuel));
        return (\<lambda>tm. BabTm_Call (merge_locations (bab_term_location tm) (fst loc_and_arg))
                                tm
                                [snd loc_and_arg])
      })
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
        loc_and_idxs \<leftarrow> located (brackets (comma_list (delay (\<lambda>_. parse_term_min fuel 0))));
        return (\<lambda>tm. BabTm_ArrayProj (merge_locations (bab_term_location tm) (fst loc_and_idxs))
                                     tm
                                     (snd loc_and_idxs))
      })"

(* Parse a primary expression, e.g. variable name, literal, parenthesized expression *)
(* TODO: Finish this - add more cases *)
| "parse_primary_expr fuel =
    (parens (delay (\<lambda>_. parse_term_min fuel 0)))
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
          tm1 \<leftarrow> delay (\<lambda>_. parse_term_min fuel 0);
          expect (KEYWORD KW_THEN);
          tm2 \<leftarrow> delay (\<lambda>_. parse_term_min fuel 0);
          expect (KEYWORD KW_ELSE);
          tm3 \<leftarrow> delay (\<lambda>_. parse_term_min fuel 0);
          return (\<lambda>loc. BabTm_If loc tm1 tm2 tm3)
        })
    <|> (do {
          expect (KEYWORD KW_LET);
          name \<leftarrow> parse_name;
          expect EQUAL;
          tm1 \<leftarrow> delay (\<lambda>_. parse_term_min fuel 0);
          expect (KEYWORD KW_IN);
          tm2 \<leftarrow> delay (\<lambda>_. parse_term_min fuel 0);
          return (\<lambda>loc. BabTm_Let loc name tm1 tm2)
        })
    <|> (do {
          quant \<leftarrow> (expect (KEYWORD KW_FORALL) <|> expect (KEYWORD KW_EXISTS));
          name_ty \<leftarrow> parens (parse_name_type_pair fuel);
          tm \<leftarrow> delay (\<lambda>_. parse_term_min fuel 0);
          let q = (if quant = KEYWORD KW_FORALL then Quant_Forall else Quant_Exists);
          return (\<lambda>loc. BabTm_Quantifier loc q (fst name_ty) (snd name_ty) tm)
        })
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
    parse_term_min (Suc count) 0
  }"


(* Run a particular parser *)
definition run_parser :: "'a Parser \<Rightarrow> string \<Rightarrow> (Location \<times> Token) list \<Rightarrow> 'a ParseResult" where
  "run_parser parser filename lexerResult =
    (let initialState = initial_parser_state filename lexerResult in
     parser initialState)"


end
