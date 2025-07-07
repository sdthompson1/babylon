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
    ((tokens, length tokens), 
     parser_next_fn, 
     parser_fuel_fn, 
     Location filename 1 1 1 1,
     Location filename 1 1 1 1)"


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

definition comma_list_no_trailing :: "'a Parser \<Rightarrow> 'a list Parser" where
  "comma_list_no_trailing p = sep_by p (expect COMMA)"


definition parse_name :: "string Parser" where
  "parse_name = do {
    tok \<leftarrow> satisfy is_name_token;
    case tok of
      NAME n \<Rightarrow> return n
    | _ \<Rightarrow> undefined
  }"

definition parse_nat_num :: "nat Parser" where
  "parse_nat_num = do {
    t \<leftarrow> satisfy is_nat_num_token;
    case t of NAT_NUM n \<Rightarrow> return n
  }"



(* PATTERN PARSING *)

fun begins_with_capital :: "string \<Rightarrow> bool" where
  "begins_with_capital [] = False"
| "begins_with_capital (c # cs) = (CHR ''A'' \<le> c \<and> c \<le> CHR ''Z'')"

fun parse_pattern_fuelled :: "nat \<Rightarrow> BabPattern Parser" where
  "parse_pattern_fuelled 0 = undefined"  (* out of fuel *)
| "parse_pattern_fuelled (Suc fuel) = 
   parens (delay (\<lambda>_. parse_pattern_fuelled fuel))
   <|> with_loc ((do {
    ref \<leftarrow> (expect (KEYWORD KW_REF) \<then> return Ref) <|> return Var;
    name \<leftarrow> parse_name;
    if begins_with_capital name then (do {
      (if ref = Ref then fail else return ());
      payload \<leftarrow> (do {
        look_ahead (expect LBRACE <|> expect LPAREN);
        pat \<leftarrow> parse_pattern_fuelled fuel;
        return (Some pat)
      }) <|> (return None);
      return (\<lambda>loc. BabPat_Variant loc name payload)
    }) 
    else if (List.member name (CHR ''.'')) then fail
    else (return (\<lambda>loc. BabPat_Var loc ref name))
  })
  <|> (do {
    expect UNDERSCORE;
    return (\<lambda>loc. BabPat_Wildcard loc)
  })
  <|> (do {
    expect (KEYWORD KW_TRUE);
    return (\<lambda>loc. BabPat_Bool loc True)
  })
  <|> (do {
    expect (KEYWORD KW_FALSE);
    return (\<lambda>loc. BabPat_Bool loc False)
  })
  <|> (do {
    expect MINUS;
    n \<leftarrow> parse_nat_num;
    return (\<lambda>loc. BabPat_Int loc (-(of_nat n)))
  })
  <|> (do {
    n \<leftarrow> parse_nat_num;
    return (\<lambda>loc. BabPat_Int loc (of_nat n))
  })
  <|> (do {
    pats \<leftarrow> braces (comma_list (delay (\<lambda>_. parse_pattern_fuelled fuel)));
    return (\<lambda>loc. BabPat_Tuple loc pats)
  })
  <|> (do {
    namePatPairs \<leftarrow> braces (comma_list (do {
      name \<leftarrow> parse_name;
      expect EQUAL;
      pat \<leftarrow> parse_pattern_fuelled fuel;
      return (name, pat)
    }));
    return (\<lambda>loc. BabPat_Record loc namePatPairs)
  }))"

definition parse_pattern :: "BabPattern Parser" where
  "parse_pattern = do {
    count \<leftarrow> get_num_tokens;
    parse_pattern_fuelled (Suc count)
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
    n \<leftarrow> parse_nat_num;
    return (BabLit_Int (of_nat n))
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
   int literal. This avoids problems with the most negative integer.
   (If the resulting negative integer would be out of range, this returns None.) *)
fun make_unop_term :: "Location \<times> BabUnop \<Rightarrow> BabTerm option \<Rightarrow> BabTerm option" where
  "make_unop_term _ None = None"
| "make_unop_term (loc1, BabUnop_Negate) (Some (BabTm_Literal loc2 (BabLit_Int i)))
    = (if i \<le> 2 ^ 63 then Some (BabTm_Literal (merge_locations loc1 loc2) (BabLit_Int (-i)))
       else None)"
| "make_unop_term (loc, op) (Some tm)
    = Some (BabTm_Unop (merge_locations loc (bab_term_location tm)) op tm)"


(* Helper for making tuple or record terms *)
fun make_tuple_or_record :: "BabTerm option \<Rightarrow> (string \<times> BabTerm) list \<Rightarrow> BabTerm list
                             \<Rightarrow> (Location \<Rightarrow> BabTerm) Parser" where
  "make_tuple_or_record (Some with) flds [] = return (\<lambda>loc. BabTm_RecordUpdate loc with flds)"
| "make_tuple_or_record (Some _) _ (tm#_) = fail_at (bab_term_location tm)"
| "make_tuple_or_record None flds [] = return (\<lambda>loc. BabTm_Record loc flds)"
| "make_tuple_or_record None [] tms = return (\<lambda>loc. BabTm_Tuple loc tms)"
| "make_tuple_or_record None ((_,tm1)#_) (tm2#_) = 
    fail_at (max_location (bab_term_location tm1) (bab_term_location tm2))" 


(* Helpers for case sums *)
fun case_sum_3 :: "('a \<Rightarrow> 'r) \<Rightarrow> ('b \<Rightarrow> 'r) \<Rightarrow> ('c \<Rightarrow> 'r)
                    \<Rightarrow> ('a + 'b + 'c \<Rightarrow> 'r)" where
  "case_sum_3 a b c = case_sum a (case_sum b c)"

fun case_sum_5 :: "('a \<Rightarrow> 'r) \<Rightarrow> ('b \<Rightarrow> 'r) \<Rightarrow> ('c \<Rightarrow> 'r) \<Rightarrow> ('d \<Rightarrow> 'r) \<Rightarrow> ('e \<Rightarrow> 'r)
                    \<Rightarrow> ('a + 'b + 'c + 'd + 'e \<Rightarrow> 'r)" where
  "case_sum_5 a b c d e = case_sum a (case_sum b (case_sum c (case_sum d e)))"


(* Note: a "restricted" term is one that cannot contain the curly-brace function
   call syntax (e.g. `f{1,2,3}`). This is used to avoid ambiguities in certain
   contexts e.g. if-conditions. It is our equivalent of the following Rust issue:
   https://github.com/rust-lang/rust/issues/50090. *)
datatype Restrict = Restricted | Unrestricted

(* Mutually recursive type and term parsing functions *)

function parse_type_fuelled :: "nat \<Rightarrow> BabType Parser"
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
  and parse_tuple_or_record :: "nat \<Rightarrow> BabTerm option \<times> (string \<times> BabTerm) list \<times> BabTerm list \<Rightarrow> 
                                (BabTerm option \<times> (string \<times> BabTerm) list \<times> BabTerm list) Parser"
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
| "parse_basic_type 0 = undefined"
| "parse_basic_type (Suc fuel) =
  (parens (delay (\<lambda>_. parse_type_fuelled fuel)))
  <|> parse_numeric_type
  <|> with_loc (
        (expect (KEYWORD KW_BOOL) \<then> return BabTy_Bool)
    <|> (do {
          name \<leftarrow> parse_name;
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
| "parse_optional_tyargs 0 = undefined"
| "parse_optional_tyargs (Suc fuel) = 
    angles (comma_list (delay (\<lambda>_. parse_type_fuelled fuel)))
      <|> return []"

(* Parse a "name : type" pair *)
| "parse_name_type_pair 0 = undefined"
| "parse_name_type_pair (Suc fuel) = do {
    name \<leftarrow> parse_name;
    expect COLON;
    ty \<leftarrow> parse_type_fuelled fuel;
    return (name, ty)
   }"


(* Parse an array-dimension-list in brackets *)
| "parse_array_suffix 0 = undefined"
| "parse_array_suffix (Suc fuel) = 
    brackets (comma_list_no_trailing (parse_array_dimension fuel))"

(* Parse a single array dimension *)
| "parse_array_dimension 0 = undefined"
| "parse_array_dimension (Suc fuel) =
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
| "parse_operator_and_term 0 _ _ = undefined"
| "parse_operator_and_term (Suc fuel) min_prec restrict =
    do {
      p \<leftarrow> binop_of_at_least_prec min_prec;
      term \<leftarrow> parse_term_min fuel (Suc (fst p)) restrict;
      return (snd p, term)
    }"

(* Parse unary operator expression *)
| "parse_unop_expr 0 _ = undefined"
| "parse_unop_expr (Suc fuel) restrict = do {
    ops \<leftarrow> many (located parse_unop);
    tm \<leftarrow> parse_call_or_proj_expr fuel restrict;
    let maybeResult = foldr make_unop_term ops (Some tm);
    case maybeResult of
      None \<Rightarrow> fail
      | Some result \<Rightarrow> return result
  }"

(* Parse function call, field projection or array projection *)
| "parse_call_or_proj_expr 0 _ = undefined"
| "parse_call_or_proj_expr (Suc fuel) restrict = do {
    tm \<leftarrow> parse_primary_expr fuel restrict;
    suffixes \<leftarrow> many (parse_call_or_proj_suffix fuel restrict);
    return (foldl (\<lambda>tm f. f tm) tm suffixes)
  }"

(* TODO: Accepting <Tyargs> after field-proj or tuple-proj is a temporary
hack and will be removed at some point *)
| "parse_call_or_proj_suffix 0 _ = undefined"
| "parse_call_or_proj_suffix (Suc fuel) restrict =
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
        loc_and_fld \<leftarrow> located parse_name;
        (case loc_and_fld of
          (loc, n) \<Rightarrow>
            return (\<lambda>tm. BabTm_RecordProj (merge_locations (bab_term_location tm) loc)
                                          tm
                                          n))
      })
  <|> (do {
        loc_and_idxs \<leftarrow> located (brackets (comma_list_no_trailing (delay (\<lambda>_. parse_term_min fuel 0 Unrestricted))));
        return (\<lambda>tm. BabTm_ArrayProj (merge_locations (bab_term_location tm) (fst loc_and_idxs))
                                     tm
                                     (snd loc_and_idxs))
      })"

(* Parse a primary expression, e.g. variable name, literal, parenthesized expression *)
| "parse_primary_expr 0 _ = undefined"
| "parse_primary_expr (Suc fuel) restrict =
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
          tm1 \<leftarrow> parse_term_min fuel 0 Unrestricted;
          expect (KEYWORD KW_THEN);
          tm2 \<leftarrow> parse_term_min fuel 0 Unrestricted;
          expect (KEYWORD KW_ELSE);
          tm3 \<leftarrow> parse_term_min fuel 0 restrict;
          return (\<lambda>loc. BabTm_If loc tm1 tm2 tm3)
        })
    <|> (do {
          expect (KEYWORD KW_MATCH);
          scrut \<leftarrow> parse_term_min fuel 0 Restricted;
          arms \<leftarrow> braces (many (do {
            expect (KEYWORD KW_CASE);
            pat \<leftarrow> parse_pattern;
            expect EQUAL_GREATER;
            rhs \<leftarrow> parse_term_min fuel 0 Unrestricted;
            optional (expect SEMICOLON);
            return (pat, rhs)
          }));
          return (\<lambda>loc. BabTm_Match loc scrut arms)
        })
    <|> (do {
          expect (KEYWORD KW_LET);
          name \<leftarrow> parse_name;
          expect EQUAL;
          tm1 \<leftarrow> parse_term_min fuel 0 Unrestricted;
          expect (KEYWORD KW_IN);
          tm2 \<leftarrow> parse_term_min fuel 0 restrict;
          return (\<lambda>loc. BabTm_Let loc name tm1 tm2)
        })
    <|> (do {
          quant \<leftarrow> (expect (KEYWORD KW_FORALL) <|> expect (KEYWORD KW_EXISTS));
          name_ty \<leftarrow> parens (delay (\<lambda>_. parse_name_type_pair fuel));
          tm \<leftarrow> parse_term_min fuel 0 Unrestricted;
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
          expect LBRACE;
          param \<leftarrow> parse_tuple_or_record fuel (None, [], []);
          case param of (with, flds, terms) \<Rightarrow>
            make_tuple_or_record with (List.rev flds) (List.rev terms)
        })
   )"

| "parse_tuple_or_record 0 _ = undefined"
| "parse_tuple_or_record (Suc fuel) param =
    (case param of (with, flds, terms) \<Rightarrow>
      (optional (expect COMMA) \<then> expect RBRACE \<then> return param)
      <|> (do {
        (if flds \<noteq> [] \<or> terms \<noteq> [] then expect COMMA else return COMMA);
        maybeName \<leftarrow> optional (do {
          name \<leftarrow> parse_name;
          expect EQUAL;
          return name
        });
        term \<leftarrow> parse_term_min fuel 0 Unrestricted;
        foundWith \<leftarrow> (if with = None \<and> maybeName = None
          then optional (expect (KEYWORD KW_WITH)) else return None);
        let newParam =
          (if foundWith \<noteq> None then (Some term, flds, terms)
          else case maybeName of
            Some name \<Rightarrow> (with, (name,term)#flds, terms)
            | None \<Rightarrow> (with, flds, term#terms));
        parse_tuple_or_record fuel newParam
      }))"

  by pat_completeness auto
  termination by (relation "measure 
    (case_sum_5
      (case_sum
        (case_sum_3 id id id)
        (case_sum_3 id id id))
      (case_sum_3
        (\<lambda>x. case x of (a,_,_) \<Rightarrow> a)
        (\<lambda>x. case x of (a,_,_) \<Rightarrow> a)
        fst)
      (case_sum fst fst)
      fst
      (\<lambda>x. case x of (a,_,_,_) \<Rightarrow> a))", 
    auto)


(* This should be more than enough fuel for the above *)
(* (Also note that if fuel runs out, it will cause the compiler to
   crash; it will not cause incorrect output to be generated.) *)
definition parser_required_fuel :: "nat Parser" where
  "parser_required_fuel = do {
    count \<leftarrow> get_num_tokens;
    return (16*(count+1))
  }"


(* Top-level type and term parsers *)
definition parse_type :: "BabType Parser" where
  "parse_type = do {
    fuel \<leftarrow> parser_required_fuel;
    parse_type_fuelled fuel
  }"

definition parse_term :: "BabTerm Parser" where
  "parse_term = do {
    fuel \<leftarrow> parser_required_fuel;
    parse_term_min fuel 0 Unrestricted
  }"

definition parse_restricted_term :: "BabTerm Parser" where
  "parse_restricted_term = do {
    fuel \<leftarrow> parser_required_fuel;
    parse_term_min fuel 0 Restricted
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

definition ghost_prefix :: "GhostOrNot Parser" where
  "ghost_prefix = (expect (KEYWORD KW_GHOST) \<then> return Ghost) <|> (return NotGhost)"

definition parse_var_decl_stmt :: "BabStatement Parser" where
  "parse_var_decl_stmt = with_loc (do {
    ghost \<leftarrow> ghost_prefix;
    varOrRef \<leftarrow> (expect (KEYWORD KW_REF) \<then> return Ref)
                <|> (expect (KEYWORD KW_VAR) \<then> return Var);
    name \<leftarrow> parse_name;
    maybeType \<leftarrow> optional (expect COLON \<then> parse_type);
    maybeRhs \<leftarrow> (do {
      expect EQUAL;
      tm \<leftarrow> parse_term;
      return (Some tm)
    }) <|> (if varOrRef = Ref then fail else return None);
    expect SEMICOLON;
    return (\<lambda>loc. BabStmt_VarDecl loc ghost name varOrRef maybeType maybeRhs)
  })"

definition parse_fix_stmt :: "BabStatement Parser" where
  "parse_fix_stmt = with_loc (do {
    ghost_prefix;
    expect (KEYWORD KW_FIX);
    name \<leftarrow> parse_name;
    expect COLON;
    ty \<leftarrow> parse_type;
    expect SEMICOLON;
    return (\<lambda>loc. BabStmt_Fix loc name ty)
  })"

definition parse_obtain_stmt :: "BabStatement Parser" where
  "parse_obtain_stmt = with_loc (do {
    ghost_prefix;
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
    ghost_prefix;
    expect (KEYWORD KW_USE);
    tm \<leftarrow> parse_term;
    expect SEMICOLON;
    return (\<lambda>loc. BabStmt_Use loc tm)
  })"

definition parse_swap_stmt :: "BabStatement Parser" where
  "parse_swap_stmt = with_loc (do {
    ghost \<leftarrow> ghost_prefix;
    expect (KEYWORD KW_SWAP);
    lhs \<leftarrow> parse_term;
    expect COMMA;
    rhs \<leftarrow> parse_term;
    expect SEMICOLON;
    return (\<lambda>loc. BabStmt_Swap loc ghost lhs rhs)
  })"

definition parse_return_stmt :: "BabStatement Parser" where
  "parse_return_stmt = with_loc (do {
    ghost \<leftarrow> ghost_prefix;
    expect (KEYWORD KW_RETURN);
    maybeTerm \<leftarrow> optional parse_term;
    expect SEMICOLON;
    return (\<lambda>loc. BabStmt_Return loc ghost maybeTerm)
  })"

(* both of these begin with a term (as opposed to a keyword) *)
(* also, they must start with LPAREN or NAME *)
definition parse_assignment_or_call_stmt :: "BabStatement Parser" where
  "parse_assignment_or_call_stmt = with_loc (do {
    ghost \<leftarrow> ghost_prefix;
    look_ahead (expect LPAREN <|> satisfy is_name_token);
    lhs \<leftarrow> parse_term;
    result \<leftarrow> (do {
      expect EQUAL;
      rhs \<leftarrow> parse_term;
      return (\<lambda>loc. BabStmt_Assign loc ghost lhs rhs)
    }) <|> 
      (case lhs of
        BabTm_Call _ _ _ \<Rightarrow> return (\<lambda>loc. BabStmt_Call loc ghost lhs)
        | _ \<Rightarrow> fail);
    expect SEMICOLON;
    return result
  })"

definition parse_assume_stmt :: "BabStatement Parser" where
  "parse_assume_stmt = with_loc (do {
    ghost_prefix;
    expect (KEYWORD KW_ASSUME);
    cond \<leftarrow> parse_term;
    expect SEMICOLON;
    return (\<lambda>loc. BabStmt_Assume loc cond)
  })"

definition parse_show_hide_stmt :: "BabStatement Parser" where
  "parse_show_hide_stmt = with_loc (do {
    ghost_prefix;
    showOrHide \<leftarrow> 
      (expect (KEYWORD KW_SHOW) \<then> return Show)
      <|> (expect (KEYWORD KW_HIDE) \<then> return Hide);
    name \<leftarrow> parse_name;
    expect SEMICOLON;
    return (\<lambda>loc. BabStmt_ShowHide loc showOrHide name)
  })"

fun parse_assert_stmt :: "nat \<Rightarrow> BabStatement Parser"
  and parse_if_stmt :: "nat \<Rightarrow> BabStatement Parser"
  and parse_match_stmt :: "nat \<Rightarrow> BabStatement Parser"
  and parse_while_stmt :: "nat \<Rightarrow> BabStatement Parser"
  and parse_stmt_fuelled :: "nat \<Rightarrow> BabStatement Parser"
  and parse_stmts_fuelled :: "nat \<Rightarrow> BabStatement list Parser"
where
  "parse_assert_stmt fuel = with_loc (do {
    ghost_prefix;
    expect (KEYWORD KW_ASSERT);
    maybeCond \<leftarrow> 
      (parse_restricted_term \<bind> return \<circ> Some) 
      <|> (expect STAR \<then> return None);
    proof \<leftarrow> 
      braces (delay (\<lambda>_. parse_stmts_fuelled fuel))
        <|> (expect SEMICOLON \<then> return []);
    return (\<lambda>loc. BabStmt_Assert loc maybeCond proof)
  })"

| "parse_if_stmt fuel = with_loc (do {
    ghost \<leftarrow> ghost_prefix;
    expect (KEYWORD KW_IF);
    cond \<leftarrow> parse_restricted_term;
    thenBlock \<leftarrow> braces (delay (\<lambda>_. parse_stmts_fuelled fuel));
    elseBlock \<leftarrow>
      (do {
        expect (KEYWORD KW_ELSE);
        braces (delay (\<lambda>_. parse_stmts_fuelled fuel))
      })
      <|> (do {
        expect (KEYWORD KW_ELSE);
        look_ahead (expect (KEYWORD KW_IF));
        ifStmt \<leftarrow> parse_stmt_fuelled fuel;
        return [ifStmt]
      })
      <|> (return []);
    return (\<lambda>loc. BabStmt_If loc ghost cond thenBlock elseBlock)
  })"

| "parse_match_stmt fuel = with_loc (do {
    ghost \<leftarrow> ghost_prefix;
    expect (KEYWORD KW_MATCH);
    scrut \<leftarrow> parse_restricted_term;
    arms \<leftarrow> braces (many (do {
      expect (KEYWORD KW_CASE);
      pat \<leftarrow> parse_pattern;
      expect EQUAL_GREATER;
      stmts \<leftarrow> parse_stmts_fuelled fuel;
      return (pat, stmts)
    }));
    return (\<lambda>loc. BabStmt_Match loc ghost scrut arms)
  })"

| "parse_while_stmt fuel = with_loc (do {
    ghost \<leftarrow> ghost_prefix;
    expect (KEYWORD KW_WHILE);
    cond \<leftarrow> parse_restricted_term;
    attrs \<leftarrow> many parse_attribute;
    body \<leftarrow> braces (delay (\<lambda>_. parse_stmts_fuelled fuel));
    return (\<lambda>loc. BabStmt_While loc ghost cond attrs body)
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
    <|> parse_match_stmt fuel
    <|> parse_while_stmt fuel"

| "parse_stmts_fuelled fuel = do {
    maybeStmts \<leftarrow> many (delay (\<lambda>_.
      (parse_stmt_fuelled fuel \<bind> return \<circ> Some)
        <|> (expect SEMICOLON \<then> return None)));
    return (List.map_filter id maybeStmts)
  }"


(* Top-level statement parser *)
definition parse_statements :: "BabStatement list Parser" where
  "parse_statements = do {
    count \<leftarrow> get_num_tokens;
    parse_stmts_fuelled (Suc count)
  }"


(* DECLARATION PARSING *)

datatype EIG = Extern | Impure | GhostMarker

definition parse_const_decl :: "BabDeclaration Parser" where
  "parse_const_decl = with_loc (do {
    ghost \<leftarrow> (do {
      ghosts \<leftarrow> many (expect (KEYWORD KW_GHOST));
      return (if ghosts = [] then NotGhost else Ghost)
    });
    expect (KEYWORD KW_CONST);
    name \<leftarrow> parse_name;
    type \<leftarrow> optional (expect COLON \<then> parse_type);
    rhs \<leftarrow> optional (expect EQUAL \<then> parse_term);
    expect SEMICOLON;
    return (\<lambda>loc. BabDecl_Const \<lparr> DC_Location = loc,
                                  DC_Name = name,
                                  DC_Type = type,
                                  DC_Value = rhs,
                                  DC_Ghost = ghost \<rparr>)
  })"

definition parse_fun_arg :: "(string \<times> VarOrRef \<times> BabType) Parser" where
  "parse_fun_arg = do {
    ref0 \<leftarrow> optional (expect (KEYWORD KW_REF));
    name \<leftarrow> parse_name;
    expect COLON;
    ref \<leftarrow> (if ref0 = None then optional (expect (KEYWORD KW_REF)) else return ref0);
    type \<leftarrow> parse_type;
    return (name, if ref = None then Var else Ref, type)
  }"

definition parse_function_decl :: "BabDeclaration Parser" where
  "parse_function_decl = with_loc (do {
    markers \<leftarrow> many
      ((expect (KEYWORD KW_GHOST) \<then> return GhostMarker)
       <|> (expect (KEYWORD KW_EXTERN) \<then> return Extern)
       <|> (expect (KEYWORD KW_IMPURE) \<then> return Impure));
    let markerSet = set markers;
    expect (KEYWORD KW_FUNCTION);
    name \<leftarrow> parse_name;
    tyvars \<leftarrow> (angles (comma_list parse_name)) <|> (return []);
    args \<leftarrow> parens (comma_list parse_fun_arg);
    retType \<leftarrow> optional (expect COLON \<then> parse_type);
    externName \<leftarrow> (if Extern \<in> markerSet then
      (optional (do {
        expect EQUAL;
        t \<leftarrow> satisfy is_string_token;
        case t of STRING s \<Rightarrow> return s }))
      else return None);
    optional (expect SEMICOLON);
    attrs \<leftarrow> many parse_attribute;
    body \<leftarrow> optional (braces parse_statements);
    return (\<lambda>loc. BabDecl_Function \<lparr> DF_Location = loc,
                                     DF_Name = name,
                                     DF_TyArgs = tyvars,
                                     DF_TmArgs = args,
                                     DF_ReturnType = retType,
                                     DF_Body = body,
                                     DF_Attributes = attrs,
                                     DF_Ghost = (if GhostMarker \<in> markerSet 
                                                  then Ghost
                                                  else NotGhost),
                                     DF_Extern = (Extern \<in> markerSet),
                                     DF_Impure = (Impure \<in> markerSet) \<rparr>)
  })"

definition parse_data_ctor :: "DataCtor Parser" where
  "parse_data_ctor = with_loc (do {
    name \<leftarrow> parse_name;
    payload \<leftarrow> optional (do {
      look_ahead (expect LPAREN <|> expect LBRACE);
      parse_type
    });
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
    name \<leftarrow> parse_name;
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
    name \<leftarrow> parse_name;
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

(* For historical reasons, the following are considered parsing errors (rather than,
   say, typechecking errors). The distinction is important for fuzz testing. *)

datatype PostParseError = 
  PPE_MixedArrayDimension
  | PPE_OldOutsidePostcondition
  | PPE_OldUsedWithReturn
  | PPE_DataCtorWrongCase

fun array_dims_valid :: "BabDimension list \<Rightarrow> bool" where
  "array_dims_valid [] = True"
| "array_dims_valid (BabDim_Unknown # dims) = list_all (\<lambda>x. x = BabDim_Unknown) dims"
| "array_dims_valid (BabDim_Allocatable # dims) = list_all (\<lambda>x. x = BabDim_Allocatable) dims"
| "array_dims_valid (BabDim_Fixed _ # dims) = list_all (\<lambda>x. case x of
                                                 BabDim_Fixed _ \<Rightarrow> True
                                                 | _ \<Rightarrow> False) dims"

abbreviation ttsize :: "BabType + BabTerm \<Rightarrow> nat"
  where "ttsize \<equiv> case_sum bab_type_size bab_term_size"

abbreviation bool_typeterm_to_typeterm :: "bool \<times> BabType + bool \<times> BabTerm \<Rightarrow> BabType + BabTerm"
  where "bool_typeterm_to_typeterm \<equiv> map_sum snd snd"

abbreviation bool_ttsize :: "bool \<times> BabType + bool \<times> BabTerm \<Rightarrow> nat"
  where "bool_ttsize \<equiv> ttsize \<circ> bool_typeterm_to_typeterm"


(* note: these functions return PPE_OldOutsidePostcondition errors, if any "old"
   term is found. These must be filtered out afterwards if the term actually 
   is part of a postcondition. *)
function post_parse_type :: "bool \<Rightarrow> BabType \<Rightarrow> (Location \<times> PostParseError) list"
  and post_parse_term :: "bool \<Rightarrow> BabTerm \<Rightarrow> (Location \<times> PostParseError) list"
where
  "post_parse_type old (BabTy_Name loc name types) = concat (map (post_parse_type old) types)"
| "post_parse_type _ (BabTy_Bool _) = []"
| "post_parse_type _ (BabTy_FiniteInt _ _ _) = []"
| "post_parse_type _ (BabTy_MathInt _) = []"
| "post_parse_type _ (BabTy_MathReal _) = []"
| "post_parse_type old (BabTy_Tuple _ types) = concat (map (post_parse_type old) types)"
| "post_parse_type old (BabTy_Record _ fieldTypes) = concat (map (post_parse_type old \<circ> snd) fieldTypes)"
| "post_parse_type old (BabTy_Array loc eltType dims) =
    post_parse_type old eltType
    @ (if array_dims_valid dims then [] else [(loc, PPE_MixedArrayDimension)])
    @ (concat (map (post_parse_term old) (concat (map array_dim_terms dims))))"

| "post_parse_term old (BabTm_Literal _ lit) = 
    (case lit of
      BabLit_Array tms \<Rightarrow> concat (map (post_parse_term old) tms)
      | _ \<Rightarrow> [])"
| "post_parse_term old (BabTm_Name loc name types) = 
      (if old \<and> name = ''return'' then [(loc, PPE_OldUsedWithReturn)] else [])
      @ concat (map (post_parse_type old) types)"
| "post_parse_term old (BabTm_Cast _ ty tm) = post_parse_type old ty @ post_parse_term old tm"
| "post_parse_term old (BabTm_If _ tm1 tm2 tm3) = 
    post_parse_term old tm1 @ post_parse_term old tm2 @ post_parse_term old tm3"
| "post_parse_term old (BabTm_Unop _ _ tm) = post_parse_term old tm"
| "post_parse_term old (BabTm_Binop _ tm lst) = post_parse_term old tm
      @ concat (map (post_parse_term old \<circ> snd) lst)"
| "post_parse_term old (BabTm_Let _ _ tm1 tm2) = post_parse_term old tm1 @ post_parse_term old tm2"
| "post_parse_term old (BabTm_Quantifier _ _ _ ty tm) = 
      post_parse_type old ty @ post_parse_term old tm"
| "post_parse_term old (BabTm_Call _ tm tms) = 
      post_parse_term old tm @ concat (map (post_parse_term old) tms)"
| "post_parse_term old (BabTm_Tuple _ tms) = concat (map (post_parse_term old) tms)"
| "post_parse_term old (BabTm_Record _ flds) = concat (map (post_parse_term old \<circ> snd) flds)"
| "post_parse_term old (BabTm_RecordUpdate _ tm flds) = post_parse_term old tm
      @ concat (map (post_parse_term old \<circ> snd) flds)"
| "post_parse_term old (BabTm_TupleProj _ tm _) = post_parse_term old tm"
| "post_parse_term old (BabTm_RecordProj _ tm _) = post_parse_term old tm"
| "post_parse_term old (BabTm_ArrayProj _ tm tms) = post_parse_term old tm 
      @ concat (map (post_parse_term old) tms)"
| "post_parse_term old (BabTm_Match _ scrut arms) = post_parse_term old scrut
      @ concat (map (post_parse_term old \<circ> snd) arms)"
| "post_parse_term old (BabTm_Sizeof _ tm) = post_parse_term old tm"
| "post_parse_term old (BabTm_Allocated _ tm) = post_parse_term old tm"
| "post_parse_term _ (BabTm_Old loc tm) = 
      (loc, PPE_OldOutsidePostcondition) 
      # post_parse_term True tm"

  by pat_completeness auto

termination
proof (relation "measure bool_ttsize")
  show "wf (measure bool_ttsize)" by auto

next
  fix old x loc name types
  show "x \<in> set types \<Longrightarrow>
       (Inl (old, x), Inl (old, BabTy_Name loc name types)) \<in> measure bool_ttsize"
    using bab_type_smaller_than_list by auto

next
  fix old loc types x
  show "x \<in> set types \<Longrightarrow>
       (Inl (old, x), Inl (old, BabTy_Tuple loc types)) \<in> measure bool_ttsize"
    using bab_type_smaller_than_list by auto

next
  fix old loc fieldTypes x
  have "x \<in> set fieldTypes \<Longrightarrow>
       (Inl (snd x), Inl (BabTy_Record loc fieldTypes)) \<in> measure ttsize"
    using bab_type_smaller_than_fieldlist
    by (metis bab_type_size.simps(7) in_measure old.sum.simps(5) plus_1_eq_Suc
        surjective_pairing) 
  thus "x \<in> set fieldTypes \<Longrightarrow>
       (Inl (old, snd x), Inl (old, BabTy_Record loc fieldTypes)) \<in> measure bool_ttsize"
    by simp

next
  fix old loc eltType dims
  show "(Inl (old, eltType), Inl (old, BabTy_Array loc eltType dims)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc eltType dims x
  show "x \<in> set (concat (map array_dim_terms dims)) \<Longrightarrow>
       (Inr (old, x), Inl (old, BabTy_Array loc eltType dims)) \<in> measure bool_ttsize"
    using bab_term_smaller_than_arraydim by force

next
  fix old loc lit tms tm
  show "lit = BabLit_Array tms \<Longrightarrow>
       tm \<in> set tms \<Longrightarrow> 
       (Inr (old, tm), Inr (old, BabTm_Literal loc lit)) \<in> measure bool_ttsize"
    using bab_term_smaller_than_list by force

next
  fix old ty types loc name
  show "ty \<in> set types \<Longrightarrow> (Inl (old, ty), Inr (old, BabTm_Name loc name types)) \<in> measure bool_ttsize"
    using bab_type_smaller_than_list by force

next
  fix old loc ty tm
  show "(Inl (old, ty), Inr (old, BabTm_Cast loc ty tm)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc ty tm
  show "(Inr (old, tm), Inr (old, BabTm_Cast loc ty tm)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc tm1 tm2 tm3
  show "(Inr (old, tm1), Inr (old, BabTm_If loc tm1 tm2 tm3)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc tm1 tm2 tm3
  show "(Inr (old, tm2), Inr (old, BabTm_If loc tm1 tm2 tm3)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc tm1 tm2 tm3
  show "(Inr (old, tm3), Inr (old, BabTm_If loc tm1 tm2 tm3)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc op tm
  show "(Inr (old, tm), Inr (old, BabTm_Unop loc op tm)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc tm lst
  show "(Inr (old, tm), Inr (old, BabTm_Binop loc tm lst)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc tm
  fix lst :: "(BabBinop \<times> BabTerm) list"
  fix x :: "BabBinop \<times> BabTerm"
  assume Elem: "x \<in> set lst"
  show "(Inr (old, snd x), Inr (old, BabTm_Binop loc tm lst)) \<in> measure bool_ttsize"
  proof (cases x)
    case (Pair op rhs)
    have "bab_term_size rhs < Suc (sum_list (map (bab_term_size \<circ> snd) lst))"
      using bab_term_smaller_than_fieldlist Pair Elem by auto
    hence "(Inr (snd x), Inr (BabTm_Binop loc tm lst)) \<in> measure ttsize"
      using Pair by auto
    thus ?thesis
      by auto
  qed

next
  fix old loc name tm1 tm2
  show "(Inr (old, tm1), Inr (old, BabTm_Let loc name tm1 tm2)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc name tm1 tm2
  show "(Inr (old, tm2), Inr (old, BabTm_Let loc name tm1 tm2)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc quant name ty tm
  show "(Inl (old, ty), Inr (old, BabTm_Quantifier loc quant name ty tm)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc quant name ty tm
  show "(Inr (old, tm), Inr (old, BabTm_Quantifier loc quant name ty tm)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc tm tms
  show "(Inr (old, tm), Inr (old, BabTm_Call loc tm tms)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc tm tms x
  show "x \<in> set tms \<Longrightarrow> (Inr (old, x), Inr (old, BabTm_Call loc tm tms)) \<in> measure bool_ttsize"
    using bab_term_smaller_than_list by force

next
  fix old loc tms x
  show "x \<in> set tms \<Longrightarrow> (Inr (old, x), Inr (old, BabTm_Tuple loc tms)) \<in> measure bool_ttsize"
    using bab_term_smaller_than_list by force

next
  fix old loc flds x
  have "x \<in> set flds \<Longrightarrow> (Inr (snd x), Inr (BabTm_Record loc flds)) \<in> measure ttsize"
    using bab_term_smaller_than_fieldlist
    by (metis bab_term_size.simps(11) in_measure old.sum.simps(6) plus_1_eq_Suc
        prod.exhaust_sel)
  thus "x \<in> set flds \<Longrightarrow> (Inr (old, snd x), Inr (old, BabTm_Record loc flds)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc tm flds 
  show "(Inr (old, tm), Inr (old, BabTm_RecordUpdate loc tm flds)) \<in> measure bool_ttsize"
    using bab_term_smaller_than_fieldlist by force

next
  fix old loc tm flds x
  have "x \<in> set flds \<Longrightarrow> (Inr (snd x), Inr (BabTm_RecordUpdate loc tm flds)) \<in> measure ttsize"
    using bab_term_smaller_than_fieldlist
    by (metis add_Suc_shift bab_term_size.simps(12) in_measure old.sum.simps(6) plus_1_eq_Suc
        surjective_pairing trans_less_add2) 
  thus "x \<in> set flds \<Longrightarrow> (Inr (old, snd x), Inr (old, BabTm_RecordUpdate loc tm flds)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc tm idx
  show "(Inr (old, tm), Inr (old, BabTm_TupleProj loc tm idx)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc tm name
  show "(Inr (old, tm), Inr (old, BabTm_RecordProj loc tm name)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc tm tms
  show "(Inr (old, tm), Inr (old, BabTm_ArrayProj loc tm tms)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc tm tms x
  show "x \<in> set tms \<Longrightarrow> (Inr (old, x), Inr (old, BabTm_ArrayProj loc tm tms)) \<in> measure bool_ttsize"
    using bab_term_smaller_than_list by force

next
  fix old loc tm
  show "(Inr (old, tm), Inr (old, BabTm_Sizeof loc tm)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc tm
  show "(Inr (old, tm), Inr (old, BabTm_Allocated loc tm)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc tm
  show "(Inr (True, tm), Inr (old, BabTm_Old loc tm)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc scrut arms
  show "(Inr (old, scrut), Inr (old, BabTm_Match loc scrut arms)) \<in> measure bool_ttsize"
    by auto

next
  fix old loc scrut arms x
  have "x \<in> set arms \<Longrightarrow> (Inr (snd x), Inr (BabTm_Match loc scrut arms)) \<in> measure ttsize"
    using bab_term_smaller_than_fieldlist
    by (metis add_Suc_shift bab_term_size.simps(16) in_measure old.sum.simps(6) plus_1_eq_Suc
        surjective_pairing trans_less_add2) 
  thus "x \<in> set arms \<Longrightarrow> (Inr (old, snd x), Inr (old, BabTm_Match loc scrut arms)) \<in> measure bool_ttsize"
    by auto
qed


fun post_parse_attribute :: "BabAttribute \<Rightarrow> (Location \<times> PostParseError) list" where
  "post_parse_attribute (BabAttr_Requires _ tm) = post_parse_term False tm"
| "post_parse_attribute (BabAttr_Ensures _ tm) = 
    filter (\<lambda>(_, err). err \<noteq> PPE_OldOutsidePostcondition)
      (post_parse_term False tm)"
| "post_parse_attribute (BabAttr_Invariant _ tm) = post_parse_term False tm"
| "post_parse_attribute (BabAttr_Decreases _ tm) = post_parse_term False tm"


fun post_parse_statement :: "BabStatement \<Rightarrow> (Location \<times> PostParseError) list"
and post_parse_stmt_arm :: "BabPattern \<times> BabStatement list \<Rightarrow> (Location \<times> PostParseError) list"
where
  "post_parse_statement (BabStmt_VarDecl _ _ _ _ maybeType maybeTerm) =
    case_option [] (post_parse_type False) maybeType 
    @ case_option [] (post_parse_term False) maybeTerm"
| "post_parse_statement (BabStmt_Fix _ _ ty) = post_parse_type False ty"
| "post_parse_statement (BabStmt_Obtain _ _ ty tm) = post_parse_type False ty @ post_parse_term False tm"
| "post_parse_statement (BabStmt_Use _ tm) = post_parse_term False tm"
| "post_parse_statement (BabStmt_Assign _ _ tm1 tm2) = post_parse_term False tm1 @ post_parse_term False tm2"
| "post_parse_statement (BabStmt_Swap _ _ tm1 tm2) = post_parse_term False tm1 @ post_parse_term False tm2"
| "post_parse_statement (BabStmt_Return _ _ maybeTm) = case_option [] (post_parse_term False) maybeTm"
| "post_parse_statement (BabStmt_Assert _ maybeTm stmts) =
    case_option [] (post_parse_term False) maybeTm
    @ concat (map post_parse_statement stmts)"
| "post_parse_statement (BabStmt_Assume _ tm) = post_parse_term False tm"
| "post_parse_statement (BabStmt_If _ _ tm stmts1 stmts2) =
    post_parse_term False tm
    @ concat (map post_parse_statement stmts1)
    @ concat (map post_parse_statement stmts2)"
| "post_parse_statement (BabStmt_While _ _ tm attrs stmts) =
    post_parse_term False tm
    @ concat (map post_parse_attribute attrs)
    @ concat (map post_parse_statement stmts)"
| "post_parse_statement (BabStmt_Call _ _ tm) = post_parse_term False tm"
| "post_parse_statement (BabStmt_Match _ _ scrut arms) = 
    post_parse_term False scrut @ concat (map post_parse_stmt_arm arms)"
| "post_parse_statement (BabStmt_ShowHide _ _ _) = []"
| "post_parse_stmt_arm (pat, stmts) = concat (map post_parse_statement stmts)"


fun post_parse_data_ctor :: "Location \<times> string \<times> (BabType option) 
    \<Rightarrow> (Location \<times> PostParseError) list" where
"post_parse_data_ctor (loc, name, maybeTy) =
   (if begins_with_capital name then [] else [(loc, PPE_DataCtorWrongCase)])
   @ case_option [] (post_parse_type False) maybeTy"


fun post_parse_declaration :: "BabDeclaration \<Rightarrow> (Location \<times> PostParseError) list" where
  "post_parse_declaration (BabDecl_Const cst) =
    case_option [] (post_parse_type False) (DC_Type cst)
    @ case_option [] (post_parse_term False) (DC_Value cst)"
| "post_parse_declaration (BabDecl_Function fun) =
    concat (map (\<lambda>(_,_,ty). post_parse_type False ty) (DF_TmArgs fun))
    @ case_option [] (post_parse_type False) (DF_ReturnType fun)
    @ case_option [] (concat \<circ> map post_parse_statement) (DF_Body fun)
    @ concat (map post_parse_attribute (DF_Attributes fun))"
| "post_parse_declaration (BabDecl_Datatype dtype) =
    concat (map post_parse_data_ctor (DD_Ctors dtype))"
| "post_parse_declaration (BabDecl_Typedef tydef) =
    case_option [] (post_parse_type False) (DT_Definition tydef)"


fun post_parse_module :: "BabModule \<Rightarrow> (Location \<times> PostParseError) list" where
  "post_parse_module module =
    concat (map post_parse_declaration (Mod_Interface module))
    @ concat (map post_parse_declaration (Mod_Implementation module))"



(* Basic sanity check: *)

definition parser_fails :: "'a Parser \<Rightarrow> (Location \<times> Token) list \<Rightarrow> bool" where
  "parser_fails p toks = (case run_parser p ''Test.b'' toks of
    PR_Success _ _ _ \<Rightarrow> False
    | PR_Error _ \<Rightarrow> True)"

lemma parse_empty_term:
  shows "parser_fails parse_term []"
  by eval


end
