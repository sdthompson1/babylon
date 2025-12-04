theory BabLexer
  imports Main "../base/Location" "BabToken" "BasicParser"
begin

(* Character constants *)
definition bell :: char where "bell = CHR 0x07"
definition backspace :: char where "backspace = CHR 0x08"
definition tab :: char where "tab = CHR 0x09"
definition newline :: char where "newline = CHR 0x0a"
definition vertical_tab :: char where "vertical_tab = CHR 0x0b"
definition form_feed :: char where "form_feed = CHR 0x0c"
definition carriage_return :: char where "carriage_return = CHR 0x0d"
definition double_quote :: char where "double_quote = CHR 0x22"
definition single_quote :: char where "single_quote = CHR 0x27"
definition backslash :: char where "backslash = CHR 0x5c"


(* Location arithmetic - assuming location is for a single char *)
fun add_one_line :: "Location \<Rightarrow> Location" where
  "add_one_line (Location file lin col _ _) =
    Location file (lin+1) 1 (lin+1) 2"

fun add_one_column :: "Location \<Rightarrow> Location" where
  "add_one_column (Location file lin col _ _) =
    Location file lin (col+1) lin (col+2)"


(* Specializing BasicParser for our lexer *)

(* Remainder of file, Next location (one-character span), Length of the string *)
type_synonym LexerStream = "string \<times> Location \<times> nat"

type_synonym LexerState = "(LexerStream, char) BasicParserState"

type_synonym 'a Lexer = "('a, LexerStream, char) BasicParser"

fun lexer_next_fn :: "LexerStream \<Rightarrow> (char \<times> Location \<times> LexerStream) option" where
  "lexer_next_fn (str, loc, count) =
    (case str of
      [] \<Rightarrow> None
    | c # cs \<Rightarrow> 
       (let new_loc = (if c = newline then add_one_line loc else add_one_column loc)
        in Some (c, loc, (cs, new_loc, count - 1))))"

fun lexer_fuel_fn :: "LexerStream \<Rightarrow> nat" where
  "lexer_fuel_fn (str, loc, count) = count"

fun initial_lexer_state :: "string \<Rightarrow> string \<Rightarrow> LexerState" where
  "initial_lexer_state filename contents =
    ((contents, Location filename 1 1 1 2, length contents), 
     lexer_next_fn, 
     lexer_fuel_fn,
     Location filename 1 1 1 1,
     Location filename 1 1 1 1)"

(* Lexer result type *)
datatype LexResult = LR_Success "(Location \<times> Token) list" | LR_Error Location

fun lr_is_error :: "LexResult \<Rightarrow> bool" where
  "lr_is_error (LR_Success _) = False"
| "lr_is_error (LR_Error _) = True"


(* Character predicates *)
definition char_in_range :: "char \<Rightarrow> char \<Rightarrow> char \<Rightarrow> bool" where
  "char_in_range a b x = (((of_char x)::nat) \<ge> of_char a
                          \<and> ((of_char x)::nat) \<le> of_char b)"

definition is_decimal_digit :: "char \<Rightarrow> bool" where
  "is_decimal_digit c = char_in_range (CHR ''0'') (CHR ''9'') c"

definition is_hex_digit :: "char \<Rightarrow> bool" where
  "is_hex_digit c = (is_decimal_digit c
      \<or> char_in_range (CHR ''a'') (CHR ''f'') c
      \<or> char_in_range (CHR ''A'') (CHR ''F'') c)"

definition is_whitespace :: "char \<Rightarrow> bool" where
  "is_whitespace c = 
    (c = CHR '' '' \<or> char_in_range tab carriage_return c)"

definition is_alpha :: "char \<Rightarrow> bool" where
  "is_alpha c = (char_in_range (CHR ''A'') (CHR ''Z'') c
    \<or> char_in_range (CHR ''a'') (CHR ''z'') c)"



(* Read a line comment (beginning with "//") *)
definition line_comment :: "unit Lexer" where
  "line_comment = do {
    expect_string ''//'';
    many_till any_token ((expect newline \<then> return ()) <|> eof);
    return ()
  }"

(* Read a block comment (beginning "/*" and ending "*/") *)
fun block_comment :: "nat \<Rightarrow> unit Lexer" where
  "block_comment 0 = undefined"  (* out of fuel *)
| "block_comment (Suc fuel) = do {
    expect_string ''/*'';
    many_till ( delay (\<lambda>_. block_comment fuel) 
                  <|> (not_parser (expect_string ''/*'') \<then> any_token \<then> return ()) )
              (expect_string ''*/'');
    return ()
   }"

(* Skip comments and whitespace (if any). *)
definition skip_comments_and_whitespace :: "unit Lexer" where
  "skip_comments_and_whitespace = do {
    count \<leftarrow> get_num_tokens;
    many (line_comment <|> 
          block_comment (Suc count) <|> 
          (satisfy is_whitespace \<then> return ()));
    return ()
   }"


(* Simple token (fixed string - used for punctuation) *)
definition simple_token :: "string \<Rightarrow> Token \<Rightarrow> Token Lexer" where
  "simple_token s tok = do {
    expect_string s;
    return tok
   }"


(* Keywords *)
definition name_to_keyword :: "string \<Rightarrow> Keyword option" where
  "name_to_keyword s = (case s of
    ''allocated'' \<Rightarrow> Some KW_ALLOCATED
  | ''assert'' \<Rightarrow> Some KW_ASSERT
  | ''assume'' \<Rightarrow> Some KW_ASSUME
  | ''bool'' \<Rightarrow> Some KW_BOOL
  | ''case'' \<Rightarrow> Some KW_CASE
  | ''cast'' \<Rightarrow> Some KW_CAST
  | ''const'' \<Rightarrow> Some KW_CONST
  | ''datatype'' \<Rightarrow> Some KW_DATATYPE
  | ''decreases'' \<Rightarrow> Some KW_DECREASES
  | ''else'' \<Rightarrow> Some KW_ELSE
  | ''ensures'' \<Rightarrow> Some KW_ENSURES
  | ''exists'' \<Rightarrow> Some KW_EXISTS
  | ''extern'' \<Rightarrow> Some KW_EXTERN
  | ''false'' \<Rightarrow> Some KW_FALSE
  | ''fix'' \<Rightarrow> Some KW_FIX
  | ''forall'' \<Rightarrow> Some KW_FORALL
  | ''function'' \<Rightarrow> Some KW_FUNCTION
  | ''ghost'' \<Rightarrow> Some KW_GHOST
  | ''hide'' \<Rightarrow> Some KW_HIDE
  | ''i8'' \<Rightarrow> Some KW_I8
  | ''i16'' \<Rightarrow> Some KW_I16
  | ''i32'' \<Rightarrow> Some KW_I32
  | ''i64'' \<Rightarrow> Some KW_I64
  | ''if'' \<Rightarrow> Some KW_IF
  | ''import'' \<Rightarrow> Some KW_IMPORT
  | ''impure'' \<Rightarrow> Some KW_IMPURE
  | ''in'' \<Rightarrow> Some KW_IN
  | ''int'' \<Rightarrow> Some KW_INT
  | ''interface'' \<Rightarrow> Some KW_INTERFACE
  | ''invariant'' \<Rightarrow> Some KW_INVARIANT
  | ''let'' \<Rightarrow> Some KW_LET
  | ''match'' \<Rightarrow> Some KW_MATCH
  | ''module'' \<Rightarrow> Some KW_MODULE
  | ''obtain'' \<Rightarrow> Some KW_OBTAIN
  | ''old'' \<Rightarrow> Some KW_OLD
  | ''real'' \<Rightarrow> Some KW_REAL
  | ''ref'' \<Rightarrow> Some KW_REF
  | ''requires'' \<Rightarrow> Some KW_REQUIRES
  | ''return'' \<Rightarrow> Some KW_RETURN
  | ''show'' \<Rightarrow> Some KW_SHOW
  | ''sizeof'' \<Rightarrow> Some KW_SIZEOF
  | ''swap'' \<Rightarrow> Some KW_SWAP
  | ''then'' \<Rightarrow> Some KW_THEN
  | ''true'' \<Rightarrow> Some KW_TRUE
  | ''type'' \<Rightarrow> Some KW_TYPE
  | ''u8'' \<Rightarrow> Some KW_U8
  | ''u16'' \<Rightarrow> Some KW_U16
  | ''u32'' \<Rightarrow> Some KW_U32
  | ''u64'' \<Rightarrow> Some KW_U64
  | ''use'' \<Rightarrow> Some KW_USE
  | ''var'' \<Rightarrow> Some KW_VAR
  | ''while'' \<Rightarrow> Some KW_WHILE
  | ''with'' \<Rightarrow> Some KW_WITH
  | _ \<Rightarrow> None)"

(* Read an identifier, keyword, or lone underscore
   (sequence of alphanumeric or underscore -- no need to filter out
   all-digits or lone underscore cases, as these will be higher 
   priority in lex_token) *)
(* Max accepted length: 200 chars *)
definition lex_ident_or_keyword_or_underscore :: "Token Lexer" where
  "lex_ident_or_keyword_or_underscore = do {
    init \<leftarrow> located (satisfy (\<lambda>c. is_alpha c \<or> c = CHR ''_''));
    rest \<leftarrow> located (many (satisfy (\<lambda>c. is_alpha c \<or> is_decimal_digit c \<or> c = CHR ''_'')));
    if length (snd rest) > 199 then
      fail_at (merge_locations (fst init) (fst rest))
    else do {
      let word = (snd init) # (snd rest);
      if word = ''_'' then
        return UNDERSCORE
      else (case name_to_keyword word of
             Some kw \<Rightarrow> return (KEYWORD kw)
           | None \<Rightarrow> return (NAME word))
    }
  }"


(* Convert decimal or hex chars or strings to int *)
definition decimal_digit_to_nat :: "char \<Rightarrow> nat" where
  "decimal_digit_to_nat c = of_char c - of_char (CHR ''0'')"

fun strip_leading_zeros :: "char list \<Rightarrow> char list" where
  "strip_leading_zeros (CHR ''0'' # xs) = strip_leading_zeros xs"
| "strip_leading_zeros xs = xs"

(* Convert decimal digits to NAT_NUM token. Max allowed value = 2^64 - 1. *)
(* Note: using (of_nat num :: int) is a hack to get this to work inside the Isabelle jEdit
   environment (trying to compute 2^64 as nat in that environment does not work) *)
fun decimal_digits_to_nat :: "Location \<times> string \<Rightarrow> Token Lexer" where
  "decimal_digits_to_nat (loc, s) =
    (if length (strip_leading_zeros s) > 20 then fail_at loc
     else let num = foldl (\<lambda>acc d. acc*10 + decimal_digit_to_nat d) 0 s
          in (if (of_nat num :: int) \<ge> 2 ^ 64 then fail_at loc
              else return (NAT_NUM num)))"

definition hex_digit_to_nat :: "char \<Rightarrow> nat" where
  "hex_digit_to_nat c =
    (if (char_in_range (CHR ''a'') (CHR ''f'') c) then
      (10 + (of_char c) - (of_char (CHR ''a'')))
     else if (char_in_range (CHR ''A'') (CHR ''F'') c) then
      (10 + (of_char c) - (of_char (CHR ''A'')))
     else
      decimal_digit_to_nat c)"

(* Convert hex digits to nat. Max allowed value = 2^64 - 1. *)
fun hex_digits_to_nat :: "Location \<times> string \<Rightarrow> Token Lexer" where
  "hex_digits_to_nat (loc, s) =
    (if length (strip_leading_zeros s) > 16 then fail_at loc
     else return (NAT_NUM (foldl (\<lambda>acc d. acc*16 + hex_digit_to_nat d) 0 s)))"

(* Natural number literal token *)
(* Note: we enforce that a numeric literal cannot be immediately followed by a letter,
   e.g. "0x" on its own (not followed by any legal hex digits) should not be parsed as 
   NATURAL_NUMBER 0, NAME ''x'', but instead reported as a lexical error. *)
definition lex_nat_num :: "Token Lexer" where
  "lex_nat_num = do {
      expect (CHR ''0'');
      (expect (CHR ''x'') <|> expect (CHR ''X''));
      digits \<leftarrow> located (many1 (satisfy is_hex_digit));
      not_parser (satisfy is_alpha);
      hex_digits_to_nat digits
    } <|> do {
      digits \<leftarrow> located (many1 (satisfy is_decimal_digit));
      not_parser (satisfy is_alpha);
      decimal_digits_to_nat digits
    }"


(* String and character literals *)
definition lex_char_escape :: "char Lexer" where
  "lex_char_escape =
    (expect (CHR ''a'') \<then> return bell)
    <|> (expect (CHR ''b'') \<then> return backspace)
    <|> (expect (CHR ''f'') \<then> return form_feed)
    <|> (expect (CHR ''n'') \<then> return newline)
    <|> (expect (CHR ''r'') \<then> return carriage_return)
    <|> (expect (CHR ''t'') \<then> return tab)
    <|> (expect (CHR ''v'') \<then> return vertical_tab)
    <|> (expect double_quote \<then> return double_quote)
    <|> (expect single_quote \<then> return single_quote)
    <|> (expect backslash \<then> return backslash)
    <|> do {
      expect (CHR ''x'');
      digit1 \<leftarrow> satisfy is_hex_digit;
      digit2 \<leftarrow> satisfy is_hex_digit;
      return (char_of (16 * hex_digit_to_nat digit1 + hex_digit_to_nat digit2))
    }"

(* lex one character from a char or string literal *)
definition lex_character :: "char \<Rightarrow> char Lexer" where
  "lex_character quote = 
    (satisfy (\<lambda>c. c \<noteq> quote \<and> c \<noteq> newline \<and> c \<noteq> backslash))
    <|> (expect backslash \<then> lex_char_escape)"

definition lex_char_literal :: "Token Lexer" where
  "lex_char_literal = do {
    ch \<leftarrow> between (expect single_quote) (expect single_quote) (lex_character single_quote);
    return (NAT_NUM (of_char ch))
  }"

definition lex_string_literal :: "Token Lexer" where
  "lex_string_literal = do {
    chars \<leftarrow> between (expect double_quote) (expect double_quote) (many (lex_character double_quote));
    return (STRING chars)
   }"


(* Lex a single token *)
definition lex_token :: "Token Lexer" where
  "lex_token = 
    lex_nat_num <|>
    lex_char_literal <|>
    lex_string_literal <|>
    lex_ident_or_keyword_or_underscore <|>
    simple_token ''+'' PLUS <|>
    simple_token ''-'' MINUS <|>
    simple_token ''*'' STAR <|>
    simple_token ''/'' SLASH <|>
    simple_token ''%'' MODULO <|>
    simple_token ''&&'' AND_AND <|>
    simple_token ''&'' AND <|>
    simple_token ''||'' BAR_BAR <|>
    simple_token ''|'' BAR <|>
    simple_token ''^'' HAT <|>
    simple_token ''!='' EXCLAM_EQUAL <|>
    simple_token ''!'' EXCLAM <|>
    simple_token ''~'' TILDE <|>
    simple_token ''<<'' LESS_LESS <|>
    simple_token ''<==>'' LESS_EQUAL_EQUAL_GREATER <|>
    simple_token ''<=='' LESS_EQUAL_EQUAL <|>
    simple_token ''<='' LESS_EQUAL <|>
    simple_token ''<'' LESS <|>
    simple_token ''>>'' GREATER_GREATER <|>
    simple_token ''>='' GREATER_EQUAL <|>
    simple_token ''>'' GREATER <|>
    simple_token ''=>'' EQUAL_GREATER <|>
    simple_token ''==>'' EQUAL_EQUAL_GREATER <|>
    simple_token ''=='' EQUAL_EQUAL <|>
    simple_token ''='' EQUAL <|>
    simple_token '':'' COLON <|>
    simple_token '';'' SEMICOLON <|>
    simple_token '','' COMMA <|>
    simple_token ''.'' DOT <|>
    simple_token ''('' LPAREN <|>
    simple_token '')'' RPAREN <|>
    simple_token ''['' LBRACKET <|>
    simple_token '']'' RBRACKET <|>
    simple_token ''{'' LBRACE <|>
    simple_token ''}'' RBRACE"

(* Lex token, but prevent parsing an unclosed "/*" as DIVIDE, TIMES. *)
definition lex_token_nocomment :: "Token Lexer" where
  "lex_token_nocomment = not_parser (expect_string ''/*'') \<then> lex_token"

(* This checks for end of input. If eof is not matched, lex_token_nocomment is tried;
   this doesn't change the success/failure status of the parser, but does give a better
   error location. *)
definition lex_end_of_input :: "unit Lexer" where
  "lex_end_of_input =
    eof <|> (lex_token_nocomment \<then> fail)"

(* Lex all tokens from now until end of input. *)
definition lex_all_tokens :: "(Location \<times> Token) list Lexer" where
  "lex_all_tokens = 
    between 
      skip_comments_and_whitespace 
      lex_end_of_input
      (end_by (located lex_token_nocomment) skip_comments_and_whitespace)"

(* Main lexer function *)
definition lex :: "string \<Rightarrow> string \<Rightarrow> LexResult" where
  "lex filename contents = 
    (let initialState = initial_lexer_state filename contents in
     (case lex_all_tokens initialState of
      PR_Success result _ _ \<Rightarrow> LR_Success result
    | PR_Error loc \<Rightarrow> LR_Error loc))"


(* Some simple test cases *)

(* success cases *)
lemma test_integers:
  shows "lex ''Int.b'' (''0 0034 100'' @ [newline] @ ''0xff 0X1a'')
          = LR_Success [(Location ''Int.b'' 1 1 1 2, NAT_NUM 0),
                        (Location ''Int.b'' 1 3 1 7, NAT_NUM 34),
                        (Location ''Int.b'' 1 8 1 11, NAT_NUM 100),
                        (Location ''Int.b'' 2 1 2 5, NAT_NUM 255),
                        (Location ''Int.b'' 2 6 2 10, NAT_NUM 26)]"
  by eval

lemma test_char_1:
  shows "lex ''Char.b'' ([single_quote, CHR ''A'', single_quote])
          = LR_Success [(Location ''Char.b'' 1 1 1 4, NAT_NUM 65)]"
  by eval

lemma test_char_2:
  shows "lex ''Char.b'' ([single_quote, backslash, CHR ''x'', CHR ''0'', CHR ''0'', single_quote,
                         CHR '' '', 
                         single_quote, backslash, CHR ''x'', CHR ''f'', CHR ''F'', single_quote])
          = LR_Success [(Location ''Char.b'' 1 1 1 7, NAT_NUM 0),
                        (Location ''Char.b'' 1 8 1 14, NAT_NUM 255)]"
  by eval

lemma test_strings:
  shows "lex ''Str.b'' ([double_quote] @ ''hello'' @ [backslash] @ ''xff'' @ [double_quote, newline]
            @ [double_quote, backslash] @ ''a'' @ [backslash] @ ''n'' @ [double_quote])
         = LR_Success [(Location ''Str.b'' 1 1 1 12, STRING (''hello'' @ [CHR 0xff])),
                       (Location ''Str.b'' 2 1 2 7, STRING [CHR 0x07, CHR 0x0a])]"
  by eval

lemma test_ident:
  shows "lex ''Ident.b'' '' foo '' = LR_Success [(Location ''Ident.b'' 1 2 1 5, NAME ''foo'')]"
  by eval

lemma test_ident_beginning_with_underscore:
  shows "lex ''Ident.b'' ''_32'' = LR_Success [(Location ''Ident.b'' 1 1 1 4, NAME ''_32'')]"
  by eval

lemma test_underscore_and_integer:
  shows "lex ''Under.b'' ''_ 32'' = LR_Success [(Location ''Under.b'' 1 1 1 2, UNDERSCORE),
                                                (Location ''Under.b'' 1 3 1 5, NAT_NUM 32)]"
  by eval

lemma test_keywords:
  shows "lex ''Keywords.b'' ('' allocated bool decreases '' @ [newline] @ ''i8 obtain u32 with '')
          = LR_Success [(Location ''Keywords.b'' 1 2 1 11, KEYWORD KW_ALLOCATED),
                        (Location ''Keywords.b'' 1 12 1 16, KEYWORD KW_BOOL),
                        (Location ''Keywords.b'' 1 17 1 26, KEYWORD KW_DECREASES),
                        (Location ''Keywords.b'' 2 1 2 3, KEYWORD KW_I8),
                        (Location ''Keywords.b'' 2 4 2 10, KEYWORD KW_OBTAIN),
                        (Location ''Keywords.b'' 2 11 2 14, KEYWORD KW_U32),
                        (Location ''Keywords.b'' 2 15 2 19, KEYWORD KW_WITH)]"
  by eval

(* this illustrates "maximal munch" rule for "|||" *)
lemma test_punctuation:
  shows "lex ''Punct.b'' ''+-& && ||| << ==> ''
          = LR_Success [(Location ''Punct.b'' 1 1 1 2, PLUS),
                        (Location ''Punct.b'' 1 2 1 3, MINUS),
                        (Location ''Punct.b'' 1 3 1 4, AND),
                        (Location ''Punct.b'' 1 5 1 7, AND_AND),
                        (Location ''Punct.b'' 1 8 1 10, BAR_BAR),
                        (Location ''Punct.b'' 1 10 1 11, BAR),
                        (Location ''Punct.b'' 1 12 1 14, LESS_LESS),
                        (Location ''Punct.b'' 1 15 1 18, EQUAL_EQUAL_GREATER)]"
  by eval

lemma test_comments:
  shows "lex ''Comment.b'' ('' 123 /* comment */ + //Line comment'' @ [newline] @ ''456'')
          = LR_Success [(Location ''Comment.b'' 1 2 1 5, NAT_NUM 123),
                        (Location ''Comment.b'' 1 20 1 21, PLUS),
                        (Location ''Comment.b'' 2 1 2 4, NAT_NUM 456)]"
  by eval

lemma test_comment_without_newline:
  shows "lex ''Comment.b'' ''//foo'' = LR_Success []"
  by eval

lemma test_nested_comment:
  shows "lex ''Nested.b'' ''/* foo /* bar */ baz */'' = LR_Success []"
  by eval

(* Lexical errors *)
lemma test_bad_character:
  shows "lex ''Error.b'' ''100 ?''
          = LR_Error (Location ''Error.b'' 1 5 1 6)"
  by eval

lemma test_newline_in_string:
  shows "lex ''BadString.b'' ([double_quote] @ ''bad'' @ [newline] @ ''string'' @ [double_quote])
          = LR_Error (Location ''BadString.b'' 1 5 1 6)"
  by eval

lemma test_newline_in_char:
  shows "lex ''BadChar.b'' [single_quote, newline, single_quote] 
          = LR_Error (Location ''BadChar.b'' 1 2 1 3)"
  by eval

lemma test_quote_in_char:
  shows "lex ''BadChar.b'' [single_quote, single_quote, single_quote]
          = LR_Error (Location ''BadChar.b'' 1 2 1 3)"
  by eval

lemma test_unclosed_string:
  shows "lex ''Bad.b'' ('' '' @ [double_quote] @ ''hello'')
          = LR_Error (Location ''Bad.b'' 1 8 1 8)"
  by eval

lemma test_invalid_char_escape:
  shows "lex ''Char.b'' [single_quote, backslash, CHR ''Z'', single_quote]
          = LR_Error (Location ''Char.b'' 1 3 1 4)"
  by eval

lemma test_invalid_hex_char_escape:
  shows "lex ''Char.b'' [single_quote, backslash, CHR ''x'', CHR ''a'', single_quote]
          = LR_Error (Location ''Char.b'' 1 5 1 6)"
  by eval

lemma test_empty_hex_literal:
  shows "lex ''BadHex.b'' ''0x;''
          = LR_Error (Location ''BadHex.b'' 1 3 1 4)"
  by eval

lemma test_invalid_number:
  shows "lex ''BadNum.b'' ''3a''
          = LR_Error (Location ''BadNum.b'' 1 2 1 3)"
  by eval

lemma test_invalid_hex_number:
  shows "lex ''BadNum.b'' ''0x3g''
          = LR_Error (Location ''BadNum.b'' 1 4 1 5)"
  by eval

(* Note: the failure location in this test case is wrong (it should cover the
   hex literal) but this is a bit of an edge case, so we won't worry about it too
   much. The important thing is that it reports failure. *)
lemma test_too_big_hex_number:
  shows "lex ''BadNum.b'' ''0x10000000000000000''
          = LR_Error (Location ''BadNum.b'' 1 20 1 20)"
  by eval

(* We can't test 2^64 as an input, because it raises Interrupt_Breakdown (in the Isabelle
   jEdit environment), but we can test a 21-digit number. *)
(* As above, error location is wrong. *)
lemma test_too_big_number:
  shows "lex ''BadNum.b'' ''999999999999999999999''
          = LR_Error (Location ''BadNum.b'' 1 22 1 22)"
  by eval

(* Names over 200 chars are rejected. This one is 201 chars. *)
(* As above, error location is wrong. *)
lemma test_too_big_name:
  shows "lex ''Test.b'' ''abcdefghij1234567890123456789012345678901234567890abcdefghij1234567890123456789012345678901234567890abcdefghij1234567890123456789012345678901234567890abcdefghij1234567890123456789012345678901234567890z''
          = LR_Error (Location ''Test.b'' 1 202 1 202)"
  by eval

(* As above, error location is wrong. *)
lemma test_unclosed_comment:
  shows "lex ''BadComment.b'' (''foo'' @ [newline] @ '' /* '' @ [newline])
          = LR_Error (Location ''BadComment.b'' 2 6 2 6)"
  by eval

(* As above, error location is wrong. *)
lemma test_unclosed_comment_2:
  shows "lex ''BadComment.b'' (''/* /*/ A'')
          = LR_Error (Location ''BadComment.b'' 1 9 1 9)"
  by eval

end
