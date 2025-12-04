theory BasicParser
  imports Main "../base/Location" "HOL-Library.Monad_Syntax"
begin

(* Basic parser state contains:
    - A "stream" object representing the remaining tokens or characters.
    - Functions to:
       - Given stream, return the next token (including its location) and a "tail" stream,
         or return None (if at EOF).
       - Given stream, return its length (i.e. number of tokens remaining).
    - A cached "current location" (points to a zero-width location at the end of the most
      recently read token).
    - A cached "error location" (used with <|> to give better error messages).
*)
type_synonym ('s, 'c) BasicParserState =
  "'s \<times> ('s \<Rightarrow> ('c \<times> Location \<times> 's) option) \<times> ('s \<Rightarrow> nat) \<times> Location \<times> Location"

(* Parse result contains:
    - On success, result of type 'a, location of consumed input 
      (might be a "zero-width" location), and a new state.
    - On failure, location of the failure.
*)
datatype ('a, 's, 'c) BasicParseResult =
  PR_Success 'a Location "('s, 'c) BasicParserState"
  | PR_Error Location

(* A BasicParser takes a BasicParserState and returns a BasicParseResult. *)
type_synonym ('a, 's, 'c) BasicParser =
  "('s, 'c) BasicParserState \<Rightarrow> ('a, 's, 'c) BasicParseResult"


(* Helper(s) to access components of the state *)
fun cur_loc_from_state :: "('s, 'c) BasicParserState \<Rightarrow> Location" where
  "cur_loc_from_state (_, _, _, cur_loc, _) = cur_loc"

fun get_state_err_loc :: "Location \<Rightarrow> ('s, 'c) BasicParserState \<Rightarrow> Location" where
  "get_state_err_loc loc1 (_, _, _, _, loc2) = max_location loc1 loc2"

fun update_state_err_loc :: "Location 
                              \<Rightarrow> ('s, 'c) BasicParserState 
                              \<Rightarrow> ('s, 'c) BasicParserState" where
  "update_state_err_loc loc1 (a, b, c, d, loc2) = (a, b, c, d, max_location loc1 loc2)"


(* Monad operations *)

(* Return a value without changing the state *)
fun return :: "'a \<Rightarrow> ('a, 's, 'c) BasicParser" where
  "return x state = 
    PR_Success x (cur_loc_from_state state) state"

(* Fail at "current location" *)
fun fail :: "('a, 's, 'c) BasicParser" where
  "fail state =
    PR_Error (get_state_err_loc (cur_loc_from_state state) state)"

(* Fail at a given location *)
definition fail_at :: "Location \<Rightarrow> ('a, 's, 'c) BasicParser" where
  "fail_at loc state = PR_Error (get_state_err_loc loc state)"

(* Monadic bind operator *)
definition bind :: "('a, 's, 'c) BasicParser 
                      \<Rightarrow> ('a \<Rightarrow> ('b, 's, 'c) BasicParser)
                      \<Rightarrow> ('b, 's, 'c) BasicParser" where
  "bind m f state =
    (case m state of
       PR_Error loc1 \<Rightarrow> PR_Error loc1
     | PR_Success x loc1 state1 \<Rightarrow>
         (case f x state1 of
            PR_Error loc2 \<Rightarrow> PR_Error loc2
          | PR_Success y loc2 state2 \<Rightarrow>
              PR_Success y (merge_locations loc1 loc2) state2))"

(* Alternation. If both parsers fail, we return the "rightmost" error
   location seen so far (from all previous <|> operators as well as this one),
   as that will likely be closest to the "real" error. *)
definition or :: "('a, 's, 'c) BasicParser 
                    \<Rightarrow> ('a, 's, 'c) BasicParser 
                    \<Rightarrow> ('a, 's, 'c) BasicParser" where
  "or p1 p2 state = 
    (case p1 state of
       PR_Success x loc1 state1 \<Rightarrow> PR_Success x loc1 state1
     | PR_Error loc1 \<Rightarrow>
        (let state1 = update_state_err_loc loc1 state in
        case p2 state1 of
           PR_Success x loc2 state2 \<Rightarrow> PR_Success x loc2 state2
         | PR_Error loc2 \<Rightarrow>
            PR_Error (get_state_err_loc loc2 state1)))"


(* Syntax for do-notation and alternatives. *)
adhoc_overloading
  Monad_Syntax.bind == bind

notation or (infixr "<|>" 60)


(* Additional primitive parsers *)

(* Consume any non-EOF token. Returns the token and updates "cur_loc" to the end of that token. *)
fun any_token :: "('c, 's, 'c) BasicParser" where
  "any_token (stream, next_fn, fuel_fn, cur_loc, err_loc) = 
    (case next_fn stream of
      None \<Rightarrow> PR_Error (max_location cur_loc err_loc)
    | Some (tok, loc, newStream) \<Rightarrow> 
        PR_Success tok loc (newStream, next_fn, fuel_fn, get_location_end loc, err_loc))"

(* Get number of input tokens remaining. *)
fun get_num_tokens :: "(nat, 's, 'c) BasicParser" where
  "get_num_tokens (stream, next_fn, fuel_fn, cur_loc, err_loc) =
    PR_Success (fuel_fn stream) cur_loc (stream, next_fn, fuel_fn, cur_loc, err_loc)"

(* Parse p but don't consume any input.
   If p fails, so does look_ahead p. *)
definition look_ahead :: "('a, 's, 'c) BasicParser \<Rightarrow> ('a, 's, 'c) BasicParser" where
  "look_ahead parser state =
    (case parser state of
      PR_Success result loc newState \<Rightarrow> PR_Success result (cur_loc_from_state state) state
    | PR_Error loc \<Rightarrow> PR_Error loc)"

(* "Invert" a parser, i.e. succeed only when the given parser fails. *)
(* This doesn't consume input. *)
definition not_parser :: "('a, 's, 'c) BasicParser \<Rightarrow> (unit, 's, 'c) BasicParser" where
  "not_parser parser state = 
    (case parser state of
      PR_Success _ loc _ \<Rightarrow> fail_at loc state
    | PR_Error _ \<Rightarrow> PR_Success () (cur_loc_from_state state) state)"

(* Extend a parser so that it returns the Location as well as its normal result. *)
definition located :: "('a, 's, 'c) BasicParser \<Rightarrow> (Location \<times> 'a, 's, 'c) BasicParser" where
  "located parser state =
    (case parser state of
      PR_Success result loc newState \<Rightarrow> PR_Success (loc, result) loc newState
    | PR_Error loc \<Rightarrow> PR_Error loc)"

(* "Delay" i.e. don't evaluate a parser immediately. Useful for avoiding issues with 
   strict evaluation. *)
definition delay :: "(unit \<Rightarrow> ('a, 's, 'c) BasicParser) \<Rightarrow> ('a, 's, 'c) BasicParser" where
  "delay p state = p () state"

(* Modify the remaining stream in-place. (Use with care.) *)
fun modify_stream :: "('s \<Rightarrow> 's) \<Rightarrow> (unit, 's, 'c) BasicParser" where
  "modify_stream f (stream, getNextTok, getLength, curLoc, errLoc) = 
    PR_Success () curLoc (f stream, getNextTok, getLength, curLoc, errLoc)"


(* Derived parsers *)

(* Try the given parser; if it fails, return None instead of failing. *)
definition optional :: "('a, 's, 'c) BasicParser \<Rightarrow> ('a option, 's, 'c) BasicParser" where
  "optional p = (p \<bind> return \<circ> Some) <|> return None"

(* Parse begin, then (one instance of) p, then end, 
   returning the result of p. *)
definition between :: "('open, 's, 'c) BasicParser
                        \<Rightarrow> ('close, 's, 'c) BasicParser
                        \<Rightarrow> ('a, 's, 'c) BasicParser
                        \<Rightarrow> ('a, 's, 'c) BasicParser" where
  "between open close p = do {
    open;
    x \<leftarrow> p;
    close;
    return x
  }"

(* Helper function for "many" *)
fun many_helper :: "nat \<Rightarrow> ('a, 's, 'c) BasicParser \<Rightarrow> ('a list, 's, 'c) BasicParser" where
  "many_helper 0 _ = undefined"  (* ran out of fuel *)
| "many_helper (Suc fuel) parser = (do {
      firstItem \<leftarrow> parser;
      nextItems \<leftarrow> many_helper fuel parser;
      return (firstItem # nextItems)
  }) <|> return []"

(* Parse 0 or more of the given parser; return all results in a list. *)
definition many :: "('a, 's, 'c) BasicParser \<Rightarrow> ('a list, 's, 'c) BasicParser" where
  "many parser = do {
    fuel \<leftarrow> get_num_tokens;
    many_helper (Suc fuel) parser
  }"

(* Parse 1 or more of the given parser; return all results in a list. *)
definition many1 :: "('a, 's, 'c) BasicParser \<Rightarrow> ('a list, 's, 'c) BasicParser" where
  "many1 parser = do {
    result \<leftarrow> parser;
    more_results \<leftarrow> many parser;
    return (result # more_results)
  }"

(* Parse p (excluding end) zero or more times, until end succeeds.
   This can be used for parsing block comments. *)
definition many_till :: "('a, 's, 'c) BasicParser \<Rightarrow> 
                           ('end, 's, 'c) BasicParser \<Rightarrow>
                           ('a list, 's, 'c) BasicParser" where
  "many_till p end = do {
    results \<leftarrow> many (not_parser end \<then> p);
    end;
    return results
   }"

(* Parse "p" zero or more times, where each item is ended by "end". *)
definition end_by :: "('a, 's, 'c) BasicParser \<Rightarrow>
                        ('end, 's, 'c) BasicParser \<Rightarrow>
                        ('a list, 's, 'c) BasicParser" where
  "end_by p end = many (between (return ()) end p)"

(* Parse "p" one or more times, where items are separated (but not
   ended) by "sep". *)
definition sep_by_1 :: "('a, 's, 'c) BasicParser \<Rightarrow>
                        ('sep, 's, 'c) BasicParser \<Rightarrow>
                        ('a list, 's, 'c) BasicParser" where
  "sep_by_1 p sep = 
    do {
      head \<leftarrow> p;
      tail \<leftarrow> many (between sep (return ()) p);
      return (head # tail)
    }"

(* Parse "p" zero or more times, separated but not ended by "sep" *)
definition sep_by :: "('a, 's, 'c) BasicParser \<Rightarrow>
                      ('sep, 's, 'c) BasicParser \<Rightarrow>
                      ('a list, 's, 'c) BasicParser" where
  "sep_by p sep = sep_by_1 p sep <|> return []"

(* Parse "p" zero or more times, where items are separated (and
   optionally ended) by "sep". *)
definition sep_end_by :: "('a, 's, 'c) BasicParser \<Rightarrow>
                            ('sep, 's, 'c) BasicParser \<Rightarrow>
                            ('a list, 's, 'c) BasicParser" where
  "sep_end_by p sep = 
    (do {
      result \<leftarrow> sep_by p sep;
      optional sep;
      return result
    })"

(* Parse eof *)
definition eof :: "(unit, 's, 'c) BasicParser" where
  "eof = not_parser any_token"

(* Parse a token if it matches predicate *)
definition satisfy :: "('c \<Rightarrow> bool) \<Rightarrow> ('c, 's, 'c) BasicParser" where
  "satisfy p = do {
    (loc, tok) \<leftarrow> located any_token;
    if p tok then
      return tok
    else
      fail_at loc
    }"

(* Parse a specific token *)
definition expect :: "'c \<Rightarrow> ('c, 's, 'c) BasicParser" where
  "expect tok = satisfy (\<lambda>c. c = tok)"

(* Parse a specific list of tokens *)
fun expect_string :: "'c list \<Rightarrow> ('c list, 's, 'c) BasicParser" where
  "expect_string [] = return []"
| "expect_string (c # s) = do {
    ch \<leftarrow> expect c;
    rest \<leftarrow> expect_string s;
    return (ch # rest)
   }"

end
