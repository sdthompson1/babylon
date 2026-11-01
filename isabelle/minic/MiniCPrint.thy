theory MiniCPrint
  imports MiniCTyping "../util/NatToString"
begin

(* ========================================================================== *)
(* MiniC: the C printer                                                       *)
(* ========================================================================== *)

(* A printer from a MiniC program to C source text. It is unverified and no
   theorem mentions it: the whole correctness argument is "it is a plain
   traversal of the syntax that prints every construct as the obvious C".
   DESIGN.md (sections 5 and 11) records the conventions; in brief:

    - Every expression is fully parenthesised, so precedence never matters.
    - Every arithmetic result is cast back to the operand's MiniC type, which
      undoes C's integer promotions (without the cast, `~x` on a uint8_t would
      be a negative int). The printer finds the type with expr_type, so it
      threads a type environment through the statements exactly as the typing
      judgement does.
    - Loads and stores through pointers are memcpy helpers (one per C type:
      bab_load_i32, bab_store_cp, ...), never typed dereferences (obligation
      P1 of DESIGN.md). Copies and zeroing are memmove and memset.
    - MS_Uninit is printed according to the printer options (PrintOpts): as
      memset(p, 0, n) (the default, which keeps gcc's -Wuninitialized quiet
      when the buffer is later copied) or as nothing at all (no run-time
      cost). Either is a sound realisation of "these bytes are undefined".
    - Shifts are helpers implementing the idiom of codegen.c's shift_binop
      (unsigned arithmetic, `+ 0u` against promotion, memcpy back for signed
      left shifts). max is a helper, except at file scope (the size of a global
      buffer must be a constant expression), where it is a conditional.
    - Integer literals use the INTn_C/UINTn_C macros; the most negative value
      of a signed type is printed as `(-MAX - 1)`.
    - Names are mangled as in codegen.c and docs/c-interface.md (section
      "Calling Babylon Functions from C"), extended with `zd` for `$` and
      `zx<hex>` for any other character, and with a `z` appended to C keywords
      and the names the generated file itself uses. Extern functions are
      printed under their C name, unmangled. Mangling is proved injective and
      never to produce a reserved name (mangle_injective, mangle_not_reserved
      below), so distinct MiniC names never print as the same C identifier.
      An extern's C name can still coincide with a mangled name; the
      executable check extern_clashes finds every such clash that would make
      the C invalid, and the driver runs it before printing.
    - The file begins with the includes, #error guards for the assumptions A1,
      A2 and A5 of DESIGN.md, the helpers, the globals, a prototype for every
      function (so that definition order does not matter), and then the
      definitions. `main` is printed as `int main(void)`. *)


section \<open>Strings\<close>

definition int_to_string :: "int \<Rightarrow> string" where
  "int_to_string i = (if i < 0 then CHR ''-'' # nat_to_string (nat (- i)) else nat_to_string (nat i))"

definition newline :: string where
  "newline = [CHR 0x0A]"

(* Join lines with newlines (each line is terminated). *)
definition unlines :: "string list \<Rightarrow> string" where
  "unlines ls = concat (map (\<lambda>l. l @ newline) ls)"

(* Join strings with a separator. *)
fun intercalate :: "string \<Rightarrow> string list \<Rightarrow> string" where
  "intercalate sep [] = []"
| "intercalate sep [s] = s"
| "intercalate sep (s # ss) = s @ sep @ intercalate sep ss"

definition indent :: "nat \<Rightarrow> string \<Rightarrow> string" where
  "indent n s = replicate (4 * n) CHR '' '' @ s"


section \<open>Name mangling\<close>

definition hex_digit :: "nat \<Rightarrow> char" where
  "hex_digit n = (if n < 10 then char_of (48 + n) else char_of (87 + n))"

definition hex2 :: "nat \<Rightarrow> string" where
  "hex2 n = [hex_digit (n div 16 mod 16), hex_digit (n mod 16)]"

(* A letter, a digit or an underscore. *)
definition is_ident_char :: "char \<Rightarrow> bool" where
  "is_ident_char c =
    (let n = of_char c :: nat
     in (48 \<le> n \<and> n \<le> 57) \<or> (65 \<le> n \<and> n \<le> 90) \<or> (97 \<le> n \<and> n \<le> 122) \<or> n = 95)"

(* The character encoding of codegen.c (encode_chars): `.` is z_, `/` is zs,
   `@` is za, `^` is zh, `-` is zm, `z` is zz, a leading `_` is zu, `$` is zd;
   any other character that codegen.c would reject is zx followed by two hex
   digits. `first` says whether this is the first character of the name. *)
fun mangle_chars :: "bool \<Rightarrow> string \<Rightarrow> string" where
  "mangle_chars first [] = []"
| "mangle_chars first (c # cs) =
    (if c = CHR ''.'' then ''z_''
     else if c = CHR ''/'' then ''zs''
     else if c = CHR ''@'' then ''za''
     else if c = CHR ''^'' then ''zh''
     else if c = CHR ''-'' then ''zm''
     else if c = CHR ''z'' then ''zz''
     else if c = CHR ''_'' \<and> first then ''zu''
     else if c = CHR ''$'' then ''zd''
     else if is_ident_char c then [c]
     else ''zx'' @ hex2 (of_char c))
    @ mangle_chars False cs"

(* The C scalar types, and the suffix naming each in a helper function name. *)
fun int_ty_suffix :: "Signedness \<Rightarrow> IntBits \<Rightarrow> string" where
  "int_ty_suffix s b = (case s of Signed \<Rightarrow> ''i'' | Unsigned \<Rightarrow> ''u'') @ nat_to_string (bit_size b)"

fun cty_suffix :: "CTy \<Rightarrow> string" where
  "cty_suffix (CTy_Int s b) = int_ty_suffix s b"
| "cty_suffix CTy_CharPtr = ''cp''"
| "cty_suffix CTy_VoidPtr = ''vp''"

definition all_int_tys :: "CTy list" where
  "all_int_tys = [CTy_Int s b. s \<leftarrow> [Signed, Unsigned], b \<leftarrow> [IntBits_8, IntBits_16, IntBits_32, IntBits_64]]"

definition all_ctys :: "CTy list" where
  "all_ctys = all_int_tys @ [CTy_CharPtr, CTy_VoidPtr]"

definition helper_name :: "string \<Rightarrow> CTy \<Rightarrow> string" where
  "helper_name kind ty = ''bab_'' @ kind @ ''_'' @ cty_suffix ty"

definition helper_names :: "string list" where
  "helper_names =
    concat (map (\<lambda>ty. [helper_name ''load'' ty, helper_name ''store'' ty]) all_ctys)
    @ concat (map (\<lambda>ty. [helper_name ''shl'' ty, helper_name ''shr'' ty, helper_name ''max'' ty]) all_int_tys)"

(* Names a mangled identifier must not be: the C keywords (C99, C11 and C23),
   the library and header names the generated file uses, and the helpers. A
   name that comes out equal to one of these gets a `z` appended (as in
   codegen.c, whose list this extends). *)
definition reserved_names :: "string list" where
  "reserved_names =
    [ ''auto'', ''break'', ''case'', ''char'', ''const'', ''continue'', ''default'', ''do'',
      ''double'', ''else'', ''enum'', ''extern'', ''float'', ''for'', ''goto'', ''if'',
      ''inline'', ''int'', ''long'', ''register'', ''restrict'', ''return'', ''short'',
      ''signed'', ''sizeof'', ''static'', ''struct'', ''switch'', ''typedef'', ''union'',
      ''unsigned'', ''void'', ''volatile'', ''while'',
      ''alignas'', ''alignof'', ''bool'', ''constexpr'', ''false'', ''nullptr'',
      ''static_assert'', ''thread_local'', ''true'', ''typeof'', ''typeof_unqual'',
      ''memcpy'', ''memmove'', ''memset'', ''size_t'', ''NULL'', ''CHAR_BIT'',
      ''int8_t'', ''int16_t'', ''int32_t'', ''int64_t'',
      ''uint8_t'', ''uint16_t'', ''uint32_t'', ''uint64_t'',
      ''INT8_C'', ''INT16_C'', ''INT32_C'', ''INT64_C'',
      ''UINT8_C'', ''UINT16_C'', ''UINT32_C'', ''UINT64_C'' ]
    @ helper_names"

definition mangle :: "string \<Rightarrow> string" where
  "mangle name =
    (let m = mangle_chars True name
     in if m \<in> set reserved_names then m @ ''z'' else m)"


subsection \<open>Mangling is injective and never produces a reserved name\<close>

(* Two properties the printer relies on: distinct MiniC names print as
   distinct C identifiers, and no printed identifier is a C keyword or one of
   the names the generated file uses. (Which is why a name such as `intz` is
   not a problem: `int` mangles to `intz`, but `intz` mangles to `intzz`,
   because its `z` is doubled. In general a reserved name followed by a lone
   `z` is never the output of mangle_chars, because every `z` that
   mangle_chars writes begins a two- or four-character code, and no reserved
   name ends in `z`.)

   The proof goes through a decoder, unmangle_chars, which is a left inverse
   of mangle_chars; it exists only for the proofs and is not exported. *)

definition unhex_digit :: "char \<Rightarrow> nat option" where
  "unhex_digit c =
    (let n = of_char c :: nat
     in if 48 \<le> n \<and> n \<le> 57 then Some (n - 48)
        else if 97 \<le> n \<and> n \<le> 102 then Some (n - 87)
        else None)"

(* The character encoded by the letter after a `z` (other than `x`). *)
definition unmangle_code :: "char \<Rightarrow> char option" where
  "unmangle_code d =
    (if d = CHR ''_'' then Some (CHR ''.'')
     else if d = CHR ''s'' then Some (CHR ''/'')
     else if d = CHR ''a'' then Some (CHR ''@'')
     else if d = CHR ''h'' then Some (CHR ''^'')
     else if d = CHR ''m'' then Some (CHR ''-'')
     else if d = CHR ''z'' then Some (CHR ''z'')
     else if d = CHR ''u'' then Some (CHR ''_'')
     else if d = CHR ''d'' then Some (CHR ''$'')
     else None)"

fun unmangle_chars :: "string \<Rightarrow> string option" where
  "unmangle_chars [] = Some []"
| "unmangle_chars (c # cs) =
    (if c = CHR ''z'' then
       (case cs of
          [] \<Rightarrow> None
        | d # cs' \<Rightarrow>
            if d = CHR ''x'' then
              (case cs' of
                 h1 # h2 # cs'' \<Rightarrow>
                   (case (unhex_digit h1, unhex_digit h2) of
                      (Some a, Some b) \<Rightarrow> map_option ((#) (char_of (16 * a + b))) (unmangle_chars cs'')
                    | _ \<Rightarrow> None)
               | _ \<Rightarrow> None)
            else (case unmangle_code d of
                    Some c' \<Rightarrow> map_option ((#) c') (unmangle_chars cs')
                  | None \<Rightarrow> None))
     else map_option ((#) c) (unmangle_chars cs))"

lemma unhex_digit_hex_digit: "n < 16 \<Longrightarrow> unhex_digit (hex_digit n) = Some n"
  by (simp add: unhex_digit_def hex_digit_def)

lemma unmangle_chars_zx:
  assumes "n < 256"
  shows "unmangle_chars (CHR ''z'' # CHR ''x'' # hex2 n @ rest) = map_option ((#) (char_of n)) (unmangle_chars rest)"
proof -
  have "n div 16 < 16" using assms by simp
  then have "n div 16 mod 16 = n div 16" by simp
  with assms show ?thesis
    by (simp add: hex2_def unhex_digit_hex_digit)
qed

(* Decoding one encoded character. *)
lemma unmangle_mangle_char:
  "unmangle_chars (mangle_chars first [c] @ rest) = map_option ((#) c) (unmangle_chars rest)"
proof (cases "c = CHR ''.'' \<or> c = CHR ''/'' \<or> c = CHR ''@'' \<or> c = CHR ''^'' \<or> c = CHR ''-''
              \<or> c = CHR ''z'' \<or> (c = CHR ''_'' \<and> first) \<or> c = CHR ''$'' \<or> is_ident_char c")
  case True
  then show ?thesis
    by (elim disjE) (simp_all add: unmangle_code_def is_ident_char_def)
next
  case False
  then have "mangle_chars first [c] @ rest = CHR ''z'' # CHR ''x'' # hex2 (of_char c) @ rest"
    by simp
  then show ?thesis
    by (simp only: unmangle_chars_zx[OF nat_of_char_less_256] char_of_char)
qed

lemma unmangle_mangle_chars:
  "unmangle_chars (mangle_chars first s @ rest) = map_option ((@) s) (unmangle_chars rest)"
proof (induction s arbitrary: first rest)
  case Nil
  then show ?case by (cases "unmangle_chars rest") simp_all
next
  case (Cons c cs)
  have "mangle_chars first (c # cs) @ rest = mangle_chars first [c] @ (mangle_chars False cs @ rest)"
    by simp
  then show ?case
    by (simp only: unmangle_mangle_char Cons.IH option.map_comp comp_def append_Cons)
qed

lemma mangle_chars_injective:
  "mangle_chars first x = mangle_chars first y \<Longrightarrow> x = y"
  using unmangle_mangle_chars[of first x "[]"] unmangle_mangle_chars[of first y "[]"]
  by simp

(* The two facts about the reserved names themselves, checked by computation:
   none decodes once a `z` is appended, and none ends in `z`. *)
lemma reserved_names_facts:
  "list_all (\<lambda>r. unmangle_chars (r @ ''z'') = None \<and> r \<noteq> [] \<and> last r \<noteq> CHR ''z'') reserved_names"
  by (simp add: reserved_names_def helper_names_def helper_name_def all_ctys_def all_int_tys_def
                unmangle_code_def unhex_digit_def char_of_eq_iff take_bit_eq_mod)

lemma reserved_name_z_not_mangled:
  assumes "r \<in> set reserved_names"
  shows "r @ ''z'' \<noteq> mangle_chars first s"
proof
  assume "r @ ''z'' = mangle_chars first s"
  then have "unmangle_chars (r @ ''z'') = Some s"
    using unmangle_mangle_chars[of first s "[]"] by simp
  with assms reserved_names_facts show False
    by (simp add: list_all_iff)
qed

lemma reserved_name_last:
  assumes "r \<in> set reserved_names"
  shows "last r \<noteq> CHR ''z''"
  using assms reserved_names_facts by (simp add: list_all_iff)

theorem mangle_injective:
  assumes "mangle x = mangle y"
  shows "x = y"
proof -
  let ?mx = "mangle_chars True x" and ?my = "mangle_chars True y"
  consider (both) "?mx \<in> set reserved_names" "?my \<in> set reserved_names"
    | (neither) "?mx \<notin> set reserved_names" "?my \<notin> set reserved_names"
    | (xonly) "?mx \<in> set reserved_names" "?my \<notin> set reserved_names"
    | (yonly) "?mx \<notin> set reserved_names" "?my \<in> set reserved_names"
    by blast
  then show ?thesis
  proof cases
    case both
    with assms have "?mx @ ''z'' = ?my @ ''z''" by (simp add: mangle_def)
    then have "?mx = ?my" by simp
    then show ?thesis by (rule mangle_chars_injective)
  next
    case neither
    with assms have "?mx = ?my" by (simp add: mangle_def)
    then show ?thesis by (rule mangle_chars_injective)
  next
    case xonly
    with assms have "?mx @ ''z'' = ?my" by (simp add: mangle_def)
    with xonly(1) show ?thesis using reserved_name_z_not_mangled by blast
  next
    case yonly
    with assms have "?my @ ''z'' = ?mx" by (simp add: mangle_def)
    with yonly(2) show ?thesis using reserved_name_z_not_mangled by blast
  qed
qed

corollary inj_mangle: "inj mangle"
  by (rule injI) (rule mangle_injective)

theorem mangle_not_reserved: "mangle x \<notin> set reserved_names"
proof
  assume reserved: "mangle x \<in> set reserved_names"
  show False
  proof (cases "mangle_chars True x \<in> set reserved_names")
    case True
    then have "mangle x = mangle_chars True x @ ''z''" by (simp add: mangle_def)
    then have "last (mangle x) = CHR ''z''" by simp
    with reserved show False using reserved_name_last by blast
  next
    case False
    then have "mangle x = mangle_chars True x" by (simp add: mangle_def)
    with False reserved show False by simp
  qed
qed


section \<open>Extern C names\<close>

(* An extern function is printed under its C name, unmangled, so that name
   shares the file's namespace with the mangled MiniC names. The typing
   judgement (MiniCTyping.thy) keeps variables apart from MiniC function
   names, but knows nothing of mangling or of C names, so the clashes an
   extern's C name can cause are found by a separate, executable check on the
   MiniC program, run before it is printed:

    - no global variable and no non-extern function may have a mangled name
      equal to an extern's C name (both are declared at file scope);
    - at a call of an extern, no variable in scope (a parameter or a local)
      may have a mangled name equal to the C name being called (the variable
      would hide the function, and C rejects the call).

   A variable whose mangled name is an extern's C name but which is not in
   scope at any call of that extern is fine: it hides the function harmlessly.
   Two externs with the same C name are not checked: C accepts a repeated
   prototype when the types agree, and the C compiler reports the clash when
   they do not. Checked by the driver (Main.hs, --minic) and, once there is a
   code generator, by its driver before printing its output; a clash is a
   compile error whose message names the function and variable involved.
   See DESIGN.md, section 3.9. *)

datatype MExternClash =
  EC_Global string string
    (* EC_Global x cname: the global variable x is printed as cname, an extern's C name *)
  | EC_Function string string
    (* EC_Function f cname: the (non-extern) function f is printed as cname, an extern's C name *)
  | EC_Local string string string
    (* EC_Local f x cname: in function f, the parameter or local x, printed as cname,
       is in scope at a call of the extern with C name cname *)

definition extern_cnames :: "MProgram \<Rightarrow> string list" where
  "extern_cnames prog = List.map_filter MF_Extern (MP_Funcs prog)"

definition global_extern_clashes :: "MProgram \<Rightarrow> MExternClash list" where
  "global_extern_clashes prog =
    [EC_Global x (mangle x). x \<leftarrow> map fst (MP_Globals prog), mangle x \<in> set (extern_cnames prog)]
    @ [EC_Function f (mangle f). f \<leftarrow> map MF_Name (filter (\<lambda>f. MF_Extern f = None) (MP_Funcs prog)),
                                  mangle f \<in> set (extern_cnames prog)]"

(* The variables in scope are threaded through a statement list as in
   stmts_ok (declarations extend the scope; a nested scope's declarations are
   dropped at its end). *)
fun stmt_extern_clashes :: "MProgram \<Rightarrow> string \<Rightarrow> string list \<Rightarrow> MStmt \<Rightarrow> MExternClash list \<times> string list"
and stmts_extern_clashes :: "MProgram \<Rightarrow> string \<Rightarrow> string list \<Rightarrow> MStmt list \<Rightarrow> MExternClash list" where
  "stmt_extern_clashes prog f sc (MS_DeclScalar x _) = ([], x # sc)"
| "stmt_extern_clashes prog f sc (MS_DeclBuf x _) = ([], x # sc)"
| "stmt_extern_clashes prog f sc (MS_If _ t e) =
    (stmts_extern_clashes prog f sc t @ stmts_extern_clashes prog f sc e, sc)"
| "stmt_extern_clashes prog f sc (MS_Loop body) = (stmts_extern_clashes prog f sc body, sc)"
| "stmt_extern_clashes prog f sc (MS_Block body) = (stmts_extern_clashes prog f sc body, sc)"
| "stmt_extern_clashes prog f sc (MS_Call _ g _) =
    ((case lookup_fun prog g of
        Some gf \<Rightarrow> (case MF_Extern gf of
                      Some cname \<Rightarrow> [EC_Local f x cname. x \<leftarrow> sc, mangle x = cname]
                    | None \<Rightarrow> [])
      | None \<Rightarrow> []), sc)"
| "stmt_extern_clashes prog f sc _ = ([], sc)"

| "stmts_extern_clashes prog f sc [] = []"
| "stmts_extern_clashes prog f sc (s # ss) =
    (let (cs, sc') = stmt_extern_clashes prog f sc s
     in cs @ stmts_extern_clashes prog f sc' ss)"

definition fun_extern_clashes :: "MProgram \<Rightarrow> MFun \<Rightarrow> MExternClash list" where
  "fun_extern_clashes prog f =
    (if MF_Extern f \<noteq> None then []
     else stmts_extern_clashes prog (MF_Name f) (map fst (MF_Params f)) (MF_Body f))"

(* All the clashes of a program, each reported once. The program may be
   printed if this is empty. *)
definition extern_clashes :: "MProgram \<Rightarrow> MExternClash list" where
  "extern_clashes prog =
    remdups (global_extern_clashes prog @ concat (map (fun_extern_clashes prog) (MP_Funcs prog)))"

(* The message for a clash. (Core carries no source locations yet, so
   messages name functions and variables.) *)
fun extern_clash_message :: "MExternClash \<Rightarrow> string" where
  "extern_clash_message (EC_Global x cname) =
    ''the global variable '' @ x @ '' would be printed as '' @ cname
    @ '', which is the C name of an extern function''"
| "extern_clash_message (EC_Function f cname) =
    ''the function '' @ f @ '' would be printed as '' @ cname
    @ '', which is the C name of an extern function''"
| "extern_clash_message (EC_Local f x cname) =
    ''in function '' @ f @ '', the variable '' @ x @ '' would be printed as '' @ cname
    @ '' and is in scope at a call of the extern function of that C name''"


section \<open>Types and literals\<close>

fun cty_name :: "CTy \<Rightarrow> string" where
  "cty_name (CTy_Int s b) = (case s of Signed \<Rightarrow> ''int'' | Unsigned \<Rightarrow> ''uint'') @ nat_to_string (bit_size b) @ ''_t''"
| "cty_name CTy_CharPtr = ''char *''"
| "cty_name CTy_VoidPtr = ''void *''"

(* INT32_C(5), (-INT32_C(5)), and ((-INT32_C(2147483647)) - 1) for the most
   negative value, whose magnitude does not fit the type. *)
definition print_int_lit :: "Signedness \<Rightarrow> IntBits \<Rightarrow> int \<Rightarrow> string" where
  "print_int_lit s b i =
    (let macro = (\<lambda>n. (case s of Signed \<Rightarrow> ''INT'' | Unsigned \<Rightarrow> ''UINT'')
                      @ nat_to_string (bit_size b) @ ''_C('' @ nat_to_string n @ '')'')
     in if i \<ge> 0 then macro (nat i)
        else if i = fst (int_range s b) then ''((-'' @ macro (nat (- i - 1)) @ '') - 1)''
        else ''(-'' @ macro (nat (- i)) @ '')'')"


section \<open>Expressions\<close>

(* Wrap s in a cast to ty, if the type is known. *)
definition cast_to :: "CTy option \<Rightarrow> string \<Rightarrow> string" where
  "cast_to tyopt s = (case tyopt of Some ty \<Rightarrow> ''(('' @ cty_name ty @ '') '' @ s @ '')'' | None \<Rightarrow> s)"

fun binop_symbol :: "CBinop \<Rightarrow> string" where
  "binop_symbol CB_Add = ''+''"
| "binop_symbol CB_Sub = ''-''"
| "binop_symbol CB_Mul = ''*''"
| "binop_symbol CB_Div = ''/''"
| "binop_symbol CB_Mod = ''%''"
| "binop_symbol CB_BitAnd = ''&''"
| "binop_symbol CB_BitOr = ''|''"
| "binop_symbol CB_BitXor = ''^''"
| "binop_symbol CB_Shl = ''<<''"
| "binop_symbol CB_Shr = ''>>''"
| "binop_symbol CB_Eq = ''==''"
| "binop_symbol CB_Ne = ''!=''"
| "binop_symbol CB_Lt = ''<''"
| "binop_symbol CB_Le = ''<=''"
| "binop_symbol CB_Gt = ''>''"
| "binop_symbol CB_Ge = ''>=''"
| "binop_symbol CB_Max = ''max''"

(* `cexpr` is true at file scope (the size of a global buffer), where the
   result must be a constant expression and no helper may be called. *)
fun print_expr :: "bool \<Rightarrow> MTyEnv \<Rightarrow> MExpr \<Rightarrow> string" where
  "print_expr cexpr env (ME_Int s b i) = print_int_lit s b i"
| "print_expr cexpr env ME_PtrSize = ''((uint64_t) sizeof(void *))''"
| "print_expr cexpr env (ME_Var x) = mangle x"
| "print_expr cexpr env (ME_AddrOf x) =
    (case fmlookup env x of
       Some VT_Buf \<Rightarrow> mangle x
     | _ \<Rightarrow> ''((char *) &'' @ mangle x @ '')'')"
| "print_expr cexpr env (ME_Load ty e) =
    helper_name ''load'' ty @ ''('' @ print_expr cexpr env e @ '')''"
| "print_expr cexpr env (ME_Unop op e) =
    (let s = print_expr cexpr env e
     in case op of
          CU_Not \<Rightarrow> ''((uint8_t) (!('' @ s @ '')))''
        | CU_Neg \<Rightarrow> cast_to (expr_type env e) (''(-('' @ s @ ''))'')
        | CU_Compl \<Rightarrow> cast_to (expr_type env e) (''(~('' @ s @ ''))''))"
| "print_expr cexpr env (ME_Binop op e1 e2) =
    (let s1 = print_expr cexpr env e1; s2 = print_expr cexpr env e2;
         ty1 = expr_type env e1;
         plain = ''(('' @ s1 @ '') '' @ binop_symbol op @ '' ('' @ s2 @ ''))''
     in if is_cmp op then ''((uint8_t) '' @ plain @ '')''
        else if is_shift op \<or> op = CB_Max then
          (case ty1 of
             Some ty \<Rightarrow>
               if op = CB_Max \<and> cexpr
               then ''((('' @ s1 @ '') > ('' @ s2 @ '')) ? ('' @ s1 @ '') : ('' @ s2 @ ''))''
               else helper_name (case op of CB_Shl \<Rightarrow> ''shl'' | CB_Shr \<Rightarrow> ''shr'' | _ \<Rightarrow> ''max'') ty
                    @ ''('' @ s1 @ '', '' @ s2 @ '')''
           | None \<Rightarrow> plain)
        else cast_to ty1 plain)"
| "print_expr cexpr env (ME_Cast ty e) =
    ''(('' @ cty_name ty @ '') ('' @ print_expr cexpr env e @ ''))''"
| "print_expr cexpr env (ME_PtrAdd e1 e2) =
    ''(((char *) ('' @ print_expr cexpr env e1 @ '')) + ('' @ print_expr cexpr env e2 @ ''))''"


section \<open>Printer options\<close>

(* How MS_Uninit (MiniCSyntax.thy) is printed. UP_Memset prints it as
   memset(p, 0, n): the region becomes defined (zero is one of the values the
   semantics allows for undefined bytes), so a later memmove of a variant
   buffer whose bytes after the payload were never written does not trigger
   gcc's -Wuninitialized (DESIGN.md 11.4). UP_Omit prints nothing: the bytes
   are left as the C implementation leaves them, which is also what the
   semantics says, and no memset is executed. *)
datatype UninitPrint = UP_Memset | UP_Omit

record PrintOpts =
  PO_Uninit :: UninitPrint

definition default_print_opts :: PrintOpts where
  "default_print_opts = \<lparr> PO_Uninit = UP_Memset \<rparr>"


section \<open>Statements\<close>

(* The name a call to f is printed with: the C name of an extern, otherwise
   the mangled MiniC name. *)
definition print_fun_name :: "MProgram \<Rightarrow> string \<Rightarrow> string" where
  "print_fun_name prog f =
    (case lookup_fun prog f of
       Some fn \<Rightarrow> (case MF_Extern fn of Some cname \<Rightarrow> cname | None \<Rightarrow> mangle f)
     | None \<Rightarrow> mangle f)"

(* Statements are printed as indented lines; the environment is extended by
   declarations, as in stmts_ok. *)
fun print_stmt :: "PrintOpts \<Rightarrow> MProgram \<Rightarrow> nat \<Rightarrow> MTyEnv \<Rightarrow> MStmt \<Rightarrow> string list \<times> MTyEnv"
and print_stmts :: "PrintOpts \<Rightarrow> MProgram \<Rightarrow> nat \<Rightarrow> MTyEnv \<Rightarrow> MStmt list \<Rightarrow> string list" where
  "print_stmt opts prog n env (MS_DeclScalar x ty) =
    ([indent n (cty_name ty @ '' '' @ mangle x @ '';'')], fmupd x (VT_Scalar ty) env)"
| "print_stmt opts prog n env (MS_DeclBuf x e) =
    ([indent n (''char '' @ mangle x @ ''['' @ print_expr False env e @ ''];'')], fmupd x VT_Buf env)"
| "print_stmt opts prog n env (MS_Assign x e) =
    ([indent n (mangle x @ '' = '' @ print_expr False env e @ '';'')], env)"
| "print_stmt opts prog n env (MS_Store ty p e) =
    ([indent n (helper_name ''store'' ty @ ''('' @ print_expr False env p @ '', ''
                @ print_expr False env e @ '');'')], env)"
| "print_stmt opts prog n env (MS_Copy d s sz) =
    ([indent n (''memmove('' @ print_expr False env d @ '', '' @ print_expr False env s @ '', ''
                @ print_expr False env sz @ '');'')], env)"
| "print_stmt opts prog n env (MS_Zero p sz) =
    ([indent n (''memset('' @ print_expr False env p @ '', 0, '' @ print_expr False env sz @ '');'')], env)"
| "print_stmt opts prog n env (MS_Uninit p sz) =
    ((case PO_Uninit opts of
        UP_Memset \<Rightarrow> [indent n (''memset('' @ print_expr False env p @ '', 0, '' @ print_expr False env sz @ '');'')]
      | UP_Omit \<Rightarrow> []), env)"
| "print_stmt opts prog n env (MS_If c t e) =
    ([indent n (''if ('' @ print_expr False env c @ '') {'')]
     @ print_stmts opts prog (Suc n) env t
     @ (if e = [] then [indent n ''}'']
        else [indent n ''} else {''] @ print_stmts opts prog (Suc n) env e @ [indent n ''}'']),
     env)"
| "print_stmt opts prog n env (MS_Loop body) =
    ([indent n ''while (1) {''] @ print_stmts opts prog (Suc n) env body @ [indent n ''}''], env)"
| "print_stmt opts prog n env MS_Break = ([indent n ''break;''], env)"
| "print_stmt opts prog n env (MS_Block body) =
    ([indent n ''{''] @ print_stmts opts prog (Suc n) env body @ [indent n ''}''], env)"
| "print_stmt opts prog n env (MS_Call xopt f args) =
    ([indent n ((case xopt of None \<Rightarrow> '''' | Some x \<Rightarrow> mangle x @ '' = '')
                @ print_fun_name prog f @ ''('' @ intercalate '', '' (map (print_expr False env) args) @ '');'')],
     env)"
| "print_stmt opts prog n env (MS_Return None) = ([indent n ''return;''], env)"
| "print_stmt opts prog n env (MS_Return (Some e)) =
    ([indent n (''return '' @ print_expr False env e @ '';'')], env)"

| "print_stmts opts prog n env [] = []"
| "print_stmts opts prog n env (s # ss) =
    (let (ls, env') = print_stmt opts prog n env s
     in ls @ print_stmts opts prog n env' ss)"


section \<open>Functions, globals, the file\<close>

(* `int main(void)`; otherwise the declared return type (void if none) and the
   parameters (void if none). *)
definition print_fun_header :: "MFun \<Rightarrow> string" where
  "print_fun_header f =
    (let ret = (if MF_Name f = ''main'' then ''int''
                else case MF_Ret f of None \<Rightarrow> ''void'' | Some ty \<Rightarrow> cty_name ty);
         name = (case MF_Extern f of Some cname \<Rightarrow> cname | None \<Rightarrow> mangle (MF_Name f));
         params = (if MF_Params f = [] then ''void''
                   else intercalate '', '' (map (\<lambda>(x, ty). cty_name ty @ '' '' @ mangle x) (MF_Params f)))
     in ret @ '' '' @ name @ ''('' @ params @ '')'')"

definition print_fun_proto :: "MFun \<Rightarrow> string list" where
  "print_fun_proto f = [print_fun_header f @ '';'']"

(* The body of a non-extern function, with the parameters in scope. *)
definition print_fun_def :: "PrintOpts \<Rightarrow> MProgram \<Rightarrow> MFun \<Rightarrow> string list" where
  "print_fun_def opts prog f =
    (if MF_Extern f \<noteq> None then []
     else
       (let env = foldl (\<lambda>env (x, ty). fmupd x (VT_Scalar ty) env) (globals_env prog) (MF_Params f)
        in [print_fun_header f @ '' {''] @ print_stmts opts prog 1 env (MF_Body f) @ [''}'', ''''] ))"

definition print_global :: "string \<times> MGlobal \<Rightarrow> string" where
  "print_global xg =
    (case snd xg of
       MG_Scalar ty \<Rightarrow> cty_name ty @ '' '' @ mangle (fst xg) @ '';''
     | MG_Buf e \<Rightarrow> ''char '' @ mangle (fst xg) @ ''['' @ print_expr True fmempty e @ ''];'')"

(* The helper functions, for one C type. The shift helpers implement the idiom
   of codegen.c (shift_binop); see DESIGN.md section 5.3. *)
definition unsigned_of :: "IntBits \<Rightarrow> string" where
  "unsigned_of b = cty_name (CTy_Int Unsigned b)"

definition print_helpers_for :: "CTy \<Rightarrow> string list" where
  "print_helpers_for ty =
    (let t = cty_name ty; sfx = cty_suffix ty
     in [ ''static inline '' @ t @ '' bab_load_'' @ sfx @ ''(const void *p) { ''
            @ t @ '' v; memcpy(&v, p, sizeof v); return v; }'',
          ''static inline void bab_store_'' @ sfx @ ''(void *p, '' @ t @ '' v) { memcpy(p, &v, sizeof v); }'' ]
        @ (case ty of
             CTy_Int s b \<Rightarrow>
               [ ''static inline '' @ t @ '' bab_max_'' @ sfx @ ''('' @ t @ '' a, '' @ t @ '' b) { return ('' @ t
                   @ '') (a > b ? a : b); }'' ]
               @ (case s of
                    Unsigned \<Rightarrow>
                      [ ''static inline '' @ t @ '' bab_shl_'' @ sfx @ ''('' @ t @ '' x, uint64_t n) { return ('' @ t
                          @ '') ((x + 0u) << n); }'',
                        ''static inline '' @ t @ '' bab_shr_'' @ sfx @ ''('' @ t @ '' x, uint64_t n) { return ('' @ t
                          @ '') ((x + 0u) >> n); }'' ]
                  | Signed \<Rightarrow>
                      [ ''static inline '' @ t @ '' bab_shl_'' @ sfx @ ''('' @ t @ '' x, uint64_t n) { ''
                          @ unsigned_of b @ '' u = ((('' @ unsigned_of b @ '') x) + 0u) << n; ''
                          @ t @ '' r; memcpy(&r, &u, sizeof r); return r; }'',
                        ''static inline '' @ t @ '' bab_shr_'' @ sfx @ ''('' @ t @ '' x, uint64_t n) { return ('' @ t
                          @ '') (x >> n); }'' ])
           | _ \<Rightarrow> []))"

definition print_prelude :: "string list" where
  "print_prelude =
    [ ''/* Generated by the Babylon MiniC printer. Do not edit. */'',
      ''#include <limits.h>'',
      ''#include <stdint.h>'',
      ''#include <string.h>'',
      '''',
      ''#if CHAR_BIT != 8'',
      ''#error CHAR_BIT must be 8'',
      ''#endif'',
      ''#if (-1 & 3) != 3'',
      ''#error a two-complement representation of signed integers is required'',
      ''#endif'',
      ''#if (-1 >> 1) != -1'',
      ''#error an arithmetic right shift of negative values is required'',
      ''#endif'',
      '''' ]
    @ concat (map print_helpers_for all_ctys)
    @ ['''']"

definition print_program :: "PrintOpts \<Rightarrow> MProgram \<Rightarrow> string" where
  "print_program opts prog =
    unlines
      (print_prelude
       @ map print_global (MP_Globals prog)
       @ ['''']
       @ concat (map print_fun_proto (MP_Funcs prog))
       @ ['''']
       @ concat (map (print_fun_def opts prog) (MP_Funcs prog)))"

end
