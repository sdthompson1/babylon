theory MatchCompile
  imports "../core/CoreSyntax"
begin

(* Core-to-Core pattern-match compilation.

   Input:  nested CorePatterns (CorePat_Variant with arbitrary payload
           sub-patterns, CorePat_Record with arbitrary nested field
           patterns).
   Output: a MatchTree IR whose every test pattern satisfies
           `flat_pattern` (see core/CoreSyntax.thy).

   Algorithm: Maranget-style matrix compilation with the "first
   non-wildcard column" heuristic. Record columns are decomposed
   losslessly into their field sub-columns. Bool/Int/Variant columns
   are tested via MT_Test with one arm per distinct head value and an
   optional trailing wildcard arm.

   This pass is polymorphic in the arm body type 'body. The same
   algorithm therefore serves both term-level matches (where the body
   is a CoreTerm) and statement-level matches (where the body is a
   CoreStatement list). Translation from MatchTree back to a CoreTerm
   or CoreStatement list is the consumer's responsibility and lives
   outside this file.

   Variable binding is not the concern of this pass. CorePattern has
   no variable-binding patterns: pattern variables in the source
   language are elaborated to Lets emitted around match arm bodies
   before this pass runs. The matrix therefore carries only patterns
   and arm bodies, with no per-row bind list. *)


section \<open>MatchTree IR\<close>

(* Parametric over the arm body type:
     'body = CoreTerm           for term matches
     'body = CoreStatement list for statement matches

   MT_Test's arm list may be non-exhaustive; a runtime match failure
   is signalled by the downstream consumer (the Core interpreter
   produces a runtime error). Every pattern in an MT_Test arm
   satisfies `flat_pattern` by construction. *)
datatype 'body MatchTree =
    MT_Leaf 'body
  | MT_Test CoreTerm "(CorePattern \<times> 'body MatchTree) list"


section \<open>Matrix representation\<close>

(* A row is a column-pattern list paired with an arm body.
   Matrix invariant: every row's pattern list has length = length scruts. *)
type_synonym 'body Row = "CorePattern list \<times> 'body"

type_synonym 'body MatchMatrix = "CoreTerm list \<times> 'body Row list"


section \<open>Column / scrutinee plumbing\<close>

fun replace_at :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "replace_at _ _ [] = []"
| "replace_at 0 y (_ # xs) = y # xs"
| "replace_at (Suc c) y (x # xs) = x # replace_at c y xs"

fun drop_at :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "drop_at _ [] = []"
| "drop_at 0 (_ # xs) = xs"
| "drop_at (Suc c) (x # xs) = x # drop_at c xs"

(* Replace element at position c with a list, splicing in place. *)
fun splice_at :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "splice_at _ _ [] = []"
| "splice_at 0 ys (_ # xs) = ys @ xs"
| "splice_at (Suc c) ys (x # xs) = x # splice_at c ys xs"


section \<open>Column-head classification\<close>

(* A pattern is "wildcard-like" if it always matches at this column.
   In Core there is only CorePat_Wildcard; the elaborator's pattern
   variables have already been compiled away. *)
fun is_wildcard_like :: "CorePattern \<Rightarrow> bool" where
  "is_wildcard_like CorePat_Wildcard = True"
| "is_wildcard_like _ = False"

(* Smallest column index c such that row 0 is non-wildcard at c.
   Returns None if row 0 is all wildcard-like, the matrix is empty,
   or row lengths differ from row 0's length. *)
definition first_non_wildcard_col :: "CorePattern list list \<Rightarrow> nat option" where
  "first_non_wildcard_col rows =
    (case rows of
       [] \<Rightarrow> None
     | r0 # _ \<Rightarrow>
         if list_all (\<lambda>r. length r = length r0) rows
         then find (\<lambda>c. \<not> is_wildcard_like (r0 ! c))
                   [0 ..< length r0]
         else None)"

(* Classify a column's head: record (decompose), variant/bool/int
   (specialise via MT_Test), or None (wildcard, no head). *)
datatype HeadKind =
    HK_Record "string list"   (* field names, in declaration order *)
  | HK_Variant
  | HK_Bool
  | HK_Int

fun head_kind_of :: "CorePattern \<Rightarrow> HeadKind option" where
  "head_kind_of CorePat_Wildcard = None"
| "head_kind_of (CorePat_Bool _) = Some HK_Bool"
| "head_kind_of (CorePat_Int _) = Some HK_Int"
| "head_kind_of (CorePat_Variant _ _) = Some HK_Variant"
| "head_kind_of (CorePat_Record flds) = Some (HK_Record (map fst flds))"


section \<open>Row specialisation\<close>

(* Bool: matching bool survives with col c dropped; non-matching bool
   drops the row; wildcard survives with col c dropped. *)
fun specialise_row_bool ::
  "nat \<Rightarrow> bool \<Rightarrow> 'body Row \<Rightarrow> 'body Row option"
where
  "specialise_row_bool c h (ps, body) =
    (case ps ! c of
       CorePat_Bool b \<Rightarrow>
         if b = h then Some (drop_at c ps, body) else None
     | CorePat_Wildcard \<Rightarrow> Some (drop_at c ps, body)
     | _ \<Rightarrow> None)"   \<comment> \<open>unreachable: col must have bool/wildcard heads\<close>

(* Int: same shape as bool. *)
fun specialise_row_int ::
  "nat \<Rightarrow> int \<Rightarrow> 'body Row \<Rightarrow> 'body Row option"
where
  "specialise_row_int c h (ps, body) =
    (case ps ! c of
       CorePat_Int i \<Rightarrow>
         if i = h then Some (drop_at c ps, body) else None
     | CorePat_Wildcard \<Rightarrow> Some (drop_at c ps, body)
     | _ \<Rightarrow> None)"

(* Variant: matching ctor with payload sub-pattern p; col c becomes p
   (caller substitutes a CoreTm_VariantProj scrutinee at this column).
   Wildcard at col c is treated as a wildcard payload. *)
fun specialise_row_variant ::
  "nat \<Rightarrow> string \<Rightarrow> 'body Row \<Rightarrow> 'body Row option"
where
  "specialise_row_variant c h (ps, body) =
    (case ps ! c of
       CorePat_Variant h' payload \<Rightarrow>
         if h' = h then Some (replace_at c payload ps, body) else None
     | CorePat_Wildcard \<Rightarrow>
         Some (replace_at c CorePat_Wildcard ps, body)
     | _ \<Rightarrow> None)"

(* Default arm: row survives only if col c is wildcard. *)
fun default_row :: "nat \<Rightarrow> 'body Row \<Rightarrow> 'body Row option" where
  "default_row c (ps, body) =
    (case ps ! c of
       CorePat_Wildcard \<Rightarrow> Some (drop_at c ps, body)
     | _ \<Rightarrow> None)"


section \<open>Record decomposition\<close>

(* Expand a row's record column c into sub-columns (one per field).
   CorePat_Record: sub-patterns in declaration order (the type system
   guarantees field name + order agreement via pattern_compatible).
   CorePat_Wildcard: fill with wildcards. *)
fun expand_record_row ::
  "nat \<Rightarrow> string list \<Rightarrow> 'body Row \<Rightarrow> 'body Row"
where
  "expand_record_row c fld_names (ps, body) =
    (case ps ! c of
       CorePat_Record row_flds \<Rightarrow>
         (splice_at c (map snd row_flds) ps, body)
     | CorePat_Wildcard \<Rightarrow>
         (splice_at c (replicate (length fld_names) CorePat_Wildcard) ps, body)
     | _ \<Rightarrow> (ps, body))"   \<comment> \<open>unreachable: col must be record-headed or wildcard\<close>

(* Scrutinee at col c is replaced by one CoreTm_RecordProj per field. *)
definition expand_record_scruts ::
  "nat \<Rightarrow> CoreTerm \<Rightarrow> string list \<Rightarrow> CoreTerm list \<Rightarrow> CoreTerm list"
where
  "expand_record_scruts c s fld_names scruts =
    splice_at c (map (\<lambda>f. CoreTm_RecordProj s f) fld_names) scruts"


section \<open>Head enumeration\<close>

(* Distinct heads of a testable column, first-appearance order.
   Filtering subsequent occurrences of the just-seen head is O(n^2),
   but match arm lists are short in practice. *)

fun distinct_bool_heads :: "CorePattern list \<Rightarrow> bool list" where
  "distinct_bool_heads [] = []"
| "distinct_bool_heads (CorePat_Bool b # rest) =
    b # distinct_bool_heads (filter (\<lambda>p. p \<noteq> CorePat_Bool b) rest)"
| "distinct_bool_heads (_ # rest) = distinct_bool_heads rest"

fun distinct_int_heads :: "CorePattern list \<Rightarrow> int list" where
  "distinct_int_heads [] = []"
| "distinct_int_heads (CorePat_Int i # rest) =
    i # distinct_int_heads (filter (\<lambda>p. p \<noteq> CorePat_Int i) rest)"
| "distinct_int_heads (_ # rest) = distinct_int_heads rest"

(* Every CorePattern variant carries a payload sub-pattern, so the
   distinct heads list only needs the ctor names. *)
fun distinct_variant_heads :: "CorePattern list \<Rightarrow> string list" where
  "distinct_variant_heads [] = []"
| "distinct_variant_heads (CorePat_Variant h _ # rest) =
    h # distinct_variant_heads
          (filter (\<lambda>p. case p of CorePat_Variant h' _ \<Rightarrow> h' \<noteq> h | _ \<Rightarrow> True) rest)"
| "distinct_variant_heads (_ # rest) = distinct_variant_heads rest"


section \<open>Termination metric\<close>

(* Weight for use in compile_matrix's termination proof. CorePat_Wildcard
   has weight 0; constructor patterns have weight 1 plus the weight of
   their immediate children. Record/variant decomposition strictly
   reduces this weight on at least one row. *)
fun core_pattern_weight :: "CorePattern \<Rightarrow> nat" where
  "core_pattern_weight CorePat_Wildcard = 0"
| "core_pattern_weight (CorePat_Bool _) = 1"
| "core_pattern_weight (CorePat_Int _) = 1"
| "core_pattern_weight (CorePat_Variant _ p) = Suc (core_pattern_weight p)"
| "core_pattern_weight (CorePat_Record flds) =
    Suc (sum_list (map (core_pattern_weight \<circ> snd) flds))"

fun row_weight :: "'body Row \<Rightarrow> nat" where
  "row_weight (ps, _) = sum_list (map core_pattern_weight ps)"

definition matrix_weight :: "'body MatchMatrix \<Rightarrow> nat" where
  "matrix_weight m = sum_list (map row_weight (snd m))"


section \<open>The algorithm\<close>

(* Maranget-style matrix compilation. Precondition: matrix has at
   least one row; every row has length = length scruts.

   Base case (row 0's columns all wildcard): emit row 0's body. Any
   later rows are dead, because row 0 always matches in this case.

   Testable column (Bool/Int/Variant): emit MT_Test with one arm per
   distinct head value and an optional trailing wildcard arm when the
   column has any wildcard rows.

   Record column: lossless decomposition; no MT_Test emitted here. *)
function compile_matrix :: "'body MatchMatrix \<Rightarrow> 'body MatchTree" where
  "compile_matrix (scruts, rows) =
    (case first_non_wildcard_col (map fst rows) of
       None \<Rightarrow>
         (case rows of
            [] \<Rightarrow> undefined   \<comment> \<open>precondition violated: zero-row matrix\<close>
          | (_, body) # _ \<Rightarrow> MT_Leaf body)
     | Some c \<Rightarrow>
         (let s_c = scruts ! c;
              col_pats = map (\<lambda>(ps, _). ps ! c) rows;
              has_default = list_ex is_wildcard_like col_pats;
              default_rows = List.map_filter (default_row c) rows;
              default_arm =
                (if has_default
                 then [(CorePat_Wildcard,
                        compile_matrix (drop_at c scruts, default_rows))]
                 else [])
          in (case head_kind_of (hd (filter (\<lambda>p. \<not> is_wildcard_like p) col_pats)) of
                Some HK_Bool \<Rightarrow>
                  (let heads = distinct_bool_heads col_pats;
                       head_arm = (\<lambda>h.
                         (CorePat_Bool h,
                          compile_matrix (drop_at c scruts,
                            List.map_filter (specialise_row_bool c h) rows)))
                   in MT_Test s_c (map head_arm heads @ default_arm))
              | Some HK_Int \<Rightarrow>
                  (let heads = distinct_int_heads col_pats;
                       head_arm = (\<lambda>h.
                         (CorePat_Int h,
                          compile_matrix (drop_at c scruts,
                            List.map_filter (specialise_row_int c h) rows)))
                   in MT_Test s_c (map head_arm heads @ default_arm))
              | Some HK_Variant \<Rightarrow>
                  (let heads = distinct_variant_heads col_pats;
                       head_arm = (\<lambda>h.
                         let new_scruts = replace_at c (CoreTm_VariantProj s_c h) scruts
                         in (CorePat_Variant h CorePat_Wildcard,
                             compile_matrix (new_scruts,
                               List.map_filter (specialise_row_variant c h) rows)))
                   in MT_Test s_c (map head_arm heads @ default_arm))
              | Some (HK_Record fld_names) \<Rightarrow>
                  compile_matrix (expand_record_scruts c s_c fld_names scruts,
                                  map (expand_record_row c fld_names) rows)
              | None \<Rightarrow> undefined)))"   \<comment> \<open>None: unreachable (c was non-wildcard)\<close>
  by pat_completeness auto


section \<open>Termination\<close>

subsection \<open>Generic list arithmetic on sum_list under drop/replace/splice\<close>

lemma sum_list_drop_at_le:
  fixes f :: "'a \<Rightarrow> nat"
  shows "sum_list (map f (drop_at c xs)) \<le> sum_list (map f xs)"
  by (induction c xs rule: drop_at.induct) auto

lemma sum_list_drop_at_lt:
  fixes f :: "'a \<Rightarrow> nat"
  shows "c < length xs \<Longrightarrow> f (xs ! c) > 0 \<Longrightarrow>
    sum_list (map f (drop_at c xs)) < sum_list (map f xs)"
  by (induction c xs rule: drop_at.induct) auto

lemma sum_list_replace_at_le:
  fixes f :: "'a \<Rightarrow> nat"
  shows "c < length xs \<Longrightarrow> f y \<le> f (xs ! c) \<Longrightarrow>
    sum_list (map f (replace_at c y xs)) \<le> sum_list (map f xs)"
  by (induction c y xs rule: replace_at.induct) auto

lemma sum_list_replace_at_lt:
  fixes f :: "'a \<Rightarrow> nat"
  shows "c < length xs \<Longrightarrow> f y < f (xs ! c) \<Longrightarrow>
    sum_list (map f (replace_at c y xs)) < sum_list (map f xs)"
  by (induction c y xs rule: replace_at.induct) auto

lemma sum_list_splice_at_lt:
  fixes f :: "'a \<Rightarrow> nat"
  shows "c < length xs \<Longrightarrow> sum_list (map f ys) < f (xs ! c) \<Longrightarrow>
    sum_list (map f (splice_at c ys xs)) < sum_list (map f xs)"
  by (induction c ys xs rule: splice_at.induct) auto

lemma sum_list_splice_at_le:
  fixes f :: "'a \<Rightarrow> nat"
  shows "c < length xs \<Longrightarrow> sum_list (map f ys) \<le> f (xs ! c) \<Longrightarrow>
    sum_list (map f (splice_at c ys xs)) \<le> sum_list (map f xs)"
  by (induction c ys xs rule: splice_at.induct) auto


subsection \<open>Facts about first_non_wildcard_col\<close>

lemma first_non_wildcard_col_SomeD:
  assumes "first_non_wildcard_col rows = Some c"
  shows "rows \<noteq> []"
    and "\<forall>r \<in> set rows. c < length r"
    and "\<not> is_wildcard_like (hd rows ! c)"
proof -
  from assms show "rows \<noteq> []"
    unfolding first_non_wildcard_col_def by (auto split: list.splits if_splits)
next
  from assms obtain r0 rs where
    rows_eq: "rows = r0 # rs" and
    len_ok: "list_all (\<lambda>r. length r = length r0) rows" and
    find_some: "find (\<lambda>c. \<not> is_wildcard_like (r0 ! c))
                     [0 ..< length r0] = Some c"
    unfolding first_non_wildcard_col_def
    by (auto split: list.splits if_splits)
  from find_some have c_in: "c \<in> set [0 ..< length r0]"
    by (metis find_Some_iff2 nth_mem)
  hence c_lt_r0: "c < length r0" by auto
  from len_ok have "\<forall>r \<in> set rows. length r = length r0"
    by (simp add: list_all_iff)
  with c_lt_r0 show "\<forall>r \<in> set rows. c < length r" by auto
next
  from assms obtain r0 rs where
    rows_eq: "rows = r0 # rs" and
    find_some: "find (\<lambda>c. \<not> is_wildcard_like (r0 ! c))
                     [0 ..< length r0] = Some c"
    unfolding first_non_wildcard_col_def
    by (auto split: list.splits if_splits)
  from find_some have "\<not> is_wildcard_like (r0 ! c)"
    by (metis find_Some_iff)
  with rows_eq show "\<not> is_wildcard_like (hd rows ! c)" by simp
qed

lemma is_wildcard_like_iff_weight_zero:
  "is_wildcard_like p \<longleftrightarrow> core_pattern_weight p = 0"
  by (cases p) auto

lemma nth_le_sum_list:
  fixes f :: "'a \<Rightarrow> nat"
  shows "c < length xs \<Longrightarrow> f (xs ! c) \<le> sum_list (map f xs)"
  by (induction c xs rule: drop_at.induct) auto

lemma row_weight_pos_at_col:
  assumes "c < length (fst r)"
      and "core_pattern_weight (fst r ! c) > 0"
  shows "row_weight r > 0"
proof -
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  with assms have c_lt: "c < length ps" and pos: "core_pattern_weight (ps ! c) > 0"
    by auto
  from c_lt have "core_pattern_weight (ps ! c) \<le> sum_list (map core_pattern_weight ps)"
    by (rule nth_le_sum_list)
  with pos r_eq show ?thesis by simp
qed

lemma first_non_wildcard_col_head_weight_pos:
  assumes "first_non_wildcard_col (map fst rows) = Some c"
      and "rows \<noteq> []"
  shows "core_pattern_weight (fst (hd rows) ! c) > 0"
proof -
  from assms(2) obtain r0 rs where rows_eq: "rows = r0 # rs"
    by (cases rows) auto
  with assms(1) have nw: "\<not> is_wildcard_like (hd (map fst rows) ! c)"
    using first_non_wildcard_col_SomeD(3)[where rows = "map fst rows"] by simp
  from rows_eq have "hd (map fst rows) = fst r0" by simp
  with nw rows_eq show ?thesis
    using is_wildcard_like_iff_weight_zero by auto
qed

lemma first_non_wildcard_col_lengths:
  assumes "first_non_wildcard_col (map fst rows) = Some c"
  shows "\<forall>r \<in> set rows. c < length (fst r)"
proof -
  from assms have "\<forall>ps \<in> set (map fst rows). c < length ps"
    using first_non_wildcard_col_SomeD(2)[where rows = "map fst rows"] by simp
  thus ?thesis by auto
qed


subsection \<open>Row weight under specialisation / expansion\<close>

(* For each row transformation we prove an "le" version (always holds)
   and a "lt" version (fires when the row is the one driving the
   recursion). The "le" version is enough for all rows of the matrix;
   the "lt" version is needed only on at least one row to make the
   matrix-weight strictly decrease. *)

lemma row_weight_drop_at_le:
  "row_weight (drop_at c ps, body) \<le> row_weight (ps, body)"
  by (simp add: sum_list_drop_at_le)

lemma row_weight_drop_at_lt:
  "c < length ps \<Longrightarrow> core_pattern_weight (ps ! c) > 0 \<Longrightarrow>
    row_weight (drop_at c ps, body) < row_weight (ps, body)"
  by (simp add: sum_list_drop_at_lt)

lemma row_weight_replace_at_le:
  "c < length ps \<Longrightarrow> core_pattern_weight y \<le> core_pattern_weight (ps ! c) \<Longrightarrow>
    row_weight (replace_at c y ps, body) \<le> row_weight (ps, body)"
  by (simp add: sum_list_replace_at_le)

lemma row_weight_replace_at_lt:
  "c < length ps \<Longrightarrow> core_pattern_weight y < core_pattern_weight (ps ! c) \<Longrightarrow>
    row_weight (replace_at c y ps, body) < row_weight (ps, body)"
  by (simp add: sum_list_replace_at_lt)

(* Default row: only wildcard columns survive; col c is then dropped.
   Since the surviving column had weight 0, drop_at gives a non-strict
   bound. *)
lemma default_row_weight_le:
  assumes "default_row c r = Some r'"
  shows "row_weight r' \<le> row_weight r"
proof -
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  with assms show ?thesis
    by (cases "ps ! c") (auto simp: sum_list_drop_at_le)
qed

(* Bool specialisation: dropping col c. The matching-bool row has
   col-c weight 1, so we get strict decrease there; the wildcard row
   only gets <=. *)
lemma specialise_row_bool_weight_le:
  assumes "specialise_row_bool c h r = Some r'"
  shows "row_weight r' \<le> row_weight r"
proof -
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  with assms show ?thesis
    by (cases "ps ! c") (auto simp: sum_list_drop_at_le split: if_splits)
qed

lemma specialise_row_bool_weight_lt_on_bool:
  assumes "specialise_row_bool c h r = Some r'"
      and "c < length (fst r)"
      and "\<exists>b. fst r ! c = CorePat_Bool b"
  shows "row_weight r' < row_weight r"
proof -
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  from assms(3) r_eq obtain b where b_eq: "ps ! c = CorePat_Bool b" by auto
  from assms(1) r_eq b_eq have "r' = (drop_at c ps, body)"
    by (auto split: if_splits)
  moreover from assms(2) r_eq have c_lt: "c < length ps" by simp
  moreover from b_eq have "core_pattern_weight (ps ! c) > 0" by simp
  ultimately show ?thesis using r_eq row_weight_drop_at_lt by auto
qed

(* Int specialisation: mirror of bool. *)
lemma specialise_row_int_weight_le:
  assumes "specialise_row_int c h r = Some r'"
  shows "row_weight r' \<le> row_weight r"
proof -
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  with assms show ?thesis
    by (cases "ps ! c") (auto simp: sum_list_drop_at_le split: if_splits)
qed

lemma specialise_row_int_weight_lt_on_int:
  assumes "specialise_row_int c h r = Some r'"
      and "c < length (fst r)"
      and "\<exists>i. fst r ! c = CorePat_Int i"
  shows "row_weight r' < row_weight r"
proof -
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  from assms(3) r_eq obtain i where i_eq: "ps ! c = CorePat_Int i" by auto
  from assms(1) r_eq i_eq have "r' = (drop_at c ps, body)"
    by (auto split: if_splits)
  moreover from assms(2) r_eq have c_lt: "c < length ps" by simp
  moreover from i_eq have "core_pattern_weight (ps ! c) > 0" by simp
  ultimately show ?thesis using r_eq row_weight_drop_at_lt by auto
qed

(* Variant specialisation: matching ctor with payload p replaces col c
   by p; weight goes from Suc(weight p) to weight p, strictly smaller.
   Wildcard at col c gets replaced by wildcard (weight stays 0). *)
lemma specialise_row_variant_weight_le:
  assumes "specialise_row_variant c h r = Some r'"
      and "c < length (fst r)"
  shows "row_weight r' \<le> row_weight r"
proof -
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  from assms(2) r_eq have c_lt: "c < length ps" by simp
  show ?thesis
  proof (cases "ps ! c")
    case (CorePat_Variant h' payload)
    show ?thesis
    proof (cases "h' = h")
      case True
      with CorePat_Variant assms(1) r_eq have r'_eq:
        "r' = (replace_at c payload ps, body)" by simp
      from CorePat_Variant have w_le:
        "core_pattern_weight payload \<le> core_pattern_weight (ps ! c)" by simp
      from c_lt w_le have
        "sum_list (map core_pattern_weight (replace_at c payload ps))
           \<le> sum_list (map core_pattern_weight ps)"
        by (rule sum_list_replace_at_le)
      with r'_eq r_eq show ?thesis by simp
    next
      case False
      with CorePat_Variant assms(1) r_eq show ?thesis by simp
    qed
  next
    case CorePat_Wildcard
    with assms(1) r_eq have r'_eq:
      "r' = (replace_at c CorePat_Wildcard ps, body)" by simp
    from CorePat_Wildcard have w_le:
      "core_pattern_weight CorePat_Wildcard \<le> core_pattern_weight (ps ! c)" by simp
    from c_lt w_le have
      "sum_list (map core_pattern_weight (replace_at c CorePat_Wildcard ps))
         \<le> sum_list (map core_pattern_weight ps)"
      by (rule sum_list_replace_at_le)
    with r'_eq r_eq show ?thesis by simp
  qed (use assms(1) r_eq in auto)
qed

lemma specialise_row_variant_weight_lt_on_variant:
  assumes "specialise_row_variant c h r = Some r'"
      and "c < length (fst r)"
      and "\<exists>p. fst r ! c = CorePat_Variant h p"
  shows "row_weight r' < row_weight r"
proof -
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  from assms(3) r_eq obtain p where v_eq: "ps ! c = CorePat_Variant h p" by auto
  from assms(1) r_eq v_eq have r'_eq: "r' = (replace_at c p ps, body)"
    by (auto split: if_splits)
  from assms(2) r_eq have c_lt: "c < length ps" by simp
  from v_eq have w_lt: "core_pattern_weight p < core_pattern_weight (ps ! c)" by simp
  from c_lt w_lt have "row_weight (replace_at c p ps, body) < row_weight (ps, body)"
    by (rule row_weight_replace_at_lt)
  with r'_eq r_eq show ?thesis by simp
qed

(* Record expansion: a record row gets its column-c CorePat_Record flds
   spliced into the row at position c. Weights drop by exactly 1
   (the Suc in CorePat_Record's weight). A wildcard row gets spliced
   with wildcards (weight stays the same). *)
lemma row_weight_expand_record_row_le:
  assumes "c < length (fst r)"
  shows "row_weight (expand_record_row c fld_names r) \<le> row_weight r"
proof -
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  show ?thesis
  proof (cases "ps ! c")
    case (CorePat_Record row_flds)
    let ?ys = "map snd row_flds"
    have sum_eq: "sum_list (map core_pattern_weight ?ys) < core_pattern_weight (ps ! c)"
      using CorePat_Record by (simp add: comp_def)
    from assms r_eq have c_lt: "c < length ps" by simp
    from c_lt sum_eq have
      "sum_list (map core_pattern_weight (splice_at c ?ys ps))
         < sum_list (map core_pattern_weight ps)"
      by (rule sum_list_splice_at_lt)
    with CorePat_Record r_eq show ?thesis by simp
  next
    case CorePat_Wildcard
    let ?ys = "replicate (length fld_names) CorePat_Wildcard"
    have ys_zero: "sum_list (map core_pattern_weight ?ys) = 0"
      by (induction fld_names) auto
    from assms r_eq have c_lt: "c < length ps" by simp
    from CorePat_Wildcard have c_weight: "core_pattern_weight (ps ! c) = 0" by simp
    from ys_zero c_weight have ys_le_c:
      "sum_list (map core_pattern_weight ?ys) \<le> core_pattern_weight (ps ! c)" by simp
    from c_lt ys_le_c have
      "sum_list (map core_pattern_weight (splice_at c ?ys ps))
         \<le> sum_list (map core_pattern_weight ps)"
      by (rule sum_list_splice_at_le)
    with CorePat_Wildcard r_eq show ?thesis by simp
  qed (use r_eq in auto)
qed

lemma row_weight_expand_record_row_lt_on_record:
  assumes "c < length (fst r)"
      and "\<exists>flds. fst r ! c = CorePat_Record flds"
  shows "row_weight (expand_record_row c fld_names r) < row_weight r"
proof -
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  from assms(2) r_eq obtain flds where rec_eq: "ps ! c = CorePat_Record flds" by auto
  let ?ys = "map snd flds"
  have sum_eq: "sum_list (map core_pattern_weight ?ys) < core_pattern_weight (ps ! c)"
    using rec_eq by (simp add: comp_def)
  from assms(1) r_eq have c_lt: "c < length ps" by simp
  from c_lt sum_eq have
    "sum_list (map core_pattern_weight (splice_at c ?ys ps))
       < sum_list (map core_pattern_weight ps)"
    by (rule sum_list_splice_at_lt)
  with rec_eq r_eq show ?thesis by simp
qed


subsection \<open>Matrix weight under each recursive call\<close>

(* List-level: sum_list over List.map_filter f is monotone in each
   per-row weight bound. *)
lemma sum_list_map_filter_le:
  fixes g :: "'a \<Rightarrow> nat"
  assumes "\<And>r r'. r \<in> set rows \<Longrightarrow> f r = Some r' \<Longrightarrow> g r' \<le> g r"
  shows "sum_list (map g (List.map_filter f rows)) \<le> sum_list (map g rows)"
  using assms
proof (induction rows)
  case Nil thus ?case by (simp add: List.map_filter_simps)
next
  case (Cons r rs)
  show ?case
  proof (cases "f r")
    case None
    with Cons.IH Cons.prems show ?thesis
      by (simp add: List.map_filter_simps)
  next
    case (Some r')
    from Cons.prems[of r r'] Some have g_le: "g r' \<le> g r" by simp
    from Cons.IH[OF Cons.prems] have
      "sum_list (map g (List.map_filter f rs)) \<le> sum_list (map g rs)" by simp
    with g_le Some show ?thesis
      by (simp add: List.map_filter_simps)
  qed
qed

(* Strict decrease at one specific row r0 \<in> rows. *)
lemma sum_list_map_filter_lt_one:
  fixes g :: "'a \<Rightarrow> nat"
  assumes le: "\<And>r r'. r \<in> set rows \<Longrightarrow> f r = Some r' \<Longrightarrow> g r' \<le> g r"
      and r0_in: "r0 \<in> set rows"
      and lt: "\<And>r'. f r0 = Some r' \<Longrightarrow> g r' < g r0"
      and present: "\<exists>r'. f r0 = Some r'"
  shows "sum_list (map g (List.map_filter f rows)) < sum_list (map g rows)"
  using assms
proof (induction rows)
  case Nil thus ?case by simp
next
  case (Cons r rs)
  show ?case
  proof (cases "r = r0")
    case True
    from Cons.prems(4) obtain r' where fr0: "f r0 = Some r'" by auto
    with True have fr: "f r = Some r'" by simp
    from Cons.prems(3)[OF fr0] have g_lt: "g r' < g r0" by simp
    have rs_le:
      "sum_list (map g (List.map_filter f rs)) \<le> sum_list (map g rs)"
      using Cons.prems(1) by (intro sum_list_map_filter_le) auto
    from True fr g_lt rs_le show ?thesis
      by (simp add: List.map_filter_simps)
  next
    case False
    with Cons.prems(2) have r0_in_rs: "r0 \<in> set rs" by simp
    have IH:
      "sum_list (map g (List.map_filter f rs)) < sum_list (map g rs)"
      using Cons.prems(1) r0_in_rs Cons.prems(3) Cons.prems(4)
      by (intro Cons.IH) auto
    show ?thesis
    proof (cases "f r")
      case None
      with IH show ?thesis by (simp add: List.map_filter_simps)
    next
      case (Some r')
      from Cons.prems(1)[OF _ Some] have "g r' \<le> g r" by simp
      with IH Some show ?thesis by (simp add: List.map_filter_simps)
    qed
  qed
qed

(* Default rows: matrix weight does not increase. *)
lemma matrix_weight_default_le:
  "sum_list (map row_weight (List.map_filter (default_row c) rows))
     \<le> sum_list (map row_weight rows)"
  by (intro sum_list_map_filter_le) (auto simp: default_row_weight_le)

(* The five recursive-call decrease lemmas. *)

lemma matrix_weight_default_lt:
  assumes "first_non_wildcard_col (map fst rows) = Some c"
  shows "matrix_weight (drop_at c scruts',
                        List.map_filter (default_row c) rows)
         < matrix_weight (scruts, rows)"
proof -
  from assms have rows_ne: "rows \<noteq> []"
    using first_non_wildcard_col_SomeD(1)[where rows = "map fst rows"] by simp
  from assms rows_ne have head_pos:
    "core_pattern_weight (fst (hd rows) ! c) > 0"
    by (rule first_non_wildcard_col_head_weight_pos)
  hence head_nw: "\<not> is_wildcard_like (fst (hd rows) ! c)"
    using is_wildcard_like_iff_weight_zero by auto
  from assms have len_all: "\<forall>r \<in> set rows. c < length (fst r)"
    by (rule first_non_wildcard_col_lengths)
  (* default_row on the head row returns None, so map_filter drops it
     entirely. Combined with non-increase on all other rows, the sum is
     strictly less than the original. *)
  obtain r0 rs where rows_eq: "rows = r0 # rs" using rows_ne by (cases rows) auto
  obtain ps0 body0 where r0_eq: "r0 = (ps0, body0)" by (cases r0) auto
  from rows_eq r0_eq head_nw have ps0_c_nw: "\<not> is_wildcard_like (ps0 ! c)" by simp
  hence "default_row c r0 = None"
    by (cases "ps0 ! c") (auto simp: r0_eq)
  hence head_filtered:
    "List.map_filter (default_row c) rows = List.map_filter (default_row c) rs"
    using rows_eq r0_eq by (simp add: List.map_filter_simps)
  have rs_le:
    "sum_list (map row_weight (List.map_filter (default_row c) rs))
       \<le> sum_list (map row_weight rs)"
    by (intro sum_list_map_filter_le) (auto simp: default_row_weight_le)
  from rows_eq r0_eq len_all have c_lt0: "c < length (fst r0)" by auto
  from rows_eq r0_eq head_pos have head_pos0: "core_pattern_weight (fst r0 ! c) > 0"
    by simp
  from c_lt0 head_pos0 have row0_pos: "row_weight r0 > 0"
    by (rule row_weight_pos_at_col)
  with rows_eq rs_le head_filtered show ?thesis
    by (simp add: matrix_weight_def)
qed

(* Bool/Int/Variant specialisation: head row has a head-kind matching
   pattern in column c, so on at least one head h the specialiser
   strictly decreases its weight. We prove a single "strict at hd"
   form per kind; the termination call site picks the right h.

   The strict decrease holds for every chosen head h: the head row's
   column-c pattern is non-wildcard (by first_non_wildcard_col), so its
   contribution to the matrix weight is either strictly reduced (when
   the row survives specialisation) or eliminated (when it is filtered
   out); other rows contribute non-increasing weight via the row-level
   `_weight_le` lemmas. *)

lemma matrix_weight_specialise_bool_lt:
  assumes "first_non_wildcard_col (map fst rows) = Some c"
  shows "matrix_weight (drop_at c scruts',
                        List.map_filter (specialise_row_bool c h) rows)
         < matrix_weight (scruts, rows)"
proof -
  from assms have rows_ne: "rows \<noteq> []"
    using first_non_wildcard_col_SomeD(1)[where rows = "map fst rows"] by simp
  from assms rows_ne have head_pos:
    "core_pattern_weight (fst (hd rows) ! c) > 0"
    by (rule first_non_wildcard_col_head_weight_pos)
  obtain r0 rs where rows_eq: "rows = r0 # rs" using rows_ne by (cases rows) auto
  obtain ps0 body0 where r0_eq: "r0 = (ps0, body0)" by (cases r0) auto
  from rows_eq r0_eq head_pos have ps0_c_pos: "core_pattern_weight (ps0 ! c) > 0" by simp
  have row0_weight_pos: "row_weight r0 > 0"
  proof -
    from assms have "\<forall>r \<in> set rows. c < length (fst r)"
      by (rule first_non_wildcard_col_lengths)
    with rows_eq r0_eq have c_lt: "c < length ps0" by auto
    from c_lt ps0_c_pos have
      "core_pattern_weight (ps0 ! c) \<le> sum_list (map core_pattern_weight ps0)"
      by (induction c ps0 rule: drop_at.induct) auto
    with ps0_c_pos r0_eq show ?thesis by simp
  qed
  (* On the head row: either specialise drops it (weight contribution 0,
     strictly less than row_weight r0) or keeps it as drop_at c ps0
     (strictly less by drop_at_lt). Either way map_filter sum is strictly
     smaller on the head row, and \<le> on the rest. *)
  have head_dropped_or_lt:
    "(case specialise_row_bool c h r0 of
        None \<Rightarrow> 0
      | Some r' \<Rightarrow> row_weight r') < row_weight r0"
  proof (cases "ps0 ! c")
    case (CorePat_Bool b)
    show ?thesis
    proof (cases "b = h")
      case True
      with CorePat_Bool r0_eq have spec_eq:
        "specialise_row_bool c h r0 = Some (drop_at c ps0, body0)" by simp
      from assms have "\<forall>r \<in> set rows. c < length (fst r)"
        by (rule first_non_wildcard_col_lengths)
      with rows_eq r0_eq have c_lt: "c < length ps0" by auto
      from c_lt ps0_c_pos have
        "row_weight (drop_at c ps0, body0) < row_weight (ps0, body0)"
        by (rule row_weight_drop_at_lt)
      with spec_eq r0_eq show ?thesis by simp
    next
      case False
      with CorePat_Bool r0_eq have "specialise_row_bool c h r0 = None" by simp
      with row0_weight_pos show ?thesis by simp
    qed
  next
    case CorePat_Wildcard
    with ps0_c_pos show ?thesis by simp
  qed (use row0_weight_pos r0_eq in \<open>auto split: option.splits\<close>)
  have rs_le:
    "sum_list (map row_weight (List.map_filter (specialise_row_bool c h) rs))
       \<le> sum_list (map row_weight rs)"
    by (intro sum_list_map_filter_le) (auto simp: specialise_row_bool_weight_le)
  show ?thesis
  proof (cases "specialise_row_bool c h r0")
    case None
    with rows_eq r0_eq head_dropped_or_lt rs_le show ?thesis
      by (simp add: matrix_weight_def List.map_filter_simps)
  next
    case (Some r')
    from Some head_dropped_or_lt have "row_weight r' < row_weight r0" by simp
    with rows_eq r0_eq Some rs_le show ?thesis
      by (simp add: matrix_weight_def List.map_filter_simps)
  qed
qed

lemma matrix_weight_specialise_int_lt:
  assumes "first_non_wildcard_col (map fst rows) = Some c"
  shows "matrix_weight (drop_at c scruts',
                        List.map_filter (specialise_row_int c h) rows)
         < matrix_weight (scruts, rows)"
proof -
  from assms have rows_ne: "rows \<noteq> []"
    using first_non_wildcard_col_SomeD(1)[where rows = "map fst rows"] by simp
  from assms rows_ne have head_pos:
    "core_pattern_weight (fst (hd rows) ! c) > 0"
    by (rule first_non_wildcard_col_head_weight_pos)
  obtain r0 rs where rows_eq: "rows = r0 # rs" using rows_ne by (cases rows) auto
  obtain ps0 body0 where r0_eq: "r0 = (ps0, body0)" by (cases r0) auto
  from rows_eq r0_eq head_pos have ps0_c_pos: "core_pattern_weight (ps0 ! c) > 0" by simp
  have row0_weight_pos: "row_weight r0 > 0"
  proof -
    from assms have "\<forall>r \<in> set rows. c < length (fst r)"
      by (rule first_non_wildcard_col_lengths)
    with rows_eq r0_eq have c_lt: "c < length ps0" by auto
    from c_lt ps0_c_pos have
      "core_pattern_weight (ps0 ! c) \<le> sum_list (map core_pattern_weight ps0)"
      by (induction c ps0 rule: drop_at.induct) auto
    with ps0_c_pos r0_eq show ?thesis by simp
  qed
  have head_dropped_or_lt:
    "(case specialise_row_int c h r0 of
        None \<Rightarrow> 0
      | Some r' \<Rightarrow> row_weight r') < row_weight r0"
  proof (cases "ps0 ! c")
    case (CorePat_Int i)
    show ?thesis
    proof (cases "i = h")
      case True
      with CorePat_Int r0_eq have spec_eq:
        "specialise_row_int c h r0 = Some (drop_at c ps0, body0)" by simp
      from assms have "\<forall>r \<in> set rows. c < length (fst r)"
        by (rule first_non_wildcard_col_lengths)
      with rows_eq r0_eq have c_lt: "c < length ps0" by auto
      from c_lt ps0_c_pos have
        "row_weight (drop_at c ps0, body0) < row_weight (ps0, body0)"
        by (rule row_weight_drop_at_lt)
      with spec_eq r0_eq show ?thesis by simp
    next
      case False
      with CorePat_Int r0_eq have "specialise_row_int c h r0 = None" by simp
      with row0_weight_pos show ?thesis by simp
    qed
  next
    case CorePat_Wildcard
    with ps0_c_pos show ?thesis by simp
  qed (use row0_weight_pos r0_eq in \<open>auto split: option.splits\<close>)
  have rs_le:
    "sum_list (map row_weight (List.map_filter (specialise_row_int c h) rs))
       \<le> sum_list (map row_weight rs)"
    by (intro sum_list_map_filter_le) (auto simp: specialise_row_int_weight_le)
  show ?thesis
  proof (cases "specialise_row_int c h r0")
    case None
    with rows_eq r0_eq head_dropped_or_lt rs_le show ?thesis
      by (simp add: matrix_weight_def List.map_filter_simps)
  next
    case (Some r')
    from Some head_dropped_or_lt have "row_weight r' < row_weight r0" by simp
    with rows_eq r0_eq Some rs_le show ?thesis
      by (simp add: matrix_weight_def List.map_filter_simps)
  qed
qed

lemma matrix_weight_specialise_variant_lt:
  assumes "first_non_wildcard_col (map fst rows) = Some c"
  shows "matrix_weight (replace_at c (CoreTm_VariantProj s_c h) scruts,
                        List.map_filter (specialise_row_variant c h) rows)
         < matrix_weight (scruts, rows)"
proof -
  from assms have rows_ne: "rows \<noteq> []"
    using first_non_wildcard_col_SomeD(1)[where rows = "map fst rows"] by simp
  from assms rows_ne have head_pos:
    "core_pattern_weight (fst (hd rows) ! c) > 0"
    by (rule first_non_wildcard_col_head_weight_pos)
  from assms have len_all: "\<forall>r \<in> set rows. c < length (fst r)"
    by (rule first_non_wildcard_col_lengths)
  obtain r0 rs where rows_eq: "rows = r0 # rs" using rows_ne by (cases rows) auto
  obtain ps0 body0 where r0_eq: "r0 = (ps0, body0)" by (cases r0) auto
  from rows_eq r0_eq head_pos have ps0_c_pos: "core_pattern_weight (ps0 ! c) > 0" by simp
  from rows_eq r0_eq len_all have c_lt0: "c < length ps0" by auto
  have row0_weight_pos: "row_weight r0 > 0"
  proof -
    from c_lt0 ps0_c_pos have
      "core_pattern_weight (ps0 ! c) \<le> sum_list (map core_pattern_weight ps0)"
      by (induction c ps0 rule: drop_at.induct) auto
    with ps0_c_pos r0_eq show ?thesis by simp
  qed
  have head_dropped_or_lt:
    "(case specialise_row_variant c h r0 of
        None \<Rightarrow> 0
      | Some r' \<Rightarrow> row_weight r') < row_weight r0"
  proof (cases "ps0 ! c")
    case (CorePat_Variant h' p)
    show ?thesis
    proof (cases "h' = h")
      case True
      with CorePat_Variant r0_eq have spec_eq:
        "specialise_row_variant c h r0 = Some (replace_at c p ps0, body0)" by simp
      from CorePat_Variant have w_lt:
        "core_pattern_weight p < core_pattern_weight (ps0 ! c)" by simp
      from c_lt0 w_lt have
        "row_weight (replace_at c p ps0, body0) < row_weight (ps0, body0)"
        by (rule row_weight_replace_at_lt)
      with spec_eq r0_eq show ?thesis by simp
    next
      case False
      with CorePat_Variant r0_eq have "specialise_row_variant c h r0 = None" by simp
      with row0_weight_pos show ?thesis by simp
    qed
  next
    case CorePat_Wildcard
    with ps0_c_pos show ?thesis by simp
  qed (use row0_weight_pos r0_eq in \<open>auto split: option.splits\<close>)
  have rs_le:
    "sum_list (map row_weight (List.map_filter (specialise_row_variant c h) rs))
       \<le> sum_list (map row_weight rs)"
  proof (intro sum_list_map_filter_le)
    fix r r'
    assume r_in: "r \<in> set rs" and r_some: "specialise_row_variant c h r = Some r'"
    from r_in rows_eq have "r \<in> set rows" by simp
    with len_all have c_lt: "c < length (fst r)" by auto
    from r_some c_lt show "row_weight r' \<le> row_weight r"
      by (rule specialise_row_variant_weight_le)
  qed
  show ?thesis
  proof (cases "specialise_row_variant c h r0")
    case None
    with rows_eq r0_eq head_dropped_or_lt rs_le show ?thesis
      by (simp add: matrix_weight_def List.map_filter_simps)
  next
    case (Some r')
    from Some head_dropped_or_lt have "row_weight r' < row_weight r0" by simp
    with rows_eq r0_eq Some rs_le show ?thesis
      by (simp add: matrix_weight_def List.map_filter_simps)
  qed
qed

lemma matrix_weight_expand_record_lt:
  assumes col_some: "first_non_wildcard_col (map fst rows) = Some c"
      and head_kind: "head_kind_of (hd (filter (\<lambda>p. \<not> is_wildcard_like p)
                                                (map (\<lambda>(ps, _). ps ! c) rows)))
                       = Some (HK_Record fld_names)"
  shows "matrix_weight (expand_record_scruts c s_c fld_names scruts,
                        map (expand_record_row c fld_names) rows)
         < matrix_weight (scruts, rows)"
proof -
  from col_some have rows_ne: "rows \<noteq> []"
    using first_non_wildcard_col_SomeD(1)[where rows = "map fst rows"] by simp
  from col_some have len_all: "\<forall>r \<in> set rows. c < length (fst r)"
    by (rule first_non_wildcard_col_lengths)
  let ?col_pats = "map (\<lambda>(ps, _). ps ! c) rows"
  let ?nw_col_pats = "filter (\<lambda>p. \<not> is_wildcard_like p) ?col_pats"
  from col_some rows_ne have head_pos:
    "core_pattern_weight (fst (hd rows) ! c) > 0"
    by (rule first_non_wildcard_col_head_weight_pos)
  from head_pos have head_nw: "\<not> is_wildcard_like (fst (hd rows) ! c)"
    using is_wildcard_like_iff_weight_zero by auto
  obtain r0 rs where rows_eq: "rows = r0 # rs" using rows_ne by (cases rows) auto
  obtain ps0 body0 where r0_eq: "r0 = (ps0, body0)" by (cases r0) auto
  from rows_eq r0_eq have hd_col: "hd ?col_pats = ps0 ! c"
    by (simp add: case_prod_unfold)
  from rows_eq r0_eq head_nw have nw_head: "\<not> is_wildcard_like (ps0 ! c)" by simp
  hence nw_col_eq: "?nw_col_pats = ps0 ! c # filter (\<lambda>p. \<not> is_wildcard_like p)
                                                    (map (\<lambda>(ps, _). ps ! c) rs)"
    using rows_eq r0_eq by (simp add: case_prod_unfold)
  with head_kind have hd_kind: "head_kind_of (ps0 ! c) = Some (HK_Record fld_names)"
    by simp
  then obtain flds where rec_eq: "ps0 ! c = CorePat_Record flds"
                              and names_eq: "fld_names = map fst flds"
    by (cases "ps0 ! c") auto
  (* Head row: weight strictly decreases by record expansion. *)
  from rows_eq r0_eq len_all have c_lt0: "c < length ps0" by auto
  have head_lt:
    "row_weight (expand_record_row c fld_names r0) < row_weight r0"
  proof -
    from r0_eq c_lt0 have c_lt_fst: "c < length (fst r0)" by simp
    from rec_eq r0_eq have ex_rec: "\<exists>flds. fst r0 ! c = CorePat_Record flds" by auto
    from c_lt_fst ex_rec show ?thesis
      by (rule row_weight_expand_record_row_lt_on_record)
  qed
  have rest_le:
    "sum_list (map row_weight (map (expand_record_row c fld_names) rs))
       \<le> sum_list (map row_weight rs)"
  proof -
    have "\<forall>r \<in> set rs. row_weight (expand_record_row c fld_names r) \<le> row_weight r"
    proof
      fix r assume r_in: "r \<in> set rs"
      with rows_eq have "r \<in> set rows" by simp
      with len_all have c_lt: "c < length (fst r)" by auto
      thus "row_weight (expand_record_row c fld_names r) \<le> row_weight r"
        by (rule row_weight_expand_record_row_le)
    qed
    thus ?thesis
      by (induction rs) auto
  qed
  from rows_eq head_lt rest_le show ?thesis
    by (simp add: matrix_weight_def)
qed


subsection \<open>Termination of compile_matrix\<close>

termination compile_matrix
  apply (relation "measure (\<lambda>(scruts, rows). matrix_weight (scruts, rows))")
        apply simp
       apply (simp_all add: matrix_weight_default_lt
                            matrix_weight_specialise_bool_lt
                            matrix_weight_specialise_int_lt
                            matrix_weight_specialise_variant_lt
                            matrix_weight_expand_record_lt)
  done


section \<open>Entry point\<close>

(* Top-level pass: compile a single match. The caller supplies the
   scrutinee term, its type (carried for use by the type-preservation
   theorem, not by the algorithm itself), and the user-level
   (pattern, body) arms.

   The result is a MatchTree; the caller plugs in its own
   MatchTree-to-CoreTerm or MatchTree-to-CoreStatement-list
   translator. *)
definition compile_match ::
  "CoreTerm \<Rightarrow> CoreType \<Rightarrow> (CorePattern \<times> 'body) list \<Rightarrow> 'body MatchTree"
where
  "compile_match scrut scrutTy arms =
    compile_matrix ([scrut], map (\<lambda>(p, b). ([p], b)) arms)"

end
