theory MatchCompile
  imports "../bab/BabSyntax" "../core/CoreSyntax" "../core/CoreTypecheck"
begin

(* Pattern-match compiler: converts Babylon's nested patterns to Core's flat patterns.

   Algorithm: Maranget-style matrix compilation, "first non-wildcard column"
   heuristic. Produces a MatchTree IR parametric over the arm body type;
   two translations then target CoreTerm (for BabTm_Match) or
   CoreStatement list (for BabStmt_Match). *)


section \<open>MatchTree IR\<close>

(* Parametric over the arm body type:
   'body = CoreTerm (term match) or CoreStatement list (stmt match).

   MT_Test's arm list may be non-exhaustive (a match failure produces a
   Core RuntimeError).

   MT_Bind is only emitted for user-level pattern variables (BabPat_Var),
   never for compiler sharing. VarOrRef matters only for the stmt
   translation; term translation ignores it and uses CoreTm_Let. *)
datatype 'body MatchTree =
    MT_Leaf 'body
  | MT_Test CoreTerm "(CorePattern \<times> 'body MatchTree) list"
  | MT_Bind VarOrRef string CoreType CoreTerm "'body MatchTree"


section \<open>Decorated pattern type\<close>

(* DecPattern is what the elaborator produces after typechecking each
   source pattern against the scrutinee's type. Compared to BabPattern:
   no Locations, no DP_Tuple (tuples desugar to "0"/"1"/... records),
   and DP_Var carries its elaborated CoreType inline.

   The compiler assumes well-formedness and does not re-check.

   DP_Record invariant (maintained by elaborator): every DP_Record lists
   every field of the record type, in declaration order. Source patterns
   that omit or reorder fields are normalised. This lets the compiler
   read the full field list off any DP_Record representative via
   `map fst flds`, and expansion is a parallel walk. *)
datatype DecPattern =
    DP_Var VarOrRef string CoreType
  | DP_Bool bool
  | DP_Int int
  | DP_Record "(string \<times> DecPattern) list"
  | DP_Variant string "DecPattern option"
  | DP_Wildcard


subsection \<open>Helpers\<close>

(* A pattern is "wildcard-like" if it always matches: DP_Var and DP_Wildcard. *)
fun is_wildcard_like :: "DecPattern \<Rightarrow> bool" where
  "is_wildcard_like (DP_Var _ _ _) = True"
| "is_wildcard_like DP_Wildcard = True"
| "is_wildcard_like _ = False"

(* Smallest column index c such that row 0 is non-wildcard at c.
   Returns None if row 0 is all wildcard-like, matrix is empty, or
   row lengths differ. *)
definition first_non_wildcard_col :: "DecPattern list list \<Rightarrow> nat option" where
  "first_non_wildcard_col rows =
    (case rows of
       [] \<Rightarrow> None
     | r0 # _ \<Rightarrow>
         if list_all (\<lambda>r. length r = length r0) rows
         then find (\<lambda>c. \<not> is_wildcard_like (r0 ! c))
                   [0 ..< length r0]
         else None)"

(* Classify a column's head: record (decompose), variant/bool/int
   (specialise via MT_Test), or None (wildcard-like, no head). *)
datatype HeadKind =
    HK_Record "string list"   (* field names, in declaration order *)
  | HK_Variant
  | HK_Bool
  | HK_Int

fun head_kind_of :: "DecPattern \<Rightarrow> HeadKind option" where
  "head_kind_of (DP_Var _ _ _) = None"
| "head_kind_of DP_Wildcard = None"
| "head_kind_of (DP_Bool _) = Some HK_Bool"
| "head_kind_of (DP_Int _) = Some HK_Int"
| "head_kind_of (DP_Variant _ _) = Some HK_Variant"
| "head_kind_of (DP_Record flds) = Some (HK_Record (map fst flds))"


subsection \<open>Matrix representation\<close>

(* Per-row list of user pattern variables encountered so far during
   column elimination. *)
type_synonym BindList = "(VarOrRef \<times> string \<times> CoreType \<times> CoreTerm) list"

(* A row is a pattern list (the columns), a list of bindings applicable to this row,
   and a body. *)
type_synonym 'body Row = "DecPattern list \<times> BindList \<times> 'body"

(* Matrix invariant: every row's pattern list has length = length scruts. *)
type_synonym 'body MatchMatrix = "CoreTerm list \<times> 'body Row list"


subsection \<open>Bind-emission helpers\<close>

(* Wrap a MatchTree in a chain of MT_Binds, first entry outermost. *)
fun binds_to_tree :: "BindList \<Rightarrow> 'body MatchTree \<Rightarrow> 'body MatchTree" where
  "binds_to_tree [] tree = tree"
| "binds_to_tree ((vr, x, ty, rhs) # rest) tree =
    MT_Bind vr x ty rhs (binds_to_tree rest tree)"

(* Walk parallel scrutinee/pattern lists and extract one bind per DP_Var;
   called at the leaf on a row whose columns are all wildcard-like. *)
fun extract_binds :: "CoreTerm list \<Rightarrow> DecPattern list \<Rightarrow> BindList" where
  "extract_binds [] [] = []"
| "extract_binds (s # ss) ((DP_Var vr x ty) # ps) =
    (vr, x, ty, s) # extract_binds ss ps"
| "extract_binds (_ # ss) (DP_Wildcard # ps) = extract_binds ss ps"
| "extract_binds _ _ = []"   \<comment> \<open>unreachable for well-formed matrix (all cols wildcard-like)\<close>


subsection \<open>Column / scrutinee plumbing\<close>

fun replace_at :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "replace_at _ _ [] = []"
| "replace_at 0 y (_ # xs) = y # xs"
| "replace_at (Suc c) y (x # xs) = x # replace_at c y xs"

fun drop_at :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "drop_at _ [] = []"
| "drop_at 0 (_ # xs) = xs"
| "drop_at (Suc c) (x # xs) = x # drop_at c xs"


subsection \<open>Row specialisation\<close>

(* Specialise a row for head-kind Bool, head h: matching bool survives
   with col c dropped; non-matching bool drops the row; wildcard-like
   survives with col c dropped (DP_Var also adds a bind). *)
fun specialise_row_bool ::
  "nat \<Rightarrow> CoreTerm \<Rightarrow> bool \<Rightarrow> 'body Row \<Rightarrow> 'body Row option"
where
  "specialise_row_bool c s h (ps, bs, body) =
    (case ps ! c of
       DP_Bool b \<Rightarrow>
         if b = h then Some (drop_at c ps, bs, body) else None
     | DP_Wildcard \<Rightarrow> Some (drop_at c ps, bs, body)
     | DP_Var vr x ty \<Rightarrow>
         Some (drop_at c ps, bs @ [(vr, x, ty, s)], body)
     | _ \<Rightarrow> None)"   \<comment> \<open>unreachable: well-formed col must have bool/wildcard-like heads\<close>

(* Int case: same shape as bool. *)
fun specialise_row_int ::
  "nat \<Rightarrow> CoreTerm \<Rightarrow> int \<Rightarrow> 'body Row \<Rightarrow> 'body Row option"
where
  "specialise_row_int c s h (ps, bs, body) =
    (case ps ! c of
       DP_Int i \<Rightarrow>
         if i = h then Some (drop_at c ps, bs, body) else None
     | DP_Wildcard \<Rightarrow> Some (drop_at c ps, bs, body)
     | DP_Var vr x ty \<Rightarrow>
         Some (drop_at c ps, bs @ [(vr, x, ty, s)], body)
     | _ \<Rightarrow> None)"

(* Specialise a row for variant ctor h. Matching ctor with payload:
   col c becomes the payload pattern (scrutinee is projected in caller).
   Matching ctor without payload or non-matching ctor: col c dropped.
   Wildcard-like: survives; col c becomes DP_Wildcard if payload, else
   dropped. DP_Var also adds a bind (to the pre-projection scrutinee). *)
fun specialise_row_variant ::
  "nat \<Rightarrow> CoreTerm \<Rightarrow> string \<Rightarrow> bool \<Rightarrow> 'body Row \<Rightarrow> 'body Row option"
where
  "specialise_row_variant c s h has_payload (ps, bs, body) =
    (case ps ! c of
       DP_Variant h' mpat \<Rightarrow>
         if h' \<noteq> h then None
         else (case mpat of
                 Some pat \<Rightarrow> Some (replace_at c pat ps, bs, body)
               | None \<Rightarrow> Some (drop_at c ps, bs, body))
     | DP_Wildcard \<Rightarrow>
         if has_payload
         then Some (replace_at c DP_Wildcard ps, bs, body)
         else Some (drop_at c ps, bs, body)
     | DP_Var vr x ty \<Rightarrow>
         let bs' = bs @ [(vr, x, ty, s)]
         in if has_payload
            then Some (replace_at c DP_Wildcard ps, bs', body)
            else Some (drop_at c ps, bs', body)
     | _ \<Rightarrow> None)"

(* Default arm: row survives only if col c is wildcard-like. *)
fun default_row :: "nat \<Rightarrow> CoreTerm \<Rightarrow> 'body Row \<Rightarrow> 'body Row option" where
  "default_row c s (ps, bs, body) =
    (case ps ! c of
       DP_Wildcard \<Rightarrow> Some (drop_at c ps, bs, body)
     | DP_Var vr x ty \<Rightarrow>
         Some (drop_at c ps, bs @ [(vr, x, ty, s)], body)
     | _ \<Rightarrow> None)"


subsection \<open>Record decomposition\<close>

(* Replace element at position c with a list, splicing in place. *)
fun splice_at :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "splice_at _ _ [] = []"
| "splice_at 0 ys (_ # xs) = ys @ xs"
| "splice_at (Suc c) ys (x # xs) = x # splice_at c ys xs"

(* Expand a row's record column c into sub-columns (one per field).
   DP_Record: sub-patterns in declaration order (per DP_Record invariant).
   DP_Wildcard / DP_Var: fill with wildcards; DP_Var also adds a bind
   to the whole record scrutinee. *)
fun expand_record_row ::
  "nat \<Rightarrow> CoreTerm \<Rightarrow> string list \<Rightarrow> 'body Row \<Rightarrow> 'body Row"
where
  "expand_record_row c s fld_names (ps, bs, body) =
    (case ps ! c of
       DP_Record row_flds \<Rightarrow>
         (splice_at c (map snd row_flds) ps, bs, body)
     | DP_Wildcard \<Rightarrow>
         (splice_at c (replicate (length fld_names) DP_Wildcard) ps, bs, body)
     | DP_Var vr x ty \<Rightarrow>
         (splice_at c (replicate (length fld_names) DP_Wildcard) ps,
          bs @ [(vr, x, ty, s)],
          body)
     | _ \<Rightarrow> (ps, bs, body))"   \<comment> \<open>unreachable: col must be record-headed or wildcard-like\<close>

(* Scrutinee at col c replaced by one CoreTm_RecordProj per field. *)
definition expand_record_scruts ::
  "nat \<Rightarrow> CoreTerm \<Rightarrow> string list \<Rightarrow> CoreTerm list \<Rightarrow> CoreTerm list"
where
  "expand_record_scruts c s fld_names scruts =
    splice_at c (map (\<lambda>f. CoreTm_RecordProj s f) fld_names) scruts"


subsection \<open>Head enumeration\<close>

(* Distinct heads of a testable column, first-appearance order. One
   function per head kind; wildcard-like patterns contribute no head.
   Filtering subsequent occurrences of the just-seen head is O(n^2),
   but match arm lists are short in practice. *)

fun distinct_bool_heads :: "DecPattern list \<Rightarrow> bool list" where
  "distinct_bool_heads [] = []"
| "distinct_bool_heads (DP_Bool b # rest) =
    b # distinct_bool_heads (filter (\<lambda>p. p \<noteq> DP_Bool b) rest)"
| "distinct_bool_heads (_ # rest) = distinct_bool_heads rest"

fun distinct_int_heads :: "DecPattern list \<Rightarrow> int list" where
  "distinct_int_heads [] = []"
| "distinct_int_heads (DP_Int i # rest) =
    i # distinct_int_heads (filter (\<lambda>p. p \<noteq> DP_Int i) rest)"
| "distinct_int_heads (_ # rest) = distinct_int_heads rest"

(* Variant heads come with a payload-presence flag (well-formedness
   ensures all patterns for the same ctor agree on the flag). *)
fun distinct_variant_heads ::
  "DecPattern list \<Rightarrow> (string \<times> bool) list"
where
  "distinct_variant_heads [] = []"
| "distinct_variant_heads (DP_Variant h mpat # rest) =
    (h, mpat \<noteq> None)
      # distinct_variant_heads
          (filter (\<lambda>p. case p of DP_Variant h' _ \<Rightarrow> h' \<noteq> h | _ \<Rightarrow> True) rest)"
| "distinct_variant_heads (_ # rest) = distinct_variant_heads rest"


subsection \<open>The algorithm\<close>

(* Maranget-style matrix compilation. Precondition: matrix has at least
   one row; every row has length = length scruts.

   Base case (row 0's columns all wildcard-like): emit row 0's body
   with its accumulated binds plus DP_Var binds from its columns.
   Any later rows are dead, because row 0 always matches in this case.

   Testable column: emit MT_Test with one arm per distinct head, plus
   an optional trailing wildcard arm if any wildcard/var rows exist.

   Record column: lossless decomposition, no MT_Test emitted here. *)
function compile_matrix :: "'body MatchMatrix \<Rightarrow> 'body MatchTree" where
  "compile_matrix (scruts, rows) =
    (case first_non_wildcard_col (map (\<lambda>(ps, _, _). ps) rows) of
       None \<Rightarrow>
         (case rows of
            [] \<Rightarrow> undefined   \<comment> \<open>precondition violated: zero-row matrix\<close>
          | (ps, bs, body) # _ \<Rightarrow>
              binds_to_tree (bs @ extract_binds scruts ps) (MT_Leaf body))
     | Some c \<Rightarrow>
         (let s_c = scruts ! c;
              col_pats = map (\<lambda>(ps, _, _). ps ! c) rows;
              has_default = list_ex is_wildcard_like col_pats;
              default_rows = List.map_filter (default_row c s_c) rows;
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
                            List.map_filter (specialise_row_bool c s_c h) rows)))
                   in MT_Test s_c (map head_arm heads @ default_arm))
              | Some HK_Int \<Rightarrow>
                  (let heads = distinct_int_heads col_pats;
                       head_arm = (\<lambda>h.
                         (CorePat_Int h,
                          compile_matrix (drop_at c scruts,
                            List.map_filter (specialise_row_int c s_c h) rows)))
                   in MT_Test s_c (map head_arm heads @ default_arm))
              | Some HK_Variant \<Rightarrow>
                  (let heads = distinct_variant_heads col_pats;
                       head_arm = (\<lambda>(h, has_payload).
                         let new_scruts =
                               (if has_payload
                                then replace_at c (CoreTm_VariantProj s_c h) scruts
                                else drop_at c scruts)
                         in (CorePat_Variant h CorePat_Wildcard,
                             compile_matrix (new_scruts,
                               List.map_filter
                                 (specialise_row_variant c s_c h has_payload) rows)))
                   in MT_Test s_c (map head_arm heads @ default_arm))
              | Some (HK_Record fld_names) \<Rightarrow>
                  compile_matrix (expand_record_scruts c s_c fld_names scruts,
                                  map (expand_record_row c s_c fld_names) rows)
              | None \<Rightarrow> undefined)))"   \<comment> \<open>None: unreachable (c was non-wildcard)\<close>
  by pat_completeness auto


subsection \<open>Termination\<close>

(* This (long) subsection proves that compile_match terminates. *)

(* Weight of a DecPattern: DP_Wildcard and DP_Var contribute 0. This
   matters for the record case: expanding a DP_Wildcard at column c
   into length-fld_names sub-wildcards must not increase the weight. *)
fun dec_pattern_weight :: "DecPattern \<Rightarrow> nat" where
  "dec_pattern_weight (DP_Var _ _ _) = 0"
| "dec_pattern_weight DP_Wildcard = 0"
| "dec_pattern_weight (DP_Bool _) = 1"
| "dec_pattern_weight (DP_Int _) = 1"
| "dec_pattern_weight (DP_Variant _ None) = 1"
| "dec_pattern_weight (DP_Variant _ (Some p)) = 1 + dec_pattern_weight p"
| "dec_pattern_weight (DP_Record flds) =
    1 + sum_list (map (dec_pattern_weight \<circ> snd) flds)"

definition row_weight :: "'body Row \<Rightarrow> nat" where
  "row_weight r = sum_list (map dec_pattern_weight (fst r))"

definition matrix_weight :: "'body Row list \<Rightarrow> nat" where
  "matrix_weight rows = sum_list (map row_weight rows)"

(* Basic arithmetic on weights under the plumbing operations. *)

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

(* Row weight under each row transformation. *)

lemma row_weight_drop_at:
  "row_weight (drop_at c ps, bs', body) \<le> row_weight (ps, bs, body)"
  unfolding row_weight_def by (simp add: sum_list_drop_at_le)

lemma row_weight_drop_at_lt:
  "c < length ps \<Longrightarrow> dec_pattern_weight (ps ! c) > 0 \<Longrightarrow>
    row_weight (drop_at c ps, bs', body) < row_weight (ps, bs, body)"
  unfolding row_weight_def by (simp add: sum_list_drop_at_lt)

lemma row_weight_replace_at_wildcard:
  "c < length ps \<Longrightarrow>
    row_weight (replace_at c DP_Wildcard ps, bs', body) \<le> row_weight (ps, bs, body)"
  unfolding row_weight_def
  using sum_list_replace_at_le[where f = dec_pattern_weight and y = DP_Wildcard and c = c and xs = ps]
  by simp

lemma row_weight_replace_at_variant_payload:
  "c < length ps \<Longrightarrow> ps ! c = DP_Variant h (Some p) \<Longrightarrow>
    row_weight (replace_at c p ps, bs', body) < row_weight (ps, bs, body)"
  unfolding row_weight_def
  using sum_list_replace_at_lt[where f = dec_pattern_weight and y = p and c = c and xs = ps]
  by simp

(* Length guarantees from first_non_wildcard_col. *)

lemma first_non_wildcard_col_SomeD:
  assumes "first_non_wildcard_col rows = Some c"
  shows "rows \<noteq> []"
    and "\<forall>r \<in> set rows. c < length r"
    and "\<exists>r \<in> set rows. \<not> is_wildcard_like (r ! c)"
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
  from find_some have "c \<in> set [0 ..< length r0]"
    by (metis find_Some_iff2 nth_mem)
  hence c_lt: "c < length r0" by auto
  show "\<forall>r \<in> set rows. c < length r"
  proof
    fix r assume "r \<in> set rows"
    with len_ok have "length r = length r0"
      by (simp add: list_all_iff)
    with c_lt show "c < length r" by simp
  qed
next
  from assms obtain r0 rs where
    rows_eq: "rows = r0 # rs" and
    find_some: "find (\<lambda>c. \<not> is_wildcard_like (r0 ! c))
                     [0 ..< length r0] = Some c"
    unfolding first_non_wildcard_col_def
    by (auto split: list.splits if_splits)
  from find_some have "\<not> is_wildcard_like (r0 ! c)"
    by (metis find_Some_iff)
  with rows_eq show "\<exists>r \<in> set rows. \<not> is_wildcard_like (r ! c)"
    by auto
qed

(* Matrix weight under each operation. *)

lemma matrix_weight_default_rows_le:
  "matrix_weight (List.map_filter (default_row c s) rows) \<le> matrix_weight rows"
proof (induction rows)
  case Nil
  show ?case by (simp add: matrix_weight_def List.map_filter_simps)
next
  case (Cons r rs)
  obtain ps bs body where r_eq: "r = (ps, bs, body)" by (cases r) auto
  show ?case
  proof (cases "default_row c s r")
    case None
    with r_eq Cons.IH show ?thesis
      by (simp add: matrix_weight_def List.map_filter_simps)
  next
    case (Some r')
    with r_eq obtain ps' bs' where
      dr: "default_row c s (ps, bs, body) = Some (ps', bs', body)"
      by (cases r') (auto split: DecPattern.splits)
    then have r'_eq: "r' = (ps', bs', body)" using Some r_eq by simp
    from dr have ps'_eq: "ps' = drop_at c ps"
      by (auto split: DecPattern.splits)
    have "row_weight r' \<le> row_weight r"
      using r_eq r'_eq ps'_eq by (simp add: row_weight_drop_at)
    with Cons.IH Some r_eq show ?thesis
      by (simp add: matrix_weight_def List.map_filter_simps)
  qed
qed

lemma default_row_drops_non_wildcard:
  "\<not> is_wildcard_like (fst r ! c) \<Longrightarrow> default_row c s r = None"
  by (cases r) (auto split: DecPattern.splits)

lemma default_row_weight_le:
  "case default_row c s r of None \<Rightarrow> True | Some r' \<Rightarrow> row_weight r' \<le> row_weight r"
  apply (cases r)
  apply (auto split: DecPattern.splits)
   apply (metis row_weight_drop_at)+
  done

lemma default_row_weight_le_cond:
  "c < length (fst r) \<Longrightarrow>
    case default_row c s r of None \<Rightarrow> True | Some r' \<Rightarrow> row_weight r' \<le> row_weight r"
  by (rule default_row_weight_le)

lemma row_weight_pos_of_non_wildcard:
  "\<not> is_wildcard_like p \<Longrightarrow> dec_pattern_weight p > 0"
proof (cases p)
  case (DP_Variant h mpat)
  thus ?thesis by (cases mpat) auto
qed auto

lemma sum_list_drop_at_is_pos:
  fixes f :: "'a \<Rightarrow> nat"
  shows "c < length xs \<Longrightarrow> f (xs ! c) > 0 \<Longrightarrow> sum_list (map f xs) > 0"
  by (induction c xs rule: drop_at.induct) auto

lemma row_weight_pos_if_col_non_wildcard:
  "c < length (fst r) \<Longrightarrow> \<not> is_wildcard_like (fst r ! c) \<Longrightarrow> row_weight r > 0"
  unfolding row_weight_def
  using row_weight_pos_of_non_wildcard sum_list_drop_at_is_pos
  by (metis (no_types, lifting))

lemma default_row_drops_non_wildcard_weight:
  assumes c_lt: "c < length (fst r)"
  assumes non_wc: "\<not> is_wildcard_like (fst r ! c)"
  shows "(case default_row c s r of None \<Rightarrow> 0 | Some r' \<Rightarrow> row_weight r') < row_weight r"
proof -
  from non_wc have dropped: "default_row c s r = None"
    by (simp add: default_row_drops_non_wildcard)
  from c_lt non_wc have "row_weight r > 0"
    by (rule row_weight_pos_if_col_non_wildcard)
  with dropped show ?thesis by simp
qed

(* Generic: given a row-specialiser that never increases weight and
   strictly decreases it on non-wildcard columns, map_filter strictly
   decreases matrix weight (assuming some row has a non-wildcard at c). *)

lemma matrix_weight_map_filter_lt_generic:
  fixes f :: "'body Row \<Rightarrow> 'body Row option"
  assumes le: "\<And>r. c < length (fst r) \<Longrightarrow>
                 case f r of None \<Rightarrow> True | Some r' \<Rightarrow> row_weight r' \<le> row_weight r"
  assumes lt: "\<And>r. c < length (fst r) \<Longrightarrow> \<not> is_wildcard_like (fst r ! c) \<Longrightarrow>
                 (case f r of None \<Rightarrow> 0 | Some r' \<Rightarrow> row_weight r') < row_weight r"
  assumes all_valid: "\<forall>r \<in> set rows. c < length (fst r)"
  assumes ex_non_wc: "\<exists>r \<in> set rows. \<not> is_wildcard_like (fst r ! c)"
  shows "matrix_weight (List.map_filter f rows) < matrix_weight rows"
  using all_valid ex_non_wc
proof (induction rows)
  case Nil
  thus ?case by simp
next
  case (Cons r rs)
  \<comment> \<open>Tail-le helper: for any rs' whose rows are all valid at c.\<close>
  have tail_le_all: "\<And>xs. \<forall>x \<in> set xs. c < length (fst x) \<Longrightarrow>
                     matrix_weight (List.map_filter f xs) \<le> matrix_weight xs"
  proof -
    fix xs :: "'body Row list"
    show "\<forall>x \<in> set xs. c < length (fst x) \<Longrightarrow>
          matrix_weight (List.map_filter f xs) \<le> matrix_weight xs"
    proof (induction xs)
      case Nil
      thus ?case by (simp add: matrix_weight_def List.map_filter_simps)
    next
      case (Cons x xs)
      from Cons.prems have x_valid: "c < length (fst x)" by simp
      have h: "case f x of None \<Rightarrow> True | Some r' \<Rightarrow> row_weight r' \<le> row_weight x"
        by (rule le[OF x_valid])
      from Cons.prems have xs_valid: "\<forall>x \<in> set xs. c < length (fst x)" by simp
      show ?case
        using Cons.IH[OF xs_valid] h
        by (cases "f x") (auto simp: matrix_weight_def List.map_filter_simps)
    qed
  qed
  show ?case
  proof (cases "\<not> is_wildcard_like (fst r ! c)")
    case True
    from Cons.prems(1) have c_lt: "c < length (fst r)" by simp
    from c_lt True have head_lt:
      "(case f r of None \<Rightarrow> 0 | Some r' \<Rightarrow> row_weight r') < row_weight r"
      by (rule lt)
    from Cons.prems(1) have rs_valid: "\<forall>x \<in> set rs. c < length (fst x)" by simp
    have tail_le: "matrix_weight (List.map_filter f rs) \<le> matrix_weight rs"
      by (rule tail_le_all[OF rs_valid])
    show ?thesis
    proof (cases "f r")
      case None
      with head_lt tail_le show ?thesis
        by (simp add: matrix_weight_def List.map_filter_simps)
    next
      case (Some r')
      with head_lt have r'_lt: "row_weight r' < row_weight r" by simp
      from Some r'_lt tail_le show ?thesis
        by (simp add: matrix_weight_def List.map_filter_simps)
    qed
  next
    case False
    hence head_wc: "is_wildcard_like (fst r ! c)" by simp
    from Cons.prems(2) head_wc have ex_rs: "\<exists>r \<in> set rs. \<not> is_wildcard_like (fst r ! c)"
      by auto
    from Cons.prems(1) have valid_rs: "\<forall>r \<in> set rs. c < length (fst r)"
      by simp
    have tail_lt: "matrix_weight (List.map_filter f rs) < matrix_weight rs"
      using Cons.IH valid_rs ex_rs by blast
    from Cons.prems(1) have c_lt_r: "c < length (fst r)" by simp
    have head_le: "case f r of None \<Rightarrow> True | Some r' \<Rightarrow> row_weight r' \<le> row_weight r"
      by (rule le[OF c_lt_r])
    show ?thesis
    proof (cases "f r")
      case None
      with tail_lt show ?thesis
        by (simp add: matrix_weight_def List.map_filter_simps)
    next
      case (Some r')
      with head_le have r'_le: "row_weight r' \<le> row_weight r" by simp
      from Some tail_lt r'_le show ?thesis
        by (simp add: matrix_weight_def List.map_filter_simps)
    qed
  qed
qed


(* -------- default_row decrease (via generic) -------- *)

lemma matrix_weight_default_rows_lt:
  assumes "first_non_wildcard_col (map (\<lambda>(ps,_,_). ps) rows) = Some c"
  shows "matrix_weight (List.map_filter (default_row c s) rows) < matrix_weight rows"
proof -
  from assms have "\<forall>r \<in> set (map (\<lambda>(ps,_,_). ps) rows). c < length r"
    by (rule first_non_wildcard_col_SomeD(2))
  hence valid: "\<forall>r \<in> set rows. c < length (fst r)"
    by (auto simp: case_prod_unfold)
  from assms have "\<exists>r \<in> set (map (\<lambda>(ps,_,_). ps) rows). \<not> is_wildcard_like (r ! c)"
    by (rule first_non_wildcard_col_SomeD(3))
  hence ex_nw: "\<exists>r \<in> set rows. \<not> is_wildcard_like (fst r ! c)"
    by (auto simp: case_prod_unfold)
  show ?thesis
    by (rule matrix_weight_map_filter_lt_generic[OF
          default_row_weight_le_cond default_row_drops_non_wildcard_weight valid ex_nw])
qed


(* -------- specialise_row_bool decrease -------- *)

lemma specialise_row_bool_weight_le:
  "case specialise_row_bool c s h r of None \<Rightarrow> True
                                      | Some r' \<Rightarrow> row_weight r' \<le> row_weight r"
  apply (cases r)
  apply (auto split: DecPattern.splits if_splits)
     apply (metis row_weight_drop_at)+
  done

lemma specialise_row_bool_weight_le_cond:
  "c < length (fst r) \<Longrightarrow>
    case specialise_row_bool c s h r of None \<Rightarrow> True
                                      | Some r' \<Rightarrow> row_weight r' \<le> row_weight r"
  by (rule specialise_row_bool_weight_le)

lemma specialise_row_bool_drops_non_wildcard_no_match_weight:
  assumes c_lt: "c < length (fst r)"
  assumes non_wc: "\<not> is_wildcard_like (fst r ! c)"
  shows "(case specialise_row_bool c s h r of None \<Rightarrow> 0 | Some r' \<Rightarrow> row_weight r') < row_weight r"
proof -
  obtain ps bs body where r_eq: "r = (ps, bs, body)" by (cases r) auto
  from c_lt r_eq have c_lt_ps: "c < length ps" by simp
  from non_wc r_eq have non_wc_ps: "\<not> is_wildcard_like (ps ! c)" by simp
  from non_wc_ps have pos: "dec_pattern_weight (ps ! c) > 0"
    by (rule row_weight_pos_of_non_wildcard)
  show ?thesis
  proof (cases "ps ! c")
    case (DP_Bool b)
    show ?thesis
    proof (cases "b = h")
      case True
      with DP_Bool r_eq have spec_eq:
        "specialise_row_bool c s h r = Some (drop_at c ps, bs, body)" by simp
      from c_lt_ps pos have
        "row_weight (drop_at c ps, bs, body) < row_weight (ps, bs, body)"
        by (rule row_weight_drop_at_lt)
      with spec_eq r_eq show ?thesis by simp
    next
      case False
      with DP_Bool r_eq have spec_eq: "specialise_row_bool c s h r = None" by simp
      from r_eq c_lt_ps pos have "row_weight r > 0"
        unfolding row_weight_def by (simp add: sum_list_drop_at_is_pos)
      with spec_eq show ?thesis by simp
    qed
  next
    \<comment> \<open>All other non-wildcard-like cases: specialise_row_bool returns None,
        and row_weight r > 0.\<close>
    case (DP_Int i)
    with r_eq have spec_eq: "specialise_row_bool c s h r = None" by simp
    from r_eq c_lt_ps pos have "row_weight r > 0"
      unfolding row_weight_def by (simp add: sum_list_drop_at_is_pos)
    with spec_eq show ?thesis by simp
  next
    case (DP_Variant h' mpat)
    with r_eq have spec_eq: "specialise_row_bool c s h r = None" by simp
    from r_eq c_lt_ps pos have "row_weight r > 0"
      unfolding row_weight_def by (simp add: sum_list_drop_at_is_pos)
    with spec_eq show ?thesis by simp
  next
    case (DP_Record flds)
    with r_eq have spec_eq: "specialise_row_bool c s h r = None" by simp
    from r_eq c_lt_ps pos have "row_weight r > 0"
      unfolding row_weight_def by (simp add: sum_list_drop_at_is_pos)
    with spec_eq show ?thesis by simp
  next
    case (DP_Var vr x ty)
    with non_wc_ps have False by simp
    thus ?thesis ..
  next
    case DP_Wildcard
    with non_wc_ps have False by simp
    thus ?thesis ..
  qed
qed

lemma matrix_weight_specialise_bool_lt:
  assumes "first_non_wildcard_col (map (\<lambda>(ps,_,_). ps) rows) = Some c"
  shows "matrix_weight (List.map_filter (specialise_row_bool c s h) rows) < matrix_weight rows"
proof -
  from assms have "\<forall>r \<in> set (map (\<lambda>(ps,_,_). ps) rows). c < length r"
    by (rule first_non_wildcard_col_SomeD(2))
  hence valid: "\<forall>r \<in> set rows. c < length (fst r)"
    by (auto simp: case_prod_unfold)
  from assms have "\<exists>r \<in> set (map (\<lambda>(ps,_,_). ps) rows). \<not> is_wildcard_like (r ! c)"
    by (rule first_non_wildcard_col_SomeD(3))
  hence ex_nw: "\<exists>r \<in> set rows. \<not> is_wildcard_like (fst r ! c)"
    by (auto simp: case_prod_unfold)
  show ?thesis
    by (rule matrix_weight_map_filter_lt_generic[OF
          specialise_row_bool_weight_le_cond
          specialise_row_bool_drops_non_wildcard_no_match_weight
          valid ex_nw])
qed


(* -------- specialise_row_int decrease -------- *)

lemma specialise_row_int_weight_le:
  "case specialise_row_int c s h r of None \<Rightarrow> True
                                    | Some r' \<Rightarrow> row_weight r' \<le> row_weight r"
  apply (cases r)
  apply (auto split: DecPattern.splits if_splits)
     apply (metis row_weight_drop_at)+
  done

lemma specialise_row_int_weight_le_cond:
  "c < length (fst r) \<Longrightarrow>
    case specialise_row_int c s h r of None \<Rightarrow> True
                                     | Some r' \<Rightarrow> row_weight r' \<le> row_weight r"
  by (rule specialise_row_int_weight_le)

lemma specialise_row_int_drops_non_wildcard_no_match_weight:
  assumes c_lt: "c < length (fst r)"
  assumes non_wc: "\<not> is_wildcard_like (fst r ! c)"
  shows "(case specialise_row_int c s h r of None \<Rightarrow> 0 | Some r' \<Rightarrow> row_weight r') < row_weight r"
proof -
  obtain ps bs body where r_eq: "r = (ps, bs, body)" by (cases r) auto
  from c_lt r_eq have c_lt_ps: "c < length ps" by simp
  from non_wc r_eq have non_wc_ps: "\<not> is_wildcard_like (ps ! c)" by simp
  from non_wc_ps have pos: "dec_pattern_weight (ps ! c) > 0"
    by (rule row_weight_pos_of_non_wildcard)
  show ?thesis
  proof (cases "ps ! c")
    case (DP_Int i)
    show ?thesis
    proof (cases "i = h")
      case True
      with DP_Int r_eq have spec_eq:
        "specialise_row_int c s h r = Some (drop_at c ps, bs, body)" by simp
      from c_lt_ps pos have
        "row_weight (drop_at c ps, bs, body) < row_weight (ps, bs, body)"
        by (rule row_weight_drop_at_lt)
      with spec_eq r_eq show ?thesis by simp
    next
      case False
      with DP_Int r_eq have spec_eq: "specialise_row_int c s h r = None" by simp
      from r_eq c_lt_ps pos have "row_weight r > 0"
        unfolding row_weight_def by (simp add: sum_list_drop_at_is_pos)
      with spec_eq show ?thesis by simp
    qed
  next
    case (DP_Bool b)
    with r_eq have spec_eq: "specialise_row_int c s h r = None" by simp
    from r_eq c_lt_ps pos have "row_weight r > 0"
      unfolding row_weight_def by (simp add: sum_list_drop_at_is_pos)
    with spec_eq show ?thesis by simp
  next
    case (DP_Variant h' mpat)
    with r_eq have spec_eq: "specialise_row_int c s h r = None" by simp
    from r_eq c_lt_ps pos have "row_weight r > 0"
      unfolding row_weight_def by (simp add: sum_list_drop_at_is_pos)
    with spec_eq show ?thesis by simp
  next
    case (DP_Record flds)
    with r_eq have spec_eq: "specialise_row_int c s h r = None" by simp
    from r_eq c_lt_ps pos have "row_weight r > 0"
      unfolding row_weight_def by (simp add: sum_list_drop_at_is_pos)
    with spec_eq show ?thesis by simp
  next
    case (DP_Var vr x ty)
    with non_wc_ps have False by simp
    thus ?thesis ..
  next
    case DP_Wildcard
    with non_wc_ps have False by simp
    thus ?thesis ..
  qed
qed

lemma matrix_weight_specialise_int_lt:
  assumes "first_non_wildcard_col (map (\<lambda>(ps,_,_). ps) rows) = Some c"
  shows "matrix_weight (List.map_filter (specialise_row_int c s h) rows) < matrix_weight rows"
proof -
  from assms have "\<forall>r \<in> set (map (\<lambda>(ps,_,_). ps) rows). c < length r"
    by (rule first_non_wildcard_col_SomeD(2))
  hence valid: "\<forall>r \<in> set rows. c < length (fst r)"
    by (auto simp: case_prod_unfold)
  from assms have "\<exists>r \<in> set (map (\<lambda>(ps,_,_). ps) rows). \<not> is_wildcard_like (r ! c)"
    by (rule first_non_wildcard_col_SomeD(3))
  hence ex_nw: "\<exists>r \<in> set rows. \<not> is_wildcard_like (fst r ! c)"
    by (auto simp: case_prod_unfold)
  show ?thesis
    by (rule matrix_weight_map_filter_lt_generic[OF
          specialise_row_int_weight_le_cond
          specialise_row_int_drops_non_wildcard_no_match_weight
          valid ex_nw])
qed


(* -------- specialise_row_variant decrease -------- *)

(* Unlike bool/int specialisers, variant's weight_le needs the
   additional hypothesis `c < length (fst r)` because some cases go
   through replace_at, whose weight bound needs c to be in range. *)
lemma specialise_row_variant_weight_le_cond:
  assumes c_lt: "c < length (fst r)"
  shows "case specialise_row_variant c s h has_payload r of None \<Rightarrow> True
                                                          | Some r' \<Rightarrow> row_weight r' \<le> row_weight r"
proof -
  obtain ps bs body where r_eq: "r = (ps, bs, body)" by (cases r) auto
  from c_lt r_eq have c_lt_ps: "c < length ps" by simp
  show ?thesis
  proof (cases "specialise_row_variant c s h has_payload r")
    case None
    thus ?thesis by simp
  next
    case (Some r')
    \<comment> \<open>Case-split on ps!c to enumerate the Some-producing branches.\<close>
    show ?thesis
    proof (cases "ps ! c")
      case (DP_Variant h' mpat)
      show ?thesis
      proof (cases "h' = h")
        case False
        with DP_Variant r_eq Some show ?thesis by simp   \<comment> \<open>None, contradicts Some\<close>
      next
        case True
        show ?thesis
        proof (cases mpat)
          case None
          with True DP_Variant r_eq Some have
            r'_eq: "r' = (drop_at c ps, bs, body)" by simp
          hence "row_weight r' \<le> row_weight r"
            using r_eq by (simp add: row_weight_drop_at)
          with Some show ?thesis by simp
        next
          case (Some p)
          with True DP_Variant r_eq \<open>specialise_row_variant c s h has_payload r = Option.Some r'\<close>
          have r'_eq: "r' = (replace_at c p ps, bs, body)" by simp
          \<comment> \<open>Weight of DP_Variant h' (Some p) is 1 + w(p); replacing with p
              gives strictly smaller weight, hence \<le>.\<close>
          have pc_eq: "ps ! c = DP_Variant h' (Option.Some p)"
            using DP_Variant Some by simp
          from c_lt_ps pc_eq have
            "row_weight (replace_at c p ps, bs, body) < row_weight (ps, bs, body)"
            by (rule row_weight_replace_at_variant_payload)
          with r_eq r'_eq \<open>specialise_row_variant c s h has_payload r = Option.Some r'\<close>
          show ?thesis by simp
        qed
      qed
    next
      case DP_Wildcard
      show ?thesis
      proof (cases has_payload)
        case True
        with DP_Wildcard r_eq Some have
          r'_eq: "r' = (replace_at c DP_Wildcard ps, bs, body)" by simp
        from c_lt_ps have
          "row_weight (replace_at c DP_Wildcard ps, bs, body) \<le> row_weight (ps, bs, body)"
          by (rule row_weight_replace_at_wildcard)
        with r_eq r'_eq Some show ?thesis by simp
      next
        case False
        with DP_Wildcard r_eq Some have
          r'_eq: "r' = (drop_at c ps, bs, body)" by simp
        hence "row_weight r' \<le> row_weight r"
          using r_eq by (simp add: row_weight_drop_at)
        with Some show ?thesis by simp
      qed
    next
      case (DP_Var vr x ty)
      show ?thesis
      proof (cases has_payload)
        case True
        with DP_Var r_eq Some have
          r'_eq: "r' = (replace_at c DP_Wildcard ps, bs @ [(vr, x, ty, s)], body)" by simp
        from c_lt_ps have
          "row_weight (replace_at c DP_Wildcard ps, bs @ [(vr, x, ty, s)], body)
              \<le> row_weight (ps, bs, body)"
          by (rule row_weight_replace_at_wildcard)
        with r_eq r'_eq Some show ?thesis by simp
      next
        case False
        with DP_Var r_eq Some have
          r'_eq: "r' = (drop_at c ps, bs @ [(vr, x, ty, s)], body)" by simp
        hence "row_weight r' \<le> row_weight r"
          using r_eq by (simp add: row_weight_drop_at)
        with Some show ?thesis by simp
      qed
    next
      \<comment> \<open>The remaining DecPattern cases all fall through to None in
          specialise_row_variant's definition, contradicting Some.\<close>
      case (DP_Bool b)
      with r_eq Some show ?thesis by simp
    next
      case (DP_Int i)
      with r_eq Some show ?thesis by simp
    next
      case (DP_Record flds)
      with r_eq Some show ?thesis by simp
    qed
  qed
qed

lemma specialise_row_variant_drops_non_wildcard_no_match_weight:
  assumes c_lt: "c < length (fst r)"
  assumes non_wc: "\<not> is_wildcard_like (fst r ! c)"
  shows "(case specialise_row_variant c s h has_payload r of None \<Rightarrow> 0
                                                            | Some r' \<Rightarrow> row_weight r') < row_weight r"
proof -
  obtain ps bs body where r_eq: "r = (ps, bs, body)" by (cases r) auto
  from c_lt r_eq have c_lt_ps: "c < length ps" by simp
  from non_wc r_eq have non_wc_ps: "\<not> is_wildcard_like (ps ! c)" by simp
  from non_wc_ps have pos_col: "dec_pattern_weight (ps ! c) > 0"
    by (rule row_weight_pos_of_non_wildcard)
  from r_eq c_lt_ps pos_col have pos_r: "row_weight r > 0"
    unfolding row_weight_def by (simp add: sum_list_drop_at_is_pos)
  show ?thesis
  proof (cases "ps ! c")
    case (DP_Variant h' mpat)
    show ?thesis
    proof (cases "h' = h")
      case False
      with DP_Variant r_eq have spec_eq:
        "specialise_row_variant c s h has_payload r = None" by simp
      from spec_eq pos_r show ?thesis by simp
    next
      case True
      show ?thesis
      proof (cases mpat)
        case None
        with True DP_Variant r_eq have spec_eq:
          "specialise_row_variant c s h has_payload r = Some (drop_at c ps, bs, body)" by simp
        from c_lt_ps pos_col have
          "row_weight (drop_at c ps, bs, body) < row_weight (ps, bs, body)"
          by (rule row_weight_drop_at_lt)
        with spec_eq r_eq show ?thesis by simp
      next
        case (Some p)
        with True DP_Variant r_eq have spec_eq:
          "specialise_row_variant c s h has_payload r = Some (replace_at c p ps, bs, body)" by simp
        from Some DP_Variant have pc_eq: "ps ! c = DP_Variant h' (Some p)" by simp
        from c_lt_ps pc_eq have
          "row_weight (replace_at c p ps, bs, body) < row_weight (ps, bs, body)"
          by (rule row_weight_replace_at_variant_payload)
        with spec_eq r_eq show ?thesis by simp
      qed
    qed
  next
    case (DP_Bool b)
    with r_eq have spec_eq: "specialise_row_variant c s h has_payload r = None" by simp
    from spec_eq pos_r show ?thesis by simp
  next
    case (DP_Int i)
    with r_eq have spec_eq: "specialise_row_variant c s h has_payload r = None" by simp
    from spec_eq pos_r show ?thesis by simp
  next
    case (DP_Record flds)
    with r_eq have spec_eq: "specialise_row_variant c s h has_payload r = None" by simp
    from spec_eq pos_r show ?thesis by simp
  next
    case (DP_Var vr x ty)
    with non_wc_ps have False by simp
    thus ?thesis ..
  next
    case DP_Wildcard
    with non_wc_ps have False by simp
    thus ?thesis ..
  qed
qed

lemma matrix_weight_specialise_variant_lt:
  assumes "first_non_wildcard_col (map (\<lambda>(ps,_,_). ps) rows) = Some c"
  shows "matrix_weight (List.map_filter (specialise_row_variant c s h has_payload) rows) < matrix_weight rows"
proof -
  from assms have "\<forall>r \<in> set (map (\<lambda>(ps,_,_). ps) rows). c < length r"
    by (rule first_non_wildcard_col_SomeD(2))
  hence valid: "\<forall>r \<in> set rows. c < length (fst r)"
    by (auto simp: case_prod_unfold)
  from assms have "\<exists>r \<in> set (map (\<lambda>(ps,_,_). ps) rows). \<not> is_wildcard_like (r ! c)"
    by (rule first_non_wildcard_col_SomeD(3))
  hence ex_nw: "\<exists>r \<in> set rows. \<not> is_wildcard_like (fst r ! c)"
    by (auto simp: case_prod_unfold)
  show ?thesis
    by (rule matrix_weight_map_filter_lt_generic[OF
          specialise_row_variant_weight_le_cond
          specialise_row_variant_drops_non_wildcard_no_match_weight
          valid ex_nw])
qed

(* -------- expand_record_row decrease -------- *)

lemma sum_list_splice_at_le:
  fixes f :: "'a \<Rightarrow> nat"
  shows "c < length xs \<Longrightarrow> sum_list (map f ys) \<le> f (xs ! c) \<Longrightarrow>
    sum_list (map f (splice_at c ys xs)) \<le> sum_list (map f xs)"
  by (induction c ys xs rule: splice_at.induct) auto

lemma expand_record_row_weight_le:
  assumes c_lt: "c < length (fst r)"
  shows "row_weight (expand_record_row c s fld_names r) \<le> row_weight r"
proof -
  obtain ps bs body where r_eq: "r = (ps, bs, body)" by (cases r) auto
  from c_lt r_eq have c_lt_ps: "c < length ps" by simp
  show ?thesis
  proof (cases "ps ! c")
    case (DP_Record flds)
    have splice_w_le: "sum_list (map dec_pattern_weight (map snd flds)) \<le> dec_pattern_weight (ps ! c)"
      using DP_Record by simp
    from c_lt_ps splice_w_le have
      "sum_list (map dec_pattern_weight (splice_at c (map snd flds) ps))
       \<le> sum_list (map dec_pattern_weight ps)"
      by (rule sum_list_splice_at_le)
    with r_eq DP_Record show ?thesis
      unfolding row_weight_def by simp
  next
    case DP_Wildcard
    have splice_w_zero:
      "sum_list (map dec_pattern_weight (replicate (length fld_names) DP_Wildcard)) = 0"
      by (induction "length fld_names") auto
    have pc_zero: "dec_pattern_weight (ps ! c) = 0"
      using DP_Wildcard by simp
    from c_lt_ps splice_w_zero pc_zero have
      "sum_list (map dec_pattern_weight
          (splice_at c (replicate (length fld_names) DP_Wildcard) ps))
       \<le> sum_list (map dec_pattern_weight ps)"
      by (intro sum_list_splice_at_le) auto
    with r_eq DP_Wildcard show ?thesis
      unfolding row_weight_def by simp
  next
    case (DP_Var vr x ty)
    have splice_w_zero:
      "sum_list (map dec_pattern_weight (replicate (length fld_names) DP_Wildcard)) = 0"
      by (induction "length fld_names") auto
    have pc_zero: "dec_pattern_weight (ps ! c) = 0"
      using DP_Var by simp
    from c_lt_ps splice_w_zero pc_zero have
      "sum_list (map dec_pattern_weight
          (splice_at c (replicate (length fld_names) DP_Wildcard) ps))
       \<le> sum_list (map dec_pattern_weight ps)"
      by (intro sum_list_splice_at_le) auto
    with r_eq DP_Var show ?thesis
      unfolding row_weight_def by simp
  next
    \<comment> \<open>Remaining cases: expand_record_row's unreachable fallback returns r unchanged.\<close>
    case (DP_Bool b)
    with r_eq show ?thesis by simp
  next
    case (DP_Int i)
    with r_eq show ?thesis by simp
  next
    case (DP_Variant h' mpat)
    with r_eq show ?thesis by simp
  qed
qed

lemma expand_record_row_weight_lt_on_record:
  assumes c_lt: "c < length (fst r)"
  assumes is_rec: "\<exists>flds. fst r ! c = DP_Record flds"
  shows "row_weight (expand_record_row c s fld_names r) < row_weight r"
proof -
  obtain ps bs body where r_eq: "r = (ps, bs, body)" by (cases r) auto
  from c_lt r_eq have c_lt_ps: "c < length ps" by simp
  from is_rec r_eq obtain flds where flds_eq: "ps ! c = DP_Record flds" by auto
  have sub_w_lt: "sum_list (map dec_pattern_weight (map snd flds)) < dec_pattern_weight (ps ! c)"
    using flds_eq by simp
  from c_lt_ps sub_w_lt have
    "sum_list (map dec_pattern_weight (splice_at c (map snd flds) ps))
     < sum_list (map dec_pattern_weight ps)"
    by (rule sum_list_splice_at_lt)
  with r_eq flds_eq show ?thesis
    unfolding row_weight_def by simp
qed

lemma matrix_weight_expand_record_le:
  assumes all_valid: "\<forall>r \<in> set rows. c < length (fst r)"
  shows "matrix_weight (map (expand_record_row c s fld_names) rows) \<le> matrix_weight rows"
  using all_valid
proof (induction rows)
  case Nil
  thus ?case by (simp add: matrix_weight_def)
next
  case (Cons r rs)
  from Cons.prems have c_lt: "c < length (fst r)" by simp
  from Cons.prems have rs_valid: "\<forall>r \<in> set rs. c < length (fst r)" by simp
  have head_le: "row_weight (expand_record_row c s fld_names r) \<le> row_weight r"
    by (rule expand_record_row_weight_le[OF c_lt])
  from Cons.IH[OF rs_valid] head_le show ?case
    by (simp add: matrix_weight_def)
qed

lemma matrix_weight_expand_record_lt_pointwise:
  assumes all_valid: "\<forall>r \<in> set rows. c < length (fst r)"
  assumes ex_record: "\<exists>r \<in> set rows. \<exists>flds. fst r ! c = DP_Record flds"
  shows "matrix_weight (map (expand_record_row c s fld_names) rows) < matrix_weight rows"
  using all_valid ex_record
proof (induction rows)
  case Nil
  thus ?case by simp
next
  case (Cons r rs)
  from Cons.prems(1) have c_lt: "c < length (fst r)" by simp
  from Cons.prems(1) have rs_valid: "\<forall>r \<in> set rs. c < length (fst r)" by simp
  show ?case
  proof (cases "\<exists>flds. fst r ! c = DP_Record flds")
    case True
    have head_lt: "row_weight (expand_record_row c s fld_names r) < row_weight r"
      by (rule expand_record_row_weight_lt_on_record[OF c_lt True])
    have tail_le: "matrix_weight (map (expand_record_row c s fld_names) rs) \<le> matrix_weight rs"
      by (rule matrix_weight_expand_record_le[OF rs_valid])
    from head_lt tail_le show ?thesis
      by (simp add: matrix_weight_def)
  next
    case False
    with Cons.prems(2) have ex_rs: "\<exists>r \<in> set rs. \<exists>flds. fst r ! c = DP_Record flds"
      by auto
    have tail_lt: "matrix_weight (map (expand_record_row c s fld_names) rs) < matrix_weight rs"
      using Cons.IH[OF rs_valid ex_rs] .
    have head_le: "row_weight (expand_record_row c s fld_names r) \<le> row_weight r"
      by (rule expand_record_row_weight_le[OF c_lt])
    from head_le tail_lt show ?thesis
      by (simp add: matrix_weight_def)
  qed
qed

(* Deduce "some row has a DP_Record at col c" from first_non_wildcard_col
   + head_kind_of = HK_Record. *)

lemma head_kind_of_Some_HK_Record_implies_DP_Record:
  "head_kind_of p = Some (HK_Record fld_names) \<Longrightarrow> \<exists>flds. p = DP_Record flds"
  by (cases p) auto

lemma filter_hd_non_wildcard_exists:
  assumes ex_nw: "\<exists>p \<in> set ps. \<not> is_wildcard_like p"
  shows "hd (filter (\<lambda>p. \<not> is_wildcard_like p) ps) \<in> set ps \<and>
         \<not> is_wildcard_like (hd (filter (\<lambda>p. \<not> is_wildcard_like p) ps))"
proof -
  from ex_nw have "filter (\<lambda>p. \<not> is_wildcard_like p) ps \<noteq> []"
    by (auto simp: filter_empty_conv)
  hence nonempty: "filter (\<lambda>p. \<not> is_wildcard_like p) ps \<noteq> []" .
  from nonempty have "hd (filter (\<lambda>p. \<not> is_wildcard_like p) ps)
                         \<in> set (filter (\<lambda>p. \<not> is_wildcard_like p) ps)"
    using list.set_sel(1) by blast
  thus ?thesis by auto
qed

lemma matrix_weight_expand_record_lt:
  assumes fnw: "first_non_wildcard_col (map (\<lambda>(ps,_,_). ps) rows) = Some c"
  assumes hk:  "head_kind_of (hd (filter (\<lambda>p. \<not> is_wildcard_like p)
                     (map (\<lambda>(ps,_,_). ps ! c) rows))) = Some (HK_Record fld_names')"
  shows "matrix_weight (map (expand_record_row c s fld_names) rows) < matrix_weight rows"
proof -
  from fnw have "\<forall>r \<in> set (map (\<lambda>(ps,_,_). ps) rows). c < length r"
    by (rule first_non_wildcard_col_SomeD(2))
  hence valid: "\<forall>r \<in> set rows. c < length (fst r)"
    by (auto simp: case_prod_unfold)
  from fnw have ex_nw_cols: "\<exists>r \<in> set (map (\<lambda>(ps,_,_). ps) rows). \<not> is_wildcard_like (r ! c)"
    by (rule first_non_wildcard_col_SomeD(3))
  hence ex_nw_in_col_pats: "\<exists>p \<in> set (map (\<lambda>(ps,_,_). ps ! c) rows). \<not> is_wildcard_like p"
    by (auto simp: case_prod_unfold)
  from hk have "\<exists>flds. hd (filter (\<lambda>p. \<not> is_wildcard_like p)
                     (map (\<lambda>(ps,_,_). ps ! c) rows)) = DP_Record flds"
    by (rule head_kind_of_Some_HK_Record_implies_DP_Record)
  then obtain flds where hd_eq:
    "hd (filter (\<lambda>p. \<not> is_wildcard_like p) (map (\<lambda>(ps,_,_). ps ! c) rows)) = DP_Record flds"
    by auto
  from filter_hd_non_wildcard_exists[OF ex_nw_in_col_pats] hd_eq
  have "DP_Record flds \<in> set (map (\<lambda>(ps,_,_). ps ! c) rows)"
    by auto
  then obtain r where r_in: "r \<in> set rows" and r_eq: "fst r ! c = DP_Record flds"
    by (auto simp: case_prod_unfold)
  from r_in r_eq have ex_record: "\<exists>r \<in> set rows. \<exists>flds. fst r ! c = DP_Record flds"
    by blast
  from valid ex_record show ?thesis
    by (rule matrix_weight_expand_record_lt_pointwise)
qed

(* Termination proof for compile_matrix. *)
termination compile_matrix
  apply (relation "measure (\<lambda>(scruts, rows). matrix_weight rows)")
  apply simp
     apply (auto simp: matrix_weight_default_rows_lt
                       matrix_weight_specialise_bool_lt
                       matrix_weight_specialise_int_lt
                       matrix_weight_specialise_variant_lt
                       matrix_weight_expand_record_lt)
  done


section \<open>Compiler entry point\<close>

(* Public entry point compile_match takes a scrutinee, the scrutinee's type,
   a fresh name (must not clash with anything else in scope, including any
   user pattern variables), and a non-empty list of (DecPattern,
   elaborated-body) rows.

   Wraps the entire match in MT_Bind freshName scrutTy scrut, then runs
   compile_matrix with [CoreTm_Var freshName] as the column scrutinee.
   This binding is needed for soundness: if the scrutinee mentions a free
   variable that a pattern then shadows, projections of the scrutinee
   inside the match body would otherwise rebind to the wrong thing. By
   binding the scrutinee to a fresh name first, all internal scruts in
   compile_matrix only ever reference the fresh name (or projections
   thereof), eliminating the shadowing hazard.

   Internally the worker compile_matrix operates on an N-column matrix of
   scrutinees and rows. Zero-row inputs are user errors to be rejected
   upstream. *)

definition compile_match ::
  "CoreTerm \<Rightarrow> CoreType \<Rightarrow> string \<Rightarrow> (DecPattern \<times> 'body) list \<Rightarrow> 'body MatchTree"
where
  "compile_match scrut scrutTy freshName rows =
    MT_Bind Var freshName scrutTy scrut
      (compile_matrix ([CoreTm_Var freshName],
                       map (\<lambda>(p, body). ([p], [], body)) rows))"


section \<open>Translation: MatchTree \<rightarrow> CoreTerm\<close>

(* For BabTm_Match. Ignores VarOrRef / CoreType on MT_Bind -- CoreTm_Let
   has no ref variant and infers its type from rhs. *)
fun matchtree_to_term :: "CoreTerm MatchTree \<Rightarrow> CoreTerm" where
  "matchtree_to_term (MT_Leaf t) = t"
| "matchtree_to_term (MT_Bind _ x _ rhs sub) =
    CoreTm_Let x rhs (matchtree_to_term sub)"
| "matchtree_to_term (MT_Test scrut arms) =
    CoreTm_Match scrut (map (\<lambda>(p, sub). (p, matchtree_to_term sub)) arms)"


section \<open>Translation: MatchTree \<rightarrow> CoreStatement list\<close>

(* For BabStmt_Match. The ghost flag is threaded in from the enclosing
   BabStmt_Match and applies uniformly to every binding / sub-match. *)
fun matchtree_to_stmts :: "GhostOrNot \<Rightarrow> CoreStatement list MatchTree \<Rightarrow> CoreStatement list" where
  "matchtree_to_stmts _ (MT_Leaf stmts) = stmts"
| "matchtree_to_stmts g (MT_Bind vr x ty rhs sub) =
    CoreStmt_VarDecl g x vr ty rhs # matchtree_to_stmts g sub"
| "matchtree_to_stmts g (MT_Test scrut arms) =
    [ CoreStmt_Match g scrut (map (\<lambda>(p, sub). (p, matchtree_to_stmts g sub)) arms) ]"


section \<open>Typing predicates\<close>

(* Env extension corresponding to a single MT_Bind, mirroring exactly the
   env extension that CoreTm_Let / CoreStmt_VarDecl(Var) perform. *)
definition extend_env_with_bind ::
  "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> string \<Rightarrow> CoreType \<Rightarrow> CoreTyEnv" where
  "extend_env_with_bind env ghost x ty =
     env \<lparr> TE_LocalVars := fmupd x ty (TE_LocalVars env),
           TE_GhostLocals := (if ghost = Ghost
                              then finsert x (TE_GhostLocals env)
                              else fminus (TE_GhostLocals env) {|x|}),
           TE_ConstLocals := finsert x (TE_ConstLocals env) \<rparr>"

(* Compatibility of a DecPattern with a CoreType under env. Mirrors
   Core's pattern_compatible but at the decorated-pattern level.
   Used as the input precondition for compile_matrix.

   Recurses on pattern structure (using the optional payload / sub-patterns
   list); the type argument is unrestricted at recursive sites. *)
fun dec_pattern_compatible :: "CoreTyEnv \<Rightarrow> DecPattern \<Rightarrow> CoreType \<Rightarrow> bool"
and dec_pattern_compatible_list :: "CoreTyEnv \<Rightarrow> DecPattern list \<Rightarrow> CoreType list \<Rightarrow> bool"
where
  "dec_pattern_compatible env (DP_Var _ _ vTy) ty = (vTy = ty)"
| "dec_pattern_compatible env DP_Wildcard _ = True"
| "dec_pattern_compatible env (DP_Bool _) ty = (ty = CoreTy_Bool)"
| "dec_pattern_compatible env (DP_Int _) ty = is_integer_type ty"
| "dec_pattern_compatible env (DP_Variant ctorName payload_opt) ty =
    (case fmlookup (TE_DataCtors env) ctorName of
       None \<Rightarrow> False
     | Some (dtName, tyvars, payloadTy) \<Rightarrow>
         (case ty of
            CoreTy_Datatype tyName tyArgs \<Rightarrow>
              tyName = dtName
              \<and> length tyArgs = length tyvars
              \<and> (case payload_opt of
                   None \<Rightarrow> True
                 | Some inner \<Rightarrow>
                     dec_pattern_compatible env inner
                       (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy))
          | _ \<Rightarrow> False))"
| "dec_pattern_compatible env (DP_Record flds) ty =
    (case ty of
       CoreTy_Record fieldTypes \<Rightarrow>
         map fst flds = map fst fieldTypes
         \<and> dec_pattern_compatible_list env (map snd flds) (map snd fieldTypes)
     | _ \<Rightarrow> False)"
| "dec_pattern_compatible_list env [] [] = True"
| "dec_pattern_compatible_list env (p # ps) (t # ts) =
     (dec_pattern_compatible env p t \<and> dec_pattern_compatible_list env ps ts)"
| "dec_pattern_compatible_list env _ _ = False"

(* Well-typedness of a MatchTree whose leaves are CoreTerms producing
   a value of type resultTy. *)
fun matchtree_term_well_typed ::
  "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> CoreType \<Rightarrow> CoreTerm MatchTree \<Rightarrow> bool" where
  "matchtree_term_well_typed env ghost resultTy (MT_Leaf t) =
     (core_term_type env ghost t = Some resultTy)"
| "matchtree_term_well_typed env ghost resultTy (MT_Bind _ x bindTy rhs sub) =
     (core_term_type env ghost rhs = Some bindTy
      \<and> matchtree_term_well_typed (extend_env_with_bind env ghost x bindTy)
                                  ghost resultTy sub)"
| "matchtree_term_well_typed env ghost resultTy (MT_Test scrut arms) =
     (arms \<noteq> []
      \<and> (\<exists>scrutTy. core_term_type env ghost scrut = Some scrutTy
                  \<and> list_all (\<lambda>(p, _). pattern_compatible env p scrutTy) arms)
      \<and> list_all (\<lambda>(_, sub). matchtree_term_well_typed env ghost resultTy sub) arms)"


subsection \<open>BindList typing\<close>

(* Extend an environment with a whole BindList. The first entry of the list
   becomes the outermost binding (matching binds_to_tree's emission order). *)
fun extend_env_with_bindlist ::
  "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> BindList \<Rightarrow> CoreTyEnv" where
  "extend_env_with_bindlist env _ [] = env"
| "extend_env_with_bindlist env ghost ((vr, x, ty, rhs) # rest) =
     extend_env_with_bindlist (extend_env_with_bind env ghost x ty) ghost rest"

(* A BindList is well-typed in env if each entry's rhs has the declared
   type, in the env progressively extended by the previous entries. *)
fun bindlist_well_typed ::
  "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> BindList \<Rightarrow> bool" where
  "bindlist_well_typed env ghost [] = True"
| "bindlist_well_typed env ghost ((vr, x, ty, rhs) # rest) =
     (core_term_type env ghost rhs = Some ty
      \<and> bindlist_well_typed (extend_env_with_bind env ghost x ty) ghost rest)"


subsection \<open>Matrix well-typedness\<close>

(* All DP_Var names appearing in a decorated pattern. Used to express the
   freshness invariant on matrices. *)
fun dec_pattern_var_names :: "DecPattern \<Rightarrow> string fset"
and dec_pattern_var_names_list :: "DecPattern list \<Rightarrow> string fset"
where
  "dec_pattern_var_names (DP_Var _ name _) = {|name|}"
| "dec_pattern_var_names (DP_Bool _) = {||}"
| "dec_pattern_var_names (DP_Int _) = {||}"
| "dec_pattern_var_names DP_Wildcard = {||}"
| "dec_pattern_var_names (DP_Variant _ None) = {||}"
| "dec_pattern_var_names (DP_Variant _ (Some inner)) = dec_pattern_var_names inner"
| "dec_pattern_var_names (DP_Record flds) = dec_pattern_var_names_list (map snd flds)"
| "dec_pattern_var_names_list [] = {||}"
| "dec_pattern_var_names_list (p # ps) =
     dec_pattern_var_names p |\<union>| dec_pattern_var_names_list ps"

(* All DP_Var names plus all bind-names appearing in a row. These are the
   names that must not appear free in any scrutinee. *)
definition row_var_names :: "'body Row \<Rightarrow> string fset" where
  "row_var_names row =
     (case row of (pats, binds, _) \<Rightarrow>
        dec_pattern_var_names_list pats |\<union>| fset_of_list (map (\<lambda>(_, x, _, _). x) binds))"

(* All (vr, name, type) triples bound by the DP_Var nodes inside a single
   pattern. The vr field on a DP_Var carries no typing information so we
   keep it here only for symmetry with dec_pattern_vars in ElabPattern.thy. *)
fun dec_pattern_var_bindings ::
  "DecPattern \<Rightarrow> (VarOrRef \<times> string \<times> CoreType) list"
and dec_pattern_var_bindings_list ::
  "DecPattern list \<Rightarrow> (VarOrRef \<times> string \<times> CoreType) list"
where
  "dec_pattern_var_bindings (DP_Var vr x ty) = [(vr, x, ty)]"
| "dec_pattern_var_bindings (DP_Bool _) = []"
| "dec_pattern_var_bindings (DP_Int _) = []"
| "dec_pattern_var_bindings DP_Wildcard = []"
| "dec_pattern_var_bindings (DP_Variant _ None) = []"
| "dec_pattern_var_bindings (DP_Variant _ (Some inner)) = dec_pattern_var_bindings inner"
| "dec_pattern_var_bindings (DP_Record flds) = dec_pattern_var_bindings_list (map snd flds)"
| "dec_pattern_var_bindings_list [] = []"
| "dec_pattern_var_bindings_list (p # ps) =
     dec_pattern_var_bindings p @ dec_pattern_var_bindings_list ps"

(* Extend env by every (vr, name, type) DP_Var binding in a pattern list.
   Used in row_term_well_typed to bring all the row's pattern variables
   (across all columns, processed and unprocessed) into scope when
   typechecking the body. *)
definition extend_env_with_pattern_vars ::
  "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> DecPattern list \<Rightarrow> CoreTyEnv" where
  "extend_env_with_pattern_vars env ghost ps =
     foldr (\<lambda>(_, x, ty) e. extend_env_with_bind e ghost x ty)
           (dec_pattern_var_bindings_list ps) env"

(* Freshness: every variable name that appears free in any column scrutinee
   does not coincide with any pattern-var-name or bind-name in any row.
   This invariant is established by compile_match's wrapping let, and
   preserved by every column-elimination step (none of which add new free
   vars to scruts; record/variant projections inherit free vars from the
   parent scrut). *)
definition matrix_scrut_freshness :: "CoreTerm MatchMatrix \<Rightarrow> bool" where
  "matrix_scrut_freshness mtx =
     (case mtx of (scruts, rows) \<Rightarrow>
        (\<forall>s \<in> set scruts. \<forall>row \<in> set rows.
           core_term_free_vars s |\<inter>| row_var_names row = {||}))"

(* A row is well-typed (for the term variant of compile_matrix) if its
   binds typecheck progressively, and *under* the env extended by those
   binds:
     - each pattern in column i is compatible with column-types[i];
     - the body has type resultTy, in env extended by both the binds and
       the pattern variables of every (still-unprocessed) column. The
       latter is needed because the user's body legitimately references
       pattern variables that haven't yet been "extracted" by column
       elimination — they reach the bindlist only at the base case (or
       when their column is specialised in a way that emits a bind).
   Note: scruts are typed in the *original* env (they refer only to
   pre-existing bindings), but we don't impose that as a per-row check
   since it's a matrix-level invariant (see matrix_term_well_typed). *)

(* A row-uniqueness invariant: a pattern's DP_Var names are pairwise distinct,
   and across the row's pattern list they're still distinct (no name appears
   in two different patterns). This is enforced by the elaborator's
   no-duplicate check. *)
definition pattern_var_names_distinct :: "DecPattern list \<Rightarrow> bool" where
  "pattern_var_names_distinct ps =
     distinct (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps))"

fun row_term_well_typed ::
  "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> CoreType list \<Rightarrow> CoreType
   \<Rightarrow> CoreTerm Row \<Rightarrow> bool" where
  "row_term_well_typed env ghost colTys resultTy (pats, binds, body) =
     (length pats = length colTys
      \<and> bindlist_well_typed env ghost binds
      \<and> pattern_var_names_distinct pats
      \<and> (let env_bs = extend_env_with_bindlist env ghost binds;
             env_body = extend_env_with_pattern_vars env_bs ghost pats
         in dec_pattern_compatible_list env_bs pats colTys
            \<and> core_term_type env_body ghost body = Some resultTy))"

(* A whole matrix is well-typed if each scrutinee typechecks (yielding
   the column types), every row is well-typed against those column types
   and the result type, and the freshness invariant on scrutinees holds. *)
definition matrix_term_well_typed ::
  "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> CoreType
   \<Rightarrow> CoreTerm MatchMatrix \<Rightarrow> bool" where
  "matrix_term_well_typed env ghost resultTy mtx =
     (case mtx of (scruts, rows) \<Rightarrow>
        (\<exists>colTys. length colTys = length scruts
                  \<and> list_all2 (\<lambda>s ty. core_term_type env ghost s = Some ty) scruts colTys
                  \<and> list_all (row_term_well_typed env ghost colTys resultTy) rows)
        \<and> matrix_scrut_freshness mtx)"


section \<open>Typing-preservation: matchtree_to_term\<close>

(* matchtree_to_term preserves well-typedness: a well-typed CoreTerm MatchTree
   translates to a CoreTerm of the expected type. *)
lemma matchtree_to_term_preserves_typing:
  "matchtree_term_well_typed env ghost resultTy mt
   \<Longrightarrow> core_term_type env ghost (matchtree_to_term mt) = Some resultTy"
proof (induction mt arbitrary: env)
  case (MT_Leaf t)
  thus ?case by simp
next
  case (MT_Test scrut arms)
  from MT_Test.prems obtain scrutTy where
    scrut_ty: "core_term_type env ghost scrut = Some scrutTy" and
    pat_compat: "list_all (\<lambda>(p, _). pattern_compatible env p scrutTy) arms"
    by auto
  from MT_Test.prems have arms_ne: "arms \<noteq> []" by simp
  from MT_Test.prems have arms_wt:
    "list_all (\<lambda>(_, sub). matchtree_term_well_typed env ghost resultTy sub) arms"
    by simp

  let ?translated_arms = "map (\<lambda>(p, sub). (p, matchtree_to_term sub)) arms"

  \<comment> \<open>Pattern list is preserved by translation\<close>
  have pats_eq: "map fst ?translated_arms = map fst arms"
    by (induction arms) auto

  \<comment> \<open>Each translated arm body has type resultTy\<close>
  have bodies_typed:
    "list_all (\<lambda>body. core_term_type env ghost body = Some resultTy)
              (map snd ?translated_arms)"
  proof -
    have "\<forall>arm \<in> set arms.
            core_term_type env ghost (matchtree_to_term (snd arm)) = Some resultTy"
    proof
      fix arm assume arm_in: "arm \<in> set arms"
      obtain p sub where arm_eq: "arm = (p, sub)"
        using prod.exhaust by blast
      with arm_in arms_wt
      have sub_wt: "matchtree_term_well_typed env ghost resultTy sub"
        by (auto simp: list_all_iff)
      have sub_in_snds: "sub \<in> Basic_BNFs.snds arm"
        using arm_eq by simp
      from MT_Test.IH[OF arm_in sub_in_snds sub_wt]
      have "core_term_type env ghost (matchtree_to_term sub) = Some resultTy" .
      thus "core_term_type env ghost (matchtree_to_term (snd arm)) = Some resultTy"
        using arm_eq by simp
    qed
    thus ?thesis by (auto simp: list_all_iff split: prod.splits)
  qed

  \<comment> \<open>arms is non-empty so the translated arms list is also non-empty\<close>
  from arms_ne have translated_ne: "?translated_arms \<noteq> []" by simp

  \<comment> \<open>Each translated arm's pattern is compatible with scrutTy\<close>
  have translated_pat_compat:
    "list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst ?translated_arms)"
    using pat_compat pats_eq
    by (induction arms) auto

  \<comment> \<open>The first translated arm's body has type resultTy\<close>
  from arms_ne bodies_typed
  have hd_body_ty: "core_term_type env ghost (snd (hd ?translated_arms)) = Some resultTy"
    by (cases arms) (auto simp: list_all_iff)

  \<comment> \<open>The tail of translated arm bodies all have type resultTy\<close>
  from arms_ne bodies_typed
  have tl_bodies_typed:
    "list_all (\<lambda>body. core_term_type env ghost body = Some resultTy)
              (tl (map snd ?translated_arms))"
    by (cases arms) auto

  have pats_eq_comp: "map (fst \<circ> (\<lambda>(p, sub). (p, matchtree_to_term sub))) arms = map fst arms"
    by (induction arms) auto
  have snd_eq_comp:
    "map (snd \<circ> (\<lambda>(p, sub). (p, matchtree_to_term sub))) arms
     = map (\<lambda>(p, sub). matchtree_to_term sub) arms"
    by (induction arms) auto
  show ?case
    using scrut_ty translated_ne translated_pat_compat
          pats_eq hd_body_ty tl_bodies_typed
    by (simp add: Let_def pats_eq_comp snd_eq_comp)
next
  case (MT_Bind vr x bindTy rhs sub)
  from MT_Bind.prems have rhs_ty: "core_term_type env ghost rhs = Some bindTy" by simp
  from MT_Bind.prems have sub_wt:
    "matchtree_term_well_typed (extend_env_with_bind env ghost x bindTy) ghost resultTy sub"
    by simp
  from MT_Bind.IH[OF sub_wt]
  have sub_ty: "core_term_type (extend_env_with_bind env ghost x bindTy) ghost
                  (matchtree_to_term sub) = Some resultTy" .
  show ?case
    using rhs_ty sub_ty
    by (simp add: extend_env_with_bind_def)
qed


section \<open>Typing-preservation: compile_matrix\<close>

subsection \<open>Helper lemmas\<close>

(* binds_to_tree preserves well-typedness: if the BindList is well-typed in env,
   and the inner tree is well-typed in env extended by all the binds, then
   the wrapped tree is well-typed in env. *)
lemma binds_to_tree_preserves_typing:
  "bindlist_well_typed env ghost binds
   \<Longrightarrow> matchtree_term_well_typed (extend_env_with_bindlist env ghost binds)
                                ghost resultTy inner
   \<Longrightarrow> matchtree_term_well_typed env ghost resultTy
         (binds_to_tree binds inner)"
proof (induction binds arbitrary: env)
  case Nil
  thus ?case by simp
next
  case (Cons b rest)
  obtain vr x ty rhs where b_eq: "b = (vr, x, ty, rhs)"
    by (cases b) auto
  let ?env' = "extend_env_with_bind env ghost x ty"
  from Cons.prems(1) b_eq have
    rhs_ty: "core_term_type env ghost rhs = Some ty" and
    rest_wt: "bindlist_well_typed ?env' ghost rest"
    by auto
  from Cons.prems(2) b_eq have
    inner_wt: "matchtree_term_well_typed (extend_env_with_bindlist ?env' ghost rest)
                                          ghost resultTy inner"
    by simp
  from Cons.IH[OF rest_wt inner_wt]
  have wrap_wt: "matchtree_term_well_typed ?env' ghost resultTy
                   (binds_to_tree rest inner)" .
  show ?case
    using rhs_ty wrap_wt b_eq by simp
qed

(* dec_pattern_compatible only inspects env via TE_DataCtors, so any env
   modification that leaves TE_DataCtors unchanged preserves it. We state
   this as a generic congruence on TE_DataCtors. *)
lemma dec_pattern_compatible_TE_DataCtors_cong:
  "TE_DataCtors env1 = TE_DataCtors env2
   \<Longrightarrow> dec_pattern_compatible env1 p t = dec_pattern_compatible env2 p t"
and dec_pattern_compatible_list_TE_DataCtors_cong:
  "TE_DataCtors env1 = TE_DataCtors env2
   \<Longrightarrow> dec_pattern_compatible_list env1 ps ts = dec_pattern_compatible_list env2 ps ts"
proof (induction env1 p t and env1 ps ts arbitrary: env2 and env2
       rule: dec_pattern_compatible_dec_pattern_compatible_list.induct)
qed (auto split: option.splits CoreType.splits prod.splits)

(* Specialisation for our use case. *)
lemma dec_pattern_compatible_extend_env_with_bind:
  "dec_pattern_compatible (extend_env_with_bind env ghost x ty) p t
   = dec_pattern_compatible env p t"
  using dec_pattern_compatible_TE_DataCtors_cong[of "extend_env_with_bind env ghost x ty" env p t]
  by (simp add: extend_env_with_bind_def)

lemma dec_pattern_compatible_list_extend_env_with_bind:
  "dec_pattern_compatible_list (extend_env_with_bind env ghost x ty) ps ts
   = dec_pattern_compatible_list env ps ts"
  using dec_pattern_compatible_list_TE_DataCtors_cong[of "extend_env_with_bind env ghost x ty" env ps ts]
  by (simp add: extend_env_with_bind_def)

(* Wrapper around core_term_type_irrelevant_var: if a term doesn't reference
   the variable name x, its type is unchanged when env is extended by a new
   binding for x. This is the form we need for the BindList preservation
   lemma below. *)
lemma core_term_type_extend_env_with_bind_irrelevant:
  assumes "x |\<notin>| core_term_free_vars tm"
      and "core_term_type env ghost tm = Some ty"
  shows "core_term_type (extend_env_with_bind env ghost x bindTy) ghost tm = Some ty"
proof -
  let ?env_modified = "env \<lparr> TE_LocalVars := fmupd x bindTy (TE_LocalVars env),
                              TE_GhostLocals := (if ghost = Ghost
                                                 then finsert x (TE_GhostLocals env)
                                                 else fminus (TE_GhostLocals env) {|x|}) \<rparr>"
  have ghost_eq: "\<forall>y. y \<noteq> x \<longrightarrow>
                    (y |\<in>| (if ghost = Ghost
                            then finsert x (TE_GhostLocals env)
                            else fminus (TE_GhostLocals env) {|x|})
                     \<longleftrightarrow> y |\<in>| TE_GhostLocals env)"
    by auto
  have step1: "core_term_type ?env_modified ghost tm = Some ty"
    using core_term_type_irrelevant_var[OF assms(1) assms(2) ghost_eq] .
  have step2: "extend_env_with_bind env ghost x bindTy
               = ?env_modified \<lparr> TE_ConstLocals := finsert x (TE_ConstLocals env) \<rparr>"
    by (simp add: extend_env_with_bind_def)
  show ?thesis
    using step1 step2 core_term_type_TE_ConstLocals_irrelevant by simp
qed

(* When all pattern columns are wildcard-like and compatible with the column
   types, extract_binds produces a well-typed BindList. The freshness
   precondition (none of the pattern var names appear free in any scrut)
   is what licenses progressively re-typing the rhs's under the
   accumulated env extensions. *)
lemma extract_binds_well_typed:
  assumes "list_all is_wildcard_like pats"
      and "length pats = length scruts"
      and "list_all2 (\<lambda>s ty. core_term_type env ghost s = Some ty) scruts colTys"
      and "length colTys = length scruts"
      and "dec_pattern_compatible_list env pats colTys"
      and "\<forall>s \<in> set scruts. dec_pattern_var_names_list pats |\<inter>| core_term_free_vars s = {||}"
  shows "bindlist_well_typed env ghost (extract_binds scruts pats)"
  using assms
proof (induction scruts pats arbitrary: env colTys rule: extract_binds.induct)
  case (1)
  thus ?case by simp
next
  case (2 s ss vr x ty ps)
  \<comment> \<open>DP_Var case\<close>
  from "2.prems"(3,4) obtain ty0 colRest where
    colTys_eq: "colTys = ty0 # colRest" and
    s_ty: "core_term_type env ghost s = Some ty0" and
    rest_typed: "list_all2 (\<lambda>s ty. core_term_type env ghost s = Some ty) ss colRest"
    by (cases colTys) auto
  from "2.prems"(5) colTys_eq have
    var_ty: "ty = ty0" and
    rest_compat: "dec_pattern_compatible_list env ps colRest"
    by auto
  from "2.prems"(1) have rest_wild: "list_all is_wildcard_like ps" by simp
  from "2.prems"(2) have len_eq: "length ps = length ss" by simp
  from "2.prems"(4) colTys_eq have len_rest: "length colRest = length ss" by simp

  let ?env' = "extend_env_with_bind env ghost x ty"

  \<comment> \<open>x doesn't appear in any of the rest's scruts (subset of original scrut set)\<close>
  from "2.prems"(6) have x_fresh:
    "\<forall>s' \<in> set ss. x |\<notin>| core_term_free_vars s'"
    by auto

  \<comment> \<open>The pattern names of ps don't appear in ss either (subset relationship)\<close>
  from "2.prems"(6) have ps_fresh:
    "\<forall>s' \<in> set ss. dec_pattern_var_names_list ps |\<inter>| core_term_free_vars s' = {||}"
    by auto

  \<comment> \<open>Lift each rest scrut's typing from env to ?env'\<close>
  have rest_typed': "list_all2 (\<lambda>s' ty'. core_term_type ?env' ghost s' = Some ty') ss colRest"
  proof -
    have "\<And>i. i < length ss \<Longrightarrow>
              core_term_type ?env' ghost (ss ! i) = Some (colRest ! i)"
    proof -
      fix i assume i_lt: "i < length ss"
      with rest_typed have orig: "core_term_type env ghost (ss ! i) = Some (colRest ! i)"
        by (auto simp: list_all2_conv_all_nth)
      have "ss ! i \<in> set ss" using i_lt by auto
      with x_fresh have x_not_in: "x |\<notin>| core_term_free_vars (ss ! i)" by auto
      from core_term_type_extend_env_with_bind_irrelevant[OF x_not_in orig]
      show "core_term_type ?env' ghost (ss ! i) = Some (colRest ! i)" .
    qed
    moreover have "length ss = length colRest" using len_rest by simp
    ultimately show ?thesis
      by (simp add: list_all2_conv_all_nth)
  qed

  \<comment> \<open>The compatibility predicate is preserved: it doesn't depend on TE_LocalVars/etc
       in the same way; but to be safe we don't actually need it here for the
       term-typing argument. The recursive call on extract_binds operates on the
       same pats=ps and scruts=ss, so we'll just propagate it.\<close>
  \<comment> \<open>Compatibility check is local to env. Since dec_pattern_compatible only uses
       env via TE_DataCtors which we don't modify, compatibility is preserved.\<close>
  have rest_compat': "dec_pattern_compatible_list ?env' ps colRest"
    using rest_compat dec_pattern_compatible_list_extend_env_with_bind by simp

  from "2.IH"[OF rest_wild len_eq rest_typed' len_rest rest_compat' ps_fresh]
  have rest_bl: "bindlist_well_typed ?env' ghost (extract_binds ss ps)" .

  have head_ok: "core_term_type env ghost s = Some ty"
    using s_ty var_ty by simp

  show ?case
    using head_ok rest_bl by simp
next
  case (3 s ss ps)
  \<comment> \<open>DP_Wildcard case\<close>
  from "3.prems"(3,4) obtain ty0 colRest where
    colTys_eq: "colTys = ty0 # colRest" and
    rest_typed: "list_all2 (\<lambda>s ty. core_term_type env ghost s = Some ty) ss colRest"
    by (cases colTys) auto
  from "3.prems"(5) colTys_eq have rest_compat: "dec_pattern_compatible_list env ps colRest"
    by auto
  from "3.prems"(1) have rest_wild: "list_all is_wildcard_like ps" by simp
  from "3.prems"(2) have len_eq: "length ps = length ss" by simp
  from "3.prems"(4) colTys_eq have len_rest: "length colRest = length ss" by simp
  from "3.prems"(6) have ps_fresh:
    "\<forall>s' \<in> set ss. dec_pattern_var_names_list ps |\<inter>| core_term_free_vars s' = {||}"
    by auto
  from "3.IH"[OF rest_wild len_eq rest_typed len_rest rest_compat ps_fresh]
  have rest_bl: "bindlist_well_typed env ghost (extract_binds ss ps)" .
  show ?case using rest_bl by simp
qed (auto)


subsection \<open>Scrutinee list manipulation\<close>

(* drop_at preserves length with one fewer element. *)
lemma length_drop_at:
  "c < length xs \<Longrightarrow> length (drop_at c xs) = length xs - 1"
  by (induction c xs rule: drop_at.induct) auto

(* replace_at preserves length. *)
lemma length_replace_at:
  "length (replace_at c y xs) = length xs"
  by (induction c y xs rule: replace_at.induct) auto

(* nth-list of drop_at: at i < c, identical; at i >= c, shifted by 1. *)
lemma nth_drop_at:
  "c < length xs \<Longrightarrow> i < length xs - 1
   \<Longrightarrow> drop_at c xs ! i = (if i < c then xs ! i else xs ! (Suc i))"
  by (induction c xs arbitrary: i rule: drop_at.induct) (auto simp: nth_Cons split: nat.splits)

(* nth-list of replace_at: at c, the new value; otherwise identical. *)
lemma nth_replace_at:
  "i < length xs
   \<Longrightarrow> replace_at c y xs ! i = (if i = c then (if c < length xs then y else xs ! i) else xs ! i)"
  by (induction c y xs arbitrary: i rule: replace_at.induct) (auto simp: nth_Cons split: nat.splits)

(* If a list of scrutinees typechecks against colTys, then dropping column c
   leaves a list that typechecks against colTys with column c dropped. *)
lemma list_all2_drop_at:
  assumes "list_all2 P xs ys"
      and "c < length xs"
  shows "list_all2 P (drop_at c xs) (drop_at c ys)"
proof -
  have len_eq: "length xs = length ys" using assms(1) by (simp add: list_all2_lengthD)
  have c_lt_ys: "c < length ys" using assms(2) len_eq by simp
  have len_drop: "length (drop_at c xs) = length (drop_at c ys)"
    using length_drop_at[OF assms(2)] length_drop_at[OF c_lt_ys] len_eq by simp
  show ?thesis
  proof (rule list_all2_all_nthI[OF len_drop])
    fix i assume i_lt: "i < length (drop_at c xs)"
    have i_bound: "i < length xs - 1"
      using i_lt length_drop_at[OF assms(2)] by simp
    have i_bound_ys: "i < length ys - 1"
      using i_bound len_eq by simp
    have step_xs: "drop_at c xs ! i = (if i < c then xs ! i else xs ! (Suc i))"
      using nth_drop_at[OF assms(2) i_bound] .
    have step_ys: "drop_at c ys ! i = (if i < c then ys ! i else ys ! (Suc i))"
      using nth_drop_at[OF c_lt_ys i_bound_ys] .
    show "P (drop_at c xs ! i) (drop_at c ys ! i)"
    proof (cases "i < c")
      case True
      have "i < length xs" using i_bound by simp
      with assms(1) have "P (xs ! i) (ys ! i)" by (simp add: list_all2_conv_all_nth)
      thus ?thesis using True step_xs step_ys by simp
    next
      case False
      have "Suc i < length xs" using i_bound by simp
      with assms(1) have "P (xs ! Suc i) (ys ! Suc i)" by (simp add: list_all2_conv_all_nth)
      thus ?thesis using False step_xs step_ys by simp
    qed
  qed
qed

(* If a list of scrutinees typechecks against colTys, then replacing column c
   with a new scrutinee that typechecks at the new type yields a typechecking
   list against the modified colTys. *)
lemma list_all2_replace_at:
  assumes "list_all2 P xs ys"
      and "c < length xs"
      and "P new_x new_y"
  shows "list_all2 P (replace_at c new_x xs) (replace_at c new_y ys)"
proof -
  have len_eq: "length xs = length ys" using assms(1) by (simp add: list_all2_lengthD)
  have c_lt_ys: "c < length ys" using assms(2) len_eq by simp
  have len_repl: "length (replace_at c new_x xs) = length (replace_at c new_y ys)"
    using length_replace_at[of c new_x xs] length_replace_at[of c new_y ys] len_eq by simp
  show ?thesis
  proof (rule list_all2_all_nthI[OF len_repl])
    fix i assume i_lt: "i < length (replace_at c new_x xs)"
    have i_bound: "i < length xs"
      using i_lt by (simp add: length_replace_at)
    have i_bound_ys: "i < length ys" using i_bound len_eq by simp
    have step_xs: "replace_at c new_x xs ! i =
                    (if i = c then (if c < length xs then new_x else xs ! i) else xs ! i)"
      using nth_replace_at[OF i_bound] .
    have step_ys: "replace_at c new_y ys ! i =
                    (if i = c then (if c < length ys then new_y else ys ! i) else ys ! i)"
      using nth_replace_at[OF i_bound_ys] .
    show "P (replace_at c new_x xs ! i) (replace_at c new_y ys ! i)"
    proof (cases "i = c")
      case True
      thus ?thesis using assms(2) c_lt_ys assms(3) step_xs step_ys by simp
    next
      case False
      have "P (xs ! i) (ys ! i)" using assms(1) i_bound by (simp add: list_all2_conv_all_nth)
      thus ?thesis using False step_xs step_ys by simp
    qed
  qed
qed


subsection \<open>dec_pattern_compatible_list under list manipulation\<close>

(* dec_pattern_compatible_list is structural in lockstep on the two lists.
   It can be re-expressed as a lockstep nth-condition. *)
lemma dec_pattern_compatible_list_iff:
  "dec_pattern_compatible_list env ps ts
   \<longleftrightarrow> length ps = length ts
       \<and> (\<forall>i < length ps. dec_pattern_compatible env (ps ! i) (ts ! i))"
proof (induction ps arbitrary: ts)
  case Nil
  thus ?case by (cases ts) auto
next
  case (Cons p ps)
  show ?case
  proof (cases ts)
    case Nil
    thus ?thesis by simp
  next
    case (Cons t ts')
    show ?thesis
    proof
      assume "dec_pattern_compatible_list env (p # ps) ts"
      with Cons have
        head: "dec_pattern_compatible env p t" and
        rest: "dec_pattern_compatible_list env ps ts'"
        by auto
      from rest Cons.IH have
        len: "length ps = length ts'" and
        nth: "\<forall>i < length ps. dec_pattern_compatible env (ps ! i) (ts' ! i)"
        by auto
      have len_full: "length (p # ps) = length ts" using Cons len by simp
      have nth_full: "\<forall>i < length (p # ps).
                        dec_pattern_compatible env ((p # ps) ! i) (ts ! i)"
      proof (intro allI impI)
        fix i assume "i < length (p # ps)"
        show "dec_pattern_compatible env ((p # ps) ! i) (ts ! i)"
          using head nth Cons \<open>i < length (p # ps)\<close>
          by (cases i) auto
      qed
      from len_full nth_full show "length (p # ps) = length ts \<and>
                                    (\<forall>i < length (p # ps).
                                      dec_pattern_compatible env ((p # ps) ! i) (ts ! i))"
        by simp
    next
      assume rhs: "length (p # ps) = length ts \<and>
                   (\<forall>i < length (p # ps). dec_pattern_compatible env ((p # ps) ! i) (ts ! i))"
      with Cons have len_eq: "length ps = length ts'" by simp
      from rhs have head: "dec_pattern_compatible env p (ts ! 0)" by auto
      have head_t: "ts ! 0 = t" using Cons by simp
      have rest_nth: "\<forall>i < length ps. dec_pattern_compatible env (ps ! i) (ts' ! i)"
      proof (intro allI impI)
        fix i assume "i < length ps"
        hence "Suc i < length (p # ps)" by simp
        with rhs have "dec_pattern_compatible env ((p # ps) ! Suc i) (ts ! Suc i)" by blast
        thus "dec_pattern_compatible env (ps ! i) (ts' ! i)"
          using Cons by simp
      qed
      from Cons.IH[of ts'] len_eq rest_nth
      have rest: "dec_pattern_compatible_list env ps ts'" by simp
      from head head_t rest Cons show "dec_pattern_compatible_list env (p # ps) ts" by simp
    qed
  qed
qed

(* drop_at preserves dec_pattern_compatible_list. *)
lemma dec_pattern_compatible_list_drop_at:
  assumes "dec_pattern_compatible_list env ps colTys"
      and "c < length ps"
      and "length colTys = length ps"
  shows "dec_pattern_compatible_list env (drop_at c ps) (drop_at c colTys)"
proof -
  from assms(1) have
    len_eq: "length ps = length colTys" and
    pointwise: "\<forall>i < length ps. dec_pattern_compatible env (ps ! i) (colTys ! i)"
    by (auto simp: dec_pattern_compatible_list_iff)
  have c_lt_colTys: "c < length colTys" using assms(2,3) by simp
  have len_drop: "length (drop_at c ps) = length (drop_at c colTys)"
    using length_drop_at[OF assms(2)] length_drop_at[OF c_lt_colTys] len_eq by simp
  have new_pointwise: "\<forall>i < length (drop_at c ps).
                          dec_pattern_compatible env (drop_at c ps ! i) (drop_at c colTys ! i)"
  proof (intro allI impI)
    fix i assume i_lt: "i < length (drop_at c ps)"
    have i_bound: "i < length ps - 1" using i_lt length_drop_at[OF assms(2)] by simp
    have i_bound_ct: "i < length colTys - 1" using i_bound len_eq by simp
    have step_ps: "drop_at c ps ! i = (if i < c then ps ! i else ps ! (Suc i))"
      using nth_drop_at[OF assms(2) i_bound] .
    have step_ct: "drop_at c colTys ! i = (if i < c then colTys ! i else colTys ! (Suc i))"
      using nth_drop_at[OF c_lt_colTys i_bound_ct] .
    show "dec_pattern_compatible env (drop_at c ps ! i) (drop_at c colTys ! i)"
    proof (cases "i < c")
      case True
      have "i < length ps" using i_bound by simp
      with pointwise have "dec_pattern_compatible env (ps ! i) (colTys ! i)" by simp
      thus ?thesis using True step_ps step_ct by simp
    next
      case False
      have "Suc i < length ps" using i_bound by simp
      with pointwise have "dec_pattern_compatible env (ps ! Suc i) (colTys ! Suc i)" by simp
      thus ?thesis using False step_ps step_ct by simp
    qed
  qed
  show ?thesis using len_drop new_pointwise by (auto simp: dec_pattern_compatible_list_iff)
qed

(* replace_at preserves dec_pattern_compatible_list when the new pattern is
   compatible with the column type at c. *)
lemma dec_pattern_compatible_list_replace_at:
  assumes "dec_pattern_compatible_list env ps colTys"
      and "c < length ps"
      and "length colTys = length ps"
      and "dec_pattern_compatible env new_p (colTys ! c)"
  shows "dec_pattern_compatible_list env (replace_at c new_p ps) colTys"
proof -
  from assms(1) have
    pointwise: "\<forall>i < length ps. dec_pattern_compatible env (ps ! i) (colTys ! i)"
    by (auto simp: dec_pattern_compatible_list_iff)
  have len_repl: "length (replace_at c new_p ps) = length colTys"
    using length_replace_at[of c new_p ps] assms(3) by simp
  have new_pointwise:
    "\<forall>i < length (replace_at c new_p ps).
       dec_pattern_compatible env (replace_at c new_p ps ! i) (colTys ! i)"
  proof (intro allI impI)
    fix i assume i_lt: "i < length (replace_at c new_p ps)"
    have i_bound: "i < length ps" using i_lt by (simp add: length_replace_at)
    have step: "replace_at c new_p ps ! i =
                  (if i = c then (if c < length ps then new_p else ps ! i) else ps ! i)"
      using nth_replace_at[OF i_bound] .
    show "dec_pattern_compatible env (replace_at c new_p ps ! i) (colTys ! i)"
    proof (cases "i = c")
      case True
      thus ?thesis using assms(2,4) step by simp
    next
      case False
      with pointwise i_bound have "dec_pattern_compatible env (ps ! i) (colTys ! i)" by simp
      thus ?thesis using False step by simp
    qed
  qed
  show ?thesis using len_repl new_pointwise by (auto simp: dec_pattern_compatible_list_iff)
qed


subsection \<open>BindList append and extension\<close>

(* Extending env by bs1 @ bs2 is the same as extending by bs1 then bs2. *)
lemma extend_env_with_bindlist_append:
  "extend_env_with_bindlist env ghost (bs1 @ bs2)
   = extend_env_with_bindlist (extend_env_with_bindlist env ghost bs1) ghost bs2"
  by (induction bs1 arbitrary: env) (auto split: prod.splits)

(* Well-typedness of an appended bindlist: bs1 well-typed in env, and bs2
   well-typed in env extended by bs1. *)
lemma bindlist_well_typed_append:
  "bindlist_well_typed env ghost (bs1 @ bs2)
   = (bindlist_well_typed env ghost bs1
      \<and> bindlist_well_typed (extend_env_with_bindlist env ghost bs1) ghost bs2)"
  by (induction bs1 arbitrary: env) (auto split: prod.splits)


subsection \<open>Lifting core_term_type through bindlist extension\<close>

(* If a term doesn't reference any of a bindlist's bind-names, then its type
   is unchanged when env is extended by the entire bindlist.
   Iteratively applies core_term_type_extend_env_with_bind_irrelevant. *)
lemma core_term_type_extend_env_with_bindlist_irrelevant:
  assumes "fset_of_list (map (\<lambda>(_, x, _, _). x) binds) |\<inter>| core_term_free_vars tm = {||}"
      and "core_term_type env ghost tm = Some ty"
  shows "core_term_type (extend_env_with_bindlist env ghost binds) ghost tm = Some ty"
  using assms
proof (induction binds arbitrary: env)
  case Nil
  thus ?case by simp
next
  case (Cons b rest)
  obtain vr x bty rhs where b_eq: "b = (vr, x, bty, rhs)"
    by (cases b) auto
  from Cons.prems(1) b_eq have
    x_fresh: "x |\<notin>| core_term_free_vars tm" and
    rest_fresh: "fset_of_list (map (\<lambda>(_, x, _, _). x) rest) |\<inter>| core_term_free_vars tm = {||}"
    by auto
  let ?env' = "extend_env_with_bind env ghost x bty"
  have step1: "core_term_type ?env' ghost tm = Some ty"
    using core_term_type_extend_env_with_bind_irrelevant[OF x_fresh Cons.prems(2)] .
  from Cons.IH[OF rest_fresh step1]
  have "core_term_type (extend_env_with_bindlist ?env' ghost rest) ghost tm = Some ty" .
  thus ?case using b_eq by simp
qed


subsection \<open>Commutativity of distinct env extensions\<close>

(* Two extend_env_with_bind operations with distinct names commute, in the
   sense that the resulting envs differ only in invisible bookkeeping —
   specifically TE_LocalVars and TE_GhostLocals and TE_ConstLocals all
   end up with the same key-to-value maps. *)
lemma extend_env_with_bind_swap:
  assumes "x \<noteq> y"
  shows "extend_env_with_bind (extend_env_with_bind env ghost x tx) ghost y ty
       = extend_env_with_bind (extend_env_with_bind env ghost y ty) ghost x tx"
proof -
  have fmupd_swap: "fmupd x tx (fmupd y ty m) = fmupd y ty (fmupd x tx m)" for m
    using assms by (auto intro: fmap_ext)
  have fminus_swap: "(S |-| {|x|}) |-| {|y|} = (S |-| {|y|}) |-| {|x|}" for S
    by (auto intro: fset_eqI)
  show ?thesis
    unfolding extend_env_with_bind_def
    using assms fmupd_swap fminus_swap
    by (cases ghost) (auto simp: finsert_commute)
qed

(* Commuting the order of bindlist and pattern-var extensions under the
   condition that the names involved are disjoint. *)
lemma extend_env_with_bindlist_extend_env_with_bind_swap:
  assumes "x \<notin> set (map (\<lambda>(_, n, _, _). n) binds)"
  shows "extend_env_with_bindlist (extend_env_with_bind env ghost x ty) ghost binds
       = extend_env_with_bind (extend_env_with_bindlist env ghost binds) ghost x ty"
  using assms
proof (induction binds arbitrary: env)
  case Nil
  thus ?case by simp
next
  case (Cons b rest)
  obtain vr y bty rhs where b_eq: "b = (vr, y, bty, rhs)" by (cases b) auto
  from Cons.prems b_eq have x_neq_y: "x \<noteq> y" by auto
  from Cons.prems b_eq have x_fresh_rest: "x \<notin> set (map (\<lambda>(_, n, _, _). n) rest)"
    by force
  have "extend_env_with_bindlist (extend_env_with_bind env ghost x ty) ghost (b # rest)
        = extend_env_with_bindlist
            (extend_env_with_bind (extend_env_with_bind env ghost x ty) ghost y bty)
            ghost rest"
    using b_eq by simp
  also have "\<dots> = extend_env_with_bindlist
                    (extend_env_with_bind (extend_env_with_bind env ghost y bty) ghost x ty)
                    ghost rest"
    using extend_env_with_bind_swap[OF x_neq_y] by simp
  also have "\<dots> = extend_env_with_bind
                    (extend_env_with_bindlist (extend_env_with_bind env ghost y bty) ghost rest)
                    ghost x ty"
    using Cons.IH[OF x_fresh_rest] .
  also have "\<dots> = extend_env_with_bind (extend_env_with_bindlist env ghost (b # rest)) ghost x ty"
    using b_eq by simp
  finally show ?case .
qed


subsection \<open>Unified flat-binding extension\<close>

(* A flat list of (VarOrRef, name, type) triples extending an env. Both
   bindlists and pattern-var lists project to this shape, so we can prove
   the commutativity lemma once at this level. *)
definition extend_env_flat ::
  "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> (VarOrRef \<times> string \<times> CoreType) list \<Rightarrow> CoreTyEnv" where
  "extend_env_flat env ghost trips =
     foldr (\<lambda>(_, x, ty) e. extend_env_with_bind e ghost x ty) trips env"

lemma extend_env_flat_Nil [simp]:
  "extend_env_flat env ghost [] = env"
  by (simp add: extend_env_flat_def)

lemma extend_env_flat_Cons [simp]:
  "extend_env_flat env ghost ((vr, x, ty) # rest)
   = extend_env_with_bind (extend_env_flat env ghost rest) ghost x ty"
  by (simp add: extend_env_flat_def)

lemma extend_env_flat_append:
  "extend_env_flat env ghost (xs @ ys)
   = extend_env_flat (extend_env_flat env ghost ys) ghost xs"
  by (induction xs) (auto split: prod.splits)

(* Names of a flat-binding list. *)
definition flat_binding_names :: "(VarOrRef \<times> string \<times> CoreType) list \<Rightarrow> string fset" where
  "flat_binding_names trips = fset_of_list (map (\<lambda>(_, x, _). x) trips)"

(* extend_env_with_pattern_vars reduces to extend_env_flat. *)
lemma extend_env_with_pattern_vars_eq_flat:
  "extend_env_with_pattern_vars env ghost ps
   = extend_env_flat env ghost (dec_pattern_var_bindings_list ps)"
  by (simp add: extend_env_with_pattern_vars_def extend_env_flat_def)

(* Cons-step for extend_env_with_pattern_vars: peels off the head pattern. *)
lemma extend_env_with_pattern_vars_Cons:
  "extend_env_with_pattern_vars env ghost (p # ps)
   = foldr (\<lambda>(_, x, ty) e. extend_env_with_bind e ghost x ty)
           (dec_pattern_var_bindings p) (extend_env_with_pattern_vars env ghost ps)"
  unfolding extend_env_with_pattern_vars_def
  by simp

(* Names introduced by extend_env_with_pattern_vars equals dec_pattern_var_names_list. *)
lemma flat_binding_names_dec_pattern_var_bindings:
  "flat_binding_names (dec_pattern_var_bindings p) = dec_pattern_var_names p"
and flat_binding_names_dec_pattern_var_bindings_list:
  "flat_binding_names (dec_pattern_var_bindings_list ps) = dec_pattern_var_names_list ps"
proof (induction p and ps rule: dec_pattern_var_bindings_dec_pattern_var_bindings_list.induct)
qed (auto simp: flat_binding_names_def)


subsection \<open>Commutativity of distinct env extensions (continued)\<close>

(* Pulling a single bind past extend_env_flat when the name doesn't appear
   among the flat-list's names. *)
lemma extend_env_flat_extend_env_with_bind_swap:
  assumes "x |\<notin>| flat_binding_names trips"
  shows "extend_env_flat (extend_env_with_bind env ghost x ty) ghost trips
       = extend_env_with_bind (extend_env_flat env ghost trips) ghost x ty"
  using assms
proof (induction trips)
  case Nil
  thus ?case by simp
next
  case (Cons t rest)
  obtain vr y bty where t_eq: "t = (vr, y, bty)" by (cases t) auto
  from Cons.prems t_eq have y_neq_x: "y \<noteq> x" by (auto simp: flat_binding_names_def)
  from Cons.prems t_eq have rest_fresh: "x |\<notin>| flat_binding_names rest"
    by (auto simp: flat_binding_names_def)
  have "extend_env_flat (extend_env_with_bind env ghost x ty) ghost (t # rest)
        = extend_env_with_bind
            (extend_env_flat (extend_env_with_bind env ghost x ty) ghost rest) ghost y bty"
    using t_eq by simp
  also have "\<dots> = extend_env_with_bind
                    (extend_env_with_bind (extend_env_flat env ghost rest) ghost x ty)
                    ghost y bty"
    using Cons.IH[OF rest_fresh] by simp
  also have "\<dots> = extend_env_with_bind
                    (extend_env_with_bind (extend_env_flat env ghost rest) ghost y bty)
                    ghost x ty"
    using extend_env_with_bind_swap[OF y_neq_x[symmetric]] by simp
  also have "\<dots> = extend_env_with_bind (extend_env_flat env ghost (t # rest)) ghost x ty"
    using t_eq by simp
  finally show ?case .
qed

(* Specialisation: extend_env_with_pattern_vars commutes with extend_env_with_bind
   when the bind's name doesn't appear in the pattern-list's DP_Var names. *)
lemma extend_env_with_pattern_vars_extend_env_with_bind_swap:
  assumes "x |\<notin>| dec_pattern_var_names_list ps"
  shows "extend_env_with_pattern_vars (extend_env_with_bind env ghost x ty) ghost ps
       = extend_env_with_bind (extend_env_with_pattern_vars env ghost ps) ghost x ty"
proof -
  have "x |\<notin>| flat_binding_names (dec_pattern_var_bindings_list ps)"
    using assms flat_binding_names_dec_pattern_var_bindings_list by simp
  thus ?thesis
    using extend_env_flat_extend_env_with_bind_swap
    by (simp add: extend_env_with_pattern_vars_eq_flat)
qed


subsection \<open>Decomposing pattern-var bindings under list manipulation\<close>

(* When ps ! c = DP_Var vr x ty, the flat bindings of drop_at c ps are the
   flat bindings of ps with that single (vr, x, ty) triple removed.
   We prove the env-equivalence directly by induction on c. *)
lemma extend_env_with_pattern_vars_drop_at_DP_Var:
  assumes "c < length ps"
      and "ps ! c = DP_Var vr x ty"
      and "pattern_var_names_distinct ps"
  shows "extend_env_with_bind (extend_env_with_pattern_vars env ghost (drop_at c ps)) ghost x ty
       = extend_env_with_pattern_vars env ghost ps"
  using assms
proof (induction c ps arbitrary: env rule: drop_at.induct)
  case (1 uu)  \<comment> \<open>empty list\<close>
  thus ?case by simp
next
  case (2 p ps)  \<comment> \<open>c = 0\<close>
  from "2.prems"(2) have p_eq: "p = DP_Var vr x ty" by simp
  have lhs_step: "extend_env_with_pattern_vars env ghost (drop_at 0 (p # ps))
                  = extend_env_with_pattern_vars env ghost ps"
    by simp
  have rhs_step: "extend_env_with_pattern_vars env ghost (p # ps)
                  = extend_env_with_bind (extend_env_with_pattern_vars env ghost ps) ghost x ty"
    using p_eq by (simp add: extend_env_with_pattern_vars_def)
  show ?case using lhs_step rhs_step by simp
next
  case (3 c p ps)  \<comment> \<open>c = Suc c', p :: DecPattern\<close>
  have c_lt: "c < length ps" using "3.prems"(1) by simp
  have nth_eq: "ps ! c = DP_Var vr x ty" using "3.prems"(2) by simp
  from "3.prems"(3) have rest_distinct: "pattern_var_names_distinct ps"
    by (simp add: pattern_var_names_distinct_def)
  from "3.IH"[OF c_lt nth_eq rest_distinct]
  have IH_eq: "\<And>e. extend_env_with_bind (extend_env_with_pattern_vars e ghost (drop_at c ps)) ghost x ty
              = extend_env_with_pattern_vars e ghost ps"
    by simp

  \<comment> \<open>x is not in dec_pattern_var_names p, since (vr,x,ty) is in ps's bindings (at col c)
       and pattern_var_names_distinct (p#ps) ensures p's names are disjoint from ps's.\<close>
  have x_in_ps: "x |\<in>| dec_pattern_var_names_list ps"
  proof -
    have subset_lemma: "\<And>(p::DecPattern) ps'. p \<in> set ps' \<Longrightarrow>
                        set (dec_pattern_var_bindings p) \<subseteq> set (dec_pattern_var_bindings_list ps')"
    proof -
      fix p :: DecPattern fix ps' assume "p \<in> set ps'"
      thus "set (dec_pattern_var_bindings p) \<subseteq> set (dec_pattern_var_bindings_list ps')"
        by (induction ps') auto
    qed
    have "(vr, x, ty) \<in> set (dec_pattern_var_bindings (ps ! c))"
      using nth_eq by simp
    moreover have "ps ! c \<in> set ps" using c_lt by simp
    ultimately have in_bindings: "(vr, x, ty) \<in> set (dec_pattern_var_bindings_list ps)"
      using subset_lemma by blast
    have "x |\<in>| flat_binding_names (dec_pattern_var_bindings_list ps)"
      unfolding flat_binding_names_def using in_bindings
      by (force simp: fset_of_list_elem)
    thus ?thesis using flat_binding_names_dec_pattern_var_bindings_list by simp
  qed
  have x_not_in_p: "x |\<notin>| dec_pattern_var_names p"
  proof
    assume x_in_p: "x |\<in>| dec_pattern_var_names p"
    have "x |\<in>| flat_binding_names (dec_pattern_var_bindings p)"
      using x_in_p flat_binding_names_dec_pattern_var_bindings by simp
    then obtain vr' ty' where vr_in: "(vr', x, ty') \<in> set (dec_pattern_var_bindings p)"
      by (auto simp: flat_binding_names_def fset_of_list_elem)
    have "x |\<in>| flat_binding_names (dec_pattern_var_bindings_list ps)"
      using x_in_ps flat_binding_names_dec_pattern_var_bindings_list by simp
    then obtain vr'' ty'' where vr_in_ps: "(vr'', x, ty'') \<in> set (dec_pattern_var_bindings_list ps)"
      by (auto simp: flat_binding_names_def fset_of_list_elem)
    \<comment> \<open>x appears in both p's name set and ps's name set, so the combined list has a duplicate.\<close>
    have x_in_p_names:
      "x \<in> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings p))"
      using vr_in by force
    have x_in_ps_names:
      "x \<in> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps))"
      using vr_in_ps by force
    have inter_nonempty:
      "set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings p))
         \<inter> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps)) \<noteq> {}"
      using x_in_p_names x_in_ps_names by blast
    have "\<not> distinct (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings p)
                       @ map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps))"
      using inter_nonempty by auto
    hence "\<not> distinct (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list (p # ps)))"
      by simp
    with "3.prems"(3) show False
      by (simp add: pattern_var_names_distinct_def)
  qed

  have lhs: "extend_env_with_bind
                (extend_env_with_pattern_vars env ghost (drop_at (Suc c) (p # ps))) ghost x ty
             = extend_env_with_bind
                 (extend_env_with_pattern_vars env ghost (p # drop_at c ps)) ghost x ty"
    by simp
  also have "\<dots> = extend_env_with_bind
                    (foldr (\<lambda>(_, n, t) e'. extend_env_with_bind e' ghost n t)
                           (dec_pattern_var_bindings p)
                           (extend_env_with_pattern_vars env ghost (drop_at c ps)))
                    ghost x ty"
    by (simp add: extend_env_with_pattern_vars_Cons)
  also have "\<dots> = foldr (\<lambda>(_, n, t) e'. extend_env_with_bind e' ghost n t)
                         (dec_pattern_var_bindings p)
                         (extend_env_with_bind
                            (extend_env_with_pattern_vars env ghost (drop_at c ps)) ghost x ty)"
  proof -
    have "x |\<notin>| flat_binding_names (dec_pattern_var_bindings p)"
      using x_not_in_p flat_binding_names_dec_pattern_var_bindings by simp
    thus ?thesis
      using extend_env_flat_extend_env_with_bind_swap[where trips="dec_pattern_var_bindings p"]
      by (simp add: extend_env_flat_def)
  qed
  also have "\<dots> = foldr (\<lambda>(_, n, t) e'. extend_env_with_bind e' ghost n t)
                         (dec_pattern_var_bindings p)
                         (extend_env_with_pattern_vars env ghost ps)"
    using IH_eq by simp
  also have "\<dots> = extend_env_with_pattern_vars env ghost (p # ps)"
    by (simp add: extend_env_with_pattern_vars_Cons)
  finally show ?case .
qed

(* When ps ! c = DP_Var vr x ty and the row's pattern-var names are distinct,
   x doesn't appear in drop_at c ps's pattern-var names. *)
lemma DP_Var_name_not_in_drop_at:
  assumes "c < length ps"
      and "ps ! c = DP_Var vr x ty"
      and "pattern_var_names_distinct ps"
  shows "x |\<notin>| dec_pattern_var_names_list (drop_at c ps)"
  using assms
proof (induction c ps rule: drop_at.induct)
  case 1 thus ?case by simp
next
  case (2 p ps)
  \<comment> \<open>c = 0: drop_at 0 (p # ps) = ps.
       p = DP_Var vr x ty, and distinct says x not in rest.\<close>
  from "2.prems"(2) have p_eq: "p = DP_Var vr x ty" by simp
  from "2.prems"(3) p_eq have
    "distinct (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list (DP_Var vr x ty # ps)))"
    by (simp add: pattern_var_names_distinct_def)
  hence "x \<notin> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps))"
    by simp
  hence "x |\<notin>| flat_binding_names (dec_pattern_var_bindings_list ps)"
    by (simp add: flat_binding_names_def fset_of_list.rep_eq)
  hence "x |\<notin>| dec_pattern_var_names_list ps"
    using flat_binding_names_dec_pattern_var_bindings_list by simp
  thus ?case by simp
next
  case (3 c p ps)
  have c_lt: "c < length ps" using "3.prems"(1) by simp
  have nth_eq: "ps ! c = DP_Var vr x ty" using "3.prems"(2) by simp
  from "3.prems"(3) have rest_distinct: "pattern_var_names_distinct ps"
    by (simp add: pattern_var_names_distinct_def)
  have IH_step: "x |\<notin>| dec_pattern_var_names_list (drop_at c ps)"
    using "3.IH"[OF c_lt nth_eq rest_distinct] .
  \<comment> \<open>x not in p's pattern-var names: x is in (Suc c)-th column (within ps),
       and distinctness across the whole row.\<close>
  have x_not_in_p: "x |\<notin>| dec_pattern_var_names p"
  proof
    assume x_in_p: "x |\<in>| dec_pattern_var_names p"
    \<comment> \<open>x is also in dec_pattern_var_names_list ps, since it's in DP_Var at column c.\<close>
    have subset_lemma: "\<And>(p::DecPattern) ps'. p \<in> set ps' \<Longrightarrow>
                        set (dec_pattern_var_bindings p)
                          \<subseteq> set (dec_pattern_var_bindings_list ps')"
    proof -
      fix p :: DecPattern fix ps' assume "p \<in> set ps'"
      thus "set (dec_pattern_var_bindings p)
              \<subseteq> set (dec_pattern_var_bindings_list ps')"
        by (induction ps') auto
    qed
    have "(vr, x, ty) \<in> set (dec_pattern_var_bindings (ps ! c))"
      using nth_eq by simp
    moreover have "ps ! c \<in> set ps" using c_lt by simp
    ultimately have x_in_ps_bindings:
      "(vr, x, ty) \<in> set (dec_pattern_var_bindings_list ps)"
      using subset_lemma by blast
    have "x |\<in>| flat_binding_names (dec_pattern_var_bindings p)"
      using x_in_p flat_binding_names_dec_pattern_var_bindings by simp
    then obtain vr' ty' where
      vr_in_p: "(vr', x, ty') \<in> set (dec_pattern_var_bindings p)"
      by (auto simp: flat_binding_names_def fset_of_list_elem)
    \<comment> \<open>So x appears in both p and ps's bindings, contradicting distinctness.\<close>
    have x_in_p_names: "x \<in> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings p))"
      using vr_in_p by force
    have x_in_ps_names:
      "x \<in> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps))"
      using x_in_ps_bindings by force
    have inter_nonempty:
      "set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings p))
         \<inter> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps)) \<noteq> {}"
      using x_in_p_names x_in_ps_names by blast
    have "\<not> distinct (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings p)
                        @ map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps))"
      using inter_nonempty by auto
    hence "\<not> distinct (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list (p # ps)))"
      by simp
    with "3.prems"(3) show False by (simp add: pattern_var_names_distinct_def)
  qed
  show ?case
    using IH_step x_not_in_p by simp
qed


subsection \<open>Pattern-var-distinctness under list manipulation\<close>

(* dec_pattern_var_bindings_list of drop_at c ps is a sublist of the original. *)
lemma dec_pattern_var_bindings_list_drop_at_subset:
  "set (dec_pattern_var_bindings_list (drop_at c ps))
   \<subseteq> set (dec_pattern_var_bindings_list ps)"
proof (induction c ps rule: drop_at.induct)
qed auto

(* drop_at preserves the distinctness invariant on pattern-var names. *)
lemma pattern_var_names_distinct_drop_at:
  "pattern_var_names_distinct ps
   \<Longrightarrow> pattern_var_names_distinct (drop_at c ps)"
proof (induction c ps rule: drop_at.induct)
  case 1 thus ?case by simp
next
  case (2 p ps)
  thus ?case by (auto simp: pattern_var_names_distinct_def)
next
  case (3 c p ps)
  from "3.prems" have rest_distinct: "pattern_var_names_distinct ps"
    by (auto simp: pattern_var_names_distinct_def)
  from "3.IH"[OF rest_distinct]
  have IH: "pattern_var_names_distinct (drop_at c ps)" .
  \<comment> \<open>p's names are disjoint from drop_at c ps's names (since drop_at c ps subset ps).\<close>
  have inter:
    "set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings p))
       \<inter> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list (drop_at c ps))) = {}"
  proof -
    have ps_subset: "set (dec_pattern_var_bindings_list (drop_at c ps))
                       \<subseteq> set (dec_pattern_var_bindings_list ps)"
      using dec_pattern_var_bindings_list_drop_at_subset .
    hence names_subset:
      "set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list (drop_at c ps)))
         \<subseteq> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps))"
      by force
    from "3.prems" have
      "set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings p))
         \<inter> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps)) = {}"
      by (auto simp: pattern_var_names_distinct_def)
    with names_subset show ?thesis by blast
  qed
  have p_distinct:
    "distinct (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings p))"
    using "3.prems" by (auto simp: pattern_var_names_distinct_def)
  have rest_drop_distinct:
    "distinct (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list (drop_at c ps)))"
    using IH by (simp add: pattern_var_names_distinct_def)
  show ?case
    using inter p_distinct rest_drop_distinct
    by (auto simp: pattern_var_names_distinct_def)
qed


subsection \<open>replace_at: pattern-var bindings and distinctness\<close>

(* When replace_at c new_p ps replaces the column-c pattern with one whose
   pattern-var bindings equal those of (ps ! c), the row's overall bindings
   list is unchanged. Used in the DP_Variant (Some pat) variant case where
   new_p = pat and (ps ! c) = DP_Variant _ (Some pat) — both have the same
   var bindings. *)
lemma dec_pattern_var_bindings_list_replace_at_same_bindings:
  assumes "c < length ps"
      and "dec_pattern_var_bindings new_p = dec_pattern_var_bindings (ps ! c)"
  shows "dec_pattern_var_bindings_list (replace_at c new_p ps)
         = dec_pattern_var_bindings_list ps"
  using assms
proof (induction c new_p ps rule: replace_at.induct)
  case (1 uu uv) thus ?case by simp
next
  case (2 y x xs) thus ?case by simp
next
  case (3 c y x xs) thus ?case by simp
qed

(* As a corollary, distinctness is preserved when the bindings list itself is
   preserved (the equal-bindings case). *)
lemma pattern_var_names_distinct_replace_at_same_bindings:
  assumes "c < length ps"
      and "pattern_var_names_distinct ps"
      and "dec_pattern_var_bindings new_p = dec_pattern_var_bindings (ps ! c)"
  shows "pattern_var_names_distinct (replace_at c new_p ps)"
  using assms dec_pattern_var_bindings_list_replace_at_same_bindings[OF assms(1,3)]
  by (simp add: pattern_var_names_distinct_def)

(* When replace_at c DP_Wildcard ps replaces the column-c pattern with
   DP_Wildcard and (ps ! c) had no var bindings (e.g. DP_Wildcard already),
   the row's overall bindings list is unchanged. *)
lemma dec_pattern_var_bindings_list_replace_at_DP_Wildcard_no_binds:
  assumes "c < length ps"
      and "dec_pattern_var_bindings (ps ! c) = []"
  shows "dec_pattern_var_bindings_list (replace_at c DP_Wildcard ps)
         = dec_pattern_var_bindings_list ps"
  using assms by (auto intro: dec_pattern_var_bindings_list_replace_at_same_bindings)

(* Pattern-var names of replace_at c DP_Wildcard ps when (ps!c) = DP_Var:
   it equals the names of drop_at c ps (the DP_Var binding is removed,
   no new bindings are introduced). *)
lemma dec_pattern_var_bindings_list_replace_at_DP_Wildcard_for_DP_Var:
  assumes "c < length ps"
      and "ps ! c = DP_Var vr x ty"
  shows "dec_pattern_var_bindings_list (replace_at c DP_Wildcard ps)
         = dec_pattern_var_bindings_list (drop_at c ps)"
  using assms
proof (induction c ps rule: drop_at.induct)
  case 1 thus ?case by simp
next
  case (2 p ps)
  from "2.prems"(2) have p_eq: "p = DP_Var vr x ty" by simp
  thus ?case by simp
next
  case (3 c p ps)
  have c_lt: "c < length ps" using "3.prems"(1) by simp
  have nth_eq: "ps ! c = DP_Var vr x ty" using "3.prems"(2) by simp
  from "3.IH"[OF c_lt nth_eq]
  have IH: "dec_pattern_var_bindings_list (replace_at c DP_Wildcard ps)
             = dec_pattern_var_bindings_list (drop_at c ps)" .
  show ?case using IH by simp
qed

(* Distinctness is preserved by replace_at c DP_Wildcard when (ps!c) = DP_Var.
   We prove this by reducing to the analogous drop_at distinctness lemma. *)
lemma pattern_var_names_distinct_replace_at_DP_Wildcard_for_DP_Var:
  assumes "c < length ps"
      and "ps ! c = DP_Var vr x ty"
      and "pattern_var_names_distinct ps"
  shows "pattern_var_names_distinct (replace_at c DP_Wildcard ps)"
  unfolding pattern_var_names_distinct_def
  using dec_pattern_var_bindings_list_replace_at_DP_Wildcard_for_DP_Var[OF assms(1,2)]
        pattern_var_names_distinct_drop_at[OF assms(3), of c]
  by (simp add: pattern_var_names_distinct_def)

subsection \<open>splice_at: length, nth, list_all2\<close>

lemma length_splice_at:
  "c < length xs \<Longrightarrow> length (splice_at c ys xs) = length xs - 1 + length ys"
  by (induction c ys xs rule: splice_at.induct) auto

lemma nth_splice_at:
  assumes "c < length xs"
      and "i < length xs - 1 + length ys"
  shows "splice_at c ys xs ! i =
           (if i < c then xs ! i
            else if i < c + length ys then ys ! (i - c)
            else xs ! (i - length ys + 1))"
  using assms
proof (induction c ys xs arbitrary: i rule: splice_at.induct)
  case (1 uu uv) thus ?case by simp
next
  case (2 ys x xs)
  thus ?case by (simp add: nth_append nth_Cons split: nat.splits)
next
  case (3 c ys x xs)
  show ?case
  proof (cases i)
    case 0 thus ?thesis by simp
  next
    case (Suc i')
    have c_lt: "c < length xs" using "3.prems"(1) by simp
    have i'_bound: "i' < length xs - 1 + length ys" using "3.prems"(2) Suc by simp
    have IH: "splice_at c ys xs ! i' =
                (if i' < c then xs ! i'
                 else if i' < c + length ys then ys ! (i' - c)
                 else xs ! (i' - length ys + 1))"
      using "3.IH"[OF c_lt i'_bound] .
    \<comment> \<open>For the else branch, we need Suc i' - length ys = Suc (i' - length ys),
         which holds because i' \<ge> c + length ys \<ge> length ys.\<close>
    show ?thesis
    proof (cases "i' < c")
      case True thus ?thesis using Suc IH by simp
    next
      case ge_c: False
      show ?thesis
      proof (cases "i' < c + length ys")
        case True thus ?thesis using Suc IH ge_c by simp
      next
        case False
        have idx_ge: "i' \<ge> length ys" using False by simp
        hence "Suc i' - length ys = Suc (i' - length ys)" by simp
        thus ?thesis using Suc IH ge_c False by simp
      qed
    qed
  qed
qed

(* list_all2 transports through parallel splice_at. *)
lemma list_all2_splice_at:
  assumes "list_all2 P xs ys"
      and "c < length xs"
      and "list_all2 P new_xs new_ys"
  shows "list_all2 P (splice_at c new_xs xs) (splice_at c new_ys ys)"
proof -
  have len_eq: "length xs = length ys" using assms(1) by (simp add: list_all2_lengthD)
  have c_lt_ys: "c < length ys" using assms(2) len_eq by simp
  have len_new: "length new_xs = length new_ys" using assms(3) by (simp add: list_all2_lengthD)
  have len_splice: "length (splice_at c new_xs xs) = length (splice_at c new_ys ys)"
    using length_splice_at[OF assms(2)] length_splice_at[OF c_lt_ys]
          len_eq len_new by simp
  show ?thesis
  proof (rule list_all2_all_nthI[OF len_splice])
    fix i assume i_lt: "i < length (splice_at c new_xs xs)"
    have i_bound: "i < length xs - 1 + length new_xs"
      using i_lt length_splice_at[OF assms(2)] by simp
    have i_bound_ys: "i < length ys - 1 + length new_ys"
      using i_bound len_eq len_new by simp
    have step_xs: "splice_at c new_xs xs ! i =
                    (if i < c then xs ! i
                     else if i < c + length new_xs then new_xs ! (i - c)
                     else xs ! (i - length new_xs + 1))"
      using nth_splice_at[OF assms(2) i_bound] .
    have step_ys: "splice_at c new_ys ys ! i =
                    (if i < c then ys ! i
                     else if i < c + length new_ys then new_ys ! (i - c)
                     else ys ! (i - length new_ys + 1))"
      using nth_splice_at[OF c_lt_ys i_bound_ys] .
    show "P (splice_at c new_xs xs ! i) (splice_at c new_ys ys ! i)"
    proof (cases "i < c")
      case True
      have "i < length xs" using assms(2) True by simp
      with assms(1) have "P (xs ! i) (ys ! i)" by (simp add: list_all2_conv_all_nth)
      thus ?thesis using True step_xs step_ys by simp
    next
      case ge_c: False
      show ?thesis
      proof (cases "i < c + length new_xs")
        case True
        have idx_lt: "i - c < length new_xs" using ge_c True by simp
        with assms(3) have "P (new_xs ! (i - c)) (new_ys ! (i - c))"
          by (simp add: list_all2_conv_all_nth)
        thus ?thesis using ge_c True step_xs step_ys len_new by simp
      next
        case False
        have past: "\<not> i < c + length new_xs" using False .
        have past_ys: "\<not> i < c + length new_ys" using False len_new by simp
        have idx_xs_lt: "i - length new_xs + 1 < length xs"
          using i_bound past by simp
        with assms(1) have "P (xs ! (i - length new_xs + 1)) (ys ! (i - length new_xs + 1))"
          by (simp add: list_all2_conv_all_nth)
        thus ?thesis using ge_c past past_ys step_xs step_ys len_new by simp
      qed
    qed
  qed
qed


subsection \<open>splice_at: pattern-var bindings\<close>

(* dec_pattern_var_bindings_list distributes over append. *)
lemma dec_pattern_var_bindings_list_append:
  "dec_pattern_var_bindings_list (xs @ ys)
   = dec_pattern_var_bindings_list xs @ dec_pattern_var_bindings_list ys"
  by (induction xs) auto

(* splice_at distributes pattern var bindings as expected. *)
lemma dec_pattern_var_bindings_list_splice_at:
  assumes "c < length ps"
  shows "dec_pattern_var_bindings_list (splice_at c new_ps ps)
         = dec_pattern_var_bindings_list (take c ps)
           @ dec_pattern_var_bindings_list new_ps
           @ dec_pattern_var_bindings_list (drop (Suc c) ps)"
  using assms
proof (induction c new_ps ps rule: splice_at.induct)
  case (1 uu uv) thus ?case by simp
next
  case (2 ys x xs) thus ?case
    by (simp add: dec_pattern_var_bindings_list_append)
next
  case (3 c ys x xs) thus ?case by simp
qed

(* When new_ps consists of all wildcards, the spliced row has the same bindings
   as drop_at c ps (the column c content goes away). *)
lemma dec_pattern_var_bindings_list_replicate_DP_Wildcard:
  "dec_pattern_var_bindings_list (replicate n DP_Wildcard) = []"
  by (induction n) auto

lemma dec_pattern_var_bindings_list_drop_at_eq_take_drop:
  "c < length ps
   \<Longrightarrow> dec_pattern_var_bindings_list (drop_at c ps)
       = dec_pattern_var_bindings_list (take c ps)
         @ dec_pattern_var_bindings_list (drop (Suc c) ps)"
proof (induction c ps rule: drop_at.induct)
  case 1 thus ?case by simp
next
  case (2 p ps) thus ?case by simp
next
  case (3 c p ps)
  thus ?case
    by (simp add: dec_pattern_var_bindings_list_append)
qed

(* When the spliced-in patterns' bindings equal ps!c's bindings, the row's
   bindings list is unchanged. *)
lemma dec_pattern_var_bindings_list_splice_at_same_bindings:
  assumes "c < length ps"
      and "dec_pattern_var_bindings_list new_ps = dec_pattern_var_bindings (ps ! c)"
  shows "dec_pattern_var_bindings_list (splice_at c new_ps ps)
         = dec_pattern_var_bindings_list ps"
proof -
  have take_drop: "dec_pattern_var_bindings_list ps
                    = dec_pattern_var_bindings_list (take c ps)
                      @ dec_pattern_var_bindings (ps ! c)
                      @ dec_pattern_var_bindings_list (drop (Suc c) ps)"
    using assms(1)
  proof (induction c ps rule: drop_at.induct)
    case 1 thus ?case by simp
  next
    case (2 p ps) thus ?case by simp
  next
    case (3 c p ps) thus ?case
      by (simp add: dec_pattern_var_bindings_list_append)
  qed
  show ?thesis
    using dec_pattern_var_bindings_list_splice_at[OF assms(1), of new_ps]
          take_drop assms(2) by simp
qed

(* When the spliced-in patterns are all wildcards (i.e. contribute no bindings),
   the row's bindings list equals drop_at c ps's bindings list. *)
lemma dec_pattern_var_bindings_list_splice_at_wildcards:
  assumes "c < length ps"
  shows "dec_pattern_var_bindings_list (splice_at c (replicate n DP_Wildcard) ps)
         = dec_pattern_var_bindings_list (drop_at c ps)"
  using assms
        dec_pattern_var_bindings_list_splice_at[OF assms(1), of "replicate n DP_Wildcard"]
        dec_pattern_var_bindings_list_drop_at_eq_take_drop[OF assms(1)]
        dec_pattern_var_bindings_list_replicate_DP_Wildcard
  by simp

(* Distinctness preserved under splice_at when the new bindings list equals
   ps!c's bindings list (e.g. DP_Record's inner patterns' bindings). *)
lemma pattern_var_names_distinct_splice_at_same_bindings:
  assumes "c < length ps"
      and "pattern_var_names_distinct ps"
      and "dec_pattern_var_bindings_list new_ps = dec_pattern_var_bindings (ps ! c)"
  shows "pattern_var_names_distinct (splice_at c new_ps ps)"
  unfolding pattern_var_names_distinct_def
  using dec_pattern_var_bindings_list_splice_at_same_bindings[OF assms(1,3)]
        assms(2)
  by (simp add: pattern_var_names_distinct_def)

(* Distinctness preserved under splice_at when new_ps is all wildcards
   (which contribute no bindings). *)
lemma pattern_var_names_distinct_splice_at_wildcards:
  assumes "c < length ps"
      and "pattern_var_names_distinct ps"
  shows "pattern_var_names_distinct (splice_at c (replicate n DP_Wildcard) ps)"
  unfolding pattern_var_names_distinct_def
  using dec_pattern_var_bindings_list_splice_at_wildcards[OF assms(1)]
        pattern_var_names_distinct_drop_at[OF assms(2), of c]
  by (simp add: pattern_var_names_distinct_def)


subsection \<open>Body env preservation for specialise_row_bool DP_Var case\<close>

(* The big payoff: in the DP_Var case of specialise_row_bool, the body env
   built from the new row equals the body env built from the old row.
   This means the body's typing is preserved automatically. *)
lemma specialise_row_bool_DP_Var_body_env_eq:
  assumes c_lt: "c < length ps"
      and nth_eq: "ps ! c = DP_Var vr x ty"
      and distinct: "pattern_var_names_distinct ps"
  shows "extend_env_with_pattern_vars
            (extend_env_with_bindlist env ghost (bs @ [(vr, x, ty, s)]))
            ghost (drop_at c ps)
       = extend_env_with_pattern_vars
            (extend_env_with_bindlist env ghost bs) ghost ps"
proof -
  let ?E = "extend_env_with_bindlist env ghost bs"
  have step1:
    "extend_env_with_pattern_vars
       (extend_env_with_bindlist env ghost (bs @ [(vr, x, ty, s)]))
       ghost (drop_at c ps)
     = extend_env_with_pattern_vars (extend_env_with_bind ?E ghost x ty)
                                    ghost (drop_at c ps)"
    by (simp add: extend_env_with_bindlist_append)
  have x_not_in_drop:
    "x |\<notin>| dec_pattern_var_names_list (drop_at c ps)"
    using DP_Var_name_not_in_drop_at[OF c_lt nth_eq distinct] .
  have step2:
    "extend_env_with_pattern_vars (extend_env_with_bind ?E ghost x ty)
                                  ghost (drop_at c ps)
     = extend_env_with_bind (extend_env_with_pattern_vars ?E ghost (drop_at c ps))
                             ghost x ty"
    using extend_env_with_pattern_vars_extend_env_with_bind_swap[OF x_not_in_drop] .
  have step3:
    "extend_env_with_bind (extend_env_with_pattern_vars ?E ghost (drop_at c ps))
                          ghost x ty
     = extend_env_with_pattern_vars ?E ghost ps"
    using extend_env_with_pattern_vars_drop_at_DP_Var[OF c_lt nth_eq distinct] .
  show ?thesis using step1 step2 step3 by simp
qed

(* Body-env equality for the variant DP_Var-with-payload subcase. The new row
   has pattern list (replace_at c DP_Wildcard ps), bindlist (bs @ [(vr,x,ty,s)]),
   and same body. The body env on the new row equals the body env on the old. *)
lemma specialise_row_variant_DP_Var_payload_body_env_eq:
  assumes c_lt: "c < length ps"
      and nth_eq: "ps ! c = DP_Var vr x ty"
      and distinct: "pattern_var_names_distinct ps"
  shows "extend_env_with_pattern_vars
            (extend_env_with_bindlist env ghost (bs @ [(vr, x, ty, s)]))
            ghost (replace_at c DP_Wildcard ps)
       = extend_env_with_pattern_vars
            (extend_env_with_bindlist env ghost bs) ghost ps"
proof -
  have bindings_eq:
    "dec_pattern_var_bindings_list (replace_at c DP_Wildcard ps)
     = dec_pattern_var_bindings_list (drop_at c ps)"
    using dec_pattern_var_bindings_list_replace_at_DP_Wildcard_for_DP_Var[OF c_lt nth_eq] .
  have env_replace_eq_drop:
    "\<And>e. extend_env_with_pattern_vars e ghost (replace_at c DP_Wildcard ps)
        = extend_env_with_pattern_vars e ghost (drop_at c ps)"
    using bindings_eq by (simp add: extend_env_with_pattern_vars_eq_flat)
  show ?thesis
    using env_replace_eq_drop[of "extend_env_with_bindlist env ghost (bs @ [(vr, x, ty, s)])"]
          specialise_row_bool_DP_Var_body_env_eq[OF c_lt nth_eq distinct, where env=env and
                                                  ghost=ghost and bs=bs and s=s]
    by simp
qed

(* Body-env equality for the variant DP_Variant-Some-pat subcase. The new row
   has pattern list (replace_at c pat ps), same bindlist bs, same body. The
   body env equality holds because DP_Variant (Some pat)'s var bindings equal
   pat's var bindings. *)
lemma specialise_row_variant_DP_Variant_Some_body_env_eq:
  assumes c_lt: "c < length ps"
      and nth_eq: "ps ! c = DP_Variant h' (Some pat)"
  shows "extend_env_with_pattern_vars env ghost (replace_at c pat ps)
       = extend_env_with_pattern_vars env ghost ps"
proof -
  have bindings_pat: "dec_pattern_var_bindings pat
                       = dec_pattern_var_bindings (ps ! c)"
    using nth_eq by simp
  have bindings_eq:
    "dec_pattern_var_bindings_list (replace_at c pat ps)
     = dec_pattern_var_bindings_list ps"
    using dec_pattern_var_bindings_list_replace_at_same_bindings[OF c_lt bindings_pat] .
  thus ?thesis by (simp add: extend_env_with_pattern_vars_eq_flat)
qed


subsection \<open>Specialiser preservation: bool\<close>

(* The freshness premise required for specialise_row_bool_preserves_typing:
   no name appearing free in s collides with any pattern-var or bind-name
   of the row. This is the row-level instance of the matrix-wide
   freshness invariant matrix_scrut_freshness. *)
abbreviation row_scrut_fresh ::
  "CoreTerm \<Rightarrow> CoreTerm Row \<Rightarrow> bool" where
  "row_scrut_fresh s row \<equiv>
     core_term_free_vars s |\<inter>| row_var_names row = {||}"

lemma specialise_row_bool_preserves_typing:
  assumes row_wt: "row_term_well_typed env ghost colTys resultTy (ps, bs, body)"
      and c_lt: "c < length colTys"
      and col_bool: "colTys ! c = CoreTy_Bool"
      and s_ty: "core_term_type env ghost s = Some CoreTy_Bool"
      and freshness: "row_scrut_fresh s (ps, bs, body)"
      and spec: "specialise_row_bool c s h (ps, bs, body) = Some new_row"
  shows "row_term_well_typed env ghost (drop_at c colTys) resultTy new_row"
proof -
  from row_wt have
    len_pats: "length ps = length colTys" and
    bs_wt: "bindlist_well_typed env ghost bs" and
    distinct_ps: "pattern_var_names_distinct ps" and
    pats_compat: "dec_pattern_compatible_list (extend_env_with_bindlist env ghost bs)
                                              ps colTys" and
    body_ty: "core_term_type
                (extend_env_with_pattern_vars (extend_env_with_bindlist env ghost bs) ghost ps)
                ghost body = Some resultTy"
    by (auto simp: Let_def)

  let ?env_bs = "extend_env_with_bindlist env ghost bs"
  let ?env_body = "extend_env_with_pattern_vars ?env_bs ghost ps"

  have c_lt_ps: "c < length ps" using c_lt len_pats by simp
  have len_drop_pats: "length (drop_at c ps) = length (drop_at c colTys)"
    using length_drop_at[OF c_lt_ps] length_drop_at[OF c_lt] len_pats by simp

  have drop_compat: "dec_pattern_compatible_list ?env_bs (drop_at c ps) (drop_at c colTys)"
    using dec_pattern_compatible_list_drop_at[OF pats_compat c_lt_ps] len_pats by simp

  have distinct_drop: "pattern_var_names_distinct (drop_at c ps)"
    using pattern_var_names_distinct_drop_at[OF distinct_ps] .

  show ?thesis
  proof (cases "ps ! c")
    case (DP_Bool b)
    show ?thesis
    proof (cases "b = h")
      case True
      with DP_Bool spec have new_row_eq: "new_row = (drop_at c ps, bs, body)" by simp
      \<comment> \<open>Body env unchanged: pattern_vars of (drop_at c ps) is the same as ps's
           (since DP_Bool contributes no pattern vars).\<close>
      have pat_vars_eq: "dec_pattern_var_bindings_list (drop_at c ps)
                         = dec_pattern_var_bindings_list ps"
        using DP_Bool c_lt_ps
      proof (induction c ps rule: drop_at.induct)
        case 1 thus ?case by simp
      next
        case (2 p ps) thus ?case by simp
      next
        case (3 c p ps)
        thus ?case by simp
      qed
      hence env_body_eq: "extend_env_with_pattern_vars ?env_bs ghost (drop_at c ps)
                          = extend_env_with_pattern_vars ?env_bs ghost ps"
        by (simp add: extend_env_with_pattern_vars_eq_flat)
      show ?thesis
        unfolding new_row_eq
        using len_drop_pats bs_wt distinct_drop drop_compat body_ty env_body_eq
        by (auto simp: Let_def)
    next
      case False
      with DP_Bool spec show ?thesis by simp
    qed
  next
    case DP_Wildcard
    with spec have new_row_eq: "new_row = (drop_at c ps, bs, body)" by simp
    have pat_vars_eq: "dec_pattern_var_bindings_list (drop_at c ps)
                       = dec_pattern_var_bindings_list ps"
      using DP_Wildcard c_lt_ps
    proof (induction c ps rule: drop_at.induct)
      case 1 thus ?case by simp
    next
      case (2 p ps) thus ?case by simp
    next
      case (3 c p ps)
      thus ?case by simp
    qed
    hence env_body_eq: "extend_env_with_pattern_vars ?env_bs ghost (drop_at c ps)
                        = extend_env_with_pattern_vars ?env_bs ghost ps"
      by (simp add: extend_env_with_pattern_vars_eq_flat)
    show ?thesis
      unfolding new_row_eq
      using len_drop_pats bs_wt distinct_drop drop_compat body_ty env_body_eq
      by (auto simp: Let_def)
  next
    case (DP_Var vr x ty)
    with spec have new_row_eq:
      "new_row = (drop_at c ps, bs @ [(vr, x, ty, s)], body)" by simp

    \<comment> \<open>From compatibility of DP_Var with CoreTy_Bool: ty = CoreTy_Bool.\<close>
    have pat_at_c: "dec_pattern_compatible ?env_bs (ps ! c) (colTys ! c)"
      using pats_compat c_lt_ps len_pats
      by (simp add: dec_pattern_compatible_list_iff)
    with DP_Var col_bool have ty_eq: "ty = CoreTy_Bool" by simp

    \<comment> \<open>Names in bs are fresh wrt s.\<close>
    have bs_fresh_s: "fset_of_list (map (\<lambda>(_, x, _, _). x) bs) |\<inter>| core_term_free_vars s = {||}"
      using freshness
      by (simp add: row_var_names_def inf_commute inf_sup_distrib1)

    \<comment> \<open>Lift s's typing into ?env_bs.\<close>
    have s_ty_in_env_bs: "core_term_type ?env_bs ghost s = Some CoreTy_Bool"
      using core_term_type_extend_env_with_bindlist_irrelevant[OF _ s_ty] bs_fresh_s by auto

    \<comment> \<open>The new bindlist is well-typed.\<close>
    have new_bs_wt: "bindlist_well_typed env ghost (bs @ [(vr, x, ty, s)])"
      using bs_wt s_ty_in_env_bs ty_eq by (simp add: bindlist_well_typed_append)

    \<comment> \<open>The new env_bs (= env extended by bs @ [(vr, x, ty, s)]).\<close>
    let ?env_bs_new = "extend_env_with_bindlist env ghost (bs @ [(vr, x, ty, s)])"
    have env_bs_new_eq: "?env_bs_new = extend_env_with_bind ?env_bs ghost x ty"
      by (simp add: extend_env_with_bindlist_append)

    \<comment> \<open>Pattern compatibility for drop_at c ps under ?env_bs_new.\<close>
    have drop_compat_new:
      "dec_pattern_compatible_list ?env_bs_new (drop_at c ps) (drop_at c colTys)"
      using drop_compat env_bs_new_eq
            dec_pattern_compatible_list_extend_env_with_bind by simp

    \<comment> \<open>Body env equality: this is the big lemma we proved.\<close>
    have env_body_eq:
      "extend_env_with_pattern_vars ?env_bs_new ghost (drop_at c ps) = ?env_body"
      using specialise_row_bool_DP_Var_body_env_eq[OF c_lt_ps DP_Var distinct_ps,
                                                    where env=env and ghost=ghost
                                                    and bs=bs and s=s] .

    have body_ty_new:
      "core_term_type (extend_env_with_pattern_vars ?env_bs_new ghost (drop_at c ps))
                       ghost body = Some resultTy"
      using body_ty env_body_eq by simp

    show ?thesis
      unfolding new_row_eq
      using len_drop_pats new_bs_wt distinct_drop drop_compat_new body_ty_new
      by (auto simp: Let_def)
  qed (use spec in simp)+
qed


subsection \<open>Specialiser preservation: int\<close>

(* Same shape as bool: column type must be an integer type, scrutinee s
   typechecks at colTys ! c. *)
lemma specialise_row_int_preserves_typing:
  assumes row_wt: "row_term_well_typed env ghost colTys resultTy (ps, bs, body)"
      and c_lt: "c < length colTys"
      and col_int: "is_integer_type (colTys ! c)"
      and s_ty: "core_term_type env ghost s = Some (colTys ! c)"
      and freshness: "row_scrut_fresh s (ps, bs, body)"
      and spec: "specialise_row_int c s h (ps, bs, body) = Some new_row"
  shows "row_term_well_typed env ghost (drop_at c colTys) resultTy new_row"
proof -
  from row_wt have
    len_pats: "length ps = length colTys" and
    bs_wt: "bindlist_well_typed env ghost bs" and
    distinct_ps: "pattern_var_names_distinct ps" and
    pats_compat: "dec_pattern_compatible_list (extend_env_with_bindlist env ghost bs)
                                              ps colTys" and
    body_ty: "core_term_type
                (extend_env_with_pattern_vars (extend_env_with_bindlist env ghost bs) ghost ps)
                ghost body = Some resultTy"
    by (auto simp: Let_def)

  let ?env_bs = "extend_env_with_bindlist env ghost bs"
  let ?env_body = "extend_env_with_pattern_vars ?env_bs ghost ps"

  have c_lt_ps: "c < length ps" using c_lt len_pats by simp
  have len_drop_pats: "length (drop_at c ps) = length (drop_at c colTys)"
    using length_drop_at[OF c_lt_ps] length_drop_at[OF c_lt] len_pats by simp

  have drop_compat: "dec_pattern_compatible_list ?env_bs (drop_at c ps) (drop_at c colTys)"
    using dec_pattern_compatible_list_drop_at[OF pats_compat c_lt_ps] len_pats by simp

  have distinct_drop: "pattern_var_names_distinct (drop_at c ps)"
    using pattern_var_names_distinct_drop_at[OF distinct_ps] .

  show ?thesis
  proof (cases "ps ! c")
    case (DP_Int i)
    show ?thesis
    proof (cases "i = h")
      case True
      with DP_Int spec have new_row_eq: "new_row = (drop_at c ps, bs, body)" by simp
      \<comment> \<open>Body env unchanged: pattern_vars of (drop_at c ps) is the same as ps's
           (since DP_Int contributes no pattern vars).\<close>
      have pat_vars_eq: "dec_pattern_var_bindings_list (drop_at c ps)
                         = dec_pattern_var_bindings_list ps"
        using DP_Int c_lt_ps
      proof (induction c ps rule: drop_at.induct)
        case 1 thus ?case by simp
      next
        case (2 p ps) thus ?case by simp
      next
        case (3 c p ps)
        thus ?case by simp
      qed
      hence env_body_eq: "extend_env_with_pattern_vars ?env_bs ghost (drop_at c ps)
                          = extend_env_with_pattern_vars ?env_bs ghost ps"
        by (simp add: extend_env_with_pattern_vars_eq_flat)
      show ?thesis
        unfolding new_row_eq
        using len_drop_pats bs_wt distinct_drop drop_compat body_ty env_body_eq
        by (auto simp: Let_def)
    next
      case False
      with DP_Int spec show ?thesis by simp
    qed
  next
    case DP_Wildcard
    with spec have new_row_eq: "new_row = (drop_at c ps, bs, body)" by simp
    have pat_vars_eq: "dec_pattern_var_bindings_list (drop_at c ps)
                       = dec_pattern_var_bindings_list ps"
      using DP_Wildcard c_lt_ps
    proof (induction c ps rule: drop_at.induct)
      case 1 thus ?case by simp
    next
      case (2 p ps) thus ?case by simp
    next
      case (3 c p ps)
      thus ?case by simp
    qed
    hence env_body_eq: "extend_env_with_pattern_vars ?env_bs ghost (drop_at c ps)
                        = extend_env_with_pattern_vars ?env_bs ghost ps"
      by (simp add: extend_env_with_pattern_vars_eq_flat)
    show ?thesis
      unfolding new_row_eq
      using len_drop_pats bs_wt distinct_drop drop_compat body_ty env_body_eq
      by (auto simp: Let_def)
  next
    case (DP_Var vr x ty)
    with spec have new_row_eq:
      "new_row = (drop_at c ps, bs @ [(vr, x, ty, s)], body)" by simp

    \<comment> \<open>From compatibility of DP_Var with colTys ! c: ty = colTys ! c.\<close>
    have pat_at_c: "dec_pattern_compatible ?env_bs (ps ! c) (colTys ! c)"
      using pats_compat c_lt_ps len_pats
      by (simp add: dec_pattern_compatible_list_iff)
    with DP_Var have ty_eq: "ty = colTys ! c" by simp

    \<comment> \<open>Names in bs are fresh wrt s.\<close>
    have bs_fresh_s: "fset_of_list (map (\<lambda>(_, x, _, _). x) bs) |\<inter>| core_term_free_vars s = {||}"
      using freshness
      by (simp add: row_var_names_def inf_commute inf_sup_distrib1)

    \<comment> \<open>Lift s's typing into ?env_bs.\<close>
    have s_ty_in_env_bs: "core_term_type ?env_bs ghost s = Some (colTys ! c)"
      using core_term_type_extend_env_with_bindlist_irrelevant[OF _ s_ty] bs_fresh_s by auto

    \<comment> \<open>The new bindlist is well-typed.\<close>
    have new_bs_wt: "bindlist_well_typed env ghost (bs @ [(vr, x, ty, s)])"
      using bs_wt s_ty_in_env_bs ty_eq by (simp add: bindlist_well_typed_append)

    \<comment> \<open>The new env_bs (= env extended by bs @ [(vr, x, ty, s)]).\<close>
    let ?env_bs_new = "extend_env_with_bindlist env ghost (bs @ [(vr, x, ty, s)])"
    have env_bs_new_eq: "?env_bs_new = extend_env_with_bind ?env_bs ghost x ty"
      by (simp add: extend_env_with_bindlist_append)

    \<comment> \<open>Pattern compatibility for drop_at c ps under ?env_bs_new.\<close>
    have drop_compat_new:
      "dec_pattern_compatible_list ?env_bs_new (drop_at c ps) (drop_at c colTys)"
      using drop_compat env_bs_new_eq
            dec_pattern_compatible_list_extend_env_with_bind by simp

    \<comment> \<open>Body env equality: this is the big lemma we proved (DP_Var case).\<close>
    have env_body_eq:
      "extend_env_with_pattern_vars ?env_bs_new ghost (drop_at c ps) = ?env_body"
      using specialise_row_bool_DP_Var_body_env_eq[OF c_lt_ps DP_Var distinct_ps,
                                                    where env=env and ghost=ghost
                                                    and bs=bs and s=s] .

    have body_ty_new:
      "core_term_type (extend_env_with_pattern_vars ?env_bs_new ghost (drop_at c ps))
                       ghost body = Some resultTy"
      using body_ty env_body_eq by simp

    show ?thesis
      unfolding new_row_eq
      using len_drop_pats new_bs_wt distinct_drop drop_compat_new body_ty_new
      by (auto simp: Let_def)
  qed (use spec in simp)+
qed


subsection \<open>Specialiser preservation: variant\<close>

(* For variants the column type must be CoreTy_Datatype dtName tyArgs, where
   dtName is the datatype that the constructor h belongs to. The scrutinee
   s typechecks at the column type; if the variant has a payload, the new
   scrutinee at column c becomes CoreTm_VariantProj s h, which typechecks
   at the (substituted) payload type — and column c's type is replaced by
   that payload type. Without a payload, column c is dropped.

   Additional precondition payload_consistent: when the row's column-c pattern
   is DP_Variant h _, its payload-Some-ness must match has_payload. This is
   the matrix-level invariant that all DP_Variant-h patterns in column c agree
   with the ctor's payload presence — established by distinct_variant_heads
   inspecting a representative pattern. *)
lemma specialise_row_variant_preserves_typing:
  assumes row_wt: "row_term_well_typed env ghost colTys resultTy (ps, bs, body)"
      and c_lt: "c < length colTys"
      and col_dt: "colTys ! c = CoreTy_Datatype dtName tyArgs"
      and ctor_info: "fmlookup (TE_DataCtors env) h = Some (dtName, tyvars, payloadTy)"
      and len_tyargs: "length tyArgs = length tyvars"
      and s_ty: "core_term_type env ghost s = Some (colTys ! c)"
      and freshness: "row_scrut_fresh s (ps, bs, body)"
      and payload_consistent:
        "\<And>mpat. ps ! c = DP_Variant h mpat \<Longrightarrow> has_payload = (mpat \<noteq> None)"
      and spec: "specialise_row_variant c s h has_payload (ps, bs, body) = Some new_row"
  shows "row_term_well_typed env ghost
           (if has_payload
            then replace_at c (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy) colTys
            else drop_at c colTys)
           resultTy new_row"
proof -
  from row_wt have
    len_pats: "length ps = length colTys" and
    bs_wt: "bindlist_well_typed env ghost bs" and
    distinct_ps: "pattern_var_names_distinct ps" and
    pats_compat: "dec_pattern_compatible_list (extend_env_with_bindlist env ghost bs)
                                              ps colTys" and
    body_ty: "core_term_type
                (extend_env_with_pattern_vars (extend_env_with_bindlist env ghost bs) ghost ps)
                ghost body = Some resultTy"
    by (auto simp: Let_def)

  let ?env_bs = "extend_env_with_bindlist env ghost bs"
  let ?env_body = "extend_env_with_pattern_vars ?env_bs ghost ps"
  let ?subst = "fmap_of_list (zip tyvars tyArgs)"
  let ?payTy = "apply_subst ?subst payloadTy"

  have c_lt_ps: "c < length ps" using c_lt len_pats by simp

  \<comment> \<open>Compatibility of the column-c pattern with colTys ! c.\<close>
  have pat_at_c: "dec_pattern_compatible ?env_bs (ps ! c) (colTys ! c)"
    using pats_compat c_lt_ps len_pats
    by (simp add: dec_pattern_compatible_list_iff)

  \<comment> \<open>Lift ctor_info into ?env_bs (TE_DataCtors is invariant under bindlist extension).\<close>
  have ctor_info_bs: "fmlookup (TE_DataCtors ?env_bs) h
                       = Some (dtName, tyvars, payloadTy)"
    using ctor_info
  proof (induction bs arbitrary: env)
    case Nil thus ?case by simp
  next
    case (Cons b bs)
    obtain vr' x' ty' rhs' where b_eq: "b = (vr', x', ty', rhs')"
      by (cases b) auto
    have step: "fmlookup (TE_DataCtors (extend_env_with_bind env ghost x' ty')) h
                = fmlookup (TE_DataCtors env) h"
      unfolding extend_env_with_bind_def by simp
    have "fmlookup (TE_DataCtors (extend_env_with_bind env ghost x' ty')) h
          = Some (dtName, tyvars, payloadTy)"
      using step Cons.prems by simp
    with Cons.IH show ?case using b_eq by simp
  qed

  \<comment> \<open>Common length and freshness facts.\<close>
  have len_drop_pats: "length (drop_at c ps) = length (drop_at c colTys)"
    using length_drop_at[OF c_lt_ps] length_drop_at[OF c_lt] len_pats by simp
  have len_repl_pats: "length (replace_at c DP_Wildcard ps) = length (replace_at c ?payTy colTys)"
    using length_replace_at[of c DP_Wildcard ps]
          length_replace_at[of c ?payTy colTys] len_pats by simp
  have drop_compat: "dec_pattern_compatible_list ?env_bs (drop_at c ps) (drop_at c colTys)"
    using dec_pattern_compatible_list_drop_at[OF pats_compat c_lt_ps] len_pats by simp
  have distinct_drop: "pattern_var_names_distinct (drop_at c ps)"
    using pattern_var_names_distinct_drop_at[OF distinct_ps] .
  have bs_fresh_s: "fset_of_list (map (\<lambda>(_, x, _, _). x) bs) |\<inter>| core_term_free_vars s = {||}"
    using freshness
    by (simp add: row_var_names_def inf_commute inf_sup_distrib1)
  have s_ty_in_env_bs: "core_term_type ?env_bs ghost s = Some (colTys ! c)"
    using core_term_type_extend_env_with_bindlist_irrelevant[OF _ s_ty] bs_fresh_s by auto

  \<comment> \<open>Compatibility for replace_at when payload pattern is DP_Wildcard.\<close>
  have repl_compat_wildcard:
    "dec_pattern_compatible_list ?env_bs
       (replace_at c DP_Wildcard ps) (replace_at c ?payTy colTys)"
  proof -
    have len_eq: "length ps = length colTys" using len_pats .
    have wild_compat: "dec_pattern_compatible ?env_bs DP_Wildcard ?payTy" by simp
    have all2: "list_all2 (dec_pattern_compatible ?env_bs) ps colTys"
      using pats_compat len_eq
      by (auto simp: dec_pattern_compatible_list_iff list_all2_conv_all_nth)
    have all2_repl: "list_all2 (dec_pattern_compatible ?env_bs)
                       (replace_at c DP_Wildcard ps) (replace_at c ?payTy colTys)"
      using list_all2_replace_at[OF all2 c_lt_ps wild_compat] .
    thus ?thesis
      by (auto simp: dec_pattern_compatible_list_iff list_all2_conv_all_nth)
  qed

  show ?thesis
  proof (cases "ps ! c")
    case (DP_Variant h' mpat)
    show ?thesis
    proof (cases "h' = h")
      case h_eq: True
      have h_lookup_bs:
        "fmlookup (TE_DataCtors ?env_bs) h = Some (dtName, tyvars, payloadTy)"
        using ctor_info_bs .
      \<comment> \<open>Compatibility under DP_Variant h mpat: extract just the payload-inner check.\<close>
      have payload_compat_if_some:
        "\<And>inner. mpat = Some inner
          \<Longrightarrow> dec_pattern_compatible ?env_bs inner ?payTy"
      proof -
        fix inner assume mpat_some: "mpat = Some inner"
        from pat_at_c DP_Variant col_dt h_eq h_lookup_bs mpat_some
        show "dec_pattern_compatible ?env_bs inner ?payTy" by simp
      qed
      \<comment> \<open>Use payload_consistent.\<close>
      have ps_at_c_h: "ps ! c = DP_Variant h mpat" using DP_Variant h_eq by simp
      hence has_payload_eq: "has_payload = (mpat \<noteq> None)"
        using payload_consistent by simp

      show ?thesis
      proof (cases mpat)
        case None
        \<comment> \<open>has_payload = False, so the new column types are drop_at c colTys.\<close>
        from has_payload_eq None have not_hp: "\<not> has_payload" by simp
        from None DP_Variant h_eq spec have new_row_eq:
          "new_row = (drop_at c ps, bs, body)" by simp
        have pat_vars_eq: "dec_pattern_var_bindings_list (drop_at c ps)
                            = dec_pattern_var_bindings_list ps"
          using DP_Variant None c_lt_ps
        proof (induction c ps rule: drop_at.induct)
          case 1 thus ?case by simp
        next
          case (2 p ps)
          from "2.prems"(1) have p_eq: "p = DP_Variant h' None" using None by simp
          show ?case using p_eq by simp
        next
          case (3 c p ps) thus ?case by simp
        qed
        hence env_body_eq: "extend_env_with_pattern_vars ?env_bs ghost (drop_at c ps)
                            = ?env_body"
          by (simp add: extend_env_with_pattern_vars_eq_flat)
        show ?thesis
          unfolding new_row_eq
          using not_hp len_drop_pats bs_wt distinct_drop drop_compat body_ty env_body_eq
          by (auto simp: Let_def)
      next
        case (Some pat)
        \<comment> \<open>has_payload = True; new row is replace_at c pat ps.\<close>
        from has_payload_eq Some have hp: "has_payload" by simp
        from Some DP_Variant h_eq spec have new_row_eq:
          "new_row = (replace_at c pat ps, bs, body)" by simp
        have pat_compat_pay: "dec_pattern_compatible ?env_bs pat ?payTy"
          using payload_compat_if_some[OF Some] .

        have len_repl_pat_pats: "length (replace_at c pat ps)
                                  = length (replace_at c ?payTy colTys)"
          using length_replace_at[of c pat ps]
                length_replace_at[of c ?payTy colTys] len_pats by simp

        have repl_compat: "dec_pattern_compatible_list ?env_bs
                              (replace_at c pat ps) (replace_at c ?payTy colTys)"
        proof -
          have all2: "list_all2 (dec_pattern_compatible ?env_bs) ps colTys"
            using pats_compat len_pats
            by (auto simp: dec_pattern_compatible_list_iff list_all2_conv_all_nth)
          have "list_all2 (dec_pattern_compatible ?env_bs)
                  (replace_at c pat ps) (replace_at c ?payTy colTys)"
            using list_all2_replace_at[OF all2 c_lt_ps pat_compat_pay] .
          thus ?thesis
            by (auto simp: dec_pattern_compatible_list_iff list_all2_conv_all_nth)
        qed

        have distinct_repl: "pattern_var_names_distinct (replace_at c pat ps)"
        proof -
          have bindings_eq: "dec_pattern_var_bindings pat = dec_pattern_var_bindings (ps ! c)"
            using DP_Variant Some by simp
          show ?thesis
            using pattern_var_names_distinct_replace_at_same_bindings[OF c_lt_ps distinct_ps bindings_eq] .
        qed

        have env_body_eq: "extend_env_with_pattern_vars ?env_bs ghost (replace_at c pat ps)
                            = ?env_body"
          using specialise_row_variant_DP_Variant_Some_body_env_eq[
                    OF c_lt_ps, where pat=pat and h'=h' and env="?env_bs" and ghost=ghost]
                DP_Variant Some by simp

        show ?thesis
          unfolding new_row_eq
          using hp len_repl_pat_pats bs_wt distinct_repl repl_compat body_ty env_body_eq
          by (auto simp: Let_def)
      qed
    next
      case False
      with DP_Variant spec show ?thesis by simp
    qed
  next
    case DP_Wildcard
    show ?thesis
    proof (cases has_payload)
      case True
      \<comment> \<open>has_payload: new row keeps col c (replace_at DP_Wildcard).\<close>
      from True DP_Wildcard spec have new_row_eq:
        "new_row = (replace_at c DP_Wildcard ps, bs, body)" by simp
      have pat_vars_eq:
        "dec_pattern_var_bindings_list (replace_at c DP_Wildcard ps)
         = dec_pattern_var_bindings_list ps"
        using dec_pattern_var_bindings_list_replace_at_DP_Wildcard_no_binds[OF c_lt_ps]
              DP_Wildcard by simp
      hence env_body_eq:
        "extend_env_with_pattern_vars ?env_bs ghost (replace_at c DP_Wildcard ps)
         = ?env_body"
        by (simp add: extend_env_with_pattern_vars_eq_flat)
      have distinct_repl: "pattern_var_names_distinct (replace_at c DP_Wildcard ps)"
        using pattern_var_names_distinct_replace_at_same_bindings[
                OF c_lt_ps distinct_ps]
              DP_Wildcard by simp
      show ?thesis
        unfolding new_row_eq
        using True len_repl_pats bs_wt distinct_repl repl_compat_wildcard body_ty env_body_eq
        by (auto simp: Let_def)
    next
      case False
      \<comment> \<open>not has_payload: new row drops col c.\<close>
      from False DP_Wildcard spec have new_row_eq:
        "new_row = (drop_at c ps, bs, body)" by simp
      have pat_vars_eq: "dec_pattern_var_bindings_list (drop_at c ps)
                         = dec_pattern_var_bindings_list ps"
        using DP_Wildcard c_lt_ps
      proof (induction c ps rule: drop_at.induct)
        case 1 thus ?case by simp
      next
        case (2 p ps) thus ?case by simp
      next
        case (3 c p ps) thus ?case by simp
      qed
      hence env_body_eq: "extend_env_with_pattern_vars ?env_bs ghost (drop_at c ps)
                          = ?env_body"
        by (simp add: extend_env_with_pattern_vars_eq_flat)
      show ?thesis
        unfolding new_row_eq
        using False len_drop_pats bs_wt distinct_drop drop_compat body_ty env_body_eq
        by (auto simp: Let_def)
    qed
  next
    case (DP_Var vr x ty)
    \<comment> \<open>From compatibility of DP_Var with colTys ! c: ty = colTys ! c.\<close>
    from DP_Var pat_at_c have ty_eq: "ty = colTys ! c" by simp
    have new_bs_wt: "bindlist_well_typed env ghost (bs @ [(vr, x, ty, s)])"
      using bs_wt s_ty_in_env_bs ty_eq by (simp add: bindlist_well_typed_append)
    let ?env_bs_new = "extend_env_with_bindlist env ghost (bs @ [(vr, x, ty, s)])"
    have env_bs_new_eq: "?env_bs_new = extend_env_with_bind ?env_bs ghost x ty"
      by (simp add: extend_env_with_bindlist_append)

    show ?thesis
    proof (cases has_payload)
      case True
      \<comment> \<open>has_payload: new row is (replace_at c DP_Wildcard ps, bs @ ..., body).\<close>
      from True DP_Var spec have new_row_eq:
        "new_row = (replace_at c DP_Wildcard ps, bs @ [(vr, x, ty, s)], body)"
        by simp
      have repl_compat_new:
        "dec_pattern_compatible_list ?env_bs_new
            (replace_at c DP_Wildcard ps) (replace_at c ?payTy colTys)"
        using repl_compat_wildcard env_bs_new_eq
              dec_pattern_compatible_list_extend_env_with_bind by simp
      have distinct_repl: "pattern_var_names_distinct (replace_at c DP_Wildcard ps)"
        using pattern_var_names_distinct_replace_at_DP_Wildcard_for_DP_Var[
                OF c_lt_ps DP_Var distinct_ps] .
      have env_body_eq:
        "extend_env_with_pattern_vars ?env_bs_new ghost (replace_at c DP_Wildcard ps)
         = ?env_body"
        using specialise_row_variant_DP_Var_payload_body_env_eq[
                OF c_lt_ps DP_Var distinct_ps,
                where env=env and ghost=ghost and bs=bs and s=s] .
      have body_ty_new:
        "core_term_type (extend_env_with_pattern_vars ?env_bs_new ghost
                          (replace_at c DP_Wildcard ps))
                         ghost body = Some resultTy"
        using body_ty env_body_eq by simp
      show ?thesis
        unfolding new_row_eq
        using True len_repl_pats new_bs_wt distinct_repl repl_compat_new body_ty_new
        by (auto simp: Let_def)
    next
      case False
      \<comment> \<open>not has_payload: new row is (drop_at c ps, bs @ ..., body) — same as bool/int DP_Var.\<close>
      from False DP_Var spec have new_row_eq:
        "new_row = (drop_at c ps, bs @ [(vr, x, ty, s)], body)" by simp
      have drop_compat_new:
        "dec_pattern_compatible_list ?env_bs_new (drop_at c ps) (drop_at c colTys)"
        using drop_compat env_bs_new_eq
              dec_pattern_compatible_list_extend_env_with_bind by simp
      have env_body_eq:
        "extend_env_with_pattern_vars ?env_bs_new ghost (drop_at c ps) = ?env_body"
        using specialise_row_bool_DP_Var_body_env_eq[OF c_lt_ps DP_Var distinct_ps,
                                                      where env=env and ghost=ghost
                                                      and bs=bs and s=s] .
      have body_ty_new:
        "core_term_type (extend_env_with_pattern_vars ?env_bs_new ghost (drop_at c ps))
                         ghost body = Some resultTy"
        using body_ty env_body_eq by simp
      show ?thesis
        unfolding new_row_eq
        using False len_drop_pats new_bs_wt distinct_drop drop_compat_new body_ty_new
        by (auto simp: Let_def)
    qed
  qed (use spec in simp)+
qed


subsection \<open>Default-row preservation\<close>

(* default_row preserves a row only when col c is wildcard-like, in which
   case col c is dropped without changing the bindlist. (DP_Var case
   does extend bs.) *)
lemma default_row_preserves_typing:
  assumes row_wt: "row_term_well_typed env ghost colTys resultTy (ps, bs, body)"
      and c_lt: "c < length colTys"
      and s_ty: "core_term_type env ghost s = Some (colTys ! c)"
      and freshness: "row_scrut_fresh s (ps, bs, body)"
      and spec: "default_row c s (ps, bs, body) = Some new_row"
  shows "row_term_well_typed env ghost (drop_at c colTys) resultTy new_row"
proof -
  from row_wt have
    len_pats: "length ps = length colTys" and
    bs_wt: "bindlist_well_typed env ghost bs" and
    distinct_ps: "pattern_var_names_distinct ps" and
    pats_compat: "dec_pattern_compatible_list (extend_env_with_bindlist env ghost bs)
                                              ps colTys" and
    body_ty: "core_term_type
                (extend_env_with_pattern_vars (extend_env_with_bindlist env ghost bs) ghost ps)
                ghost body = Some resultTy"
    by (auto simp: Let_def)

  let ?env_bs = "extend_env_with_bindlist env ghost bs"
  let ?env_body = "extend_env_with_pattern_vars ?env_bs ghost ps"

  have c_lt_ps: "c < length ps" using c_lt len_pats by simp
  have len_drop_pats: "length (drop_at c ps) = length (drop_at c colTys)"
    using length_drop_at[OF c_lt_ps] length_drop_at[OF c_lt] len_pats by simp

  have drop_compat: "dec_pattern_compatible_list ?env_bs (drop_at c ps) (drop_at c colTys)"
    using dec_pattern_compatible_list_drop_at[OF pats_compat c_lt_ps] len_pats by simp

  have distinct_drop: "pattern_var_names_distinct (drop_at c ps)"
    using pattern_var_names_distinct_drop_at[OF distinct_ps] .

  show ?thesis
  proof (cases "ps ! c")
    case DP_Wildcard
    with spec have new_row_eq: "new_row = (drop_at c ps, bs, body)" by simp
    have pat_vars_eq: "dec_pattern_var_bindings_list (drop_at c ps)
                       = dec_pattern_var_bindings_list ps"
      using DP_Wildcard c_lt_ps
    proof (induction c ps rule: drop_at.induct)
      case 1 thus ?case by simp
    next
      case (2 p ps) thus ?case by simp
    next
      case (3 c p ps)
      thus ?case by simp
    qed
    hence env_body_eq: "extend_env_with_pattern_vars ?env_bs ghost (drop_at c ps)
                        = extend_env_with_pattern_vars ?env_bs ghost ps"
      by (simp add: extend_env_with_pattern_vars_eq_flat)
    show ?thesis
      unfolding new_row_eq
      using len_drop_pats bs_wt distinct_drop drop_compat body_ty env_body_eq
      by (auto simp: Let_def)
  next
    case (DP_Var vr x ty)
    with spec have new_row_eq:
      "new_row = (drop_at c ps, bs @ [(vr, x, ty, s)], body)" by simp

    \<comment> \<open>From compatibility of DP_Var with colTys ! c: ty = colTys ! c.\<close>
    have pat_at_c: "dec_pattern_compatible ?env_bs (ps ! c) (colTys ! c)"
      using pats_compat c_lt_ps len_pats
      by (simp add: dec_pattern_compatible_list_iff)
    with DP_Var have ty_eq: "ty = colTys ! c" by simp

    \<comment> \<open>Names in bs are fresh wrt s.\<close>
    have bs_fresh_s: "fset_of_list (map (\<lambda>(_, x, _, _). x) bs) |\<inter>| core_term_free_vars s = {||}"
      using freshness
      by (simp add: row_var_names_def inf_commute inf_sup_distrib1)

    \<comment> \<open>Lift s's typing into ?env_bs.\<close>
    have s_ty_in_env_bs: "core_term_type ?env_bs ghost s = Some (colTys ! c)"
      using core_term_type_extend_env_with_bindlist_irrelevant[OF _ s_ty] bs_fresh_s by auto

    \<comment> \<open>The new bindlist is well-typed.\<close>
    have new_bs_wt: "bindlist_well_typed env ghost (bs @ [(vr, x, ty, s)])"
      using bs_wt s_ty_in_env_bs ty_eq by (simp add: bindlist_well_typed_append)

    \<comment> \<open>The new env_bs (= env extended by bs @ [(vr, x, ty, s)]).\<close>
    let ?env_bs_new = "extend_env_with_bindlist env ghost (bs @ [(vr, x, ty, s)])"
    have env_bs_new_eq: "?env_bs_new = extend_env_with_bind ?env_bs ghost x ty"
      by (simp add: extend_env_with_bindlist_append)

    \<comment> \<open>Pattern compatibility for drop_at c ps under ?env_bs_new.\<close>
    have drop_compat_new:
      "dec_pattern_compatible_list ?env_bs_new (drop_at c ps) (drop_at c colTys)"
      using drop_compat env_bs_new_eq
            dec_pattern_compatible_list_extend_env_with_bind by simp

    \<comment> \<open>Body env equality: same lemma as the bool case (DP_Var subproof).\<close>
    have env_body_eq:
      "extend_env_with_pattern_vars ?env_bs_new ghost (drop_at c ps) = ?env_body"
      using specialise_row_bool_DP_Var_body_env_eq[OF c_lt_ps DP_Var distinct_ps,
                                                    where env=env and ghost=ghost
                                                    and bs=bs and s=s] .

    have body_ty_new:
      "core_term_type (extend_env_with_pattern_vars ?env_bs_new ghost (drop_at c ps))
                       ghost body = Some resultTy"
      using body_ty env_body_eq by simp

    show ?thesis
      unfolding new_row_eq
      using len_drop_pats new_bs_wt distinct_drop drop_compat_new body_ty_new
      by (auto simp: Let_def)
  qed (use spec in simp)+
qed


subsection \<open>Record decomposition preservation\<close>

(* expand_record_row decomposes a record column into its fields. The column
   type must be CoreTy_Record fieldTypes; the column scrutinee s typechecks
   at that type, and the result row has length-extended pattern list and
   column types matching the field types (spliced in at column c). *)
lemma expand_record_row_preserves_typing:
  assumes row_wt: "row_term_well_typed env ghost colTys resultTy (ps, bs, body)"
      and c_lt: "c < length colTys"
      and col_rec: "colTys ! c = CoreTy_Record fieldTypes"
      and s_ty: "core_term_type env ghost s = Some (colTys ! c)"
      and freshness: "row_scrut_fresh s (ps, bs, body)"
      and fld_names_eq: "fld_names = map fst fieldTypes"
  shows "row_term_well_typed env ghost
           (splice_at c (map snd fieldTypes) colTys)
           resultTy
           (expand_record_row c s fld_names (ps, bs, body))"
proof -
  from row_wt have
    len_pats: "length ps = length colTys" and
    bs_wt: "bindlist_well_typed env ghost bs" and
    distinct_ps: "pattern_var_names_distinct ps" and
    pats_compat: "dec_pattern_compatible_list (extend_env_with_bindlist env ghost bs)
                                              ps colTys" and
    body_ty: "core_term_type
                (extend_env_with_pattern_vars (extend_env_with_bindlist env ghost bs) ghost ps)
                ghost body = Some resultTy"
    by (auto simp: Let_def)

  let ?env_bs = "extend_env_with_bindlist env ghost bs"
  let ?env_body = "extend_env_with_pattern_vars ?env_bs ghost ps"
  let ?fldTys = "map snd fieldTypes"
  let ?n = "length fld_names"

  have c_lt_ps: "c < length ps" using c_lt len_pats by simp

  have pat_at_c: "dec_pattern_compatible ?env_bs (ps ! c) (colTys ! c)"
    using pats_compat c_lt_ps len_pats
    by (simp add: dec_pattern_compatible_list_iff)

  \<comment> \<open>list_all2 form of pats_compat.\<close>
  have pats_compat_all2: "list_all2 (dec_pattern_compatible ?env_bs) ps colTys"
    using pats_compat len_pats
    by (auto simp: dec_pattern_compatible_list_iff list_all2_conv_all_nth)

  \<comment> \<open>n = length fieldTypes.\<close>
  have n_eq: "?n = length fieldTypes" using fld_names_eq by simp

  \<comment> \<open>Length facts.\<close>
  have len_splice_colTys: "length (splice_at c ?fldTys colTys) = length colTys - 1 + length fieldTypes"
    using length_splice_at[OF c_lt] by simp

  \<comment> \<open>Freshness of bs against s.\<close>
  have bs_fresh_s: "fset_of_list (map (\<lambda>(_, x, _, _). x) bs) |\<inter>| core_term_free_vars s = {||}"
    using freshness
    by (simp add: row_var_names_def inf_commute inf_sup_distrib1)
  have s_ty_in_env_bs: "core_term_type ?env_bs ghost s = Some (colTys ! c)"
    using core_term_type_extend_env_with_bindlist_irrelevant[OF _ s_ty] bs_fresh_s by auto

  show ?thesis
  proof (cases "ps ! c")
    case (DP_Record row_flds)
    \<comment> \<open>Compatibility gives map fst row_flds = map fst fieldTypes and inner compat.\<close>
    from pat_at_c DP_Record col_rec have
      flds_names: "map fst row_flds = map fst fieldTypes" and
      flds_compat: "dec_pattern_compatible_list ?env_bs (map snd row_flds) ?fldTys"
      by simp_all
    have len_flds: "length row_flds = length fieldTypes"
      using flds_names by (metis length_map)

    from DP_Record have new_row_eq:
      "expand_record_row c s fld_names (ps, bs, body)
       = (splice_at c (map snd row_flds) ps, bs, body)" by simp

    \<comment> \<open>Length of new row matches.\<close>
    have len_new_pats: "length (splice_at c (map snd row_flds) ps)
                        = length (splice_at c ?fldTys colTys)"
      using length_splice_at[OF c_lt_ps] length_splice_at[OF c_lt]
            len_pats len_flds by simp

    \<comment> \<open>Pattern compatibility list under splice_at.\<close>
    have inner_all2: "list_all2 (dec_pattern_compatible ?env_bs)
                        (map snd row_flds) ?fldTys"
      using flds_compat
      by (auto simp: dec_pattern_compatible_list_iff list_all2_conv_all_nth)
    have splice_all2: "list_all2 (dec_pattern_compatible ?env_bs)
                        (splice_at c (map snd row_flds) ps) (splice_at c ?fldTys colTys)"
      using list_all2_splice_at[OF pats_compat_all2 c_lt_ps inner_all2] .
    have splice_compat: "dec_pattern_compatible_list ?env_bs
                          (splice_at c (map snd row_flds) ps) (splice_at c ?fldTys colTys)"
      using splice_all2
      by (auto simp: dec_pattern_compatible_list_iff list_all2_conv_all_nth)

    \<comment> \<open>Distinctness preserved.\<close>
    have bindings_eq: "dec_pattern_var_bindings_list (map snd row_flds)
                        = dec_pattern_var_bindings (ps ! c)"
      using DP_Record by simp
    have distinct_splice: "pattern_var_names_distinct (splice_at c (map snd row_flds) ps)"
      using pattern_var_names_distinct_splice_at_same_bindings[OF c_lt_ps distinct_ps bindings_eq] .

    \<comment> \<open>Body env preserved.\<close>
    have env_body_eq:
      "extend_env_with_pattern_vars ?env_bs ghost (splice_at c (map snd row_flds) ps)
       = ?env_body"
      using dec_pattern_var_bindings_list_splice_at_same_bindings[OF c_lt_ps bindings_eq]
      by (simp add: extend_env_with_pattern_vars_eq_flat)

    show ?thesis
      unfolding new_row_eq
      using len_new_pats bs_wt distinct_splice splice_compat body_ty env_body_eq
      by (auto simp: Let_def)

  next
    case DP_Wildcard
    from DP_Wildcard have new_row_eq:
      "expand_record_row c s fld_names (ps, bs, body)
       = (splice_at c (replicate ?n DP_Wildcard) ps, bs, body)" by simp

    \<comment> \<open>Length.\<close>
    have len_new_pats: "length (splice_at c (replicate ?n DP_Wildcard) ps)
                        = length (splice_at c ?fldTys colTys)"
      using length_splice_at[OF c_lt_ps] length_splice_at[OF c_lt]
            len_pats n_eq by simp

    \<comment> \<open>Compatibility under splice_at.\<close>
    have wild_all2: "list_all2 (dec_pattern_compatible ?env_bs)
                       (replicate ?n DP_Wildcard) ?fldTys"
      using n_eq by (simp add: list_all2_conv_all_nth)
    have splice_all2: "list_all2 (dec_pattern_compatible ?env_bs)
                        (splice_at c (replicate ?n DP_Wildcard) ps) (splice_at c ?fldTys colTys)"
      using list_all2_splice_at[OF pats_compat_all2 c_lt_ps wild_all2] .
    have splice_compat: "dec_pattern_compatible_list ?env_bs
                          (splice_at c (replicate ?n DP_Wildcard) ps)
                          (splice_at c ?fldTys colTys)"
      using splice_all2
      by (auto simp: dec_pattern_compatible_list_iff list_all2_conv_all_nth)

    \<comment> \<open>Distinctness preserved.\<close>
    have distinct_splice: "pattern_var_names_distinct (splice_at c (replicate ?n DP_Wildcard) ps)"
      using pattern_var_names_distinct_splice_at_wildcards[OF c_lt_ps distinct_ps] .

    \<comment> \<open>Body env: bindings of splice_at-wildcards = bindings of drop_at, and DP_Wildcard
         contributes no bindings, so drop_at's bindings = ps's bindings.\<close>
    have pat_vars_eq: "dec_pattern_var_bindings_list (drop_at c ps)
                       = dec_pattern_var_bindings_list ps"
      using DP_Wildcard c_lt_ps
    proof (induction c ps rule: drop_at.induct)
      case 1 thus ?case by simp
    next
      case (2 p ps) thus ?case by simp
    next
      case (3 c p ps) thus ?case by simp
    qed
    have env_body_eq:
      "extend_env_with_pattern_vars ?env_bs ghost (splice_at c (replicate ?n DP_Wildcard) ps)
       = ?env_body"
      using dec_pattern_var_bindings_list_splice_at_wildcards[OF c_lt_ps] pat_vars_eq
      by (simp add: extend_env_with_pattern_vars_eq_flat)

    show ?thesis
      unfolding new_row_eq
      using len_new_pats bs_wt distinct_splice splice_compat body_ty env_body_eq
      by (auto simp: Let_def)

  next
    case (DP_Var vr x ty)
    from DP_Var have new_row_eq:
      "expand_record_row c s fld_names (ps, bs, body)
       = (splice_at c (replicate ?n DP_Wildcard) ps, bs @ [(vr, x, ty, s)], body)"
      by simp

    \<comment> \<open>From DP_Var compatibility, ty = colTys ! c.\<close>
    from DP_Var pat_at_c have ty_eq: "ty = colTys ! c" by simp
    have new_bs_wt: "bindlist_well_typed env ghost (bs @ [(vr, x, ty, s)])"
      using bs_wt s_ty_in_env_bs ty_eq by (simp add: bindlist_well_typed_append)
    let ?env_bs_new = "extend_env_with_bindlist env ghost (bs @ [(vr, x, ty, s)])"
    have env_bs_new_eq: "?env_bs_new = extend_env_with_bind ?env_bs ghost x ty"
      by (simp add: extend_env_with_bindlist_append)

    \<comment> \<open>Length.\<close>
    have len_new_pats: "length (splice_at c (replicate ?n DP_Wildcard) ps)
                        = length (splice_at c ?fldTys colTys)"
      using length_splice_at[OF c_lt_ps] length_splice_at[OF c_lt]
            len_pats n_eq by simp

    \<comment> \<open>Compatibility under splice_at, in the extended env.\<close>
    have wild_all2: "list_all2 (dec_pattern_compatible ?env_bs)
                       (replicate ?n DP_Wildcard) ?fldTys"
      using n_eq by (simp add: list_all2_conv_all_nth)
    have splice_all2: "list_all2 (dec_pattern_compatible ?env_bs)
                        (splice_at c (replicate ?n DP_Wildcard) ps) (splice_at c ?fldTys colTys)"
      using list_all2_splice_at[OF pats_compat_all2 c_lt_ps wild_all2] .
    have splice_compat_old: "dec_pattern_compatible_list ?env_bs
                              (splice_at c (replicate ?n DP_Wildcard) ps)
                              (splice_at c ?fldTys colTys)"
      using splice_all2
      by (auto simp: dec_pattern_compatible_list_iff list_all2_conv_all_nth)
    have splice_compat: "dec_pattern_compatible_list ?env_bs_new
                          (splice_at c (replicate ?n DP_Wildcard) ps)
                          (splice_at c ?fldTys colTys)"
      using splice_compat_old env_bs_new_eq
            dec_pattern_compatible_list_extend_env_with_bind by simp

    \<comment> \<open>Distinctness preserved (the new wildcard bindings list has no var bindings,
         so distinctness of replace_at-wildcards reduces to drop_at distinctness which
         we already have for DP_Var).\<close>
    have distinct_splice:
      "pattern_var_names_distinct (splice_at c (replicate ?n DP_Wildcard) ps)"
      using pattern_var_names_distinct_splice_at_wildcards[OF c_lt_ps distinct_ps] .

    \<comment> \<open>Body env: with the new bindlist (bs @ [(vr,x,ty,s)]), the body env on
         splice_at-wildcards equals the original ?env_body. Same shape as the
         variant DP_Var-with-payload case.\<close>
    have splice_bindings_eq:
      "dec_pattern_var_bindings_list (splice_at c (replicate ?n DP_Wildcard) ps)
       = dec_pattern_var_bindings_list (drop_at c ps)"
      using dec_pattern_var_bindings_list_splice_at_wildcards[OF c_lt_ps] .
    have env_splice_eq_drop:
      "\<And>e. extend_env_with_pattern_vars e ghost (splice_at c (replicate ?n DP_Wildcard) ps)
          = extend_env_with_pattern_vars e ghost (drop_at c ps)"
      using splice_bindings_eq
      by (simp add: extend_env_with_pattern_vars_eq_flat)
    have env_body_eq:
      "extend_env_with_pattern_vars ?env_bs_new ghost
        (splice_at c (replicate ?n DP_Wildcard) ps)
       = ?env_body"
      using env_splice_eq_drop[of ?env_bs_new]
            specialise_row_bool_DP_Var_body_env_eq[OF c_lt_ps DP_Var distinct_ps,
                                                    where env=env and ghost=ghost
                                                    and bs=bs and s=s]
      by simp
    have body_ty_new:
      "core_term_type (extend_env_with_pattern_vars ?env_bs_new ghost
                        (splice_at c (replicate ?n DP_Wildcard) ps))
                       ghost body = Some resultTy"
      using body_ty env_body_eq by simp

    show ?thesis
      unfolding new_row_eq
      using len_new_pats new_bs_wt distinct_splice splice_compat body_ty_new
      by (auto simp: Let_def)

  next
    \<comment> \<open>Unreachable cases: DP_Bool, DP_Int, DP_Variant — incompatible with CoreTy_Record.\<close>
    case (DP_Bool b)
    with pat_at_c col_rec show ?thesis by simp
  next
    case (DP_Int i)
    with pat_at_c col_rec show ?thesis by simp
  next
    case (DP_Variant h' mpat)
    with pat_at_c col_rec have False
      by (simp split: option.splits CoreType.splits)
    thus ?thesis by simp
  qed
qed


subsection \<open>Helpers for the Some-c recursive case\<close>

(* row_var_names of expand_record_row's output is a subset of the input row's. *)
lemma row_var_names_expand_record_row_subset:
  assumes "c < length ps"
  shows "row_var_names (expand_record_row c s fld_names (ps, bs, body))
         |\<subseteq>| row_var_names (ps, bs, body)"
  using assms
proof (cases "ps ! c")
  case (DP_Record row_flds)
  have eq: "dec_pattern_var_bindings_list (splice_at c (map snd row_flds) ps)
            = dec_pattern_var_bindings_list ps"
    using DP_Record assms
          dec_pattern_var_bindings_list_splice_at_same_bindings[
            OF assms, of "map snd row_flds"]
    by simp
  have new_eq: "expand_record_row c s fld_names (ps, bs, body)
                = (splice_at c (map snd row_flds) ps, bs, body)"
    using DP_Record by simp
  show ?thesis
    using new_eq eq
    by (simp add: row_var_names_def
                  flat_binding_names_dec_pattern_var_bindings_list[symmetric]
                  flat_binding_names_def)
next
  case DP_Wildcard
  have new_eq: "expand_record_row c s fld_names (ps, bs, body)
                = (splice_at c (replicate (length fld_names) DP_Wildcard) ps, bs, body)"
    using DP_Wildcard by simp
  have eq_drop: "dec_pattern_var_bindings_list
                    (splice_at c (replicate (length fld_names) DP_Wildcard) ps)
                  = dec_pattern_var_bindings_list (drop_at c ps)"
    using dec_pattern_var_bindings_list_splice_at_wildcards[OF assms] .
  have subset: "set (dec_pattern_var_bindings_list (drop_at c ps))
                \<subseteq> set (dec_pattern_var_bindings_list ps)"
    using dec_pattern_var_bindings_list_drop_at_subset .
  \<comment> \<open>The pattern var name fset is monotone in the bindings set.\<close>
  have pat_names_subset:
    "dec_pattern_var_names_list
        (splice_at c (replicate (length fld_names) DP_Wildcard) ps)
     |\<subseteq>| dec_pattern_var_names_list ps"
  proof -
    have step:
      "flat_binding_names
         (dec_pattern_var_bindings_list (splice_at c (replicate (length fld_names) DP_Wildcard) ps))
       |\<subseteq>| flat_binding_names (dec_pattern_var_bindings_list ps)"
      unfolding flat_binding_names_def using eq_drop subset
      by (simp add: DP_Wildcard assms dec_pattern_var_bindings_list_replicate_DP_Wildcard
          dec_pattern_var_bindings_list_splice_at_same_bindings)
    thus ?thesis
      by (simp add: flat_binding_names_dec_pattern_var_bindings_list)
  qed
  show ?thesis
    using new_eq pat_names_subset
    by (auto simp: row_var_names_def)
next
  case (DP_Var vr x ty)
  have new_eq: "expand_record_row c s fld_names (ps, bs, body)
                = (splice_at c (replicate (length fld_names) DP_Wildcard) ps,
                   bs @ [(vr, x, ty, s)], body)"
    using DP_Var by simp
  have eq_drop: "dec_pattern_var_bindings_list
                    (splice_at c (replicate (length fld_names) DP_Wildcard) ps)
                  = dec_pattern_var_bindings_list (drop_at c ps)"
    using dec_pattern_var_bindings_list_splice_at_wildcards[OF assms] .
  have subset: "set (dec_pattern_var_bindings_list (drop_at c ps))
                \<subseteq> set (dec_pattern_var_bindings_list ps)"
    using dec_pattern_var_bindings_list_drop_at_subset .
  have pat_names_subset:
    "dec_pattern_var_names_list
        (splice_at c (replicate (length fld_names) DP_Wildcard) ps)
     |\<subseteq>| dec_pattern_var_names_list ps"
  proof -
    have map_subset:
      "set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list (drop_at c ps)))
       \<subseteq> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps))"
      using subset by force
    have "flat_binding_names
            (dec_pattern_var_bindings_list (splice_at c (replicate (length fld_names) DP_Wildcard) ps))
          |\<subseteq>| flat_binding_names (dec_pattern_var_bindings_list ps)"
      unfolding flat_binding_names_def
      using eq_drop fset_of_list_subset[OF map_subset]
      by simp
    thus ?thesis
      by (simp add: flat_binding_names_dec_pattern_var_bindings_list)
  qed
  \<comment> \<open>x is in ps's pattern var names (it's the DP_Var binding at column c).\<close>
  have x_in_ps: "x |\<in>| dec_pattern_var_names_list ps"
  proof -
    have "(vr, x, ty) \<in> set (dec_pattern_var_bindings (ps ! c))"
      using DP_Var by simp
    hence "(vr, x, ty) \<in> set (dec_pattern_var_bindings_list ps)"
      using assms by (induction ps arbitrary: c) (auto simp: nth_Cons split: nat.splits)
    hence "x |\<in>| flat_binding_names (dec_pattern_var_bindings_list ps)"
      by (force simp: flat_binding_names_def fset_of_list_elem)
    thus ?thesis
      by (simp add: flat_binding_names_dec_pattern_var_bindings_list)
  qed
  show ?thesis
    using new_eq pat_names_subset x_in_ps
    by (auto simp: row_var_names_def)
qed (use assms in \<open>auto simp: row_var_names_def\<close>)+

(* Unfolding compile_matrix in the record case. *)
lemma compile_matrix_unfold_record:
  assumes fnw: "first_non_wildcard_col (map (\<lambda>(ps, _, _). ps) rows) = Some c"
      and hd_eq: "hd (filter (\<lambda>p. \<not> is_wildcard_like p)
                              (map (\<lambda>(ps, _, _). ps ! c) rows)) = head_pat"
      and hk_eq: "head_kind_of head_pat = Some (HK_Record fld_names)"
  shows "compile_matrix (scruts, rows)
       = compile_matrix (expand_record_scruts c (scruts ! c) fld_names scruts,
                         map (expand_record_row c (scruts ! c) fld_names) rows)"
  by (subst compile_matrix.simps) (simp add: fnw hd_eq hk_eq Let_def)

(* Unfolding compile_matrix in the bool case. *)
lemma compile_matrix_unfold_bool:
  assumes fnw: "first_non_wildcard_col (map (\<lambda>(ps, _, _). ps) rows) = Some c"
      and hd_eq: "hd (filter (\<lambda>p. \<not> is_wildcard_like p)
                              (map (\<lambda>(ps, _, _). ps ! c) rows)) = head_pat"
      and hk_eq: "head_kind_of head_pat = Some HK_Bool"
  shows "compile_matrix (scruts, rows)
       = (let s_c = scruts ! c;
              col_pats = map (\<lambda>(ps, _, _). ps ! c) rows;
              has_default = list_ex is_wildcard_like col_pats;
              default_rows = List.map_filter (default_row c s_c) rows;
              default_arm =
                (if has_default
                 then [(CorePat_Wildcard,
                        compile_matrix (drop_at c scruts, default_rows))]
                 else []);
              heads = distinct_bool_heads col_pats;
              head_arm = (\<lambda>h.
                (CorePat_Bool h,
                 compile_matrix (drop_at c scruts,
                   List.map_filter (specialise_row_bool c s_c h) rows)))
          in MT_Test s_c (map head_arm heads @ default_arm))"
  by (subst compile_matrix.simps) (simp add: fnw hd_eq hk_eq Let_def)

(* Unfolding compile_matrix in the int case. *)
lemma compile_matrix_unfold_int:
  assumes fnw: "first_non_wildcard_col (map (\<lambda>(ps, _, _). ps) rows) = Some c"
      and hd_eq: "hd (filter (\<lambda>p. \<not> is_wildcard_like p)
                              (map (\<lambda>(ps, _, _). ps ! c) rows)) = head_pat"
      and hk_eq: "head_kind_of head_pat = Some HK_Int"
  shows "compile_matrix (scruts, rows)
       = (let s_c = scruts ! c;
              col_pats = map (\<lambda>(ps, _, _). ps ! c) rows;
              has_default = list_ex is_wildcard_like col_pats;
              default_rows = List.map_filter (default_row c s_c) rows;
              default_arm =
                (if has_default
                 then [(CorePat_Wildcard,
                        compile_matrix (drop_at c scruts, default_rows))]
                 else []);
              heads = distinct_int_heads col_pats;
              head_arm = (\<lambda>h.
                (CorePat_Int h,
                 compile_matrix (drop_at c scruts,
                   List.map_filter (specialise_row_int c s_c h) rows)))
          in MT_Test s_c (map head_arm heads @ default_arm))"
  by (subst compile_matrix.simps) (simp add: fnw hd_eq hk_eq Let_def)

(* Unfolding compile_matrix in the variant case. *)
lemma compile_matrix_unfold_variant:
  assumes fnw: "first_non_wildcard_col (map (\<lambda>(ps, _, _). ps) rows) = Some c"
      and hd_eq: "hd (filter (\<lambda>p. \<not> is_wildcard_like p)
                              (map (\<lambda>(ps, _, _). ps ! c) rows)) = head_pat"
      and hk_eq: "head_kind_of head_pat = Some HK_Variant"
  shows "compile_matrix (scruts, rows)
       = (let s_c = scruts ! c;
              col_pats = map (\<lambda>(ps, _, _). ps ! c) rows;
              has_default = list_ex is_wildcard_like col_pats;
              default_rows = List.map_filter (default_row c s_c) rows;
              default_arm =
                (if has_default
                 then [(CorePat_Wildcard,
                        compile_matrix (drop_at c scruts, default_rows))]
                 else []);
              heads = distinct_variant_heads col_pats;
              head_arm = (\<lambda>(h, has_payload).
                let new_scruts =
                      (if has_payload
                       then replace_at c (CoreTm_VariantProj s_c h) scruts
                       else drop_at c scruts)
                in (CorePat_Variant h CorePat_Wildcard,
                    compile_matrix (new_scruts,
                      List.map_filter (specialise_row_variant c s_c h has_payload) rows)))
          in MT_Test s_c (map head_arm heads @ default_arm))"
  by (subst compile_matrix.simps) (simp add: fnw hd_eq hk_eq Let_def)


(* Splice-at preserves list_all P: when xs is list_all-P and ys is also
   list_all-P, the spliced list is list_all-P. *)
lemma list_all_splice_at:
  assumes "list_all P xs"
      and "list_all P ys"
  shows "list_all P (splice_at c ys xs)"
  using assms
  by (induction c ys xs rule: splice_at.induct) auto

(* Drop-at preserves list_all P. *)
lemma list_all_drop_at:
  "list_all P xs \<Longrightarrow> list_all P (drop_at c xs)"
  by (induction c xs rule: drop_at.induct) auto

(* Replace-at preserves list_all P when the new element satisfies P. *)
lemma list_all_replace_at:
  assumes "list_all P xs"
      and "P y"
  shows "list_all P (replace_at c y xs)"
  using assms
  by (induction c y xs rule: replace_at.induct) auto


section \<open>Main theorem: compile_matrix preserves typing\<close>

(* All DP_Variant subpatterns of a DecPattern. *)
fun dec_pattern_all_variants :: "DecPattern \<Rightarrow> (string \<times> DecPattern option) set"
and dec_pattern_all_variants_list :: "DecPattern list \<Rightarrow> (string \<times> DecPattern option) set"
where
  "dec_pattern_all_variants (DP_Var _ _ _) = {}"
| "dec_pattern_all_variants DP_Wildcard = {}"
| "dec_pattern_all_variants (DP_Bool _) = {}"
| "dec_pattern_all_variants (DP_Int _) = {}"
| "dec_pattern_all_variants (DP_Variant h None) = {(h, None)}"
| "dec_pattern_all_variants (DP_Variant h (Some inner)) =
     {(h, Some inner)} \<union> dec_pattern_all_variants inner"
| "dec_pattern_all_variants (DP_Record flds) =
     dec_pattern_all_variants_list (map snd flds)"
| "dec_pattern_all_variants_list [] = {}"
| "dec_pattern_all_variants_list (p # ps) =
     dec_pattern_all_variants p \<union> dec_pattern_all_variants_list ps"

(* All DP_Variant subpatterns appearing anywhere in a row. *)
definition row_all_variants :: "'body Row \<Rightarrow> (string \<times> DecPattern option) set" where
  "row_all_variants row = (case row of (pats, _, _) \<Rightarrow> dec_pattern_all_variants_list pats)"

(* Matrix-level invariant: any two DP_Variant subpatterns ANYWHERE in the
   matrix that share the same constructor name agree on payload-presence.
   This is enforced by the elaborator (check_payload_arity in ElabPattern.thy)
   and is required so that compile_matrix's choice of has_payload is
   consistent across all rows. *)
definition matrix_payload_consistent :: "'body MatchMatrix \<Rightarrow> bool" where
  "matrix_payload_consistent mtx =
     (case mtx of (_, rows) \<Rightarrow>
        (\<forall>row1 \<in> set rows. \<forall>row2 \<in> set rows.
           \<forall>h mpat1 mpat2.
              (h, mpat1) \<in> row_all_variants row1
              \<and> (h, mpat2) \<in> row_all_variants row2
              \<longrightarrow> (mpat1 = None) = (mpat2 = None)))"


subsection \<open>Helpers about dec_pattern_all_variants\<close>

(* dec_pattern_all_variants_list distributes over append. *)
lemma dec_pattern_all_variants_list_append:
  "dec_pattern_all_variants_list (xs @ ys)
   = dec_pattern_all_variants_list xs \<union> dec_pattern_all_variants_list ys"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons p xs)
  have "dec_pattern_all_variants_list ((p # xs) @ ys)
        = dec_pattern_all_variants_list (p # (xs @ ys))" by simp
  also have "\<dots> = dec_pattern_all_variants p \<union> dec_pattern_all_variants_list (xs @ ys)"
    by simp
  also have "\<dots> = dec_pattern_all_variants p
                  \<union> dec_pattern_all_variants_list xs
                  \<union> dec_pattern_all_variants_list ys"
    using Cons.IH by auto
  also have "\<dots> = dec_pattern_all_variants_list (p # xs)
                  \<union> dec_pattern_all_variants_list ys"
    by simp
  finally show ?case .
qed

(* dec_pattern_all_variants_list of splice_at: take c ++ middle ++ drop (Suc c). *)
lemma dec_pattern_all_variants_list_splice_at:
  assumes "c < length ps"
  shows "dec_pattern_all_variants_list (splice_at c new_ps ps)
         = dec_pattern_all_variants_list (take c ps)
           \<union> dec_pattern_all_variants_list new_ps
           \<union> dec_pattern_all_variants_list (drop (Suc c) ps)"
  using assms
  by (induction c new_ps ps rule: splice_at.induct)
     (auto simp: dec_pattern_all_variants_list_append)

(* Variants of original ps decompose into variants at column c, plus
   variants in (take c) and (drop (Suc c)). *)
lemma dec_pattern_all_variants_list_decompose:
  assumes "c < length ps"
  shows "dec_pattern_all_variants_list ps
         = dec_pattern_all_variants_list (take c ps)
           \<union> dec_pattern_all_variants (ps ! c)
           \<union> dec_pattern_all_variants_list (drop (Suc c) ps)"
  using assms
  by (induction c ps rule: drop_at.induct)
     (auto simp: dec_pattern_all_variants_list_append)

(* dec_pattern_all_variants_list of (replicate n DP_Wildcard) is empty. *)
lemma dec_pattern_all_variants_list_replicate_DP_Wildcard:
  "dec_pattern_all_variants_list (replicate n DP_Wildcard) = {}"
  by (induction n) auto

(* DP_Record's all_variants equals the all_variants of its inner pattern list. *)
lemma dec_pattern_all_variants_DP_Record_eq:
  "dec_pattern_all_variants (DP_Record flds)
   = dec_pattern_all_variants_list (map snd flds)"
  by simp

(* row_all_variants of expand_record_row's output is a subset of the input row's. *)
lemma row_all_variants_expand_record_row_subset:
  assumes "c < length ps"
  shows "row_all_variants (expand_record_row c s fld_names (ps, bs, body))
         \<subseteq> row_all_variants (ps, bs, body)"
proof (cases "ps ! c")
  case (DP_Record row_flds)
  have new_eq: "expand_record_row c s fld_names (ps, bs, body)
                = (splice_at c (map snd row_flds) ps, bs, body)"
    using DP_Record by simp
  have variants_eq:
    "dec_pattern_all_variants_list (splice_at c (map snd row_flds) ps)
     = dec_pattern_all_variants_list ps"
    using DP_Record dec_pattern_all_variants_list_splice_at[OF assms]
          dec_pattern_all_variants_list_decompose[OF assms]
    by simp
  show ?thesis using new_eq variants_eq by (simp add: row_all_variants_def)
next
  case DP_Wildcard
  have new_eq: "expand_record_row c s fld_names (ps, bs, body)
                = (splice_at c (replicate (length fld_names) DP_Wildcard) ps, bs, body)"
    using DP_Wildcard by simp
  have variants_subset:
    "dec_pattern_all_variants_list
       (splice_at c (replicate (length fld_names) DP_Wildcard) ps)
     \<subseteq> dec_pattern_all_variants_list ps"
    using dec_pattern_all_variants_list_splice_at[OF assms]
          dec_pattern_all_variants_list_decompose[OF assms]
          dec_pattern_all_variants_list_replicate_DP_Wildcard
    by auto
  show ?thesis using new_eq variants_subset by (simp add: row_all_variants_def)
next
  case (DP_Var vr x ty)
  have new_eq: "expand_record_row c s fld_names (ps, bs, body)
                = (splice_at c (replicate (length fld_names) DP_Wildcard) ps,
                   bs @ [(vr, x, ty, s)], body)"
    using DP_Var by simp
  have variants_subset:
    "dec_pattern_all_variants_list
       (splice_at c (replicate (length fld_names) DP_Wildcard) ps)
     \<subseteq> dec_pattern_all_variants_list ps"
    using dec_pattern_all_variants_list_splice_at[OF assms]
          dec_pattern_all_variants_list_decompose[OF assms]
          dec_pattern_all_variants_list_replicate_DP_Wildcard
    by auto
  show ?thesis using new_eq variants_subset by (simp add: row_all_variants_def)
qed (use assms in \<open>auto simp: row_all_variants_def\<close>)+

(* dec_pattern_all_variants_list of drop_at \<subseteq> original. *)
lemma dec_pattern_all_variants_list_drop_at_subset:
  "dec_pattern_all_variants_list (drop_at c ps)
   \<subseteq> dec_pattern_all_variants_list ps"
  by (induction c ps rule: drop_at.induct) auto

(* dec_pattern_all_variants_list of replace_at: c-th original is replaced by new_p.
   So variants become (variants \<setminus> ps!c's variants) \<union> new_p's variants.
   For a generic statement: bound by variants \<union> new_p's. *)
lemma dec_pattern_all_variants_list_replace_at_subset:
  assumes "c < length ps"
  shows "dec_pattern_all_variants_list (replace_at c new_p ps)
         \<subseteq> dec_pattern_all_variants_list ps \<union> dec_pattern_all_variants new_p"
  using assms
  by (induction c new_p ps rule: replace_at.induct) auto

(* When new_p's variants \<subseteq> (ps!c)'s variants, replace_at preserves variant set. *)
lemma dec_pattern_all_variants_list_replace_at_preserves:
  assumes "c < length ps"
      and "dec_pattern_all_variants new_p \<subseteq> dec_pattern_all_variants (ps ! c)"
  shows "dec_pattern_all_variants_list (replace_at c new_p ps)
         \<subseteq> dec_pattern_all_variants_list ps"
  using assms
  by (induction c new_p ps rule: replace_at.induct) auto

(* row_all_variants of specialise_row_bool (when not None) is \<subseteq> original's. *)
lemma row_all_variants_specialise_row_bool_subset:
  assumes "specialise_row_bool c s h (ps, bs, body) = Some new_row"
  shows "row_all_variants new_row \<subseteq> row_all_variants (ps, bs, body)"
proof -
  have "new_row = (drop_at c ps, bs, body) \<or>
        (\<exists>vr x ty. new_row = (drop_at c ps, bs @ [(vr, x, ty, s)], body))"
    using assms by (cases "ps ! c") (auto split: if_splits)
  thus ?thesis
    using dec_pattern_all_variants_list_drop_at_subset
    by (auto simp: row_all_variants_def)
qed

(* row_all_variants of specialise_row_int is \<subseteq> original's. *)
lemma row_all_variants_specialise_row_int_subset:
  assumes "specialise_row_int c s h (ps, bs, body) = Some new_row"
  shows "row_all_variants new_row \<subseteq> row_all_variants (ps, bs, body)"
proof -
  have "new_row = (drop_at c ps, bs, body) \<or>
        (\<exists>vr x ty. new_row = (drop_at c ps, bs @ [(vr, x, ty, s)], body))"
    using assms by (cases "ps ! c") (auto split: if_splits)
  thus ?thesis
    using dec_pattern_all_variants_list_drop_at_subset
    by (auto simp: row_all_variants_def)
qed

(* row_all_variants of default_row (when not None) is \<subseteq> original's. *)
lemma row_all_variants_default_row_subset:
  assumes "default_row c s (ps, bs, body) = Some new_row"
  shows "row_all_variants new_row \<subseteq> row_all_variants (ps, bs, body)"
proof -
  have "new_row = (drop_at c ps, bs, body) \<or>
        (\<exists>vr x ty. new_row = (drop_at c ps, bs @ [(vr, x, ty, s)], body))"
    using assms by (cases "ps ! c") auto
  thus ?thesis
    using dec_pattern_all_variants_list_drop_at_subset
    by (auto simp: row_all_variants_def)
qed

(* row_all_variants of specialise_row_variant is \<subseteq> original's.
   Even though the DP_Variant (Some pat) case uses replace_at c pat ps, pat's
   variants are a subset of (DP_Variant h (Some pat))'s variants. *)
lemma row_all_variants_specialise_row_variant_subset:
  assumes "c < length ps"
      and "specialise_row_variant c s h has_payload (ps, bs, body) = Some new_row"
  shows "row_all_variants new_row \<subseteq> row_all_variants (ps, bs, body)"
proof -
  show ?thesis
  proof (cases "ps ! c")
    case (DP_Variant h' mpat)
    show ?thesis
    proof (cases "h' = h")
      case h_eq: True
      show ?thesis
      proof (cases mpat)
        case None
        from None DP_Variant h_eq assms have new_row_eq:
          "new_row = (drop_at c ps, bs, body)" by simp
        show ?thesis
          using new_row_eq dec_pattern_all_variants_list_drop_at_subset
          by (auto simp: row_all_variants_def)
      next
        case (Some pat)
        from Some DP_Variant h_eq assms have new_row_eq:
          "new_row = (replace_at c pat ps, bs, body)" by simp
        \<comment> \<open>pat's variants \<subseteq> (DP_Variant h (Some pat))'s variants.\<close>
        have pat_subset: "dec_pattern_all_variants pat \<subseteq> dec_pattern_all_variants (ps ! c)"
          using DP_Variant Some by auto
        have repl_subset:
          "dec_pattern_all_variants_list (replace_at c pat ps)
           \<subseteq> dec_pattern_all_variants_list ps"
          using dec_pattern_all_variants_list_replace_at_preserves[OF assms(1) pat_subset] .
        show ?thesis
          using new_row_eq repl_subset
          by (auto simp: row_all_variants_def)
      qed
    next
      case False
      with DP_Variant assms show ?thesis by simp
    qed
  next
    case DP_Wildcard
    show ?thesis
    proof (cases has_payload)
      case True
      from True DP_Wildcard assms have new_row_eq:
        "new_row = (replace_at c DP_Wildcard ps, bs, body)" by simp
      have wild_subset: "dec_pattern_all_variants DP_Wildcard \<subseteq> dec_pattern_all_variants (ps ! c)"
        by simp
      have repl_subset:
        "dec_pattern_all_variants_list (replace_at c DP_Wildcard ps)
         \<subseteq> dec_pattern_all_variants_list ps"
        using dec_pattern_all_variants_list_replace_at_preserves[OF assms(1) wild_subset] .
      show ?thesis
        using new_row_eq repl_subset
        by (auto simp: row_all_variants_def)
    next
      case False
      from False DP_Wildcard assms have new_row_eq:
        "new_row = (drop_at c ps, bs, body)" by simp
      show ?thesis
        using new_row_eq dec_pattern_all_variants_list_drop_at_subset
        by (auto simp: row_all_variants_def)
    qed
  next
    case (DP_Var vr x ty)
    show ?thesis
    proof (cases has_payload)
      case True
      from True DP_Var assms have new_row_eq:
        "new_row = (replace_at c DP_Wildcard ps, bs @ [(vr, x, ty, s)], body)" by simp
      have wild_subset: "dec_pattern_all_variants DP_Wildcard \<subseteq> dec_pattern_all_variants (ps ! c)"
        by simp
      have repl_subset:
        "dec_pattern_all_variants_list (replace_at c DP_Wildcard ps)
         \<subseteq> dec_pattern_all_variants_list ps"
        using dec_pattern_all_variants_list_replace_at_preserves[OF assms(1) wild_subset] .
      show ?thesis
        using new_row_eq repl_subset
        by (auto simp: row_all_variants_def)
    next
      case False
      from False DP_Var assms have new_row_eq:
        "new_row = (drop_at c ps, bs @ [(vr, x, ty, s)], body)" by simp
      show ?thesis
        using new_row_eq dec_pattern_all_variants_list_drop_at_subset
        by (auto simp: row_all_variants_def)
    qed
  qed (use assms in simp)+
qed


subsection \<open>Helpers about row_var_names under specialisation\<close>

(* Helper: dec_pattern_var_bindings_list of drop_at c ps is sublist (set-wise) of original.
   Already proved as dec_pattern_var_bindings_list_drop_at_subset. *)

(* row_var_names of specialise_row_bool's output is a subset of the input row's. *)
lemma row_var_names_specialise_row_bool_subset:
  assumes "c < length ps"
      and "specialise_row_bool c s h (ps, bs, body) = Some new_row"
  shows "row_var_names new_row |\<subseteq>| row_var_names (ps, bs, body)"
proof -
  consider
    (drop_no_bind) "new_row = (drop_at c ps, bs, body)" |
    (drop_with_bind) vr x ty where "new_row = (drop_at c ps, bs @ [(vr, x, ty, s)], body)"
                                    "ps ! c = DP_Var vr x ty"
    using assms by (cases "ps ! c") (auto split: if_splits)
  thus ?thesis
  proof cases
    case drop_no_bind
    have subset:
      "set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list (drop_at c ps)))
       \<subseteq> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps))"
      using dec_pattern_var_bindings_list_drop_at_subset by force
    show ?thesis
      using drop_no_bind subset
            fset_of_list_subset[OF subset]
      by (auto simp: row_var_names_def
                     flat_binding_names_dec_pattern_var_bindings_list[symmetric]
                     flat_binding_names_def)
  next
    case (drop_with_bind vr x ty)
    \<comment> \<open>x is in ps's pattern var names (DP_Var at column c).\<close>
    have x_in_ps: "x |\<in>| dec_pattern_var_names_list ps"
    proof -
      have "(vr, x, ty) \<in> set (dec_pattern_var_bindings (ps ! c))"
        using drop_with_bind(2) by simp
      hence "(vr, x, ty) \<in> set (dec_pattern_var_bindings_list ps)"
        using assms(1) by (induction ps arbitrary: c) (auto simp: nth_Cons split: nat.splits)
      hence "x |\<in>| flat_binding_names (dec_pattern_var_bindings_list ps)"
        by (force simp: flat_binding_names_def fset_of_list_elem)
      thus ?thesis
        by (simp add: flat_binding_names_dec_pattern_var_bindings_list)
    qed
    have subset:
      "set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list (drop_at c ps)))
       \<subseteq> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps))"
      using dec_pattern_var_bindings_list_drop_at_subset by force
    show ?thesis
      using drop_with_bind(1) x_in_ps fset_of_list_subset[OF subset]
      by (auto simp: row_var_names_def
                     flat_binding_names_dec_pattern_var_bindings_list[symmetric]
                     flat_binding_names_def)
  qed
qed

(* row_var_names of specialise_row_int's output is a subset of the input row's. *)
lemma row_var_names_specialise_row_int_subset:
  assumes "c < length ps"
      and "specialise_row_int c s h (ps, bs, body) = Some new_row"
  shows "row_var_names new_row |\<subseteq>| row_var_names (ps, bs, body)"
proof -
  consider
    (drop_no_bind) "new_row = (drop_at c ps, bs, body)" |
    (drop_with_bind) vr x ty where "new_row = (drop_at c ps, bs @ [(vr, x, ty, s)], body)"
                                    "ps ! c = DP_Var vr x ty"
    using assms by (cases "ps ! c") (auto split: if_splits)
  thus ?thesis
  proof cases
    case drop_no_bind
    have subset:
      "set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list (drop_at c ps)))
       \<subseteq> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps))"
      using dec_pattern_var_bindings_list_drop_at_subset by force
    show ?thesis
      using drop_no_bind fset_of_list_subset[OF subset]
      by (auto simp: row_var_names_def
                     flat_binding_names_dec_pattern_var_bindings_list[symmetric]
                     flat_binding_names_def)
  next
    case (drop_with_bind vr x ty)
    have x_in_ps: "x |\<in>| dec_pattern_var_names_list ps"
    proof -
      have "(vr, x, ty) \<in> set (dec_pattern_var_bindings (ps ! c))"
        using drop_with_bind(2) by simp
      hence "(vr, x, ty) \<in> set (dec_pattern_var_bindings_list ps)"
        using assms(1) by (induction ps arbitrary: c) (auto simp: nth_Cons split: nat.splits)
      hence "x |\<in>| flat_binding_names (dec_pattern_var_bindings_list ps)"
        by (force simp: flat_binding_names_def fset_of_list_elem)
      thus ?thesis
        by (simp add: flat_binding_names_dec_pattern_var_bindings_list)
    qed
    have subset:
      "set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list (drop_at c ps)))
       \<subseteq> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps))"
      using dec_pattern_var_bindings_list_drop_at_subset by force
    show ?thesis
      using drop_with_bind(1) x_in_ps fset_of_list_subset[OF subset]
      by (auto simp: row_var_names_def
                     flat_binding_names_dec_pattern_var_bindings_list[symmetric]
                     flat_binding_names_def)
  qed
qed

(* row_var_names of default_row's output is a subset of the input row's. *)
lemma row_var_names_default_row_subset:
  assumes "c < length ps"
      and "default_row c s (ps, bs, body) = Some new_row"
  shows "row_var_names new_row |\<subseteq>| row_var_names (ps, bs, body)"
proof -
  consider
    (drop_no_bind) "new_row = (drop_at c ps, bs, body)" "ps ! c = DP_Wildcard" |
    (drop_with_bind) vr x ty where "new_row = (drop_at c ps, bs @ [(vr, x, ty, s)], body)"
                                    "ps ! c = DP_Var vr x ty"
    using assms by (cases "ps ! c") auto
  thus ?thesis
  proof cases
    case drop_no_bind
    have subset:
      "set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list (drop_at c ps)))
       \<subseteq> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps))"
      using dec_pattern_var_bindings_list_drop_at_subset by force
    show ?thesis
      using drop_no_bind(1) fset_of_list_subset[OF subset]
      by (auto simp: row_var_names_def
                     flat_binding_names_dec_pattern_var_bindings_list[symmetric]
                     flat_binding_names_def)
  next
    case (drop_with_bind vr x ty)
    have x_in_ps: "x |\<in>| dec_pattern_var_names_list ps"
    proof -
      have "(vr, x, ty) \<in> set (dec_pattern_var_bindings (ps ! c))"
        using drop_with_bind(2) by simp
      hence "(vr, x, ty) \<in> set (dec_pattern_var_bindings_list ps)"
        using assms(1) by (induction ps arbitrary: c) (auto simp: nth_Cons split: nat.splits)
      hence "x |\<in>| flat_binding_names (dec_pattern_var_bindings_list ps)"
        by (force simp: flat_binding_names_def fset_of_list_elem)
      thus ?thesis
        by (simp add: flat_binding_names_dec_pattern_var_bindings_list)
    qed
    have subset:
      "set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list (drop_at c ps)))
       \<subseteq> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps))"
      using dec_pattern_var_bindings_list_drop_at_subset by force
    show ?thesis
      using drop_with_bind(1) x_in_ps fset_of_list_subset[OF subset]
      by (auto simp: row_var_names_def
                     flat_binding_names_dec_pattern_var_bindings_list[symmetric]
                     flat_binding_names_def)
  qed
qed

(* row_var_names of specialise_row_variant's output is a subset of the input row's. *)
lemma row_var_names_specialise_row_variant_subset:
  assumes "c < length ps"
      and "specialise_row_variant c s h has_payload (ps, bs, body) = Some new_row"
  shows "row_var_names new_row |\<subseteq>| row_var_names (ps, bs, body)"
proof -
  consider
    (drop_no_bind) "new_row = (drop_at c ps, bs, body)" |
    (replace_no_bind) new_p where
      "new_row = (replace_at c new_p ps, bs, body)"
      "dec_pattern_var_bindings new_p = []
       \<or> dec_pattern_var_bindings new_p = dec_pattern_var_bindings (ps ! c)" |
    (drop_with_bind) vr x ty where
      "new_row = (drop_at c ps, bs @ [(vr, x, ty, s)], body)"
      "ps ! c = DP_Var vr x ty" |
    (replace_with_bind) vr x ty where
      "new_row = (replace_at c DP_Wildcard ps, bs @ [(vr, x, ty, s)], body)"
      "ps ! c = DP_Var vr x ty"
  proof (cases "ps ! c")
    case (DP_Variant h' mpat)
    show ?thesis
    proof (cases "h' = h")
      case True
      show ?thesis
      proof (cases mpat)
        case None
        from None DP_Variant True assms have "new_row = (drop_at c ps, bs, body)" by simp
        thus ?thesis using that(1) by simp
      next
        case (Some pat)
        from Some DP_Variant True assms have eq:
          "new_row = (replace_at c pat ps, bs, body)" by simp
        have bindings_eq: "dec_pattern_var_bindings pat = dec_pattern_var_bindings (ps ! c)"
          using DP_Variant Some by simp
        show ?thesis using that(2)[OF eq] bindings_eq by simp
      qed
    next
      case False
      with DP_Variant assms show ?thesis by simp
    qed
  next
    case DP_Wildcard
    show ?thesis
    proof (cases has_payload)
      case True
      from True DP_Wildcard assms have eq:
        "new_row = (replace_at c DP_Wildcard ps, bs, body)" by simp
      have bindings_empty: "dec_pattern_var_bindings DP_Wildcard = []" by simp
      show ?thesis using that(2)[OF eq] bindings_empty by simp
    next
      case False
      from False DP_Wildcard assms have "new_row = (drop_at c ps, bs, body)" by simp
      thus ?thesis using that(1) by simp
    qed
  next
    case (DP_Var vr x ty)
    show ?thesis
    proof (cases has_payload)
      case True
      from True DP_Var assms have
        "new_row = (replace_at c DP_Wildcard ps, bs @ [(vr, x, ty, s)], body)" by simp
      thus ?thesis using DP_Var that(4) by simp
    next
      case False
      from False DP_Var assms have "new_row = (drop_at c ps, bs @ [(vr, x, ty, s)], body)"
        by simp
      thus ?thesis using DP_Var that(3) by simp
    qed
  qed (use assms in simp)+
  thus ?thesis
  proof cases
    case drop_no_bind
    have subset:
      "set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list (drop_at c ps)))
       \<subseteq> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps))"
      using dec_pattern_var_bindings_list_drop_at_subset by force
    show ?thesis
      using drop_no_bind fset_of_list_subset[OF subset]
      by (auto simp: row_var_names_def
                     flat_binding_names_dec_pattern_var_bindings_list[symmetric]
                     flat_binding_names_def)
  next
    case (replace_no_bind new_p)
    \<comment> \<open>Either new_p has no bindings (so replace_at gives sublist of ps's bindings via the
         general replace_at_subset bound), or new_p's bindings equal ps!c's.\<close>
    from replace_no_bind(2) consider
      "dec_pattern_var_bindings new_p = []" |
      "dec_pattern_var_bindings new_p = dec_pattern_var_bindings (ps ! c)"
      by blast
    thus ?thesis
    proof cases
      case 1
      \<comment> \<open>new_p has no bindings — same as drop_at c ps for var-name purposes.\<close>
      have eq: "dec_pattern_var_bindings_list (replace_at c new_p ps)
                  = dec_pattern_var_bindings_list (drop_at c ps)"
      proof -
        have take_drop_eq: "dec_pattern_var_bindings_list (replace_at c new_p ps)
                              = dec_pattern_var_bindings_list (take c ps)
                                @ dec_pattern_var_bindings_list (drop (Suc c) ps)"
          using dec_pattern_var_bindings_list_replace_at_DP_Wildcard_for_DP_Var
          \<comment> \<open>Easier: derive by direct induction on (c, new_p, ps).\<close>
          using assms(1) "1"
        proof (induction c new_p ps rule: replace_at.induct)
          case (1 uu uv) thus ?case by simp
        next
          case (2 y x xs) thus ?case
            by (simp add: dec_pattern_var_bindings_list_append "2.prems"(3))
        next
          case (3 c y x xs) thus ?case by simp
        qed
        show ?thesis
          using take_drop_eq dec_pattern_var_bindings_list_drop_at_eq_take_drop[OF assms(1)]
          by simp
      qed
      have subset:
        "set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list (replace_at c new_p ps)))
         \<subseteq> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps))"
        using eq dec_pattern_var_bindings_list_drop_at_subset by force
      show ?thesis
        using replace_no_bind(1) fset_of_list_subset[OF subset]
        by (auto simp: row_var_names_def
                       flat_binding_names_dec_pattern_var_bindings_list[symmetric]
                       flat_binding_names_def)
    next
      case 2
      \<comment> \<open>new_p's bindings = ps!c's. So replace_at preserves bindings list (set-wise).\<close>
      have eq: "dec_pattern_var_bindings_list (replace_at c new_p ps)
                  = dec_pattern_var_bindings_list ps"
        using dec_pattern_var_bindings_list_replace_at_same_bindings[OF assms(1) "2"] .
      have names_eq: "dec_pattern_var_names_list (replace_at c new_p ps)
                      = dec_pattern_var_names_list ps"
        using eq
        by (simp add: flat_binding_names_dec_pattern_var_bindings_list[symmetric])
      show ?thesis
        using replace_no_bind(1) names_eq
        by (auto simp: row_var_names_def)
    qed
  next
    case (drop_with_bind vr x ty)
    have x_in_ps: "x |\<in>| dec_pattern_var_names_list ps"
    proof -
      have "(vr, x, ty) \<in> set (dec_pattern_var_bindings (ps ! c))"
        using drop_with_bind(2) by simp
      hence "(vr, x, ty) \<in> set (dec_pattern_var_bindings_list ps)"
        using assms(1) by (induction ps arbitrary: c) (auto simp: nth_Cons split: nat.splits)
      hence "x |\<in>| flat_binding_names (dec_pattern_var_bindings_list ps)"
        by (force simp: flat_binding_names_def fset_of_list_elem)
      thus ?thesis
        by (simp add: flat_binding_names_dec_pattern_var_bindings_list)
    qed
    have subset:
      "set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list (drop_at c ps)))
       \<subseteq> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps))"
      using dec_pattern_var_bindings_list_drop_at_subset by force
    show ?thesis
      using drop_with_bind(1) x_in_ps fset_of_list_subset[OF subset]
      by (auto simp: row_var_names_def
                     flat_binding_names_dec_pattern_var_bindings_list[symmetric]
                     flat_binding_names_def)
  next
    case (replace_with_bind vr x ty)
    \<comment> \<open>ps!c = DP_Var vr x ty (so x is in ps's pattern vars). new pattern list is
         replace_at c DP_Wildcard ps; bindings list of that = drop_at c ps's
         (the DP_Var's binding is removed). bs gains (vr,x,ty,s), so x is back in
         the row's name set. Net: new row's names \<subseteq> ps's names.\<close>
    have x_in_ps: "x |\<in>| dec_pattern_var_names_list ps"
    proof -
      have "(vr, x, ty) \<in> set (dec_pattern_var_bindings (ps ! c))"
        using replace_with_bind(2) by simp
      hence "(vr, x, ty) \<in> set (dec_pattern_var_bindings_list ps)"
        using assms(1) by (induction ps arbitrary: c) (auto simp: nth_Cons split: nat.splits)
      hence "x |\<in>| flat_binding_names (dec_pattern_var_bindings_list ps)"
        by (force simp: flat_binding_names_def fset_of_list_elem)
      thus ?thesis
        by (simp add: flat_binding_names_dec_pattern_var_bindings_list)
    qed
    have eq: "dec_pattern_var_bindings_list (replace_at c DP_Wildcard ps)
              = dec_pattern_var_bindings_list (drop_at c ps)"
      using dec_pattern_var_bindings_list_replace_at_DP_Wildcard_for_DP_Var[
              OF assms(1) replace_with_bind(2)] .
    have subset:
      "set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list (drop_at c ps)))
       \<subseteq> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps))"
      using dec_pattern_var_bindings_list_drop_at_subset by force
    show ?thesis
      using replace_with_bind(1) x_in_ps eq fset_of_list_subset[OF subset]
      by (auto simp: row_var_names_def
                     flat_binding_names_dec_pattern_var_bindings_list[symmetric]
                     flat_binding_names_def)
  qed
qed


subsection \<open>Helpers about distinct_bool_heads / distinct_int_heads / distinct_variant_heads\<close>

(* Each head from distinct_bool_heads col_pats appears in col_pats as DP_Bool h. *)
lemma distinct_bool_heads_in_col_pats:
  "h \<in> set (distinct_bool_heads ps) \<Longrightarrow> DP_Bool h \<in> set ps"
  by (induction ps rule: distinct_bool_heads.induct) (auto split: if_splits)

lemma distinct_int_heads_in_col_pats:
  "i \<in> set (distinct_int_heads ps) \<Longrightarrow> DP_Int i \<in> set ps"
  by (induction ps rule: distinct_int_heads.induct) (auto split: if_splits)

lemma distinct_variant_heads_in_col_pats:
  "(h, hp) \<in> set (distinct_variant_heads ps)
   \<Longrightarrow> \<exists>mpat. DP_Variant h mpat \<in> set ps \<and> hp = (mpat \<noteq> None)"
proof (induction ps rule: distinct_variant_heads.induct)
  case 1 thus ?case by simp
next
  case (2 h' mpat' rest)
  show ?case
  proof (cases "h = h' \<and> hp = (mpat' \<noteq> None)")
    case True thus ?thesis by auto
  next
    case False
    with "2.prems" have in_rest:
      "(h, hp) \<in> set (distinct_variant_heads
                        (filter (\<lambda>p. case p of DP_Variant h'' _ \<Rightarrow> h'' \<noteq> h' | _ \<Rightarrow> True) rest))"
      by auto
    from "2.IH"[OF in_rest] obtain mpat where
      mpat_in: "DP_Variant h mpat
                  \<in> set (filter (\<lambda>p. case p of DP_Variant h'' _ \<Rightarrow> h'' \<noteq> h' | _ \<Rightarrow> True) rest)"
      and hp_eq: "hp = (mpat \<noteq> None)" by auto
    from mpat_in have "DP_Variant h mpat \<in> set rest" by auto
    thus ?thesis using hp_eq by auto
  qed
qed (auto)

(* distinct_bool_heads produces distinct heads. *)
lemma distinct_bool_heads_distinct:
  "distinct (distinct_bool_heads ps)"
  by (induction ps rule: distinct_bool_heads.induct)
     (auto dest: distinct_bool_heads_in_col_pats)

lemma distinct_int_heads_distinct:
  "distinct (distinct_int_heads ps)"
  by (induction ps rule: distinct_int_heads.induct)
     (auto dest: distinct_int_heads_in_col_pats)

lemma distinct_variant_heads_distinct:
  "distinct (map fst (distinct_variant_heads ps))"
proof (induction ps rule: distinct_variant_heads.induct)
  case 1 thus ?case by simp
next
  case (2 h mpat rest)
  let ?filt = "filter (\<lambda>p. case p of DP_Variant h' _ \<Rightarrow> h' \<noteq> h | _ \<Rightarrow> True) rest"
  have h_not_in: "h \<notin> set (map fst (distinct_variant_heads ?filt))"
  proof
    assume "h \<in> set (map fst (distinct_variant_heads ?filt))"
    then obtain hp where in_set: "(h, hp) \<in> set (distinct_variant_heads ?filt)" by auto
    from distinct_variant_heads_in_col_pats[OF in_set] obtain mpat' where
      "DP_Variant h mpat' \<in> set ?filt" by auto
    thus False by auto
  qed
  show ?case
    using h_not_in "2.IH" by simp
qed (auto)


(* The headline theorem of Layer 1: compile_matrix produces a well-typed
   MatchTree given a well-typed input matrix. Combined with
   matchtree_to_term_preserves_typing, this gives the end-to-end guarantee
   that compile_match produces well-typed CoreTerms. *)
theorem compile_matrix_preserves_typing:
  assumes "matrix_term_well_typed env ghost resultTy (scruts, rows)"
      and "matrix_payload_consistent (scruts, rows)"
      and "tyenv_well_formed env"
      and "rows \<noteq> []"
  shows "matchtree_term_well_typed env ghost resultTy
           (compile_matrix (scruts, rows))"
  using assms
proof (induction "(scruts, rows)" arbitrary: scruts rows env ghost resultTy
       rule: compile_matrix.induct)
  case (1 scruts rows)
  from "1.prems"(1) obtain colTys where
    len_eq: "length colTys = length scruts" and
    scruts_typed:
      "list_all2 (\<lambda>s ty. core_term_type env ghost s = Some ty) scruts colTys" and
    rows_typed: "list_all (row_term_well_typed env ghost colTys resultTy) rows" and
    fresh_inv: "matrix_scrut_freshness (scruts, rows)"
    unfolding matrix_term_well_typed_def by auto

  \<comment> \<open>colTys are well-kinded, derived from scruts being well-typed in a
       well-formed env.\<close>
  have colTys_wk: "list_all (is_well_kinded env) colTys"
  proof -
    have "\<forall>i < length colTys. is_well_kinded env (colTys ! i)"
    proof (intro allI impI)
      fix i assume i_lt: "i < length colTys"
      from scruts_typed i_lt have
        "core_term_type env ghost (scruts ! i) = Some (colTys ! i)"
        by (simp add: list_all2_conv_all_nth)
      from core_term_type_well_kinded[OF this "1.prems"(3)]
      show "is_well_kinded env (colTys ! i)" .
    qed
    thus ?thesis
      by (simp add: list_all_length)
  qed

  show ?case
  proof (cases "first_non_wildcard_col (map (\<lambda>(ps, _, _). ps) rows)")
    case None
    \<comment> \<open>Base case: first_non_wildcard_col returned None, so all of row 0's
         columns are wildcard-like. Output binds_to_tree (bs @ extract_binds ...)
         with row 0's body.\<close>
    from "1.prems"(3) obtain ps0 bs0 body0 rest where
      rows_eq: "rows = (ps0, bs0, body0) # rest"
      by (metis "1.prems"(4) neq_Nil_conv surj_pair)
    \<comment> \<open>From row 0's well-typedness:\<close>
    from rows_typed rows_eq have
      row0_wt: "row_term_well_typed env ghost colTys resultTy (ps0, bs0, body0)"
      by (simp add: list_all_iff)
    from row0_wt have
      len_ps0: "length ps0 = length colTys" and
      bs0_wt: "bindlist_well_typed env ghost bs0" and
      distinct_ps0: "pattern_var_names_distinct ps0" and
      ps0_compat: "dec_pattern_compatible_list (extend_env_with_bindlist env ghost bs0)
                                                ps0 colTys" and
      body0_ty: "core_term_type
                   (extend_env_with_pattern_vars
                      (extend_env_with_bindlist env ghost bs0) ghost ps0)
                   ghost body0 = Some resultTy"
      by (auto simp: Let_def)

    \<comment> \<open>None branch of first_non_wildcard_col: row 0's columns are all wildcard-like.
         To derive this we need: all rows have pattern length = length ps0 (so the
         length-check inside first_non_wildcard_col passes, and we get the find=None).\<close>
    have all_rows_same_len:
      "list_all (\<lambda>r. length (fst r) = length ps0) rows"
    proof -
      have "\<forall>r \<in> set rows. length (fst r) = length ps0"
      proof
        fix r assume r_in: "r \<in> set rows"
        obtain rps rbs rbody where r_eq: "r = (rps, rbs, rbody)" by (cases r) auto
        from rows_typed r_in r_eq have
          "row_term_well_typed env ghost colTys resultTy (rps, rbs, rbody)"
          by (auto simp: list_all_iff)
        hence "length rps = length colTys" by (auto simp: Let_def)
        thus "length (fst r) = length ps0" using r_eq len_ps0 by simp
      qed
      thus ?thesis by (simp add: list_all_iff)
    qed
    have len_check_pass:
      "list_all (\<lambda>r. length r = length ps0) (map (\<lambda>(ps, _, _). ps) rows)"
      using all_rows_same_len
      by (induction rows) (auto simp: case_prod_unfold)
    have all_wc: "list_all is_wildcard_like ps0"
    proof -
      from None rows_eq len_check_pass have
        find_none: "find (\<lambda>c. \<not> is_wildcard_like (ps0 ! c)) [0 ..< length ps0] = None"
        by (auto simp: first_non_wildcard_col_def split: list.splits if_splits)
      have nth_wc: "\<forall>i < length ps0. is_wildcard_like (ps0 ! i)"
        using find_none
        by (metis atLeastLessThan_iff find_None_iff
                  set_upt zero_le)
      thus ?thesis
        by (auto simp: list_all_iff in_set_conv_nth)
    qed

    \<comment> \<open>compile_matrix unfolds to binds_to_tree (bs0 @ extract_binds scruts ps0) (MT_Leaf body0).\<close>
    have compile_eq:
      "compile_matrix (scruts, rows)
       = binds_to_tree (bs0 @ extract_binds scruts ps0) (MT_Leaf body0)"
      using None rows_eq by simp

    \<comment> \<open>Freshness: pattern var names of ps0 don't collide with any scrut's free vars.\<close>
    have scruts_fresh:
      "\<forall>s \<in> set scruts. dec_pattern_var_names_list ps0
                          |\<inter>| core_term_free_vars s = {||}"
    proof
      fix s assume s_in: "s \<in> set scruts"
      from fresh_inv s_in rows_eq have
        "core_term_free_vars s |\<inter>| row_var_names (ps0, bs0, body0) = {||}"
        by (auto simp: matrix_scrut_freshness_def)
      thus "dec_pattern_var_names_list ps0 |\<inter>| core_term_free_vars s = {||}"
        by (auto simp: row_var_names_def inf_commute inf_sup_distrib1)
    qed

    \<comment> \<open>extract_binds produces a well-typed BindList.\<close>
    have extract_wt:
      "bindlist_well_typed (extend_env_with_bindlist env ghost bs0) ghost
         (extract_binds scruts ps0)"
    proof -
      have len_pat_scruts: "length ps0 = length scruts" using len_ps0 len_eq by simp
      have scruts_typed_in_bs:
        "list_all2 (\<lambda>s ty. core_term_type
                            (extend_env_with_bindlist env ghost bs0) ghost s
                            = Some ty) scruts colTys"
      proof (rule list_all2_all_nthI)
        show "length scruts = length colTys" using len_eq by simp
      next
        fix i assume i_lt: "i < length scruts"
        from scruts_typed i_lt have
          si_ty: "core_term_type env ghost (scruts ! i) = Some (colTys ! i)"
          by (simp add: list_all2_conv_all_nth)
        \<comment> \<open>The scrut at index i has free vars disjoint from bs0's bind names
             (from fresh_inv).\<close>
        have si_fresh: "fset_of_list (map (\<lambda>(_, x, _, _). x) bs0)
                          |\<inter>| core_term_free_vars (scruts ! i) = {||}"
        proof -
          from fresh_inv i_lt have
            "core_term_free_vars (scruts ! i)
              |\<inter>| row_var_names (ps0, bs0, body0) = {||}"
            using rows_eq by (auto simp: matrix_scrut_freshness_def)
          thus ?thesis
            by (auto simp: row_var_names_def inf_commute inf_sup_distrib1)
        qed
        show "core_term_type
                (extend_env_with_bindlist env ghost bs0) ghost (scruts ! i)
                = Some (colTys ! i)"
          using core_term_type_extend_env_with_bindlist_irrelevant[OF si_fresh si_ty] .
      qed
      show ?thesis
        using extract_binds_well_typed[OF all_wc len_pat_scruts scruts_typed_in_bs
                                          len_eq ps0_compat scruts_fresh] .
    qed

    \<comment> \<open>The body's type holds in env extended by bs0 @ extract_binds (since
         extract_binds extends env by ps0's pattern vars).\<close>
    have body_ty_in_full_env:
      "core_term_type
         (extend_env_with_bindlist env ghost (bs0 @ extract_binds scruts ps0))
         ghost body0 = Some resultTy"
    proof -
      \<comment> \<open>extend_env_with_bindlist (bs0 @ extract_binds scruts ps0) =
            extend_env_with_pattern_vars (extend_env_with_bindlist bs0) ps0,
          since extract_binds scruts ps0 just enumerates ps0's DP_Var bindings.\<close>
      have key:
        "extend_env_with_bindlist env ghost (bs0 @ extract_binds scruts ps0)
         = extend_env_with_pattern_vars
             (extend_env_with_bindlist env ghost bs0) ghost ps0"
      proof -
        have step:
          "\<And>e. extend_env_with_bindlist e ghost (extract_binds scruts ps0)
              = extend_env_with_pattern_vars e ghost ps0"
        proof -
          fix e
          have len_pat_scruts: "length ps0 = length scruts" using len_ps0 len_eq by simp
          show "extend_env_with_bindlist e ghost (extract_binds scruts ps0)
                = extend_env_with_pattern_vars e ghost ps0"
            using all_wc len_pat_scruts distinct_ps0
          proof (induction scruts ps0 arbitrary: e rule: extract_binds.induct)
            case 1 thus ?case
              by (simp add: extend_env_with_pattern_vars_def)
          next
            case (2 s ss vr x ty ps)
            \<comment> \<open>x is not in dec_pattern_var_names_list ps (from distinctness).\<close>
            from "2.prems"(3) have x_not_in_rest:
              "x |\<notin>| flat_binding_names (dec_pattern_var_bindings_list ps)"
            proof -
              from "2.prems"(3) have
                "distinct (map (\<lambda>(_, x, _). x)
                            (dec_pattern_var_bindings_list (DP_Var vr x ty # ps)))"
                by (simp add: pattern_var_names_distinct_def)
              hence "x \<notin> set (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps))"
                by simp
              thus ?thesis
                by (simp add: flat_binding_names_def fset_of_list.rep_eq)
            qed
            from "2.prems"(1) have rest_wc: "list_all is_wildcard_like ps"
              by (simp add: list_all_iff)
            from "2.prems"(2) have rest_len: "length ps = length ss" by simp
            from "2.prems"(3) have rest_distinct: "pattern_var_names_distinct ps"
              by (auto simp: pattern_var_names_distinct_def)
            from "2.IH"[OF rest_wc rest_len rest_distinct]
            have IH_eq: "\<And>e'. extend_env_with_bindlist e' ghost (extract_binds ss ps)
                        = extend_env_with_pattern_vars e' ghost ps" by simp
            \<comment> \<open>LHS: extend_env_with_bind e ghost x ty, then fold over extract_binds ss ps.
                 By IH, equals extend_env_with_pattern_vars (extend_env_with_bind e x ty) ps
                       = extend_env_flat (extend_env_with_bind e x ty) (dec_pattern_var_bindings_list ps)
                 By swap (x not in rest), equals
                       extend_env_with_bind (extend_env_flat e (dec_pattern_var_bindings_list ps)) x ty
                       = extend_env_with_bind (extend_env_with_pattern_vars e ghost ps) ghost x ty
                       = extend_env_with_pattern_vars e ghost (DP_Var vr x ty # ps).\<close>
            have lhs:
              "extend_env_with_bindlist e ghost (extract_binds (s # ss) (DP_Var vr x ty # ps))
               = extend_env_with_bindlist (extend_env_with_bind e ghost x ty) ghost
                   (extract_binds ss ps)"
              by simp
            also have "\<dots> = extend_env_with_pattern_vars
                              (extend_env_with_bind e ghost x ty) ghost ps"
              using IH_eq .
            also have "\<dots> = extend_env_flat (extend_env_with_bind e ghost x ty) ghost
                              (dec_pattern_var_bindings_list ps)"
              by (simp add: extend_env_with_pattern_vars_eq_flat)
            also have "\<dots> = extend_env_with_bind
                              (extend_env_flat e ghost (dec_pattern_var_bindings_list ps))
                              ghost x ty"
              using extend_env_flat_extend_env_with_bind_swap[OF x_not_in_rest] .
            also have "\<dots> = extend_env_with_bind (extend_env_with_pattern_vars e ghost ps)
                              ghost x ty"
              by (simp add: extend_env_with_pattern_vars_eq_flat)
            also have "\<dots> = extend_env_with_pattern_vars e ghost (DP_Var vr x ty # ps)"
              by (simp add: extend_env_with_pattern_vars_def)
            finally show ?case .
          next
            case (3 s ss ps)
            from "3.prems"(1) have rest_wc: "list_all is_wildcard_like ps"
              by (simp add: list_all_iff)
            from "3.prems"(2) have rest_len: "length ps = length ss" by simp
            from "3.prems"(3) have rest_distinct: "pattern_var_names_distinct ps"
              by (auto simp: pattern_var_names_distinct_def)
            from "3.IH"[OF rest_wc rest_len rest_distinct]
            have IH_eq: "\<And>e'. extend_env_with_bindlist e' ghost (extract_binds ss ps)
                        = extend_env_with_pattern_vars e' ghost ps" by simp
            show ?case
              using IH_eq[of e]
              by (simp add: extend_env_with_pattern_vars_def)
          qed (auto simp: list_all_iff)
        qed
        show ?thesis
          using step[of "extend_env_with_bindlist env ghost bs0"]
          by (simp add: extend_env_with_bindlist_append)
      qed
      show ?thesis using body0_ty key by simp
    qed

    \<comment> \<open>The MT_Leaf body0 is well-typed in the full env.\<close>
    have leaf_wt:
      "matchtree_term_well_typed
         (extend_env_with_bindlist env ghost (bs0 @ extract_binds scruts ps0))
         ghost resultTy (MT_Leaf body0)"
      using body_ty_in_full_env by simp

    \<comment> \<open>The full bindlist is well-typed: bs0 first, then extract_binds in extended env.\<close>
    have full_bs_wt:
      "bindlist_well_typed env ghost (bs0 @ extract_binds scruts ps0)"
      using bs0_wt extract_wt by (simp add: bindlist_well_typed_append)

    \<comment> \<open>Apply binds_to_tree_preserves_typing.\<close>
    show ?thesis
      unfolding compile_eq
      using binds_to_tree_preserves_typing[OF full_bs_wt leaf_wt] .

  next
    case (Some c)
    note fnw = Some
    \<comment> \<open>Recursive case: split on head_kind_of for the recursive arms.\<close>
    \<comment> \<open>Common facts about the c-th column.\<close>
    let ?col_pats = "map (\<lambda>(ps, _, _). ps ! c) rows"
    let ?s_c = "scruts ! c"
    let ?has_default = "list_ex is_wildcard_like ?col_pats"
    let ?default_rows = "List.map_filter (default_row c ?s_c) rows"
    let ?default_arm = "(if ?has_default
                          then [(CorePat_Wildcard,
                                 compile_matrix (drop_at c scruts, ?default_rows))]
                          else [])"

    \<comment> \<open>From first_non_wildcard_col Some c: c < length r for each row, and
         there exists a row whose c-th pattern is non-wildcard-like.\<close>
    have c_facts: "rows \<noteq> []
                    \<and> (\<forall>r \<in> set rows. c < length (fst r))
                    \<and> (\<exists>r \<in> set rows. \<not> is_wildcard_like (fst r ! c))"
    proof -
      from Some have res: "first_non_wildcard_col (map (\<lambda>(ps, _, _). ps) rows) = Some c" .
      note D = first_non_wildcard_col_SomeD[OF res]
      have ne: "rows \<noteq> []" using D(1) by (cases rows) auto
      have all_lt: "\<forall>r \<in> set rows. c < length (fst r)"
      proof
        fix r assume r_in: "r \<in> set rows"
        obtain rps rbs rbody where r_eq: "r = (rps, rbs, rbody)" by (cases r) auto
        have rps_in: "rps \<in> set (map (\<lambda>(ps, _, _). ps) rows)"
          using r_in r_eq by force
        from D(2) rps_in have "c < length rps" by auto
        thus "c < length (fst r)" using r_eq by simp
      qed
      have ex_nw: "\<exists>r \<in> set rows. \<not> is_wildcard_like (fst r ! c)"
      proof -
        from D(3) obtain ps_nw where ps_nw_in: "ps_nw \<in> set (map (\<lambda>(ps, _, _). ps) rows)"
          and nw: "\<not> is_wildcard_like (ps_nw ! c)" by blast
        from ps_nw_in obtain r where r_in: "r \<in> set rows" and r_pat: "fst r = ps_nw"
          by force
        thus ?thesis using nw by auto
      qed
      show ?thesis using ne all_lt ex_nw by blast
    qed
    have c_lt_scruts: "c < length scruts"
    proof -
      from "1.prems"(3) obtain r where r_in: "r \<in> set rows"
        by (metis "1.prems"(4) list.exhaust list.set_intros(1))
      obtain rps rbs rbody where r_eq: "r = (rps, rbs, rbody)" by (cases r) auto
      from rows_typed r_in r_eq have
        "row_term_well_typed env ghost colTys resultTy (rps, rbs, rbody)"
        by (auto simp: list_all_iff)
      hence "length rps = length colTys" by (auto simp: Let_def)
      moreover from c_facts r_in r_eq have "c < length rps" by auto
      ultimately show ?thesis using len_eq by simp
    qed
    have c_lt_colTys: "c < length colTys" using c_lt_scruts len_eq by simp

    \<comment> \<open>Some-c recursive case. Get the representative non-wildcard pattern
         and dispatch on its head_kind. From c_facts we know
         filter (\<not> is_wildcard_like) col_pats is non-empty.\<close>

    have ex_nw_in_col_pats: "\<exists>p \<in> set ?col_pats. \<not> is_wildcard_like p"
    proof -
      from c_facts obtain r where r_in: "r \<in> set rows"
        and r_nw: "\<not> is_wildcard_like (fst r ! c)" by blast
      obtain rps rbs rbody where r_eq: "r = (rps, rbs, rbody)" by (cases r) auto
      have "rps ! c \<in> set ?col_pats" using r_in r_eq by force
      thus ?thesis using r_nw r_eq by force
    qed

    obtain head_pat where
      head_pat_eq:
        "head_pat = hd (filter (\<lambda>p. \<not> is_wildcard_like p) ?col_pats)" and
      head_pat_in_col: "head_pat \<in> set ?col_pats" and
      head_pat_nw: "\<not> is_wildcard_like head_pat"
    proof -
      let ?fc = "filter (\<lambda>p. \<not> is_wildcard_like p) ?col_pats"
      from ex_nw_in_col_pats have fc_ne: "?fc \<noteq> []" by (simp add: filter_empty_conv)
      hence hd_in_fc: "hd ?fc \<in> set ?fc" by (cases ?fc) auto
      hence "hd ?fc \<in> set ?col_pats \<and> \<not> is_wildcard_like (hd ?fc)" by auto
      thus thesis using that[of "hd ?fc"] by simp
    qed

    show ?thesis
    proof (cases "head_kind_of head_pat")
      case None
      \<comment> \<open>Unreachable: head_pat is non-wildcard, so head_kind_of head_pat is Some.\<close>
      from None head_pat_nw show ?thesis by (cases head_pat) auto
    next
      case (Some hk)
      show ?thesis
      proof (cases hk)
        case (HK_Record fld_names_hk)
        \<comment> \<open>Record case: head_pat = DP_Record flds with fld_names_hk = map fst flds.
             compile_matrix recurses on the expanded matrix.\<close>
        from Some HK_Record obtain flds where head_pat_eq2:
          "head_pat = DP_Record flds" and fld_names_hk_eq:
          "fld_names_hk = map fst flds"
          by (cases head_pat) auto

        \<comment> \<open>Find a row with c-th pattern = head_pat to derive the column type.\<close>
        from head_pat_in_col obtain r_rec where r_rec_in: "r_rec \<in> set rows"
          and r_rec_pat: "fst r_rec ! c = head_pat" by force
        obtain rps_rec rbs_rec rbody_rec where r_rec_eq:
          "r_rec = (rps_rec, rbs_rec, rbody_rec)" by (cases r_rec) auto
        from rows_typed r_rec_in r_rec_eq have
          rec_row_wt: "row_term_well_typed env ghost colTys resultTy
                         (rps_rec, rbs_rec, rbody_rec)"
          by (auto simp: list_all_iff)
        from rec_row_wt have
          rec_compat: "dec_pattern_compatible_list
                         (extend_env_with_bindlist env ghost rbs_rec)
                         rps_rec colTys"
          and rec_len: "length rps_rec = length colTys"
          by (auto simp: Let_def)
        have rec_c: "rps_rec ! c = DP_Record flds"
          using r_rec_pat r_rec_eq head_pat_eq2 by simp
        have rec_compat_at_c: "dec_pattern_compatible
                                  (extend_env_with_bindlist env ghost rbs_rec)
                                  (DP_Record flds) (colTys ! c)"
          using rec_compat c_lt_colTys rec_len rec_c dec_pattern_compatible_list_iff
          by auto
        \<comment> \<open>From DP_Record compatibility: colTys ! c = CoreTy_Record fieldTypes,
             map fst flds = map fst fieldTypes.\<close>
        from rec_compat_at_c obtain fieldTypes where
          colTy_c: "colTys ! c = CoreTy_Record fieldTypes" and
          fld_names_match: "map fst flds = map fst fieldTypes"
          by (cases "colTys ! c") (auto split: option.splits)
        from fld_names_match fld_names_hk_eq have fld_names_hk_eq_fields:
          "fld_names_hk = map fst fieldTypes" by simp

        \<comment> \<open>Well-kindedness gives field-name distinctness and well-kinded field types.\<close>
        have colTy_c_wk: "is_well_kinded env (CoreTy_Record fieldTypes)"
          using colTys_wk c_lt_colTys colTy_c
          by (metis list_all_length)
        have fld_distinct: "distinct (map fst fieldTypes)"
          using colTy_c_wk by simp
        have fld_tys_wk: "list_all (is_well_kinded env) (map snd fieldTypes)"
          using colTy_c_wk by simp

        \<comment> \<open>The compile_matrix unfolds for this case.\<close>
        have hd_eq: "hd (filter (\<lambda>p. \<not> is_wildcard_like p) ?col_pats) = head_pat"
          using head_pat_eq by blast
        have head_kind_eq: "head_kind_of head_pat = Some (HK_Record fld_names_hk)"
          using Some HK_Record by simp
        have compile_eq:
          "compile_matrix (scruts, rows)
           = compile_matrix (expand_record_scruts c ?s_c fld_names_hk scruts,
                             map (expand_record_row c ?s_c fld_names_hk) rows)"
          using compile_matrix_unfold_record[OF fnw hd_eq head_kind_eq] .

        let ?new_scruts = "expand_record_scruts c ?s_c fld_names_hk scruts"
        let ?new_rows = "map (expand_record_row c ?s_c fld_names_hk) rows"
        let ?new_colTys = "splice_at c (map snd fieldTypes) colTys"

        \<comment> \<open>The new scruts typecheck against the new colTys.\<close>
        have s_c_ty: "core_term_type env ghost ?s_c = Some (CoreTy_Record fieldTypes)"
          using scruts_typed c_lt_scruts colTy_c
          by (auto simp: list_all2_conv_all_nth)

        let ?proj_scruts = "map (\<lambda>f. CoreTm_RecordProj ?s_c f) fld_names_hk"
        have new_scruts_def: "?new_scruts = splice_at c ?proj_scruts scruts"
          unfolding expand_record_scruts_def by simp

        have proj_typed:
          "list_all2 (\<lambda>s ty. core_term_type env ghost s = Some ty)
             ?proj_scruts (map snd fieldTypes)"
        proof (rule list_all2_all_nthI)
          show "length ?proj_scruts = length (map snd fieldTypes)"
            using fld_names_hk_eq_fields by simp
        next
          fix i assume i_lt: "i < length ?proj_scruts"
          have i_lt_flds: "i < length fieldTypes"
            using i_lt fld_names_hk_eq_fields by simp
          have proj_i: "?proj_scruts ! i = CoreTm_RecordProj ?s_c (fld_names_hk ! i)"
            using i_lt by simp
          have fld_name_i: "fld_names_hk ! i = fst (fieldTypes ! i)"
            using fld_names_hk_eq_fields i_lt_flds by (metis nth_map)
          have map_of_lookup:
            "map_of fieldTypes (fst (fieldTypes ! i)) = Some (snd (fieldTypes ! i))"
            using fld_distinct i_lt_flds
            by (metis map_of_eq_Some_iff nth_mem prod.collapse)
          show "core_term_type env ghost (?proj_scruts ! i) = Some (map snd fieldTypes ! i)"
            using proj_i s_c_ty fld_name_i map_of_lookup i_lt_flds
            by simp
        qed

        have new_scruts_typed:
          "list_all2 (\<lambda>s ty. core_term_type env ghost s = Some ty) ?new_scruts ?new_colTys"
          unfolding new_scruts_def
          using list_all2_splice_at[OF scruts_typed c_lt_scruts proj_typed] .

        \<comment> \<open>The new colTys are well-kinded.\<close>
        have new_colTys_wk: "list_all (is_well_kinded env) ?new_colTys"
          using list_all_splice_at[OF colTys_wk fld_tys_wk] .

        \<comment> \<open>Each new row is well-typed.\<close>
        have new_rows_typed:
          "list_all (row_term_well_typed env ghost ?new_colTys resultTy) ?new_rows"
        proof -
          have "\<forall>row \<in> set ?new_rows.
                  row_term_well_typed env ghost ?new_colTys resultTy row"
          proof
            fix new_row assume new_row_in: "new_row \<in> set ?new_rows"
            then obtain orig_row where
              orig_in: "orig_row \<in> set rows" and
              new_row_eq: "new_row = expand_record_row c ?s_c fld_names_hk orig_row"
              by auto
            obtain ops obs obody where
              orig_row_eq: "orig_row = (ops, obs, obody)" by (cases orig_row) auto
            from rows_typed orig_in orig_row_eq have
              orig_row_wt: "row_term_well_typed env ghost colTys resultTy (ops, obs, obody)"
              by (auto simp: list_all_iff)
            \<comment> \<open>The freshness condition for this row.\<close>
            from fresh_inv orig_in c_lt_scruts have
              s_c_fresh_row: "core_term_free_vars ?s_c
                              |\<inter>| row_var_names orig_row = {||}"
              by (auto simp: matrix_scrut_freshness_def)
            with orig_row_eq have row_fresh_s_c:
              "core_term_free_vars ?s_c |\<inter>| row_var_names (ops, obs, obody) = {||}"
              by simp
            have new_row_eq2:
              "new_row = expand_record_row c ?s_c fld_names_hk (ops, obs, obody)"
              using new_row_eq orig_row_eq by simp
            show "row_term_well_typed env ghost ?new_colTys resultTy new_row"
              unfolding new_row_eq2
              using expand_record_row_preserves_typing[OF orig_row_wt c_lt_colTys colTy_c
                                                          _ row_fresh_s_c
                                                          fld_names_hk_eq_fields]
                    s_c_ty colTy_c
              by simp
          qed
          thus ?thesis by (simp add: list_all_iff)
        qed

        \<comment> \<open>Matrix scrut freshness preserved.\<close>
        have new_fresh: "matrix_scrut_freshness (?new_scruts, ?new_rows)"
          unfolding matrix_scrut_freshness_def
        proof clarify
          fix s :: CoreTerm and new_row :: "CoreTerm Row"
          assume s_in: "s \<in> set ?new_scruts"
             and new_row_in: "new_row \<in> set ?new_rows"
          \<comment> \<open>Get the original row.\<close>
          from new_row_in obtain orig_row where
            orig_in: "orig_row \<in> set rows" and
            new_row_eq: "new_row = expand_record_row c ?s_c fld_names_hk orig_row"
            by auto
          obtain ops obs obody where
            orig_row_eq: "orig_row = (ops, obs, obody)" by (cases orig_row) auto
          have c_lt_ops: "c < length ops"
            using c_facts orig_in orig_row_eq by auto
          have row_var_names_subset:
            "row_var_names new_row |\<subseteq>| row_var_names orig_row"
            using new_row_eq orig_row_eq
                  row_var_names_expand_record_row_subset[OF c_lt_ops, of ?s_c fld_names_hk obs obody]
            by simp

          \<comment> \<open>For each new scrut s, its free vars are either an original scrut's
               free vars, or s_c's free vars (which is one of the original scruts).\<close>
          have new_scruts_unfold: "?new_scruts = splice_at c
                (map (\<lambda>f. CoreTm_RecordProj ?s_c f) fld_names_hk) scruts"
            unfolding expand_record_scruts_def by simp
          have splice_set_subset:
            "set ?new_scruts \<subseteq> set scruts \<union>
                set (map (\<lambda>f. CoreTm_RecordProj ?s_c f) fld_names_hk)"
          proof -
            have "set (splice_at c (map (\<lambda>f. CoreTm_RecordProj ?s_c f) fld_names_hk) scruts)
                  \<subseteq> set scruts \<union> set (map (\<lambda>f. CoreTm_RecordProj ?s_c f) fld_names_hk)"
              by (induction c "(map (\<lambda>f. CoreTm_RecordProj ?s_c f) fld_names_hk)" scruts
                          rule: splice_at.induct) auto
            thus ?thesis using new_scruts_unfold by simp
          qed
          have s_orig_or_proj:
            "s \<in> set scruts \<or>
             (\<exists>f. s = CoreTm_RecordProj ?s_c f)"
            using s_in splice_set_subset by auto

          have s_c_in: "?s_c \<in> set scruts" using c_lt_scruts by simp

          have s_free_subset:
            "\<exists>orig_s \<in> set scruts. core_term_free_vars s |\<subseteq>| core_term_free_vars orig_s"
          proof (cases "s \<in> set scruts")
            case True
            thus ?thesis by auto
          next
            case False
            with s_orig_or_proj obtain f where
              s_eq: "s = CoreTm_RecordProj ?s_c f" by blast
            have s_free: "core_term_free_vars s = core_term_free_vars ?s_c"
              using s_eq by simp
            show ?thesis using s_free s_c_in by force
          qed
          obtain orig_s where orig_s_in: "orig_s \<in> set scruts"
            and free_subset: "core_term_free_vars s |\<subseteq>| core_term_free_vars orig_s"
            using s_free_subset by blast
          from fresh_inv orig_s_in orig_in have
            "core_term_free_vars orig_s |\<inter>| row_var_names orig_row = {||}"
            by (auto simp: matrix_scrut_freshness_def)
          with free_subset row_var_names_subset
          show "core_term_free_vars s |\<inter>| row_var_names new_row = {||}"
            by blast
        qed

        \<comment> \<open>Combine into matrix_term_well_typed.\<close>
        have new_matrix_wt:
          "matrix_term_well_typed env ghost resultTy (?new_scruts, ?new_rows)"
          unfolding matrix_term_well_typed_def
          using new_scruts_typed new_colTys_wk new_rows_typed new_fresh
          by (auto simp: list_all2_lengthD)

        \<comment> \<open>Payload-consistent preserved: row_all_variants of the new row
             is a subset of the original row's, so the invariant lifts.\<close>
        have new_payload: "matrix_payload_consistent (?new_scruts, ?new_rows)"
          unfolding matrix_payload_consistent_def
        proof clarify
          fix new_row1 :: "CoreTerm Row" and new_row2 :: "CoreTerm Row"
          fix h mpat1 mpat2
          assume nr1_in: "new_row1 \<in> set ?new_rows"
             and nr2_in: "new_row2 \<in> set ?new_rows"
             and v1: "(h, mpat1) \<in> row_all_variants new_row1"
             and v2: "(h, mpat2) \<in> row_all_variants new_row2"
          from nr1_in obtain orig_row1 where
            o1_in: "orig_row1 \<in> set rows" and
            nr1_eq: "new_row1 = expand_record_row c ?s_c fld_names_hk orig_row1"
            by auto
          from nr2_in obtain orig_row2 where
            o2_in: "orig_row2 \<in> set rows" and
            nr2_eq: "new_row2 = expand_record_row c ?s_c fld_names_hk orig_row2"
            by auto
          obtain o1ps o1bs o1body where o1_eq:
            "orig_row1 = (o1ps, o1bs, o1body)" by (cases orig_row1) auto
          obtain o2ps o2bs o2body where o2_eq:
            "orig_row2 = (o2ps, o2bs, o2body)" by (cases orig_row2) auto
          have c_lt_o1: "c < length o1ps"
            using c_facts o1_in o1_eq by auto
          have c_lt_o2: "c < length o2ps"
            using c_facts o2_in o2_eq by auto
          have v1_orig: "(h, mpat1) \<in> row_all_variants orig_row1"
            using v1 nr1_eq o1_eq
                  row_all_variants_expand_record_row_subset[OF c_lt_o1, of ?s_c fld_names_hk o1bs o1body]
            by auto
          have v2_orig: "(h, mpat2) \<in> row_all_variants orig_row2"
            using v2 nr2_eq o2_eq
                  row_all_variants_expand_record_row_subset[OF c_lt_o2, of ?s_c fld_names_hk o2bs o2body]
            by auto
          show "(mpat1 = None) = (mpat2 = None)"
            using "1.prems"(2) o1_in o2_in v1_orig v2_orig
            unfolding matrix_payload_consistent_def
            by blast
        qed

        have new_rows_ne: "?new_rows \<noteq> []" using "1.prems"(3) by (simp add: "1.prems"(4))

        \<comment> \<open>Apply the IH for the record branch.\<close>
        have hd_head_kind:
          "head_kind_of (hd (filter (\<lambda>p. \<not> is_wildcard_like p) ?col_pats))
           = Some (HK_Record fld_names_hk)"
          using hd_eq head_kind_eq by simp

        have IH:
          "matchtree_term_well_typed env ghost resultTy
            (compile_matrix (?new_scruts, ?new_rows))"
          using "1.hyps"(2)[OF fnw refl refl refl refl refl hd_head_kind refl
                              new_matrix_wt new_payload "1.prems"(3) new_rows_ne] .

        show ?thesis
          unfolding compile_eq using IH .
      next
        case HK_Bool
        \<comment> \<open>Bool case: MT_Test with arms for each distinct bool head + optional default.
             The column type at c is CoreTy_Bool (from any DP_Bool pattern's compatibility).\<close>
        \<comment> \<open>head_pat is DP_Bool b for some b.\<close>
        from Some HK_Bool obtain b where head_pat_eq2: "head_pat = DP_Bool b"
          by (cases head_pat) auto
        have head_kind_eq: "head_kind_of head_pat = Some HK_Bool"
          using Some HK_Bool by simp
        have hd_eq: "hd (filter (\<lambda>p. \<not> is_wildcard_like p) ?col_pats) = head_pat"
          using head_pat_eq by blast

        \<comment> \<open>Find a row whose c-th pattern is head_pat to derive col c's type.\<close>
        from head_pat_in_col obtain r_b where r_b_in: "r_b \<in> set rows"
          and r_b_pat: "fst r_b ! c = head_pat" by force
        obtain rps_b rbs_b rbody_b where r_b_eq:
          "r_b = (rps_b, rbs_b, rbody_b)" by (cases r_b) auto
        from rows_typed r_b_in r_b_eq have
          b_row_wt: "row_term_well_typed env ghost colTys resultTy
                       (rps_b, rbs_b, rbody_b)"
          by (auto simp: list_all_iff)
        from b_row_wt have
          b_compat: "dec_pattern_compatible_list
                       (extend_env_with_bindlist env ghost rbs_b)
                       rps_b colTys"
          and b_len: "length rps_b = length colTys"
          by (auto simp: Let_def)
        have b_c: "rps_b ! c = DP_Bool b"
          using r_b_pat r_b_eq head_pat_eq2 by simp
        have c_lt_b: "c < length rps_b" using c_lt_colTys b_len by simp
        have b_compat_at_c: "dec_pattern_compatible
                                (extend_env_with_bindlist env ghost rbs_b)
                                (rps_b ! c) (colTys ! c)"
          using b_compat c_lt_b b_len
          by (auto simp: dec_pattern_compatible_list_iff)
        with b_c have colTy_c_bool: "colTys ! c = CoreTy_Bool" by simp

        \<comment> \<open>s_c typechecks at CoreTy_Bool.\<close>
        have s_c_ty: "core_term_type env ghost ?s_c = Some CoreTy_Bool"
          using scruts_typed c_lt_scruts colTy_c_bool
          by (auto simp: list_all2_conv_all_nth)

        \<comment> \<open>The compile_matrix unfolds to MT_Test.\<close>
        have compile_eq:
          "compile_matrix (scruts, rows)
           = (let s_c = ?s_c;
                  col_pats = ?col_pats;
                  has_default = list_ex is_wildcard_like col_pats;
                  default_rows = List.map_filter (default_row c s_c) rows;
                  default_arm =
                    (if has_default
                     then [(CorePat_Wildcard,
                            compile_matrix (drop_at c scruts, default_rows))]
                     else []);
                  heads = distinct_bool_heads col_pats;
                  head_arm = (\<lambda>h.
                    (CorePat_Bool h,
                     compile_matrix (drop_at c scruts,
                       List.map_filter (specialise_row_bool c s_c h) rows)))
              in MT_Test s_c (map head_arm heads @ default_arm))"
          using compile_matrix_unfold_bool[OF fnw hd_eq head_kind_eq] .

        let ?heads = "distinct_bool_heads ?col_pats"
        let ?head_arm = "\<lambda>h. (CorePat_Bool h,
                              compile_matrix (drop_at c scruts,
                                List.map_filter (specialise_row_bool c ?s_c h) rows))"

        \<comment> \<open>Common preconditions for the recursive calls in this branch.\<close>
        have head_kind_at_hd: "head_kind_of (hd (filter (\<lambda>p. \<not> is_wildcard_like p) ?col_pats))
                                = Some HK_Bool"
          using hd_eq head_kind_eq by simp

        \<comment> \<open>Show each head arm is well-typed.\<close>
        have head_arm_wt:
          "\<forall>h \<in> set ?heads.
             matchtree_term_well_typed env ghost resultTy
               (compile_matrix (drop_at c scruts,
                  List.map_filter (specialise_row_bool c ?s_c h) rows))"
        proof
          fix h assume h_in: "h \<in> set ?heads"
          let ?spec_rows = "List.map_filter (specialise_row_bool c ?s_c h) rows"
          let ?new_colTys = "drop_at c colTys"

          \<comment> \<open>specialise_row_bool preserves typing for each row.\<close>
          have spec_rows_typed:
            "list_all (row_term_well_typed env ghost ?new_colTys resultTy) ?spec_rows"
          proof -
            have "\<forall>new_row \<in> set ?spec_rows.
                    row_term_well_typed env ghost ?new_colTys resultTy new_row"
            proof
              fix new_row assume "new_row \<in> set ?spec_rows"
              then obtain orig_row where orig_in: "orig_row \<in> set rows"
                and spec_some: "specialise_row_bool c ?s_c h orig_row = Some new_row"
                by (auto simp: List.map_filter_def)
              obtain ops obs obody where
                orig_row_eq: "orig_row = (ops, obs, obody)" by (cases orig_row) auto
              from rows_typed orig_in orig_row_eq have
                orig_wt: "row_term_well_typed env ghost colTys resultTy (ops, obs, obody)"
                by (auto simp: list_all_iff)
              from fresh_inv orig_in c_lt_scruts orig_row_eq have
                row_fresh: "row_scrut_fresh ?s_c (ops, obs, obody)"
                by (auto simp: matrix_scrut_freshness_def)
              show "row_term_well_typed env ghost ?new_colTys resultTy new_row"
                using specialise_row_bool_preserves_typing[
                          OF orig_wt c_lt_colTys colTy_c_bool s_c_ty row_fresh]
                      spec_some orig_row_eq
                by simp
            qed
            thus ?thesis by (simp add: list_all_iff)
          qed

          \<comment> \<open>Scruts after drop_at typecheck.\<close>
          have new_scruts_typed:
            "list_all2 (\<lambda>s ty. core_term_type env ghost s = Some ty)
                       (drop_at c scruts) ?new_colTys"
            using list_all2_drop_at[OF scruts_typed c_lt_scruts] .

          have new_colTys_wk: "list_all (is_well_kinded env) ?new_colTys"
            using list_all_drop_at[OF colTys_wk] .

          \<comment> \<open>Freshness: scrut freshness preserved under drop_at + filter.\<close>
          have new_fresh: "matrix_scrut_freshness (drop_at c scruts, ?spec_rows)"
            unfolding matrix_scrut_freshness_def
          proof clarify
            fix s :: CoreTerm and new_row :: "CoreTerm Row"
            assume s_in: "s \<in> set (drop_at c scruts)" and nr_in: "new_row \<in> set ?spec_rows"
            from s_in have s_in_orig: "s \<in> set scruts"
              by (induction c scruts rule: drop_at.induct) auto
            from nr_in obtain orig_row where
              orig_in: "orig_row \<in> set rows" and
              spec_some: "specialise_row_bool c ?s_c h orig_row = Some new_row"
              by (auto simp: List.map_filter_def)
            obtain ops obs obody where
              orig_row_eq: "orig_row = (ops, obs, obody)" by (cases orig_row) auto
            have c_lt_ops: "c < length ops"
              using c_facts orig_in orig_row_eq by auto
            have row_subset:
              "row_var_names new_row |\<subseteq>| row_var_names orig_row"
              using row_var_names_specialise_row_bool_subset[OF c_lt_ops]
                    spec_some orig_row_eq by simp
            from fresh_inv s_in_orig orig_in have
              "core_term_free_vars s |\<inter>| row_var_names orig_row = {||}"
              by (auto simp: matrix_scrut_freshness_def)
            with row_subset show "core_term_free_vars s |\<inter>| row_var_names new_row = {||}"
              by blast
          qed

          \<comment> \<open>Combine into matrix_term_well_typed.\<close>
          have new_matrix_wt:
            "matrix_term_well_typed env ghost resultTy (drop_at c scruts, ?spec_rows)"
            unfolding matrix_term_well_typed_def
            using new_scruts_typed new_colTys_wk spec_rows_typed new_fresh
            by (auto simp: list_all2_lengthD)

          \<comment> \<open>Payload consistency preserved.\<close>
          have new_payload: "matrix_payload_consistent (drop_at c scruts, ?spec_rows)"
            unfolding matrix_payload_consistent_def
          proof clarify
            fix new_row1 :: "CoreTerm Row" and new_row2 :: "CoreTerm Row"
            fix h' mpat1 mpat2
            assume nr1_in: "new_row1 \<in> set ?spec_rows"
               and nr2_in: "new_row2 \<in> set ?spec_rows"
               and v1: "(h', mpat1) \<in> row_all_variants new_row1"
               and v2: "(h', mpat2) \<in> row_all_variants new_row2"
            from nr1_in obtain o1 where o1_in: "o1 \<in> set rows"
              and s1: "specialise_row_bool c ?s_c h o1 = Some new_row1"
              by (auto simp: List.map_filter_def)
            from nr2_in obtain o2 where o2_in: "o2 \<in> set rows"
              and s2: "specialise_row_bool c ?s_c h o2 = Some new_row2"
              by (auto simp: List.map_filter_def)
            obtain o1ps o1bs o1body where
              o1_eq: "o1 = (o1ps, o1bs, o1body)" by (cases o1) auto
            obtain o2ps o2bs o2body where
              o2_eq: "o2 = (o2ps, o2bs, o2body)" by (cases o2) auto
            have v1_orig: "(h', mpat1) \<in> row_all_variants o1"
              using v1 row_all_variants_specialise_row_bool_subset s1 o1_eq by (metis in_mono)
            have v2_orig: "(h', mpat2) \<in> row_all_variants o2"
              using v2 row_all_variants_specialise_row_bool_subset s2 o2_eq by (metis in_mono)
            show "(mpat1 = None) = (mpat2 = None)"
              using "1.prems"(2) o1_in o2_in v1_orig v2_orig
              unfolding matrix_payload_consistent_def by blast
          qed

          \<comment> \<open>specialised_rows \<noteq> []: there's a row whose c-th pattern is DP_Bool h.\<close>
          have spec_ne: "?spec_rows \<noteq> []"
          proof -
            from h_in distinct_bool_heads_in_col_pats
            have "DP_Bool h \<in> set ?col_pats" by blast
            then obtain orig_row where orig_in: "orig_row \<in> set rows"
              and orig_pat: "fst orig_row ! c = DP_Bool h"
              by force
            obtain ops obs obody where
              orig_row_eq: "orig_row = (ops, obs, obody)" by (cases orig_row) auto
            from orig_pat orig_row_eq have ops_c: "ops ! c = DP_Bool h" by simp
            have spec_some: "specialise_row_bool c ?s_c h orig_row
                              = Some (drop_at c ops, obs, obody)"
              using ops_c orig_row_eq by simp
            have "(drop_at c ops, obs, obody) \<in> set ?spec_rows"
            proof -
              have witness:
                "orig_row \<in> {x \<in> set rows. \<exists>y. specialise_row_bool c ?s_c h x = Some y}"
                using orig_in spec_some by auto
              have "the (specialise_row_bool c ?s_c h orig_row) = (drop_at c ops, obs, obody)"
                using spec_some by simp
              hence "(drop_at c ops, obs, obody)
                       \<in> (\<lambda>x. the (specialise_row_bool c ?s_c h x))
                          ` {x \<in> set rows. \<exists>y. specialise_row_bool c ?s_c h x = Some y}"
                using witness by (metis (no_types, lifting) imageI)
              thus ?thesis by (simp add: List.map_filter_def)
            qed
            thus ?thesis by auto
          qed

          \<comment> \<open>Apply IH for the bool head arm.\<close>
          show "matchtree_term_well_typed env ghost resultTy
                  (compile_matrix (drop_at c scruts, ?spec_rows))"
            using "1.hyps"(4)[OF fnw refl refl refl refl refl head_kind_at_hd refl refl
                                new_matrix_wt new_payload "1.prems"(3) spec_ne] .
        qed

        \<comment> \<open>Show the default arm is well-typed (when present).\<close>
        have default_arm_wt:
          "?has_default \<longrightarrow>
             matchtree_term_well_typed env ghost resultTy
               (compile_matrix (drop_at c scruts, ?default_rows))"
        proof
          assume has_default: ?has_default
          let ?new_colTys = "drop_at c colTys"

          have default_rows_typed:
            "list_all (row_term_well_typed env ghost ?new_colTys resultTy) ?default_rows"
          proof -
            have "\<forall>new_row \<in> set ?default_rows.
                    row_term_well_typed env ghost ?new_colTys resultTy new_row"
            proof
              fix new_row assume "new_row \<in> set ?default_rows"
              then obtain orig_row where orig_in: "orig_row \<in> set rows"
                and spec_some: "default_row c ?s_c orig_row = Some new_row"
                by (auto simp: List.map_filter_def)
              obtain ops obs obody where
                orig_row_eq: "orig_row = (ops, obs, obody)" by (cases orig_row) auto
              from rows_typed orig_in orig_row_eq have
                orig_wt: "row_term_well_typed env ghost colTys resultTy (ops, obs, obody)"
                by (auto simp: list_all_iff)
              from fresh_inv orig_in c_lt_scruts orig_row_eq have
                row_fresh: "row_scrut_fresh ?s_c (ops, obs, obody)"
                by (auto simp: matrix_scrut_freshness_def)
              \<comment> \<open>Need: core_term_type env ghost s_c = Some (colTys ! c). We have it via s_c_ty
                   only when colTys ! c = CoreTy_Bool — which we have.\<close>
              have s_c_at_c: "core_term_type env ghost ?s_c = Some (colTys ! c)"
                using s_c_ty colTy_c_bool by simp
              show "row_term_well_typed env ghost ?new_colTys resultTy new_row"
                using default_row_preserves_typing[
                          OF orig_wt c_lt_colTys s_c_at_c row_fresh]
                      spec_some orig_row_eq
                by simp
            qed
            thus ?thesis by (simp add: list_all_iff)
          qed

          have new_scruts_typed:
            "list_all2 (\<lambda>s ty. core_term_type env ghost s = Some ty)
                       (drop_at c scruts) ?new_colTys"
            using list_all2_drop_at[OF scruts_typed c_lt_scruts] .

          have new_colTys_wk: "list_all (is_well_kinded env) ?new_colTys"
            using list_all_drop_at[OF colTys_wk] .

          have new_fresh: "matrix_scrut_freshness (drop_at c scruts, ?default_rows)"
            unfolding matrix_scrut_freshness_def
          proof clarify
            fix s :: CoreTerm and new_row :: "CoreTerm Row"
            assume s_in: "s \<in> set (drop_at c scruts)" and nr_in: "new_row \<in> set ?default_rows"
            from s_in have s_in_orig: "s \<in> set scruts"
              by (induction c scruts rule: drop_at.induct) auto
            from nr_in obtain orig_row where
              orig_in: "orig_row \<in> set rows" and
              spec_some: "default_row c ?s_c orig_row = Some new_row"
              by (auto simp: List.map_filter_def)
            obtain ops obs obody where
              orig_row_eq: "orig_row = (ops, obs, obody)" by (cases orig_row) auto
            have c_lt_ops: "c < length ops"
              using c_facts orig_in orig_row_eq by auto
            have row_subset:
              "row_var_names new_row |\<subseteq>| row_var_names orig_row"
              using row_var_names_default_row_subset[OF c_lt_ops]
                    spec_some orig_row_eq by simp
            from fresh_inv s_in_orig orig_in have
              "core_term_free_vars s |\<inter>| row_var_names orig_row = {||}"
              by (auto simp: matrix_scrut_freshness_def)
            with row_subset show "core_term_free_vars s |\<inter>| row_var_names new_row = {||}"
              by blast
          qed

          have new_matrix_wt:
            "matrix_term_well_typed env ghost resultTy (drop_at c scruts, ?default_rows)"
            unfolding matrix_term_well_typed_def
            using new_scruts_typed new_colTys_wk default_rows_typed new_fresh
            by (auto simp: list_all2_lengthD)

          have new_payload: "matrix_payload_consistent (drop_at c scruts, ?default_rows)"
            unfolding matrix_payload_consistent_def
          proof clarify
            fix new_row1 :: "CoreTerm Row" and new_row2 :: "CoreTerm Row"
            fix h' mpat1 mpat2
            assume nr1_in: "new_row1 \<in> set ?default_rows"
               and nr2_in: "new_row2 \<in> set ?default_rows"
               and v1: "(h', mpat1) \<in> row_all_variants new_row1"
               and v2: "(h', mpat2) \<in> row_all_variants new_row2"
            from nr1_in obtain o1 where o1_in: "o1 \<in> set rows"
              and s1: "default_row c ?s_c o1 = Some new_row1"
              by (auto simp: List.map_filter_def)
            from nr2_in obtain o2 where o2_in: "o2 \<in> set rows"
              and s2: "default_row c ?s_c o2 = Some new_row2"
              by (auto simp: List.map_filter_def)
            obtain o1ps o1bs o1body where
              o1_eq: "o1 = (o1ps, o1bs, o1body)" by (cases o1) auto
            obtain o2ps o2bs o2body where
              o2_eq: "o2 = (o2ps, o2bs, o2body)" by (cases o2) auto
            have v1_orig: "(h', mpat1) \<in> row_all_variants o1"
              using v1 row_all_variants_default_row_subset s1 o1_eq by (metis in_mono)
            have v2_orig: "(h', mpat2) \<in> row_all_variants o2"
              using v2 row_all_variants_default_row_subset s2 o2_eq by (metis in_mono)
            show "(mpat1 = None) = (mpat2 = None)"
              using "1.prems"(2) o1_in o2_in v1_orig v2_orig
              unfolding matrix_payload_consistent_def by blast
          qed

          \<comment> \<open>default_rows \<noteq> []: has_default means some col_pat is wildcard-like, so
               there's a row whose c-th pattern is wildcard-like, which survives default_row.\<close>
          have default_ne: "?default_rows \<noteq> []"
          proof -
            from has_default obtain p where p_in: "p \<in> set ?col_pats"
              and p_wc: "is_wildcard_like p"
              by (meson in_set_conv_nth list_ex_length)
            from p_in obtain orig_row where orig_in: "orig_row \<in> set rows"
              and orig_pat: "fst orig_row ! c = p" by force
            obtain ops obs obody where
              orig_row_eq: "orig_row = (ops, obs, obody)" by (cases orig_row) auto
            from orig_pat orig_row_eq have ops_c_wc: "is_wildcard_like (ops ! c)"
              using p_wc by simp
            have spec_some: "\<exists>new_row. default_row c ?s_c orig_row = Some new_row"
              using ops_c_wc orig_row_eq
              by (cases "ops ! c") auto
            then obtain new_row where spec_eq: "default_row c ?s_c orig_row = Some new_row"
              by blast
            have witness:
              "orig_row \<in> {x \<in> set rows. \<exists>y. default_row c ?s_c x = Some y}"
              using orig_in spec_eq by blast
            have "the (default_row c ?s_c orig_row) = new_row" using spec_eq by simp
            hence "new_row \<in> (\<lambda>x. the (default_row c ?s_c x))
                              ` {x \<in> set rows. \<exists>y. default_row c ?s_c x = Some y}"
              using witness by blast
            hence "new_row \<in> set ?default_rows" by (simp add: List.map_filter_def)
            thus ?thesis by auto
          qed

          show "matchtree_term_well_typed env ghost resultTy
                  (compile_matrix (drop_at c scruts, ?default_rows))"
            using "1.hyps"(1)[OF fnw refl refl refl refl has_default
                                new_matrix_wt new_payload "1.prems"(3) default_ne] .
        qed

        \<comment> \<open>Show each head pattern is compatible with CoreTy_Bool.\<close>
        have head_pats_compat:
          "list_all (\<lambda>(p, _). pattern_compatible env p CoreTy_Bool)
                    (map ?head_arm ?heads @ ?default_arm)"
          by (auto simp: list_all_iff)

        \<comment> \<open>Show arms are non-empty: heads are non-empty (head_pat = DP_Bool b is in col_pats).\<close>
        have heads_ne: "?heads \<noteq> []"
        proof -
          from head_pat_in_col head_pat_eq2 have b_in: "DP_Bool b \<in> set ?col_pats" by simp
          have aux: "\<And>ps. DP_Bool b \<in> set ps \<Longrightarrow> distinct_bool_heads ps \<noteq> []"
          proof -
            fix ps :: "DecPattern list"
            assume "DP_Bool b \<in> set ps"
            thus "distinct_bool_heads ps \<noteq> []"
              by (induction ps rule: distinct_bool_heads.induct) auto
          qed
          show ?thesis using aux[OF b_in] .
        qed
        have arms_ne: "map ?head_arm ?heads @ ?default_arm \<noteq> []"
          using heads_ne by simp

        show ?thesis
          unfolding compile_eq Let_def
          using s_c_ty arms_ne head_pats_compat
                head_arm_wt default_arm_wt
          by (auto simp: list_all_iff)
      next
        case HK_Int
        \<comment> \<open>Int case: MT_Test with arms for each distinct int head + optional default.
             The column type at c is some integer type (from any DP_Int pattern's compatibility).\<close>
        from Some HK_Int obtain b where head_pat_eq2: "head_pat = DP_Int b"
          by (cases head_pat) auto
        have head_kind_eq: "head_kind_of head_pat = Some HK_Int"
          using Some HK_Int by simp
        have hd_eq: "hd (filter (\<lambda>p. \<not> is_wildcard_like p) ?col_pats) = head_pat"
          using head_pat_eq by blast

        from head_pat_in_col obtain r_b where r_b_in: "r_b \<in> set rows"
          and r_b_pat: "fst r_b ! c = head_pat" by force
        obtain rps_b rbs_b rbody_b where r_b_eq:
          "r_b = (rps_b, rbs_b, rbody_b)" by (cases r_b) auto
        from rows_typed r_b_in r_b_eq have
          b_row_wt: "row_term_well_typed env ghost colTys resultTy
                       (rps_b, rbs_b, rbody_b)"
          by (auto simp: list_all_iff)
        from b_row_wt have
          b_compat: "dec_pattern_compatible_list
                       (extend_env_with_bindlist env ghost rbs_b)
                       rps_b colTys"
          and b_len: "length rps_b = length colTys"
          by (auto simp: Let_def)
        have b_c: "rps_b ! c = DP_Int b"
          using r_b_pat r_b_eq head_pat_eq2 by simp
        have c_lt_b: "c < length rps_b" using c_lt_colTys b_len by simp
        have b_compat_at_c: "dec_pattern_compatible
                                (extend_env_with_bindlist env ghost rbs_b)
                                (rps_b ! c) (colTys ! c)"
          using b_compat c_lt_b b_len
          by (auto simp: dec_pattern_compatible_list_iff)
        with b_c have colTy_c_int: "is_integer_type (colTys ! c)" by simp

        have s_c_ty: "core_term_type env ghost ?s_c = Some (colTys ! c)"
          using scruts_typed c_lt_scruts
          by (auto simp: list_all2_conv_all_nth)

        have compile_eq:
          "compile_matrix (scruts, rows)
           = (let s_c = ?s_c;
                  col_pats = ?col_pats;
                  has_default = list_ex is_wildcard_like col_pats;
                  default_rows = List.map_filter (default_row c s_c) rows;
                  default_arm =
                    (if has_default
                     then [(CorePat_Wildcard,
                            compile_matrix (drop_at c scruts, default_rows))]
                     else []);
                  heads = distinct_int_heads col_pats;
                  head_arm = (\<lambda>h.
                    (CorePat_Int h,
                     compile_matrix (drop_at c scruts,
                       List.map_filter (specialise_row_int c s_c h) rows)))
              in MT_Test s_c (map head_arm heads @ default_arm))"
          using compile_matrix_unfold_int[OF fnw hd_eq head_kind_eq] .

        let ?heads = "distinct_int_heads ?col_pats"
        let ?head_arm = "\<lambda>h. (CorePat_Int h,
                              compile_matrix (drop_at c scruts,
                                List.map_filter (specialise_row_int c ?s_c h) rows))"

        have head_kind_at_hd: "head_kind_of (hd (filter (\<lambda>p. \<not> is_wildcard_like p) ?col_pats))
                                = Some HK_Int"
          using hd_eq head_kind_eq by simp

        have head_arm_wt:
          "\<forall>h \<in> set ?heads.
             matchtree_term_well_typed env ghost resultTy
               (compile_matrix (drop_at c scruts,
                  List.map_filter (specialise_row_int c ?s_c h) rows))"
        proof
          fix h assume h_in: "h \<in> set ?heads"
          let ?spec_rows = "List.map_filter (specialise_row_int c ?s_c h) rows"
          let ?new_colTys = "drop_at c colTys"

          have spec_rows_typed:
            "list_all (row_term_well_typed env ghost ?new_colTys resultTy) ?spec_rows"
          proof -
            have "\<forall>new_row \<in> set ?spec_rows.
                    row_term_well_typed env ghost ?new_colTys resultTy new_row"
            proof
              fix new_row assume "new_row \<in> set ?spec_rows"
              then obtain orig_row where orig_in: "orig_row \<in> set rows"
                and spec_some: "specialise_row_int c ?s_c h orig_row = Some new_row"
                by (auto simp: List.map_filter_def)
              obtain ops obs obody where
                orig_row_eq: "orig_row = (ops, obs, obody)" by (cases orig_row) auto
              from rows_typed orig_in orig_row_eq have
                orig_wt: "row_term_well_typed env ghost colTys resultTy (ops, obs, obody)"
                by (auto simp: list_all_iff)
              from fresh_inv orig_in c_lt_scruts orig_row_eq have
                row_fresh: "row_scrut_fresh ?s_c (ops, obs, obody)"
                by (auto simp: matrix_scrut_freshness_def)
              show "row_term_well_typed env ghost ?new_colTys resultTy new_row"
                using specialise_row_int_preserves_typing[
                          OF orig_wt c_lt_colTys colTy_c_int s_c_ty row_fresh]
                      spec_some orig_row_eq
                by simp
            qed
            thus ?thesis by (simp add: list_all_iff)
          qed

          have new_scruts_typed:
            "list_all2 (\<lambda>s ty. core_term_type env ghost s = Some ty)
                       (drop_at c scruts) ?new_colTys"
            using list_all2_drop_at[OF scruts_typed c_lt_scruts] .

          have new_colTys_wk: "list_all (is_well_kinded env) ?new_colTys"
            using list_all_drop_at[OF colTys_wk] .

          have new_fresh: "matrix_scrut_freshness (drop_at c scruts, ?spec_rows)"
            unfolding matrix_scrut_freshness_def
          proof clarify
            fix s :: CoreTerm and new_row :: "CoreTerm Row"
            assume s_in: "s \<in> set (drop_at c scruts)" and nr_in: "new_row \<in> set ?spec_rows"
            from s_in have s_in_orig: "s \<in> set scruts"
              by (induction c scruts rule: drop_at.induct) auto
            from nr_in obtain orig_row where
              orig_in: "orig_row \<in> set rows" and
              spec_some: "specialise_row_int c ?s_c h orig_row = Some new_row"
              by (auto simp: List.map_filter_def)
            obtain ops obs obody where
              orig_row_eq: "orig_row = (ops, obs, obody)" by (cases orig_row) auto
            have c_lt_ops: "c < length ops"
              using c_facts orig_in orig_row_eq by auto
            have row_subset:
              "row_var_names new_row |\<subseteq>| row_var_names orig_row"
              using row_var_names_specialise_row_int_subset[OF c_lt_ops]
                    spec_some orig_row_eq by simp
            from fresh_inv s_in_orig orig_in have
              "core_term_free_vars s |\<inter>| row_var_names orig_row = {||}"
              by (auto simp: matrix_scrut_freshness_def)
            with row_subset show "core_term_free_vars s |\<inter>| row_var_names new_row = {||}"
              by blast
          qed

          have new_matrix_wt:
            "matrix_term_well_typed env ghost resultTy (drop_at c scruts, ?spec_rows)"
            unfolding matrix_term_well_typed_def
            using new_scruts_typed new_colTys_wk spec_rows_typed new_fresh
            by (auto simp: list_all2_lengthD)

          have new_payload: "matrix_payload_consistent (drop_at c scruts, ?spec_rows)"
            unfolding matrix_payload_consistent_def
          proof clarify
            fix new_row1 :: "CoreTerm Row" and new_row2 :: "CoreTerm Row"
            fix h' mpat1 mpat2
            assume nr1_in: "new_row1 \<in> set ?spec_rows"
               and nr2_in: "new_row2 \<in> set ?spec_rows"
               and v1: "(h', mpat1) \<in> row_all_variants new_row1"
               and v2: "(h', mpat2) \<in> row_all_variants new_row2"
            from nr1_in obtain o1 where o1_in: "o1 \<in> set rows"
              and s1: "specialise_row_int c ?s_c h o1 = Some new_row1"
              by (auto simp: List.map_filter_def)
            from nr2_in obtain o2 where o2_in: "o2 \<in> set rows"
              and s2: "specialise_row_int c ?s_c h o2 = Some new_row2"
              by (auto simp: List.map_filter_def)
            obtain o1ps o1bs o1body where
              o1_eq: "o1 = (o1ps, o1bs, o1body)" by (cases o1) auto
            obtain o2ps o2bs o2body where
              o2_eq: "o2 = (o2ps, o2bs, o2body)" by (cases o2) auto
            have v1_orig: "(h', mpat1) \<in> row_all_variants o1"
              using v1 row_all_variants_specialise_row_int_subset s1 o1_eq by (metis in_mono)
            have v2_orig: "(h', mpat2) \<in> row_all_variants o2"
              using v2 row_all_variants_specialise_row_int_subset s2 o2_eq by (metis in_mono)
            show "(mpat1 = None) = (mpat2 = None)"
              using "1.prems"(2) o1_in o2_in v1_orig v2_orig
              unfolding matrix_payload_consistent_def by blast
          qed

          have spec_ne: "?spec_rows \<noteq> []"
          proof -
            from h_in distinct_int_heads_in_col_pats
            have "DP_Int h \<in> set ?col_pats" by blast
            then obtain orig_row where orig_in: "orig_row \<in> set rows"
              and orig_pat: "fst orig_row ! c = DP_Int h"
              by force
            obtain ops obs obody where
              orig_row_eq: "orig_row = (ops, obs, obody)" by (cases orig_row) auto
            from orig_pat orig_row_eq have ops_c: "ops ! c = DP_Int h" by simp
            have spec_some: "specialise_row_int c ?s_c h orig_row
                              = Some (drop_at c ops, obs, obody)"
              using ops_c orig_row_eq by simp
            have "(drop_at c ops, obs, obody) \<in> set ?spec_rows"
            proof -
              have witness:
                "orig_row \<in> {x \<in> set rows. \<exists>y. specialise_row_int c ?s_c h x = Some y}"
                using orig_in spec_some by auto
              have "the (specialise_row_int c ?s_c h orig_row) = (drop_at c ops, obs, obody)"
                using spec_some by simp
              hence "(drop_at c ops, obs, obody)
                       \<in> (\<lambda>x. the (specialise_row_int c ?s_c h x))
                          ` {x \<in> set rows. \<exists>y. specialise_row_int c ?s_c h x = Some y}"
                using witness by (metis (no_types, lifting) imageI)
              thus ?thesis by (simp add: List.map_filter_def)
            qed
            thus ?thesis by auto
          qed

          show "matchtree_term_well_typed env ghost resultTy
                  (compile_matrix (drop_at c scruts, ?spec_rows))"
            using "1.hyps"(5)[OF fnw refl refl refl refl refl head_kind_at_hd refl refl
                                new_matrix_wt new_payload "1.prems"(3) spec_ne] .
        qed

        have default_arm_wt:
          "?has_default \<longrightarrow>
             matchtree_term_well_typed env ghost resultTy
               (compile_matrix (drop_at c scruts, ?default_rows))"
        proof
          assume has_default: ?has_default
          let ?new_colTys = "drop_at c colTys"

          have default_rows_typed:
            "list_all (row_term_well_typed env ghost ?new_colTys resultTy) ?default_rows"
          proof -
            have "\<forall>new_row \<in> set ?default_rows.
                    row_term_well_typed env ghost ?new_colTys resultTy new_row"
            proof
              fix new_row assume "new_row \<in> set ?default_rows"
              then obtain orig_row where orig_in: "orig_row \<in> set rows"
                and spec_some: "default_row c ?s_c orig_row = Some new_row"
                by (auto simp: List.map_filter_def)
              obtain ops obs obody where
                orig_row_eq: "orig_row = (ops, obs, obody)" by (cases orig_row) auto
              from rows_typed orig_in orig_row_eq have
                orig_wt: "row_term_well_typed env ghost colTys resultTy (ops, obs, obody)"
                by (auto simp: list_all_iff)
              from fresh_inv orig_in c_lt_scruts orig_row_eq have
                row_fresh: "row_scrut_fresh ?s_c (ops, obs, obody)"
                by (auto simp: matrix_scrut_freshness_def)
              show "row_term_well_typed env ghost ?new_colTys resultTy new_row"
                using default_row_preserves_typing[
                          OF orig_wt c_lt_colTys s_c_ty row_fresh]
                      spec_some orig_row_eq
                by simp
            qed
            thus ?thesis by (simp add: list_all_iff)
          qed

          have new_scruts_typed:
            "list_all2 (\<lambda>s ty. core_term_type env ghost s = Some ty)
                       (drop_at c scruts) ?new_colTys"
            using list_all2_drop_at[OF scruts_typed c_lt_scruts] .

          have new_colTys_wk: "list_all (is_well_kinded env) ?new_colTys"
            using list_all_drop_at[OF colTys_wk] .

          have new_fresh: "matrix_scrut_freshness (drop_at c scruts, ?default_rows)"
            unfolding matrix_scrut_freshness_def
          proof clarify
            fix s :: CoreTerm and new_row :: "CoreTerm Row"
            assume s_in: "s \<in> set (drop_at c scruts)" and nr_in: "new_row \<in> set ?default_rows"
            from s_in have s_in_orig: "s \<in> set scruts"
              by (induction c scruts rule: drop_at.induct) auto
            from nr_in obtain orig_row where
              orig_in: "orig_row \<in> set rows" and
              spec_some: "default_row c ?s_c orig_row = Some new_row"
              by (auto simp: List.map_filter_def)
            obtain ops obs obody where
              orig_row_eq: "orig_row = (ops, obs, obody)" by (cases orig_row) auto
            have c_lt_ops: "c < length ops"
              using c_facts orig_in orig_row_eq by auto
            have row_subset:
              "row_var_names new_row |\<subseteq>| row_var_names orig_row"
              using row_var_names_default_row_subset[OF c_lt_ops]
                    spec_some orig_row_eq by simp
            from fresh_inv s_in_orig orig_in have
              "core_term_free_vars s |\<inter>| row_var_names orig_row = {||}"
              by (auto simp: matrix_scrut_freshness_def)
            with row_subset show "core_term_free_vars s |\<inter>| row_var_names new_row = {||}"
              by blast
          qed

          have new_matrix_wt:
            "matrix_term_well_typed env ghost resultTy (drop_at c scruts, ?default_rows)"
            unfolding matrix_term_well_typed_def
            using new_scruts_typed new_colTys_wk default_rows_typed new_fresh
            by (auto simp: list_all2_lengthD)

          have new_payload: "matrix_payload_consistent (drop_at c scruts, ?default_rows)"
            unfolding matrix_payload_consistent_def
          proof clarify
            fix new_row1 :: "CoreTerm Row" and new_row2 :: "CoreTerm Row"
            fix h' mpat1 mpat2
            assume nr1_in: "new_row1 \<in> set ?default_rows"
               and nr2_in: "new_row2 \<in> set ?default_rows"
               and v1: "(h', mpat1) \<in> row_all_variants new_row1"
               and v2: "(h', mpat2) \<in> row_all_variants new_row2"
            from nr1_in obtain o1 where o1_in: "o1 \<in> set rows"
              and s1: "default_row c ?s_c o1 = Some new_row1"
              by (auto simp: List.map_filter_def)
            from nr2_in obtain o2 where o2_in: "o2 \<in> set rows"
              and s2: "default_row c ?s_c o2 = Some new_row2"
              by (auto simp: List.map_filter_def)
            obtain o1ps o1bs o1body where
              o1_eq: "o1 = (o1ps, o1bs, o1body)" by (cases o1) auto
            obtain o2ps o2bs o2body where
              o2_eq: "o2 = (o2ps, o2bs, o2body)" by (cases o2) auto
            have v1_orig: "(h', mpat1) \<in> row_all_variants o1"
              using v1 row_all_variants_default_row_subset s1 o1_eq by (metis in_mono)
            have v2_orig: "(h', mpat2) \<in> row_all_variants o2"
              using v2 row_all_variants_default_row_subset s2 o2_eq by (metis in_mono)
            show "(mpat1 = None) = (mpat2 = None)"
              using "1.prems"(2) o1_in o2_in v1_orig v2_orig
              unfolding matrix_payload_consistent_def by blast
          qed

          have default_ne: "?default_rows \<noteq> []"
          proof -
            from has_default obtain p where p_in: "p \<in> set ?col_pats"
              and p_wc: "is_wildcard_like p"
              by (meson in_set_conv_nth list_ex_length)
            from p_in obtain orig_row where orig_in: "orig_row \<in> set rows"
              and orig_pat: "fst orig_row ! c = p" by force
            obtain ops obs obody where
              orig_row_eq: "orig_row = (ops, obs, obody)" by (cases orig_row) auto
            from orig_pat orig_row_eq have ops_c_wc: "is_wildcard_like (ops ! c)"
              using p_wc by simp
            have spec_some: "\<exists>new_row. default_row c ?s_c orig_row = Some new_row"
              using ops_c_wc orig_row_eq
              by (cases "ops ! c") auto
            then obtain new_row where spec_eq: "default_row c ?s_c orig_row = Some new_row"
              by blast
            have witness:
              "orig_row \<in> {x \<in> set rows. \<exists>y. default_row c ?s_c x = Some y}"
              using orig_in spec_eq by blast
            have "the (default_row c ?s_c orig_row) = new_row" using spec_eq by simp
            hence "new_row \<in> (\<lambda>x. the (default_row c ?s_c x))
                              ` {x \<in> set rows. \<exists>y. default_row c ?s_c x = Some y}"
              using witness by blast
            hence "new_row \<in> set ?default_rows" by (simp add: List.map_filter_def)
            thus ?thesis by auto
          qed

          show "matchtree_term_well_typed env ghost resultTy
                  (compile_matrix (drop_at c scruts, ?default_rows))"
            using "1.hyps"(1)[OF fnw refl refl refl refl has_default
                                new_matrix_wt new_payload "1.prems"(3) default_ne] .
        qed

        have head_pats_compat:
          "list_all (\<lambda>(p, _). pattern_compatible env p (colTys ! c))
                    (map ?head_arm ?heads @ ?default_arm)"
          using colTy_c_int by (auto simp: list_all_iff)

        have heads_ne: "?heads \<noteq> []"
        proof -
          from head_pat_in_col head_pat_eq2 have b_in: "DP_Int b \<in> set ?col_pats" by simp
          have aux: "\<And>ps. DP_Int b \<in> set ps \<Longrightarrow> distinct_int_heads ps \<noteq> []"
          proof -
            fix ps :: "DecPattern list"
            assume "DP_Int b \<in> set ps"
            thus "distinct_int_heads ps \<noteq> []"
              by (induction ps rule: distinct_int_heads.induct) auto
          qed
          show ?thesis using aux[OF b_in] .
        qed
        have arms_ne: "map ?head_arm ?heads @ ?default_arm \<noteq> []"
          using heads_ne by simp

        show ?thesis
          unfolding compile_eq Let_def
          using s_c_ty arms_ne head_pats_compat
                head_arm_wt default_arm_wt
          by (auto simp: list_all_iff)
      next
        case HK_Variant
        \<comment> \<open>Variant case: MT_Test with arms for each distinct variant head + optional default.
             head_pat is DP_Variant h_top mpat_top for some h_top, mpat_top.\<close>
        from Some HK_Variant obtain h_top mpat_top where head_pat_eq2:
          "head_pat = DP_Variant h_top mpat_top"
          by (cases head_pat) auto
        have head_kind_eq: "head_kind_of head_pat = Some HK_Variant"
          using Some HK_Variant by simp
        have hd_eq: "hd (filter (\<lambda>p. \<not> is_wildcard_like p) ?col_pats) = head_pat"
          using head_pat_eq by blast

        \<comment> \<open>Find a row whose c-th pattern is head_pat to derive col c's type.\<close>
        from head_pat_in_col obtain r_v where r_v_in: "r_v \<in> set rows"
          and r_v_pat: "fst r_v ! c = head_pat" by force
        obtain rps_v rbs_v rbody_v where r_v_eq:
          "r_v = (rps_v, rbs_v, rbody_v)" by (cases r_v) auto
        from rows_typed r_v_in r_v_eq have
          v_row_wt: "row_term_well_typed env ghost colTys resultTy
                       (rps_v, rbs_v, rbody_v)"
          by (auto simp: list_all_iff)
        from v_row_wt have
          v_compat: "dec_pattern_compatible_list
                       (extend_env_with_bindlist env ghost rbs_v)
                       rps_v colTys"
          and v_len: "length rps_v = length colTys"
          by (auto simp: Let_def)
        have v_c: "rps_v ! c = DP_Variant h_top mpat_top"
          using r_v_pat r_v_eq head_pat_eq2 by simp
        have c_lt_v: "c < length rps_v" using c_lt_colTys v_len by simp
        have v_compat_at_c: "dec_pattern_compatible
                                (extend_env_with_bindlist env ghost rbs_v)
                                (rps_v ! c) (colTys ! c)"
          using v_compat c_lt_v v_len
          by (auto simp: dec_pattern_compatible_list_iff)

        \<comment> \<open>From DP_Variant compatibility: colTys ! c = CoreTy_Datatype dtName tyArgs
             for some dtName, tyArgs, with appropriate ctor lookup.\<close>
        from v_compat_at_c v_c obtain dtName tyArgs tyvars payloadTy where
          colTy_c_dt: "colTys ! c = CoreTy_Datatype dtName tyArgs" and
          ctor_info_bs:
            "fmlookup (TE_DataCtors (extend_env_with_bindlist env ghost rbs_v)) h_top
              = Some (dtName, tyvars, payloadTy)" and
          tyargs_len: "length tyArgs = length tyvars"
          by (cases "colTys ! c"; cases "fmlookup (TE_DataCtors
                                              (extend_env_with_bindlist env ghost rbs_v)) h_top")
             (auto split: option.splits)

        \<comment> \<open>Lift ctor_info to env (TE_DataCtors invariant under bindlist extension).\<close>
        have TE_DataCtors_eq: "\<And>bs.
                TE_DataCtors (extend_env_with_bindlist env ghost bs) = TE_DataCtors env"
        proof -
          fix bs :: BindList
          show "TE_DataCtors (extend_env_with_bindlist env ghost bs) = TE_DataCtors env"
          proof (induction bs arbitrary: env)
            case Nil thus ?case by simp
          next
            case (Cons b bs)
            obtain vr' x' ty' rhs' where b_eq: "b = (vr', x', ty', rhs')"
              by (cases b) auto
            have step: "TE_DataCtors (extend_env_with_bind env ghost x' ty')
                        = TE_DataCtors env"
              unfolding extend_env_with_bind_def by simp
            show ?case using b_eq Cons.IH step by simp
          qed
        qed
        have ctor_info: "fmlookup (TE_DataCtors env) h_top
                          = Some (dtName, tyvars, payloadTy)"
          using ctor_info_bs TE_DataCtors_eq by simp

        \<comment> \<open>s_c typechecks at colTys ! c.\<close>
        have s_c_ty: "core_term_type env ghost ?s_c = Some (colTys ! c)"
          using scruts_typed c_lt_scruts
          by (auto simp: list_all2_conv_all_nth)

        have compile_eq:
          "compile_matrix (scruts, rows)
           = (let s_c = ?s_c;
                  col_pats = ?col_pats;
                  has_default = list_ex is_wildcard_like col_pats;
                  default_rows = List.map_filter (default_row c s_c) rows;
                  default_arm =
                    (if has_default
                     then [(CorePat_Wildcard,
                            compile_matrix (drop_at c scruts, default_rows))]
                     else []);
                  heads = distinct_variant_heads col_pats;
                  head_arm = (\<lambda>(h, has_payload).
                    let new_scruts =
                          (if has_payload
                           then replace_at c (CoreTm_VariantProj s_c h) scruts
                           else drop_at c scruts)
                    in (CorePat_Variant h CorePat_Wildcard,
                        compile_matrix (new_scruts,
                          List.map_filter (specialise_row_variant c s_c h has_payload) rows)))
              in MT_Test s_c (map head_arm heads @ default_arm))"
          using compile_matrix_unfold_variant[OF fnw hd_eq head_kind_eq] .

        let ?heads = "distinct_variant_heads ?col_pats"
        let ?head_arm = "\<lambda>(h, has_payload).
              let new_scruts =
                    (if has_payload
                     then replace_at c (CoreTm_VariantProj ?s_c h) scruts
                     else drop_at c scruts)
              in (CorePat_Variant h CorePat_Wildcard,
                  compile_matrix (new_scruts,
                    List.map_filter (specialise_row_variant c ?s_c h has_payload) rows))"

        have head_kind_at_hd: "head_kind_of (hd (filter (\<lambda>p. \<not> is_wildcard_like p) ?col_pats))
                                = Some HK_Variant"
          using hd_eq head_kind_eq by simp

        \<comment> \<open>Show each head arm is well-typed.\<close>
        have head_arm_wt:
          "\<forall>(h, has_payload) \<in> set ?heads.
             matchtree_term_well_typed env ghost resultTy
               (compile_matrix (
                  if has_payload
                  then replace_at c (CoreTm_VariantProj ?s_c h) scruts
                  else drop_at c scruts,
                  List.map_filter (specialise_row_variant c ?s_c h has_payload) rows))"
        proof clarify
          fix h has_payload
          assume h_in: "(h, has_payload) \<in> set ?heads"
          let ?spec_rows = "List.map_filter (specialise_row_variant c ?s_c h has_payload) rows"

          \<comment> \<open>From distinct_variant_heads: there's a row with DP_Variant h mpat where
               has_payload = (mpat \<noteq> None).\<close>
          from h_in distinct_variant_heads_in_col_pats obtain mpat_h where
            mpat_h_in: "DP_Variant h mpat_h \<in> set ?col_pats" and
            has_payload_eq_top: "has_payload = (mpat_h \<noteq> None)"
            by blast
          \<comment> \<open>This DP_Variant h mpat_h is in some row at column c.\<close>
          from mpat_h_in obtain row_h where row_h_in: "row_h \<in> set rows"
            and row_h_pat_c: "fst row_h ! c = DP_Variant h mpat_h"
            by force

          \<comment> \<open>Derive ctor info for h: from row_h's well-typedness.\<close>
          obtain rh_ps rh_bs rh_body where row_h_eq:
            "row_h = (rh_ps, rh_bs, rh_body)" by (cases row_h) auto
          from rows_typed row_h_in row_h_eq have
            row_h_wt: "row_term_well_typed env ghost colTys resultTy (rh_ps, rh_bs, rh_body)"
            by (auto simp: list_all_iff)
          from row_h_wt have
            row_h_compat: "dec_pattern_compatible_list
                            (extend_env_with_bindlist env ghost rh_bs)
                            rh_ps colTys"
            and row_h_len: "length rh_ps = length colTys"
            by (auto simp: Let_def)
          have rh_c: "rh_ps ! c = DP_Variant h mpat_h"
            using row_h_pat_c row_h_eq by simp
          have c_lt_rh: "c < length rh_ps" using c_lt_colTys row_h_len by simp
          have rh_compat_at_c: "dec_pattern_compatible
                                  (extend_env_with_bindlist env ghost rh_bs)
                                  (rh_ps ! c) (colTys ! c)"
            using row_h_compat c_lt_rh row_h_len
            by (auto simp: dec_pattern_compatible_list_iff)
          \<comment> \<open>Hence h has the same datatype as the column type.\<close>
          have h_lookup:
            "\<exists>tyvars_h payloadTy_h.
                fmlookup (TE_DataCtors env) h
                  = Some (dtName, tyvars_h, payloadTy_h)
                \<and> length tyArgs = length tyvars_h"
          proof -
            from rh_compat_at_c rh_c colTy_c_dt
            obtain dtName_h tyvars_h payloadTy_h where
              lookup_eq: "fmlookup (TE_DataCtors (extend_env_with_bindlist env ghost rh_bs)) h
                          = Some (dtName_h, tyvars_h, payloadTy_h)" and
              dtName_eq: "dtName_h = dtName" and
              tyargs_len_h: "length tyArgs = length tyvars_h"
              by (cases "fmlookup (TE_DataCtors (extend_env_with_bindlist env ghost rh_bs)) h")
                 (auto split: option.splits)
            from lookup_eq dtName_eq TE_DataCtors_eq
            have "fmlookup (TE_DataCtors env) h = Some (dtName, tyvars_h, payloadTy_h)"
              by simp
            with tyargs_len_h show ?thesis by blast
          qed
          obtain tyvars_h payloadTy_h where
            ctor_h_info: "fmlookup (TE_DataCtors env) h = Some (dtName, tyvars_h, payloadTy_h)"
            and tyargs_len_h: "length tyArgs = length tyvars_h"
            using h_lookup by blast

          \<comment> \<open>Now we can apply specialise_row_variant_preserves_typing per row.
               First, we need each row's payload_consistent precondition.\<close>
          have payload_per_row:
            "\<And>orig_row mpat_row.
               orig_row \<in> set rows
               \<Longrightarrow> fst orig_row ! c = DP_Variant h mpat_row
               \<Longrightarrow> has_payload = (mpat_row \<noteq> None)"
          proof -
            fix orig_row mpat_row
            assume orig_in: "orig_row \<in> set rows"
              and orig_pat: "fst orig_row ! c = DP_Variant h mpat_row"
            \<comment> \<open>matrix_payload_consistent: orig_row's variant pattern at column c
                 must agree with row_h's variant pattern at column c.\<close>
            obtain o_ps o_bs o_body where o_eq: "orig_row = (o_ps, o_bs, o_body)"
              by (cases orig_row) auto
            from rows_typed orig_in o_eq have
              "row_term_well_typed env ghost colTys resultTy (o_ps, o_bs, o_body)"
              by (auto simp: list_all_iff)
            hence o_len: "length o_ps = length colTys" by (auto simp: Let_def)
            have c_lt_o: "c < length o_ps" using c_lt_colTys o_len by simp
            have o_pat_c: "o_ps ! c = DP_Variant h mpat_row"
              using orig_pat o_eq by simp
            \<comment> \<open>(h, mpat_row) is in row_all_variants of orig_row.\<close>
            have v_orig: "(h, mpat_row) \<in> row_all_variants orig_row"
            proof -
              have "(h, mpat_row) \<in> dec_pattern_all_variants (DP_Variant h mpat_row)"
                by (cases mpat_row) auto
              hence "(h, mpat_row) \<in> dec_pattern_all_variants (o_ps ! c)"
                using o_pat_c by simp
              hence "(h, mpat_row) \<in> dec_pattern_all_variants_list o_ps"
                using c_lt_o
                by (induction o_ps arbitrary: c) (auto simp: nth_Cons split: nat.splits)
              thus ?thesis using o_eq by (simp add: row_all_variants_def)
            qed
            \<comment> \<open>(h, mpat_h) is in row_all_variants of row_h.\<close>
            have v_h: "(h, mpat_h) \<in> row_all_variants row_h"
            proof -
              have "(h, mpat_h) \<in> dec_pattern_all_variants (DP_Variant h mpat_h)"
                by (cases mpat_h) auto
              hence "(h, mpat_h) \<in> dec_pattern_all_variants (rh_ps ! c)"
                using rh_c by simp
              hence "(h, mpat_h) \<in> dec_pattern_all_variants_list rh_ps"
                using c_lt_rh
                by (induction rh_ps arbitrary: c) (auto simp: nth_Cons split: nat.splits)
              thus ?thesis using row_h_eq by (simp add: row_all_variants_def)
            qed
            from "1.prems"(2) orig_in row_h_in v_orig v_h
            have "(mpat_row = None) = (mpat_h = None)"
              unfolding matrix_payload_consistent_def by blast
            thus "has_payload = (mpat_row \<noteq> None)"
              using has_payload_eq_top by simp
          qed

          \<comment> \<open>spec_rows are well-typed against the new colTys.\<close>
          let ?new_colTys = "if has_payload
                             then replace_at c (apply_subst (fmap_of_list (zip tyvars_h tyArgs))
                                                            payloadTy_h) colTys
                             else drop_at c colTys"
          let ?new_scruts = "if has_payload
                             then replace_at c (CoreTm_VariantProj ?s_c h) scruts
                             else drop_at c scruts"

          have spec_rows_typed:
            "list_all (row_term_well_typed env ghost ?new_colTys resultTy) ?spec_rows"
          proof -
            have "\<forall>new_row \<in> set ?spec_rows.
                    row_term_well_typed env ghost ?new_colTys resultTy new_row"
            proof
              fix new_row assume "new_row \<in> set ?spec_rows"
              then obtain orig_row where orig_in: "orig_row \<in> set rows"
                and spec_some: "specialise_row_variant c ?s_c h has_payload orig_row = Some new_row"
                by (auto simp: List.map_filter_def)
              obtain ops obs obody where
                orig_row_eq: "orig_row = (ops, obs, obody)" by (cases orig_row) auto
              from rows_typed orig_in orig_row_eq have
                orig_wt: "row_term_well_typed env ghost colTys resultTy (ops, obs, obody)"
                by (auto simp: list_all_iff)
              from fresh_inv orig_in c_lt_scruts orig_row_eq have
                row_fresh: "row_scrut_fresh ?s_c (ops, obs, obody)"
                by (auto simp: matrix_scrut_freshness_def)

              \<comment> \<open>per-row payload consistency.\<close>
              have row_payload_consistent:
                "\<And>mpat'. ops ! c = DP_Variant h mpat' \<Longrightarrow> has_payload = (mpat' \<noteq> None)"
              proof -
                fix mpat'
                assume "ops ! c = DP_Variant h mpat'"
                hence "fst orig_row ! c = DP_Variant h mpat'"
                  using orig_row_eq by simp
                thus "has_payload = (mpat' \<noteq> None)"
                  using payload_per_row[OF orig_in] by blast
              qed
              show "row_term_well_typed env ghost ?new_colTys resultTy new_row"
                using specialise_row_variant_preserves_typing[
                          OF orig_wt c_lt_colTys colTy_c_dt ctor_h_info tyargs_len_h
                             s_c_ty row_fresh row_payload_consistent]
                      spec_some orig_row_eq
                by simp
            qed
            thus ?thesis by (simp add: list_all_iff)
          qed

          \<comment> \<open>The new colTys are well-kinded.\<close>
          have new_colTys_wk: "list_all (is_well_kinded env) ?new_colTys"
          proof (cases has_payload)
            case True
            \<comment> \<open>The new payload type is well-kinded: from the well-kindedness of
                 colTys ! c = CoreTy_Datatype dtName tyArgs and the well-kindedness of
                 payloadTy_h under tyvars_h (from tyenv_well_formed).\<close>
            have payloadTy_h_wk:
              "is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list tyvars_h \<rparr>) payloadTy_h"
              using "1.prems"(3) ctor_h_info
              unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def by auto
            have tyvars_h_distinct: "distinct tyvars_h"
              using "1.prems"(3) ctor_h_info
              unfolding tyenv_well_formed_def tyenv_ctor_tyvars_distinct_def by auto
            have colTy_c_wk: "is_well_kinded env (CoreTy_Datatype dtName tyArgs)"
              using colTys_wk c_lt_colTys colTy_c_dt
              by (metis list_all_length)
            hence tyArgs_wk: "list_all (is_well_kinded env) tyArgs"
              by (auto split: option.splits)
            \<comment> \<open>Apply apply_subst_preserves_well_kinded.\<close>
            have new_payTy_wk:
              "is_well_kinded env (apply_subst (fmap_of_list (zip tyvars_h tyArgs)) payloadTy_h)"
            proof (rule apply_subst_preserves_well_kinded[OF payloadTy_h_wk])
              show "TE_Datatypes env = TE_Datatypes (env \<lparr> TE_TypeVars := fset_of_list tyvars_h \<rparr>)"
                by simp
            next
              fix n assume n_in: "n |\<in>| TE_TypeVars (env \<lparr> TE_TypeVars := fset_of_list tyvars_h \<rparr>)"
              hence n_in_tyvars: "n \<in> set tyvars_h" by (simp add: fset_of_list.rep_eq)
              \<comment> \<open>The substitution maps n to the corresponding tyArg.\<close>
              from n_in_tyvars obtain i where i_lt: "i < length tyvars_h"
                and n_eq: "n = tyvars_h ! i" by (auto simp: in_set_conv_nth)
              have lookup_eq: "fmlookup (fmap_of_list (zip tyvars_h tyArgs)) n = Some (tyArgs ! i)"
              proof -
                have zip_nth: "zip tyvars_h tyArgs ! i = (tyvars_h ! i, tyArgs ! i)"
                  using i_lt tyargs_len_h by simp
                have zip_distinct: "distinct (map fst (zip tyvars_h tyArgs))"
                  using tyvars_h_distinct tyargs_len_h
                  by simp
                show ?thesis
                  using zip_nth n_eq i_lt tyargs_len_h zip_distinct
                  by (metis (no_types, lifting) fmlookup_of_list
                            length_zip min.idem nth_mem map_of_eq_Some_iff)
              qed
              have tyArg_i_wk: "is_well_kinded env (tyArgs ! i)"
                using tyArgs_wk i_lt tyargs_len_h by (simp add: list_all_iff)
              show "case fmlookup (fmap_of_list (zip tyvars_h tyArgs)) n of
                      Some ty' \<Rightarrow> is_well_kinded env ty'
                    | None \<Rightarrow> n |\<in>| TE_TypeVars env"
                using lookup_eq tyArg_i_wk by simp
            qed
            show ?thesis using True new_payTy_wk colTys_wk
              by (simp add: list_all_replace_at)
          next
            case False
            show ?thesis using False list_all_drop_at[OF colTys_wk] by simp
          qed

          \<comment> \<open>Scruts after drop_at/replace_at typecheck.\<close>
          have new_scruts_typed:
            "list_all2 (\<lambda>s ty. core_term_type env ghost s = Some ty)
                       ?new_scruts ?new_colTys"
          proof (cases has_payload)
            case True
            have proj_ty: "core_term_type env ghost (CoreTm_VariantProj ?s_c h)
                            = Some (apply_subst (fmap_of_list (zip tyvars_h tyArgs)) payloadTy_h)"
              using s_c_ty colTy_c_dt ctor_h_info tyargs_len_h by simp
            show ?thesis using True
                  list_all2_replace_at[OF scruts_typed c_lt_scruts proj_ty]
              by simp
          next
            case False
            show ?thesis using False list_all2_drop_at[OF scruts_typed c_lt_scruts] by simp
          qed

          \<comment> \<open>Freshness preserved.\<close>
          have new_fresh: "matrix_scrut_freshness (?new_scruts, ?spec_rows)"
            unfolding matrix_scrut_freshness_def
          proof clarify
            fix s :: CoreTerm and new_row :: "CoreTerm Row"
            assume s_in: "s \<in> set ?new_scruts" and nr_in: "new_row \<in> set ?spec_rows"
            from nr_in obtain orig_row where
              orig_in: "orig_row \<in> set rows" and
              spec_some: "specialise_row_variant c ?s_c h has_payload orig_row = Some new_row"
              by (auto simp: List.map_filter_def)
            obtain ops obs obody where
              orig_row_eq: "orig_row = (ops, obs, obody)" by (cases orig_row) auto
            have c_lt_ops: "c < length ops"
              using c_facts orig_in orig_row_eq by auto
            have row_subset:
              "row_var_names new_row |\<subseteq>| row_var_names orig_row"
              using row_var_names_specialise_row_variant_subset[OF c_lt_ops]
                    spec_some orig_row_eq by simp

            have s_in_orig_or_proj:
              "s \<in> set scruts \<or> s = CoreTm_VariantProj ?s_c h"
              using s_in
            proof (cases has_payload)
              case True
              with s_in have "s \<in> set (replace_at c (CoreTm_VariantProj ?s_c h) scruts)" by simp
              \<comment> \<open>Either s is the inserted projection or one of the original scruts.\<close>
              hence "s \<in> {CoreTm_VariantProj ?s_c h} \<union> set scruts"
                by (induction c "(CoreTm_VariantProj ?s_c h)" scruts
                            rule: replace_at.induct) auto
              thus ?thesis by auto
            next
              case False
              with s_in have "s \<in> set (drop_at c scruts)" by simp
              hence "s \<in> set scruts"
                by (induction c scruts rule: drop_at.induct) auto
              thus ?thesis by auto
            qed

            have free_subset:
              "\<exists>s_orig \<in> set scruts. core_term_free_vars s |\<subseteq>| core_term_free_vars s_orig"
            proof (cases "s \<in> set scruts")
              case True thus ?thesis by auto
            next
              case False
              with s_in_orig_or_proj have s_eq: "s = CoreTm_VariantProj ?s_c h" by blast
              have s_free: "core_term_free_vars s = core_term_free_vars ?s_c"
                using s_eq by simp
              have s_c_in: "?s_c \<in> set scruts" using c_lt_scruts by simp
              show ?thesis using s_free s_c_in by force
            qed
            obtain s_orig where s_orig_in: "s_orig \<in> set scruts"
              and s_orig_subset: "core_term_free_vars s |\<subseteq>| core_term_free_vars s_orig"
              using free_subset by blast
            from fresh_inv s_orig_in orig_in have
              "core_term_free_vars s_orig |\<inter>| row_var_names orig_row = {||}"
              by (auto simp: matrix_scrut_freshness_def)
            with s_orig_subset row_subset
            show "core_term_free_vars s |\<inter>| row_var_names new_row = {||}"
              by blast
          qed

          have new_matrix_wt:
            "matrix_term_well_typed env ghost resultTy (?new_scruts, ?spec_rows)"
            unfolding matrix_term_well_typed_def
            using new_scruts_typed new_colTys_wk spec_rows_typed new_fresh
            by (auto simp: list_all2_lengthD)

          have new_payload: "matrix_payload_consistent (?new_scruts, ?spec_rows)"
            unfolding matrix_payload_consistent_def
          proof clarify
            fix new_row1 :: "CoreTerm Row" and new_row2 :: "CoreTerm Row"
            fix h' mpat1 mpat2
            assume nr1_in: "new_row1 \<in> set ?spec_rows"
               and nr2_in: "new_row2 \<in> set ?spec_rows"
               and v1: "(h', mpat1) \<in> row_all_variants new_row1"
               and v2: "(h', mpat2) \<in> row_all_variants new_row2"
            from nr1_in obtain o1 where o1_in: "o1 \<in> set rows"
              and s1: "specialise_row_variant c ?s_c h has_payload o1 = Some new_row1"
              by (auto simp: List.map_filter_def)
            from nr2_in obtain o2 where o2_in: "o2 \<in> set rows"
              and s2: "specialise_row_variant c ?s_c h has_payload o2 = Some new_row2"
              by (auto simp: List.map_filter_def)
            obtain o1ps o1bs o1body where
              o1_eq: "o1 = (o1ps, o1bs, o1body)" by (cases o1) auto
            obtain o2ps o2bs o2body where
              o2_eq: "o2 = (o2ps, o2bs, o2body)" by (cases o2) auto
            have c_lt_o1: "c < length o1ps"
              using c_facts o1_in o1_eq by auto
            have c_lt_o2: "c < length o2ps"
              using c_facts o2_in o2_eq by auto
            have v1_orig: "(h', mpat1) \<in> row_all_variants o1"
              using v1 row_all_variants_specialise_row_variant_subset[OF c_lt_o1] s1 o1_eq
              by (metis in_mono)
            have v2_orig: "(h', mpat2) \<in> row_all_variants o2"
              using v2 row_all_variants_specialise_row_variant_subset[OF c_lt_o2] s2 o2_eq
              by (metis in_mono)
            show "(mpat1 = None) = (mpat2 = None)"
              using "1.prems"(2) o1_in o2_in v1_orig v2_orig
              unfolding matrix_payload_consistent_def by blast
          qed

          have spec_ne: "?spec_rows \<noteq> []"
          proof -
            \<comment> \<open>row_h has c-th pattern DP_Variant h mpat_h with has_payload = (mpat_h \<noteq> None).
                 So specialise_row_variant succeeds on row_h.\<close>
            from row_h_pat_c row_h_eq have rh_ps_c: "rh_ps ! c = DP_Variant h mpat_h" by simp
            have spec_some: "\<exists>new. specialise_row_variant c ?s_c h has_payload row_h = Some new"
              using rh_ps_c row_h_eq has_payload_eq_top
              by (cases mpat_h) auto
            then obtain new where spec_eq: "specialise_row_variant c ?s_c h has_payload row_h = Some new"
              by blast
            have witness: "row_h \<in> {x \<in> set rows.
                              \<exists>y. specialise_row_variant c ?s_c h has_payload x = Some y}"
              using row_h_in spec_eq by blast
            have "the (specialise_row_variant c ?s_c h has_payload row_h) = new"
              using spec_eq by simp
            hence "new \<in> (\<lambda>x. the (specialise_row_variant c ?s_c h has_payload x))
                          ` {x \<in> set rows. \<exists>y. specialise_row_variant c ?s_c h has_payload x = Some y}"
              using witness by blast
            hence "new \<in> set ?spec_rows" by (simp add: List.map_filter_def)
            thus ?thesis by auto
          qed

          have IH:
            "matchtree_term_well_typed env ghost resultTy
              (compile_matrix (?new_scruts, ?spec_rows))"
            using "1.hyps"(3)[OF fnw refl refl refl refl refl head_kind_at_hd refl refl refl
                                new_matrix_wt new_payload "1.prems"(3) spec_ne] .
          show "matchtree_term_well_typed env ghost resultTy
                  (compile_matrix
                    (if has_payload
                     then replace_at c (CoreTm_VariantProj ?s_c h) scruts
                     else drop_at c scruts,
                     ?spec_rows))"
            using IH by simp
        qed

        \<comment> \<open>Default arm well-typed.\<close>
        have default_arm_wt:
          "?has_default \<longrightarrow>
             matchtree_term_well_typed env ghost resultTy
               (compile_matrix (drop_at c scruts, ?default_rows))"
        proof
          assume has_default: ?has_default
          let ?new_colTys = "drop_at c colTys"

          have default_rows_typed:
            "list_all (row_term_well_typed env ghost ?new_colTys resultTy) ?default_rows"
          proof -
            have "\<forall>new_row \<in> set ?default_rows.
                    row_term_well_typed env ghost ?new_colTys resultTy new_row"
            proof
              fix new_row assume "new_row \<in> set ?default_rows"
              then obtain orig_row where orig_in: "orig_row \<in> set rows"
                and spec_some: "default_row c ?s_c orig_row = Some new_row"
                by (auto simp: List.map_filter_def)
              obtain ops obs obody where
                orig_row_eq: "orig_row = (ops, obs, obody)" by (cases orig_row) auto
              from rows_typed orig_in orig_row_eq have
                orig_wt: "row_term_well_typed env ghost colTys resultTy (ops, obs, obody)"
                by (auto simp: list_all_iff)
              from fresh_inv orig_in c_lt_scruts orig_row_eq have
                row_fresh: "row_scrut_fresh ?s_c (ops, obs, obody)"
                by (auto simp: matrix_scrut_freshness_def)
              show "row_term_well_typed env ghost ?new_colTys resultTy new_row"
                using default_row_preserves_typing[
                          OF orig_wt c_lt_colTys s_c_ty row_fresh]
                      spec_some orig_row_eq
                by simp
            qed
            thus ?thesis by (simp add: list_all_iff)
          qed

          have new_scruts_typed:
            "list_all2 (\<lambda>s ty. core_term_type env ghost s = Some ty)
                       (drop_at c scruts) ?new_colTys"
            using list_all2_drop_at[OF scruts_typed c_lt_scruts] .

          have new_fresh: "matrix_scrut_freshness (drop_at c scruts, ?default_rows)"
            unfolding matrix_scrut_freshness_def
          proof clarify
            fix s :: CoreTerm and new_row :: "CoreTerm Row"
            assume s_in: "s \<in> set (drop_at c scruts)" and nr_in: "new_row \<in> set ?default_rows"
            from s_in have s_in_orig: "s \<in> set scruts"
              by (induction c scruts rule: drop_at.induct) auto
            from nr_in obtain orig_row where
              orig_in: "orig_row \<in> set rows" and
              spec_some: "default_row c ?s_c orig_row = Some new_row"
              by (auto simp: List.map_filter_def)
            obtain ops obs obody where
              orig_row_eq: "orig_row = (ops, obs, obody)" by (cases orig_row) auto
            have c_lt_ops: "c < length ops"
              using c_facts orig_in orig_row_eq by auto
            have row_subset:
              "row_var_names new_row |\<subseteq>| row_var_names orig_row"
              using row_var_names_default_row_subset[OF c_lt_ops]
                    spec_some orig_row_eq by simp
            from fresh_inv s_in_orig orig_in have
              "core_term_free_vars s |\<inter>| row_var_names orig_row = {||}"
              by (auto simp: matrix_scrut_freshness_def)
            with row_subset show "core_term_free_vars s |\<inter>| row_var_names new_row = {||}"
              by blast
          qed

          have new_matrix_wt:
            "matrix_term_well_typed env ghost resultTy (drop_at c scruts, ?default_rows)"
            unfolding matrix_term_well_typed_def
            using new_scruts_typed default_rows_typed new_fresh
            by (auto simp: list_all2_lengthD)

          have new_payload: "matrix_payload_consistent (drop_at c scruts, ?default_rows)"
            unfolding matrix_payload_consistent_def
          proof clarify
            fix new_row1 :: "CoreTerm Row" and new_row2 :: "CoreTerm Row"
            fix h' mpat1 mpat2
            assume nr1_in: "new_row1 \<in> set ?default_rows"
               and nr2_in: "new_row2 \<in> set ?default_rows"
               and v1: "(h', mpat1) \<in> row_all_variants new_row1"
               and v2: "(h', mpat2) \<in> row_all_variants new_row2"
            from nr1_in obtain o1 where o1_in: "o1 \<in> set rows"
              and s1: "default_row c ?s_c o1 = Some new_row1"
              by (auto simp: List.map_filter_def)
            from nr2_in obtain o2 where o2_in: "o2 \<in> set rows"
              and s2: "default_row c ?s_c o2 = Some new_row2"
              by (auto simp: List.map_filter_def)
            obtain o1ps o1bs o1body where
              o1_eq: "o1 = (o1ps, o1bs, o1body)" by (cases o1) auto
            obtain o2ps o2bs o2body where
              o2_eq: "o2 = (o2ps, o2bs, o2body)" by (cases o2) auto
            have v1_orig: "(h', mpat1) \<in> row_all_variants o1"
              using v1 row_all_variants_default_row_subset s1 o1_eq by (metis in_mono)
            have v2_orig: "(h', mpat2) \<in> row_all_variants o2"
              using v2 row_all_variants_default_row_subset s2 o2_eq by (metis in_mono)
            show "(mpat1 = None) = (mpat2 = None)"
              using "1.prems"(2) o1_in o2_in v1_orig v2_orig
              unfolding matrix_payload_consistent_def by blast
          qed

          have default_ne: "?default_rows \<noteq> []"
          proof -
            from has_default obtain p where p_in: "p \<in> set ?col_pats"
              and p_wc: "is_wildcard_like p"
              by (meson in_set_conv_nth list_ex_length)
            from p_in obtain orig_row where orig_in: "orig_row \<in> set rows"
              and orig_pat: "fst orig_row ! c = p" by force
            obtain ops obs obody where
              orig_row_eq: "orig_row = (ops, obs, obody)" by (cases orig_row) auto
            from orig_pat orig_row_eq have ops_c_wc: "is_wildcard_like (ops ! c)"
              using p_wc by simp
            have spec_some: "\<exists>new_row. default_row c ?s_c orig_row = Some new_row"
              using ops_c_wc orig_row_eq
              by (cases "ops ! c") auto
            then obtain new_row where spec_eq: "default_row c ?s_c orig_row = Some new_row"
              by blast
            have witness:
              "orig_row \<in> {x \<in> set rows. \<exists>y. default_row c ?s_c x = Some y}"
              using orig_in spec_eq by blast
            have "the (default_row c ?s_c orig_row) = new_row" using spec_eq by simp
            hence "new_row \<in> (\<lambda>x. the (default_row c ?s_c x))
                              ` {x \<in> set rows. \<exists>y. default_row c ?s_c x = Some y}"
              using witness by blast
            hence "new_row \<in> set ?default_rows" by (simp add: List.map_filter_def)
            thus ?thesis by auto
          qed

          show "matchtree_term_well_typed env ghost resultTy
                  (compile_matrix (drop_at c scruts, ?default_rows))"
            using "1.hyps"(1)[OF fnw refl refl refl refl has_default
                                new_matrix_wt new_payload "1.prems"(3) default_ne] .
        qed

        \<comment> \<open>Each head in ?heads: the constructor lookup gives the same dtName.\<close>
        have head_ctor_info:
          "\<forall>(h, hp) \<in> set ?heads.
              \<exists>tyvars_h payloadTy_h.
                fmlookup (TE_DataCtors env) h = Some (dtName, tyvars_h, payloadTy_h)
                \<and> length tyArgs = length tyvars_h"
        proof clarify
          fix h hp
          assume h_in: "(h, hp) \<in> set ?heads"
          from h_in distinct_variant_heads_in_col_pats obtain mpat_h where
            mpat_h_in: "DP_Variant h mpat_h \<in> set ?col_pats"
            by blast
          from mpat_h_in obtain row_h where row_h_in: "row_h \<in> set rows"
            and row_h_pat_c: "fst row_h ! c = DP_Variant h mpat_h"
            by force
          obtain rh_ps rh_bs rh_body where row_h_eq:
            "row_h = (rh_ps, rh_bs, rh_body)" by (cases row_h) auto
          from rows_typed row_h_in row_h_eq have
            row_h_wt: "row_term_well_typed env ghost colTys resultTy (rh_ps, rh_bs, rh_body)"
            by (auto simp: list_all_iff)
          from row_h_wt have
            row_h_compat: "dec_pattern_compatible_list
                            (extend_env_with_bindlist env ghost rh_bs)
                            rh_ps colTys"
            and row_h_len: "length rh_ps = length colTys"
            by (auto simp: Let_def)
          have rh_c: "rh_ps ! c = DP_Variant h mpat_h"
            using row_h_pat_c row_h_eq by simp
          have c_lt_rh: "c < length rh_ps" using c_lt_colTys row_h_len by simp
          have rh_compat_at_c: "dec_pattern_compatible
                                  (extend_env_with_bindlist env ghost rh_bs)
                                  (rh_ps ! c) (colTys ! c)"
            using row_h_compat c_lt_rh row_h_len
            by (auto simp: dec_pattern_compatible_list_iff)
          from rh_compat_at_c rh_c colTy_c_dt
          obtain dtName_h tyvars_h payloadTy_h where
            lookup_eq: "fmlookup (TE_DataCtors (extend_env_with_bindlist env ghost rh_bs)) h
                          = Some (dtName_h, tyvars_h, payloadTy_h)" and
            dtName_eq: "dtName_h = dtName" and
            len_eq: "length tyArgs = length tyvars_h"
            by (cases "fmlookup (TE_DataCtors (extend_env_with_bindlist env ghost rh_bs)) h")
               (auto split: option.splits)
          from lookup_eq dtName_eq TE_DataCtors_eq
          have lookup_in_env:
            "fmlookup (TE_DataCtors env) h = Some (dtName, tyvars_h, payloadTy_h)" by simp
          from lookup_in_env len_eq
          show "\<exists>tyvars_h payloadTy_h.
                  fmlookup (TE_DataCtors env) h = Some (dtName, tyvars_h, payloadTy_h)
                  \<and> length tyArgs = length tyvars_h"
            by blast
        qed

        \<comment> \<open>Head pattern compatibility.\<close>
        have head_pats_compat:
          "list_all (\<lambda>(p, _). pattern_compatible env p (colTys ! c))
                    (map ?head_arm ?heads @ ?default_arm)"
        proof -
          have head_arm_pats_compat:
            "\<forall>(h, hp) \<in> set ?heads.
                pattern_compatible env (CorePat_Variant h CorePat_Wildcard) (colTys ! c)"
          proof clarify
            fix h hp
            assume h_in: "(h, hp) \<in> set ?heads"
            from head_ctor_info h_in obtain tyvars_h payloadTy_h where
              h_lookup: "fmlookup (TE_DataCtors env) h = Some (dtName, tyvars_h, payloadTy_h)"
              and h_len: "length tyArgs = length tyvars_h"
              by blast
            from h_lookup h_len
            show "pattern_compatible env (CorePat_Variant h CorePat_Wildcard) (colTys ! c)"
              using colTy_c_dt by simp
          qed
          show ?thesis
            using head_arm_pats_compat
            by (auto simp: list_all_iff split_def Let_def)
        qed

        \<comment> \<open>arms non-empty.\<close>
        have heads_ne: "?heads \<noteq> []"
        proof -
          from head_pat_in_col head_pat_eq2 have v_in: "DP_Variant h_top mpat_top \<in> set ?col_pats"
            by simp
          have aux: "\<And>ps. DP_Variant h_top mpat_top \<in> set ps \<Longrightarrow> distinct_variant_heads ps \<noteq> []"
          proof -
            fix ps :: "DecPattern list"
            assume "DP_Variant h_top mpat_top \<in> set ps"
            thus "distinct_variant_heads ps \<noteq> []"
              by (induction ps rule: distinct_variant_heads.induct) auto
          qed
          show ?thesis using aux[OF v_in] .
        qed
        have arms_ne: "map ?head_arm ?heads @ ?default_arm \<noteq> []"
          using heads_ne by simp

        \<comment> \<open>Final assembly: each arm is well-typed.\<close>
        have all_arms_wt:
          "list_all (\<lambda>(_, sub). matchtree_term_well_typed env ghost resultTy sub)
                    (map ?head_arm ?heads @ ?default_arm)"
        proof -
          have head_arms_wt:
            "list_all (\<lambda>(_, sub). matchtree_term_well_typed env ghost resultTy sub)
                      (map ?head_arm ?heads)"
            using head_arm_wt
            by (auto simp: list_all_iff split_def Let_def)
          have default_arm_wt_list:
            "list_all (\<lambda>(_, sub). matchtree_term_well_typed env ghost resultTy sub)
                      ?default_arm"
            using default_arm_wt by (cases ?has_default) auto
          show ?thesis using head_arms_wt default_arm_wt_list by simp
        qed

        show ?thesis
          unfolding compile_eq Let_def
          using s_c_ty arms_ne head_pats_compat all_arms_wt
          by (simp del: compile_matrix.simps)
      qed
    qed
  qed
qed

(* Corollary for the public entry point compile_match. The wrapping
   MT_Bind freshName scrutTy scrut converts the scrutinee into a column
   scrutinee that's a fresh CoreTm_Var, ensuring the matrix freshness
   invariant by construction. *)
theorem compile_match_preserves_typing:
  assumes scrut_ty: "core_term_type env ghost scrut = Some scrutTy"
      and env_wf: "tyenv_well_formed env"
      and rows_ne: "rows \<noteq> []"
      and rows_wt:
        "list_all
            (\<lambda>(p, body).
               dec_pattern_compatible
                 (extend_env_with_bind env ghost freshName scrutTy) p scrutTy
               \<and> pattern_var_names_distinct [p]
               \<and> core_term_type
                   (extend_env_with_pattern_vars
                      (extend_env_with_bind env ghost freshName scrutTy) ghost [p])
                   ghost body = Some resultTy
               \<and> freshName |\<notin>| dec_pattern_var_names p)
            rows"
      and payload_consistent_rows:
        "\<forall>(p1, body1) \<in> set rows. \<forall>(p2, body2) \<in> set rows.
           \<forall>h mpat1 mpat2.
              (h, mpat1) \<in> dec_pattern_all_variants p1
              \<and> (h, mpat2) \<in> dec_pattern_all_variants p2
              \<longrightarrow> (mpat1 = None) = (mpat2 = None)"
      and runtime_constraint:
        "ghost = NotGhost \<Longrightarrow> is_runtime_type env scrutTy"
  shows "matchtree_term_well_typed env ghost resultTy
           (compile_match scrut scrutTy freshName rows)"
proof -
  let ?env' = "extend_env_with_bind env ghost freshName scrutTy"
  let ?translated_rows = "map (\<lambda>(p, body). ([p], [], body)) rows"

  \<comment> \<open>compile_match unfolds to MT_Bind wrapping compile_matrix.\<close>
  have compile_eq:
    "compile_match scrut scrutTy freshName rows
     = MT_Bind Var freshName scrutTy scrut
         (compile_matrix ([CoreTm_Var freshName], ?translated_rows))"
    by (simp add: compile_match_def)

  \<comment> \<open>Translated rows is non-empty.\<close>
  have translated_ne: "?translated_rows \<noteq> []" using rows_ne by simp

  \<comment> \<open>The new scrutinee CoreTm_Var freshName typechecks at scrutTy under env'.\<close>
  have scrut_var_ty: "core_term_type ?env' ghost (CoreTm_Var freshName) = Some scrutTy"
  proof -
    have lookup: "tyenv_lookup_var ?env' freshName = Some scrutTy"
      unfolding tyenv_lookup_var_def extend_env_with_bind_def by simp
    have ghost_ok: "ghost = NotGhost \<longrightarrow> \<not> tyenv_var_ghost ?env' freshName"
      unfolding tyenv_var_ghost_def extend_env_with_bind_def
      by simp
    show ?thesis using lookup ghost_ok by (simp split: option.splits if_splits)
  qed

  \<comment> \<open>Each translated row is well-typed against [scrutTy].\<close>
  have rows_typed:
    "list_all (row_term_well_typed ?env' ghost [scrutTy] resultTy) ?translated_rows"
  proof -
    have "\<forall>row \<in> set ?translated_rows.
            row_term_well_typed ?env' ghost [scrutTy] resultTy row"
    proof
      fix row :: "CoreTerm Row"
      assume row_in: "row \<in> set ?translated_rows"
      then obtain p body where
        p_body: "(p, body) \<in> set rows" "row = ([p], [], body)"
        by auto
      with rows_wt have
        compat: "dec_pattern_compatible ?env' p scrutTy" and
        distinct: "pattern_var_names_distinct [p]" and
        body_ty: "core_term_type
                    (extend_env_with_pattern_vars ?env' ghost [p]) ghost body
                  = Some resultTy"
        by (auto simp: list_all_iff)
      show "row_term_well_typed ?env' ghost [scrutTy] resultTy row"
        unfolding p_body
        using compat distinct body_ty
        by (auto simp: Let_def)
    qed
    thus ?thesis by (simp add: list_all_iff)
  qed

  \<comment> \<open>Matrix scrutinee freshness: free_vars (CoreTm_Var freshName) = {freshName},
       and freshName |\<notin>| dec_pattern_var_names p for every row p.\<close>
  have scrut_free_vars: "core_term_free_vars (CoreTm_Var freshName) = {|freshName|}"
    by simp
  have freshness:
    "matrix_scrut_freshness ([CoreTm_Var freshName], ?translated_rows)"
  proof -
    have "\<forall>(p, body) \<in> set rows.
            core_term_free_vars (CoreTm_Var freshName)
              |\<inter>| row_var_names ([p], [], body) = {||}"
    proof clarify
      fix p body assume p_body: "(p, body) \<in> set rows"
      with rows_wt have not_in: "freshName |\<notin>| dec_pattern_var_names p"
        by (auto simp: list_all_iff)
      show "core_term_free_vars (CoreTm_Var freshName)
              |\<inter>| row_var_names ([p], [], body) = {||}"
        using not_in by (auto simp: row_var_names_def)
    qed
    thus ?thesis
      unfolding matrix_scrut_freshness_def by auto
  qed

  \<comment> \<open>Derive scrutTy's well-kindedness from env_wf via core_term_type_well_kinded.\<close>
  have scrut_ty_wk: "is_well_kinded env scrutTy"
    using core_term_type_well_kinded[OF scrut_ty env_wf] .

  \<comment> \<open>Well-formedness preserved under env extension by a fresh well-kinded local.\<close>
  have env'_wf: "tyenv_well_formed ?env'"
  proof (cases ghost)
    case Ghost
    let ?env_no_const = "env \<lparr> TE_LocalVars := fmupd freshName scrutTy (TE_LocalVars env),
                                TE_GhostLocals := finsert freshName (TE_GhostLocals env) \<rparr>"
    have step: "tyenv_well_formed ?env_no_const"
      using tyenv_well_formed_add_ghost_var[OF env_wf scrut_ty_wk] .
    have env'_eq: "?env' = ?env_no_const \<lparr> TE_ConstLocals := finsert freshName (TE_ConstLocals env) \<rparr>"
      using Ghost unfolding extend_env_with_bind_def by simp
    show ?thesis
      using tyenv_well_formed_TE_ConstLocals_irrelevant[OF step] env'_eq by simp
  next
    case NotGhost
    have rt: "is_runtime_type env scrutTy" using runtime_constraint NotGhost by simp
    let ?env_no_const = "env \<lparr> TE_LocalVars := fmupd freshName scrutTy (TE_LocalVars env),
                                TE_GhostLocals := fminus (TE_GhostLocals env) {|freshName|} \<rparr>"
    have step: "tyenv_well_formed ?env_no_const"
      using tyenv_well_formed_add_var[OF env_wf scrut_ty_wk rt] .
    have env'_eq: "?env' = ?env_no_const \<lparr> TE_ConstLocals := finsert freshName (TE_ConstLocals env) \<rparr>"
      using NotGhost unfolding extend_env_with_bind_def by simp
    show ?thesis
      using tyenv_well_formed_TE_ConstLocals_irrelevant[OF step] env'_eq by simp
  qed

  \<comment> \<open>Combine into matrix_term_well_typed.\<close>
  have matrix_wt:
    "matrix_term_well_typed ?env' ghost resultTy
       ([CoreTm_Var freshName], ?translated_rows)"
    unfolding matrix_term_well_typed_def
    using scrut_var_ty rows_typed freshness
    by force

  \<comment> \<open>Payload-consistent: lifted from the per-row hypothesis on the user
       rows. Each translated row has [p] as its pattern list, so the
       DP_Variant subpatterns of the row equal those of the user's pattern.\<close>
  have payload_consistent:
    "matrix_payload_consistent ([CoreTm_Var freshName], ?translated_rows)"
    unfolding matrix_payload_consistent_def
  proof clarify
    fix row1 :: "CoreTerm Row" and row2 :: "CoreTerm Row"
    fix h mpat1 mpat2
    assume row1_in: "row1 \<in> set ?translated_rows"
       and row2_in: "row2 \<in> set ?translated_rows"
       and r1_var: "(h, mpat1) \<in> row_all_variants row1"
       and r2_var: "(h, mpat2) \<in> row_all_variants row2"
    from row1_in obtain p1 body1 where
      row1_eq: "row1 = ([p1], [], body1)" and pb1: "(p1, body1) \<in> set rows" by auto
    from row2_in obtain p2 body2 where
      row2_eq: "row2 = ([p2], [], body2)" and pb2: "(p2, body2) \<in> set rows" by auto
    from r1_var row1_eq have p1_var: "(h, mpat1) \<in> dec_pattern_all_variants p1"
      by (simp add: row_all_variants_def)
    from r2_var row2_eq have p2_var: "(h, mpat2) \<in> dec_pattern_all_variants p2"
      by (simp add: row_all_variants_def)
    show "(mpat1 = None) = (mpat2 = None)"
      using payload_consistent_rows pb1 pb2 p1_var p2_var by blast
  qed

  \<comment> \<open>Apply the main theorem.\<close>
  have inner_wt:
    "matchtree_term_well_typed ?env' ghost resultTy
       (compile_matrix ([CoreTm_Var freshName], ?translated_rows))"
    using compile_matrix_preserves_typing[OF matrix_wt payload_consistent env'_wf translated_ne] .

  \<comment> \<open>Wrap with MT_Bind.\<close>
  show ?thesis
    unfolding compile_eq
    using scrut_ty inner_wt by simp
qed


end
