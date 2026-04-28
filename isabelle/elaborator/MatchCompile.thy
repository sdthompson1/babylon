theory MatchCompile
  imports "../bab/BabSyntax" "../core/CoreSyntax"
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
                         in (CorePat_Variant h,
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

(* Public entry point compile_match takes a scrutinee and a non-empty
   list of (DecPattern, elaborated-body) rows. Internally the worker
   compile_matrix operates on an N-column matrix of scrutinees and rows.
   Zero-row inputs are user errors to be rejected upstream. *)

definition compile_match ::
  "CoreTerm \<Rightarrow> (DecPattern \<times> 'body) list \<Rightarrow> 'body MatchTree"
where
  "compile_match scrut rows =
    compile_matrix ([scrut], map (\<lambda>(p, body). ([p], [], body)) rows)"


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

(* TODO: MatchTree well-typedness predicates and typing-preservation
   theorems for compile_match and the two matchtree_to_* translations.
   Target signatures (using core_term_type / core_statement_list_type
   from CoreTypecheck / CoreStmtTypecheck):

     matchtree_term_well_typed  :: CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> CoreType
                                    \<Rightarrow> CoreTerm MatchTree \<Rightarrow> bool
     matchtree_stmts_well_typed :: CoreTyEnv \<Rightarrow> GhostOrNot
                                    \<Rightarrow> CoreStatement list MatchTree \<Rightarrow> bool

   MT_Leaf checks the body against the Core typechecker; MT_Bind extends
   the env; MT_Test recurses into each arm under the same env (Core's
   flat patterns don't bind new variables, since variant payloads are
   projected separately in our translation). *)



end
