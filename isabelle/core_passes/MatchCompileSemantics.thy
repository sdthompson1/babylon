theory MatchCompileSemantics
  imports MatchCompileTyping "../interpreter/CoreValue"
begin

(* Semantic preservation for the Core-to-Core match-compilation pass
   (Phase 5.3 / Checkpoint C of the match-compiler plan).

   This file gives two reference semantics on the matrix IR, both polymorphic 
   in 'body and both independent of the full Core interpreter:

   * matrix_first_match — walks the matrix rows in order and returns
     the body of the first row whose patterns all match the
     corresponding scrutinee values (under a variable environment
     rho :: string \<rightharpoonup> CoreValue).

   * match_tree_eval — walks a MatchTree, evaluating each MT_Test
     scrutinee against rho and following the first arm whose pattern
     matches.

   The headline theorem is compile_matrix_semantics:

     match_tree_eval rho (compile_matrix m) = matrix_first_match rho m

   under the matrix typing invariant from MatchCompileTyping plus
   non-emptiness and a "scrutinees agree with rho" hypothesis.

   We then prove a corollary, compile_match_semantics, which shows that

     match_tree_eval \<rho> (compile_match scrut scrutTy arms)
       = arms_first_match v arms

   where \<rho> is a simplified variable environment, compile_match is
   the full pattern match compiler, and arms_first_match is a model
   of the interpreter's pattern matching behaviour.

   Another file (to be written) should be able to relate match_tree_eval
   and arms_first_match to the real interpreter's pattern matching semantics
   in a straightforward way, and thus prove semantic preservation of
   compile_match when applied to both match terms and match statements.
*)


section \<open>Pure scrutinee walker\<close>

(* The compile_matrix algorithm only ever constructs scrutinees in the
   sublanguage  Var | VariantProj _ _ | RecordProj _ _ . The caller is
   responsible for handing in a top-level scrutinee in this
   sublanguage; the elaborator's finalize_match_term wraps the user's
   scrutinee in a Let, so this invariant holds in practice.

   Defining a dedicated walker keeps Layer 1 free of InterpState and
   fuel: a consumer-side equivalence lemma will later bridge to
   interp_term. *)
fun eval_match_scrut ::
  "(string \<rightharpoonup> CoreValue) \<Rightarrow> CoreTerm \<Rightarrow> CoreValue option"
where
  "eval_match_scrut \<rho> (CoreTm_Var x) = \<rho> x"
| "eval_match_scrut \<rho> (CoreTm_VariantProj t h) =
     (case eval_match_scrut \<rho> t of
        Some (CV_Variant h' v) \<Rightarrow> if h' = h then Some v else None
      | _ \<Rightarrow> None)"
| "eval_match_scrut \<rho> (CoreTm_RecordProj t f) =
     (case eval_match_scrut \<rho> t of
        Some (CV_Record flds) \<Rightarrow> map_of flds f
      | _ \<Rightarrow> None)"
| "eval_match_scrut _ _ = None"


section \<open>Pattern matching\<close>

(* Re-state pattern matching here so Layer 1 does not import
   CoreInterp (which would drag in InterpState). The clauses are
   structurally identical to CoreInterp.pattern_matches; a consumer
   layer will prove they agree. *)
fun matches :: "CoreValue \<Rightarrow> CorePattern \<Rightarrow> bool"
and matches_fields ::
  "(string \<times> CoreValue) list \<Rightarrow> (string \<times> CorePattern) list \<Rightarrow> bool"
where
  "matches (CV_Bool b1) (CorePat_Bool b2) = (b1 = b2)"
| "matches (CV_FiniteInt _ _ i1) (CorePat_Int i2) = (i1 = i2)"
| "matches (CV_Variant c1 v) (CorePat_Variant c2 p) =
     (c1 = c2 \<and> matches v p)"
| "matches (CV_Record vflds) (CorePat_Record pflds) =
     matches_fields vflds pflds"
| "matches _ CorePat_Wildcard = True"
| "matches _ _ = False"
| "matches_fields [] [] = True"
| "matches_fields ((vn, v) # vs) ((pn, p) # ps) =
     (vn = pn \<and> matches v p \<and> matches_fields vs ps)"
| "matches_fields _ _ = False"


section \<open>Reference semantics: matrix_first_match\<close>

(* A row matches the current scrutinee values if every column's pattern
   matches the value obtained by walking the corresponding scrutinee
   term under \<rho>. If any scrutinee fails to evaluate, the row does not
   match. *)
definition row_matches ::
  "(string \<rightharpoonup> CoreValue) \<Rightarrow> CoreTerm list \<Rightarrow> CorePattern list \<Rightarrow> bool"
where
  "row_matches \<rho> scruts ps \<longleftrightarrow>
     list_all2 (\<lambda>s p. case eval_match_scrut \<rho> s of
                       Some v \<Rightarrow> matches v p
                     | None \<Rightarrow> False)
               scruts ps"

(* Reference semantics on a matrix: return the body of the first row
   whose patterns all match the scrutinee values. None if no row
   matches (i.e. a runtime match failure). *)
fun matrix_first_match ::
  "(string \<rightharpoonup> CoreValue) \<Rightarrow> 'body MatchMatrix \<Rightarrow> 'body option"
where
  "matrix_first_match \<rho> (scruts, []) = None"
| "matrix_first_match \<rho> (scruts, (ps, body) # rest) =
     (if row_matches \<rho> scruts ps
      then Some body
      else matrix_first_match \<rho> (scruts, rest))"


section \<open>Tree-walking interpreter: match_tree_eval\<close>

(* Walk a MatchTree under \<rho>. At MT_Test, evaluate the scrutinee and
   follow the first arm whose pattern matches. None means a runtime
   match failure (no arm matched, or a sub-evaluation failed). *)
fun arms_find ::
  "CoreValue \<Rightarrow> (CorePattern \<times> 'body MatchTree) list \<Rightarrow> 'body MatchTree option"
where
  "arms_find _ [] = None"
| "arms_find v ((p, t) # rest) =
     (if matches v p then Some t else arms_find v rest)"

function match_tree_eval ::
  "(string \<rightharpoonup> CoreValue) \<Rightarrow> 'body MatchTree \<Rightarrow> 'body option"
where
  "match_tree_eval \<rho> (MT_Leaf b) = Some b"
| "match_tree_eval \<rho> (MT_Test s arms) =
     (case eval_match_scrut \<rho> s of
        None \<Rightarrow> None
      | Some v \<Rightarrow>
          (case arms_find v arms of
             None \<Rightarrow> None
           | Some t \<Rightarrow> match_tree_eval \<rho> t))"
  by pat_completeness auto

(* Termination: each recursive call moves into a child of the current
   tree. Size on the parametric datatype handles this directly. *)
lemma arms_find_in:
  "arms_find v arms = Some t \<Longrightarrow> t \<in> snd ` set arms"
  by (induction v arms rule: arms_find.induct) (auto split: if_splits)

lemma size_lt_MT_Test:
  "t \<in> snd ` set arms \<Longrightarrow> size t < size (MT_Test s arms)"
proof (induction arms)
  case Nil thus ?case by simp
next
  case (Cons pa rest)
  obtain p t' where pa_eq: "pa = (p, t')" by (cases pa) auto
  show ?case
  proof (cases "t = t'")
    case True with pa_eq show ?thesis by simp
  next
    case False
    with Cons.prems pa_eq have "t \<in> snd ` set rest" by auto
    from Cons.IH[OF this] show ?thesis by simp
  qed
qed

termination match_tree_eval
  by (relation "measure (\<lambda>(\<rho>, t). size t)")
     (auto dest!: arms_find_in size_lt_MT_Test)


section \<open>Scrutinee consistency with the variable environment\<close>

(* The body-polymorphic theorem needs to assume that each column
   scrutinee evaluates under \<rho> to a value of the column's type, so
   the algorithm's sub-scrutinees (CoreTm_VariantProj, CoreTm_RecordProj)
   also evaluate. Stated as a list_all2 mirroring matrix_inv. *)
definition scruts_consistent ::
  "(string \<rightharpoonup> CoreValue) \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTerm list \<Rightarrow> CoreType list \<Rightarrow> bool"
where
  "scruts_consistent \<rho> env scruts colTys \<longleftrightarrow>
     list_all2 (\<lambda>s ty. \<exists>v. eval_match_scrut \<rho> s = Some v
                       \<and> value_has_type env v ty)
               scruts colTys"


section \<open>Small structural facts (provable without the main induction)\<close>

lemma row_matches_Nil [simp]:
  "row_matches \<rho> [] []"
  by (simp add: row_matches_def)

lemma row_matches_length_eq:
  "row_matches \<rho> scruts ps \<Longrightarrow> length scruts = length ps"
  by (auto simp: row_matches_def list_all2_lengthD)

(* Wildcard at the head: the row matches iff the rest matches, provided
   the head scrutinee evaluates. This is the workhorse of the base case
   (row 0 all-wildcards \<Rightarrow> row 0 always matches when scrutinees evaluate). *)
lemma row_matches_Cons_wildcard:
  assumes "eval_match_scrut \<rho> s = Some v"
  shows "row_matches \<rho> (s # ss) (CorePat_Wildcard # ps)
           \<longleftrightarrow> row_matches \<rho> ss ps"
  using assms by (simp add: row_matches_def)

lemma all_wildcards_match:
  assumes "list_all2 (\<lambda>s p. \<exists>v. eval_match_scrut \<rho> s = Some v) scruts ps"
  assumes "list_all (\<lambda>p. p = CorePat_Wildcard) ps"
  shows "row_matches \<rho> scruts ps"
  using assms
proof (induction scruts ps rule: list_all2_induct)
  case Nil show ?case by simp
next
  case (Cons s ss p ps)
  then obtain v where "eval_match_scrut \<rho> s = Some v" by blast
  with Cons show ?case
    by (simp add: row_matches_def)
qed

(* Singleton-column collapse, useful for the entry-point corollary. *)
lemma row_matches_singleton:
  "row_matches \<rho> [s] [p]
     \<longleftrightarrow> (case eval_match_scrut \<rho> s of
            Some v \<Rightarrow> matches v p
          | None \<Rightarrow> False)"
  by (simp add: row_matches_def)

(* Every body reachable from match_tree_eval comes from match_tree_bodies.
   Useful for stitching with bodies_subset. *)
lemma match_tree_eval_body_in_bodies:
  "match_tree_eval \<rho> t = Some b \<Longrightarrow> b \<in> match_tree_bodies t"
proof (induction \<rho> t rule: match_tree_eval.induct)
  case (1 \<rho> b') thus ?case by simp
next
  case (2 \<rho> s arms)
  show ?case
  proof (cases "eval_match_scrut \<rho> s")
    case None with "2.prems" show ?thesis by simp
  next
    case (Some v)
    show ?thesis
    proof (cases "arms_find v arms")
      case None with Some "2.prems" show ?thesis by simp
    next
      case t'_some: (Some t')
      from arms_find_in[OF t'_some] have t'_in: "t' \<in> snd ` set arms" .
      from "2.prems" Some t'_some
      have rec: "match_tree_eval \<rho> t' = Some b" by simp
      from "2.IH"[OF Some t'_some rec]
      have "b \<in> match_tree_bodies t'" .
      with t'_in show ?thesis by force
    qed
  qed
qed


section \<open>Projection-evaluation lemmas (used by the main proof's variant / record cases)\<close>

(* When a variant scrutinee evaluates to CV_Variant h v, the sub-scrutinee
   produced by the algorithm (CoreTm_VariantProj s h) evaluates to v. *)
lemma eval_match_scrut_VariantProj_match:
  assumes "eval_match_scrut \<rho> s = Some (CV_Variant h v)"
  shows "eval_match_scrut \<rho> (CoreTm_VariantProj s h) = Some v"
  using assms by simp

(* Wrong ctor: the projection fails. The algorithm only takes the arm
   for ctor h after a successful test, so this is the off-path case. *)
lemma eval_match_scrut_VariantProj_mismatch:
  assumes "eval_match_scrut \<rho> s = Some (CV_Variant h' v)"
  assumes "h' \<noteq> h"
  shows "eval_match_scrut \<rho> (CoreTm_VariantProj s h) = None"
  using assms by simp

(* Record field projection. *)
lemma eval_match_scrut_RecordProj:
  assumes "eval_match_scrut \<rho> s = Some (CV_Record flds)"
  assumes "map_of flds f = Some v"
  shows "eval_match_scrut \<rho> (CoreTm_RecordProj s f) = Some v"
  using assms by simp


section \<open>List arithmetic for row-survival lemmas\<close>

(* row_matches splits at any column index. The head step is matches
   on (scruts!c, ps!c); the tail steps are matches at the drop_at indices. *)
lemma row_matches_drop_at_split:
  assumes "length scruts = length ps"
  assumes "c < length ps"
  shows "row_matches \<rho> scruts ps
           \<longleftrightarrow> (case eval_match_scrut \<rho> (scruts ! c) of
                  Some v \<Rightarrow> matches v (ps ! c)
                | None \<Rightarrow> False)
             \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
  using assms
proof (induction c arbitrary: scruts ps)
  case (0 scruts ps)
  then obtain s ss p ps' where eqs: "scruts = s # ss" "ps = p # ps'"
    by (metis neq_Nil_conv list.size(3) not_less0)
  show ?case
    unfolding eqs row_matches_def
    by (simp only: nth_Cons_0 drop_at.simps list_all2_Cons)
next
  case (Suc c scruts ps)
  then obtain s ss p ps' where eqs: "scruts = s # ss" "ps = p # ps'"
    by (metis neq_Nil_conv list.size(3) not_less0)
  from Suc.prems eqs have ih: "length ss = length ps'" "c < length ps'" by simp_all
  from Suc.IH[OF ih] show ?case
    unfolding eqs row_matches_def
    by (simp only: nth_Cons_Suc drop_at.simps list_all2_Cons) auto
qed

(* For replace_at on patterns (variant payload swap): the row matches
   the updated pattern list iff the original list matched, but with the
   col c match replaced by the new sub-pattern's match against the new
   col c scrutinee. *)
lemma row_matches_replace_at:
  assumes "length scruts = length ps"
  assumes "c < length ps"
  shows "row_matches \<rho> (replace_at c s' scruts) (replace_at c p' ps)
           \<longleftrightarrow> (case eval_match_scrut \<rho> s' of
                  Some v \<Rightarrow> matches v p'
                | None \<Rightarrow> False)
             \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
  using assms
proof (induction c arbitrary: scruts ps)
  case (0 scruts ps)
  then obtain s ss p ps' where eqs: "scruts = s # ss" "ps = p # ps'"
    by (metis neq_Nil_conv list.size(3) not_less0)
  show ?case
    unfolding eqs row_matches_def
    by (simp only: replace_at.simps drop_at.simps list_all2_Cons)
next
  case (Suc c scruts ps)
  then obtain s ss p ps' where eqs: "scruts = s # ss" "ps = p # ps'"
    by (metis neq_Nil_conv list.size(3) not_less0)
  from Suc.prems eqs have ih: "length ss = length ps'" "c < length ps'" by simp_all
  from Suc.IH[OF ih] show ?case
    unfolding eqs row_matches_def
    by (simp only: replace_at.simps drop_at.simps list_all2_Cons) auto
qed

(* For splice_at on both patterns and scruts (record expansion). The row
   matches the spliced lists iff the original list matched, with the col
   c slot replaced by a length-n list_all2 over the spliced segments. *)
lemma row_matches_splice_at:
  assumes "length scruts = length ps"
  assumes "c < length ps"
  assumes "length scruts' = length ps'"
  shows "row_matches \<rho> (splice_at c scruts' scruts) (splice_at c ps' ps)
           \<longleftrightarrow> row_matches \<rho> scruts' ps'
             \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
  using assms
proof (induction c arbitrary: scruts ps)
  case (0 scruts ps)
  then obtain s ss p ps'' where eqs: "scruts = s # ss" "ps = p # ps''"
    by (metis neq_Nil_conv list.size(3) not_less0)
  from 0 eqs have len_eq: "length ss = length ps''" by simp
  show ?case
    unfolding eqs row_matches_def
    by (simp only: splice_at.simps drop_at.simps)
       (auto simp: list_all2_append assms(3) len_eq)
next
  case (Suc c scruts ps)
  then obtain s ss p ps'' where eqs: "scruts = s # ss" "ps = p # ps''"
    by (metis neq_Nil_conv list.size(3) not_less0)
  from Suc.prems eqs have ih: "length ss = length ps''" "c < length ps''" by simp_all
  from Suc.IH[OF ih Suc.prems(3)] show ?case
    unfolding eqs row_matches_def
    by (simp only: splice_at.simps drop_at.simps list_all2_Cons) auto
qed


section \<open>Row-survival lemmas (one per algorithmic transformation)\<close>

(* default_row: a row survives the default arm iff its col c is wildcard.
   When it does, source-row matching is equivalent to new-row matching
   modulo the col c scrutinee evaluating. *)
lemma default_row_row_matches:
  assumes "default_row c r = Some r'"
  assumes "length scruts = length (fst r)"
  assumes "c < length (fst r)"
  assumes "eval_match_scrut \<rho> (scruts ! c) = Some v_c"
  shows "row_matches \<rho> scruts (fst r)
           \<longleftrightarrow> row_matches \<rho> (drop_at c scruts) (fst r')"
proof -
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  with assms(1) have col_wc: "ps ! c = CorePat_Wildcard"
    and r'_eq: "r' = (drop_at c ps, body)"
    by (auto split: CorePattern.splits)
  show ?thesis
    using row_matches_drop_at_split[OF assms(2,3)[unfolded r_eq fst_conv]]
          assms(4) col_wc
    by (simp add: r_eq r'_eq)
qed

(* default_row dropped a row (None) — this means col c is non-wildcard.
   We do NOT prove a "source row doesn't match" dual here because col c
   being a Bool/Int/Variant/Record pattern can still match v_c. The
   layer-2 lift for the default-arm case has to use head-enumeration
   completeness, not just default_row's None outcome. *)


(* specialise_row_bool: when v_c matches the head bool h, source-row
   matching equals new-row matching. *)
lemma specialise_row_bool_row_matches:
  assumes "specialise_row_bool c h r = Some r'"
  assumes "length scruts = length (fst r)"
  assumes "c < length (fst r)"
  assumes "eval_match_scrut \<rho> (scruts ! c) = Some (CV_Bool h)"
  shows "row_matches \<rho> scruts (fst r)
           \<longleftrightarrow> row_matches \<rho> (drop_at c scruts) (fst r')"
proof -
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  from assms(1) r_eq have col_cases:
    "(ps ! c = CorePat_Bool h \<and> r' = (drop_at c ps, body))
     \<or> (ps ! c = CorePat_Wildcard \<and> r' = (drop_at c ps, body))"
    by (auto split: CorePattern.splits if_splits)
  from assms(2,3) r_eq have split:
    "row_matches \<rho> scruts (ps)
       \<longleftrightarrow> (case eval_match_scrut \<rho> (scruts ! c) of
              Some v \<Rightarrow> matches v (ps ! c)
            | None \<Rightarrow> False)
         \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
    by (intro row_matches_drop_at_split) auto
  from col_cases assms(4) split show ?thesis
    by (auto simp: r_eq)
qed

(* specialise_row_bool dropped a row (None) AND v_c matches head h — then
   the source row does NOT match. col c must be CorePat_Bool b' with b'\<noteq>h
   (the only way None is returned given the col is bool-or-wildcard headed). *)
lemma specialise_row_bool_row_no_match:
  assumes "specialise_row_bool c h r = None"
  assumes "length scruts = length (fst r)"
  assumes "c < length (fst r)"
  assumes "eval_match_scrut \<rho> (scruts ! c) = Some (CV_Bool h)"
  assumes "head_kind_of (fst r ! c) = Some HK_Bool \<or> fst r ! c = CorePat_Wildcard"
  shows "\<not> row_matches \<rho> scruts (fst r)"
proof -
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  from assms(1) r_eq assms(5)
  obtain b' where col_eq: "ps ! c = CorePat_Bool b'" and ne: "b' \<noteq> h"
    by (cases "ps ! c") (auto split: CorePattern.splits if_splits)
  from assms(2,3) r_eq have split:
    "row_matches \<rho> scruts ps
       \<longleftrightarrow> (case eval_match_scrut \<rho> (scruts ! c) of
              Some v \<Rightarrow> matches v (ps ! c)
            | None \<Rightarrow> False)
         \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
    by (intro row_matches_drop_at_split) auto
  from col_eq ne assms(4) split show ?thesis
    by (simp add: r_eq)
qed


(* specialise_row_int: same shape as bool. *)
lemma specialise_row_int_row_matches:
  assumes "specialise_row_int c h r = Some r'"
  assumes "length scruts = length (fst r)"
  assumes "c < length (fst r)"
  assumes "eval_match_scrut \<rho> (scruts ! c) = Some (CV_FiniteInt sign bits h)"
  shows "row_matches \<rho> scruts (fst r)
           \<longleftrightarrow> row_matches \<rho> (drop_at c scruts) (fst r')"
proof -
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  from assms(1) r_eq have col_cases:
    "(ps ! c = CorePat_Int h \<and> r' = (drop_at c ps, body))
     \<or> (ps ! c = CorePat_Wildcard \<and> r' = (drop_at c ps, body))"
    by (auto split: CorePattern.splits if_splits)
  from assms(2,3) r_eq have split:
    "row_matches \<rho> scruts ps
       \<longleftrightarrow> (case eval_match_scrut \<rho> (scruts ! c) of
              Some v \<Rightarrow> matches v (ps ! c)
            | None \<Rightarrow> False)
         \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
    by (intro row_matches_drop_at_split) auto
  from col_cases assms(4) split show ?thesis
    by (auto simp: r_eq)
qed

lemma specialise_row_int_row_no_match:
  assumes "specialise_row_int c h r = None"
  assumes "length scruts = length (fst r)"
  assumes "c < length (fst r)"
  assumes "eval_match_scrut \<rho> (scruts ! c) = Some (CV_FiniteInt sign bits h)"
  assumes "head_kind_of (fst r ! c) = Some HK_Int \<or> fst r ! c = CorePat_Wildcard"
  shows "\<not> row_matches \<rho> scruts (fst r)"
proof -
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  from assms(1) r_eq assms(5)
  obtain i' where col_eq: "ps ! c = CorePat_Int i'" and ne: "i' \<noteq> h"
    by (cases "ps ! c") (auto split: CorePattern.splits if_splits)
  from assms(2,3) r_eq have split:
    "row_matches \<rho> scruts ps
       \<longleftrightarrow> (case eval_match_scrut \<rho> (scruts ! c) of
              Some v \<Rightarrow> matches v (ps ! c)
            | None \<Rightarrow> False)
         \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
    by (intro row_matches_drop_at_split) auto
  from col_eq ne assms(4) split show ?thesis
    by (simp add: r_eq)
qed


(* specialise_row_variant: when v_c is CV_Variant h v_pl (i.e. ctor matches
   head h), source-row matching equals new-row matching where col c is
   replaced by the variant's payload sub-pattern and the new col-c
   scrutinee CoreTm_VariantProj s_c h evaluates to v_pl. *)
lemma specialise_row_variant_row_matches:
  assumes "specialise_row_variant c h r = Some r'"
  assumes "length scruts = length (fst r)"
  assumes "c < length (fst r)"
  assumes "scruts ! c = s_c"
  assumes "eval_match_scrut \<rho> s_c = Some (CV_Variant h v_pl)"
  shows "row_matches \<rho> scruts (fst r)
           \<longleftrightarrow> row_matches \<rho> (replace_at c (CoreTm_VariantProj s_c h) scruts) (fst r')"
proof -
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  from assms(1) r_eq have col_cases:
    "(\<exists>payload. ps ! c = CorePat_Variant h payload
       \<and> r' = (replace_at c payload ps, body))
     \<or> (ps ! c = CorePat_Wildcard
       \<and> r' = (replace_at c CorePat_Wildcard ps, body))"
    by (auto split: CorePattern.splits if_splits)
  from assms(2,3) r_eq have split_src:
    "row_matches \<rho> scruts ps
       \<longleftrightarrow> (case eval_match_scrut \<rho> (scruts ! c) of
              Some v \<Rightarrow> matches v (ps ! c)
            | None \<Rightarrow> False)
         \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
    by (intro row_matches_drop_at_split) auto
  have new_scrut_eval: "eval_match_scrut \<rho> (CoreTm_VariantProj s_c h) = Some v_pl"
    by (rule eval_match_scrut_VariantProj_match[OF assms(5)])
  show ?thesis
  proof (cases "ps ! c = CorePat_Wildcard")
    case True
    with col_cases have r'_eq: "r' = (replace_at c CorePat_Wildcard ps, body)" by auto
    from assms(2,3) r_eq
    have split_new:
      "row_matches \<rho> (replace_at c (CoreTm_VariantProj s_c h) scruts)
                      (replace_at c CorePat_Wildcard ps)
         \<longleftrightarrow> (case eval_match_scrut \<rho> (CoreTm_VariantProj s_c h) of
                Some v \<Rightarrow> matches v CorePat_Wildcard
              | None \<Rightarrow> False)
           \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
      by (intro row_matches_replace_at) auto
    show ?thesis
      using True assms(4,5) new_scrut_eval split_src split_new
      by (simp add: r_eq r'_eq)
  next
    case False
    with col_cases obtain payload where
      col_eq: "ps ! c = CorePat_Variant h payload" and
      r'_eq: "r' = (replace_at c payload ps, body)"
      by blast
    from assms(2,3) r_eq
    have split_new:
      "row_matches \<rho> (replace_at c (CoreTm_VariantProj s_c h) scruts)
                      (replace_at c payload ps)
         \<longleftrightarrow> (case eval_match_scrut \<rho> (CoreTm_VariantProj s_c h) of
                Some v \<Rightarrow> matches v payload
              | None \<Rightarrow> False)
           \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
      by (intro row_matches_replace_at) auto
    show ?thesis
      using col_eq assms(4,5) new_scrut_eval split_src split_new
      by (simp add: r_eq r'_eq)
  qed
qed

(* specialise_row_variant dropped a row, ctor doesn't match. *)
lemma specialise_row_variant_row_no_match:
  assumes "specialise_row_variant c h r = None"
  assumes "length scruts = length (fst r)"
  assumes "c < length (fst r)"
  assumes "eval_match_scrut \<rho> (scruts ! c) = Some (CV_Variant h v_pl)"
  assumes "head_kind_of (fst r ! c) = Some HK_Variant \<or> fst r ! c = CorePat_Wildcard"
  shows "\<not> row_matches \<rho> scruts (fst r)"
proof -
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  from assms(1) r_eq assms(5)
  obtain h' payload where
    col_eq: "ps ! c = CorePat_Variant h' payload" and ne: "h' \<noteq> h"
    by (cases "ps ! c") (auto split: CorePattern.splits if_splits)
  from assms(2,3) r_eq have split:
    "row_matches \<rho> scruts ps
       \<longleftrightarrow> (case eval_match_scrut \<rho> (scruts ! c) of
              Some v \<Rightarrow> matches v (ps ! c)
            | None \<Rightarrow> False)
         \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
    by (intro row_matches_drop_at_split) auto
  from col_eq ne assms(4) split show ?thesis
    by (simp add: r_eq)
qed


(* Key bridge: under distinctness, projection through s_c on any field
   name resolves to the value map_of vflds finds. *)
lemma eval_match_scrut_RecordProj_map_of:
  assumes "eval_match_scrut \<rho> s_c = Some (CV_Record vflds)"
  shows "eval_match_scrut \<rho> (CoreTm_RecordProj s_c f) = map_of vflds f"
  using assms by simp

(* Auxiliary: matches_fields equals list_all2 on (name eq + matches val pat). *)
lemma matches_fields_iff_list_all2:
  assumes "length vs = length ps"
  shows "matches_fields vs ps
           \<longleftrightarrow> list_all2 (\<lambda>(vn, v) (pn, p). vn = pn \<and> matches v p) vs ps"
  using assms
proof (induction vs ps rule: list_induct2)
  case Nil show ?case by simp
next
  case (Cons x xs y ys)
  obtain vn v where x_eq: "x = (vn, v)" by (cases x)
  obtain pn p where y_eq: "y = (pn, p)" by (cases y)
  show ?case using Cons x_eq y_eq by simp
qed

(* Helper: when s_c evaluates to CV_Record vflds with distinct field names
   and pflds shares the same names positionally, matches_fields coincides
   with row_matches over the projection scrutinees and pattern values. *)
lemma matches_fields_via_record_proj:
  assumes s_c_eval: "eval_match_scrut \<rho> s_c = Some (CV_Record vflds)"
  assumes distinct: "distinct (map fst vflds)"
  assumes names_eq: "map fst vflds = map fst pflds"
  shows "matches_fields vflds pflds
           \<longleftrightarrow> row_matches \<rho>
                 (map (\<lambda>f. CoreTm_RecordProj s_c f) (map fst vflds))
                 (map snd pflds)"
proof -
  have len_vp: "length vflds = length pflds"
    using names_eq by (metis length_map)
  \<comment> \<open>Each projection through s_c on a name from vflds resolves positionally.\<close>
  have proj_at_i: "\<forall>i < length vflds.
        eval_match_scrut \<rho> (CoreTm_RecordProj s_c (fst (vflds ! i)))
        = Some (snd (vflds ! i))"
  proof (intro allI impI)
    fix i assume i_lt: "i < length vflds"
    have in_set: "(fst (vflds ! i), snd (vflds ! i)) \<in> set vflds"
      using i_lt by (metis nth_mem prod.collapse)
    have lookup: "map_of vflds (fst (vflds ! i)) = Some (snd (vflds ! i))"
      using distinct in_set by (rule map_of_is_SomeI)
    show "eval_match_scrut \<rho> (CoreTm_RecordProj s_c (fst (vflds ! i)))
            = Some (snd (vflds ! i))"
      using s_c_eval lookup by simp
  qed
  \<comment> \<open>Translate matches_fields to per-index condition. \<close>
  have mf_iff: "matches_fields vflds pflds
                  \<longleftrightarrow> (\<forall>i < length vflds.
                         fst (vflds ! i) = fst (pflds ! i)
                       \<and> matches (snd (vflds ! i)) (snd (pflds ! i)))"
    using len_vp matches_fields_iff_list_all2[OF len_vp]
    by (simp add: list_all2_conv_all_nth case_prod_unfold)
  \<comment> \<open>Translate row_matches to per-index condition (using proj_at_i).\<close>
  have rm_iff: "row_matches \<rho>
                  (map (\<lambda>f. CoreTm_RecordProj s_c f) (map fst vflds))
                  (map snd pflds)
                \<longleftrightarrow> (\<forall>i < length vflds.
                       matches (snd (vflds ! i)) (snd (pflds ! i)))"
  proof -
    have len_proj: "length (map (\<lambda>f. CoreTm_RecordProj s_c f) (map fst vflds))
                    = length (map snd pflds)"
      using len_vp by simp
    have "row_matches \<rho>
            (map (\<lambda>f. CoreTm_RecordProj s_c f) (map fst vflds))
            (map snd pflds)
          \<longleftrightarrow> (\<forall>i < length vflds.
                 case eval_match_scrut \<rho> (CoreTm_RecordProj s_c (fst (vflds ! i))) of
                   Some v' \<Rightarrow> matches v' (snd (pflds ! i))
                 | None \<Rightarrow> False)"
      unfolding row_matches_def
      using len_vp
      by (auto simp: list_all2_conv_all_nth split: option.splits)
    also have "\<dots> \<longleftrightarrow> (\<forall>i < length vflds.
                          matches (snd (vflds ! i)) (snd (pflds ! i)))"
      using proj_at_i by force
    finally show ?thesis .
  qed
  \<comment> \<open>Combine: matches_fields adds the per-index name equality which is also
      implied by names_eq.\<close>
  have names_at_i: "\<forall>i < length vflds. fst (vflds ! i) = fst (pflds ! i)"
    using names_eq len_vp by (metis nth_map)
  show ?thesis
    using mf_iff rm_iff names_at_i by blast
qed


(* expand_record_row: record column is decomposed. Lossless — always
   returns Some (the function is total, not partial). When v_c is
   CV_Record vflds with field names matching fld_names positionally,
   source-row matching equals expanded-row matching. *)
lemma expand_record_row_row_matches:
  assumes "length scruts = length (fst r)"
  assumes "c < length (fst r)"
  assumes "scruts ! c = s_c"
  assumes "eval_match_scrut \<rho> s_c = Some (CV_Record vflds)"
  assumes "distinct (map fst vflds)"
  assumes "map fst vflds = fld_names"
  assumes "head_kind_of (fst r ! c) = Some (HK_Record fld_names)
           \<or> fst r ! c = CorePat_Wildcard"
  shows "row_matches \<rho> scruts (fst r)
           \<longleftrightarrow> row_matches \<rho>
                 (expand_record_scruts c s_c fld_names scruts)
                 (fst (expand_record_row c fld_names r))"
proof -
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  from assms(7) r_eq have col_cases:
    "(\<exists>row_flds. ps ! c = CorePat_Record row_flds
       \<and> map fst row_flds = fld_names)
     \<or> ps ! c = CorePat_Wildcard"
    by (cases "ps ! c") (auto)
  from assms(1,2) r_eq have src_split:
    "row_matches \<rho> scruts ps
       \<longleftrightarrow> (case eval_match_scrut \<rho> (scruts ! c) of
              Some v \<Rightarrow> matches v (ps ! c)
            | None \<Rightarrow> False)
         \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
    by (intro row_matches_drop_at_split) auto

  let ?proj_scruts = "map (\<lambda>f. CoreTm_RecordProj s_c f) fld_names"

  show ?thesis
  proof (cases "ps ! c = CorePat_Wildcard")
    case True
    let ?new_ps = "replicate (length fld_names) CorePat_Wildcard"
    from True have new_row_eq:
      "expand_record_row c fld_names r
         = (splice_at c ?new_ps ps, body)"
      by (simp add: r_eq)
    have len_eq': "length ?proj_scruts = length ?new_ps" by simp
    have new_split:
      "row_matches \<rho>
         (splice_at c ?proj_scruts scruts)
         (splice_at c ?new_ps ps)
         \<longleftrightarrow> row_matches \<rho> ?proj_scruts ?new_ps
           \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
      using assms(1,2) r_eq len_eq'
      by (intro row_matches_splice_at) auto
    \<comment> \<open>Wildcard match: row_matches on the projected scruts and an
        all-wildcard pattern list reduces to "each projection evaluates".
        Each projection does evaluate (to map_of vflds f, which under
        name agreement always Some-resolves).\<close>
    have all_wc_match: "row_matches \<rho> ?proj_scruts ?new_ps"
      unfolding row_matches_def
    proof (rule list_all2_all_nthI)
      show "length ?proj_scruts = length ?new_ps" using len_eq' .
    next
      fix i assume i_lt: "i < length ?proj_scruts"
      hence i_lt': "i < length fld_names" by simp
      let ?f = "fld_names ! i"
      have proj_i: "?proj_scruts ! i = CoreTm_RecordProj s_c ?f"
        using i_lt' by simp
      have new_i: "?new_ps ! i = CorePat_Wildcard"
        using i_lt' by simp
      have f_in: "?f \<in> set fld_names" using i_lt' by simp
      with assms(6) have "?f \<in> set (map fst vflds)" by simp
      then obtain v_f where vf: "map_of vflds ?f = Some v_f"
        by (metis list.set_map map_of_eq_None_iff not_None_eq)
      hence eval_f: "eval_match_scrut \<rho> (CoreTm_RecordProj s_c ?f) = Some v_f"
        using assms(4) by simp
      show "case eval_match_scrut \<rho> (?proj_scruts ! i) of
              Some v \<Rightarrow> matches v (?new_ps ! i) | None \<Rightarrow> False"
        unfolding proj_i new_i using eval_f by simp
    qed
    have src_matches_col:
      "(case eval_match_scrut \<rho> (scruts ! c) of
          Some v \<Rightarrow> matches v (ps ! c) | None \<Rightarrow> False)"
      using True assms(3,4) by simp
    show ?thesis
      using src_split new_split all_wc_match src_matches_col
      unfolding expand_record_scruts_def new_row_eq r_eq
      by (simp add: True)
  next
    case False
    with col_cases obtain row_flds where
      col_eq: "ps ! c = CorePat_Record row_flds" and
      fnames: "map fst row_flds = fld_names"
      by blast
    let ?new_ps = "map snd row_flds"
    from col_eq have new_row_eq:
      "expand_record_row c fld_names r
         = (splice_at c ?new_ps ps, body)"
      by (simp add: r_eq)
    from fnames have len_match: "length ?new_ps = length fld_names" by auto
    have len_eq': "length ?proj_scruts = length ?new_ps"
      using len_match by simp
    have new_split:
      "row_matches \<rho>
         (splice_at c ?proj_scruts scruts)
         (splice_at c ?new_ps ps)
         \<longleftrightarrow> row_matches \<rho> ?proj_scruts ?new_ps
           \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
      using assms(1,2) r_eq len_eq'
      by (intro row_matches_splice_at) auto
    have names_agree: "map fst vflds = map fst row_flds"
      using assms(6) fnames by simp
    have col_match_iff:
      "matches (CV_Record vflds) (CorePat_Record row_flds)
         \<longleftrightarrow> row_matches \<rho> ?proj_scruts ?new_ps"
      using matches_fields_via_record_proj[OF assms(4) assms(5) names_agree]
            assms(6) names_agree
      by simp
    have src_matches_col:
      "(case eval_match_scrut \<rho> (scruts ! c) of
          Some v \<Rightarrow> matches v (ps ! c) | None \<Rightarrow> False)
         \<longleftrightarrow> matches (CV_Record vflds) (CorePat_Record row_flds)"
      using col_eq assms(3,4) by simp
    show ?thesis
      using src_split new_split col_match_iff src_matches_col
      unfolding expand_record_scruts_def new_row_eq r_eq
      by (simp add: col_eq)
  qed
qed


section \<open>Matrix-level lifts\<close>

(* Bundle the per-row preconditions needed by the row-survival lemmas. *)
definition rows_well_shaped ::
  "nat \<Rightarrow> CoreTerm list \<Rightarrow> 'body Row list \<Rightarrow> bool"
where
  "rows_well_shaped c scruts rows \<longleftrightarrow>
     c < length scruts
   \<and> list_all (\<lambda>r. length (fst r) = length scruts) rows"

lemma rows_well_shaped_Cons:
  "rows_well_shaped c scruts (r # rs)
     \<longleftrightarrow> c < length scruts \<and> length (fst r) = length scruts
       \<and> rows_well_shaped c scruts rs"
  by (auto simp: rows_well_shaped_def)

(* Lift for default_row: when v_c does not match any of the source col-c
   non-wildcard heads at the matrix level (so the source side's first
   match is necessarily on a wildcard-col-c row), the source matrix and
   the default-filtered matrix agree.

   The hypothesis "no non-wildcard col-c pattern matches v_c" is exactly
   what's true when the algorithm descends into the default arm. *)
lemma matrix_first_match_default:
  fixes rows :: "'body Row list"
  assumes "rows_well_shaped c scruts rows"
  assumes "eval_match_scrut \<rho> (scruts ! c) = Some v_c"
  assumes "list_all (\<lambda>r. \<not> is_wildcard_like (fst r ! c)
                          \<longrightarrow> \<not> matches v_c (fst r ! c)) rows"
  shows "matrix_first_match \<rho>
            (drop_at c scruts, List.map_filter (default_row c) rows)
         = matrix_first_match \<rho> (scruts, rows)"
  using assms
proof (induction rows)
  case Nil show ?case by (simp add: List.map_filter_simps)
next
  case (Cons r rs)
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  from Cons.prems(1) have rs_shape: "rows_well_shaped c scruts rs"
    and r_len: "length ps = length scruts" and c_lt: "c < length scruts"
    by (auto simp: rows_well_shaped_Cons r_eq)
  from Cons.prems(3) have r_head:
    "\<not> is_wildcard_like (ps ! c) \<longrightarrow> \<not> matches v_c (ps ! c)"
    and rs_head:
    "list_all (\<lambda>r. \<not> is_wildcard_like (fst r ! c)
                    \<longrightarrow> \<not> matches v_c (fst r ! c)) rs"
    by (auto simp: r_eq)
  from Cons.IH[OF rs_shape Cons.prems(2) rs_head]
  have ih: "matrix_first_match \<rho>
              (drop_at c scruts, List.map_filter (default_row c) rs)
            = matrix_first_match \<rho> (scruts, rs)" .
  show ?case
  proof (cases "ps ! c")
    case CorePat_Wildcard
    let ?r' = "(drop_at c ps, body)"
    have df_some: "default_row c r = Some ?r'"
      by (simp add: r_eq CorePat_Wildcard)
    from default_row_row_matches[OF df_some, of scruts \<rho> v_c]
         r_len c_lt Cons.prems(2)
    have row_eq: "row_matches \<rho> scruts ps
                    \<longleftrightarrow> row_matches \<rho> (drop_at c scruts) (fst ?r')"
      by (simp add: r_eq)
    show ?thesis
      using df_some row_eq ih
      by (simp add: r_eq List.map_filter_simps)
  next
    case (CorePat_Bool b)
    hence non_wc: "\<not> is_wildcard_like (ps ! c)" by simp
    from r_head non_wc have no_match: "\<not> matches v_c (ps ! c)" by simp
    have df_none: "default_row c r = None"
      by (simp add: r_eq CorePat_Bool)
    \<comment> \<open>Source row doesn't match (its col-c pattern fails on v_c).\<close>
    have src_split:
      "row_matches \<rho> scruts ps
         \<longleftrightarrow> (case eval_match_scrut \<rho> (scruts ! c) of
                Some v \<Rightarrow> matches v (ps ! c)
              | None \<Rightarrow> False)
           \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
      using r_len c_lt by (intro row_matches_drop_at_split) auto
    have src_no_match: "\<not> row_matches \<rho> scruts ps"
      using src_split Cons.prems(2) no_match by simp
    show ?thesis
      using df_none src_no_match ih
      by (simp add: r_eq List.map_filter_simps)
  next
    case (CorePat_Int i)
    hence non_wc: "\<not> is_wildcard_like (ps ! c)" by simp
    from r_head non_wc have no_match: "\<not> matches v_c (ps ! c)" by simp
    have df_none: "default_row c r = None"
      by (simp add: r_eq CorePat_Int)
    have src_split:
      "row_matches \<rho> scruts ps
         \<longleftrightarrow> (case eval_match_scrut \<rho> (scruts ! c) of
                Some v \<Rightarrow> matches v (ps ! c)
              | None \<Rightarrow> False)
           \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
      using r_len c_lt by (intro row_matches_drop_at_split) auto
    have src_no_match: "\<not> row_matches \<rho> scruts ps"
      using src_split Cons.prems(2) no_match by simp
    show ?thesis
      using df_none src_no_match ih
      by (simp add: r_eq List.map_filter_simps)
  next
    case (CorePat_Variant h' pl)
    hence non_wc: "\<not> is_wildcard_like (ps ! c)" by simp
    from r_head non_wc have no_match: "\<not> matches v_c (ps ! c)" by simp
    have df_none: "default_row c r = None"
      by (simp add: r_eq CorePat_Variant)
    have src_split:
      "row_matches \<rho> scruts ps
         \<longleftrightarrow> (case eval_match_scrut \<rho> (scruts ! c) of
                Some v \<Rightarrow> matches v (ps ! c)
              | None \<Rightarrow> False)
           \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
      using r_len c_lt by (intro row_matches_drop_at_split) auto
    have src_no_match: "\<not> row_matches \<rho> scruts ps"
      using src_split Cons.prems(2) no_match by simp
    show ?thesis
      using df_none src_no_match ih
      by (simp add: r_eq List.map_filter_simps)
  next
    case (CorePat_Record flds)
    hence non_wc: "\<not> is_wildcard_like (ps ! c)" by simp
    from r_head non_wc have no_match: "\<not> matches v_c (ps ! c)" by simp
    have df_none: "default_row c r = None"
      by (simp add: r_eq CorePat_Record)
    have src_split:
      "row_matches \<rho> scruts ps
         \<longleftrightarrow> (case eval_match_scrut \<rho> (scruts ! c) of
                Some v \<Rightarrow> matches v (ps ! c)
              | None \<Rightarrow> False)
           \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
      using r_len c_lt by (intro row_matches_drop_at_split) auto
    have src_no_match: "\<not> row_matches \<rho> scruts ps"
      using src_split Cons.prems(2) no_match by simp
    show ?thesis
      using df_none src_no_match ih
      by (simp add: r_eq List.map_filter_simps)
  qed
qed


(* Lift for specialise_row_bool: when v_c = CV_Bool h, source and
   bool-specialised matrices agree. *)
lemma matrix_first_match_specialise_bool:
  fixes rows :: "'body Row list"
  assumes "rows_well_shaped c scruts rows"
  assumes "eval_match_scrut \<rho> (scruts ! c) = Some (CV_Bool h)"
  assumes "list_all (\<lambda>r. head_kind_of (fst r ! c) = Some HK_Bool
                          \<or> fst r ! c = CorePat_Wildcard) rows"
  shows "matrix_first_match \<rho>
            (drop_at c scruts, List.map_filter (specialise_row_bool c h) rows)
         = matrix_first_match \<rho> (scruts, rows)"
  using assms
proof (induction rows)
  case Nil show ?case by (simp add: List.map_filter_simps)
next
  case (Cons r rs)
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  from Cons.prems(1) have rs_shape: "rows_well_shaped c scruts rs"
    and r_len: "length ps = length scruts" and c_lt: "c < length scruts"
    by (auto simp: rows_well_shaped_Cons r_eq)
  from Cons.prems(3) have r_head:
    "head_kind_of (ps ! c) = Some HK_Bool \<or> ps ! c = CorePat_Wildcard"
    and rs_head:
    "list_all (\<lambda>r. head_kind_of (fst r ! c) = Some HK_Bool
                    \<or> fst r ! c = CorePat_Wildcard) rs"
    by (auto simp: r_eq)
  from Cons.IH[OF rs_shape Cons.prems(2) rs_head]
  have ih: "matrix_first_match \<rho>
              (drop_at c scruts, List.map_filter (specialise_row_bool c h) rs)
            = matrix_first_match \<rho> (scruts, rs)" .
  show ?case
  proof (cases "specialise_row_bool c h r")
    case None
    have len_fst_r: "length (fst r) = length scruts" using r_len r_eq by simp
    have c_lt_r: "c < length (fst r)" using c_lt r_len r_eq by simp
    have r_head_r: "head_kind_of (fst r ! c) = Some HK_Bool \<or> fst r ! c = CorePat_Wildcard"
      using r_head r_eq by simp
    from specialise_row_bool_row_no_match[OF None _ _ Cons.prems(2) r_head_r]
         len_fst_r c_lt_r
    have src_no_match: "\<not> row_matches \<rho> scruts (fst r)" by simp
    show ?thesis
      using None src_no_match ih
      by (simp add: r_eq List.map_filter_simps)
  next
    case (Some r')
    have len_fst_r: "length (fst r) = length scruts" using r_len r_eq by simp
    have c_lt_r: "c < length (fst r)" using c_lt r_len r_eq by simp
    from specialise_row_bool_row_matches[OF Some _ _ Cons.prems(2)]
         len_fst_r c_lt_r
    have row_eq: "row_matches \<rho> scruts (fst r)
                    \<longleftrightarrow> row_matches \<rho> (drop_at c scruts) (fst r')" by simp
    have body_eq: "snd r' = snd r"
      by (rule specialise_row_bool_body[OF Some])
    show ?thesis
      using Some row_eq ih body_eq
      by (cases r'; simp add: r_eq List.map_filter_simps)
  qed
qed


(* Lift for specialise_row_int: same shape as bool. *)
lemma matrix_first_match_specialise_int:
  fixes rows :: "'body Row list"
  assumes "rows_well_shaped c scruts rows"
  assumes "eval_match_scrut \<rho> (scruts ! c) = Some (CV_FiniteInt sign bits h)"
  assumes "list_all (\<lambda>r. head_kind_of (fst r ! c) = Some HK_Int
                          \<or> fst r ! c = CorePat_Wildcard) rows"
  shows "matrix_first_match \<rho>
            (drop_at c scruts, List.map_filter (specialise_row_int c h) rows)
         = matrix_first_match \<rho> (scruts, rows)"
  using assms
proof (induction rows)
  case Nil show ?case by (simp add: List.map_filter_simps)
next
  case (Cons r rs)
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  from Cons.prems(1) have rs_shape: "rows_well_shaped c scruts rs"
    and r_len: "length ps = length scruts" and c_lt: "c < length scruts"
    by (auto simp: rows_well_shaped_Cons r_eq)
  from Cons.prems(3) have r_head:
    "head_kind_of (ps ! c) = Some HK_Int \<or> ps ! c = CorePat_Wildcard"
    and rs_head:
    "list_all (\<lambda>r. head_kind_of (fst r ! c) = Some HK_Int
                    \<or> fst r ! c = CorePat_Wildcard) rs"
    by (auto simp: r_eq)
  from Cons.IH[OF rs_shape Cons.prems(2) rs_head]
  have ih: "matrix_first_match \<rho>
              (drop_at c scruts, List.map_filter (specialise_row_int c h) rs)
            = matrix_first_match \<rho> (scruts, rs)" .
  show ?case
  proof (cases "specialise_row_int c h r")
    case None
    have len_fst_r: "length (fst r) = length scruts" using r_len r_eq by simp
    have c_lt_r: "c < length (fst r)" using c_lt r_len r_eq by simp
    have r_head_r: "head_kind_of (fst r ! c) = Some HK_Int \<or> fst r ! c = CorePat_Wildcard"
      using r_head r_eq by simp
    from specialise_row_int_row_no_match[OF None _ _ Cons.prems(2) r_head_r]
         len_fst_r c_lt_r
    have src_no_match: "\<not> row_matches \<rho> scruts (fst r)" by simp
    show ?thesis
      using None src_no_match ih
      by (simp add: r_eq List.map_filter_simps)
  next
    case (Some r')
    have len_fst_r: "length (fst r) = length scruts" using r_len r_eq by simp
    have c_lt_r: "c < length (fst r)" using c_lt r_len r_eq by simp
    from specialise_row_int_row_matches[OF Some _ _ Cons.prems(2)]
         len_fst_r c_lt_r
    have row_eq: "row_matches \<rho> scruts (fst r)
                    \<longleftrightarrow> row_matches \<rho> (drop_at c scruts) (fst r')" by simp
    have body_eq: "snd r' = snd r"
      by (rule specialise_row_int_body[OF Some])
    show ?thesis
      using Some row_eq ih body_eq
      by (cases r'; simp add: r_eq List.map_filter_simps)
  qed
qed


(* Lift for specialise_row_variant: when v_c = CV_Variant h v_pl, source
   and variant-specialised matrices agree. New scruts list: col c is
   replaced by CoreTm_VariantProj s_c h. *)
lemma matrix_first_match_specialise_variant:
  fixes rows :: "'body Row list"
  assumes "rows_well_shaped c scruts rows"
  assumes "scruts ! c = s_c"
  assumes "eval_match_scrut \<rho> s_c = Some (CV_Variant h v_pl)"
  assumes "list_all (\<lambda>r. head_kind_of (fst r ! c) = Some HK_Variant
                          \<or> fst r ! c = CorePat_Wildcard) rows"
  shows "matrix_first_match \<rho>
            (replace_at c (CoreTm_VariantProj s_c h) scruts,
             List.map_filter (specialise_row_variant c h) rows)
         = matrix_first_match \<rho> (scruts, rows)"
  using assms
proof (induction rows)
  case Nil show ?case by (simp add: List.map_filter_simps)
next
  case (Cons r rs)
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  from Cons.prems(1) have rs_shape: "rows_well_shaped c scruts rs"
    and r_len: "length ps = length scruts" and c_lt: "c < length scruts"
    by (auto simp: rows_well_shaped_Cons r_eq)
  from Cons.prems(4) have r_head:
    "head_kind_of (ps ! c) = Some HK_Variant \<or> ps ! c = CorePat_Wildcard"
    and rs_head:
    "list_all (\<lambda>r. head_kind_of (fst r ! c) = Some HK_Variant
                    \<or> fst r ! c = CorePat_Wildcard) rs"
    by (auto simp: r_eq)
  have s_c_eval: "eval_match_scrut \<rho> (scruts ! c) = Some (CV_Variant h v_pl)"
    using Cons.prems(2,3) by simp
  from Cons.IH[OF rs_shape Cons.prems(2,3) rs_head]
  have ih: "matrix_first_match \<rho>
              (replace_at c (CoreTm_VariantProj s_c h) scruts,
               List.map_filter (specialise_row_variant c h) rs)
            = matrix_first_match \<rho> (scruts, rs)" .
  show ?case
  proof (cases "specialise_row_variant c h r")
    case None
    have len_fst_r: "length (fst r) = length scruts" using r_len r_eq by simp
    have c_lt_r: "c < length (fst r)" using c_lt r_len r_eq by simp
    have r_head_r: "head_kind_of (fst r ! c) = Some HK_Variant \<or> fst r ! c = CorePat_Wildcard"
      using r_head r_eq by simp
    from specialise_row_variant_row_no_match[OF None _ _ s_c_eval r_head_r]
         len_fst_r c_lt_r
    have src_no_match: "\<not> row_matches \<rho> scruts (fst r)" by simp
    show ?thesis
      using None src_no_match ih
      by (simp add: r_eq List.map_filter_simps)
  next
    case (Some r')
    have len_fst_r: "length (fst r) = length scruts" using r_len r_eq by simp
    have c_lt_r: "c < length (fst r)" using c_lt r_len r_eq by simp
    from specialise_row_variant_row_matches[OF Some _ _ Cons.prems(2,3)]
         len_fst_r c_lt_r
    have row_eq: "row_matches \<rho> scruts (fst r)
                    \<longleftrightarrow> row_matches \<rho> (replace_at c (CoreTm_VariantProj s_c h) scruts) (fst r')"
      by simp
    have body_eq: "snd r' = snd r"
      by (rule specialise_row_variant_body[OF Some])
    show ?thesis
      using Some row_eq ih body_eq
      by (cases r'; simp add: r_eq List.map_filter_simps)
  qed
qed


(* Lift for expand_record_row: lossless — always Some. Use plain List.map
   instead of List.map_filter. *)
lemma matrix_first_match_expand_record:
  fixes rows :: "'body Row list"
  assumes "rows_well_shaped c scruts rows"
  assumes "scruts ! c = s_c"
  assumes "eval_match_scrut \<rho> s_c = Some (CV_Record vflds)"
  assumes "distinct (map fst vflds)"
  assumes "map fst vflds = fld_names"
  assumes "list_all (\<lambda>r. head_kind_of (fst r ! c) = Some (HK_Record fld_names)
                          \<or> fst r ! c = CorePat_Wildcard) rows"
  shows "matrix_first_match \<rho>
            (expand_record_scruts c s_c fld_names scruts,
             map (expand_record_row c fld_names) rows)
         = matrix_first_match \<rho> (scruts, rows)"
  using assms
proof (induction rows)
  case Nil show ?case by simp
next
  case (Cons r rs)
  obtain ps body where r_eq: "r = (ps, body)" by (cases r) auto
  from Cons.prems(1) have rs_shape: "rows_well_shaped c scruts rs"
    and r_len: "length ps = length scruts" and c_lt: "c < length scruts"
    by (auto simp: rows_well_shaped_Cons r_eq)
  from Cons.prems(6) have r_head:
    "head_kind_of (ps ! c) = Some (HK_Record fld_names)
       \<or> ps ! c = CorePat_Wildcard"
    and rs_head:
    "list_all (\<lambda>r. head_kind_of (fst r ! c) = Some (HK_Record fld_names)
                    \<or> fst r ! c = CorePat_Wildcard) rs"
    by (auto simp: r_eq)
  from Cons.IH[OF rs_shape Cons.prems(2,3,4,5) rs_head]
  have ih: "matrix_first_match \<rho>
              (expand_record_scruts c s_c fld_names scruts,
               map (expand_record_row c fld_names) rs)
            = matrix_first_match \<rho> (scruts, rs)" .
  have len_fst_r: "length scruts = length (fst r)" using r_len r_eq by simp
  have c_lt_r: "c < length (fst r)" using c_lt r_len r_eq by simp
  have r_head_r: "head_kind_of (fst r ! c) = Some (HK_Record fld_names)
                    \<or> fst r ! c = CorePat_Wildcard"
    using r_head r_eq by simp
  from expand_record_row_row_matches[OF len_fst_r c_lt_r Cons.prems(2,3,4,5) r_head_r]
  have row_eq: "row_matches \<rho> scruts (fst r)
                  \<longleftrightarrow> row_matches \<rho>
                        (expand_record_scruts c s_c fld_names scruts)
                        (fst (expand_record_row c fld_names r))"
    by simp
  have body_eq: "snd (expand_record_row c fld_names r) = snd r"
    by (rule expand_record_row_body)
  show ?case
    using row_eq ih body_eq
    by (cases "expand_record_row c fld_names r"; simp add: r_eq)
qed


section \<open>Layer 3: scruts_consistent preservation\<close>

lemma scruts_consistent_drop_at:
  assumes "scruts_consistent \<rho> env scruts colTys"
  shows "scruts_consistent \<rho> env (drop_at c scruts) (drop_at c colTys)"
  using assms
  unfolding scruts_consistent_def
  by (rule list_all2_drop_at)

(* Variant: new col-c scrutinee is CoreTm_VariantProj s_c h. When v_c is
   CV_Variant h v_pl and matches the column's datatype type, the
   variant-projection scrutinee evaluates to v_pl, and v_pl has the
   instantiated payload type. *)
lemma scruts_consistent_specialise_variant:
  assumes sc: "scruts_consistent \<rho> env scruts colTys"
  assumes c_lt: "c < length colTys"
  assumes col_c: "colTys ! c = CoreTy_Datatype dtName tyArgs"
  assumes lookup: "fmlookup (TE_DataCtors env) h = Some (dtName, tyvars, payloadTy)"
  assumes len_ty: "length tyArgs = length tyvars"
  assumes v_c: "eval_match_scrut \<rho> (scruts ! c) = Some (CV_Variant h v_pl)"
  defines "payloadTy' \<equiv> apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy"
  shows "scruts_consistent \<rho> env
           (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts)
           (replace_at c payloadTy' colTys)"
proof -
  from sc have list_all2:
    "list_all2 (\<lambda>s ty. \<exists>v. eval_match_scrut \<rho> s = Some v
                       \<and> value_has_type env v ty) scruts colTys"
    unfolding scruts_consistent_def .
  from list_all2_lengthD[OF list_all2] have len: "length scruts = length colTys" .
  from c_lt len have c_lt_s: "c < length scruts" by simp
  from list_all2_nthD[OF list_all2 c_lt_s] obtain v where
    v_eval: "eval_match_scrut \<rho> (scruts ! c) = Some v" and
    v_ty: "value_has_type env v (colTys ! c)"
    by auto
  from v_eval v_c have v_eq: "v = CV_Variant h v_pl" by simp
  from v_ty col_c v_eq have vt_variant:
    "value_has_type env (CV_Variant h v_pl) (CoreTy_Datatype dtName tyArgs)"
    by simp
  from vt_variant lookup len_ty have payload_ty:
    "value_has_type env v_pl payloadTy'"
    unfolding payloadTy'_def by simp
  have new_proj_eval:
    "eval_match_scrut \<rho> (CoreTm_VariantProj (scruts ! c) h) = Some v_pl"
    using v_c by simp
  have new_at_c:
    "\<exists>v. eval_match_scrut \<rho> (CoreTm_VariantProj (scruts ! c) h) = Some v
       \<and> value_has_type env v payloadTy'"
    using new_proj_eval payload_ty by blast
  show ?thesis
    unfolding scruts_consistent_def
    using list_all2_replace_at_both[OF list_all2, of "[CoreTm_VariantProj (scruts ! c) h]" "[payloadTy']"]
          new_at_c c_lt_s
    by (intro list_all2_replace_at_sym[OF list_all2]) auto
qed

(* Record: each new field-projection scrutinee evaluates to the
   corresponding field value, and the value's type is the field type. *)
lemma scruts_consistent_expand_record:
  assumes sc: "scruts_consistent \<rho> env scruts colTys"
  assumes c_lt: "c < length colTys"
  assumes col_c: "colTys ! c = CoreTy_Record fldTys"
  assumes fld_names: "fld_names = map fst fldTys"
  assumes v_c: "eval_match_scrut \<rho> (scruts ! c) = Some (CV_Record vflds)"
  shows "scruts_consistent \<rho> env
           (expand_record_scruts c (scruts ! c) fld_names scruts)
           (splice_at c (map snd fldTys) colTys)"
proof -
  from sc have list_all2:
    "list_all2 (\<lambda>s ty. \<exists>v. eval_match_scrut \<rho> s = Some v
                       \<and> value_has_type env v ty) scruts colTys"
    unfolding scruts_consistent_def .
  from list_all2_lengthD[OF list_all2] have len: "length scruts = length colTys" .
  from c_lt len have c_lt_s: "c < length scruts" by simp
  from list_all2_nthD[OF list_all2 c_lt_s] obtain v where
    v_eval: "eval_match_scrut \<rho> (scruts ! c) = Some v" and
    v_ty: "value_has_type env v (colTys ! c)"
    by auto
  from v_eval v_c have v_eq: "v = CV_Record vflds" by simp
  from v_ty col_c v_eq have vt_record:
    "value_has_type env (CV_Record vflds) (CoreTy_Record fldTys)"
    by simp
  hence distinct_fld: "distinct (map fst fldTys)"
    and fields_typed: "list_all2
       (\<lambda>(name1, fldVal) (name2, fldTy).
          name1 = name2 \<and> value_has_type env fldVal fldTy)
       vflds fldTys"
    by simp_all
  have names_eq: "map fst vflds = map fst fldTys"
    using fields_typed by (induction vflds fldTys rule: list_all2_induct) auto
  have len_vf: "length vflds = length fldTys"
    using fields_typed by (rule list_all2_lengthD)
  have distinct_vf: "distinct (map fst vflds)"
    using names_eq distinct_fld by simp
  \<comment> \<open>Each new sub-scrut evaluates to the i-th field value, with field type.\<close>
  have new_sc_pc:
    "list_all2 (\<lambda>s ty. \<exists>v. eval_match_scrut \<rho> s = Some v
                       \<and> value_has_type env v ty)
       (map (\<lambda>f. CoreTm_RecordProj (scruts ! c) f) fld_names)
       (map snd fldTys)"
  proof (rule list_all2_all_nthI)
    show "length (map (\<lambda>f. CoreTm_RecordProj (scruts ! c) f) fld_names)
            = length (map snd fldTys)"
      using fld_names by simp
  next
    fix i assume i_lt: "i < length (map (\<lambda>f. CoreTm_RecordProj (scruts ! c) f) fld_names)"
    hence i_lt': "i < length fldTys" using fld_names by simp
    let ?f = "fld_names ! i"
    have proj_i: "(map (\<lambda>f. CoreTm_RecordProj (scruts ! c) f) fld_names) ! i
                    = CoreTm_RecordProj (scruts ! c) ?f"
      using i_lt' fld_names by simp
    have ty_i: "map snd fldTys ! i = snd (fldTys ! i)"
      using i_lt' by simp
    have f_eq: "?f = fst (fldTys ! i)"
      using fld_names i_lt' by simp
    \<comment> \<open>The i-th vflds entry has fst = ?f and value of type snd (fldTys ! i).\<close>
    have v_i_name: "fst (vflds ! i) = fst (fldTys ! i)"
      using fields_typed i_lt' len_vf
      by (auto simp: list_all2_conv_all_nth case_prod_unfold)
    have v_i_ty: "value_has_type env (snd (vflds ! i)) (snd (fldTys ! i))"
      using fields_typed i_lt' len_vf
      by (auto simp: list_all2_conv_all_nth case_prod_unfold)
    have v_i_in: "(fst (vflds ! i), snd (vflds ! i)) \<in> set vflds"
      using i_lt' len_vf by (metis nth_mem prod.collapse)
    have map_of_v: "map_of vflds (fst (vflds ! i)) = Some (snd (vflds ! i))"
      using distinct_vf v_i_in by (rule map_of_is_SomeI)
    have proj_eval: "eval_match_scrut \<rho> (CoreTm_RecordProj (scruts ! c) ?f) = Some (snd (vflds ! i))"
      using v_c map_of_v f_eq v_i_name by simp
    show "\<exists>v. eval_match_scrut \<rho>
                ((map (\<lambda>f. CoreTm_RecordProj (scruts ! c) f) fld_names) ! i) = Some v
              \<and> value_has_type env v (map snd fldTys ! i)"
      unfolding proj_i ty_i
      using proj_eval v_i_ty by blast
  qed
  show ?thesis
    unfolding scruts_consistent_def expand_record_scruts_def
    using list_all2_replace_at_both[OF list_all2 new_sc_pc] len fld_names
    by simp
qed


section \<open>arms_find on the compiled-arm shapes\<close>

(* The compiled arms for a head_kind have the shape
   "map (\<lambda>h. (P h, f h)) heads @ default_arm". These lemmas describe
   how arms_find walks them when the runtime value matches one of the
   enumerated heads, doesn't match any of them but matches the default,
   or matches none of them at all. *)

lemma arms_find_append_no_head_match:
  assumes "list_all (\<lambda>(p, _). \<not> matches v p) arms1"
  shows "arms_find v (arms1 @ arms2) = arms_find v arms2"
  using assms
  by (induction arms1) (auto split: if_splits)

lemma arms_find_default_arm:
  "arms_find v [(CorePat_Wildcard, t)] = Some t"
  by simp

lemma arms_find_bool_heads_hit:
  assumes "b \<in> set heads"
  shows "arms_find (CV_Bool b)
           (map (\<lambda>h. (CorePat_Bool h, f h)) heads @ rest)
         = Some (f b)"
  using assms by (induction heads) auto

lemma arms_find_bool_heads_miss:
  assumes "b \<notin> set heads"
  shows "arms_find (CV_Bool b)
           (map (\<lambda>h. (CorePat_Bool h, f h)) heads @ rest)
         = arms_find (CV_Bool b) rest"
  using assms
  by (induction heads) (auto)

lemma arms_find_int_heads_hit:
  assumes "i \<in> set heads"
  shows "arms_find (CV_FiniteInt sign bits i)
           (map (\<lambda>h. (CorePat_Int h, f h)) heads @ rest)
         = Some (f i)"
  using assms by (induction heads) auto

lemma arms_find_int_heads_miss:
  assumes "i \<notin> set heads"
  shows "arms_find (CV_FiniteInt sign bits i)
           (map (\<lambda>h. (CorePat_Int h, f h)) heads @ rest)
         = arms_find (CV_FiniteInt sign bits i) rest"
  using assms
  by (induction heads) (auto)

lemma arms_find_variant_heads_hit:
  assumes "h \<in> set heads"
  shows "arms_find (CV_Variant h v)
           (map (\<lambda>h'. (CorePat_Variant h' CorePat_Wildcard, f h')) heads @ rest)
         = Some (f h)"
  using assms by (induction heads) auto

lemma arms_find_variant_heads_miss:
  assumes "h \<notin> set heads"
  shows "arms_find (CV_Variant h v)
           (map (\<lambda>h'. (CorePat_Variant h' CorePat_Wildcard, f h')) heads @ rest)
         = arms_find (CV_Variant h v) rest"
  using assms by (induction heads) auto


section \<open>Helper lemmas about distinct_*_heads\<close>

lemma distinct_bool_heads_complete:
  "set (distinct_bool_heads col_pats)
     = {b. CorePat_Bool b \<in> set col_pats}"
  by (induction col_pats rule: distinct_bool_heads.induct) auto

lemma distinct_int_heads_complete:
  "set (distinct_int_heads col_pats)
     = {i. CorePat_Int i \<in> set col_pats}"
  by (induction col_pats rule: distinct_int_heads.induct) auto

lemma distinct_variant_heads_complete:
  "set (distinct_variant_heads col_pats)
     = {h. \<exists>p. CorePat_Variant h p \<in> set col_pats}"
proof (induction col_pats rule: distinct_variant_heads.induct)
  case 1 show ?case by simp
next
  case (2 h p rest)
  thus ?case by auto
qed auto


section \<open>Headline theorem\<close>

(* Theorem compile_matrix_semantics: the tree interpreter on the
   compiled tree agrees with the reference semantics on the source
   matrix.

   Proof by compile_matrix.induct, five cases. *)
theorem compile_matrix_semantics:
  fixes m :: "'body MatchMatrix"
  assumes "matrix_inv env g colTys m"
  assumes "snd m \<noteq> []"
  assumes "tyenv_well_formed env"
  assumes "scruts_consistent \<rho> env (fst m) colTys"
  shows   "match_tree_eval \<rho> (compile_matrix m) = matrix_first_match \<rho> m"
  using assms
proof (induction m arbitrary: colTys rule: compile_matrix.induct)
  case (1 scruts rows)
  from "1.prems"(2) have rows_ne: "rows \<noteq> []" by simp
  note inv = "1.prems"(1)
  note wf = "1.prems"(3)
  note sc_cons = "1.prems"(4)
  from inv have len_scruts: "length scruts = length colTys"
    unfolding matrix_inv_def by simp
  from inv have rows_inv:
    "list_all (\<lambda>(ps, _).
       length ps = length colTys
     \<and> list_all2 (pattern_compatible env) ps colTys) rows"
    unfolding matrix_inv_def by simp
  have rows_shape: "list_all (\<lambda>r. length (fst r) = length scruts) rows"
    using rows_inv len_scruts
    by (auto simp: list_all_iff case_prod_unfold)
  show ?case
  proof (cases "first_non_wildcard_col (map fst rows)")
    case None
    \<comment> \<open>Row 0 has all-wildcard patterns. compile_matrix returns MT_Leaf body0.
        matrix_first_match also returns Some body0 because every scrut
        evaluates (scruts_consistent) and wildcards match anything.\<close>
    with rows_ne obtain r0 rs where rows_eq: "rows = r0 # rs" by (cases rows) auto
    obtain ps0 body0 where r0_eq: "r0 = (ps0, body0)" by (cases r0) auto
    from None rows_eq r0_eq
    have compile_eq: "compile_matrix (scruts, rows) = MT_Leaf body0" by simp
    \<comment> \<open>Show row 0 matches by all_wildcards_match.
        From matrix_inv all rows have length = length colTys = length ps0,
        so the list_all-length condition in first_non_wildcard_col holds.
        Then None can only come from find returning None. \<close>
    have len_ps0: "length ps0 = length colTys"
      using rows_inv rows_eq r0_eq
      by (auto simp: list_all_iff case_prod_unfold)
    have lengths_eq: "list_all (\<lambda>r. length r = length ps0) (map fst rows)"
      using rows_inv len_ps0
      by (auto simp: list_all_iff case_prod_unfold)
    from None rows_eq r0_eq lengths_eq
    have find_none: "find (\<lambda>c'. \<not> is_wildcard_like (ps0 ! c')) [0 ..< length ps0] = None"
      by (auto simp: first_non_wildcard_col_def)
    from find_none have all_wc_idx: "\<forall>i < length ps0. is_wildcard_like (ps0 ! i)"
      by (simp add: find_None_iff)
    have all_wc: "list_all (\<lambda>p. p = CorePat_Wildcard) ps0"
      using all_wc_idx
      by (auto simp: list_all_iff in_set_conv_nth) (metis is_wildcard_like.elims(2))
    have len_ps0_s: "length ps0 = length scruts"
      using len_ps0 len_scruts by simp
    have scruts_eval: "list_all2 (\<lambda>s p. \<exists>v. eval_match_scrut \<rho> s = Some v) scruts ps0"
      using sc_cons len_ps0_s len_scruts
      unfolding scruts_consistent_def
      by (auto simp: list_all2_conv_all_nth)
    have row0_matches: "row_matches \<rho> scruts ps0"
      using all_wildcards_match[OF scruts_eval all_wc] .
    from compile_eq rows_eq r0_eq row0_matches show ?thesis by simp
  next
    case (Some c)
    let ?col_pats = "map (\<lambda>(ps, _). ps ! c) rows"
    let ?nw_col_pats = "filter (\<lambda>p. \<not> is_wildcard_like p) ?col_pats"
    obtain r0 rs where rows_eq: "rows = r0 # rs" using rows_ne by (cases rows) auto
    obtain ps0 body0 where r0_eq: "r0 = (ps0, body0)" by (cases r0) auto
    from Some rows_ne have head_nw: "\<not> is_wildcard_like (fst (hd rows) ! c)"
      using first_non_wildcard_col_head_weight_pos
            is_wildcard_like_iff_weight_zero by auto
    from rows_eq r0_eq head_nw have head_nw': "\<not> is_wildcard_like (ps0 ! c)" by simp
    hence nw_col_eq:
      "?nw_col_pats = (ps0 ! c) # filter (\<lambda>p. \<not> is_wildcard_like p)
                                         (map (\<lambda>(ps, _). ps ! c) rs)"
      using rows_eq r0_eq by (simp add: case_prod_unfold)
    from inv have c_lt: "c < length colTys"
      using Some
      unfolding matrix_inv_def first_non_wildcard_col_def
      using rows_eq r0_eq
      by (auto split: list.splits if_splits dest!: find_Some_iff[THEN iffD1])
    from c_lt len_scruts have c_lt_s: "c < length scruts" by simp
    from inv have sc_pc:
      "list_all2 (\<lambda>s ty. core_term_type env g s = Some ty) scruts colTys"
      unfolding matrix_inv_def by simp
    \<comment> \<open>Get v_c from scruts_consistent at c.\<close>
    from sc_cons have sc_la:
      "list_all2 (\<lambda>s ty. \<exists>v. eval_match_scrut \<rho> s = Some v
                       \<and> value_has_type env v ty) scruts colTys"
      unfolding scruts_consistent_def by simp
    from list_all2_nthD[OF sc_la c_lt_s]
    obtain v_c where
      v_c_eval: "eval_match_scrut \<rho> (scruts ! c) = Some v_c" and
      v_c_ty: "value_has_type env v_c (colTys ! c)"
      by auto

    show ?thesis
    proof (cases "head_kind_of (hd ?nw_col_pats)")
      case None
      from nw_col_eq have "hd ?nw_col_pats = ps0 ! c" by simp
      with None head_nw' head_kind_of_non_wildcard show ?thesis by (metis not_Some_eq)
    next
      case (Some hk)
      have col_some: "first_non_wildcard_col (map fst rows) = Some c"
        using \<open>first_non_wildcard_col (map fst rows) = Some c\<close> .
      from Some have head_kind_some: "head_kind_of (hd ?nw_col_pats) = Some hk" .

      \<comment> \<open>Row-head shape: every row's col-c pattern has matching head_kind or is wildcard. \<close>
      from \<open>rows = r0 # rs\<close> \<open>r0 = (ps0, body0)\<close>
      have ps0_at_c_kind: "head_kind_of (ps0 ! c) = Some hk"
        using nw_col_eq head_kind_some by simp

      show ?thesis
      proof (cases hk)
        case HK_Bool
        \<comment> \<open>Column is bool-typed; v_c is CV_Bool b for some b.\<close>
        from col_type_bool[OF rows_inv _ c_lt]
        have col_c_bool_when:
          "\<And>h. h \<in> set (distinct_bool_heads ?col_pats) \<Longrightarrow> colTys ! c = CoreTy_Bool"
          by blast
        \<comment> \<open>The first non-wildcard col-c pattern is bool; ps0!c has kind HK_Bool,
            so ps0!c = CorePat_Bool b0 for some b0. b0 is in distinct_bool_heads. \<close>
        obtain b0 where ps0_c_bool: "ps0 ! c = CorePat_Bool b0"
          using ps0_at_c_kind HK_Bool by (cases "ps0 ! c") auto
        have col_pats_eq: "?col_pats = (ps0 ! c) # map (\<lambda>(ps, _). ps ! c) rs"
          using rows_eq r0_eq by (simp add: case_prod_unfold)
        have b0_in: "b0 \<in> set (distinct_bool_heads ?col_pats)"
          unfolding col_pats_eq ps0_c_bool by simp
        have col_c_bool: "colTys ! c = CoreTy_Bool" using col_c_bool_when[OF b0_in] .
        from v_c_ty col_c_bool obtain b where v_c_eq: "v_c = CV_Bool b"
          by (cases v_c) auto
        have eval_at_c: "eval_match_scrut \<rho> (scruts ! c) = Some (CV_Bool b)"
          using v_c_eval v_c_eq by simp
        \<comment> \<open>Every col-c pattern is HK_Bool or wildcard.\<close>
        have row_heads_bool:
          "list_all (\<lambda>r. head_kind_of (fst r ! c) = Some HK_Bool
                          \<or> fst r ! c = CorePat_Wildcard) rows"
          unfolding list_all_iff
        proof
          fix r assume r_in: "r \<in> set rows"
          obtain ps b where r_split: "r = (ps, b)" by (cases r) auto
          show "head_kind_of (fst r ! c) = Some HK_Bool \<or> fst r ! c = CorePat_Wildcard"
          proof (cases "is_wildcard_like (ps ! c)")
            case True with r_split show ?thesis by (cases "ps ! c") auto
          next
            case False
            from rows_inv r_in r_split have
              row_pc: "list_all2 (pattern_compatible env) ps colTys"
              by (auto simp: list_all_iff case_prod_unfold)
            from list_all2_nth[OF row_pc] c_lt
            have ps_c_pc: "pattern_compatible env (ps ! c) (colTys ! c)"
              by (simp add: list_all2_nthD2 row_pc)
            from ps_c_pc col_c_bool have pc_bool: "pattern_compatible env (ps ! c) CoreTy_Bool" by simp
            from pc_bool False have "head_kind_of (ps ! c) = Some HK_Bool"
              by (cases "ps ! c") (auto split: option.splits prod.splits CoreType.splits)
            with r_split show ?thesis by simp
          qed
        qed

        have shape: "rows_well_shaped c scruts rows"
          using rows_shape c_lt_s by (simp add: rows_well_shaped_def)

        \<comment> \<open>Define the unfolded compile_matrix expression.\<close>
        have unfolded:
          "compile_matrix (scruts, rows) =
             MT_Test (scruts ! c)
               (map (\<lambda>h. (CorePat_Bool h,
                          compile_matrix (drop_at c scruts,
                            List.map_filter (specialise_row_bool c h) rows)))
                    (distinct_bool_heads ?col_pats)
                @ (if list_ex is_wildcard_like ?col_pats
                   then [(CorePat_Wildcard,
                          compile_matrix (drop_at c scruts,
                            List.map_filter (default_row c) rows))]
                   else []))"
          using col_some head_kind_some HK_Bool
          by (simp add: case_prod_unfold)
        \<comment> \<open>IH for each head and for the default arm.\<close>
        have IH_head:
          "\<And>h. h \<in> set (distinct_bool_heads ?col_pats) \<Longrightarrow>
             match_tree_eval \<rho>
               (compile_matrix (drop_at c scruts,
                                List.map_filter (specialise_row_bool c h) rows))
             = matrix_first_match \<rho>
                 (drop_at c scruts, List.map_filter (specialise_row_bool c h) rows)"
        proof -
          fix h assume h_in: "h \<in> set (distinct_bool_heads ?col_pats)"
          from matrix_inv_specialise_bool[OF inv c_lt, of h]
          have inv': "matrix_inv env g (drop_at c colTys)
                       (drop_at c scruts, List.map_filter (specialise_row_bool c h) rows)" .
          have ne': "snd (drop_at c scruts, List.map_filter (specialise_row_bool c h) rows) \<noteq> []"
            using specialise_bool_rows_nonempty[OF h_in] by simp
          have sc': "scruts_consistent \<rho> env
                       (fst (drop_at c scruts, List.map_filter (specialise_row_bool c h) rows))
                       (drop_at c colTys)"
            using scruts_consistent_drop_at[OF sc_cons] by simp
          from "1.IH"(4)[OF col_some _ _ _ _ _ head_kind_some HK_Bool _ inv' ne' wf sc']
          show "match_tree_eval \<rho>
                  (compile_matrix (drop_at c scruts,
                                   List.map_filter (specialise_row_bool c h) rows))
                = matrix_first_match \<rho>
                    (drop_at c scruts, List.map_filter (specialise_row_bool c h) rows)"
            by auto
        qed
        have IH_default:
          "list_ex is_wildcard_like ?col_pats \<Longrightarrow>
             match_tree_eval \<rho>
               (compile_matrix (drop_at c scruts, List.map_filter (default_row c) rows))
             = matrix_first_match \<rho>
                 (drop_at c scruts, List.map_filter (default_row c) rows)"
        proof -
          assume has_default: "list_ex is_wildcard_like ?col_pats"
          from matrix_inv_default[OF inv c_lt]
          have inv': "matrix_inv env g (drop_at c colTys)
                       (drop_at c scruts, List.map_filter (default_row c) rows)" .
          have ne': "snd (drop_at c scruts, List.map_filter (default_row c) rows) \<noteq> []"
            using default_rows_nonempty[OF col_some has_default] by simp
          have sc': "scruts_consistent \<rho> env
                       (fst (drop_at c scruts, List.map_filter (default_row c) rows))
                       (drop_at c colTys)"
            using scruts_consistent_drop_at[OF sc_cons] by simp
          from "1.IH"(1)[OF col_some _ _ _ _ has_default inv' ne' wf sc']
          show "match_tree_eval \<rho>
                  (compile_matrix (drop_at c scruts, List.map_filter (default_row c) rows))
                = matrix_first_match \<rho>
                    (drop_at c scruts, List.map_filter (default_row c) rows)"
            by auto
        qed

        \<comment> \<open>Case split on whether b is among the enumerated heads.\<close>
        let ?head_arms = "map (\<lambda>h. (CorePat_Bool h,
                                    compile_matrix (drop_at c scruts,
                                      List.map_filter (specialise_row_bool c h) rows)))
                              (distinct_bool_heads ?col_pats)"
        let ?default_arm = "if list_ex is_wildcard_like ?col_pats
                            then [(CorePat_Wildcard,
                                   compile_matrix (drop_at c scruts,
                                     List.map_filter (default_row c) rows))]
                            else []"

        show ?thesis
        proof (cases "b \<in> set (distinct_bool_heads ?col_pats)")
          case True
          \<comment> \<open>v_c matches one of the enumerated heads; arms_find hits that arm.\<close>
          let ?sub_tree = "compile_matrix (drop_at c scruts,
                            List.map_filter (specialise_row_bool c b) rows)"
          have af: "arms_find (CV_Bool b) (?head_arms @ ?default_arm) = Some ?sub_tree"
            using arms_find_bool_heads_hit[OF True] by metis
          have tree_eval:
            "match_tree_eval \<rho> (compile_matrix (scruts, rows)) = match_tree_eval \<rho> ?sub_tree"
            unfolding unfolded
            using eval_at_c af by simp
          have lift: "matrix_first_match \<rho>
                        (drop_at c scruts, List.map_filter (specialise_row_bool c b) rows)
                      = matrix_first_match \<rho> (scruts, rows)"
            using matrix_first_match_specialise_bool[OF shape eval_at_c row_heads_bool] .
          show ?thesis
            using tree_eval IH_head[OF True] lift by simp
        next
          case False
          \<comment> \<open>v_c is not in any head; arms_find walks past head arms to default arm or returns None.\<close>
          have af_miss: "arms_find (CV_Bool b) ?head_arms = None"
            using arms_find_bool_heads_miss[OF False, where f = "\<lambda>h. compile_matrix (drop_at c scruts, List.map_filter (specialise_row_bool c h) rows)" and rest = "[]"]
            by simp
          have head_arms_no_match:
            "list_all (\<lambda>(p, _). \<not> matches (CV_Bool b) p) ?head_arms"
          proof -
            have "\<forall>h \<in> set (distinct_bool_heads ?col_pats). h \<noteq> b"
              using False by blast
            thus ?thesis
              by (auto simp: list_all_iff)
          qed
          \<comment> \<open>No source-row col-c pattern matches v_c either (no row has CorePat_Bool b' with b' = b
              since b \<notin> heads; wildcard rows still match — they're handled via default arm).\<close>
          \<comment> \<open>For the source matrix_first_match to land on a row, that row's col-c must
              match v_c. Bool head rows with b'\<noteq>b don't match. Wildcard rows DO match col-c,
              and these are exactly the rows surviving default_row.\<close>
          show ?thesis
          proof (cases "list_ex is_wildcard_like ?col_pats")
            case has_default: True
            let ?sub_tree = "compile_matrix (drop_at c scruts,
                              List.map_filter (default_row c) rows)"
            have af: "arms_find (CV_Bool b) (?head_arms @ ?default_arm) = Some ?sub_tree"
              using arms_find_append_no_head_match[OF head_arms_no_match]
                    has_default by simp
            have tree_eval:
              "match_tree_eval \<rho> (compile_matrix (scruts, rows)) = match_tree_eval \<rho> ?sub_tree"
              unfolding unfolded
              using eval_at_c af by simp
            \<comment> \<open>Source side: no row with non-wildcard col-c matches v_c.\<close>
            have no_head_match_at_rows:
              "list_all (\<lambda>r. \<not> is_wildcard_like (fst r ! c)
                              \<longrightarrow> \<not> matches (CV_Bool b) (fst r ! c)) rows"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              then obtain r where r_in: "r \<in> set rows"
                              and not_wc: "\<not> is_wildcard_like (fst r ! c)"
                              and matches_b: "matches (CV_Bool b) (fst r ! c)"
                by (auto simp: list_all_iff)
              obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
              from row_heads_bool r_in not_wc r_split
              have "head_kind_of (ps ! c) = Some HK_Bool"
                by (auto simp: list_all_iff)
              then obtain b' where col_eq: "ps ! c = CorePat_Bool b'"
                by (cases "ps ! c") auto
              from matches_b col_eq r_split have b_eq: "b' = b" by simp
              from r_in r_split col_eq b_eq
              have "CorePat_Bool b \<in> set ?col_pats"
                by (force simp: case_prod_unfold)
              hence "b \<in> set (distinct_bool_heads ?col_pats)"
                using distinct_bool_heads_complete by blast
              with False show False by simp
            qed
            have lift: "matrix_first_match \<rho>
                          (drop_at c scruts, List.map_filter (default_row c) rows)
                        = matrix_first_match \<rho> (scruts, rows)"
              using matrix_first_match_default[OF shape eval_at_c no_head_match_at_rows] .
            show ?thesis
              using tree_eval IH_default[OF has_default] lift by simp
          next
            case no_default: False
            \<comment> \<open>No wildcard col-c in any row; no arm matches; tree returns None.
                Source side: every row has a non-wildcard col-c pattern that doesn't
                match v_c (since v_c is not in distinct_bool_heads and the col-c pattern
                must be CorePat_Bool b' for some b' \<noteq> b). So matrix_first_match = None.\<close>
            have af: "arms_find (CV_Bool b) (?head_arms @ ?default_arm) = None"
              using af_miss no_default by simp
            have tree_eval:
              "match_tree_eval \<rho> (compile_matrix (scruts, rows)) = None"
              unfolding unfolded
              using eval_at_c af by simp
            \<comment> \<open>Source side: every row has non-wildcard col-c (no_default), and none match v_c.\<close>
            have all_non_wc: "list_all (\<lambda>r. \<not> is_wildcard_like (fst r ! c)) rows"
              using no_default
              unfolding list_ex_iff
              by (auto simp: list_all_iff case_prod_unfold)
            have all_no_match: "list_all (\<lambda>r. \<not> matches (CV_Bool b) (fst r ! c)) rows"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              then obtain r where r_in: "r \<in> set rows"
                              and matches_b: "matches (CV_Bool b) (fst r ! c)"
                by (auto simp: list_all_iff)
              from all_non_wc r_in have not_wc: "\<not> is_wildcard_like (fst r ! c)"
                by (auto simp: list_all_iff)
              obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
              from row_heads_bool r_in r_split not_wc
              have "head_kind_of (ps ! c) = Some HK_Bool"
                by (auto simp: list_all_iff)
              then obtain b' where col_eq: "ps ! c = CorePat_Bool b'"
                by (cases "ps ! c") auto
              from matches_b col_eq r_split have b_eq: "b' = b" by simp
              from r_in r_split col_eq b_eq
              have "CorePat_Bool b \<in> set ?col_pats"
                by (force simp: case_prod_unfold)
              hence "b \<in> set (distinct_bool_heads ?col_pats)"
                using distinct_bool_heads_complete by blast
              with False show False by simp
            qed
            \<comment> \<open>Therefore source matrix_first_match = None.\<close>
            have src_none: "matrix_first_match \<rho> (scruts, rows) = None"
              using all_no_match rows_shape c_lt_s eval_at_c
            proof (induction rows)
              case Nil show ?case by simp
            next
              case (Cons r rs)
              obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
              from Cons.prems(1) r_split have
                no_match_r: "\<not> matches (CV_Bool b) (ps ! c)" and
                no_match_rs: "list_all (\<lambda>r. \<not> matches (CV_Bool b) (fst r ! c)) rs"
                by auto
              from Cons.prems(2) r_split have
                len_ps: "length ps = length scruts" and
                rs_shape: "list_all (\<lambda>r. length (fst r) = length scruts) rs"
                by auto
              have src_split:
                "row_matches \<rho> scruts ps
                   \<longleftrightarrow> (case eval_match_scrut \<rho> (scruts ! c) of
                          Some v \<Rightarrow> matches v (ps ! c)
                        | None \<Rightarrow> False)
                     \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
                using len_ps Cons.prems(3)
                by (intro row_matches_drop_at_split) auto
              from src_split Cons.prems(4) no_match_r
              have row0_no_match: "\<not> row_matches \<rho> scruts ps" by simp
              from Cons.IH[OF no_match_rs rs_shape Cons.prems(3) Cons.prems(4)]
              have ih: "matrix_first_match \<rho> (scruts, rs) = None" .
              from r_split row0_no_match ih show ?case by simp
            qed
            from tree_eval src_none show ?thesis by simp
          qed
        qed
      next
        case HK_Int
        \<comment> \<open>Column is integer-typed; v_c is CV_FiniteInt sign bits i for some i.\<close>
        from col_type_int[OF rows_inv _ c_lt]
        have col_c_int_when:
          "\<And>h. h \<in> set (distinct_int_heads ?col_pats) \<Longrightarrow> is_integer_type (colTys ! c)"
          by blast
        obtain i0 where ps0_c_int: "ps0 ! c = CorePat_Int i0"
          using ps0_at_c_kind HK_Int by (cases "ps0 ! c") auto
        have col_pats_eq: "?col_pats = (ps0 ! c) # map (\<lambda>(ps, _). ps ! c) rs"
          using rows_eq r0_eq by (simp add: case_prod_unfold)
        have i0_in: "i0 \<in> set (distinct_int_heads ?col_pats)"
          unfolding col_pats_eq ps0_c_int by simp
        have col_c_int: "is_integer_type (colTys ! c)" using col_c_int_when[OF i0_in] .
        from v_c_ty col_c_int obtain sign bits i where v_c_eq: "v_c = CV_FiniteInt sign bits i"
          by (cases v_c; cases "colTys ! c") auto
        have eval_at_c: "eval_match_scrut \<rho> (scruts ! c) = Some (CV_FiniteInt sign bits i)"
          using v_c_eval v_c_eq by simp
        have row_heads_int:
          "list_all (\<lambda>r. head_kind_of (fst r ! c) = Some HK_Int
                          \<or> fst r ! c = CorePat_Wildcard) rows"
          unfolding list_all_iff
        proof
          fix r assume r_in: "r \<in> set rows"
          obtain ps b where r_split: "r = (ps, b)" by (cases r) auto
          show "head_kind_of (fst r ! c) = Some HK_Int \<or> fst r ! c = CorePat_Wildcard"
          proof (cases "is_wildcard_like (ps ! c)")
            case True with r_split show ?thesis by (cases "ps ! c") auto
          next
            case False
            from rows_inv r_in r_split have
              row_pc: "list_all2 (pattern_compatible env) ps colTys"
              by (auto simp: list_all_iff case_prod_unfold)
            from list_all2_nth[OF row_pc] c_lt
            have ps_c_pc: "pattern_compatible env (ps ! c) (colTys ! c)"
              using list_all2_nthD2 row_pc by blast
            from ps_c_pc col_c_int have pc_int: "pattern_compatible env (ps ! c) (colTys ! c) \<and> is_integer_type (colTys ! c)" by simp
            from pc_int False have "head_kind_of (ps ! c) = Some HK_Int"
              by (cases "ps ! c") (auto split: option.splits prod.splits CoreType.splits)
            with r_split show ?thesis by simp
          qed
        qed
        have shape: "rows_well_shaped c scruts rows"
          using rows_shape c_lt_s by (simp add: rows_well_shaped_def)
        have unfolded:
          "compile_matrix (scruts, rows) =
             MT_Test (scruts ! c)
               (map (\<lambda>h. (CorePat_Int h,
                          compile_matrix (drop_at c scruts,
                            List.map_filter (specialise_row_int c h) rows)))
                    (distinct_int_heads ?col_pats)
                @ (if list_ex is_wildcard_like ?col_pats
                   then [(CorePat_Wildcard,
                          compile_matrix (drop_at c scruts,
                            List.map_filter (default_row c) rows))]
                   else []))"
          using col_some head_kind_some HK_Int
          by (simp add: case_prod_unfold)
        have IH_head:
          "\<And>h. h \<in> set (distinct_int_heads ?col_pats) \<Longrightarrow>
             match_tree_eval \<rho>
               (compile_matrix (drop_at c scruts,
                                List.map_filter (specialise_row_int c h) rows))
             = matrix_first_match \<rho>
                 (drop_at c scruts, List.map_filter (specialise_row_int c h) rows)"
        proof -
          fix h assume h_in: "h \<in> set (distinct_int_heads ?col_pats)"
          from matrix_inv_specialise_int[OF inv c_lt, of h]
          have inv': "matrix_inv env g (drop_at c colTys)
                       (drop_at c scruts, List.map_filter (specialise_row_int c h) rows)" .
          have ne': "snd (drop_at c scruts, List.map_filter (specialise_row_int c h) rows) \<noteq> []"
            using specialise_int_rows_nonempty[OF h_in] by simp
          have sc': "scruts_consistent \<rho> env
                       (fst (drop_at c scruts, List.map_filter (specialise_row_int c h) rows))
                       (drop_at c colTys)"
            using scruts_consistent_drop_at[OF sc_cons] by simp
          from "1.IH"(5)[OF col_some _ _ _ _ _ head_kind_some HK_Int _ inv' ne' wf sc']
          show "match_tree_eval \<rho>
                  (compile_matrix (drop_at c scruts,
                                   List.map_filter (specialise_row_int c h) rows))
                = matrix_first_match \<rho>
                    (drop_at c scruts, List.map_filter (specialise_row_int c h) rows)"
            by auto
        qed
        have IH_default:
          "list_ex is_wildcard_like ?col_pats \<Longrightarrow>
             match_tree_eval \<rho>
               (compile_matrix (drop_at c scruts, List.map_filter (default_row c) rows))
             = matrix_first_match \<rho>
                 (drop_at c scruts, List.map_filter (default_row c) rows)"
        proof -
          assume has_default: "list_ex is_wildcard_like ?col_pats"
          from matrix_inv_default[OF inv c_lt]
          have inv': "matrix_inv env g (drop_at c colTys)
                       (drop_at c scruts, List.map_filter (default_row c) rows)" .
          have ne': "snd (drop_at c scruts, List.map_filter (default_row c) rows) \<noteq> []"
            using default_rows_nonempty[OF col_some has_default] by simp
          have sc': "scruts_consistent \<rho> env
                       (fst (drop_at c scruts, List.map_filter (default_row c) rows))
                       (drop_at c colTys)"
            using scruts_consistent_drop_at[OF sc_cons] by simp
          from "1.IH"(1)[OF col_some _ _ _ _ has_default inv' ne' wf sc']
          show "match_tree_eval \<rho>
                  (compile_matrix (drop_at c scruts, List.map_filter (default_row c) rows))
                = matrix_first_match \<rho>
                    (drop_at c scruts, List.map_filter (default_row c) rows)"
            by auto
        qed
        let ?head_arms = "map (\<lambda>h. (CorePat_Int h,
                                    compile_matrix (drop_at c scruts,
                                      List.map_filter (specialise_row_int c h) rows)))
                              (distinct_int_heads ?col_pats)"
        let ?default_arm = "if list_ex is_wildcard_like ?col_pats
                            then [(CorePat_Wildcard,
                                   compile_matrix (drop_at c scruts,
                                     List.map_filter (default_row c) rows))]
                            else []"
        show ?thesis
        proof (cases "i \<in> set (distinct_int_heads ?col_pats)")
          case True
          let ?sub_tree = "compile_matrix (drop_at c scruts,
                            List.map_filter (specialise_row_int c i) rows)"
          have af: "arms_find (CV_FiniteInt sign bits i) (?head_arms @ ?default_arm) = Some ?sub_tree"
            using arms_find_int_heads_hit[OF True] by metis
          have tree_eval:
            "match_tree_eval \<rho> (compile_matrix (scruts, rows)) = match_tree_eval \<rho> ?sub_tree"
            unfolding unfolded
            using eval_at_c af by simp
          have lift: "matrix_first_match \<rho>
                        (drop_at c scruts, List.map_filter (specialise_row_int c i) rows)
                      = matrix_first_match \<rho> (scruts, rows)"
            using matrix_first_match_specialise_int[OF shape eval_at_c row_heads_int] .
          show ?thesis
            using tree_eval IH_head[OF True] lift by simp
        next
          case False
          have af_miss: "arms_find (CV_FiniteInt sign bits i) ?head_arms = None"
            using arms_find_int_heads_miss[OF False, where f = "\<lambda>h. compile_matrix (drop_at c scruts, List.map_filter (specialise_row_int c h) rows)" and rest = "[]"]
            by simp
          have head_arms_no_match:
            "list_all (\<lambda>(p, _). \<not> matches (CV_FiniteInt sign bits i) p) ?head_arms"
          proof -
            have "\<forall>h \<in> set (distinct_int_heads ?col_pats). h \<noteq> i"
              using False by auto
            thus ?thesis by (auto simp: list_all_iff)
          qed
          show ?thesis
          proof (cases "list_ex is_wildcard_like ?col_pats")
            case has_default: True
            let ?sub_tree = "compile_matrix (drop_at c scruts,
                              List.map_filter (default_row c) rows)"
            have af: "arms_find (CV_FiniteInt sign bits i) (?head_arms @ ?default_arm) = Some ?sub_tree"
              using arms_find_append_no_head_match[OF head_arms_no_match]
                    has_default by simp
            have tree_eval:
              "match_tree_eval \<rho> (compile_matrix (scruts, rows)) = match_tree_eval \<rho> ?sub_tree"
              unfolding unfolded
              using eval_at_c af by simp
            have no_head_match_at_rows:
              "list_all (\<lambda>r. \<not> is_wildcard_like (fst r ! c)
                              \<longrightarrow> \<not> matches (CV_FiniteInt sign bits i) (fst r ! c)) rows"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              then obtain r where r_in: "r \<in> set rows"
                              and not_wc: "\<not> is_wildcard_like (fst r ! c)"
                              and matches_i: "matches (CV_FiniteInt sign bits i) (fst r ! c)"
                by (auto simp: list_all_iff)
              obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
              from row_heads_int r_in not_wc r_split
              have "head_kind_of (ps ! c) = Some HK_Int"
                by (auto simp: list_all_iff)
              then obtain i' where col_eq: "ps ! c = CorePat_Int i'"
                by (cases "ps ! c") auto
              from matches_i col_eq r_split have i_eq: "i' = i" by simp
              from r_in r_split col_eq i_eq
              have "CorePat_Int i \<in> set ?col_pats"
                by (force simp: case_prod_unfold)
              hence "i \<in> set (distinct_int_heads ?col_pats)"
                using distinct_int_heads_complete by blast
              with False show False by simp
            qed
            have lift: "matrix_first_match \<rho>
                          (drop_at c scruts, List.map_filter (default_row c) rows)
                        = matrix_first_match \<rho> (scruts, rows)"
              using matrix_first_match_default[OF shape eval_at_c no_head_match_at_rows] .
            show ?thesis
              using tree_eval IH_default[OF has_default] lift by simp
          next
            case no_default: False
            have af: "arms_find (CV_FiniteInt sign bits i) (?head_arms @ ?default_arm) = None"
              using af_miss no_default by simp
            have tree_eval:
              "match_tree_eval \<rho> (compile_matrix (scruts, rows)) = None"
              unfolding unfolded
              using eval_at_c af by simp
            have all_non_wc: "list_all (\<lambda>r. \<not> is_wildcard_like (fst r ! c)) rows"
              using no_default
              unfolding list_ex_iff
              by (auto simp: list_all_iff case_prod_unfold)
            have all_no_match: "list_all (\<lambda>r. \<not> matches (CV_FiniteInt sign bits i) (fst r ! c)) rows"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              then obtain r where r_in: "r \<in> set rows"
                              and matches_i: "matches (CV_FiniteInt sign bits i) (fst r ! c)"
                by (auto simp: list_all_iff)
              from all_non_wc r_in have not_wc: "\<not> is_wildcard_like (fst r ! c)"
                by (auto simp: list_all_iff)
              obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
              from row_heads_int r_in r_split not_wc
              have "head_kind_of (ps ! c) = Some HK_Int"
                by (auto simp: list_all_iff)
              then obtain i' where col_eq: "ps ! c = CorePat_Int i'"
                by (cases "ps ! c") auto
              from matches_i col_eq r_split have i_eq: "i' = i" by simp
              from r_in r_split col_eq i_eq
              have "CorePat_Int i \<in> set ?col_pats"
                by (force simp: case_prod_unfold)
              hence "i \<in> set (distinct_int_heads ?col_pats)"
                using distinct_int_heads_complete by blast
              with False show False by simp
            qed
            have src_none: "matrix_first_match \<rho> (scruts, rows) = None"
              using all_no_match rows_shape c_lt_s eval_at_c
            proof (induction rows)
              case Nil show ?case by simp
            next
              case (Cons r rs)
              obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
              from Cons.prems(1) r_split have
                no_match_r: "\<not> matches (CV_FiniteInt sign bits i) (ps ! c)" and
                no_match_rs: "list_all (\<lambda>r. \<not> matches (CV_FiniteInt sign bits i) (fst r ! c)) rs"
                by auto
              from Cons.prems(2) r_split have
                len_ps: "length ps = length scruts" and
                rs_shape: "list_all (\<lambda>r. length (fst r) = length scruts) rs"
                by auto
              have src_split:
                "row_matches \<rho> scruts ps
                   \<longleftrightarrow> (case eval_match_scrut \<rho> (scruts ! c) of
                          Some v \<Rightarrow> matches v (ps ! c)
                        | None \<Rightarrow> False)
                     \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
                using len_ps Cons.prems(3)
                by (intro row_matches_drop_at_split) auto
              from src_split Cons.prems(4) no_match_r
              have row0_no_match: "\<not> row_matches \<rho> scruts ps" by simp
              from Cons.IH[OF no_match_rs rs_shape Cons.prems(3) Cons.prems(4)]
              have ih: "matrix_first_match \<rho> (scruts, rs) = None" .
              from r_split row0_no_match ih show ?case by simp
            qed
            from tree_eval src_none show ?thesis by simp
          qed
        qed
      next
        case HK_Variant
        \<comment> \<open>Column is variant-typed; v_c is CV_Variant h v_pl for some h, v_pl.\<close>
        obtain h0 pl0 where ps0_c_variant: "ps0 ! c = CorePat_Variant h0 pl0"
          using ps0_at_c_kind HK_Variant by (cases "ps0 ! c") auto
        have col_pats_eq: "?col_pats = (ps0 ! c) # map (\<lambda>(ps, _). ps ! c) rs"
          using rows_eq r0_eq by (simp add: case_prod_unfold)
        have h0_in: "h0 \<in> set (distinct_variant_heads ?col_pats)"
          unfolding col_pats_eq ps0_c_variant by simp
        from col_type_variant[OF rows_inv h0_in c_lt]
        obtain dtName tyArgs tyvars0 payloadTy0 where
          col_c_dt: "colTys ! c = CoreTy_Datatype dtName tyArgs" and
          lookup_h0: "fmlookup (TE_DataCtors env) h0 = Some (dtName, tyvars0, payloadTy0)" and
          len_ty0: "length tyArgs = length tyvars0"
          by metis
        from v_c_ty col_c_dt obtain h v_pl where v_c_eq: "v_c = CV_Variant h v_pl"
          by (cases v_c) auto
        have eval_at_c: "eval_match_scrut \<rho> (scruts ! c) = Some (CV_Variant h v_pl)"
          using v_c_eval v_c_eq by simp
        have row_heads_variant:
          "list_all (\<lambda>r. head_kind_of (fst r ! c) = Some HK_Variant
                          \<or> fst r ! c = CorePat_Wildcard) rows"
          unfolding list_all_iff
        proof
          fix r assume r_in: "r \<in> set rows"
          obtain ps b where r_split: "r = (ps, b)" by (cases r) auto
          show "head_kind_of (fst r ! c) = Some HK_Variant \<or> fst r ! c = CorePat_Wildcard"
          proof (cases "is_wildcard_like (ps ! c)")
            case True with r_split show ?thesis by (cases "ps ! c") auto
          next
            case False
            from rows_inv r_in r_split have
              row_pc: "list_all2 (pattern_compatible env) ps colTys"
              by (auto simp: list_all_iff case_prod_unfold)
            from list_all2_nth[OF row_pc] c_lt
            have ps_c_pc: "pattern_compatible env (ps ! c) (colTys ! c)"
              by (simp add: list_all2_nthD2 row_pc)
            from ps_c_pc col_c_dt have pc_dt: "pattern_compatible env (ps ! c) (CoreTy_Datatype dtName tyArgs)" by simp
            from pc_dt False have "head_kind_of (ps ! c) = Some HK_Variant"
              by (cases "ps ! c") (auto split: option.splits prod.splits CoreType.splits)
            with r_split show ?thesis by simp
          qed
        qed
        have shape: "rows_well_shaped c scruts rows"
          using rows_shape c_lt_s by (simp add: rows_well_shaped_def)
        have unfolded:
          "compile_matrix (scruts, rows) =
             MT_Test (scruts ! c)
               (map (\<lambda>h'. (CorePat_Variant h' CorePat_Wildcard,
                           compile_matrix
                             (replace_at c (CoreTm_VariantProj (scruts ! c) h') scruts,
                              List.map_filter (specialise_row_variant c h') rows)))
                    (distinct_variant_heads ?col_pats)
                @ (if list_ex is_wildcard_like ?col_pats
                   then [(CorePat_Wildcard,
                          compile_matrix (drop_at c scruts,
                            List.map_filter (default_row c) rows))]
                   else []))"
          using col_some head_kind_some HK_Variant
          by (simp add: case_prod_unfold Let_def)
        have IH_head_for_h:
          "h \<in> set (distinct_variant_heads ?col_pats) \<Longrightarrow>
             match_tree_eval \<rho>
               (compile_matrix
                 (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                  List.map_filter (specialise_row_variant c h) rows))
             = matrix_first_match \<rho>
                 (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                  List.map_filter (specialise_row_variant c h) rows)"
        proof -
          assume h_in: "h \<in> set (distinct_variant_heads ?col_pats)"
          from col_type_variant[OF rows_inv h_in c_lt]
          obtain dtName1 tyArgs1 tyvars1 payloadTy1 where
            col_c_dt1: "colTys ! c = CoreTy_Datatype dtName1 tyArgs1" and
            lookup_h1: "fmlookup (TE_DataCtors env) h = Some (dtName1, tyvars1, payloadTy1)" and
            len_ty1: "length tyArgs1 = length tyvars1"
            by metis
          from col_c_dt col_c_dt1 have dt_eq: "dtName1 = dtName" "tyArgs1 = tyArgs" by auto
          let ?payloadTy_sub = "apply_subst (fmap_of_list (zip tyvars1 tyArgs1)) payloadTy1"
          from matrix_inv_specialise_variant[OF inv c_lt col_c_dt1 lookup_h1 len_ty1 wf]
          have inv': "matrix_inv env g (replace_at c ?payloadTy_sub colTys)
                       (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                        List.map_filter (specialise_row_variant c h) rows)" .
          have ne': "snd (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                          List.map_filter (specialise_row_variant c h) rows) \<noteq> []"
            using specialise_variant_rows_nonempty[OF h_in] by simp
          have sc_cons': "scruts_consistent \<rho> env scruts colTys" using sc_cons by simp
          have sc': "scruts_consistent \<rho> env
                       (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts)
                       (replace_at c ?payloadTy_sub colTys)"
            using scruts_consistent_specialise_variant[OF sc_cons' c_lt col_c_dt1 lookup_h1 len_ty1 eval_at_c]
            by simp
          have ih:
            "match_tree_eval \<rho>
               (compile_matrix
                 (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                  List.map_filter (specialise_row_variant c h) rows))
             = matrix_first_match \<rho>
                 (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                  List.map_filter (specialise_row_variant c h) rows)"
            using "1.IH"(3)[where xaa = h, of c "scruts ! c" "map (\<lambda>(ps, _). ps ! c) rows"
                              "list_ex is_wildcard_like (map (\<lambda>(ps, _). ps ! c) rows)"
                              "List.map_filter (default_row c) rows" _
                              hk "distinct_variant_heads (map (\<lambda>(ps, _). ps ! c) rows)"
                              "replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts"
                              "replace_at c ?payloadTy_sub colTys"]
                  col_some head_kind_some HK_Variant inv' ne' wf sc'
            by simp
          show "match_tree_eval \<rho>
                  (compile_matrix
                    (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                     List.map_filter (specialise_row_variant c h) rows))
                = matrix_first_match \<rho>
                    (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                     List.map_filter (specialise_row_variant c h) rows)"
            using ih .
        qed
        have IH_default:
          "list_ex is_wildcard_like ?col_pats \<Longrightarrow>
             match_tree_eval \<rho>
               (compile_matrix (drop_at c scruts, List.map_filter (default_row c) rows))
             = matrix_first_match \<rho>
                 (drop_at c scruts, List.map_filter (default_row c) rows)"
        proof -
          assume has_default: "list_ex is_wildcard_like ?col_pats"
          from matrix_inv_default[OF inv c_lt]
          have inv': "matrix_inv env g (drop_at c colTys)
                       (drop_at c scruts, List.map_filter (default_row c) rows)" .
          have ne': "snd (drop_at c scruts, List.map_filter (default_row c) rows) \<noteq> []"
            using default_rows_nonempty[OF col_some has_default] by simp
          have sc': "scruts_consistent \<rho> env
                       (fst (drop_at c scruts, List.map_filter (default_row c) rows))
                       (drop_at c colTys)"
            using scruts_consistent_drop_at[OF sc_cons] by simp
          from "1.IH"(1)[OF col_some _ _ _ _ has_default inv' ne' wf sc']
          show "match_tree_eval \<rho>
                  (compile_matrix (drop_at c scruts, List.map_filter (default_row c) rows))
                = matrix_first_match \<rho>
                    (drop_at c scruts, List.map_filter (default_row c) rows)"
            by auto
        qed
        let ?head_arms = "map (\<lambda>h'. (CorePat_Variant h' CorePat_Wildcard,
                                     compile_matrix
                                       (replace_at c (CoreTm_VariantProj (scruts ! c) h') scruts,
                                        List.map_filter (specialise_row_variant c h') rows)))
                              (distinct_variant_heads ?col_pats)"
        let ?default_arm = "if list_ex is_wildcard_like ?col_pats
                            then [(CorePat_Wildcard,
                                   compile_matrix (drop_at c scruts,
                                     List.map_filter (default_row c) rows))]
                            else []"
        show ?thesis
        proof (cases "h \<in> set (distinct_variant_heads ?col_pats)")
          case True
          let ?sub_tree = "compile_matrix
                             (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                              List.map_filter (specialise_row_variant c h) rows)"
          have af: "arms_find (CV_Variant h v_pl) (?head_arms @ ?default_arm) = Some ?sub_tree"
            using arms_find_variant_heads_hit[OF True] by metis
          have tree_eval:
            "match_tree_eval \<rho> (compile_matrix (scruts, rows)) = match_tree_eval \<rho> ?sub_tree"
            unfolding unfolded
            using eval_at_c af by simp
          have lift: "matrix_first_match \<rho>
                        (replace_at c (CoreTm_VariantProj (scruts ! c) h) scruts,
                         List.map_filter (specialise_row_variant c h) rows)
                      = matrix_first_match \<rho> (scruts, rows)"
            using matrix_first_match_specialise_variant[OF shape refl eval_at_c row_heads_variant] .
          show ?thesis
            using tree_eval IH_head_for_h[OF True] lift by simp
        next
          case False
          have af_miss: "arms_find (CV_Variant h v_pl) ?head_arms = None"
            using arms_find_variant_heads_miss[OF False, where f = "\<lambda>h'. compile_matrix (replace_at c (CoreTm_VariantProj (scruts ! c) h') scruts, List.map_filter (specialise_row_variant c h') rows)" and rest = "[]"]
            by simp
          have head_arms_no_match:
            "list_all (\<lambda>(p, _). \<not> matches (CV_Variant h v_pl) p) ?head_arms"
          proof -
            have "\<forall>h' \<in> set (distinct_variant_heads ?col_pats). h' \<noteq> h"
              using False by auto
            thus ?thesis by (auto simp: list_all_iff)
          qed
          show ?thesis
          proof (cases "list_ex is_wildcard_like ?col_pats")
            case has_default: True
            let ?sub_tree = "compile_matrix (drop_at c scruts,
                              List.map_filter (default_row c) rows)"
            have af: "arms_find (CV_Variant h v_pl) (?head_arms @ ?default_arm) = Some ?sub_tree"
              using arms_find_append_no_head_match[OF head_arms_no_match]
                    has_default by simp
            have tree_eval:
              "match_tree_eval \<rho> (compile_matrix (scruts, rows)) = match_tree_eval \<rho> ?sub_tree"
              unfolding unfolded
              using eval_at_c af by simp
            have no_head_match_at_rows:
              "list_all (\<lambda>r. \<not> is_wildcard_like (fst r ! c)
                              \<longrightarrow> \<not> matches (CV_Variant h v_pl) (fst r ! c)) rows"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              then obtain r where r_in: "r \<in> set rows"
                              and not_wc: "\<not> is_wildcard_like (fst r ! c)"
                              and matches_h: "matches (CV_Variant h v_pl) (fst r ! c)"
                by (auto simp: list_all_iff)
              obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
              from row_heads_variant r_in not_wc r_split
              have "head_kind_of (ps ! c) = Some HK_Variant"
                by (auto simp: list_all_iff)
              then obtain h' pl' where col_eq: "ps ! c = CorePat_Variant h' pl'"
                by (cases "ps ! c") auto
              from matches_h col_eq r_split have h_eq: "h' = h" by simp
              from r_in r_split col_eq h_eq
              have "CorePat_Variant h pl' \<in> set ?col_pats"
                by (force simp: case_prod_unfold)
              hence "h \<in> set (distinct_variant_heads ?col_pats)"
                using distinct_variant_heads_complete by blast
              with False show False by simp
            qed
            have lift: "matrix_first_match \<rho>
                          (drop_at c scruts, List.map_filter (default_row c) rows)
                        = matrix_first_match \<rho> (scruts, rows)"
              using matrix_first_match_default[OF shape eval_at_c no_head_match_at_rows] .
            show ?thesis
              using tree_eval IH_default[OF has_default] lift by simp
          next
            case no_default: False
            have af: "arms_find (CV_Variant h v_pl) (?head_arms @ ?default_arm) = None"
              using af_miss no_default by simp
            have tree_eval:
              "match_tree_eval \<rho> (compile_matrix (scruts, rows)) = None"
              unfolding unfolded
              using eval_at_c af by simp
            have all_non_wc: "list_all (\<lambda>r. \<not> is_wildcard_like (fst r ! c)) rows"
              using no_default
              unfolding list_ex_iff
              by (auto simp: list_all_iff case_prod_unfold)
            have all_no_match: "list_all (\<lambda>r. \<not> matches (CV_Variant h v_pl) (fst r ! c)) rows"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              then obtain r where r_in: "r \<in> set rows"
                              and matches_h: "matches (CV_Variant h v_pl) (fst r ! c)"
                by (auto simp: list_all_iff)
              from all_non_wc r_in have not_wc: "\<not> is_wildcard_like (fst r ! c)"
                by (auto simp: list_all_iff)
              obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
              from row_heads_variant r_in r_split not_wc
              have "head_kind_of (ps ! c) = Some HK_Variant"
                by (auto simp: list_all_iff)
              then obtain h' pl' where col_eq: "ps ! c = CorePat_Variant h' pl'"
                by (cases "ps ! c") auto
              from matches_h col_eq r_split have h_eq: "h' = h" by simp
              from r_in r_split col_eq h_eq
              have "CorePat_Variant h pl' \<in> set ?col_pats"
                by (force simp: case_prod_unfold)
              hence "h \<in> set (distinct_variant_heads ?col_pats)"
                using distinct_variant_heads_complete by blast
              with False show False by simp
            qed
            have src_none: "matrix_first_match \<rho> (scruts, rows) = None"
              using all_no_match rows_shape c_lt_s eval_at_c
            proof (induction rows)
              case Nil show ?case by simp
            next
              case (Cons r rs)
              obtain ps body where r_split: "r = (ps, body)" by (cases r) auto
              from Cons.prems(1) r_split have
                no_match_r: "\<not> matches (CV_Variant h v_pl) (ps ! c)" and
                no_match_rs: "list_all (\<lambda>r. \<not> matches (CV_Variant h v_pl) (fst r ! c)) rs"
                by auto
              from Cons.prems(2) r_split have
                len_ps: "length ps = length scruts" and
                rs_shape: "list_all (\<lambda>r. length (fst r) = length scruts) rs"
                by auto
              have src_split:
                "row_matches \<rho> scruts ps
                   \<longleftrightarrow> (case eval_match_scrut \<rho> (scruts ! c) of
                          Some v \<Rightarrow> matches v (ps ! c)
                        | None \<Rightarrow> False)
                     \<and> row_matches \<rho> (drop_at c scruts) (drop_at c ps)"
                using len_ps Cons.prems(3)
                by (intro row_matches_drop_at_split) auto
              from src_split Cons.prems(4) no_match_r
              have row0_no_match: "\<not> row_matches \<rho> scruts ps" by simp
              from Cons.IH[OF no_match_rs rs_shape Cons.prems(3) Cons.prems(4)]
              have ih: "matrix_first_match \<rho> (scruts, rs) = None" .
              from r_split row0_no_match ih show ?case by simp
            qed
            from tree_eval src_none show ?thesis by simp
          qed
        qed
      next
        case (HK_Record fld_names)
        \<comment> \<open>Column is record-typed; v_c is CV_Record vflds with field names = fld_names.\<close>
        from head_kind_some HK_Record nw_col_eq
        have head_record: "head_kind_of (ps0 ! c) = Some (HK_Record fld_names)" by simp
        then obtain pflds where
          ps0_c_eq: "ps0 ! c = CorePat_Record pflds" and
          fld_names_eq: "fld_names = map fst pflds"
          by (cases "ps0 ! c") auto
        from rows_eq r0_eq have r0_in: "r0 \<in> set rows" by simp
        from rows_inv r0_in r0_eq have
          ps0_pcs: "list_all2 (pattern_compatible env) ps0 colTys"
          by (auto simp: list_all_iff)
        from list_all2_nth[OF ps0_pcs] c_lt
        have ps0_at_c_pc: "pattern_compatible env (ps0 ! c) (colTys ! c)"
          by (simp add: list_all2_nthD2 ps0_pcs)
        with ps0_c_eq have
          "pattern_compatible env (CorePat_Record pflds) (colTys ! c)" by simp
        from pattern_compatible_record_inv[OF this]
        obtain fldTys where
          col_c_rec: "colTys ! c = CoreTy_Record fldTys" and
          la2: "list_all2 (\<lambda>(pn, p) (fn, fty). pn = fn \<and> pattern_compatible env p fty)
                          pflds fldTys"
          by metis
        have names_eq: "map fst pflds = map fst fldTys"
          using la2 by (induction pflds fldTys rule: list_all2_induct) auto
        have fld_names_eq': "fld_names = map fst fldTys"
          using fld_names_eq names_eq by simp
        from v_c_ty col_c_rec obtain vflds where
          v_c_eq: "v_c = CV_Record vflds" and
          distinct_flds: "distinct (map fst fldTys)" and
          fields_typed: "list_all2 (\<lambda>(name1, fldVal) (name2, fldTy).
                                       name1 = name2 \<and> value_has_type env fldVal fldTy) vflds fldTys"
          by (cases v_c) auto
        have v_names_eq: "map fst vflds = map fst fldTys"
          using fields_typed by (induction vflds fldTys rule: list_all2_induct) auto
        have v_fld_names: "map fst vflds = fld_names"
          using v_names_eq fld_names_eq' by simp
        have distinct_vflds: "distinct (map fst vflds)"
          using v_names_eq distinct_flds by simp
        have eval_at_c: "eval_match_scrut \<rho> (scruts ! c) = Some (CV_Record vflds)"
          using v_c_eval v_c_eq by simp
        have row_heads_rec:
          "list_all (\<lambda>r. head_kind_of (fst r ! c) = Some (HK_Record fld_names)
                          \<or> fst r ! c = CorePat_Wildcard) rows"
          unfolding list_all_iff
        proof
          fix r assume r_in: "r \<in> set rows"
          obtain ps b where r_split: "r = (ps, b)" by (cases r) auto
          show "head_kind_of (fst r ! c) = Some (HK_Record fld_names) \<or> fst r ! c = CorePat_Wildcard"
          proof (cases "is_wildcard_like (ps ! c)")
            case True with r_split show ?thesis by (cases "ps ! c") auto
          next
            case False
            from rows_inv r_in r_split have
              row_pc: "list_all2 (pattern_compatible env) ps colTys"
              by (auto simp: list_all_iff case_prod_unfold)
            from list_all2_nth[OF row_pc] c_lt
            have ps_c_pc: "pattern_compatible env (ps ! c) (colTys ! c)"
              by (simp add: list_all2_nthD2 row_pc)
            from ps_c_pc col_c_rec have pc_rec: "pattern_compatible env (ps ! c) (CoreTy_Record fldTys)" by simp
            from pc_rec False obtain row_flds where
              col_eq: "ps ! c = CorePat_Record row_flds" and
              row_la2: "list_all2 (\<lambda>(pn, p) (fn, fty). pn = fn \<and> pattern_compatible env p fty)
                                  row_flds fldTys"
              by (cases "ps ! c") (auto split: option.splits prod.splits CoreType.splits)
            have row_names_eq: "map fst row_flds = map fst fldTys"
              using row_la2 by (induction row_flds fldTys rule: list_all2_induct) auto
            have row_names: "map fst row_flds = fld_names"
              using row_names_eq fld_names_eq' by simp
            from col_eq row_names have "head_kind_of (ps ! c) = Some (HK_Record fld_names)"
              by simp
            with r_split show ?thesis by simp
          qed
        qed
        have shape: "rows_well_shaped c scruts rows"
          using rows_shape c_lt_s by (simp add: rows_well_shaped_def)
        have unfolded:
          "compile_matrix (scruts, rows) =
             compile_matrix (expand_record_scruts c (scruts ! c) fld_names scruts,
                             map (expand_record_row c fld_names) rows)"
          using col_some head_kind_some HK_Record
          by (simp add: case_prod_unfold Let_def)
        from matrix_inv_expand_record[OF inv c_lt col_c_rec fld_names_eq' wf]
        have inv': "matrix_inv env g (splice_at c (map snd fldTys) colTys)
                     (expand_record_scruts c (scruts ! c) fld_names scruts,
                      map (expand_record_row c fld_names) rows)" .
        have ne': "snd (expand_record_scruts c (scruts ! c) fld_names scruts,
                        map (expand_record_row c fld_names) rows) \<noteq> []"
          using rows_ne by simp
        have sc_cons': "scruts_consistent \<rho> env scruts colTys" using sc_cons by simp
        have sc': "scruts_consistent \<rho> env
                     (fst (expand_record_scruts c (scruts ! c) fld_names scruts,
                           map (expand_record_row c fld_names) rows))
                     (splice_at c (map snd fldTys) colTys)"
          using scruts_consistent_expand_record[OF sc_cons' c_lt col_c_rec fld_names_eq' eval_at_c]
          by simp
        from "1.IH"(2)[OF col_some _ _ _ _ _ head_kind_some HK_Record inv' ne' wf sc']
        have ih: "match_tree_eval \<rho>
                    (compile_matrix (expand_record_scruts c (scruts ! c) fld_names scruts,
                                     map (expand_record_row c fld_names) rows))
                  = matrix_first_match \<rho>
                      (expand_record_scruts c (scruts ! c) fld_names scruts,
                       map (expand_record_row c fld_names) rows)"
          by auto
        have lift: "matrix_first_match \<rho>
                      (expand_record_scruts c (scruts ! c) fld_names scruts,
                       map (expand_record_row c fld_names) rows)
                    = matrix_first_match \<rho> (scruts, rows)"
          using matrix_first_match_expand_record[OF shape refl eval_at_c distinct_vflds v_fld_names row_heads_rec] .
        from unfolded ih lift show ?thesis by simp
      qed
    qed
  qed
qed


section \<open>Entry-point corollary\<close>

(* compile_match-level statement, mirroring the type-preservation
   layer's compile_match_arm_patterns_compatible. The reference
   semantics on the singleton-column matrix collapses to "walk the
   user-level (pattern, body) arms in order", which is the natural
   spec for a single match. *)

fun arms_first_match ::
  "CoreValue \<Rightarrow> (CorePattern \<times> 'body) list \<Rightarrow> 'body option"
where
  "arms_first_match _ [] = None"
| "arms_first_match v ((p, b) # rest) =
     (if matches v p then Some b else arms_first_match v rest)"

lemma matrix_first_match_singleton:
  "matrix_first_match \<rho> ([scrut], map (\<lambda>(p, b). ([p], b)) arms)
     = (case eval_match_scrut \<rho> scrut of
          None \<Rightarrow> None
        | Some v \<Rightarrow> arms_first_match v arms)"
proof (induction arms)
  case Nil show ?case
    by (metis arms_first_match.simps(1) list.map_disc_iff matrix_first_match.simps(1) not_Some_eq
        option.simps(4,5))
next
  case (Cons pb rest)
  obtain p b where pb_eq: "pb = (p, b)" by (cases pb) auto
  show ?case
  proof (cases "eval_match_scrut \<rho> scrut")
    case None
    with pb_eq show ?thesis
      by (simp add: local.Cons row_matches_singleton)
  next
    case (Some v)
    with pb_eq Cons.IH show ?thesis
      by (simp add: row_matches_def)
  qed
qed

theorem compile_match_semantics:
  fixes arms :: "(CorePattern \<times> 'body) list"
  assumes "core_term_type env g scrut = Some scrutTy"
  assumes "arms \<noteq> []"
  assumes "list_all (\<lambda>(p, _). pattern_compatible env p scrutTy) arms"
  assumes "tyenv_well_formed env"
  assumes "eval_match_scrut \<rho> scrut = Some v"
  assumes "value_has_type env v scrutTy"
  shows   "match_tree_eval \<rho> (compile_match scrut scrutTy arms)
             = arms_first_match v arms"
proof -
  let ?m = "([scrut], map (\<lambda>(p, b). ([p], b)) arms)"
  have inv: "matrix_inv env g [scrutTy] ?m"
    unfolding matrix_inv_def
    using assms(1,3) by (auto simp: list_all_iff)
  have ne: "snd ?m \<noteq> []" using assms(2) by simp
  have sc: "scruts_consistent \<rho> env (fst ?m) [scrutTy]"
    unfolding scruts_consistent_def
    using assms(5,6) by simp
  from compile_matrix_semantics[OF inv ne assms(4) sc]
  have "match_tree_eval \<rho> (compile_matrix ?m) = matrix_first_match \<rho> ?m" .
  also have "matrix_first_match \<rho> ?m
               = (case eval_match_scrut \<rho> scrut of
                    None \<Rightarrow> None
                  | Some v \<Rightarrow> arms_first_match v arms)"
    by (rule matrix_first_match_singleton)
  also have "\<dots> = arms_first_match v arms"
    using assms(5) by simp
  finally show ?thesis
    unfolding compile_match_def .
qed

end
