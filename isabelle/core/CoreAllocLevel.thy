theory CoreAllocLevel
  imports CoreTyEnv "HOL-Library.While_Combinator" "HOL-Library.Char_ord" "HOL-Library.List_Lexorder"
begin

(* ========================================================================== *)
(* The order on alloc levels                                                  *)
(* ========================================================================== *)

(* A CoreAllocLevel is a set of facts about `allocated(x)` that may be assumed for
   every value x of a type:
     - Never \<Rightarrow> "not allocated(x)" for all x;
     - IfNotDefault \<Rightarrow> "not allocated(default)";
     - Always \<Rightarrow> nothing may be assumed.

   The alloc levels are ordered: Never < IfNotDefault < Always, where lower levels
   in the order provide more facts.

   The alloc level of a realization of an abstract type must have an alloc level \<le>
   the level that the type was originally declared with (i.e. it must provide at
   least as many facts as were promised in the original declaration).
*)

(* Definition of the levels, as a numeric rank, and a "\<le>" function *)
fun alloc_level_rank :: "CoreAllocLevel \<Rightarrow> nat" where
  "alloc_level_rank CoreAlloc_Never = 0"
| "alloc_level_rank CoreAlloc_IfNotDefault = 1"
| "alloc_level_rank CoreAlloc_Always = 2"

definition alloc_level_le :: "CoreAllocLevel \<Rightarrow> CoreAllocLevel \<Rightarrow> bool" where
  "alloc_level_le l1 l2 = (alloc_level_rank l1 \<le> alloc_level_rank l2)"

(* Basic properties *)
lemma alloc_level_le_refl [simp]: "alloc_level_le l l"
  unfolding alloc_level_le_def by simp

lemma alloc_level_le_trans:
  "alloc_level_le l1 l2 \<Longrightarrow> alloc_level_le l2 l3 \<Longrightarrow> alloc_level_le l1 l3"
  unfolding alloc_level_le_def by simp

lemma alloc_level_le_antisym:
  "alloc_level_le l1 l2 \<Longrightarrow> alloc_level_le l2 l1 \<Longrightarrow> l1 = l2"
  unfolding alloc_level_le_def by (cases l1; cases l2) simp_all

lemma alloc_level_le_total:
  "alloc_level_le l1 l2 \<or> alloc_level_le l2 l1"
  unfolding alloc_level_le_def by auto

lemma alloc_level_le_Never [simp]: "alloc_level_le CoreAlloc_Never l"
  unfolding alloc_level_le_def by (cases l) simp_all

lemma alloc_level_le_Always [simp]: "alloc_level_le l CoreAlloc_Always"
  unfolding alloc_level_le_def by (cases l) simp_all

(* The larger of two levels (fewer facts). *)
definition alloc_level_max :: "CoreAllocLevel \<Rightarrow> CoreAllocLevel \<Rightarrow> CoreAllocLevel" where
  "alloc_level_max l1 l2 = (if alloc_level_le l1 l2 then l2 else l1)"

lemma alloc_level_max_le1: "alloc_level_le l1 (alloc_level_max l1 l2)"
  unfolding alloc_level_max_def using alloc_level_le_total[of l1 l2] by auto

lemma alloc_level_max_le2: "alloc_level_le l2 (alloc_level_max l1 l2)"
  unfolding alloc_level_max_def using alloc_level_le_total[of l1 l2] by auto

lemma alloc_level_max_least:
  "alloc_level_le l1 l \<Longrightarrow> alloc_level_le l2 l \<Longrightarrow> alloc_level_le (alloc_level_max l1 l2) l"
  unfolding alloc_level_max_def by auto

lemma alloc_level_max_Never [simp]:
  "alloc_level_max CoreAlloc_Never l = l"
  "alloc_level_max l CoreAlloc_Never = l"
  unfolding alloc_level_max_def alloc_level_le_def by (cases l; simp)+

(* The maximum of a list of levels (CoreAlloc_Never for the empty list). *)
definition alloc_level_max_list :: "CoreAllocLevel list \<Rightarrow> CoreAllocLevel" where
  "alloc_level_max_list ls = foldr alloc_level_max ls CoreAlloc_Never"

lemma alloc_level_max_list_Nil [simp]:
  "alloc_level_max_list [] = CoreAlloc_Never"
  unfolding alloc_level_max_list_def by simp

lemma alloc_level_max_list_Cons [simp]:
  "alloc_level_max_list (l # ls) = alloc_level_max l (alloc_level_max_list ls)"
  unfolding alloc_level_max_list_def by simp

lemma alloc_level_max_list_ge:
  "l \<in> set ls \<Longrightarrow> alloc_level_le l (alloc_level_max_list ls)"
proof (induction ls)
  case Nil then show ?case by simp
next
  case (Cons l' ls)
  show ?case
  proof (cases "l = l'")
    case True
    then show ?thesis using alloc_level_max_le1 by simp
  next
    case False
    with Cons.prems have "l \<in> set ls" by simp
    from Cons.IH[OF this] show ?thesis
      using alloc_level_le_trans alloc_level_max_le2 by fastforce
  qed
qed

lemma alloc_level_max_list_least:
  "(\<And>l. l \<in> set ls \<Longrightarrow> alloc_level_le l bound) \<Longrightarrow> alloc_level_le (alloc_level_max_list ls) bound"
  by (induction ls) (auto intro: alloc_level_max_least)

lemma alloc_level_max_mono:
  "alloc_level_le a1 a2 \<Longrightarrow> alloc_level_le b1 b2 \<Longrightarrow>
   alloc_level_le (alloc_level_max a1 b1) (alloc_level_max a2 b2)"
  by (cases a1; cases a2; cases b1; cases b2) (simp_all add: alloc_level_max_def alloc_level_le_def)

(* A datatype is only CoreAlloc_Always if the first payload is. If any other payload
   is CoreAlloc_Always, that only makes the datatype CoreAlloc_IfNotDefault, because
   the default value (the first constructor) doesn't carry that payload. *)
fun downgrade_nonfirst :: "CoreAllocLevel \<Rightarrow> CoreAllocLevel" where
  "downgrade_nonfirst CoreAlloc_Always = CoreAlloc_IfNotDefault"
| "downgrade_nonfirst l = l"

lemma downgrade_nonfirst_le: "alloc_level_le (downgrade_nonfirst l) l"
  by (cases l) (simp_all add: alloc_level_le_def)

lemma downgrade_nonfirst_mono:
  "alloc_level_le l1 l2 \<Longrightarrow> alloc_level_le (downgrade_nonfirst l1) (downgrade_nonfirst l2)"
  by (cases l1; cases l2) (simp_all add: alloc_level_le_def)


(* ========================================================================== *)
(* Alloc levels of Core types                                                 *)
(* ========================================================================== *)

(* The alloc level of a Core type can be computed structurally:
    - bool, finite int, int, real: CoreAlloc_Never;
    - record: max over the fields;
    - datatype: max over the payloads, except that non-first payloads are downgraded
        using `downgrade_nonfirst` (above);
    - allocatable array T[*]: CoreAlloc_IfNotDefault (regardless of element type);
    - fixed-sized array T[n]: the level of the element type;
    - type variable: the level from TE_AbstractAllocLevels if present (an abstract
        type), otherwise CoreAlloc_Always (a function-level type parameter, about
        whose values nothing is known);
    - extern type (CoreTy_Extern n l): the level l, carried by the type. *)

(* (Note that the language considers it a type error to ask `allocated(x)` if x's
   type contains an incomplete array type T[], so the level returned for such types
   is irrelevant. We return the level of the element type, which follows the convention
   used in the interpreter.) *)

(* The difficulty is that datatypes may have payloads that are other datatypes, so
   the above definition is recursive. Moreover, although the elaborator (currently)
   does not allow recursive datatypes, there is no constraint in core_tyenv_well_formed
   that rules them out. Therefore, the above recursion might not even terminate, at least
   for type envs created outside the elaborator. *)

(* We resolve this by computing a least fixpoint. The basic idea is to start from a state
   where each datatype is considered non-allocated, then recompute the allocated-status of all
   datatypes under that assumption. Iterating this procedure must eventually converge to a
   fixpoint (because each step only increases the alloc-levels, and there are a finite number
   of possible states), and that fixpoint is what is used for calculating the alloc-level of
   any given type. (This is a slight over-simplification; more details are given below.) *)

(* To compute the alloc level of a type, one can use alloc_level_of_type (below), which
   re-does the fixpoint iteration each time; or, more efficiently in executable code, one
   can precompute the fixpoint using datatype_alloc_info env, then use
   alloc_level_of_type_info. *)


(* ---- AllocModes ---- *)

(* A mode says how the level of a type argument contributes to the level of a
   datatype application.

   Mode_Never: the parameter doesn't contribute at all.
   Mode_Downgrade: the parameter's mode is downgraded (downgrade_first) before contributing.
   Mode_Always: the parameter's mode contributes as-is.

   For example, in datatype Foo<S,T,U> = Foo1(T) | Foo2(U):
    - S doesn't affect the alloc level at all (it isn't mentioned in any payload), so it
        has Mode_Never;
    - T appears in the first constructor, so it has Mode_Always (if T's alloc level is X,
        then Foo's alloc level must be at least X);
    - U appears in non-first position, so it has Mode_Downgrade (if U's alloc level is
        Alloc_Always, then Foo is still only at least Alloc_IfNotDefault, because U doesn't
        appear in Foo1, the default constructor).

   The modes are ordered: Never < Downgrade < Identity.
*)
datatype AllocMode = Mode_Never | Mode_Downgrade | Mode_Identity

fun mode_rank :: "AllocMode \<Rightarrow> nat" where
  "mode_rank Mode_Never = 0"
| "mode_rank Mode_Downgrade = 1"
| "mode_rank Mode_Identity = 2"

definition mode_le :: "AllocMode \<Rightarrow> AllocMode \<Rightarrow> bool" where
  "mode_le m1 m2 = (mode_rank m1 \<le> mode_rank m2)"

lemma mode_le_refl [simp]: "mode_le m m"
  unfolding mode_le_def by simp

lemma mode_le_trans: "mode_le m1 m2 \<Longrightarrow> mode_le m2 m3 \<Longrightarrow> mode_le m1 m3"
  unfolding mode_le_def by simp

lemma mode_le_Never [simp]: "mode_le Mode_Never m"
  unfolding mode_le_def by (cases m) simp_all

lemma mode_le_Identity [simp]: "mode_le m Mode_Identity"
  unfolding mode_le_def by (cases m) simp_all

fun apply_mode :: "AllocMode \<Rightarrow> CoreAllocLevel \<Rightarrow> CoreAllocLevel" where
  "apply_mode Mode_Never l = CoreAlloc_Never"
| "apply_mode Mode_Downgrade l = downgrade_nonfirst l"
| "apply_mode Mode_Identity l = l"

definition mode_max :: "AllocMode \<Rightarrow> AllocMode \<Rightarrow> AllocMode" where
  "mode_max m1 m2 = (if mode_le m1 m2 then m2 else m1)"

definition mode_min :: "AllocMode \<Rightarrow> AllocMode \<Rightarrow> AllocMode" where
  "mode_min m1 m2 = (if mode_le m1 m2 then m1 else m2)"

(* Composition of modes is min: Identity is neutral, Never absorbs, and
   downgrade_nonfirst is idempotent. *)
lemma apply_mode_mode_min:
  "apply_mode (mode_min m1 m2) l = apply_mode m1 (apply_mode m2 l)"
  by (cases m1; cases m2; cases l) (simp_all add: mode_min_def mode_le_def)

(* Every mode commutes with max (it is a monotone map on a chain). *)
lemma apply_mode_max:
  "apply_mode m (alloc_level_max l1 l2) = alloc_level_max (apply_mode m l1) (apply_mode m l2)"
  by (cases m; cases l1; cases l2) (simp_all add: alloc_level_max_def alloc_level_le_def)

lemma apply_mode_mono:
  "mode_le m1 m2 \<Longrightarrow> alloc_level_le l1 l2 \<Longrightarrow> alloc_level_le (apply_mode m1 l1) (apply_mode m2 l2)"
  by (cases m1; cases m2; cases l1; cases l2) (simp_all add: mode_le_def alloc_level_le_def)

lemma mode_max_mono:
  "mode_le a1 a2 \<Longrightarrow> mode_le b1 b2 \<Longrightarrow> mode_le (mode_max a1 b1) (mode_max a2 b2)"
  by (cases a1; cases a2; cases b1; cases b2) (simp_all add: mode_max_def mode_le_def)

lemma mode_min_mono:
  "mode_le a1 a2 \<Longrightarrow> mode_le b1 b2 \<Longrightarrow> mode_le (mode_min a1 b1) (mode_min a2 b2)"
  by (cases a1; cases a2; cases b1; cases b2) (simp_all add: mode_min_def mode_le_def)


(* ---- Summaries ---- *)

(* An AllocSummary tells us the alloc level of a datatype, given the alloc levels of each
   of its actual type arguments.

   The summary is encoded as a tuple of a "base" alloc level (representing the
   non-parameterised parts of the datatype) and a mode for each type argument. The alloc
   level of the datatype (applied to given type arguments) is then computed as the max
   of the base alloc level, and the alloc levels of the type arguments, the latter first
   being filtered through their respective modes (see `apply_mode`).

   For example, datatype Foo = Foo(i32[*]) would have summary (CoreAlloc_IfNotDefault, []),
   meaning that this datatype has alloc level IfNotDefault (and there are no type parameters).

   A datatype Bar<S,T,U> = Bar1(T) | Bar2(U) would have summary
   (CoreAlloc_Never, [Mode_Never, Mode_Identity, Mode_Downgrade], meaning that the alloc
   level of Bar<S,T,U> is the max of three things: CoreAlloc_Never (the base level), the
   level of T, and the downgraded level of U.

   An AllocSummary can also be calculated for any type, not just a datatype. For example,
   the AllocSummary of a record type is the max (using summary_max_list) of the summaries
   of all the record field types.
*)

type_synonym AllocSummary = "CoreAllocLevel \<times> AllocMode list"

(* The "constant" summary, representing an alloc level of l, regardless of the type
   arguments (n is the number of arguments). *)
definition summary_const :: "CoreAllocLevel \<Rightarrow> nat \<Rightarrow> AllocSummary" where
  "summary_const l n = (l, replicate n Mode_Never)"

(* The "top" summary: CoreAlloc_Always, regardless of the type arguments.
   This says that nothing at all is known about the datatype's alloc level. *)
definition summary_top :: "nat \<Rightarrow> AllocSummary" where
  "summary_top n = (CoreAlloc_Always, replicate n Mode_Identity)"

lemma summary_const_length [simp]: "length (snd (summary_const l n)) = n"
  by (simp add: summary_const_def)

lemma summary_top_length [simp]: "length (snd (summary_top n)) = n"
  by (simp add: summary_top_def)

(* Pointwise max of two summaries over the same parameters. *)
definition summary_max :: "AllocSummary \<Rightarrow> AllocSummary \<Rightarrow> AllocSummary" where
  "summary_max s1 s2 = (alloc_level_max (fst s1) (fst s2), map2 mode_max (snd s1) (snd s2))"

(* A mode applied to the result of a summary (apply_mode_max and
   apply_mode_mode_min justify the pointwise form). *)
definition summary_compose :: "AllocMode \<Rightarrow> AllocSummary \<Rightarrow> AllocSummary" where
  "summary_compose m s = (apply_mode m (fst s), map (mode_min m) (snd s))"

(* The pointwise order on summaries over the same parameters. *)
definition summary_le :: "AllocSummary \<Rightarrow> AllocSummary \<Rightarrow> bool" where
  "summary_le s1 s2 = (alloc_level_le (fst s1) (fst s2) \<and> list_all2 mode_le (snd s1) (snd s2))"

lemma summary_le_refl [simp]: "summary_le s s"
  unfolding summary_le_def by (simp add: list_all2_conv_all_nth)

lemma summary_le_trans:
  assumes "summary_le s1 s2" and "summary_le s2 s3"
  shows "summary_le s1 s3"
proof -
  have "alloc_level_le (fst s1) (fst s3)"
    using assms alloc_level_le_trans unfolding summary_le_def by blast
  moreover have "list_all2 mode_le (snd s1) (snd s3)"
    using assms unfolding summary_le_def list_all2_conv_all_nth
    by (metis mode_le_trans)
  ultimately show ?thesis unfolding summary_le_def by simp
qed

lemma summary_max_mono:
  assumes a: "summary_le a1 a2" and b: "summary_le b1 b2"
  shows "summary_le (summary_max a1 b1) (summary_max a2 b2)"
proof -
  have l: "alloc_level_le (alloc_level_max (fst a1) (fst b1)) (alloc_level_max (fst a2) (fst b2))"
    using a b alloc_level_max_mono unfolding summary_le_def by blast
  have "list_all2 mode_le (map2 mode_max (snd a1) (snd b1)) (map2 mode_max (snd a2) (snd b2))"
    using a b unfolding summary_le_def list_all2_conv_all_nth
    by (auto simp: mode_max_mono)
  with l show ?thesis unfolding summary_le_def summary_max_def by simp
qed

lemma summary_compose_mono:
  "mode_le m1 m2 \<Longrightarrow> summary_le s1 s2 \<Longrightarrow> summary_le (summary_compose m1 s1) (summary_compose m2 s2)"
  unfolding summary_le_def summary_compose_def list_all2_conv_all_nth
  by (auto simp: apply_mode_mono mode_min_mono)

lemma summary_compose_length [simp]:
  "length (snd (summary_compose m s)) = length (snd s)"
  by (simp add: summary_compose_def)

(* Max of a list of summaries over n parameters; the constant Never for the
   empty list. *)
definition summary_max_list :: "nat \<Rightarrow> AllocSummary list \<Rightarrow> AllocSummary" where
  "summary_max_list n ss = foldr summary_max ss (summary_const CoreAlloc_Never n)"

lemma summary_max_list_mono:
  assumes "list_all2 summary_le ss1 ss2"
  shows "summary_le (summary_max_list n ss1) (summary_max_list n ss2)"
  using assms unfolding summary_max_list_def
  by (induction ss1 ss2 rule: list_all2_induct) (auto intro: summary_max_mono)

(* Compute the summary of a datatype application, given the (parameterised) summary of
   the datatype itself, and the summaries of its type arguments.

   The result is itself parameterised over n parameters (the parameters of the type
   being summarised).

   The modes are zipped with the arguments; a mismatched arity (which never happens for
   well-kinded types) just drops the surplus on one side. *)
definition apply_summary ::
  "nat \<Rightarrow> AllocSummary \<Rightarrow> AllocSummary list \<Rightarrow> AllocSummary" where
  "apply_summary n entry argSums =
     summary_max_list n (summary_const (fst entry) n # map2 summary_compose (snd entry) argSums)"

lemma apply_summary_mono:
  assumes e: "summary_le e1 e2" and ss: "list_all2 summary_le ss1 ss2"
  shows "summary_le (apply_summary n e1 ss1) (apply_summary n e2 ss2)"
proof -
  from e have bl: "alloc_level_le (fst e1) (fst e2)" and ml: "list_all2 mode_le (snd e1) (snd e2)"
    by (simp_all add: summary_le_def)
  have len1: "length (snd e1) = length (snd e2)" using ml by (rule list_all2_lengthD)
  have len2: "length ss1 = length ss2" using ss by (rule list_all2_lengthD)
  have hd: "summary_le (summary_const (fst e1) n) (summary_const (fst e2) n)"
    using bl by (simp add: summary_le_def summary_const_def list_all2_conv_all_nth)
  have elem: "\<And>i. i < length (snd e1) \<Longrightarrow> i < length ss1 \<Longrightarrow>
                summary_le (summary_compose (snd e1 ! i) (ss1 ! i))
                           (summary_compose (snd e2 ! i) (ss2 ! i))"
  proof -
    fix i assume i1: "i < length (snd e1)" and i2: "i < length ss1"
    have "mode_le (snd e1 ! i) (snd e2 ! i)" using ml i1 by (simp add: list_all2_conv_all_nth)
    moreover have "summary_le (ss1 ! i) (ss2 ! i)" using ss i2 by (simp add: list_all2_conv_all_nth)
    ultimately show "summary_le (summary_compose (snd e1 ! i) (ss1 ! i))
                                (summary_compose (snd e2 ! i) (ss2 ! i))"
      by (rule summary_compose_mono)
  qed
  have tl: "list_all2 summary_le (map2 summary_compose (snd e1) ss1) (map2 summary_compose (snd e2) ss2)"
    using elem len1 len2 by (auto simp: list_all2_conv_all_nth)
  from hd tl show ?thesis unfolding apply_summary_def by (intro summary_max_list_mono) simp
qed


(* ---- The traversal: the summary of a type ---- *)

(* summarize env info params ty: the summary of ty relative to the type
   parameters params, reading the datatype summaries from info. A type
   variable that is one of the params contributes through its mode; any other
   type variable contributes its declared level if it is an abstract type, and
   CoreAlloc_Always if it has no entry (a function-level type parameter). *)
fun summarize ::
  "CoreTyEnv \<Rightarrow> (string \<Rightarrow> AllocSummary) \<Rightarrow> string list \<Rightarrow> CoreType \<Rightarrow> AllocSummary" where
  "summarize env info params (CoreTy_Datatype dt args) =
     apply_summary (length params) (info dt) (map (summarize env info params) args)"
| "summarize env info params CoreTy_Bool = summary_const CoreAlloc_Never (length params)"
| "summarize env info params (CoreTy_FiniteInt sign bits) =
     summary_const CoreAlloc_Never (length params)"
| "summarize env info params CoreTy_MathInt = summary_const CoreAlloc_Never (length params)"
| "summarize env info params CoreTy_MathReal = summary_const CoreAlloc_Never (length params)"
| "summarize env info params (CoreTy_Record flds) =
     summary_max_list (length params) (map (\<lambda>fld. summarize env info params (snd fld)) flds)"
| "summarize env info params (CoreTy_Array elemTy dims) =
     (if list_ex (\<lambda>d. d = CoreDim_Allocatable) dims
      then summary_const CoreAlloc_IfNotDefault (length params)
      else summarize env info params elemTy)"
| "summarize env info params (CoreTy_Var v) =
     (if v \<in> set params
      then (CoreAlloc_Never, map (\<lambda>p. if p = v then Mode_Identity else Mode_Never) params)
      else summary_const
             (case fmlookup (TE_AbstractAllocLevels env) v of
                None \<Rightarrow> CoreAlloc_Always
              | Some l \<Rightarrow> l)
             (length params))"
| "summarize env info params (CoreTy_Extern n l) = summary_const l (length params)"

(* summarize is monotone in the datatype summaries. *)
lemma summarize_mono:
  assumes "\<And>dt. summary_le (info1 dt) (info2 dt)"
  shows "summary_le (summarize env info1 params ty) (summarize env info2 params ty)"
  using assms
proof (induction env info1 params ty rule: summarize.induct)
  case (1 env info1 params dt args)
  have IH: "\<And>x. x \<in> set args \<Longrightarrow>
              summary_le (summarize env info1 params x) (summarize env info2 params x)"
    by (rule "1.IH"[OF _ "1.prems"])
  have "list_all2 summary_le (map (summarize env info1 params) args)
                             (map (summarize env info2 params) args)"
    using IH by (auto simp: list_all2_conv_all_nth)
  then show ?case by (simp add: apply_summary_mono[OF "1.prems"])
next
  case (6 env info1 params flds)
  have IH: "\<And>fld. fld \<in> set flds \<Longrightarrow>
              summary_le (summarize env info1 params (snd fld)) (summarize env info2 params (snd fld))"
    by (rule "6.IH"[OF _ "6.prems"])
  have "list_all2 summary_le (map (\<lambda>fld. summarize env info1 params (snd fld)) flds)
                             (map (\<lambda>fld. summarize env info2 params (snd fld)) flds)"
    using IH by (auto simp: list_all2_conv_all_nth)
  then show ?case by (simp add: summary_max_list_mono)
next
  case (7 env info1 params elemTy dims)
  show ?case using "7.IH"[OF _ "7.prems"] by auto
qed simp_all

(* The summary of a type has one mode per parameter. *)
lemma summary_max_length:
  "length (snd (summary_max s1 s2)) = min (length (snd s1)) (length (snd s2))"
  by (simp add: summary_max_def)

lemma summary_max_list_length:
  "(\<And>s. s \<in> set ss \<Longrightarrow> length (snd s) = n) \<Longrightarrow> length (snd (summary_max_list n ss)) = n"
  unfolding summary_max_list_def
proof (induction ss)
  case Nil
  then show ?case by simp
next
  case (Cons s ss)
  have "length (snd (foldr summary_max ss (summary_const CoreAlloc_Never n))) = n"
    by (rule Cons.IH) (simp add: Cons.prems)
  moreover have "length (snd s) = n" by (simp add: Cons.prems)
  ultimately show ?case by (simp add: summary_max_length)
qed

lemma apply_summary_length:
  assumes "\<And>s. s \<in> set ss \<Longrightarrow> length (snd s) = n"
  shows "length (snd (apply_summary n e ss)) = n"
  unfolding apply_summary_def
proof (rule summary_max_list_length)
  fix s assume mem: "s \<in> set (summary_const (fst e) n # map2 summary_compose (snd e) ss)"
  show "length (snd s) = n"
  proof (cases "s = summary_const (fst e) n")
    case True
    then show ?thesis by simp
  next
    case False
    with mem obtain i where "i < length ss" and "s = summary_compose (snd e ! i) (ss ! i)"
      by (auto simp: set_zip)
    then show ?thesis using assms[OF nth_mem] by simp
  qed
qed

lemma summarize_length:
  "length (snd (summarize env info params ty)) = length params"
proof (induction env info params ty rule: summarize.induct)
  case (1 env info params dt args)
  have "length (snd (apply_summary (length params) (info dt) (map (summarize env info params) args)))
          = length params"
    by (rule apply_summary_length) (auto simp: "1.IH")
  then show ?case by simp
next
  case (6 env info params flds)
  have "length (snd (summary_max_list (length params)
                       (map (\<lambda>fld. summarize env info params (snd fld)) flds)))
          = length params"
  proof (rule summary_max_list_length)
    fix s assume "s \<in> set (map (\<lambda>fld. summarize env info params (snd fld)) flds)"
    then obtain fld where "fld \<in> set flds" and "s = summarize env info params (snd fld)"
      by auto
    then show "length (snd s) = length params" by (simp add: "6.IH")
  qed
  then show ?case by simp
next
  case (7 env info params elemTy dims)
  then show ?case by auto
next
  case (8 env info params v)
  then show ?case
    by (cases "fmlookup (TE_AbstractAllocLevels env) v") auto
qed auto


(* ---- The summary of a datatype under given summaries ---- *)

(* One constructor's payload summarized relative to the datatype's own type
   variables. The arity test is only there to keep the invariant that a
   datatype's summary has one mode per parameter (ctor_summary_length), which
   the encoding below relies on; a well-formed env satisfies it anyway. *)
definition ctor_summary ::
  "CoreTyEnv \<Rightarrow> (string \<Rightarrow> AllocSummary) \<Rightarrow> nat \<Rightarrow> string \<Rightarrow> AllocSummary" where
  "ctor_summary env info arity c =
     (case fmlookup (TE_DataCtors env) c of
        None \<Rightarrow> summary_top arity
      | Some (_, tyvars, payloadTy) \<Rightarrow>
          if length tyvars = arity then summarize env info tyvars payloadTy else summary_top arity)"

(* The summary of a datatype: the max over its constructors, with the
   non-first constructors downgraded. *)
definition datatype_summary ::
  "CoreTyEnv \<Rightarrow> (string \<Rightarrow> AllocSummary) \<Rightarrow> string \<Rightarrow> AllocSummary" where
  "datatype_summary env info dt =
     (case fmlookup (TE_Datatypes env) dt of
        None \<Rightarrow> summary_top 0
      | Some arity \<Rightarrow>
          (case fmlookup (TE_DataCtorsByType env) dt of
             None \<Rightarrow> summary_top arity
           | Some [] \<Rightarrow> summary_top arity
           | Some (c # cs) \<Rightarrow>
               summary_max_list arity
                 (ctor_summary env info arity c
                  # map (\<lambda>c'. summary_compose Mode_Downgrade (ctor_summary env info arity c')) cs)))"

lemma ctor_summary_mono:
  assumes info: "\<And>dt. summary_le (info1 dt) (info2 dt)"
  shows "summary_le (ctor_summary env info1 arity c) (ctor_summary env info2 arity c)"
proof (cases "fmlookup (TE_DataCtors env) c")
  case None
  then show ?thesis by (simp add: ctor_summary_def)
next
  case (Some entry)
  obtain dtName tyvars payloadTy where e: "entry = (dtName, tyvars, payloadTy)"
    using prod_cases3 by blast
  show ?thesis using Some e by (simp add: ctor_summary_def summarize_mono[OF info])
qed

lemma datatype_summary_mono:
  assumes info: "\<And>dt. summary_le (info1 dt) (info2 dt)"
  shows "summary_le (datatype_summary env info1 dt) (datatype_summary env info2 dt)"
proof (cases "fmlookup (TE_Datatypes env) dt")
  case None
  then show ?thesis by (simp add: datatype_summary_def)
next
  case (Some arity)
  show ?thesis
  proof (cases "fmlookup (TE_DataCtorsByType env) dt")
    case None
    with Some show ?thesis by (simp add: datatype_summary_def)
  next
    case (Some ctors)
    show ?thesis
    proof (cases ctors)
      case Nil
      with \<open>fmlookup (TE_Datatypes env) dt = Some arity\<close> Some show ?thesis
        by (simp add: datatype_summary_def)
    next
      case (Cons c cs)
      have tl: "list_all2 summary_le
              (map (\<lambda>c'. summary_compose Mode_Downgrade (ctor_summary env info1 arity c')) cs)
              (map (\<lambda>c'. summary_compose Mode_Downgrade (ctor_summary env info2 arity c')) cs)"
        unfolding list_all2_conv_all_nth
        by (auto intro: summary_compose_mono ctor_summary_mono[OF info])
      have "list_all2 summary_le
              (ctor_summary env info1 arity c
               # map (\<lambda>c'. summary_compose Mode_Downgrade (ctor_summary env info1 arity c')) cs)
              (ctor_summary env info2 arity c
               # map (\<lambda>c'. summary_compose Mode_Downgrade (ctor_summary env info2 arity c')) cs)"
        using tl ctor_summary_mono[OF info] by simp
      then have "summary_le
              (summary_max_list arity (ctor_summary env info1 arity c
               # map (\<lambda>c'. summary_compose Mode_Downgrade (ctor_summary env info1 arity c')) cs))
              (summary_max_list arity (ctor_summary env info2 arity c
               # map (\<lambda>c'. summary_compose Mode_Downgrade (ctor_summary env info2 arity c')) cs))"
        by (rule summary_max_list_mono)
      with \<open>fmlookup (TE_Datatypes env) dt = Some arity\<close> Some Cons show ?thesis
        by (simp add: datatype_summary_def)
    qed
  qed
qed

lemma ctor_summary_length:
  "length (snd (ctor_summary env info arity c)) = arity"
  unfolding ctor_summary_def
  by (auto split: option.splits prod.splits simp: summarize_length)

lemma datatype_summary_length:
  assumes "fmlookup (TE_Datatypes env) dt = Some arity"
  shows "length (snd (datatype_summary env info dt)) = arity"
proof (cases "fmlookup (TE_DataCtorsByType env) dt")
  case None
  with assms show ?thesis by (simp add: datatype_summary_def)
next
  case (Some ctors)
  show ?thesis
  proof (cases ctors)
    case Nil
    with assms Some show ?thesis by (simp add: datatype_summary_def)
  next
    case (Cons c cs)
    have "length (snd (summary_max_list arity
            (ctor_summary env info arity c
             # map (\<lambda>c'. summary_compose Mode_Downgrade (ctor_summary env info arity c')) cs))) = arity"
      by (rule summary_max_list_length) (auto simp: ctor_summary_length)
    with assms Some Cons show ?thesis by (simp add: datatype_summary_def)
  qed
qed


(* ---- The fixpoint: atoms, encoding and decoding ---- *)

(* The datatype summaries are computed as the least fixpoint of a monotone
   operator on a finite powerset lattice (while_option_finite_subset_Some,
   lfp_the_while_option). The state is a set of atoms, read as "at least":
   AA_Base dt l says the base level of dt is at least l, and AA_Mode dt i m
   says the mode of dt's i-th parameter is at least m. An entry is encoded as
   the downward-closed set of atoms it dominates and decoded by taking the
   largest atom present; both directions are monotone, so the operator is. *)
datatype AllocAtom =
    AA_Base string CoreAllocLevel
  | AA_Mode string nat AllocMode

fun atom_name :: "AllocAtom \<Rightarrow> string" where
  "atom_name (AA_Base dt _) = dt"
| "atom_name (AA_Mode dt _ _) = dt"

definition all_levels :: "CoreAllocLevel list" where
  "all_levels = [CoreAlloc_Never, CoreAlloc_IfNotDefault, CoreAlloc_Always]"

definition all_modes :: "AllocMode list" where
  "all_modes = [Mode_Never, Mode_Downgrade, Mode_Identity]"

lemma all_levels_UNIV [simp]: "set all_levels = UNIV"
proof -
  have "l \<in> set all_levels" for l by (cases l) (simp_all add: all_levels_def)
  then show ?thesis by blast
qed

lemma all_modes_UNIV [simp]: "set all_modes = UNIV"
proof -
  have "m \<in> set all_modes" for m by (cases m) (simp_all add: all_modes_def)
  then show ?thesis by blast
qed

(* Decoding: the largest atom present. *)
definition decode_level :: "AllocAtom set \<Rightarrow> string \<Rightarrow> CoreAllocLevel" where
  "decode_level A dt =
     (if AA_Base dt CoreAlloc_Always \<in> A then CoreAlloc_Always
      else if AA_Base dt CoreAlloc_IfNotDefault \<in> A then CoreAlloc_IfNotDefault
      else CoreAlloc_Never)"

definition decode_mode :: "AllocAtom set \<Rightarrow> string \<Rightarrow> nat \<Rightarrow> AllocMode" where
  "decode_mode A dt i =
     (if AA_Mode dt i Mode_Identity \<in> A then Mode_Identity
      else if AA_Mode dt i Mode_Downgrade \<in> A then Mode_Downgrade
      else Mode_Never)"

definition decode_entry :: "AllocAtom set \<Rightarrow> string \<Rightarrow> nat \<Rightarrow> AllocSummary" where
  "decode_entry A dt arity = (decode_level A dt, map (decode_mode A dt) [0..<arity])"

(* The summaries read from a set of atoms. A name that is not a datatype of
   the env (which well-kinded types never mention) gets the top summary. *)
definition decode_info :: "CoreTyEnv \<Rightarrow> AllocAtom set \<Rightarrow> string \<Rightarrow> AllocSummary" where
  "decode_info env A dt =
     (case fmlookup (TE_Datatypes env) dt of
        None \<Rightarrow> summary_top 0
      | Some arity \<Rightarrow> decode_entry A dt arity)"

(* Encoding: all atoms the entry dominates. *)
definition encode_entry :: "string \<Rightarrow> nat \<Rightarrow> AllocSummary \<Rightarrow> AllocAtom list" where
  "encode_entry dt arity entry =
     map (AA_Base dt) (filter (\<lambda>l. alloc_level_le l (fst entry)) all_levels)
     @ concat (map (\<lambda>i. map (AA_Mode dt i) (filter (\<lambda>m. mode_le m (snd entry ! i)) all_modes))
                   [0..<min arity (length (snd entry))])"

lemma in_encode_entry:
  "x \<in> set (encode_entry dt arity (b, ms)) \<longleftrightarrow>
     (\<exists>l. x = AA_Base dt l \<and> alloc_level_le l b) \<or>
     (\<exists>i m. i < arity \<and> i < length ms \<and> mode_le m (ms ! i) \<and> x = AA_Mode dt i m)"
  by (fastforce simp: encode_entry_def)

lemma encode_entry_name:
  assumes "x \<in> set (encode_entry dt arity e)"
  shows "atom_name x = dt"
proof -
  obtain b ms where "e = (b, ms)" by (cases e)
  with assms show ?thesis by (auto simp: in_encode_entry)
qed

(* Decoding depends only on the atoms of the name being decoded. *)
lemma decode_entry_cong:
  assumes "\<And>x. atom_name x = dt \<Longrightarrow> x \<in> A \<longleftrightarrow> x \<in> B"
  shows "decode_entry A dt arity = decode_entry B dt arity"
  unfolding decode_entry_def decode_level_def decode_mode_def
  by (simp add: assms)

(* Decoding inverts encoding, for an entry of the right arity. *)
lemma decode_entry_encode:
  assumes "length (snd e) = arity"
  shows "decode_entry (set (encode_entry dt arity e)) dt arity = e"
proof -
  obtain b ms where e: "e = (b, ms)" by (cases e)
  have len: "length ms = arity" using assms e by simp
  have lvl: "decode_level (set (encode_entry dt arity (b, ms))) dt = b"
    by (cases b) (simp_all add: decode_level_def in_encode_entry alloc_level_le_def)
  have md: "\<And>i. i < arity \<Longrightarrow> decode_mode (set (encode_entry dt arity (b, ms))) dt i = ms ! i"
  proof -
    fix i assume "i < arity"
    then show "decode_mode (set (encode_entry dt arity (b, ms))) dt i = ms ! i"
      using len by (cases "ms ! i") (simp_all add: decode_mode_def in_encode_entry mode_le_def)
  qed
  have "map (decode_mode (set (encode_entry dt arity (b, ms))) dt) [0..<arity] = ms"
    using md len by (intro nth_equalityI) simp_all
  with lvl e show ?thesis by (simp add: decode_entry_def)
qed

(* Monotonicity of decoding and encoding. *)
lemma decode_level_mono:
  "A \<subseteq> B \<Longrightarrow> alloc_level_le (decode_level A dt) (decode_level B dt)"
  unfolding decode_level_def alloc_level_le_def by auto

lemma decode_mode_mono:
  "A \<subseteq> B \<Longrightarrow> mode_le (decode_mode A dt i) (decode_mode B dt i)"
  unfolding decode_mode_def mode_le_def by auto

lemma decode_entry_mono:
  "A \<subseteq> B \<Longrightarrow> summary_le (decode_entry A dt arity) (decode_entry B dt arity)"
  unfolding decode_entry_def
  by (auto simp: summary_le_def list_all2_conv_all_nth decode_level_mono decode_mode_mono)

lemma decode_info_mono:
  "A \<subseteq> B \<Longrightarrow> summary_le (decode_info env A dt) (decode_info env B dt)"
  unfolding decode_info_def by (auto split: option.splits simp: decode_entry_mono)

lemma encode_entry_mono:
  assumes "summary_le e1 e2"
  shows "set (encode_entry dt arity e1) \<subseteq> set (encode_entry dt arity e2)"
proof -
  obtain b1 ms1 where e1: "e1 = (b1, ms1)" by (cases e1)
  obtain b2 ms2 where e2: "e2 = (b2, ms2)" by (cases e2)
  from assms e1 e2 have bl: "alloc_level_le b1 b2" and ml: "list_all2 mode_le ms1 ms2"
    by (simp_all add: summary_le_def)
  have len: "length ms2 = length ms1" using ml by (simp add: list_all2_lengthD)
  have mi: "\<And>i. i < length ms1 \<Longrightarrow> mode_le (ms1 ! i) (ms2 ! i)"
    using ml by (simp add: list_all2_conv_all_nth)
  show ?thesis
    unfolding e1 e2
    by (fastforce simp: in_encode_entry len
                  intro: alloc_level_le_trans[OF _ bl] mode_le_trans[OF _ mi])
qed

(* Every encoding over arity lies within the encoding of the top summary. *)
lemma encode_entry_subset_top:
  "set (encode_entry dt arity e) \<subseteq> set (encode_entry dt arity (summary_top arity))"
proof -
  obtain b ms where e: "e = (b, ms)" by (cases e)
  show ?thesis
    unfolding e summary_top_def by (auto simp: in_encode_entry)
qed


(* ---- The operator and its least fixpoint ---- *)

(* One round: every datatype of the env is summarized under the summaries
   decoded from the current atoms, and the results are re-encoded. *)
definition alloc_step :: "CoreTyEnv \<Rightarrow> AllocAtom set \<Rightarrow> AllocAtom set" where
  "alloc_step env A =
     (\<Union>dt \<in> fset (fmdom (TE_Datatypes env)).
        set (encode_entry dt (the (fmlookup (TE_Datatypes env) dt))
                          (datatype_summary env (decode_info env A) dt)))"

lemma alloc_step_code [code]:
  "alloc_step env A =
     set (concat (map (\<lambda>dt. encode_entry dt (the (fmlookup (TE_Datatypes env) dt))
                                        (datatype_summary env (decode_info env A) dt))
                     (sorted_list_of_fset (fmdom (TE_Datatypes env)))))"
  unfolding alloc_step_def by simp

(* All atoms of the env's datatypes: the finite universe the iteration lives in. *)
definition alloc_universe :: "CoreTyEnv \<Rightarrow> AllocAtom set" where
  "alloc_universe env =
     (\<Union>dt \<in> fset (fmdom (TE_Datatypes env)).
        set (encode_entry dt (the (fmlookup (TE_Datatypes env) dt))
                          (summary_top (the (fmlookup (TE_Datatypes env) dt)))))"

lemma alloc_universe_finite: "finite (alloc_universe env)"
  unfolding alloc_universe_def by (rule finite_UN_I) simp_all

lemma alloc_step_mono: "mono (alloc_step env)"
proof (rule monoI)
  fix A B :: "AllocAtom set"
  assume sub: "A \<subseteq> B"
  have dec: "\<And>dt. summary_le (decode_info env A dt) (decode_info env B dt)"
    using decode_info_mono[OF sub] .
  have enc: "\<And>dt n. set (encode_entry dt n (datatype_summary env (decode_info env A) dt))
                     \<subseteq> set (encode_entry dt n (datatype_summary env (decode_info env B) dt))"
    by (rule encode_entry_mono[OF datatype_summary_mono[OF dec]])
  show "alloc_step env A \<subseteq> alloc_step env B"
    unfolding alloc_step_def by (intro UN_mono subset_refl enc)
qed

lemma alloc_step_bounded: "alloc_step env A \<subseteq> alloc_universe env"
  unfolding alloc_step_def alloc_universe_def
  by (intro UN_mono subset_refl encode_entry_subset_top)

lemma alloc_step_while_Some:
  "\<exists>P. while_option (\<lambda>A. alloc_step env A \<noteq> A) (alloc_step env) {} = Some P"
  by (rule while_option_finite_subset_Some[OF alloc_step_mono _ alloc_universe_finite])
     (rule alloc_step_bounded)

(* The fixpoint, as atoms and as summaries. *)
definition datatype_alloc_atoms :: "CoreTyEnv \<Rightarrow> AllocAtom set" where
  "datatype_alloc_atoms env = the (while_option (\<lambda>A. alloc_step env A \<noteq> A) (alloc_step env) {})"

definition datatype_alloc_info :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> AllocSummary" where
  "datatype_alloc_info env = decode_info env (datatype_alloc_atoms env)"

lemma datatype_alloc_atoms_lfp: "datatype_alloc_atoms env = lfp (alloc_step env)"
  unfolding datatype_alloc_atoms_def
  by (rule lfp_the_while_option[OF alloc_step_mono _ alloc_universe_finite, symmetric])
     (rule alloc_step_bounded)

lemma datatype_alloc_atoms_fixpoint:
  "alloc_step env (datatype_alloc_atoms env) = datatype_alloc_atoms env"
  unfolding datatype_alloc_atoms_lfp by (rule lfp_unfold[OF alloc_step_mono, symmetric])

(* Decoding one round gives exactly the per-datatype summaries of that round. *)
lemma decode_info_alloc_step:
  assumes dt: "fmlookup (TE_Datatypes env) dt = Some arity"
  shows "decode_info env (alloc_step env A) dt = datatype_summary env (decode_info env A) dt"
proof -
  let ?e = "datatype_summary env (decode_info env A) dt"
  have dom: "dt \<in> fset (fmdom (TE_Datatypes env))" using dt by (rule fmdomI)
  have mem: "\<And>x. atom_name x = dt \<Longrightarrow> x \<in> alloc_step env A \<longleftrightarrow> x \<in> set (encode_entry dt arity ?e)"
  proof -
    fix x assume n: "atom_name x = dt"
    show "x \<in> alloc_step env A \<longleftrightarrow> x \<in> set (encode_entry dt arity ?e)"
    proof
      assume "x \<in> alloc_step env A"
      then obtain dt' where dt': "dt' \<in> fset (fmdom (TE_Datatypes env))"
        and x: "x \<in> set (encode_entry dt' (the (fmlookup (TE_Datatypes env) dt'))
                                       (datatype_summary env (decode_info env A) dt'))"
        unfolding alloc_step_def by blast
      from x have "atom_name x = dt'" by (rule encode_entry_name)
      with n have "dt' = dt" by simp
      with x dt show "x \<in> set (encode_entry dt arity ?e)" by simp
    next
      assume x: "x \<in> set (encode_entry dt arity ?e)"
      show "x \<in> alloc_step env A"
        unfolding alloc_step_def by (rule UN_I[OF dom]) (simp add: dt x)
    qed
  qed
  have "decode_entry (alloc_step env A) dt arity = decode_entry (set (encode_entry dt arity ?e)) dt arity"
    by (rule decode_entry_cong) (rule mem)
  also have "... = ?e"
    by (rule decode_entry_encode) (rule datatype_summary_length[OF dt])
  finally show ?thesis using dt by (simp add: decode_info_def)
qed

(* The computed summaries satisfy the defining equations. *)
lemma datatype_alloc_info_unfold:
  assumes "fmlookup (TE_Datatypes env) dt = Some arity"
  shows "datatype_alloc_info env dt = datatype_summary env (datatype_alloc_info env) dt"
  using decode_info_alloc_step[OF assms, of "datatype_alloc_atoms env"]
  unfolding datatype_alloc_info_def datatype_alloc_atoms_fixpoint .

(* ---- The level of a type ---- *)

(* The level of a type under given datatype summaries: the base of its summary
   relative to no parameters. *)
definition alloc_level_of_type_info ::
  "CoreTyEnv \<Rightarrow> (string \<Rightarrow> AllocSummary) \<Rightarrow> CoreType \<Rightarrow> CoreAllocLevel" where
  "alloc_level_of_type_info env info ty = fst (summarize env info [] ty)"

(* The level of a type: structural recursion on the type, with the datatype
   summaries of the env. *)
definition alloc_level_of_type :: "CoreTyEnv \<Rightarrow> CoreType \<Rightarrow> CoreAllocLevel" where
  "alloc_level_of_type env ty = alloc_level_of_type_info env (datatype_alloc_info env) ty"

(* Is a type's level compatible with a declared level? That is, does the type
   give at least the facts the declaration promises? Used by link_alloc_ok
   (LinkModules.thy) for every binding of the merged substitution, and by the
   elaborator at every realization (typedef, datatype, or extern type
   realizing an abstract type). *)
definition alloc_level_compatible :: "CoreTyEnv \<Rightarrow> CoreAllocLevel \<Rightarrow> CoreType \<Rightarrow> bool" where
  "alloc_level_compatible env declared ty =
     alloc_level_le (alloc_level_of_type env ty) declared"

(* The same test under given datatype summaries, so that a caller checking
   many types in one env (link_alloc_ok) computes the fixpoint once. *)
definition alloc_level_compatible_info ::
  "CoreTyEnv \<Rightarrow> (string \<Rightarrow> AllocSummary) \<Rightarrow> CoreAllocLevel \<Rightarrow> CoreType \<Rightarrow> bool" where
  "alloc_level_compatible_info env info declared ty =
     alloc_level_le (alloc_level_of_type_info env info ty) declared"

lemma alloc_level_compatible_info_eq:
  "alloc_level_compatible env declared ty =
     alloc_level_compatible_info env (datatype_alloc_info env) declared ty"
  by (simp add: alloc_level_compatible_def alloc_level_compatible_info_def alloc_level_of_type_def)

(* Scalar and extern types have a fixed level; a type variable has its
   declared level, or CoreAlloc_Always if it has none. *)
lemma alloc_level_of_type_scalar [simp]:
  "alloc_level_of_type env CoreTy_Bool = CoreAlloc_Never"
  "alloc_level_of_type env (CoreTy_FiniteInt sign bits) = CoreAlloc_Never"
  "alloc_level_of_type env CoreTy_MathInt = CoreAlloc_Never"
  "alloc_level_of_type env CoreTy_MathReal = CoreAlloc_Never"
  "alloc_level_of_type env (CoreTy_Extern n l) = l"
  by (simp_all add: alloc_level_of_type_def alloc_level_of_type_info_def summary_const_def)

lemma alloc_level_of_type_Var [simp]:
  "alloc_level_of_type env (CoreTy_Var n) =
     (case fmlookup (TE_AbstractAllocLevels env) n of
        None \<Rightarrow> CoreAlloc_Always
      | Some l \<Rightarrow> l)"
  by (cases "fmlookup (TE_AbstractAllocLevels env) n")
     (simp_all add: alloc_level_of_type_def alloc_level_of_type_info_def summary_const_def)

end
