theory MetavarName
  imports "../core/CoreSyntax" "../core/CoreFreeVars" "../util/NatToString"
begin

(* ========================================================================== *)
(* Metavariable names                                                          *)
(*                                                                            *)
(* Compiler-generated unification variables ("metavariables") are given names *)
(* of the form "?<n>" — a question mark followed by the decimal rendering of  *)
(* a nat counter. This keeps them in the same string namespace as rigid       *)
(* (source-level) type variables, but disjoint from any source name (a source *)
(* identifier cannot contain "?").                                            *)
(* ========================================================================== *)

(* The name of the metavariable allocated from counter value i. *)
definition mv_name :: "nat \<Rightarrow> string" where
  "mv_name i = CHR ''?'' # nat_to_string i"

(* mv_name is injective. *)
lemma mv_name_inj: "inj mv_name"
  by (rule injI) (auto simp: mv_name_def nat_to_string_injective)

lemma mv_name_eq_iff [simp]: "mv_name i = mv_name j \<longleftrightarrow> i = j"
  using mv_name_inj by (auto dest: injD)

(* inj_on form, convenient for distinct_map / card arguments. *)
lemma inj_on_mv_name [simp]: "inj_on mv_name S"
  using mv_name_inj by (simp add: inj_on_def)


(* ========================================================================== *)
(* Metavar blocks                                                             *)
(*                                                                            *)
(* mv_block lo hi is the CoreType list of fresh tyvar *types* allocated for   *)
(* the half-open interval [lo, hi).                                           *)
(*                                                                            *)
(* NB. mv_block produces a CoreType list. The *name set* used in env tyvar    *)
(* sets and substitution domains is "mv_name ` {lo..<hi}" (a string set) —   *)
(* a different object; see ExtendEnvWithTyvars / clear_metavars.              *)
(* ========================================================================== *)

definition mv_block :: "nat \<Rightarrow> nat \<Rightarrow> CoreType list" where
  "mv_block lo hi = map (CoreTy_Var \<circ> mv_name) [lo ..< hi]"

lemma mv_block_empty [simp]: "lo \<ge> hi \<Longrightarrow> mv_block lo hi = []"
  unfolding mv_block_def by simp

lemma mv_block_length [simp]: "length (mv_block lo hi) = hi - lo"
  unfolding mv_block_def by simp

(* A block is map CoreTy_Var over the list of fresh names. This is the bridge
   to lemmas like list_all_tyvar_is_well_kinded, which are phrased over
   map CoreTy_Var of a name list. *)
lemma mv_block_eq_map_CoreTy_Var:
  "mv_block lo hi = map CoreTy_Var (map mv_name [lo ..< hi])"
  unfolding mv_block_def by simp

(* Splitting a contiguous block at a midpoint. *)
lemma mv_block_split:
  assumes "lo \<le> mid" and "mid \<le> hi"
  shows "mv_block lo hi = mv_block lo mid @ mv_block mid hi"
proof -
  have "[lo..<hi] = [lo..<mid] @ [mid..<hi]"
    using assms le_Suc_ex upt_add_eq_append by blast
  thus ?thesis unfolding mv_block_def by simp
qed

(* Membership: the elements of a block are exactly the CoreTy_Var (mv_name i)
   for i in the interval. *)
lemma mv_block_mem [simp]:
  "x \<in> set (mv_block lo hi) \<longleftrightarrow> (\<exists>i. lo \<le> i \<and> i < hi \<and> x = CoreTy_Var (mv_name i))"
  unfolding mv_block_def by auto

lemma mv_block_nth:
  assumes "i < hi - lo"
  shows "mv_block lo hi ! i = CoreTy_Var (mv_name (lo + i))"
  using assms unfolding mv_block_def by simp

(* A block is distinct, since mv_name is injective and [lo..<hi] is distinct. *)
lemma distinct_mv_block [simp]: "distinct (mv_block lo hi)"
  unfolding mv_block_def
  by (simp add: distinct_map comp_inj_on) (simp add: inj_on_def)

(* The type variables of a block are exactly the names mv_name ` {lo..<hi}. *)
lemma type_tyvars_mv_block:
  "\<Union>(set (map type_tyvars (mv_block lo hi))) = mv_name ` {lo..<hi}"
  unfolding mv_block_def by auto


(* ========================================================================== *)
(* Metavar name sets                                                          *)
(*                                                                            *)
(* mv_fset lo hi is the string fset of fresh tyvar *names* allocated for the  *)
(* half-open interval [lo, hi). It is the object installed into the env tyvar *)
(* sets (TE_TypeVars / TE_RuntimeTypeVars).                                   *)
(* ========================================================================== *)

definition mv_fset :: "nat \<Rightarrow> nat \<Rightarrow> string fset" where
  "mv_fset lo hi = fset_of_list (map mv_name [lo ..< hi])"

lemma mv_fset_empty [simp]: "lo \<ge> hi \<Longrightarrow> mv_fset lo hi = {||}"
  unfolding mv_fset_def by simp

(* Membership: name x is in the block iff it is mv_name i for some i in range. *)
lemma mv_fset_mem [simp]:
  "x |\<in>| mv_fset lo hi \<longleftrightarrow> (\<exists>i. lo \<le> i \<and> i < hi \<and> x = mv_name i)"
  unfolding mv_fset_def by (auto simp: fset_of_list_elem)

(* Every fresh name of a block lies in the corresponding name set. *)
lemma mv_name_in_mv_fset:
  assumes "lo \<le> i" and "i < hi"
  shows "mv_name i |\<in>| mv_fset lo hi"
  using assms by auto

(* Splitting a contiguous interval of fresh type-variable names. *)
lemma mv_fset_split:
  assumes "lo \<le> mid" and "mid \<le> hi"
  shows "mv_fset lo mid |\<union>| mv_fset mid hi = mv_fset lo hi"
proof -
  have "[lo..<hi] = [lo..<mid] @ [mid..<hi]"
    using assms le_Suc_ex upt_add_eq_append by blast
  thus ?thesis unfolding mv_fset_def by simp
qed

(* Widening the interval enlarges the name set: disjoint-range images compose. *)
lemma mv_fset_mono:
  assumes "lo' \<le> lo" and "hi \<le> hi'"
  shows "mv_fset lo hi |\<subseteq>| mv_fset lo' hi'"
  using assms by (auto simp: less_le_trans le_less_trans)


(* ========================================================================== *)
(* Freshness predicate                                                        *)
(*                                                                            *)
(* tyvar_fresh_ok n k says that: either n is not a metavariable name, or it's *)
(* a metavariable name "?<i>" where i < k.                                    *)
(*                                                                            *)
(* This means that a variable named n will not clash with any metavariable    *)
(* that will be allocated from next_mv counter value k onwards.               *)
(*                                                                            *)
(* The elaborator's freshness invariant — fresh metavars never collide with  *)
(* anything already in scope — is "every n in TE_TypeVars env satisfies      *)
(* tyvar_fresh_ok n next_mv".                                                 *)
(* ========================================================================== *)

definition tyvar_fresh_ok :: "string \<Rightarrow> nat \<Rightarrow> bool" where
  "tyvar_fresh_ok n k \<longleftrightarrow> (\<forall>i. n = mv_name i \<longrightarrow> i < k)"

(* For a metavar name, fresh-ok-at-k is exactly "allocated below k". *)
lemma tyvar_fresh_ok_mv_name [simp]: "tyvar_fresh_ok (mv_name i) k \<longleftrightarrow> i < k"
  unfolding tyvar_fresh_ok_def by auto

(* Monotone in the counter: fresh-ok at k is fresh-ok at any k' \<ge> k. *)
lemma tyvar_fresh_ok_mono:
  assumes "tyvar_fresh_ok n k" and "k \<le> k'"
  shows "tyvar_fresh_ok n k'"
  using assms unfolding tyvar_fresh_ok_def by auto

(* A fresh-ok-at-lo name is disjoint from a block allocated from lo upward.
   This is the disjointness the freshness invariant is ultimately used for. *)
lemma tyvar_fresh_ok_notin_mv_fset:
  assumes "tyvar_fresh_ok n lo"
  shows "n |\<notin>| mv_fset lo hi"
  using assms unfolding tyvar_fresh_ok_def by auto

end
