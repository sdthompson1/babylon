theory SizeBound
  imports SizeExpr "../core/CoreModuleTypecheck" "../graph/Dependency"
begin

(* ========================================================================== *)
(* The static size bound (minic/DESIGN.md, section 3.2)                       *)
(* ========================================================================== *)

(* core_module_sizeable P m is the executable check that every size the
   generated code computes fits a uint64_t, at pointer size P (the theorems
   take enc_ptr_size enc <= P as a hypothesis; sizes are monotone in the
   pointer size). It checks, in this order:

   1. datatypes_acyclic (DatatypeAcyclic.thy), and that every datatype has
      at most 2^32 constructors (so that its tags fit the tag type);
   2. the call graph is acyclic: the functions are ordered callers first
      (call_order), failing on a cycle (the elaborator rejects recursion, so
      this cannot fail on elaborator output);
   3. per-function bounds B_f for the sizes of the type parameters,
      computed top-down in that order (compute_bounds): for every call site
      f<ty1..tym> in a function g, B_f(Ti) is at least |tyi| evaluated at
      B_g; main and uncalled functions have bound 0;
   4. every type that the code of a function f computes the size of fits
      (size_fits) at B_f: the parameter and return types, the type of every
      subterm of the body, the type of every variable declaration, the type
      arguments and the instantiated return type of every call, and the
      cast types; and every global's type fits.

   The soundness lemmas (static part):
     (a) sizeable_call_bound: at every call site f<tys> in g, |tyi| at any
         assignment bounded by B_g is at most B_f(Ti);
     (b) sizeable_fun_type_fits: every checked type of g fits at any
         assignment bounded by B_g;
     (c) sizeable_global_fits: every global's type fits;
     (d) sizeable_acyclic: the datatypes are acyclic.
   The dynamic part ("IS_TyArgs of the running function is bounded by B_f")
   is an induction over the interpreter that the simulation proof of stage 6
   carries as part of its invariant, discharging the call case with (a).

   Note: No realistic program is ever expected to fail the sizeable_check; but the
   check is still needed, to rule out pathological cases where the proofs would fail.
   (If the check does fail, compilation is aborted with an error, rather than allowing
   faulty code to be generated.)
*)


section \<open>Call sites\<close>

fun term_calls :: "CoreTerm \<Rightarrow> (string \<times> CoreType list) list" where
  "term_calls (CoreTm_LitArray _ tms) = concat (map term_calls tms)"
| "term_calls (CoreTm_Cast _ tm) = term_calls tm"
| "term_calls (CoreTm_Unop _ tm) = term_calls tm"
| "term_calls (CoreTm_Binop _ lhs rhs) = term_calls lhs @ term_calls rhs"
| "term_calls (CoreTm_Let _ rhs body) = term_calls rhs @ term_calls body"
| "term_calls (CoreTm_Quantifier _ _ _ body) = term_calls body"
| "term_calls (CoreTm_FunctionCall f tys args) = (f, tys) # concat (map term_calls args)"
| "term_calls (CoreTm_VariantCtor _ _ payload) = term_calls payload"
| "term_calls (CoreTm_Record flds) = concat (map (term_calls \<circ> snd) flds)"
| "term_calls (CoreTm_RecordProj tm _) = term_calls tm"
| "term_calls (CoreTm_VariantProj tm _) = term_calls tm"
| "term_calls (CoreTm_ArrayProj arr idxs) = term_calls arr @ concat (map term_calls idxs)"
| "term_calls (CoreTm_Match scrut arms) = term_calls scrut @ concat (map (term_calls \<circ> snd) arms)"
| "term_calls (CoreTm_Sizeof tm) = term_calls tm"
| "term_calls (CoreTm_Allocated _ tm) = term_calls tm"
| "term_calls _ = []"

fun stmt_calls :: "CoreStatement \<Rightarrow> (string \<times> CoreType list) list"
and stmts_calls :: "CoreStatement list \<Rightarrow> (string \<times> CoreType list) list" where
  "stmt_calls (CoreStmt_VarDecl _ _ _ _ tm) = term_calls tm"
| "stmt_calls (CoreStmt_VarDeclCall _ _ _ _ f tys args) = (f, tys) # concat (map term_calls args)"
| "stmt_calls (CoreStmt_Fix _ _) = []"
| "stmt_calls (CoreStmt_Obtain _ _ tm) = term_calls tm"
| "stmt_calls (CoreStmt_Use tm) = term_calls tm"
| "stmt_calls (CoreStmt_Assign _ _ lhs rhs) = term_calls lhs @ term_calls rhs"
| "stmt_calls (CoreStmt_AssignCall _ lhs _ f tys args) = (f, tys) # term_calls lhs @ concat (map term_calls args)"
| "stmt_calls (CoreStmt_Swap _ lhs rhs) = term_calls lhs @ term_calls rhs"
| "stmt_calls (CoreStmt_Return tm) = term_calls tm"
| "stmt_calls (CoreStmt_Assert condOpt body) =
    (case condOpt of None \<Rightarrow> [] | Some tm \<Rightarrow> term_calls tm) @ stmts_calls body"
| "stmt_calls (CoreStmt_Assume tm) = term_calls tm"
| "stmt_calls (CoreStmt_While _ cond invars decr body) =
    term_calls cond @ concat (map term_calls invars)
    @ (case decr of None \<Rightarrow> [] | Some tm \<Rightarrow> term_calls tm) @ stmts_calls body"
| "stmt_calls (CoreStmt_Match _ scrut arms) = term_calls scrut @ concat (map (stmts_calls \<circ> snd) arms)"
| "stmt_calls (CoreStmt_ShowHide _ _) = []"
| "stmt_calls (CoreStmt_Block body) = stmts_calls body"
| "stmts_calls [] = []"
| "stmts_calls (s # ss) = stmt_calls s @ stmts_calls ss"

(* The call sites of a function (none for an extern or unknown function). *)
definition fun_calls :: "CoreModule \<Rightarrow> string \<Rightarrow> (string \<times> CoreType list) list" where
  "fun_calls m f =
    (case fmlookup (CM_Functions m) f of
       Some cf \<Rightarrow> (case CF_Body cf of Some body \<Rightarrow> stmts_calls body | None \<Rightarrow> [])
     | None \<Rightarrow> [])"

definition fun_callees :: "CoreModule \<Rightarrow> string \<Rightarrow> string list" where
  "fun_callees m f = remdups (map fst (fun_calls m f))"

definition module_fun_names :: "CoreModule \<Rightarrow> string list" where
  "module_fun_names m = map fst (sorted_list_of_fmap (CM_Functions m))"

lemma set_module_fun_names: "set (module_fun_names m) = fset (fmdom (CM_Functions m))"
  by (auto simp: module_fun_names_def sorted_list_of_fmap_def comp_def fmlookup_dom_iff)

lemma distinct_module_fun_names: "distinct (module_fun_names m)"
  by (simp add: module_fun_names_def sorted_list_of_fmap_def comp_def distinct_map inj_on_def
                sorted_list_of_fset.rep_eq)

lemma fun_calls_nonempty_dom: "fun_calls m g \<noteq> [] \<Longrightarrow> fmlookup (CM_Functions m) g \<noteq> None"
  by (auto simp: fun_calls_def split: option.splits)


section \<open>The call order\<close>

(* The SCCs of the call graph, which analyze_dependencies_generic lists callees-first. *)
definition call_sccs :: "CoreModule \<Rightarrow> (DependencyError, string list list) sum" where
  "call_sccs m = analyze_dependencies_generic (module_fun_names m) id (fun_callees m)"

(* The functions of a module, in an order with callers before callees. *)
definition call_order :: "CoreModule \<Rightarrow> string list" where
  "call_order m = (case call_sccs m of Inl _ \<Rightarrow> [] | Inr sccs \<Rightarrow> rev (concat sccs))"

(* None if the call graph is acyclic (and every callee is a function of the
   module); otherwise the functions of a cycle, or [] for a missing callee
   (which cannot happen for a well-typed module). *)
definition call_cycle :: "CoreModule \<Rightarrow> string list option" where
  "call_cycle m =
    (case call_sccs m of
       Inl _ \<Rightarrow> Some []
     | Inr sccs \<Rightarrow>
         (case find (\<lambda>scc. length scc \<noteq> 1) sccs of
            Some scc \<Rightarrow> Some scc
          | None \<Rightarrow>
              (case find (\<lambda>f. f \<in> set (fun_callees m f)) (module_fun_names m) of
                 Some f \<Rightarrow> Some [f]
               | None \<Rightarrow> None)))"

(* What a successful cycle check gives: an order that is a permutation of the
   functions, in which every caller precedes each of its callees. *)
lemma call_order_sound:
  assumes "call_cycle m = None"
  shows "distinct (call_order m)"
    and "set (call_order m) = fset (fmdom (CM_Functions m))"
    and "\<And>g f tys. (f, tys) \<in> set (fun_calls m g) \<Longrightarrow>
           \<exists>i j. i < j \<and> j < length (call_order m) \<and> call_order m ! i = g \<and> call_order m ! j = f"
proof -
  let ?items = "module_fun_names m"
  from assms obtain sccs where
    res: "analyze_dependencies_generic ?items id (fun_callees m) = Inr sccs"
    and single: "\<forall>scc \<in> set sccs. length scc = 1"
    and no_self: "\<forall>f \<in> set ?items. f \<notin> set (fun_callees m f)"
    unfolding call_cycle_def call_sccs_def
    by (auto simp del: analyze_dependencies_generic.simps simp: find_None_iff
             split: sum.splits option.splits)
  have order: "call_order m = rev (concat sccs)" unfolding call_order_def call_sccs_def res by simp
  have perm: "mset (concat sccs) = mset ?items"
    using analyze_dependencies_generic_permutation[OF res] by simp
  have set_c: "set (concat sccs) = set ?items" using perm by (rule mset_eq_setD)
  have len_c: "length (concat sccs) = length ?items" using perm by (rule mset_eq_length)
  have dist_c: "distinct (concat sccs)"
    by (rule iffD2[OF mset_eq_imp_distinct_iff[OF perm] distinct_module_fun_names])
  show "distinct (call_order m)" unfolding order using dist_c by simp
  show "set (call_order m) = fset (fmdom (CM_Functions m))"
    unfolding order using set_c set_module_fun_names by simp
  have concat_eq: "concat sccs = map hd sccs"
    using single
  proof (induction sccs)
    case Nil then show ?case by simp
  next
    case (Cons scc sccs)
    then obtain d where "scc = [d]" by (cases scc) auto
    with Cons show ?case by simp
  qed
  have scc_nth: "\<And>i. i < length sccs \<Longrightarrow> sccs ! i = [concat sccs ! i]"
  proof -
    fix i assume i: "i < length sccs"
    have "length (sccs ! i) = 1" using single i by simp
    then obtain d where "sccs ! i = [d]" by (cases "sccs ! i") auto
    thus "sccs ! i = [concat sccs ! i]" using concat_eq i by simp
  qed
  have len_sccs: "length sccs = length (concat sccs)" using concat_eq by simp
  \<comment> \<open>Every callee is a function of the module.\<close>
  have deps_exist: "check_deps_exist id (fun_callees m) ?items (build_item_map id ?items) = None"
  proof (cases "check_duplicate_names id ?items")
    case (Some err)
    from res[unfolded analyze_dependencies_generic.simps Some option.case] have False by simp
    thus ?thesis ..
  next
    case None
    note c1 = None
    show ?thesis
    proof (cases "check_deps_exist id (fun_callees m) ?items (build_item_map id ?items)")
      case (Some err)
      from res[unfolded analyze_dependencies_generic.simps c1 option.case Let_def Some] have False by simp
      thus ?thesis ..
    next
      case None thus ?thesis .
    qed
  qed
  have callee_in: "\<And>g f. g \<in> set ?items \<Longrightarrow> f \<in> set (fun_callees m g) \<Longrightarrow> f \<in> set ?items"
  proof -
    fix g f assume g: "g \<in> set ?items" and f: "f \<in> set (fun_callees m g)"
    have "fmlookup (build_item_map id ?items) f \<noteq> None"
      by (rule check_deps_exist_None_means_all_exist[OF deps_exist, rule_format, OF g f])
    then obtain y where "fmlookup (build_item_map id ?items) f = Some y"
      by (cases "fmlookup (build_item_map id ?items) f") auto
    hence "f |\<in>| fmdom (build_item_map id ?items)" by (rule fmdomI)
    thus "f \<in> set ?items" using build_item_map_dom[of id ?items] by simp
  qed
  fix g f tys assume call: "(f, tys) \<in> set (fun_calls m g)"
  have g_in: "g \<in> set ?items"
  proof -
    have "fun_calls m g \<noteq> []" using call by auto
    from fun_calls_nonempty_dom[OF this] obtain y where "fmlookup (CM_Functions m) g = Some y" by auto
    hence "g |\<in>| fmdom (CM_Functions m)" by (rule fmdomI)
    thus ?thesis using set_module_fun_names by simp
  qed
  have dep: "f \<in> set (fun_callees m g)" using call by (force simp: fun_callees_def)
  have f_in: "f \<in> set ?items" by (rule callee_in[OF g_in dep])
  from analyze_dependencies_generic_topological_order[OF res g_in f_in] dep
  obtain i j where ij: "i \<le> j" "i < length sccs" "j < length sccs"
    and f_i: "f \<in> set (sccs ! i)" and g_j: "g \<in> set (sccs ! j)" by auto
  from f_i scc_nth[OF ij(2)] have f_eq: "concat sccs ! i = f" by simp
  from g_j scc_nth[OF ij(3)] have g_eq: "concat sccs ! j = g" by simp
  have "i \<noteq> j"
  proof
    assume "i = j"
    with f_eq g_eq have "f = g" by simp
    with dep no_self g_in show False by blast
  qed
  with ij have ilt: "i < j" by simp
  let ?n = "length (concat sccs)"
  have j_lt: "j < ?n" and i_lt: "i < ?n" using ij len_sccs by simp_all
  have "call_order m ! (?n - 1 - j) = g" unfolding order using rev_nth[of "?n - 1 - j" "concat sccs"] j_lt g_eq by simp
  moreover have "call_order m ! (?n - 1 - i) = f" unfolding order using rev_nth[of "?n - 1 - i" "concat sccs"] i_lt f_eq by simp
  moreover have "?n - 1 - j < ?n - 1 - i" using ilt j_lt by simp
  moreover have "?n - 1 - i < length (call_order m)" unfolding order using i_lt by simp
  ultimately show "\<exists>i j. i < j \<and> j < length (call_order m) \<and> call_order m ! i = g \<and> call_order m ! j = f"
    by blast
qed


section \<open>Bounds\<close>

(* The bound of each function: the bound of each of its type parameters
   (0 for a parameter, or a function, not in the map). *)
type_synonym Bounds = "(string, (string, nat) fmap) fmap"

definition fval :: "(string, nat) fmap \<Rightarrow> string \<Rightarrow> nat" where
  "fval bf v = (case fmlookup bf v of Some n \<Rightarrow> n | None \<Rightarrow> 0)"

definition bfun :: "Bounds \<Rightarrow> string \<Rightarrow> (string, nat) fmap" where
  "bfun B f = (case fmlookup B f of Some bf \<Rightarrow> bf | None \<Rightarrow> fmempty)"

definition bval :: "Bounds \<Rightarrow> string \<Rightarrow> string \<Rightarrow> nat" where
  "bval B f v = fval (bfun B f) v"

definition bounds_le :: "Bounds \<Rightarrow> Bounds \<Rightarrow> bool" where
  "bounds_le B B' = (\<forall>f v. bval B f v \<le> bval B' f v)"

lemma bounds_le_refl [simp]: "bounds_le B B"
  by (simp add: bounds_le_def)

lemma bounds_le_trans: "bounds_le B1 B2 \<Longrightarrow> bounds_le B2 B3 \<Longrightarrow> bounds_le B1 B3"
  unfolding bounds_le_def by (blast intro: le_trans)

(* Raise the bounds of the listed type variables to at least the listed sizes. *)
fun bump :: "string list \<Rightarrow> nat list \<Rightarrow> (string, nat) fmap \<Rightarrow> (string, nat) fmap" where
  "bump (v # vs) (n # ns) bf = bump vs ns (fmupd v (max n (fval bf v)) bf)"
| "bump _ _ bf = bf"

lemma fval_bump_ge: "fval bf v \<le> fval (bump vs ns bf) v"
proof (induction vs ns bf rule: bump.induct)
  case (1 v' vs n ns bf)
  have "fval bf v \<le> fval (fmupd v' (max n (fval bf v')) bf) v"
    by (simp add: fval_def)
  with "1.IH" show ?case by simp
next
  case ("2_1" ns bf) then show ?case by simp
next
  case ("2_2" vs bf) then show ?case by simp
qed

lemma fval_bump_nth:
  assumes "distinct vs" and "i < length vs" and "i < length ns"
  shows "ns ! i \<le> fval (bump vs ns bf) (vs ! i)"
  using assms
proof (induction vs ns bf arbitrary: i rule: bump.induct)
  case (1 v vs n ns bf)
  show ?case
  proof (cases i)
    case 0
    have "n \<le> fval (fmupd v (max n (fval bf v)) bf) v" by (simp add: fval_def)
    also have "\<dots> \<le> fval (bump vs ns (fmupd v (max n (fval bf v)) bf)) v" by (rule fval_bump_ge)
    finally show ?thesis using 0 by simp
  next
    case (Suc i')
    with "1.prems" have "distinct vs" "i' < length vs" "i' < length ns" by auto
    from "1.IH"[OF this] Suc show ?thesis by simp
  qed
qed simp_all

fun update_bound :: "CoreTyEnv \<Rightarrow> nat \<Rightarrow> (string \<Rightarrow> nat) \<Rightarrow> string \<times> CoreType list \<Rightarrow> Bounds \<Rightarrow> Bounds" where
  "update_bound env P sz (f, tys) B =
    (case fmlookup (TE_Functions env) f of
       None \<Rightarrow> B
     | Some info \<Rightarrow> fmupd f (bump (FI_TyArgs info) (map (type_size env P sz) tys) (bfun B f)) B)"

lemma update_bound_other: "h \<noteq> fst c \<Longrightarrow> bval (update_bound env P sz c B) h = bval B h"
  by (cases c) (auto simp: bval_def bfun_def split: option.splits)

lemma update_bound_le: "bounds_le B (update_bound env P sz c B)"
proof (cases c)
  case (Pair f tys)
  show ?thesis unfolding bounds_le_def
  proof (intro allI)
    fix h v
    show "bval B h v \<le> bval (update_bound env P sz c B) h v"
    proof (cases "h = f")
      case True
      then show ?thesis using Pair fval_bump_ge[of "bfun B f" v]
        by (auto simp: bval_def bfun_def split: option.splits)
    next
      case False
      then show ?thesis using update_bound_other[of h c env P sz B] Pair by (simp del: update_bound.simps)
    qed
  qed
qed

lemma update_bound_ge:
  assumes "fmlookup (TE_Functions env) f = Some info" and "distinct (FI_TyArgs info)"
    and "i < length (FI_TyArgs info)" and "i < length tys"
  shows "type_size env P sz (tys ! i) \<le> bval (update_bound env P sz (f, tys) B) f (FI_TyArgs info ! i)"
  using fval_bump_nth[OF assms(2,3), of "map (type_size env P sz) tys" "bfun B f"] assms
  by (simp add: bval_def bfun_def)

lemma fold_update_bound_le: "bounds_le B (fold (update_bound env P sz) cs B)"
proof (induction cs arbitrary: B)
  case Nil then show ?case by simp
next
  case (Cons c cs)
  show ?case using update_bound_le[of B env P sz c] Cons.IH by (simp add: bounds_le_trans)
qed

lemma fold_update_bound_other:
  "h \<notin> fst ` set cs \<Longrightarrow> bval (fold (update_bound env P sz) cs B) h = bval B h"
  by (induction cs arbitrary: B) (simp_all add: update_bound_other)

lemma fold_update_bound_ge:
  assumes "(f, tys) \<in> set cs"
    and "fmlookup (TE_Functions env) f = Some info" and "distinct (FI_TyArgs info)"
    and "i < length (FI_TyArgs info)" and "i < length tys"
  shows "type_size env P sz (tys ! i) \<le> bval (fold (update_bound env P sz) cs B) f (FI_TyArgs info ! i)"
  using assms(1)
proof (induction cs arbitrary: B)
  case Nil then show ?case by simp
next
  case (Cons c cs)
  show ?case
  proof (cases "c = (f, tys)")
    case True
    have "type_size env P sz (tys ! i) \<le> bval (update_bound env P sz (f, tys) B) f (FI_TyArgs info ! i)"
      by (rule update_bound_ge[OF assms(2-5)])
    also have "\<dots> \<le> bval (fold (update_bound env P sz) cs (update_bound env P sz (f, tys) B)) f (FI_TyArgs info ! i)"
      using fold_update_bound_le unfolding bounds_le_def by blast
    finally show ?thesis using True by simp
  next
    case False
    with Cons.prems have "(f, tys) \<in> set cs" by simp
    from Cons.IH[OF this] show ?thesis by simp
  qed
qed

(* Processing a function: raise the bounds of its callees from its own bound. *)
definition process_fun :: "CoreTyEnv \<Rightarrow> nat \<Rightarrow> CoreModule \<Rightarrow> string \<Rightarrow> Bounds \<Rightarrow> Bounds" where
  "process_fun env P m g B = fold (update_bound env P (bval B g)) (fun_calls m g) B"

lemma process_fun_le: "bounds_le B (process_fun env P m g B)"
  unfolding process_fun_def by (rule fold_update_bound_le)

lemma process_fun_other:
  "h \<notin> fst ` set (fun_calls m g) \<Longrightarrow> bval (process_fun env P m g B) h = bval B h"
  unfolding process_fun_def by (rule fold_update_bound_other)

lemma process_fun_ge:
  assumes "(f, tys) \<in> set (fun_calls m g)"
    and "fmlookup (TE_Functions env) f = Some info" and "distinct (FI_TyArgs info)"
    and "i < length (FI_TyArgs info)" and "i < length tys"
  shows "type_size env P (bval B g) (tys ! i) \<le> bval (process_fun env P m g B) f (FI_TyArgs info ! i)"
  unfolding process_fun_def by (rule fold_update_bound_ge[OF assms])

definition compute_bounds :: "nat \<Rightarrow> CoreModule \<Rightarrow> Bounds" where
  "compute_bounds P m = fold (process_fun (CM_TyEnv m) P m) (call_order m) fmempty"

(* The bounds after the first k functions of the order. *)
definition bounds_after :: "nat \<Rightarrow> CoreModule \<Rightarrow> nat \<Rightarrow> Bounds" where
  "bounds_after P m k = fold (process_fun (CM_TyEnv m) P m) (take k (call_order m)) fmempty"

lemma bounds_after_Suc:
  "k < length (call_order m) \<Longrightarrow>
   bounds_after P m (Suc k) = process_fun (CM_TyEnv m) P m (call_order m ! k) (bounds_after P m k)"
  by (simp add: bounds_after_def take_Suc_conv_app_nth)

lemma bounds_after_full: "compute_bounds P m = bounds_after P m (length (call_order m))"
  by (simp add: compute_bounds_def bounds_after_def)

lemma bounds_after_le:
  "k \<le> l \<Longrightarrow> bounds_le (bounds_after P m k) (bounds_after P m l)"
proof (induction l)
  case 0 then show ?case by simp
next
  case (Suc l)
  show ?case
  proof (cases "k = Suc l")
    case True then show ?thesis by simp
  next
    case False
    with Suc.prems have "k \<le> l" by simp
    from Suc.IH[OF this] have le1: "bounds_le (bounds_after P m k) (bounds_after P m l)" .
    have "bounds_le (bounds_after P m l) (bounds_after P m (Suc l))"
    proof (cases "l < length (call_order m)")
      case True then show ?thesis by (simp add: bounds_after_Suc process_fun_le)
    next
      case False
      hence "take (Suc l) (call_order m) = take l (call_order m)" by simp
      then show ?thesis by (simp add: bounds_after_def)
    qed
    with le1 show ?thesis by (rule bounds_le_trans)
  qed
qed

(* The bound of a function is final once the function has been processed: a
   later function in the order is never one of its callers. *)
lemma bounds_after_stable:
  assumes "call_cycle m = None" and "j < length (call_order m)" and "j \<le> l"
  shows "bval (bounds_after P m l) (call_order m ! j) = bval (bounds_after P m j) (call_order m ! j)"
  using assms(3)
proof (induction l)
  case 0 then show ?case by simp
next
  case (Suc l)
  show ?case
  proof (cases "j = Suc l")
    case True then show ?thesis by simp
  next
    case False
    with Suc.prems have jl: "j \<le> l" by simp
    show ?thesis
    proof (cases "l < length (call_order m)")
      case True
      let ?g = "call_order m ! j" and ?h = "call_order m ! l"
      have "?g \<notin> fst ` set (fun_calls m ?h)"
      proof
        assume "?g \<in> fst ` set (fun_calls m ?h)"
        then obtain tys where "(?g, tys) \<in> set (fun_calls m ?h)" by auto
        from call_order_sound(3)[OF assms(1) this] obtain i' j' where
          "i' < j'" "j' < length (call_order m)" "call_order m ! i' = ?h" "call_order m ! j' = ?g" by blast
        with call_order_sound(1)[OF assms(1)] True assms(2) have "i' = l" "j' = j"
          by (auto simp: nth_eq_iff_index_eq)
        with \<open>i' < j'\<close> jl show False by simp
      qed
      from process_fun_other[OF this] Suc.IH[OF jl] True show ?thesis
        by (simp add: bounds_after_Suc)
    next
      case False
      hence "take (Suc l) (call_order m) = take l (call_order m)" by simp
      with Suc.IH[OF jl] show ?thesis by (simp add: bounds_after_def)
    qed
  qed
qed

(* Soundness (a), in terms of compute_bounds: at every call site, the sizes
   of the type arguments at the caller's bound are at most the callee's bound. *)
lemma compute_bounds_call:
  assumes "call_cycle m = None"
    and "(f, tys) \<in> set (fun_calls m g)"
    and "fmlookup (TE_Functions (CM_TyEnv m)) f = Some info" and "distinct (FI_TyArgs info)"
    and "i < length (FI_TyArgs info)" and "i < length tys"
  shows "type_size (CM_TyEnv m) P (bval (compute_bounds P m) g) (tys ! i)
         \<le> bval (compute_bounds P m) f (FI_TyArgs info ! i)"
proof -
  let ?order = "call_order m"
  from call_order_sound(3)[OF assms(1,2)] obtain jg jf where
    "jg < jf" and jf: "jf < length ?order" and g: "?order ! jg = g" and f: "?order ! jf = f" by blast
  have jg: "jg < length ?order" using \<open>jg < jf\<close> jf by simp
  have final_g: "bval (compute_bounds P m) g = bval (bounds_after P m jg) g"
    unfolding bounds_after_full g[symmetric] by (rule bounds_after_stable[OF assms(1) jg]) (use jg in simp)
  have "type_size (CM_TyEnv m) P (bval (bounds_after P m jg) g) (tys ! i)
        \<le> bval (process_fun (CM_TyEnv m) P m g (bounds_after P m jg)) f (FI_TyArgs info ! i)"
    by (rule process_fun_ge[OF assms(2-6)])
  also have "\<dots> = bval (bounds_after P m (Suc jg)) f (FI_TyArgs info ! i)"
    using bounds_after_Suc[OF jg] g by simp
  also have "\<dots> \<le> bval (compute_bounds P m) f (FI_TyArgs info ! i)"
    unfolding bounds_after_full using bounds_after_le[of "Suc jg" "length ?order" P m] jg
    unfolding bounds_le_def by simp
  finally show ?thesis unfolding final_g .
qed


section \<open>The types of a function body\<close>

(* The types whose sizes the generated code of a term computes: the type of
   every subterm (temporaries), the type arguments of calls and constructors.
   core_term_type gives the type of each subterm; the environment is
   extended at a Let exactly as core_term_type extends it. None if a subterm
   does not typecheck (impossible for a well-typed body). *)

definition let_env :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> CoreType \<Rightarrow> CoreTyEnv" where
  "let_env env var rhsTy =
    env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
          TE_GhostLocals := fminus (TE_GhostLocals env) {|var|},
          TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"

fun term_types :: "CoreTyEnv \<Rightarrow> CoreTerm \<Rightarrow> CoreType list option" where
  "term_types env tm =
    (case core_term_type env NotGhost tm of
       None \<Rightarrow> None
     | Some ty \<Rightarrow>
         map_option ((#) ty)
           (case tm of
              CoreTm_LitArray _ tms \<Rightarrow> map_option concat (those (map (term_types env) tms))
            | CoreTm_Cast _ t \<Rightarrow> term_types env t
            | CoreTm_Unop _ t \<Rightarrow> term_types env t
            | CoreTm_Binop _ t1 t2 \<Rightarrow>
                (case (term_types env t1, term_types env t2) of
                   (Some l1, Some l2) \<Rightarrow> Some (l1 @ l2) | _ \<Rightarrow> None)
            | CoreTm_Let x t1 t2 \<Rightarrow>
                (case core_term_type env NotGhost t1 of
                   None \<Rightarrow> None
                 | Some rhsTy \<Rightarrow>
                     (case (term_types env t1, term_types (let_env env x rhsTy) t2) of
                        (Some l1, Some l2) \<Rightarrow> Some (l1 @ l2) | _ \<Rightarrow> None))
            | CoreTm_FunctionCall _ tys args \<Rightarrow>
                map_option (\<lambda>ls. tys @ concat ls) (those (map (term_types env) args))
            | CoreTm_VariantCtor _ tys t \<Rightarrow> map_option (\<lambda>l. tys @ l) (term_types env t)
            | CoreTm_Record flds \<Rightarrow> map_option concat (those (map (term_types env \<circ> snd) flds))
            | CoreTm_RecordProj t _ \<Rightarrow> term_types env t
            | CoreTm_VariantProj t _ \<Rightarrow> term_types env t
            | CoreTm_ArrayProj t idxs \<Rightarrow>
                (case (term_types env t, those (map (term_types env) idxs)) of
                   (Some l, Some ls) \<Rightarrow> Some (l @ concat ls) | _ \<Rightarrow> None)
            | CoreTm_Match s arms \<Rightarrow>
                (case (term_types env s, those (map (term_types env \<circ> snd) arms)) of
                   (Some l, Some ls) \<Rightarrow> Some (l @ concat ls) | _ \<Rightarrow> None)
            | CoreTm_Sizeof t \<Rightarrow> term_types env t
            | _ \<Rightarrow> Some []))"

(* The same for statements: the declared types, the cast types, the type
   arguments and instantiated return types of the statement-level calls, and
   the types of all terms; the environment is threaded by
   core_statement_type. *)
fun stmt_types :: "CoreTyEnv \<Rightarrow> CoreStatement \<Rightarrow> CoreType list option"
and stmts_types :: "CoreTyEnv \<Rightarrow> CoreStatement list \<Rightarrow> CoreType list option" where
  "stmt_types env (CoreStmt_VarDecl _ _ _ ty tm) = map_option ((#) ty) (term_types env tm)"
| "stmt_types env (CoreStmt_VarDeclCall _ _ ty castOpt f tys args) =
    (case core_impure_call_type env NotGhost f tys args of
       None \<Rightarrow> None
     | Some retTy \<Rightarrow>
         map_option (\<lambda>ls. ty # retTy # (case castOpt of None \<Rightarrow> [] | Some t \<Rightarrow> [t]) @ tys @ concat ls)
                    (those (map (term_types env) args)))"
| "stmt_types env (CoreStmt_Assign _ ty lhs rhs) =
    (case (term_types env lhs, term_types env rhs) of
       (Some l1, Some l2) \<Rightarrow> Some (ty # l1 @ l2) | _ \<Rightarrow> None)"
| "stmt_types env (CoreStmt_AssignCall _ lhs castOpt f tys args) =
    (case core_impure_call_type env NotGhost f tys args of
       None \<Rightarrow> None
     | Some retTy \<Rightarrow>
         (case (term_types env lhs, those (map (term_types env) args)) of
            (Some l, Some ls) \<Rightarrow>
              Some (retTy # (case castOpt of None \<Rightarrow> [] | Some t \<Rightarrow> [t]) @ tys @ l @ concat ls)
          | _ \<Rightarrow> None))"
| "stmt_types env (CoreStmt_Swap _ lhs rhs) =
    (case (term_types env lhs, term_types env rhs) of
       (Some l1, Some l2) \<Rightarrow> Some (l1 @ l2) | _ \<Rightarrow> None)"
| "stmt_types env (CoreStmt_Return tm) = term_types env tm"
| "stmt_types env (CoreStmt_While _ cond _ _ body) =
    (case (term_types env cond, stmts_types (env \<lparr> TE_ProofTopLevel := False \<rparr>) body) of
       (Some l1, Some l2) \<Rightarrow> Some (l1 @ l2) | _ \<Rightarrow> None)"
| "stmt_types env (CoreStmt_Match _ scrut arms) =
    (case (term_types env scrut,
           those (map (stmts_types (env \<lparr> TE_ProofTopLevel := False \<rparr>) \<circ> snd) arms)) of
       (Some l, Some ls) \<Rightarrow> Some (l @ concat ls) | _ \<Rightarrow> None)"
| "stmt_types env (CoreStmt_Block body) = stmts_types env body"
| "stmt_types env _ = None"  \<comment> \<open>ghost statements: not in a ghost-free module\<close>
| "stmts_types env [] = Some []"
| "stmts_types env (s # ss) =
    (case stmt_types env s of
       None \<Rightarrow> None
     | Some l \<Rightarrow>
         (case core_statement_type env NotGhost s of
            None \<Rightarrow> None
          | Some env' \<Rightarrow> map_option ((@) l) (stmts_types env' ss)))"

(* All the types the generated code of a function computes sizes of: its
   parameter and return types, and the types of its body. None for an
   unknown function, or if the body does not typecheck. *)
definition fun_types :: "CoreModule \<Rightarrow> string \<Rightarrow> CoreType list option" where
  "fun_types m f =
    (case (fmlookup (CM_Functions m) f, fmlookup (TE_Functions (CM_TyEnv m)) f) of
       (Some cf, Some info) \<Rightarrow>
         (let sigTys = map fst (FI_TmArgs info) @ [FI_ReturnType info]
          in case CF_Body cf of
               None \<Rightarrow> Some sigTys
             | Some body \<Rightarrow>
                 map_option ((@) sigTys)
                   (stmts_types (module_body_env_for (CM_TyEnv m) (CF_Args cf) info) body))
     | _ \<Rightarrow> None)"

(* The types of the globals. *)
definition global_types :: "CoreModule \<Rightarrow> (string \<times> CoreType) list" where
  "global_types m = sorted_list_of_fmap (TE_GlobalVars (CM_TyEnv m))"


section \<open>The check\<close>

datatype SizeError =
    SE_DatatypeCycle "string list"       \<comment> \<open>datatypes that depend on each other\<close>
  | SE_TooManyCtors string               \<comment> \<open>a datatype with more than 2^32 constructors\<close>
  | SE_CallCycle "string list"           \<comment> \<open>functions that call each other (empty: a callee is unknown)\<close>
  | SE_BodyNotTyped string               \<comment> \<open>a function whose body does not typecheck\<close>
  | SE_SizeTooLarge string CoreType "(string \<times> nat) list"
      \<comment> \<open>function, type, and the bounds of the type parameters at which its size exceeds 2^64 - 1\<close>
  | SE_GlobalTooLarge string CoreType   \<comment> \<open>global and its type, whose size exceeds 2^64 - 1\<close>

(* The bound of a function as an assignment. *)
definition fun_bound :: "nat \<Rightarrow> CoreModule \<Rightarrow> string \<Rightarrow> string \<Rightarrow> nat" where
  "fun_bound P m f = bval (compute_bounds P m) f"

definition fun_bound_list :: "nat \<Rightarrow> CoreModule \<Rightarrow> string \<Rightarrow> (string \<times> nat) list" where
  "fun_bound_list P m f = sorted_list_of_fmap (bfun (compute_bounds P m) f)"

(* The first type of a list that does not fit, if any. *)
definition find_unfit :: "CoreTyEnv \<Rightarrow> nat \<Rightarrow> (string \<Rightarrow> nat) \<Rightarrow> CoreType list \<Rightarrow> CoreType option" where
  "find_unfit env P sz tys = find (\<lambda>ty. \<not> size_fits env P sz ty) tys"

definition check_fun_sizes :: "nat \<Rightarrow> CoreModule \<Rightarrow> string \<Rightarrow> SizeError option" where
  "check_fun_sizes P m f =
    (case fun_types m f of
       None \<Rightarrow> Some (SE_BodyNotTyped f)
     | Some tys \<Rightarrow>
         (case find_unfit (CM_TyEnv m) P (fun_bound P m f) tys of
            Some ty \<Rightarrow> Some (SE_SizeTooLarge f ty (fun_bound_list P m f))
          | None \<Rightarrow> None))"

definition check_global_sizes :: "nat \<Rightarrow> CoreModule \<Rightarrow> SizeError option" where
  "check_global_sizes P m =
    (case find (\<lambda>(g, ty). \<not> size_fits (CM_TyEnv m) P (\<lambda>_. 0) ty) (global_types m) of
       Some (g, ty) \<Rightarrow> Some (SE_GlobalTooLarge g ty)
     | None \<Rightarrow> None)"

(* The first error of a list of checks. *)
fun first_error :: "SizeError option list \<Rightarrow> SizeError option" where
  "first_error [] = None"
| "first_error (None # rest) = first_error rest"
| "first_error (Some e # _) = Some e"

definition sizeable_check :: "nat \<Rightarrow> CoreModule \<Rightarrow> SizeError option" where
  "sizeable_check P m =
    (case datatype_cycle (CM_TyEnv m) of
       Some cyc \<Rightarrow> Some (SE_DatatypeCycle cyc)
     | None \<Rightarrow>
         (case find (\<lambda>d. \<not> dt_tags_fit (CM_TyEnv m) d) (dt_known (CM_TyEnv m)) of
            Some d \<Rightarrow> Some (SE_TooManyCtors d)
          | None \<Rightarrow>
              (case call_cycle m of
                 Some cyc \<Rightarrow> Some (SE_CallCycle cyc)
               | None \<Rightarrow>
                   first_error (check_global_sizes P m # map (check_fun_sizes P m) (module_fun_names m)))))"

definition core_module_sizeable :: "nat \<Rightarrow> CoreModule \<Rightarrow> bool" where
  "core_module_sizeable P m = (sizeable_check P m = None)"


section \<open>Soundness\<close>

lemma first_error_None: "first_error es = None \<Longrightarrow> e \<in> set es \<Longrightarrow> e = None"
  by (induction es rule: first_error.induct) auto

lemma sizeable_parts:
  assumes "core_module_sizeable P m"
  shows "datatypes_acyclic (CM_TyEnv m)"
    and "\<And>d. fmlookup (TE_DataCtorsByType (CM_TyEnv m)) d \<noteq> None \<Longrightarrow> dt_tags_fit (CM_TyEnv m) d"
    and "call_cycle m = None"
    and "check_global_sizes P m = None"
    and "\<And>f. fmlookup (CM_Functions m) f \<noteq> None \<Longrightarrow> check_fun_sizes P m f = None"
proof -
  from assms have chk: "sizeable_check P m = None" by (simp add: core_module_sizeable_def)
  show "datatypes_acyclic (CM_TyEnv m)"
    using chk by (simp add: sizeable_check_def datatypes_acyclic_def split: option.splits)
  have "find (\<lambda>d. \<not> dt_tags_fit (CM_TyEnv m) d) (dt_known (CM_TyEnv m)) = None"
    using chk by (simp add: sizeable_check_def split: option.splits)
  thus "\<And>d. fmlookup (TE_DataCtorsByType (CM_TyEnv m)) d \<noteq> None \<Longrightarrow> dt_tags_fit (CM_TyEnv m) d"
    unfolding find_None_iff using dt_known_iff by blast
  show "call_cycle m = None"
    using chk by (simp add: sizeable_check_def split: option.splits)
  have fe: "first_error (check_global_sizes P m # map (check_fun_sizes P m) (module_fun_names m)) = None"
    using chk by (simp add: sizeable_check_def split: option.splits)
  show "check_global_sizes P m = None" using first_error_None[OF fe] by simp
  show "\<And>f. fmlookup (CM_Functions m) f \<noteq> None \<Longrightarrow> check_fun_sizes P m f = None"
    using first_error_None[OF fe] set_module_fun_names by (auto simp: fmlookup_dom_iff)
qed

(* (d) *)
theorem sizeable_acyclic: "core_module_sizeable P m \<Longrightarrow> datatypes_acyclic (CM_TyEnv m)"
  by (rule sizeable_parts(1))

theorem sizeable_tags_fit:
  "core_module_sizeable P m \<Longrightarrow> fmlookup (TE_DataCtorsByType (CM_TyEnv m)) d \<noteq> None
   \<Longrightarrow> dt_tags_fit (CM_TyEnv m) d"
  by (rule sizeable_parts(2))

(* (b): every checked type of a function fits at every assignment bounded by
   the function's bound, and at every pointer size at most P. *)
theorem sizeable_fun_type_fits:
  assumes "core_module_sizeable P m"
    and "fmlookup (CM_Functions m) f \<noteq> None"
    and "fun_types m f = Some tys" and "ty \<in> set tys"
    and "\<And>v. sz v \<le> fun_bound P m f v" and "P' \<le> P"
  shows "size_fits (CM_TyEnv m) P' sz ty"
proof -
  have "check_fun_sizes P m f = None" by (rule sizeable_parts(5)[OF assms(1,2)])
  hence "size_fits (CM_TyEnv m) P (fun_bound P m f) ty"
    using assms(3,4) by (auto simp: check_fun_sizes_def find_unfit_def find_None_iff split: option.splits)
  thus ?thesis by (rule size_fits_anti_mono[OF assms(5,6)])
qed

(* (c): every global's type fits (at the zero assignment; globals have closed
   types, for which the assignment is irrelevant: size_fits_cong_sz). *)
theorem sizeable_global_fits:
  assumes "core_module_sizeable P m"
    and "fmlookup (TE_GlobalVars (CM_TyEnv m)) g = Some ty" and "P' \<le> P"
  shows "size_fits (CM_TyEnv m) P' (\<lambda>_. 0) ty"
proof -
  have "check_global_sizes P m = None" by (rule sizeable_parts(4)[OF assms(1)])
  moreover have "(g, ty) \<in> set (global_types m)"
    using assms(2) by (simp add: global_types_def sorted_list_of_fmap_def fmlookup_dom_iff image_iff)
  ultimately have fits: "size_fits (CM_TyEnv m) P (\<lambda>_. 0) ty"
    by (auto simp: check_global_sizes_def find_None_iff split: option.splits)
  show ?thesis by (rule size_fits_anti_mono[OF _ assms(3) fits]) simp
qed

(* (a): at every call site f<tys> in g, the size of each type argument at
   any assignment bounded by g's bound is at most f's bound for the
   corresponding type parameter, at any pointer size at most P. *)
theorem sizeable_call_bound:
  assumes "core_module_sizeable P m"
    and "(f, tys) \<in> set (fun_calls m g)"
    and "fmlookup (TE_Functions (CM_TyEnv m)) f = Some info" and "distinct (FI_TyArgs info)"
    and "i < length (FI_TyArgs info)" and "i < length tys"
    and "\<And>v. sz v \<le> fun_bound P m g v" and "P' \<le> P"
  shows "type_size (CM_TyEnv m) P' sz (tys ! i) \<le> fun_bound P m f (FI_TyArgs info ! i)"
proof -
  have "type_size (CM_TyEnv m) P' sz (tys ! i) \<le> type_size (CM_TyEnv m) P (fun_bound P m g) (tys ! i)"
    by (rule type_size_mono[OF assms(7,8)])
  also have "\<dots> \<le> fun_bound P m f (FI_TyArgs info ! i)"
    unfolding fun_bound_def by (rule compute_bounds_call[OF sizeable_parts(3)[OF assms(1)] assms(2-6)])
  finally show ?thesis .
qed

(* The call sites of a function are those of its body. *)
lemma fun_calls_body:
  "fmlookup (CM_Functions m) f = Some cf \<Longrightarrow> CF_Body cf = Some body \<Longrightarrow> fun_calls m f = stmts_calls body"
  by (simp add: fun_calls_def)

end
