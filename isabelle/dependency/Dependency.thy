theory Dependency
  imports Main "HOL-Library.Char_ord" "HOL-Library.List_Lexorder" "HOL-Library.FSet" "HOL-Library.Finite_Map" "HOL-Library.Multiset" "KosarajuMain"
begin

(*-----------------------------------------------------------------------------*)
(* Dependency error type *)
(*-----------------------------------------------------------------------------*)

datatype DependencyError =
  DepErr_DuplicateName string
  | DepErr_DependencyNotFound string string  (* depender name, dependee name *)


(*-----------------------------------------------------------------------------*)
(* Mapping names to items *)
(*-----------------------------------------------------------------------------*)

(* Build a map from name to item *)
fun build_item_map :: "('a \<Rightarrow> string) \<Rightarrow> 'a list \<Rightarrow> (string, 'a) fmap"
  where
"build_item_map getName items =
  fmap_of_list (map (\<lambda>item. (getName item, item)) items)"

(* The domain of build_item_map is exactly the set of item names *)
lemma build_item_map_dom:
  "fset (fmdom (build_item_map getName items)) = set (map getName items)"
proof (intro subset_antisym subsetI)
  fix x
  assume "x \<in> fset (fmdom (build_item_map getName items))"
  then have "x |\<in>| fmdom (build_item_map getName items)" by simp
  then have "fmlookup (build_item_map getName items) x \<noteq> None"
    by (meson fmdom_notI)
  then have "fmlookup (fmap_of_list (map (\<lambda>i. (getName i, i)) items)) x \<noteq> None"
    by simp
  then have "x \<in> set (map fst (map (\<lambda>i. (getName i, i)) items))"
    using \<open>x |\<in>| fmdom (build_item_map getName items)\<close> fset_of_list_elem by fastforce
  then show "x \<in> set (map getName items)"
    by simp
next
  fix x
  assume "x \<in> set (map getName items)"
  then obtain item where "item \<in> set items" "getName item = x"
    by auto
  then have "(x, item) \<in> set (map (\<lambda>i. (getName i, i)) items)"
    by auto
  then have "x \<in> fst ` set (map (\<lambda>i. (getName i, i)) items)"
    by force
  then have "fmlookup (fmap_of_list (map (\<lambda>i. (getName i, i)) items)) x \<noteq> None"
    by (simp add: fmlookup_of_list map_of_eq_None_iff)
  then have "x |\<in>| fmdom (build_item_map getName items)"
    by (metis build_item_map.simps fmdom_notD)
  then show "x \<in> fset (fmdom (build_item_map getName items))"
    by simp
qed

(* Use the name-to-item map to map SCCs from item names back to items *)
fun map_sccs_to_items :: "(string, 'a) fmap \<Rightarrow> string list list \<Rightarrow> 'a list list"
  where
"map_sccs_to_items item_map sccs =
  map (\<lambda>scc. map (\<lambda>name. the (fmlookup item_map name)) scc) sccs"


(*-----------------------------------------------------------------------------*)
(* Checking for duplicate item names *)
(*-----------------------------------------------------------------------------*)

(* Check for adjacent duplicates in a sorted list *)
fun check_adjacent_dups :: "string list \<Rightarrow> DependencyError option"
  where
"check_adjacent_dups [] = None" |
"check_adjacent_dups [x] = None" |
"check_adjacent_dups (x # y # rest) =
  (if x = y then Some (DepErr_DuplicateName x)
   else check_adjacent_dups (y # rest))"

(* If check_adjacent_dups returns None on a sorted list, it's distinct *)
lemma check_adjacent_dups_None_implies_distinct:
  assumes "check_adjacent_dups xs = None"
    and "sorted xs"
  shows "distinct xs"
  using assms
proof (induction xs)
  case Nil
  then show ?case
    by simp 
next
  case (Cons a xs)
  then show ?case proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case Cons2: (Cons b ys)
    then have "a \<noteq> b"
      using Cons.prems(1) by auto
    have "check_adjacent_dups (a # b # ys) = check_adjacent_dups (b # ys)"
      by (simp add: \<open>a \<noteq> b\<close>)
    thus ?thesis
      using Cons.IH Cons.prems(1,2) Cons2 \<open>a \<noteq> b\<close> by force
  qed
qed

(* Check for duplicate names in a list (not necessarily sorted) *)
fun check_duplicate_names :: "('a \<Rightarrow> string) \<Rightarrow> 'a list \<Rightarrow> DependencyError option"
  where
"check_duplicate_names getName items =
  (let sorted_names = sort (map getName items)
   in check_adjacent_dups sorted_names)"

(* If check_duplicate_names returns no error, then names are distinct *)
lemma no_duplicate_errors_means_distinct:
  assumes "check_duplicate_names getName items = None"
  shows "distinct (map getName items)"
proof -
  define sorted_names where "sorted_names = sort (map getName items)"

  (* check_duplicate_names returns None means check_adjacent_dups returned None *)
  have "check_adjacent_dups sorted_names = None"
    using assms sorted_names_def by auto

  (* sorted_names is sorted *)
  have "sorted sorted_names"
    using sorted_names_def by simp

  (* Therefore sorted_names is distinct *)
  have "distinct sorted_names"
    using check_adjacent_dups_None_implies_distinct[OF \<open>check_adjacent_dups sorted_names = None\<close> \<open>sorted sorted_names\<close>]
    by simp

  (* distinct sorted list implies distinct original list *)
  thus ?thesis
    by (simp add: sorted_names_def)
qed


(*-----------------------------------------------------------------------------*)
(* Checking for non-existent dependencies *)
(*-----------------------------------------------------------------------------*)

(* Check if all dependencies of one item exist *)
fun check_item_deps :: "string \<Rightarrow> string list \<Rightarrow> (string, 'a) fmap \<Rightarrow> DependencyError option"
  where
"check_item_deps item_name [] item_map = None" |
"check_item_deps item_name (dep # rest) item_map =
  (if fmlookup item_map dep = None
   then Some (DepErr_DependencyNotFound item_name dep)
   else check_item_deps item_name rest item_map)"

(* If check_item_deps returns None, all dependencies exist *)
lemma check_item_deps_None_means_all_exist:
  assumes "check_item_deps item_name deps item_map = None"
  shows "\<forall>dep \<in> set deps. fmlookup item_map dep \<noteq> None"
  using assms
proof (induction deps)
  case Nil
  then show ?case by simp
next
  case (Cons dep rest)
  from Cons.prems have "fmlookup item_map dep \<noteq> None"
    by (simp split: if_splits)
  moreover from Cons.prems \<open>fmlookup item_map dep \<noteq> None\<close>
    have "check_item_deps item_name rest item_map = None"
    by simp
  then have "\<forall>d \<in> set rest. fmlookup item_map d \<noteq> None"
    using Cons.IH by simp
  ultimately show ?case by simp
qed

(* Check that all dependencies reference existing items *)
fun check_deps_exist :: "('a \<Rightarrow> string) \<Rightarrow> ('a \<Rightarrow> string list) \<Rightarrow> 'a list \<Rightarrow> (string, 'a) fmap
                          \<Rightarrow> DependencyError option"
  where
"check_deps_exist getName getDeps [] item_map = None" |
"check_deps_exist getName getDeps (item # rest) item_map =
  (case check_item_deps (getName item) (getDeps item) item_map of
     Some err \<Rightarrow> Some err
   | None \<Rightarrow> check_deps_exist getName getDeps rest item_map)"

(* If check_deps_exist returns None, all dependencies of all items exist *)
lemma check_deps_exist_None_means_all_exist:
  assumes "check_deps_exist getName getDeps items item_map = None"
  shows "\<forall>item \<in> set items. \<forall>dep \<in> set (getDeps item). fmlookup item_map dep \<noteq> None"
  using assms
proof (induction items)
  case Nil
  then show ?case by simp
next
  case (Cons item rest)
  from Cons.prems have item_deps_ok: "check_item_deps (getName item) (getDeps item) item_map = None"
    by (auto split: option.splits)
  from Cons.prems item_deps_ok have rest_ok: "check_deps_exist getName getDeps rest item_map = None"
    by (auto split: option.splits)
  from item_deps_ok have "\<forall>dep \<in> set (getDeps item). fmlookup item_map dep \<noteq> None"
    using check_item_deps_None_means_all_exist by simp
  moreover from rest_ok have "\<forall>i \<in> set rest. \<forall>dep \<in> set (getDeps i). fmlookup item_map dep \<noteq> None"
    using Cons.IH by simp
  ultimately show ?case by simp
qed


(*-----------------------------------------------------------------------------*)
(* Building the dependency graph *)
(*-----------------------------------------------------------------------------*)

(* Helper type for dependency graph representation *)
type_synonym DependencyGraph = "(string, string list) fmap"

(* Build dependency graph as finite map from list of items *)
fun build_dep_graph :: "('a \<Rightarrow> string) \<Rightarrow> ('a \<Rightarrow> string list) \<Rightarrow> 'a list \<Rightarrow> DependencyGraph"
  where
"build_dep_graph getName getDeps items =
  fmap_of_list (map (\<lambda>item. (getName item, getDeps item)) items)"

(* The domain of build_dep_graph is exactly the item names *)
lemma build_dep_graph_dom:
  "fset (fmdom (build_dep_graph getName getDeps items)) = set (map getName items)"
proof (intro subset_antisym subsetI)
  fix x
  assume "x \<in> fset (fmdom (build_dep_graph getName getDeps items))"
  then have "x |\<in>| fmdom (build_dep_graph getName getDeps items)" by simp
  then have "fmlookup (build_dep_graph getName getDeps items) x \<noteq> None"
    by (meson fmdom_notI)
  then obtain deps where "fmlookup (build_dep_graph getName getDeps items) x = Some deps"
    by auto
  then have "fmlookup (fmap_of_list (map (\<lambda>item. (getName item, getDeps item)) items)) x = Some deps"
    by simp
  then have "x \<in> set (map fst (map (\<lambda>item. (getName item, getDeps item)) items))"
    by (metis (lifting) domI fmdom.rep_eq fmdom_fmap_of_list fset_of_list.rep_eq)
  then show "x \<in> set (map getName items)"
    by simp
next
  fix x
  assume "x \<in> set (map getName items)"
  then obtain item where "item \<in> set items" and "x = getName item"
    by auto
  then have "(x, getDeps item) \<in> set (map (\<lambda>i. (getName i, getDeps i)) items)"
    by auto
  then have "x \<in> fst ` set (map (\<lambda>i. (getName i, getDeps i)) items)"
    by force
  then have "fmlookup (fmap_of_list (map (\<lambda>i. (getName i, getDeps i)) items)) x \<noteq> None"
    by (simp add: fmlookup_of_list map_of_eq_None_iff)
  then have "x |\<in>| fmdom (build_dep_graph getName getDeps items)"
    by (metis build_dep_graph.elims fmdom_notD)
  then show "x \<in> fset (fmdom (build_dep_graph getName getDeps items))"
    by simp
qed

(* When there are no dependency errors, the graph is valid *)
lemma no_dep_errors_means_valid_graph:
  assumes "check_duplicate_names getName items = None"
    and "check_deps_exist getName getDeps items (build_item_map getName items) = None"
  shows "valid_graph (build_dep_graph getName getDeps items)"
  unfolding valid_graph.simps
proof (intro allI impI)
  fix v w
  assume v_vertex: "has_vertex (build_dep_graph getName getDeps items) v"
  assume edge_vw: "has_edge (build_dep_graph getName getDeps items) v w"

  (* v is in the graph, so v is an item name *)
  have "v \<in> fset (fmdom (build_dep_graph getName getDeps items))"
    using v_vertex by simp
  then have "v \<in> set (map getName items)"
    using build_dep_graph_dom
    by blast 
  then obtain item where item_props: "item \<in> set items" "getName item = v"
    by auto

  (* There's an edge from v to w, so w is in v's dependency list *)
  have "fmlookup (build_dep_graph getName getDeps items) v \<noteq> None"
    by (metis \<open>v |\<in>| fmdom (build_dep_graph getName getDeps items)\<close> fmdom_notI)
  then obtain deps where deps_def: "fmlookup (build_dep_graph getName getDeps items) v = Some deps"
    by auto

  have "has_edge (build_dep_graph getName getDeps items) v w"
    using edge_vw .
  then have "List.member deps w"
    using deps_def by (auto split: option.splits)

  (* deps is the list of dependencies for item v *)
  have "deps = getDeps item"
  proof -
    have pair_in: "(v, getDeps item) \<in> set (map (\<lambda>i. (getName i, getDeps i)) items)"
      using item_props by auto

    have "fmlookup (build_dep_graph getName getDeps items) v =
          fmlookup (fmap_of_list (map (\<lambda>i. (getName i, getDeps i)) items)) v"
      by simp

    also have "... = Some (getDeps item)"
    proof -
      have "map fst (map (\<lambda>i. (getName i, getDeps i)) items) = map getName items"
        by simp
      then have "distinct (map fst (map (\<lambda>i. (getName i, getDeps i)) items))"
        using assms(1)
        by (metis no_duplicate_errors_means_distinct) 
      then show ?thesis
        by (metis (lifting) fmap_of_list.rep_eq graph_map_of_if_distinct_dom in_graphD pair_in)
    qed

    finally show ?thesis using deps_def by simp
  qed

  (* So w is in getDeps item *)
  have "List.member (getDeps item) w"
    using \<open>List.member deps w\<close> \<open>deps = getDeps item\<close> by simp

  have "w \<in> set (getDeps item)"
    by (metis \<open>List.member (getDeps item) w\<close> in_set_member)

  (* Since check_deps_exist returned None, all dependencies must exist in item_map *)
  have "fmlookup (build_item_map getName items) w \<noteq> None"
  proof -
    (* From assms(2), check_deps_exist returned None *)
    have "check_deps_exist getName getDeps items (build_item_map getName items) = None"
      using assms(2) by simp

    (* By our helper lemma, this means all dependencies of all items exist *)
    then have "\<forall>item \<in> set items. \<forall>dep \<in> set (getDeps item).
                fmlookup (build_item_map getName items) dep \<noteq> None"
      using check_deps_exist_None_means_all_exist by blast

    (* Since item \<in> set items and w \<in> set (getDeps item), we get the result *)
    thus ?thesis
      using item_props(1) \<open>w \<in> set (getDeps item)\<close> by blast
  qed

  (* If w is in the item_map, then w is an item name *)
  then have "w |\<in>| fmdom (build_item_map getName items)"
    by (meson fmdom_notD)

  (* The domain of build_item_map is the same as build_dep_graph *)
  have "fmdom (build_item_map getName items) = fmdom (build_dep_graph getName getDeps items)"
    using build_item_map_dom build_dep_graph_dom
    by blast

  then have "w |\<in>| fmdom (build_dep_graph getName getDeps items)"
    using \<open>w |\<in>| fmdom (build_item_map getName items)\<close> by simp

  then show "has_vertex (build_dep_graph getName getDeps items) w"
    by simp
qed


(*-----------------------------------------------------------------------------*)
(* Dependency analysis main entry point *)
(*-----------------------------------------------------------------------------*)

(* Main dependency analysis function *)
(* This sorts items into strongly connected components in topological order.
   Each SCC is a list of items. If an SCC contains multiple items, they form a cycle.
   The SCCs are ordered such that dependencies appear before dependants.
   If there are any errors (duplicate names or missing dependencies) then a DependencyError 
   is returned instead (currently only a max of one error is returned).
*)
fun analyze_dependencies_generic ::
  "'a list \<Rightarrow> ('a \<Rightarrow> string) \<Rightarrow> ('a \<Rightarrow> string list) \<Rightarrow> (DependencyError, 'a list list) sum"
  where
"analyze_dependencies_generic items getName getDeps = (
  case check_duplicate_names getName items of
    Some err \<Rightarrow> Inl err
  | None \<Rightarrow> (
      let item_map = build_item_map getName items
      in case check_deps_exist getName getDeps items item_map of
        Some err \<Rightarrow> Inl err
      | None \<Rightarrow> (
          let graph = build_dep_graph getName getDeps items;
              sccs = kosaraju graph
          in
            Inr (map_sccs_to_items item_map (rev sccs))
        )
    )
)"


(*-----------------------------------------------------------------------------*)
(* Permutation property *)
(*-----------------------------------------------------------------------------*)

(* analyze_dependencies_generic always returns a permutation of the input *)
theorem analyze_dependencies_generic_permutation:
  assumes "analyze_dependencies_generic items getName getDeps = Inr sccs"
  shows "mset (concat sccs) = mset items"
proof -
  define graph where "graph = build_dep_graph getName getDeps items"
  define kos where "kos = kosaraju graph"
  define itemMap where "itemMap = build_item_map getName items"
  define sortedNames where "sortedNames = concat (rev kos)"
  define sortedItems where "sortedItems = map (\<lambda>name. the (fmlookup itemMap name)) sortedNames"

  have no_dup_errors: "check_duplicate_names getName items = None"
  proof (cases "check_duplicate_names getName items")
    case None
    then show ?thesis by simp
  next
    case (Some err)
    then have "analyze_dependencies_generic items getName getDeps = Inl err"
      by simp
    thus ?thesis using assms by auto
  qed

  have deps_exist: "check_deps_exist getName getDeps items itemMap = None"
  proof (cases "check_deps_exist getName getDeps items itemMap")
    case None
    then show ?thesis by simp
  next
    case (Some err)
    then have "analyze_dependencies_generic items getName getDeps = Inl err"
      using itemMap_def no_dup_errors
      by simp
    thus ?thesis using assms by auto
  qed

  (* Since check_duplicate_names returned None, the names must be distinct *)
  have names_distinct: "distinct (map getName items)"
    using no_dup_errors no_duplicate_errors_means_distinct by blast

  have result: "sccs = map_sccs_to_items itemMap (rev kos)"
    using assms no_dup_errors deps_exist graph_def kos_def itemMap_def
    by simp

  (* graph is valid *)
  have graph_valid: "valid_graph graph"
    using names_distinct deps_exist graph_def itemMap_def no_dep_errors_means_valid_graph
    using no_dup_errors by blast

  (* sortedNames contains only names from the graph *)
  have names_in_graph: "set sortedNames \<subseteq> fset (fmdom graph)"
  proof
    fix name
    assume "name \<in> set sortedNames"
    then have "name \<in> set (concat (rev kos))"
      unfolding sortedNames_def by simp
    then have "name \<in> set (concat kos)"
      by simp
    then obtain scc where "scc \<in> set kos" "name \<in> set scc"
      by auto
    then obtain v where "v \<in> set scc \<and> in_same_scc graph name v"
      using graph_valid kosaraju_sound kos_def by blast
    then have "has_vertex graph name"
      using graph_valid in_same_scc.simps reachable_implies_vertices(1) by blast
    thus "name \<in> fset (fmdom graph)"
      by simp
  qed

  (* sortedNames contains all names from the graph *)
  have all_names_present: "fset (fmdom (build_dep_graph getName getDeps items)) \<subseteq> set sortedNames"
  proof
    fix name
    assume "name \<in> fset (fmdom (build_dep_graph getName getDeps items))"
    then have "has_vertex graph name"
      by (simp add: graph_def)
    then obtain scc where "scc \<in> set kos" "name \<in> set scc"
      using graph_valid kosaraju_complete kos_def by blast
    then have "name \<in> set (concat kos)"
      by auto
    then show "name \<in> set sortedNames"
      using sortedNames_def by simp
  qed

  (* sortedNames is distinct *)
  have sorted_names_distinct: "distinct sortedNames"
  proof -
    have "distinct (map set kos)"
      using graph_valid kosaraju_distinct_list kos_def by blast
    hence "distinct kos"
      by (simp add: distinct_map)
    moreover have "\<forall> scc \<in> set kos. distinct scc"
      using graph_valid kosaraju_distinct kos_def by blast
    moreover have "\<forall>scc1 scc2. scc1 \<in> set kos \<and> scc2 \<in> set kos \<and> scc1 \<noteq> scc2 \<longrightarrow>
       set scc1 \<inter> set scc2 = {}"
    proof (intro allI impI)
      fix scc1 scc2
      assume hyp: "scc1 \<in> set kos \<and> scc2 \<in> set kos \<and> scc1 \<noteq> scc2"
      obtain v1 where v1_def: "v1 \<in> set scc1 \<and> (\<forall>w. w \<in> set scc1 \<longleftrightarrow> has_vertex graph w \<and> in_same_scc graph w v1)"
        using kosaraju_sound hyp kos_def graph_valid by blast
      hence set1_def: "set scc1 = {w. has_vertex graph w \<and> in_same_scc graph w v1}"
        by auto
      obtain v2 where v2_def: "v2 \<in> set scc2 \<and> (\<forall>w. w \<in> set scc2 \<longleftrightarrow> has_vertex graph w \<and> in_same_scc graph w v2)"
        using kosaraju_sound hyp kos_def graph_valid by blast
      hence set2_def: "set scc2 = {w. has_vertex graph w \<and> in_same_scc graph w v2}"
        by auto
      show "set scc1 \<inter> set scc2 = {}"
      proof (cases "set scc1 = set scc2")
        case True
        then have "scc1 = scc2"
        proof -
          have "distinct (map set kos)"
            using graph_valid kosaraju_distinct_list kos_def by blast
          then have "inj_on set (set kos)"
            by (simp add: distinct_map)
          moreover have "scc1 \<in> set kos" "scc2 \<in> set kos"
            using hyp by auto
          ultimately show ?thesis
            using True by (meson inj_onD)
        qed
        thus ?thesis using hyp by simp
      next
        case False
        then show ?thesis using scc_disjoint_or_equal
          using graph_valid set1_def set2_def v1_def v2_def by blast
      qed
    qed
    ultimately have "distinct (concat kos)" using distinct_concat by blast
    thus ?thesis
      by (simp add: \<open>distinct kos\<close> distinct_concat_iff distinct_removeAll sortedNames_def)
  qed

  (* The item map correctly looks up the unique item with the given name *)
  have item_map_correct: "\<forall>name \<in> set sortedNames.
      fmlookup itemMap name
      = Some (THE item. item \<in> set items \<and> getName item = name)"
  proof (intro ballI)
    fix name
    assume "name \<in> set sortedNames"

    (* Since name is in sortedNames, it's in the dependency graph domain *)
    have "name \<in> fset (fmdom graph)"
      using \<open>name \<in> set sortedNames\<close> names_in_graph by auto

    (* By build_dep_graph_dom, this means name is an item name *)
    then have "name \<in> set (map getName items)"
      using build_dep_graph_dom graph_def by blast

    (* So there exists an item with this name *)
    then obtain item where "item \<in> set items" and "getName item = name"
      by auto

    (* Since item names are distinct, this item is unique *)
    have unique: "\<forall>i \<in> set items. getName i = name \<longrightarrow> i = item"
      using names_distinct \<open>item \<in> set items\<close> \<open>getName item = name\<close>
      by (metis Diff_insert_absorb Set.set_insert distinct_map inj_on_image_mem_iff insertE
                set_remove1_eq set_remove1_subset)

    (* Therefore THE gives us the unique item *)
    have the_eq: "(THE i. i \<in> set items \<and> getName i = name) = item"
      using \<open>item \<in> set items\<close> \<open>getName item = name\<close> unique
      by blast

    (* Now show that fmlookup itemMap name = Some item *)
    have "fmlookup itemMap name =
          fmlookup (fmap_of_list (map (\<lambda>i. (getName i, i)) items)) name"
      unfolding itemMap_def by simp

    also have "... = Some item"
    proof -
      have pair_in: "(name, item) \<in> set (map (\<lambda>i. (getName i, i)) items)"
        using \<open>item \<in> set items\<close> \<open>getName item = name\<close> by auto
      have "map fst (map (\<lambda>i. (getName i, i)) items) = map getName items"
        by simp
      then have "distinct (map fst (map (\<lambda>i. (getName i, i)) items))"
        using assms(1)
        by (metis names_distinct) 
      then show ?thesis
        by (metis fmap_of_list.rep_eq map_of_eq_Some_iff pair_in)
    qed

    finally show "fmlookup itemMap name = Some (THE i. i \<in> set items \<and> getName i = name)"
      using the_eq by simp
  qed

  (* Since we map each name to its unique item, we get all items back *)
  have "mset (map (\<lambda>name. the (fmlookup itemMap name)) sortedNames)
      = mset items"
  proof -
    (* From names_in_graph and all_names_present, sortedNames is exactly the item names *)
    have names_eq: "set sortedNames = fset (fmdom (build_dep_graph getName getDeps items))"
      using names_in_graph all_names_present graph_def by auto

    (* But the domain of build_dep_graph is exactly the item names *)
    have "fset (fmdom (build_dep_graph getName getDeps items)) = set (map getName items)"
      by (rule build_dep_graph_dom)

    (* So set sortedNames equals the set of item names *)
    hence set_eq: "set sortedNames = set (map getName items)"
      using names_eq by simp

    (* But we have that all elements of sortedNames are distinct (proved above),
       and all elements of (map getName items) are distinct (names_distinct),
       so this means they are equal as multisets as well *)
    have mset_names: "mset sortedNames = mset (map getName items)"
      using set_eq names_distinct sorted_names_distinct set_eq_iff_mset_eq_distinct by blast

    (* So mapping sortedNames through itemMap gives the same multiset as items *)
    have msets_equal: "mset (map (\<lambda>name. the (fmlookup itemMap name)) sortedNames) =
          mset (map (\<lambda>name. the (fmlookup itemMap name)) (map getName items))"
      using item_map_correct mset_names multiset.map_comp by auto

    (* Also, since item names are distinct, each item is uniquely determined by its name *)
    have unique_items: "\<forall>name \<in> set (map getName items).
                          \<exists>!item. item \<in> set items \<and> getName item = name"
    proof (intro ballI)
      fix name
      assume "name \<in> set (map getName items)"
      then obtain item where "item \<in> set items" and "getName item = name"
        by auto
      moreover have "\<forall>i \<in> set items. getName i = name \<longrightarrow> i = item"
        using names_distinct \<open>item \<in> set items\<close> \<open>getName item = name\<close>
        by (metis Diff_insert_absorb Set.set_insert distinct_map inj_on_image_mem_iff insertE
            set_remove1_eq set_remove1_subset)
      ultimately show "\<exists>!item. item \<in> set items \<and> getName item = name"
        by auto
    qed

    (* Therefore, mapping names back to items is the inverse of getName *)
    have inverse: "\<forall>item \<in> set items.
                   (THE i. i \<in> set items \<and> getName i = getName item) = item"
      using names_distinct unique_items by auto

    (* Another way of putting this (using item_map_correct) is: *)
    have "\<forall>item \<in> set items. the (fmlookup itemMap (getName item)) = item"
      using item_map_correct inverse set_eq by auto

    (* Therefore we can show: *)
    hence "mset (map (\<lambda>name. the (fmlookup itemMap name)) (map getName items)) = mset items"
      by (simp add: map_idI)

    thus ?thesis using msets_equal by simp
  qed

  (* Now relate this to sccs *)
  have "concat sccs = concat (map_sccs_to_items itemMap (rev kos))"
    using result by simp
  also have "... = map (\<lambda>name. the (fmlookup itemMap name)) (concat (rev kos))"
    by (simp add: map_concat)
  also have "... = map (\<lambda>name. the (fmlookup itemMap name)) sortedNames"
    using sortedNames_def by simp
  finally have "concat sccs = map (\<lambda>name. the (fmlookup itemMap name)) sortedNames" .

  thus ?thesis
    using \<open>mset (map (\<lambda>name. the (fmlookup itemMap name)) sortedNames) = mset items\<close>
    by simp
qed


(*-----------------------------------------------------------------------------*)
(* Topological ordering property *)
(*-----------------------------------------------------------------------------*)

(* If analyze_dependencies_generic succeeds, dependencies appear before depandents.

   More precisely: if item1 depends on item2 (getName item2 \<in> set (getDeps item1)),
   then item2's SCC appears at an index <= item1's SCC index in the result list.
   (Equality occurs when they're in the same SCC, i.e., part of a dependency cycle.)

   This is the crucial property for compiler use: the SCCs are topologically ordered,
   so you can process them left-to-right and all dependencies between different SCCs
   will be satisfied. Items within the same SCC (cycles) mutually depend on each other
   and must be processed together. 

   Note: we don't actually prove that items in the same SCC really do form part of 
   a cycle; e.g. analyze_dependencies_generic could return all the items in one big
   SCC, and it would satisfy both this property and the permutation property. However,
   this property is good enough for our purposes for now.
*)
theorem analyze_dependencies_generic_topological_order:
  assumes result: "analyze_dependencies_generic items getName getDeps = Inr sccs"
    and item1_in: "item1 \<in> set items"
    and item2_in: "item2 \<in> set items"
    and item1_depends_on_item2: "getName item2 \<in> set (getDeps item1)"
  shows item2_appears_first: 
          "\<exists>i j. i \<le> j \<and>
                  i < length sccs \<and>
                  j < length sccs \<and>
                  item2 \<in> set (sccs ! i) \<and>
                  item1 \<in> set (sccs ! j)"
proof -
  define graph where "graph = build_dep_graph getName getDeps items"
  define kos where "kos = kosaraju graph"
  define itemMap where "itemMap = build_item_map getName items"

  (* Establish preconditions *)
  have no_dup_errors: "check_duplicate_names getName items = None"
  proof (cases "check_duplicate_names getName items")
    case None
    then show ?thesis by simp
  next
    case (Some err)
    then have "analyze_dependencies_generic items getName getDeps = Inl err"
      by simp
    thus ?thesis using assms(1) by auto
  qed

  have deps_exist: "check_deps_exist getName getDeps items itemMap = None"
  proof (cases "check_deps_exist getName getDeps items itemMap")
    case None
    then show ?thesis by simp
  next
    case (Some err)
    then have "analyze_dependencies_generic items getName getDeps = Inl err"
      using itemMap_def no_dup_errors
      by simp
    thus ?thesis using assms(1) by auto
  qed

  have names_distinct: "distinct (map getName items)"
    using no_dup_errors no_duplicate_errors_means_distinct by blast

  have graph_valid: "valid_graph graph"
    using names_distinct deps_exist graph_def itemMap_def no_dep_errors_means_valid_graph
    using no_dup_errors by blast

  have result: "sccs = map_sccs_to_items itemMap (rev kos)"
    using assms(1) no_dup_errors deps_exist graph_def kos_def itemMap_def
    by simp

  (* There is an edge in the graph from item1 to item2 *)
  have edge_in_graph: "has_edge graph (getName item1) (getName item2)"
  proof -
    have "fmlookup graph (getName item1) = Some (getDeps item1)"
    proof -
      have pair_in: "(getName item1, getDeps item1) \<in> set (map (\<lambda>i. (getName i, getDeps i)) items)"
        using assms(2) by auto
      have "map fst (map (\<lambda>i. (getName i, getDeps i)) items) = map getName items"
        by simp
      then have "distinct (map fst (map (\<lambda>i. (getName i, getDeps i)) items))"
        using names_distinct by metis
      then show ?thesis
        unfolding graph_def build_dep_graph.simps
        by (metis fmap_of_list.rep_eq map_of_eq_Some_iff pair_in)
    qed
    moreover have "List.member (getDeps item1) (getName item2)"
      using assms(4) by (simp add: in_set_member)
    ultimately show ?thesis
      by simp
  qed

  (* Both names are vertices in the graph *)
  have vertex1: "has_vertex graph (getName item1)"
    using item1_in build_dep_graph_dom graph_def by force
  have vertex2: "has_vertex graph (getName item2)"
    using item2_in build_dep_graph_dom graph_def by force

  (* Find the SCCs containing item1 and item2 in kos *)
  obtain scc1_name where scc1_props: "scc1_name \<in> set kos" "getName item1 \<in> set scc1_name"
    using vertex1 graph_valid kosaraju_complete kos_def by blast

  obtain scc2_name where scc2_props: "scc2_name \<in> set kos" "getName item2 \<in> set scc2_name"
    using vertex2 graph_valid kosaraju_complete kos_def by blast

  (* Find the indices in kos *)
  obtain idx1_kos where idx1_kos_def: "idx1_kos < length kos" "kos ! idx1_kos = scc1_name"
    by (metis in_set_conv_nth scc1_props(1))
  obtain idx2_kos where idx2_kos_def: "idx2_kos < length kos" "kos ! idx2_kos = scc2_name"
    by (metis in_set_conv_nth scc2_props(1))

  (* By topological ordering property *)
  have topo_ordered: "sccs_topologically_ordered graph kos"
    using graph_valid kosaraju_topologically_ordered kos_def by simp

  (* If they're in different SCCs, then scc2 must come before scc1 in the reversed
     order i.e. (idx2_kos > idx1_kos) *)
  have scc_ordering: "scc1_name \<noteq> scc2_name \<Longrightarrow> idx2_kos > idx1_kos"
  proof -
    assume "scc1_name \<noteq> scc2_name"

    (* By contradiction *)
    show "idx2_kos > idx1_kos"
    proof (rule ccontr)
      assume "\<not> idx2_kos > idx1_kos"
      then have "idx1_kos \<ge> idx2_kos" by simp
      then have "idx1_kos > idx2_kos \<or> idx1_kos = idx2_kos" by auto
      moreover have "idx1_kos \<noteq> idx2_kos"
        using \<open>scc1_name \<noteq> scc2_name\<close> idx1_kos_def(2) idx2_kos_def(2) by auto
      ultimately have "idx1_kos > idx2_kos" by simp

      (* This means scc1 comes before scc2, so no edge from item1 to item2 by topological ordering *)
      have "\<not>has_edge graph (getName item2) (getName item1)"
      proof -
        have "idx2_kos < length kos" using idx2_kos_def(1) .
        have "getName item1 \<in> set (kos ! idx1_kos)" using scc1_props(2) idx1_kos_def(2) by simp
        have "getName item2 \<in> set (kos ! idx2_kos)" using scc2_props(2) idx2_kos_def(2) by simp

        from topo_ordered have "\<forall>i j. i < j \<and> j < length kos \<longrightarrow>
           (\<forall>u v. u \<in> set (kos ! i) \<and> v \<in> set (kos ! j) \<longrightarrow> \<not>has_edge graph v u)"
          unfolding sccs_topologically_ordered_def .

        hence "\<forall>u v. u \<in> set (kos ! idx1_kos) \<and> v \<in> set (kos ! idx2_kos) \<longrightarrow> \<not>has_edge graph v u"
          using \<open>idx1_kos > idx2_kos\<close> \<open>idx2_kos < length kos\<close>
          using edge_in_graph idx1_kos_def(1,2) idx2_kos_def(2) scc1_props(2) scc2_props(2)
          by blast 
        
        thus ?thesis
          using \<open>getName item1 \<in> set (kos ! idx1_kos)\<close> \<open>getName item2 \<in> set (kos ! idx2_kos)\<close>
          by simp
      qed

      thus False using edge_in_graph
        using \<open>idx2_kos < idx1_kos\<close> idx1_kos_def(1,2) idx2_kos_def(2) scc1_props(2) scc2_props(2)
          sccs_topologically_ordered_def topo_ordered by blast 
    qed
  qed

  (* Now we have: sccs = rev kos mapped through itemMap *)
  (* So indices in sccs are: length kos - 1 - idx_in_kos *)

  have sccs_result: "sccs = map_sccs_to_items itemMap (rev kos)"
    using result no_dup_errors deps_exist graph_def kos_def itemMap_def by simp

  (* Map the indices from kos to sccs (which is rev kos) *)
  define idx1 where "idx1 = length kos - 1 - idx1_kos"
  define idx2 where "idx2 = length kos - 1 - idx2_kos"

  (* Indices are valid *)
  have idx1_valid: "idx1 < length sccs"
    using idx1_kos_def(1) idx1_def sccs_result by simp
  have idx2_valid: "idx2 < length sccs"
    using idx2_kos_def(1) idx2_def sccs_result by simp

  (* The SCCs at these indices in sccs *)
  have "sccs ! idx1 = map (\<lambda>name. the (fmlookup itemMap name)) scc1_name"
  proof -
    have "rev kos ! idx1 = scc1_name"
      using idx1_kos_def idx1_def by (simp add: rev_nth)
    thus ?thesis
      using sccs_result idx1_def idx1_kos_def(1) by simp
  qed

  have "sccs ! idx2 = map (\<lambda>name. the (fmlookup itemMap name)) scc2_name"
  proof -
    have "rev kos ! idx2 = scc2_name"
      using idx2_kos_def idx2_def by (simp add: rev_nth)
    thus ?thesis
      using sccs_result idx2_def idx2_kos_def(1) by simp
  qed

  (* item1 is in sccs ! idx1 *)
  have item1_in_scc: "item1 \<in> set (sccs ! idx1)"
  proof -
    have "getName item1 \<in> set scc1_name"
      using scc1_props(2) by simp
    moreover have "fmlookup itemMap (getName item1) = Some item1"
    proof -
      have pair_in: "(getName item1, item1) \<in> set (map (\<lambda>i. (getName i, i)) items)"
        using item1_in by auto
      have "map fst (map (\<lambda>i. (getName i, i)) items) = map getName items"
        by simp
      then have "distinct (map fst (map (\<lambda>i. (getName i, i)) items))"
        using names_distinct by metis
      then show ?thesis
        unfolding itemMap_def build_item_map.simps
        by (metis fmap_of_list.rep_eq map_of_eq_Some_iff pair_in)
    qed
    ultimately show ?thesis
      using \<open>sccs ! idx1 = map (\<lambda>name. the (fmlookup itemMap name)) scc1_name\<close>
      by force
  qed

  (* item2 is in sccs ! idx2 *)
  have item2_in_scc: "item2 \<in> set (sccs ! idx2)"
  proof -
    have "getName item2 \<in> set scc2_name"
      using scc2_props(2) by simp
    moreover have "fmlookup itemMap (getName item2) = Some item2"
    proof -
      have pair_in: "(getName item2, item2) \<in> set (map (\<lambda>i. (getName i, i)) items)"
        using item2_in by auto
      have "map fst (map (\<lambda>i. (getName i, i)) items) = map getName items"
        by simp
      then have "distinct (map fst (map (\<lambda>i. (getName i, i)) items))"
        using names_distinct by metis
      then show ?thesis
        unfolding itemMap_def build_item_map.simps
        by (metis fmap_of_list.rep_eq map_of_eq_Some_iff pair_in)
    qed
    ultimately show ?thesis
      using \<open>sccs ! idx2 = map (\<lambda>name. the (fmlookup itemMap name)) scc2_name\<close>
      by force
  qed

  (* Show idx2 <= idx1 *)
  have "idx2 \<le> idx1"
  proof (cases "scc1_name = scc2_name")
    case True
    then show ?thesis
      using idx1_def idx2_def
      by (metis diff_le_mono2 edge_in_graph idx1_kos_def(1,2) idx2_kos_def(2) scc1_props(2)
          scc2_props(2) sccs_topologically_ordered_def topo_ordered verit_comp_simplify1(3)) 
  next
    case False
    then have "idx2_kos > idx1_kos"
      using scc_ordering by simp
    then show ?thesis
      by (simp add: diff_le_mono2 idx1_def idx2_def)
  qed

  thus ?thesis
    using idx1_valid idx2_valid item1_in_scc item2_in_scc by blast
qed

(*-----------------------------------------------------------------------------*)
(* Non-empty property *)
(*-----------------------------------------------------------------------------*)

(* If analyze_dependencies_generic succeeds, all SCCs are non-empty *)
theorem analyze_dependencies_generic_non_empty:
  assumes "analyze_dependencies_generic items getName getDeps = Inr sccs"
  shows "\<forall>scc \<in> set sccs. scc \<noteq> []"
proof -
  define graph where "graph = build_dep_graph getName getDeps items"
  define kos where "kos = kosaraju graph"
  define itemMap where "itemMap = build_item_map getName items"

  (* Establish preconditions *)
  have no_dup_errors: "check_duplicate_names getName items = None"
  proof (cases "check_duplicate_names getName items")
    case None
    then show ?thesis by simp
  next
    case (Some err)
    then have "analyze_dependencies_generic items getName getDeps = Inl err"
      by simp
    thus ?thesis using assms by auto
  qed

  have deps_exist: "check_deps_exist getName getDeps items itemMap = None"
  proof (cases "check_deps_exist getName getDeps items itemMap")
    case None
    then show ?thesis by simp
  next
    case (Some err)
    then have "analyze_dependencies_generic items getName getDeps = Inl err"
      using itemMap_def no_dup_errors
      by simp
    thus ?thesis using assms by auto
  qed

  have names_distinct: "distinct (map getName items)"
    using no_dup_errors no_duplicate_errors_means_distinct by blast

  have graph_valid: "valid_graph graph"
    using names_distinct deps_exist graph_def itemMap_def no_dep_errors_means_valid_graph
    using no_dup_errors by blast

  have result: "sccs = map_sccs_to_items itemMap (rev kos)"
    using assms no_dup_errors deps_exist graph_def kos_def itemMap_def
    by simp

  (* Each SCC in kos is non-empty by kosaraju_sound *)
  have kos_non_empty: "\<forall>scc_names \<in> set kos. scc_names \<noteq> []"
  proof (intro ballI)
    fix scc_names
    assume "scc_names \<in> set kos"
    then obtain v where "v \<in> set scc_names \<and> (\<forall>w. w \<in> set scc_names \<longleftrightarrow> has_vertex graph w \<and> in_same_scc graph w v)"
      using graph_valid kosaraju_sound kos_def by blast
    then show "scc_names \<noteq> []" by auto
  qed

  (* Therefore each SCC in sccs is non-empty *)
  show ?thesis
  proof (intro ballI)
    fix scc
    assume "scc \<in> set sccs"
    then have "scc \<in> set (map_sccs_to_items itemMap (rev kos))"
      using result by simp
    then obtain scc_names where "scc_names \<in> set (rev kos)"
      and "scc = map (\<lambda>name. the (fmlookup itemMap name)) scc_names"
      by auto
    then have "scc_names \<in> set kos" by simp
    then have "scc_names \<noteq> []" using kos_non_empty by simp
    then show "scc \<noteq> []" using `scc = map (\<lambda>name. the (fmlookup itemMap name)) scc_names` by simp
  qed
qed

end
