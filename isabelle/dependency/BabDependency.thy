theory BabDependency
  imports Main "HOL-Library.Char_ord" "HOL-Library.List_Lexorder" "HOL-Library.FSet" "HOL-Library.Finite_Map" "HOL-Library.Multiset" "../base/Location" "../base/BabSyntax" "Dependency"
begin

(* Babylon-specific dependency errors *)
datatype BabDependencyError =
  BabDepErr_CircularDependency Location "string list"  (* circular dependency detected: <cycle> *)
  | BabDepErr_SelfImport Location string  (* module imports itself: location, module name *)
  | BabDepErr_Other DependencyError  (* Generic dependency error from Dependency.thy *)


(* Function to extract all imported module names from a module *)
fun get_module_imports :: "BabModule \<Rightarrow> string list"
  where
"get_module_imports module =
  (let interfaceImports = map Imp_ModuleName (Mod_InterfaceImports module);
       implImports = map Imp_ModuleName (Mod_ImplementationImports module)
   in interfaceImports @ implImports)"


(* Check if any module imports itself *)
fun check_self_imports :: "BabModule list \<Rightarrow> BabDependencyError option"
  where
"check_self_imports [] = None" |
"check_self_imports (m # rest) =
  (if List.member (get_module_imports m) (Mod_Name m) then
    Some (BabDepErr_SelfImport
      (case find (\<lambda>imp. Imp_ModuleName imp = Mod_Name m)
                  (Mod_InterfaceImports m @ Mod_ImplementationImports m) of
        Some imp \<Rightarrow> Imp_Location imp
      | None \<Rightarrow> Location '''' 0 0 0 0)
      (Mod_Name m))
   else check_self_imports rest)"

(* Find an import statement that belongs to a (known) cycle *)
fun make_circular_dependency_error :: "BabModule list \<Rightarrow> string list \<Rightarrow> BabDependencyError"
  where
"make_circular_dependency_error modules cycle =
  (case cycle of
    [] \<Rightarrow> BabDepErr_CircularDependency (Location '''' 0 0 0 0) cycle
  | (first_name # _) \<Rightarrow>
      (case find (\<lambda>m. Mod_Name m = first_name) modules of
        None \<Rightarrow> BabDepErr_CircularDependency (Location '''' 0 0 0 0) cycle
      | Some module \<Rightarrow>
          let all_imports = Mod_InterfaceImports module @ Mod_ImplementationImports module;
              imports_in_cycle = filter (\<lambda>imp. List.member cycle (Imp_ModuleName imp)) all_imports
          in (case imports_in_cycle of
              [] \<Rightarrow> BabDepErr_CircularDependency (Location '''' 0 0 0 0) cycle
            | (imp # _) \<Rightarrow> BabDepErr_CircularDependency (Imp_Location imp) cycle)))"


(* Main dependency analysis function *)
(* This sorts modules such that if one module imports another (directly or indirectly),
   then the dependency will appear BEFORE the importer in the list.
   This means that if modules are processed in the resulting order then no name will
   be encountered before its definition.
   If cyclic dependencies exist or any other error occurs, a BabDependencyError will
   be reported.
*)
fun analyze_dependencies :: "BabModule list \<Rightarrow> (BabDependencyError, BabModule list) sum"
  where
"analyze_dependencies modules =
  (case check_self_imports modules of
    Some err \<Rightarrow> Inl err
  | None \<Rightarrow>
      (case analyze_dependencies_generic modules Mod_Name get_module_imports of
        Inl err \<Rightarrow> Inl (BabDepErr_Other err)
      | Inr sccs \<Rightarrow>
          let cycles = filter (\<lambda>scc. length scc > 1) sccs
          in
            if cycles = [] then
              Inr (concat sccs)
            else
              let cycle_names = map (map Mod_Name) cycles;
                  error = make_circular_dependency_error modules (hd cycle_names)
              in Inl error)
  )"

(* Properties: *)

(* Property 1: analyze_dependencies (if successful) returns a permutation of the input *)
theorem analyze_dependencies_permutation:
  assumes "analyze_dependencies modules = Inr sorted_modules"  (* No errors occurred *)
  shows "mset sorted_modules = mset modules"
proof -
  (* analyze_dependencies succeeded, so self-imports check passed *)
  have no_self_imports: "check_self_imports modules = None"
    using assms by (auto split: option.splits sum.splits)

  (* And we must have gotten sccs from the generic analysis *)
  obtain sccs where sccs_result: "analyze_dependencies_generic modules Mod_Name get_module_imports = Inr sccs"
    and no_cycles: "filter (\<lambda>scc. length scc > 1) sccs = []"
    and result_eq: "sorted_modules = concat sccs"
    using assms no_self_imports
    by (auto split: sum.splits if_splits option.splits simp: Let_def)

  (* Use the permutation theorem from Dependency.thy *)
  have "mset (concat sccs) = mset modules"
    using sccs_result analyze_dependencies_generic_permutation by blast

  thus ?thesis using result_eq by simp
qed

(* Helper lemma: sum of lengths of singletons equals the count *)
lemma sum_singleton_list_take:
  assumes "\<forall>scc \<in> set sccs. length scc = 1"
    and "n \<le> length sccs"
  shows "sum_list (map length (take n sccs)) = n"
  using assms
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have "n < length sccs" by simp
  then have "sccs ! n \<in> set sccs" by simp
  then have "length (sccs ! n) = 1" using Suc.prems(1) by simp

  have "sum_list (map length (take (Suc n) sccs)) =
        sum_list (map length (take n sccs @ [sccs ! n]))"
    using `n < length sccs` by (simp add: take_Suc_conv_app_nth)
  also have "... = sum_list (map length (take n sccs)) + sum_list (map length [sccs ! n])"
    by simp
  also have "... = sum_list (map length (take n sccs)) + 1"
    using `length (sccs ! n) = 1` by simp
  also have "... = n + 1"
    using Suc.IH Suc.prems(1) `n < length sccs` by simp
  finally show ?case by simp
qed

(* Property 2: If analyze_dependencies succeeds, dependencies appear strictly before
   dependants.

   Since cycles are rejected, if module1 imports module2, then module2 appears at a
   strictly earlier index than module1 in the sorted list.

   This is the crucial property for compiler use: modules can be processed left-to-right
   and all imports will already have been processed.
*)
theorem analyze_dependencies_strict_topological_order:
  assumes result: "analyze_dependencies modules = Inr sorted_modules"
    and module1_in: "module1 \<in> set modules"
    and module2_in: "module2 \<in> set modules"
    and module1_imports_module2: "Mod_Name module2 \<in> set (get_module_imports module1)"
  shows "\<exists>i j. i < j \<and>
                i < length sorted_modules \<and>
                j < length sorted_modules \<and>
                sorted_modules ! i = module2 \<and>
                sorted_modules ! j = module1"
proof -
  (* analyze_dependencies succeeded, so self-imports check passed *)
  have no_self_imports: "check_self_imports modules = None"
    using assms(1) by (auto split: option.splits sum.splits)

  (* And we got sccs with no cycles *)
  obtain sccs where sccs_result: "analyze_dependencies_generic modules Mod_Name get_module_imports = Inr sccs"
    and no_cycles: "filter (\<lambda>scc. length scc > 1) sccs = []"
    and result_eq: "sorted_modules = concat sccs"
    using assms(1) no_self_imports
    by (auto split: sum.splits if_splits option.splits simp: Let_def)

  (* Use the topological ordering theorem from Dependency.thy *)
  obtain i' j' where ij_props:
    "i' \<le> j'" "i' < length sccs" "j' < length sccs"
    "module2 \<in> set (sccs ! i')" "module1 \<in> set (sccs ! j')"
    using sccs_result module1_in module2_in module1_imports_module2
    by (meson analyze_dependencies_generic_topological_order)

  (* Since there are no cycles, each SCC has length 1 *)
  have all_singleton: "\<forall>scc \<in> set sccs. length scc = 1"
  proof (intro ballI)
    fix scc
    assume "scc \<in> set sccs"
    then show "length scc = 1"
    proof (cases "length scc > 1")
      case True
      then have "scc \<in> set (filter (\<lambda>scc. length scc > 1) sccs)"
        using `scc \<in> set sccs` by simp
      then show ?thesis using no_cycles
        by (metis length_pos_if_in_set less_numeral_extra(3) list.size(3))
    next
      case False
      moreover have "length scc \<noteq> 0" using sccs_result analyze_dependencies_generic_non_empty
        using \<open>scc \<in> set sccs\<close> by blast
      ultimately show ?thesis by linarith 
    qed
  qed

  (* So sccs ! i' and sccs ! j' are singleton lists *)
  have "length (sccs ! i') = 1"
    using ij_props(2) all_singleton by simp
  then have scc_i'_singleton: "sccs ! i' = [module2]"
    using ij_props(4) by (cases "sccs ! i'") auto

  have "length (sccs ! j') = 1"
    using ij_props(3) all_singleton by simp
  then have scc_j'_singleton: "sccs ! j' = [module1]"
    using ij_props(5) by (cases "sccs ! j'") auto

  (* Since no_self_imports, module1 cannot import itself *)
  have module1_neq_module2: "module1 \<noteq> module2"
  proof (rule ccontr)
    assume "\<not> module1 \<noteq> module2"
    then have "module1 = module2" by simp
    then have "Mod_Name module2 \<in> set (get_module_imports module1)" using module1_imports_module2 by simp
    then have "Mod_Name module1 \<in> set (get_module_imports module1)" using `module1 = module2` by simp
    then have "List.member (get_module_imports module1) (Mod_Name module1)"
      by (meson in_set_member) 
    then have "check_self_imports modules \<noteq> None"
      using module1_in by (induction modules) auto
    then show False using no_self_imports by simp
  qed

  (* Since module1 depends on module2 and both are in different SCCs, we must have i' < j' *)
  have "i' < j'"
  proof (rule ccontr)
    assume "\<not> i' < j'"
    then have "i' = j'" using ij_props(1) by simp
    then have "module1 \<in> set (sccs ! i')" using ij_props(5) by simp
    then have "module1 \<in> set [module2]" using scc_i'_singleton `i' = j'` scc_j'_singleton by simp
    then have "module1 = module2" by simp
    then show False using module1_neq_module2 by simp
  qed

  (* Find indices in sorted_modules *)
  have sorted_is_concat: "sorted_modules = concat sccs"
    using result_eq by simp

  (* Calculate the index of module2 in sorted_modules *)
  define idx_i where "idx_i = length (concat (take i' sccs))"

  (* Calculate the index of module1 in sorted_modules *)
  define idx_j where "idx_j = length (concat (take j' sccs))"

  (* Since all SCCs are singletons, idx_i = i' and idx_j = j' *)
  have idx_i_eq: "idx_i = i'"
  proof -
    have "idx_i = sum_list (map length (take i' sccs))"
      unfolding idx_i_def by (simp add: length_concat)
    also have "... = i'"
      using all_singleton ij_props(2) sum_singleton_list_take
      using nat_less_le by auto
    finally show ?thesis .
  qed

  have idx_j_eq: "idx_j = j'"
  proof -
    have "idx_j = sum_list (map length (take j' sccs))"
      unfolding idx_j_def by (simp add: length_concat)
    also have "... = j'"
      using all_singleton ij_props(3) sum_singleton_list_take
      using nat_less_le by auto
    finally show ?thesis .
  qed

  (* module2 is at index idx_i *)
  have module2_at_idx: "sorted_modules ! idx_i = module2"
  proof -
    have "sorted_modules = concat (take i' sccs) @ (sccs ! i') @ concat (drop (Suc i') sccs)"
      using sorted_is_concat ij_props(2)
      by (metis Cons_nth_drop_Suc append_take_drop_id concat.simps(2) concat_append)
    then have "sorted_modules = concat (take i' sccs) @ [module2] @ concat (drop (Suc i') sccs)"
      using scc_i'_singleton by simp
    then show ?thesis
      unfolding idx_i_def
      by (simp add: nth_append)
  qed

  (* module1 is at index idx_j *)
  have module1_at_idx: "sorted_modules ! idx_j = module1"
  proof -
    have "sorted_modules = concat (take j' sccs) @ (sccs ! j') @ concat (drop (Suc j') sccs)"
      using sorted_is_concat ij_props(3)
      by (metis Cons_nth_drop_Suc append_take_drop_id concat.simps(2) concat_append)
    then have "sorted_modules = concat (take j' sccs) @ [module1] @ concat (drop (Suc j') sccs)"
      using scc_j'_singleton by simp
    then show ?thesis
      unfolding idx_j_def
      by (simp add: nth_append)
  qed

  (* idx_i < idx_j because i' < j' *)
  have "idx_i < idx_j"
    using idx_i_eq idx_j_eq `i' < j'` by simp

  (* Indices are valid *)
  have "idx_i < length sorted_modules"
  proof -
    have "length sorted_modules = sum_list (map length sccs)"
      using sorted_is_concat by (simp add: length_concat)
    also have "... = length sccs"
      using all_singleton sum_singleton_list_take
      by (metis le_refl take_all_iff) 
    finally have "length sorted_modules = length sccs" .
    then show ?thesis using idx_i_eq ij_props(2) by simp
  qed

  have "idx_j < length sorted_modules"
  proof -
    have "length sorted_modules = sum_list (map length sccs)"
      using sorted_is_concat by (simp add: length_concat)
    also have "... = length sccs"
      using all_singleton sum_singleton_list_take
      by (metis le_refl take_all_iff) 
    finally have "length sorted_modules = length sccs" .
    then show ?thesis using idx_j_eq ij_props(3) by simp
  qed

  thus ?thesis
    using `idx_i < idx_j` `idx_i < length sorted_modules` `idx_j < length sorted_modules`
          module2_at_idx module1_at_idx
    by blast
qed

end
