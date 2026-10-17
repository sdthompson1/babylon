theory ElabModule
  imports ElabDecl "../bab/BabNames" "../core/LinkModules" "../graph/Dependency"
begin

(* Module elaborator. This typechecks a BabModule and converts it into the Core
   representation.

   Each BabModule is converted into a *pair* of CompiledModules (one for the interface
   and one for the implementation), where CompiledModule = CoreModule \<times> ElabEnv.
   (The CoreModule contains the compiled Core code corresponding to the original
   declarations; the ElabEnv contains additional information that is not represented
   in Core, e.g. typedefs or Babylon-level "void" functions.)

   Inputs to elab_module:
    - The BabModule to be elaborated.
    - A list of CompiledModules representing the *interfaces* of this BabModule's
      *interface* imports.
    - A list of CompiledModules representing the *interfaces* of this BabModule's
      *implementation* imports.

   The outputs are either the pair of CompiledModules representing the successfully
   compiled interface and implementation of this module; or an error.

   If module elaboration succeeds and linking also succeeds, then the resulting linked
   CoreModule is guaranteed to be well-typed at the Core level (under certain mild
   assumptions), so a separate Core typechecking pass is not needed. See
   ElabModuleCorrect.thy for the details.
*)


(* ========================================================================== *)
(* Declaration classification                                                 *)
(* ========================================================================== *)

(* True if a BabDeclaration is a declaration only, not a definition (e.g.: const
   without a right-hand-side, non-extern function without a body). *)
fun is_decl_only :: "BabDeclaration \<Rightarrow> bool" where
  "is_decl_only (BabDecl_Const dc) = (DC_Value dc = None)"
| "is_decl_only (BabDecl_Function df) = (DF_Body df = None \<and> \<not> DF_Extern df)"
| "is_decl_only (BabDecl_Datatype dd) = False"
| "is_decl_only (BabDecl_Typedef dt) = (DT_Definition dt = None \<and> \<not> DT_Extern dt)"

(* True if a BabDeclaration declares a term-namespace name (a constant or a
   function), as opposed to a type-namespace name (a datatype or typedef). *)
fun is_term_decl :: "BabDeclaration \<Rightarrow> bool" where
  "is_term_decl (BabDecl_Const _) = True"
| "is_term_decl (BabDecl_Function _) = True"
| "is_term_decl (BabDecl_Datatype _) = False"
| "is_term_decl (BabDecl_Typedef _) = False"


(* ========================================================================== *)
(* Module error checks                                                        *)
(* ========================================================================== *)

(* Structural checks needed on a module:

    - A name cannot be declared or defined more than once in the *same* face
      of a module. This would be caught by the DepErr_DuplicateName check in
      sort_declarations.

    - If the same name is declared/defined in *both* faces of a module, then
      it must be a declaration in the interface, and a definition in the
      implementation (the declare-then-define pattern).
       - For type names, this is checked by ElabDecl (which can see all type-
         namespace definitions in the typing env).
       - For term names, this is checked by check_cross_face_duplicates below
         (it can't be done in ElabDecl; the latter records "definedness" only
         in the face-local CoreModule, so it can't distinguish between a name
         that was defined in the implementation, vs. one that was only declared
         there).

    - Only definitions, not declarations, are allowed in the implementation
      face. This is checked by check_impl_definitions, below.

    - Every declaration in the interface must have a corresponding definition
      in the implementation. This is checked by check_completeness, below.

    - In the declare-then-define pattern, ghostness, function argument types,
      etc., must match between declaration and definition. This is checked by
      ElabDecl on a case-by-case basis.
*)

(* This is the cross-face duplicates check for term names, as described above. *)
definition check_cross_face_duplicates ::
  "BabDeclaration list \<Rightarrow> BabDeclaration list \<Rightarrow> TypeError list" where
  "check_cross_face_duplicates intf impl =
     (let intfDefs = filter (\<lambda>d. is_term_decl d \<and> \<not> is_decl_only d) intf
      in concat (map (\<lambda>d.
           if is_term_decl d
              \<and> find (\<lambda>di. get_decl_name di = get_decl_name d) intfDefs \<noteq> None
           then [TyErr_DuplicateName (bab_declaration_location d) (get_decl_name d)]
           else []) impl))"

(* This is the check that the implementation contains only definitions, not
   declarations, as described above. *)
definition check_impl_definitions :: "BabDeclaration list \<Rightarrow> TypeError list" where
  "check_impl_definitions impl =
     concat (map (\<lambda>d. if is_decl_only d
                      then [TyErr_DeclarationOnlyInImplementation
                              (bab_declaration_location d) (get_decl_name d)]
                      else [])
                 impl)"

(* This is the check that every declaration has a corresponding definition, as
   described above. It runs after the CoreModules have been produced. *)
definition check_completeness ::
  "BabDeclaration list \<Rightarrow> CoreModule \<Rightarrow> CoreModule \<Rightarrow> TypeError list" where
  "check_completeness intf intMod implMod =
     concat (map (\<lambda>d.
       case d of
         BabDecl_Const dc \<Rightarrow>
           \<comment> \<open>A ghost constant is desugared to a nullary ghost function, so its
              definition lands in CM_Functions, not CM_GlobalVars.\<close>
           (if DC_Value dc = None
               \<and> (if DC_Ghost dc = Ghost
                  then DC_Name dc |\<notin>| fmdom (CM_Functions intMod)
                       \<and> DC_Name dc |\<notin>| fmdom (CM_Functions implMod)
                  else DC_Name dc |\<notin>| fmdom (CM_GlobalVars intMod)
                       \<and> DC_Name dc |\<notin>| fmdom (CM_GlobalVars implMod))
            then [TyErr_DeclaredButNotDefined (DC_Location dc) (DC_Name dc)]
            else [])
       | BabDecl_Function df \<Rightarrow>
           (if DF_Body df = None \<and> \<not> DF_Extern df
               \<and> DF_Name df |\<notin>| fmdom (CM_Functions intMod)
               \<and> DF_Name df |\<notin>| fmdom (CM_Functions implMod)
            then [TyErr_DeclaredButNotDefined (DF_Location df) (DF_Name df)]
            else [])
       | BabDecl_Datatype dd \<Rightarrow> []
       | BabDecl_Typedef dt \<Rightarrow>
           (if DT_Definition dt = None \<and> \<not> DT_Extern dt
               \<and> DT_Name dt |\<notin>| fmdom (CM_TypeSubst implMod)
            then [TyErr_AbstractTypeNotRealized (DT_Location dt) (DT_Name dt)]
            else []))
       intf)"


(* ========================================================================== *)
(* Declaration dependency sorting                                             *)
(* ========================================================================== *)

(* Map NsRef to a graph key, by prepending a tag ("V:" for term names, "T:" for types). *)
fun tag_ref :: "NsRef \<Rightarrow> string" where
  "tag_ref (NsRef_Term n) = ''V:'' @ n"
| "tag_ref (NsRef_Type n) = ''T:'' @ n"

(* Get the name of a BabDeclaration, as an NsRef. *)
definition decl_ref :: "BabDeclaration \<Rightarrow> NsRef" where
  "decl_ref d = (if is_term_decl d then NsRef_Term (get_decl_name d)
                 else NsRef_Type (get_decl_name d))"

(* Get the name of a BabDeclaration, as a graph key. *)
definition tagged_decl_name :: "BabDeclaration \<Rightarrow> string" where
  "tagged_decl_name d = tag_ref (decl_ref d)"

(* Extract all the data ctor names being defined by a list of declarations,
   each paired with its datatype name. *)
definition decl_ctor_owners :: "BabDeclaration list \<Rightarrow> (string \<times> string) list" where
  "decl_ctor_owners ds =
     concat (map (\<lambda>d. case d of
                        BabDecl_Datatype dd \<Rightarrow> map (\<lambda>(_, cn, _). (cn, DD_Name dd)) (DD_Ctors dd)
                      | _ \<Rightarrow> []) ds)"

(* Given a name (NsRef) found in the program text, find the graph key of the
   BabDeclaration that originally defined that name.
   For data constructors, this returns the corresponding datatype name (looked up in the
   "owners" list); for anything else, the name is returned directly. *)
definition ref_key :: "(string \<times> string) list \<Rightarrow> NsRef \<Rightarrow> string" where
  "ref_key owners r =
     (case r of
        NsRef_Term n \<Rightarrow> (case map_of owners n of
                           Some dt \<Rightarrow> tag_ref (NsRef_Type dt)
                         | None \<Rightarrow> tag_ref r)
      | NsRef_Type _ \<Rightarrow> tag_ref r)"

(* Scan a BabDeclaration to find its dependencies, as a list of graph keys.
   The results are filtered to only those in the given "declNames" set (which is itself
   a set of graph keys). *)
definition decl_deps ::
  "(string \<times> string) list \<Rightarrow> string fset \<Rightarrow> BabDeclaration \<Rightarrow> string list" where
  "decl_deps owners declNames d =
     filter (\<lambda>n. n |\<in>| declNames) (map (ref_key owners) (bab_declaration_names d))"

(* Helper function used by sort_declarations. This takes the ctxDecls and decls lists
   from that function, and returns a combined list, containing (True, d) for items from
   decls, and (False, d) for items from ctxDecls that are not also in decls. The idea
   is that (in "implementation" mode) the dependency graph should also contain nodes
   from the interface, but those nodes are tagged False so that they can be filtered
   out later. *)
definition sort_items ::
  "BabDeclaration list \<Rightarrow> BabDeclaration list \<Rightarrow> (bool \<times> BabDeclaration) list" where
  "sort_items ctxDecls decls =
     (let ownNames = set (map tagged_decl_name decls)
      in map (Pair True) decls
         @ map (Pair False) (filter (\<lambda>c. tagged_decl_name c \<notin> ownNames) ctxDecls))"

(* Given a graph item (bool \<times> BabDeclaration, see sort_items), this calculates its
   dependencies, as a list of graph keys.

   A "decls" item also gets the dependencies of its corresponding "ctxDecls" item
   (e.g. if we have "const x: i32 = y;" in the impl, and "const x: T;" in the interface,
   then "x" depends on both "y", from the implementation, and "T", from the interface). *)
definition item_deps ::
  "(string \<times> string) list \<Rightarrow> string fset \<Rightarrow> BabDeclaration list
   \<Rightarrow> bool \<times> BabDeclaration \<Rightarrow> string list" where
  "item_deps owners declNames ctxDecls item =
     (let deps = decl_deps owners declNames;
          (own, d) = item
      in deps d
         @ (if own
            then concat (map deps (filter (\<lambda>c. tagged_decl_name c = tagged_decl_name d) ctxDecls))
            else []))"

(* The errors of a result (none, if it is a success). *)
fun result_errors :: "'e list + 'a \<Rightarrow> 'e list" where
  "result_errors (Inl errs) = errs"
| "result_errors (Inr _) = []"

(* This goes through the SCCs (from Kosaraju) and fishes out the declarations in
   dependency order. Only the items tagged True are kept (see sort_items).
   Errors are checked:
    - A non-singleton SCC is always an error (mutual recursion).
    - A singleton SCC is an error if the name depends upon itself (self-recursion). *)
fun check_sccs ::
  "((bool \<times> BabDeclaration) \<Rightarrow> string list) \<Rightarrow> (bool \<times> BabDeclaration) list list
   \<Rightarrow> TypeError list + BabDeclaration list" where
  "check_sccs deps [] = Inr []"
| "check_sccs deps ([] # rest) = check_sccs deps rest"
| "check_sccs deps ([(own, d)] # rest) =
    (if tagged_decl_name d \<in> set (deps (own, d))
     then Inl (TyErr_RecursiveDeclarations (bab_declaration_location d) [get_decl_name d]
               # result_errors (check_sccs deps rest))
     else (case check_sccs deps rest of
             Inl errs \<Rightarrow> Inl errs
           | Inr ds \<Rightarrow> Inr (if own then d # ds else ds)))"
| "check_sccs deps (scc # rest) =
    Inl (TyErr_RecursiveDeclarations
           (bab_declaration_location
              (case find fst scc of Some (_, d) \<Rightarrow> d | None \<Rightarrow> snd (hd scc)))
           (map (get_decl_name \<circ> snd) scc)
         # result_errors (check_sccs deps rest))"

(* The main function to sort BabDeclarations into dependency order.
   Calls analyze_dependencies_generic (which itself calls Kosaraju) to find SCCs, then
   uses check_sccs to rule out dependency cycles (recursive declarations are not currently
   permitted).

   This is called twice per module: once for the interface, and once for the implementation.
   In "interface" mode, ctxDecls is empty and decls contains the interface declarations.
   In "implementation" mode, ctxDecls contains the interface declarations, and decls the
   implementation ones.
   This allows cycles through both faces to be detected, e.g. "type T; datatype D = D(T);"
   in the interface, with "type T = D;" in the implementation.
   Note that only the declarations from decls will be returned.

   As was mentioned above, this is also where duplicate names within the same face are
   detected. *)
definition sort_declarations ::
  "BabDeclaration list \<Rightarrow> BabDeclaration list \<Rightarrow> TypeError list + BabDeclaration list" where
  "sort_declarations ctxDecls decls =
     (case decls of
        [] \<Rightarrow> Inr []
      | d0 # _ \<Rightarrow>
          (let items = sort_items ctxDecls decls;
               declNames = fset_of_list (map (tagged_decl_name \<circ> snd) items);
               owners = decl_ctor_owners (map snd items);
               deps = item_deps owners declNames ctxDecls
           in case analyze_dependencies_generic items (tagged_decl_name \<circ> snd) deps of
                Inl (DepErr_DuplicateName dup) \<Rightarrow>
                  \<comment> \<open>The find cannot fail: the duplicate (tagged) name comes from the items
                     themselves. The error reports the untagged name.\<close>
                  (let d = the (find (\<lambda>d. tagged_decl_name d = dup) (map snd items))
                   in Inl [TyErr_DuplicateName (bab_declaration_location d) (get_decl_name d)])
              | Inl (DepErr_DependencyNotFound _ _) \<Rightarrow>
                  \<comment> \<open>Shouldn't happen: decl_deps filters its result to declNames\<close>
                  Inl [TyErr_DependencyAnalysisUnexpectedFailure (bab_declaration_location d0)]
              | Inr sccs \<Rightarrow> check_sccs deps sccs))"

(* check_sccs returns exactly the True-tagged declarations of its SCC list,
   concatenated in topological order: the multiset is preserved. *)
lemma check_sccs_mset:
  assumes "check_sccs deps sccs = Inr ds"
  shows "mset ds = mset (map snd (filter fst (concat sccs)))"
  using assms
proof (induction deps sccs arbitrary: ds rule: check_sccs.induct)
  case 1
  then show ?case by auto
next
  case (2 deps rest)
  then show ?case by simp
next
  case (3 deps own d rest)
  from "3.prems" have cond: "tagged_decl_name d \<notin> set (deps (own, d))"
    by (auto split: if_splits)
  from "3.prems" cond obtain ds' where
    rest_ok: "check_sccs deps rest = Inr ds'" and ds_eq: "ds = (if own then d # ds' else ds')"
    by (auto split: sum.splits)
  have ih: "mset ds' = mset (map snd (filter fst (concat rest)))"
    using "3.IH" cond rest_ok by blast
  show ?case
    using ih by (cases own) (simp_all add: ds_eq)
next
  case 4
  then show ?case by auto
qed

(* The True-tagged items of sort_items are exactly decls. *)
lemma sort_items_own:
  "map snd (filter fst (sort_items ctxDecls decls)) = decls"
  by (simp add: sort_items_def Let_def filter_map comp_def)

(* Hence sort_declarations returns a permutation of decls: the dependency
   analysis emits every item exactly once across its SCCs
   (analyze_dependencies_generic_permutation), and check_sccs concatenates
   the True-tagged ones, which are exactly decls (sort_items_own). *)
lemma sort_declarations_mset:
  assumes ok: "sort_declarations ctxDecls decls = Inr sortedDecls"
  shows "mset sortedDecls = mset decls"
proof (cases decls)
  case Nil
  then have "sortedDecls = []"
    using ok unfolding sort_declarations_def by simp
  then show ?thesis using Nil by simp
next
  case (Cons d ds)
  let ?items = "sort_items ctxDecls decls"
  let ?deps = "item_deps (decl_ctor_owners (map snd ?items))
                 (fset_of_list (map (tagged_decl_name \<circ> snd) ?items)) ctxDecls"
  obtain sccs where
    ana: "analyze_dependencies_generic ?items (tagged_decl_name \<circ> snd) ?deps = Inr sccs" and
    chk: "check_sccs ?deps sccs = Inr sortedDecls"
    using ok unfolding sort_declarations_def Let_def
    by (auto simp: Cons split: sum.splits DependencyError.splits)
  have "mset sortedDecls = mset (map snd (filter fst (concat sccs)))"
    by (rule check_sccs_mset[OF chk])
  also have "\<dots> = mset (map snd (filter fst ?items))"
    by (simp only: mset_map mset_filter analyze_dependencies_generic_permutation[OF ana])
  also have "\<dots> = mset decls"
    by (simp only: sort_items_own)
  finally show ?thesis .
qed


(* ========================================================================== *)
(* Compiled modules and ElabEnv combination                                   *)
(* ========================================================================== *)

(* The compiled representation of a module face: the CoreModule carries the
   semantically-important content, the ElabEnv the elaborator-only residue
   (typedefs, nullary-data-ctor names, void-function names - data that is
   not recoverable from a CoreModule), and the two travel together.

   The CoreModule's type env contains only newly declared items; it does not
   contain "repeat" entries for imported items. Similarly, the ElabEnv only contains
   new items (e.g. new typedefs) created by this module; it doesn't repeat typedefs
   (or other items) that only came in through the imports. *)
type_synonym CompiledModule = "CoreModule \<times> ElabEnv"

(* Field-wise union of a list of (domain-disjoint) ElabEnvs.
   EE_CurrentFunctionVoid is per-function scratch state, not module data, so
   the union resets it to its neutral value. *)
definition elabenv_union :: "ElabEnv list \<Rightarrow> ElabEnv" where
  "elabenv_union es =
     \<lparr> EE_Typedefs = fmlist_union (map EE_Typedefs es),
       EE_NullaryDataCtors = funion_list (map EE_NullaryDataCtors es),
       EE_VoidFunctions = funion_list (map EE_VoidFunctions es),
       EE_GhostConstants = funion_list (map EE_GhostConstants es),
       EE_CurrentFunctionVoid = False \<rparr>"

(* The delta of a fold's final ElabEnv against its initial one: the entries
   the fold added, i.e. the module face's own contributions. This is a domain
   restriction, not a value comparison; imported entries rewritten in place
   by this face's realizations are deliberately dropped (those rewrites
   matter only while elaborating this face). *)
definition elabenv_delta :: "ElabEnv \<Rightarrow> ElabEnv \<Rightarrow> ElabEnv" where
  "elabenv_delta initial final =
     \<lparr> EE_Typedefs = fmdrop_fset (fmdom (EE_Typedefs initial)) (EE_Typedefs final),
       EE_NullaryDataCtors = EE_NullaryDataCtors final |-| EE_NullaryDataCtors initial,
       EE_VoidFunctions = EE_VoidFunctions final |-| EE_VoidFunctions initial,
       EE_GhostConstants = EE_GhostConstants final |-| EE_GhostConstants initial,
       EE_CurrentFunctionVoid = False \<rparr>"

lemma elabenv_union_fields [simp]:
  "EE_Typedefs (elabenv_union es) = fmlist_union (map EE_Typedefs es)"
  "EE_NullaryDataCtors (elabenv_union es) = funion_list (map EE_NullaryDataCtors es)"
  "EE_VoidFunctions (elabenv_union es) = funion_list (map EE_VoidFunctions es)"
  "EE_GhostConstants (elabenv_union es) = funion_list (map EE_GhostConstants es)"
  "EE_CurrentFunctionVoid (elabenv_union es) = False"
  by (simp_all add: elabenv_union_def)

lemma elabenv_delta_fields [simp]:
  "EE_Typedefs (elabenv_delta initial final)
     = fmdrop_fset (fmdom (EE_Typedefs initial)) (EE_Typedefs final)"
  "EE_NullaryDataCtors (elabenv_delta initial final)
     = EE_NullaryDataCtors final |-| EE_NullaryDataCtors initial"
  "EE_VoidFunctions (elabenv_delta initial final)
     = EE_VoidFunctions final |-| EE_VoidFunctions initial"
  "EE_GhostConstants (elabenv_delta initial final)
     = EE_GhostConstants final |-| EE_GhostConstants initial"
  "EE_CurrentFunctionVoid (elabenv_delta initial final) = False"
  by (simp_all add: elabenv_delta_def)


(* ========================================================================== *)
(* elab_module                                                                *)
(* ========================================================================== *)

(* Errors: elab_module needs to link together all the import modules (to create a unified
   import environment) and therefore, theoretically, can generate link errors. However,
   link errors are not expected to occur in normal use, so this can be considered an
   "internal compiler error". Type errors, by contrast, are normal and expected. *)
datatype ElabModuleError =
  EM_LinkError LinkError
  | EM_TypeErrors "TypeError list"

(* Compile one face against its dependency set: link the deps' CoreModules
   into a typing context, union their ElabEnv deltas, sort the face's
   declarations into dependency order, elaborate them (see ElabDecl.thy),
   and return the face's unlinked CoreModule paired with its delta ElabEnv. *)
definition elab_face ::
  "CompiledModule list \<Rightarrow> string fset \<Rightarrow> BabDeclaration list \<Rightarrow> BabDeclaration list
   \<Rightarrow> ElabModuleError + CompiledModule" where
  "elab_face deps ownAbstract ctxDecls decls =
     (case link_modules (map fst deps) of
        Inl le \<Rightarrow> Inl (EM_LinkError le)
      | Inr ctx \<Rightarrow>
          (let e = elabenv_union (map snd deps)
           in case sort_declarations ctxDecls decls of
                Inl errs \<Rightarrow> Inl (EM_TypeErrors errs)
              | Inr sortedDecls \<Rightarrow>
                  (case elab_declarations (CM_TyEnv ctx) e ownAbstract
                                          (CM_GlobalVars ctx) sortedDecls of
                     Inl errs \<Rightarrow> Inl (EM_TypeErrors errs)
                   | Inr (m, foldEnv) \<Rightarrow> Inr (m, elabenv_delta e foldEnv))))"

(* The main elab_module function. *)
definition elab_module ::
  "BabModule \<Rightarrow> CompiledModule list \<Rightarrow> CompiledModule list
   \<Rightarrow> ElabModuleError + (CompiledModule \<times> CompiledModule)" where
  "elab_module bm intDeps implDeps =
    (let checkErrs = check_cross_face_duplicates (Mod_Interface bm) (Mod_Implementation bm)
                     @ check_impl_definitions (Mod_Implementation bm)
     in if checkErrs \<noteq> [] then Inl (EM_TypeErrors checkErrs)
        else case elab_face intDeps {||} [] (Mod_Interface bm) of
               Inl err \<Rightarrow> Inl err
             | Inr (intMod, intEE) \<Rightarrow>
                 (case elab_face (intDeps @ implDeps @ [(intMod, intEE)])
                         (TE_TypeVars (CM_TyEnv intMod))
                         (Mod_Interface bm) (Mod_Implementation bm) of
                    Inl err \<Rightarrow> Inl err
                  | Inr (implMod, implEE) \<Rightarrow>
                      (let compErrs = check_completeness (Mod_Interface bm) intMod implMod
                       in if compErrs \<noteq> []
                          then Inl (EM_TypeErrors compErrs)
                          else Inr ((intMod, intEE), (implMod, implEE)))))"

end
