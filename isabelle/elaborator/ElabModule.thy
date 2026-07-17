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
| "is_decl_only (BabDecl_Typedef dt) = (DT_Definition dt = None)"

(* True if two BabDeclarations are of the same kind: the same constructor, and
   for constants also the same ghost marker. Used by check_unique_names to
   require that an interface declaration is defined by the same *kind* of
   declaration in the implementation (a `ghost const` must be defined by a
   `ghost const`, not by a function or a non-ghost const, and so on). *)
fun same_decl_kind :: "BabDeclaration \<Rightarrow> BabDeclaration \<Rightarrow> bool" where
  "same_decl_kind (BabDecl_Const dc1) (BabDecl_Const dc2) = (DC_Ghost dc1 = DC_Ghost dc2)"
| "same_decl_kind (BabDecl_Function _) (BabDecl_Function _) = True"
| "same_decl_kind (BabDecl_Datatype _) (BabDecl_Datatype _) = True"
| "same_decl_kind (BabDecl_Typedef _) (BabDecl_Typedef _) = True"
| "same_decl_kind _ _ = False"


(* ========================================================================== *)
(* Module error checks                                                        *)
(* ========================================================================== *)

(* Names must be unique within each face (interface or implementation).
   Across the two faces, the same name may appear once in each, so long as it's a
   declaration in the interface and definition in the implementation (declare-then-define
   pattern), and both declarations are of the same kind (same_decl_kind). *)
definition check_unique_names ::
  "BabDeclaration list \<Rightarrow> BabDeclaration list \<Rightarrow> TypeError list" where
  "check_unique_names intf impl =
     (case first_duplicate_name get_decl_name intf of
        Some dup \<Rightarrow>
          \<comment> \<open>The find cannot fail (first_duplicate_name_Some_implies_find)\<close>
          (let d = the (find (\<lambda>d. get_decl_name d = dup) intf)
           in [TyErr_DuplicateName (bab_declaration_location d) dup])
      | None \<Rightarrow> [])
     @ (case first_duplicate_name get_decl_name impl of
          Some dup \<Rightarrow>
            (let d = the (find (\<lambda>d. get_decl_name d = dup) impl)
             in [TyErr_DuplicateName (bab_declaration_location d) dup])
        | None \<Rightarrow> [])
     @ concat (map (\<lambda>d.
          (case find (\<lambda>di. get_decl_name di = get_decl_name d) intf of
             None \<Rightarrow> []
           | Some di \<Rightarrow>
               if is_decl_only di \<and> \<not> is_decl_only d \<and> same_decl_kind di d then []
               else [TyErr_DuplicateName (bab_declaration_location d) (get_decl_name d)]))
          impl)"

(* The implementation must contain only definitions, not declarations *)
definition check_impl_definitions :: "BabDeclaration list \<Rightarrow> TypeError list" where
  "check_impl_definitions impl =
     concat (map (\<lambda>d. if is_decl_only d
                      then [TyErr_DeclarationOnlyInImplementation
                              (bab_declaration_location d) (get_decl_name d)]
                      else [])
                 impl)"

(* Every declaration in the interface must have a corresponding definition in the
   implementation *)
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
           (if DT_Definition dt = None
               \<and> DT_Name dt |\<notin>| fmdom (CM_TypeSubst implMod)
            then [TyErr_AbstractTypeNotRealized (DT_Location dt) (DT_Name dt)]
            else []))
       intf)"


(* ========================================================================== *)
(* Declaration dependency sorting                                             *)
(* ========================================================================== *)

(* The type variables occurring in the context-declared type(s) of a name:
   the declared type of a global, the argument/return types of a function,
   the payload type of a data constructor, or the target of a typedef. These
   are the abstract types a use of the name depends on. *)
definition ctx_declared_type_tyvars :: "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> string \<Rightarrow> string list" where
  "ctx_declared_type_tyvars env elabEnv n =
     (case fmlookup (TE_GlobalVars env) n of
        Some ty \<Rightarrow> type_tyvars_list ty | None \<Rightarrow> [])
     @ (case fmlookup (TE_Functions env) n of
          Some info \<Rightarrow> concat (map (type_tyvars_list \<circ> fst) (FI_TmArgs info))
                       @ type_tyvars_list (FI_ReturnType info)
        | None \<Rightarrow> [])
     @ (case fmlookup (TE_DataCtors env) n of
          Some (_, _, payload) \<Rightarrow> type_tyvars_list payload | None \<Rightarrow> [])
     @ (case fmlookup (EE_Typedefs elabEnv) n of
          Some (_, target) \<Rightarrow> type_tyvars_list target | None \<Rightarrow> [])"

(* The dependencies of a declaration, filtered to the names declared in the
   same list (declNames): the names it syntactically references, plus the
   *realization-visibility* edges. A declaration can depend on a realization
   without mentioning the realized name: "const b: i32 = x;" references only
   x, yet elaborates correctly only once x's declared type T has been
   realized. So the declaration also depends on the abstract types occurring
   in the context-declared types of the names it references - and of the name
   it itself defines, when it defines a previously-declared name ("const x:
   i32 = 100;" against interface "const x: T;" references nothing at all, yet
   its must-match-the-declaration check needs T realized). One level
   suffices: a realization's own target references the next type name,
   ordering the realizations among themselves. For names declared in the same
   list the context lookups return nothing, and ordinary reference edges plus
   transitivity cover the same ground.

   The declaration's own name is excluded from the realization-visibility
   edges: for a realization "type T = ...", the context lookup of T itself
   finds T's own typedef entry ([], CoreTy_Var T), whose type variable is T -
   a spurious self-edge that would make every realization look recursive.
   Genuine self-recursion is still detected, through the *syntactic*
   references (a self-referential declaration necessarily mentions its own
   name). *)
definition decl_deps ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> string fset \<Rightarrow> BabDeclaration \<Rightarrow> string list" where
  "decl_deps env elabEnv declNames d =
     (let refs = bab_declaration_names d;
          realizationDeps =
            filter (\<lambda>n. n \<noteq> get_decl_name d)
              (concat (map (ctx_declared_type_tyvars env elabEnv) (get_decl_name d # refs)))
      in filter (\<lambda>n. n |\<in>| declNames) (refs @ realizationDeps))"

(* This goes through the SCCs (from Kosaraju) and fishes out the declarations in
   dependency order. Errors are checked for:
    - A non-singleton SCC is always an error (mutual recursion).
    - A singleton SCC is an error if the name depends upon itself (self-recursion). *)
fun check_sccs ::
  "(BabDeclaration \<Rightarrow> string list) \<Rightarrow> BabDeclaration list list
   \<Rightarrow> TypeError list + BabDeclaration list" where
  "check_sccs deps [] = Inr []"
| "check_sccs deps ([] # rest) = check_sccs deps rest"
| "check_sccs deps ([d] # rest) =
    (if get_decl_name d \<in> set (deps d)
     then Inl [TyErr_RecursiveDeclarations (bab_declaration_location d) [get_decl_name d]]
     else (case check_sccs deps rest of
             Inl errs \<Rightarrow> Inl errs
           | Inr ds \<Rightarrow> Inr (d # ds)))"
| "check_sccs deps (scc # rest) =
    Inl [TyErr_RecursiveDeclarations (bab_declaration_location (hd scc))
           (map get_decl_name scc)]"

(* The main function to sort the BabDeclarations into dependency order.
   Calls analyze_dependencies_generic (which itself calls Kosaraju) to find SCCs, then
   uses check_sccs to rule out dependency cycles (recursive declarations are not currently
   permitted). *)
definition sort_declarations ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> BabDeclaration list
   \<Rightarrow> TypeError list + BabDeclaration list" where
  "sort_declarations env elabEnv decls =
     (case decls of
        [] \<Rightarrow> Inr []
      | d0 # _ \<Rightarrow>
          (let declNames = fset_of_list (map get_decl_name decls);
               deps = decl_deps env elabEnv declNames
           in case analyze_dependencies_generic decls get_decl_name deps of
                Inl _ \<Rightarrow> Inl [TyErr_InternalError_DependencyAnalysis
                                (bab_declaration_location d0)]
              | Inr sccs \<Rightarrow> check_sccs deps sccs))"

(* check_sccs returns exactly the declarations of its SCC list, concatenated
   in topological order: the multiset is preserved. *)
lemma check_sccs_mset:
  assumes "check_sccs deps sccs = Inr ds"
  shows "mset ds = mset (concat sccs)"
  using assms
proof (induction deps sccs arbitrary: ds rule: check_sccs.induct)
  case 1
  then show ?case by auto
next
  case (2 deps rest)
  then show ?case by simp
next
  case (3 deps d rest)
  from "3.prems" have cond: "get_decl_name d \<notin> set (deps d)"
    by (auto split: if_splits)
  from "3.prems" cond obtain ds' where
    rest_ok: "check_sccs deps rest = Inr ds'" and ds_eq: "ds = d # ds'"
    by (auto split: sum.splits)
  show ?case
    using "3.IH"[OF cond rest_ok] by (simp add: ds_eq)
next
  case 4
  then show ?case by auto
qed

(* Hence sort_declarations returns a permutation of its input: the dependency
   analysis emits every input declaration exactly once across its SCCs
   (analyze_dependencies_generic_permutation), and check_sccs concatenates
   them. *)
lemma sort_declarations_mset:
  assumes ok: "sort_declarations env elabEnv decls = Inr sortedDecls"
  shows "mset sortedDecls = mset decls"
proof (cases decls)
  case Nil
  then have "sortedDecls = []"
    using ok unfolding sort_declarations_def by simp
  then show ?thesis using Nil by simp
next
  case (Cons d ds)
  let ?deps = "decl_deps env elabEnv (fset_of_list (map get_decl_name decls))"
  obtain sccs where
    ana: "analyze_dependencies_generic decls get_decl_name ?deps = Inr sccs" and
    chk: "check_sccs ?deps sccs = Inr sortedDecls"
    using ok unfolding sort_declarations_def Let_def
    by (auto simp: Cons split: sum.splits)
  have "mset sortedDecls = mset (concat sccs)"
    by (rule check_sccs_mset[OF chk])
  also have "\<dots> = mset decls"
    by (rule analyze_dependencies_generic_permutation[OF ana])
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
  "CompiledModule list \<Rightarrow> string fset \<Rightarrow> BabDeclaration list
   \<Rightarrow> ElabModuleError + CompiledModule" where
  "elab_face deps ownAbstract decls =
     (case link_modules (map fst deps) of
        Inl le \<Rightarrow> Inl (EM_LinkError le)
      | Inr ctx \<Rightarrow>
          (let e = elabenv_union (map snd deps)
           in case sort_declarations (CM_TyEnv ctx) e decls of
                Inl errs \<Rightarrow> Inl (EM_TypeErrors errs)
              | Inr sortedDecls \<Rightarrow>
                  (case elab_declarations (CM_TyEnv ctx) e ownAbstract sortedDecls of
                     Inl errs \<Rightarrow> Inl (EM_TypeErrors errs)
                   | Inr (m, foldEnv) \<Rightarrow> Inr (m, elabenv_delta e foldEnv))))"

(* The main elab_module function. *)
definition elab_module ::
  "BabModule \<Rightarrow> CompiledModule list \<Rightarrow> CompiledModule list
   \<Rightarrow> ElabModuleError + (CompiledModule \<times> CompiledModule)" where
  "elab_module bm intDeps implDeps =
    (let checkErrs = check_unique_names (Mod_Interface bm) (Mod_Implementation bm)
                     @ check_impl_definitions (Mod_Implementation bm)
     in if checkErrs \<noteq> [] then Inl (EM_TypeErrors checkErrs)
        else case elab_face intDeps {||} (Mod_Interface bm) of
               Inl err \<Rightarrow> Inl err
             | Inr (intMod, intEE) \<Rightarrow>
                 (case elab_face (intDeps @ implDeps @ [(intMod, intEE)])
                         (TE_TypeVars (CM_TyEnv intMod))
                         (Mod_Implementation bm) of
                    Inl err \<Rightarrow> Inl err
                  | Inr (implMod, implEE) \<Rightarrow>
                      (let compErrs = check_completeness (Mod_Interface bm) intMod implMod
                       in if compErrs \<noteq> []
                          then Inl (EM_TypeErrors compErrs)
                          else Inr ((intMod, intEE), (implMod, implEE)))))"

end
