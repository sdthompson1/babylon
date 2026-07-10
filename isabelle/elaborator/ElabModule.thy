theory ElabModule
  imports ElabDecl "../bab/BabNames" "../core/LinkModules" "../graph/Dependency"
begin

(* Per-module orchestration: elaborate the two faces of a BabModule.

   The caller (the pipeline) supplies the unlinked interface CoreModules of
   the module's interface-dependency and implementation-dependency sets (each
   original module exactly once - linked results never compose under the
   strict conflict rule), and the imports' exported elaborator-level data,
   already unioned into a single ElabEnv (overlapping entries agree, by
   global name-uniqueness).

   elab_module then:
    1. runs the purely syntactic cross-face checks (unique names across the
       two faces; declaration-only forms are interface-only);
    2. links the interface-dependency modules into a context A;
    3. sorts the interface declarations into dependency order and elaborates
       them in CM_TyEnv A (an interface realizes nothing, so ownAbstract is
       empty), giving the unlinked interface and the exported ElabEnv data;
    4. links the implementation-dependency modules plus the just-produced
       unlinked interface into a context B;
    5. sorts and elaborates the implementation declarations in CM_TyEnv B,
       with ownAbstract = the interface's abstract types, giving the unlinked
       implementation;
    6. checks per-module completeness (everything the module declares is
       defined by the module itself);
    7. returns (unlinked interface, unlinked implementation, exported
       ElabEnv data). *)


(* ========================================================================== *)
(* Declaration classification                                                 *)
(* ========================================================================== *)

(* A declaration without a definition: a const without a value, a non-extern
   function without a body, or a typedef without a right-hand side (an
   abstract type). These are only allowed in an interface. Everything else -
   including an extern function (whose implementation arrives at interpreter-
   state creation) and a datatype - is a definition. *)
fun is_decl_only :: "BabDeclaration \<Rightarrow> bool" where
  "is_decl_only (BabDecl_Const dc) = (DC_Value dc = None)"
| "is_decl_only (BabDecl_Function df) = (DF_Body df = None \<and> \<not> DF_Extern df)"
| "is_decl_only (BabDecl_Datatype dd) = False"
| "is_decl_only (BabDecl_Typedef dt) = (DT_Definition dt = None)"


(* ========================================================================== *)
(* Syntactic cross-face checks                                                *)
(* ========================================================================== *)

(* Names must be unique within each face. Across the two faces the same name
   may appear once in each, provided the interface occurrence is a
   declaration (no rhs/body) and the implementation occurrence a definition -
   the declare-then-define idiom. Anything else is a duplicate. *)
definition check_unique_names ::
  "BabDeclaration list \<Rightarrow> BabDeclaration list \<Rightarrow> TypeError list" where
  "check_unique_names intf impl =
     (case first_duplicate_name get_decl_name intf of
        Some dup \<Rightarrow>
          (case find (\<lambda>d. get_decl_name d = dup) intf of
             Some d \<Rightarrow> [TyErr_DuplicateName (bab_declaration_location d) dup]
           | None \<Rightarrow> [])
      | None \<Rightarrow> [])
     @ (case first_duplicate_name get_decl_name impl of
          Some dup \<Rightarrow>
            (case find (\<lambda>d. get_decl_name d = dup) impl of
               Some d \<Rightarrow> [TyErr_DuplicateName (bab_declaration_location d) dup]
             | None \<Rightarrow> [])
        | None \<Rightarrow> [])
     @ concat (map (\<lambda>d.
          (case find (\<lambda>di. get_decl_name di = get_decl_name d) intf of
             None \<Rightarrow> []
           | Some di \<Rightarrow>
               if is_decl_only di \<and> \<not> is_decl_only d then []
               else [TyErr_DuplicateName (bab_declaration_location d) (get_decl_name d)]))
          impl)"

(* Declaration-only forms may not appear in an implementation: such a
   declaration is always dead (a later same-face definition would be a
   duplicate name, and no other module may define this module's names), so it
   is rejected outright, for a well-located error. *)
definition check_impl_definitions :: "BabDeclaration list \<Rightarrow> TypeError list" where
  "check_impl_definitions impl =
     concat (map (\<lambda>d. if is_decl_only d
                      then [TyErr_DeclarationOnlyInImplementation
                              (bab_declaration_location d) (get_decl_name d)]
                      else [])
                 impl)"


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

(* Split the sorter's output: a non-singleton SCC is a mutual-recursion
   error; a singleton whose own dependency list contains its own name is a
   self-recursion error (a self-loop is a singleton SCC, which the
   non-singleton check cannot catch); otherwise concatenate in topological
   order. *)
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

(* Sort a face's declarations into dependency order. Cyclic dependencies are
   errors: the language supports no recursion (this is also what lets every
   datatype be laid out as a finite fixed-size block). The underlying
   dependency analysis cannot itself fail here: duplicate names are checked
   before sorting, and dependencies are filtered to names present in the
   list. *)
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


(* ========================================================================== *)
(* Per-module completeness                                                    *)
(* ========================================================================== *)

(* Everything a module declares must be defined by the module itself: every
   declared constant/function must be defined in one of the two faces (an
   extern function counts - its CM_Functions entry has CF_Body = None), and
   every abstract type must be realized by the implementation. This is
   necessarily the module's own error and this is the only place it can be
   reported well-located: the strict link makes even re-declaring the name in
   another module a conflict, and a definition requires its own declaration,
   so no other module can ever supply the missing definition. Only interface
   declarations need checking: declaration-only forms in the implementation
   were already rejected. *)
definition check_completeness ::
  "BabDeclaration list \<Rightarrow> CoreModule \<Rightarrow> CoreModule \<Rightarrow> TypeError list" where
  "check_completeness intf intMod implMod =
     concat (map (\<lambda>d.
       case d of
         BabDecl_Const dc \<Rightarrow>
           (if DC_Value dc = None
               \<and> DC_Name dc |\<notin>| fmdom (CM_GlobalVars intMod)
               \<and> DC_Name dc |\<notin>| fmdom (CM_GlobalVars implMod)
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
(* elab_module                                                                *)
(* ========================================================================== *)

datatype ElabModuleError =
  EM_LinkError LinkError
  | EM_TypeErrors "TypeError list"

definition elab_module ::
  "BabModule \<Rightarrow> CoreModule list \<Rightarrow> CoreModule list \<Rightarrow> ElabEnv
   \<Rightarrow> ElabModuleError + (CoreModule \<times> CoreModule \<times> ElabEnv)" where
  "elab_module bm intDeps implDeps initElabEnv =
    (let checkErrs = check_unique_names (Mod_Interface bm) (Mod_Implementation bm)
                     @ check_impl_definitions (Mod_Implementation bm)
     in if checkErrs \<noteq> [] then Inl (EM_TypeErrors checkErrs)
        else case link_modules intDeps of
               Inl le \<Rightarrow> Inl (EM_LinkError le)
             | Inr a \<Rightarrow>
                 (case sort_declarations (CM_TyEnv a) initElabEnv (Mod_Interface bm) of
                    Inl errs \<Rightarrow> Inl (EM_TypeErrors errs)
                  | Inr sortedInt \<Rightarrow>
                      (case elab_declarations (CM_TyEnv a) initElabEnv {||} sortedInt of
                         Inl errs \<Rightarrow> Inl (EM_TypeErrors errs)
                       | Inr (intMod, expElabEnv) \<Rightarrow>
                           (case link_modules (implDeps @ [intMod]) of
                              Inl le \<Rightarrow> Inl (EM_LinkError le)
                            | Inr b \<Rightarrow>
                                (case sort_declarations (CM_TyEnv b) expElabEnv
                                        (Mod_Implementation bm) of
                                   Inl errs \<Rightarrow> Inl (EM_TypeErrors errs)
                                 | Inr sortedImpl \<Rightarrow>
                                     (case elab_declarations (CM_TyEnv b) expElabEnv
                                             (TE_TypeVars (CM_TyEnv intMod)) sortedImpl of
                                        Inl errs \<Rightarrow> Inl (EM_TypeErrors errs)
                                      | Inr (implMod, _) \<Rightarrow>
                                          (let compErrs = check_completeness
                                                            (Mod_Interface bm) intMod implMod
                                           in if compErrs \<noteq> []
                                              then Inl (EM_TypeErrors compErrs)
                                              else Inr (intMod, implMod, expElabEnv))))))))"

end
