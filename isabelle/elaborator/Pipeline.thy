theory Pipeline
  imports "../bab_dependency/BabDependency" ElabModule
begin

(* The compilation pipeline (LINKING.md step 7): turns a list of BabModules
   (already loaded and renamed by the front end) into elaborated
   CoreModules, and finally into a single closed whole-program CoreModule
   usable to generate an InterpState.

   The pipeline only *sequences*: every check lives in elab_module (or the
   functions it calls) and the pipeline merely propagates their errors.
   Under the strict linking semantics, linked results never compose, so the
   pipeline state stores only *original* (unlinked) elaboration results;
   every link is computed at its point of use, as link_modules over
   originals, each exactly once. Where a later pass wants a linked module,
   it is derived on demand:

    - linked interface of a module: link_modules of the M_CompiledInterface
      CoreModules of its M_IntDeps plus its own;
    - linked implementation: link_modules of the M_CompiledInterface
      CoreModules of its M_ImplDeps (which include its own interface) plus
      its own implementation CoreModule.

   No theorems are stated about the pipeline itself - it is plumbing, and
   its layering was chosen so that all verified statements attach to
   elab_module (elab_module_well_typed), link_modules
   (link_preserves_well_typed) and normalize_module. *)


(* ========================================================================== *)
(* Pipeline state                                                             *)
(* ========================================================================== *)

(* Per-module pipeline entry.

   M_IntDeps is the set of names of *all* modules whose interfaces this
   module's interface transitively depends on: the union, over the
   interface imports, of the import itself plus the import's own M_IntDeps.
   A diamond (two imports sharing a dependency) contributes it once - set
   union is what makes the strict linking rule safe.

   M_ImplDeps is the same for the implementation face, whose "imports" are
   the module's own interface plus the implementation imports; so it is the
   module's own name, its M_IntDeps, and the implementation imports with
   their M_IntDeps. It is the name set whose interfaces the implementation
   face is elaborated against (plus its own interface CoreModule).

   The compiled fields hold the raw, *unlinked* results of elaborating each
   face's declarations: the CoreModule plus the face's ElabEnv delta
   (elaborator-only data not recoverable from a CoreModule). The
   implementation's ElabEnv half currently has no consumer (implementations
   are never imported); it is stored for uniformity. There are no *linked*
   fields: linked results never compose, so nothing in the pipeline could
   consume one, and each is a pure function of the fields above. *)
record PipelineModule =
  M_InterfaceImports :: "string list"
  M_ImplementationImports :: "string list"
  M_IntDeps :: "string fset"
  M_ImplDeps :: "string fset"
  M_CompiledInterface :: CompiledModule
  M_CompiledImplementation :: CompiledModule

type_synonym PipelineState = "(string, PipelineModule) fmap"

datatype PipelineError =
  PE_DependencyError BabDependencyError
  | PE_MissingModule string
      (* a name was not present in the pipeline state; unreachable when the
         modules come from the front end (imports resolve) and were sorted
         by analyze_dependencies (dependencies are processed first) *)
  | PE_ElabError string ElabModuleError   (* module name, error *)
  | PE_LinkError LinkError                (* whole-program link *)


(* ========================================================================== *)
(* The fold step                                                              *)
(* ========================================================================== *)

(* Look up each named module's pipeline entry, in order. *)
fun lookup_entries ::
  "PipelineState \<Rightarrow> string list \<Rightarrow> (PipelineError, PipelineModule list) sum" where
  "lookup_entries ps [] = Inr []"
| "lookup_entries ps (n # ns) =
     (case fmlookup ps n of
        None \<Rightarrow> Inl (PE_MissingModule n)
      | Some e \<Rightarrow>
          (case lookup_entries ps ns of
             Inl err \<Rightarrow> Inl err
           | Inr es \<Rightarrow> Inr (e # es)))"

(* The transitive interface-dependency set contributed by a face's direct
   imports: each import itself plus that import's M_IntDeps (already
   transitively closed - the fold visits dependencies first). *)
definition face_dep_set :: "string list \<Rightarrow> PipelineModule list \<Rightarrow> string fset" where
  "face_dep_set names entries =
     funion_list (map2 (\<lambda>n e. finsert n (M_IntDeps e)) names entries)"

(* Process one BabModule: compute the two dependency sets, gather the two
   disjoint lists of compiled interfaces - those named by M_IntDeps, and
   those named by M_ImplDeps - M_IntDeps - {own name} (the modules only the
   implementation face sees; each original module once across both lists) -
   and hand them with the BabModule to elab_module, which does all linking
   and ElabEnv unioning itself. *)
definition pipeline_step ::
  "PipelineState \<Rightarrow> BabModule \<Rightarrow> (PipelineError, PipelineState) sum" where
  "pipeline_step ps bm =
     (let name = Mod_Name bm;
          intImports = map Imp_ModuleName (Mod_InterfaceImports bm);
          implImports = map Imp_ModuleName (Mod_ImplementationImports bm)
      in case lookup_entries ps intImports of
           Inl err \<Rightarrow> Inl err
         | Inr intEntries \<Rightarrow>
             (case lookup_entries ps implImports of
                Inl err \<Rightarrow> Inl err
              | Inr implEntries \<Rightarrow>
                  (let intDeps = face_dep_set intImports intEntries;
                       implDeps = finsert name
                         (intDeps |\<union>| face_dep_set implImports implEntries);
                       implOnly = implDeps |-| intDeps |-| {|name|}
                   in case lookup_entries ps (sorted_list_of_fset intDeps) of
                        Inl err \<Rightarrow> Inl err
                      | Inr intCtx \<Rightarrow>
                          (case lookup_entries ps (sorted_list_of_fset implOnly) of
                             Inl err \<Rightarrow> Inl err
                           | Inr implCtx \<Rightarrow>
                               (case elab_module bm
                                       (map M_CompiledInterface intCtx)
                                       (map M_CompiledInterface implCtx) of
                                  Inl err \<Rightarrow> Inl (PE_ElabError name err)
                                | Inr (compInt, compImpl) \<Rightarrow>
                                    Inr (fmupd name
                                          \<lparr> M_InterfaceImports = intImports,
                                            M_ImplementationImports = implImports,
                                            M_IntDeps = intDeps,
                                            M_ImplDeps = implDeps,
                                            M_CompiledInterface = compInt,
                                            M_CompiledImplementation = compImpl \<rparr>
                                          ps))))))"

(* Fold across the modules; they must already be in dependency order. *)
fun pipeline_fold ::
  "PipelineState \<Rightarrow> BabModule list \<Rightarrow> (PipelineError, PipelineState) sum" where
  "pipeline_fold ps [] = Inr ps"
| "pipeline_fold ps (bm # bms) =
     (case pipeline_step ps bm of
        Inl err \<Rightarrow> Inl err
      | Inr ps' \<Rightarrow> pipeline_fold ps' bms)"


(* ========================================================================== *)
(* Whole-program link and top-level entry point                               *)
(* ========================================================================== *)

(* The whole-program module: link_modules over *every* module's interface
   and implementation CoreModules, each original exactly once (not a link
   of derived linked modules, which would multiply-define every shared
   dependency). The result is closed, so it can form an InterpState. The
   modules are supplied in dependency order, each interface before its
   implementation. *)
definition whole_program_link ::
  "PipelineState \<Rightarrow> BabModule list \<Rightarrow> (PipelineError, CoreModule) sum" where
  "whole_program_link ps modules =
     (case lookup_entries ps (map Mod_Name modules) of
        Inl err \<Rightarrow> Inl err
      | Inr entries \<Rightarrow>
          (case link_modules
                  (concat (map (\<lambda>e. [fst (M_CompiledInterface e),
                                     fst (M_CompiledImplementation e)]) entries)) of
             Inl le \<Rightarrow> Inl (PE_LinkError le)
           | Inr prog \<Rightarrow> Inr prog))"

(* Sort the modules into dependency order, elaborate each, then link the
   whole program. Returns the final pipeline state (for per-module passes,
   which derive linked modules on demand) together with the closed
   whole-program CoreModule. *)
definition compile_program ::
  "BabModule list \<Rightarrow> (PipelineError, PipelineState \<times> CoreModule) sum" where
  "compile_program modules =
     (case analyze_dependencies modules of
        Inl err \<Rightarrow> Inl (PE_DependencyError err)
      | Inr sortedModules \<Rightarrow>
          (case pipeline_fold fmempty sortedModules of
             Inl err \<Rightarrow> Inl err
           | Inr ps \<Rightarrow>
               (case whole_program_link ps sortedModules of
                  Inl err \<Rightarrow> Inl err
                | Inr prog \<Rightarrow> Inr (ps, prog))))"

end
