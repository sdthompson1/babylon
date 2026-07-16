theory ElabProgram
  imports "../bab_dependency/BabDependency" ElabModule
begin

(* Whole-program elaborator.

   `elab_program`: Turns a list of BabModules (already loaded and renamed by the front end)
   into elaborated CoreModules.

   `whole_program_link`: Links the output of elab_program into a single closed CoreModule,
   from which an InterpState can be generated.

   `module_impl_link`: Links a single module with all its imported interfaces, giving a
   single CoreModule that can be separately verified or code-generated.

   See also ElabProgramCorrect.thy, which proves that the results of elab_program +
   whole_program_link, or elab_program + module_impl_link, when successful, are always
   well-typed as CoreModules (and also closed, in the case of whole_program_link).
*)


(* ========================================================================== *)
(* Pipeline state and errors                                                  *)
(* ========================================================================== *)

(* Per-module pipeline entry. *)
record PipelineModule =
  (* Module names directly imported by this module's interface *)
  M_InterfaceImports :: "string list"

  (* Module names directly imported by this module's implementation *)
  M_ImplementationImports :: "string list"

  (* Transitive closure of M_InterfaceImports: union of all the interface imports together
     with their own M_IntDeps. *)
  M_IntDeps :: "string fset"

  (* Transitive closure of M_InterfaceImports plus M_ImplementationImports, together with
     this module's own name (an implementation is considered to "import" its own interface). *)
  M_ImplDeps :: "string fset"

  (* The (unlinked) result of elaborating this module's interface. *)
  M_CompiledInterface :: CompiledModule

  (* The (unlinked) result of elaborating this module's implementation. Note that only the
     CoreModule half is used; the ElabEnv half is not needed, because nothing can "import"
     from an implementation, but is kept anyway for completeness. *)
  M_CompiledImplementation :: CompiledModule


(* The pipeline state is a map from module name to a PipelineModule record. *)
type_synonym PipelineState = "(string, PipelineModule) fmap"


(* Pipeline errors. *)
datatype PipelineError =
  (* Module dependency error (e.g. circular imports). *)
  PE_DependencyError BabDependencyError

  (* Missing module (normally not possible as it would be caught by the loader). *)
  | PE_MissingModule string

  (* Error from the elaborator (e.g. a type error). *)
  | PE_ElabError string ElabModuleError   (* module name, error *)


(* ========================================================================== *)
(* The fold step                                                              *)
(* ========================================================================== *)

(* Look up each named module's pipeline entry, in order. *)
fun lookup_entries ::
  "PipelineState \<Rightarrow> string list \<Rightarrow> PipelineError + PipelineModule list" where 
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

(* Process one BabModule: gather the dependencies, call elab_module, and
   update the PipelineState (or return an error). *)
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
  "PipelineState \<Rightarrow> BabModule list \<Rightarrow> PipelineError + PipelineState" where
  "pipeline_fold ps [] = Inr ps"
| "pipeline_fold ps (bm # bms) =
     (case pipeline_step ps bm of
        Inl err \<Rightarrow> Inl err
      | Inr ps' \<Rightarrow> pipeline_fold ps' bms)"


(* ========================================================================== *)
(* elab_program *)
(* ========================================================================== *)

(* Sort the modules into dependency order, then elaborate them.
   Returns the final pipeline state, which is basically a dictionary mapping each
   module-name to a pair of elaborated CoreModules (one for the interface, one for
   the implementation). *)
definition elab_program ::
  "BabModule list \<Rightarrow> PipelineError + PipelineState" where
  "elab_program modules =
     (case analyze_dependencies modules of
        Inl err \<Rightarrow> Inl (PE_DependencyError err)
      | Inr sortedModules \<Rightarrow>
          pipeline_fold fmempty sortedModules)"


(* ========================================================================== *)
(* whole_program_link *)
(* ========================================================================== *)

(* Link all the CoreModules contained in a PipelineState into a single closed CoreModule. *)
definition whole_program_link ::
  "PipelineState \<Rightarrow> LinkError + CoreModule" where
  "whole_program_link ps =
     (let entries = map (the \<circ> fmlookup ps) (sorted_list_of_fset (fmdom ps))
      in link_modules
               (concat (map (\<lambda>e. [fst (M_CompiledInterface e),
                                  fst (M_CompiledImplementation e)]) entries)))"


(* ========================================================================== *)
(* module_impl_link *)
(* ========================================================================== *)

(* Link a single module with all of its imported interfaces to produce a single
   CoreModule, suitable for separate code-generation or verification.

   Returns None if the given module name isn't present in the PipelineState. *)
definition module_impl_link ::
  "PipelineState \<Rightarrow> string \<Rightarrow> (LinkError + CoreModule) option" where
  "module_impl_link ps name =
     (case fmlookup ps name of
        None \<Rightarrow> None
      | Some e \<Rightarrow>
          (let entries = map (the \<circ> fmlookup ps) (sorted_list_of_fset (M_ImplDeps e))
           in Some (link_modules
                (map (fst \<circ> M_CompiledInterface) entries
                 @ [fst (M_CompiledImplementation e)]))))"


end
