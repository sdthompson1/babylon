theory EndToEnd
  imports PipelineCorrect "../interpreter/MakeInterpStateCorrect"
begin

(* The end-to-end capstone: whatever the compiler accepts is type-safe to
   run.

   If compile_program accepts a program (and the supplied extern functions
   satisfy extern_fun_contract), then make_interp_state on the whole-program
   module yields a state satisfying state_matches_env against the normalized
   module's type environment, with the empty store typing - so the type
   soundness theorems govern every evaluation performed in it.

   The proof is pure composition: compile_program_well_typed gives
   core_module_well_typed prog, compile_program_closed gives
   core_module_closed prog, and make_interp_state_matches_env does the rest. *)
theorem compile_program_interp_state:
  assumes cp: "compile_program modules = Inr (ps, prog)"
      and decls: "\<forall>bm \<in> set modules. list_all decl_tyvars_fresh_ok (Mod_Interface bm)
                    \<and> list_all decl_tyvars_fresh_ok (Mod_Implementation bm)"
      and externs_ok: "\<And>name info externFun.
            \<lbrakk> fmlookup (TE_Functions (CM_TyEnv (normalize_module prog))) name = Some info;
              fmlookup externs name = Some externFun \<rbrakk> \<Longrightarrow>
            extern_fun_contract (CM_TyEnv (normalize_module prog)) info externFun"
      and mk: "make_interp_state fuel world externs prog = Inr state"
  shows "state_matches_env state (CM_TyEnv (normalize_module prog)) []"
  by (rule make_interp_state_matches_env[OF compile_program_well_typed[OF cp decls]
        compile_program_closed[OF cp decls] externs_ok mk])

end
