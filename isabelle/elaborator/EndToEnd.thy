theory EndToEnd
  imports ElabProgramCorrect "../interpreter/MakeInterpStateCorrect"
begin

(* The end-to-end capstone: whatever the compiler accepts is type-safe to
   run.

   If elab_program accepts a program, whole_program_link links it (and the
   supplied extern functions satisfy extern_fun_contract), then
   make_interp_state on the whole-program module yields a state satisfying
   state_matches_env against the normalized module's type environment, with
   the empty store typing - so the type soundness theorems govern every
   evaluation performed in it.

   The proof is pure composition: elab_program_well_typed gives
   core_module_well_typed prog, elab_program_closed gives
   core_module_closed prog, and make_interp_state_matches_env does the rest. *)

(* Note: the hypothesis `mk` (that `make_interp_state` succeeds) is needed only to rule
   out the case where not all of the required extern functions have been provided. If the
   first three hypotheses below are true, and additionally the domain of `externs` covers
   everything needed by the program, then it could be proved that `make_interp_state`
   will definitely succeed in this case (but we haven't actually formalized this
   as a theorem). *)

theorem compile_program_interp_state:
  assumes cp: "elab_program modules = Inr ps"
      and link: "whole_program_link ps = Inr prog"
      and externs_ok: "\<And>name info externFun.
            \<lbrakk> fmlookup (TE_Functions (CM_TyEnv (normalize_module prog))) name = Some info;
              fmlookup externs name = Some externFun \<rbrakk> \<Longrightarrow>
            extern_fun_contract (CM_TyEnv (normalize_module prog)) info externFun"
      and mk: "make_interp_state world externs prog = Inr state"
  shows "state_matches_env state (CM_TyEnv (normalize_module prog)) []"
  by (rule make_interp_state_matches_env[OF elab_program_well_typed[OF cp link]
        elab_program_closed[OF cp link] externs_ok mk])

end
