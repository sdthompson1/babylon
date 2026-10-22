theory MiniCFuelMono
  imports MiniCSemantics
begin

(* ========================================================================== *)
(* MiniC: fuel monotonicity                                                   *)
(* ========================================================================== *)

(* A result that is not "insufficient fuel" is stable under adding fuel. This
   is the lemma that lets the simulation proof (stage 6) combine the fuel
   bounds of sub-executions: each lemma there produces "some fuel suffices",
   and the maximum of the fuels then suffices for all of them.

   First the one-step version, by the mutual induction of the interpreter. *)

lemma fuel_mono_Suc:
  "exec_stmt f ctx st s \<noteq> Inl MErr_Fuel \<longrightarrow> exec_stmt (Suc f) ctx st s = exec_stmt f ctx st s"
  "exec_stmts f ctx st ss \<noteq> Inl MErr_Fuel \<longrightarrow> exec_stmts (Suc f) ctx st ss = exec_stmts f ctx st ss"
  "exec_scope f ctx st body \<noteq> Inl MErr_Fuel \<longrightarrow> exec_scope (Suc f) ctx st body = exec_scope f ctx st body"
  "call_fun f ctx st fn vals \<noteq> Inl MErr_Fuel \<longrightarrow> call_fun (Suc f) ctx st fn vals = call_fun f ctx st fn vals"
proof (induction f ctx st s and f ctx st ss and f ctx st body and f ctx st fn vals
       rule: exec_stmt_exec_stmts_exec_scope_call_fun.induct)
  case (9 fuel ctx st body)
  \<comment> \<open>MS_Loop: the body (a scope), then the loop itself at the same reduced
      fuel. Done by hand, because the recursive call at `fuel` must not be
      unfolded by the simplifier before the induction hypothesis is applied.\<close>
  show ?case
  proof
    assume ne: "exec_stmt (Suc fuel) ctx st (MS_Loop body) \<noteq> Inl MErr_Fuel"
    show "exec_stmt (Suc (Suc fuel)) ctx st (MS_Loop body) = exec_stmt (Suc fuel) ctx st (MS_Loop body)"
    proof (cases "exec_scope fuel ctx st body")
      case (Inl err)
      with ne have "err \<noteq> MErr_Fuel" by simp
      with Inl "9.IH"(1) have "exec_scope (Suc fuel) ctx st body = Inl err" by simp
      with Inl show ?thesis by simp
    next
      case (Inr r)
      then obtain st' out where r: "r = (st', out)" by (cases r) auto
      from Inr "9.IH"(1) have sc: "exec_scope (Suc fuel) ctx st body = Inr (st', out)"
        by (simp add: r)
      show ?thesis
      proof (cases out)
        case MO_Normal
        with ne Inr r have ne': "exec_stmt fuel ctx st' (MS_Loop body) \<noteq> Inl MErr_Fuel" by simp
        have IH2: "exec_stmt (Suc fuel) ctx st' (MS_Loop body) = exec_stmt fuel ctx st' (MS_Loop body)"
          using "9.IH"(2)[OF Inr[unfolded r] refl MO_Normal] ne' by simp
        have L: "exec_stmt (Suc (Suc fuel)) ctx st (MS_Loop body) = exec_stmt (Suc fuel) ctx st' (MS_Loop body)"
          using sc MO_Normal by (simp only: exec_stmt.simps(9) sum.case prod.case MOutcome.case)
        have R: "exec_stmt (Suc fuel) ctx st (MS_Loop body) = exec_stmt fuel ctx st' (MS_Loop body)"
          using Inr r MO_Normal by simp
        show ?thesis unfolding L R by (rule IH2)
      next
        case MO_Break
        with Inr r sc show ?thesis by simp
      next
        case (MO_Return v)
        with Inr r sc show ?thesis by simp
      qed
    qed
  qed
qed (auto split: option.splits sum.splits prod.splits MOutcome.splits if_splits)


(* The general versions. *)

lemma exec_stmt_fuel_mono:
  assumes "exec_stmt f ctx st s \<noteq> Inl MErr_Fuel" and "f \<le> f'"
  shows "exec_stmt f' ctx st s = exec_stmt f ctx st s"
  using assms(2)
proof (induction rule: dec_induct)
  case base show ?case by simp
next
  case (step n)
  then show ?case using assms(1) fuel_mono_Suc(1)[of n ctx st s] by simp
qed

lemma exec_stmts_fuel_mono:
  assumes "exec_stmts f ctx st ss \<noteq> Inl MErr_Fuel" and "f \<le> f'"
  shows "exec_stmts f' ctx st ss = exec_stmts f ctx st ss"
  using assms(2)
proof (induction rule: dec_induct)
  case base show ?case by simp
next
  case (step n)
  then show ?case using assms(1) fuel_mono_Suc(2)[of n ctx st ss] by simp
qed

lemma exec_scope_fuel_mono:
  assumes "exec_scope f ctx st body \<noteq> Inl MErr_Fuel" and "f \<le> f'"
  shows "exec_scope f' ctx st body = exec_scope f ctx st body"
  using assms(2)
proof (induction rule: dec_induct)
  case base show ?case by simp
next
  case (step n)
  then show ?case using assms(1) fuel_mono_Suc(3)[of n ctx st body] by simp
qed

lemma call_fun_fuel_mono:
  assumes "call_fun f ctx st fn vals \<noteq> Inl MErr_Fuel" and "f \<le> f'"
  shows "call_fun f' ctx st fn vals = call_fun f ctx st fn vals"
  using assms(2)
proof (induction rule: dec_induct)
  case base show ?case by simp
next
  case (step n)
  then show ?case using assms(1) fuel_mono_Suc(4)[of n ctx st fn vals] by simp
qed

(* The forms the simulation proof will use: a normal result persists. *)

lemma exec_stmts_Inr_mono:
  "exec_stmts f ctx st ss = Inr r \<Longrightarrow> f \<le> f' \<Longrightarrow> exec_stmts f' ctx st ss = Inr r"
  using exec_stmts_fuel_mono[of f ctx st ss f'] by simp

lemma call_fun_Inr_mono:
  "call_fun f ctx st fn vals = Inr r \<Longrightarrow> f \<le> f' \<Longrightarrow> call_fun f' ctx st fn vals = Inr r"
  using call_fun_fuel_mono[of f ctx st fn vals f'] by simp

lemma run_program_fuel_mono:
  assumes "run_program f enc externs prog w \<noteq> Inl MErr_Fuel" and "f \<le> f'"
  shows "run_program f' enc externs prog w = run_program f enc externs prog w"
proof (cases "alloc_globals enc w empty_mem fmempty (MP_Globals prog)")
  case None
  then show ?thesis by (simp add: run_program_def)
next
  case (Some mg)
  then obtain m genv where ag: "alloc_globals enc w empty_mem fmempty (MP_Globals prog) = Some (m, genv)"
    by (cases mg) auto
  define ctx where "ctx = \<lparr> MC_Enc = enc, MC_Prog = prog, MC_Externs = externs \<rparr>"
  define st where "st = \<lparr> MS_Mem = m, MS_Globals = genv, MS_Locals = fmempty,
                          MS_Stack = [], MS_World = w \<rparr>"
  have ne: "call_fun f ctx st ''main'' [] \<noteq> Inl MErr_Fuel"
    using assms(1) ag
    by (auto simp: run_program_def Let_def ctx_def st_def split: sum.splits option.splits prod.splits)
  then have "call_fun f' ctx st ''main'' [] = call_fun f ctx st ''main'' []"
    using assms(2) by (rule call_fun_fuel_mono)
  then show ?thesis using ag by (simp add: run_program_def Let_def ctx_def st_def)
qed

end
