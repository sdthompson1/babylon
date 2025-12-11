theory CoreInterpFuelMono
  imports CoreInterp
begin

(* ========================================================================== *)
(* Helper lemmas about process_one_arg and fold *)
(* ========================================================================== *)

lemma fold_process_one_arg_error:
  "fold process_one_arg xs (Inl err) = Inl err"
  by (induct xs) simp_all

lemma process_one_arg_val_error:
  "\<exists>e. process_one_arg ((name, vr), refResult, Inl err) acc = Inl e"
  by (cases vr; cases refResult; cases acc) simp_all

lemma process_one_arg_ref_error:
  "\<exists>e. process_one_arg ((name, Ref), Inl err, valResult) acc = Inl e"
  by (cases valResult; cases acc) simp_all

(* If the fold succeeds and an argument is Ref, its lvalue result must be Inr *)
lemma fold_process_one_arg_ref_ok:
  assumes "fold process_one_arg (zip args (zip refResults valResults)) acc = Inr finalState"
    and "length args = length refResults"
    and "length refResults = length valResults"
    and "(i, (name, Ref)) \<in> set (zip [0..<length args] args)"
  shows "\<exists>lval. refResults ! i = Inr lval"
  using assms
proof (induction args arbitrary: refResults valResults acc i)
  case Nil
  then show ?case by simp
next
  case (Cons arg args)
  from Cons.prems(2,3) obtain refResult refResults' valResult' valResults'
    where refResults_eq: "refResults = refResult # refResults'"
      and valResults_eq: "valResults = valResult' # valResults'"
      and len_ref': "length args = length refResults'"
      and len_val': "length refResults' = length valResults'"
    by (cases refResults; cases valResults) auto

  obtain argName argVr where arg_eq: "arg = (argName, argVr)" by (cases arg)

  let ?step = "process_one_arg ((argName, argVr), refResult, valResult') acc"

  have fold_eq: "fold process_one_arg (zip (arg # args) (zip refResults valResults)) acc
               = fold process_one_arg (zip args (zip refResults' valResults')) ?step"
    using refResults_eq valResults_eq arg_eq by simp

  from Cons.prems(4) obtain j where j_bound: "j < length (arg # args)"
    and i_eq: "i = [0..<length (arg # args)] ! j"
    and arg_at_j: "(arg # args) ! j = (name, Ref)"
    by (auto simp: set_zip)
  hence i_eq': "i = j" using j_bound
    by (metis One_nat_def add_diff_inverse_nat diff_Suc_1 diff_Suc_Suc less_zeroE nth_upt)
  hence i_bound: "i < Suc (length args)" and arg_at_i: "(arg # args) ! i = (name, Ref)"
    using j_bound arg_at_j by auto

  show ?case
  proof (cases "i = 0")
    case True
    hence "arg = (name, Ref)" using arg_at_i by simp
    hence argVr_eq: "argVr = Ref" and argName_eq: "argName = name" using arg_eq by auto
    show ?thesis
    proof (cases refResult)
      case (Inl err)
      hence "?step = Inl err" using argVr_eq process_one_arg_ref_error
        by (metis Cons.prems(1) fold_process_one_arg_error old.sum.exhaust
            process_one_arg.simps(5))
      hence "fold process_one_arg (zip args (zip refResults' valResults')) ?step = Inl err"
        by (simp add: fold_process_one_arg_error)
      hence "fold process_one_arg (zip (arg # args) (zip refResults valResults)) acc = Inl err"
        using fold_eq by simp
      thus ?thesis using Cons.prems(1) by simp
    next
      case (Inr lval)
      thus ?thesis using True refResults_eq by simp
    qed
  next
    case False
    hence i_pos: "i > 0" using i_bound by simp
    have tail_in: "(i - 1, (name, Ref)) \<in> set (zip [0..<length args] args)"
    proof -
      from False i_bound have len: "i - 1 < length args" by simp
      have "[0..<length args] ! (i - 1) = i - 1" using len by simp
      moreover have "args ! (i - 1) = (name, Ref)" using arg_at_i False by simp
      ultimately show ?thesis using len by (auto simp: set_zip intro!: exI[of _ "i - 1"])
    qed
    (* Need to show the fold on tail succeeds *)
    have fold_tail: "fold process_one_arg (zip args (zip refResults' valResults')) ?step = Inr finalState"
      using Cons.prems(1) fold_eq by simp
    (* Need ?step = Inr _ for IH *)
    have step_ok: "\<exists>st. ?step = Inr st"
    proof (cases acc)
      case (Inl err)
      hence "?step = Inl err" by simp
      hence "fold process_one_arg (zip args (zip refResults' valResults')) ?step = Inl err"
        by (simp add: fold_process_one_arg_error)
      thus ?thesis using fold_tail by simp
    next
      case (Inr st)
      show ?thesis
      proof (cases argVr)
        case Var
        show ?thesis
        proof (cases valResult')
          case (Inl err)
          hence "\<exists>e. ?step = Inl e" using process_one_arg_val_error Var by simp
          then obtain e where "?step = Inl e" by blast
          thus ?thesis using fold_tail fold_process_one_arg_error by metis
        next
          case (Inr val)
          thus ?thesis using Inr Var arg_eq
            by (metis fold_process_one_arg_error fold_tail obj_sumE)
        qed
      next
        case Ref
        show ?thesis
        proof (cases refResult)
          case (Inl err)
          hence "?step = Inl err" using Ref process_one_arg_ref_error Inr by simp
          thus ?thesis using fold_tail fold_process_one_arg_error by metis
        next
          case ref_ok: (Inr lval)
          show ?thesis
          proof (cases valResult')
            case (Inl err)
            hence "\<exists>e. ?step = Inl e" using process_one_arg_val_error Ref by simp
            then obtain e where "?step = Inl e" by blast
            thus ?thesis using fold_tail fold_process_one_arg_error by metis
          next
            case (Inr val)
            thus ?thesis using Inr Ref ref_ok arg_eq
              by (metis fold_process_one_arg_error fold_tail obj_sumE)
          qed
        qed
      qed
    qed
    then obtain st' where step_eq: "?step = Inr st'" by blast
    have "refResults' ! (i - 1) = refResults ! i"
      using i_pos refResults_eq by (simp add: nth_Cons')
    moreover have "\<exists>lval. refResults' ! (i - 1) = Inr lval"
      using Cons.IH[OF _ len_ref' len_val' tail_in] fold_tail step_eq by simp
    ultimately show ?thesis by simp
  qed
qed

(* More convenient form: if argTm is at position i where fnArg is Ref, lvalue result is Inr *)
lemma fold_process_one_arg_ref_lvalue_ok:
  assumes "fold process_one_arg (zip fnArgs (zip refResults valResults)) acc = Inr finalState"
    and "length fnArgs = length argTms"
    and "length argTms = length refResults"
    and "length refResults = length valResults"
    and "refResults = map f argTms"
    and "(argTm, (name, Ref)) \<in> set (zip argTms fnArgs)"
  shows "\<exists>lval. f argTm = Inr lval"
proof -
  from assms(6) obtain i where i_bound: "i < length argTms"
    and argTm_eq: "argTms ! i = argTm"
    and fnArg_eq: "fnArgs ! i = (name, Ref)"
    by (auto simp: set_zip in_set_conv_nth)
  have "(i, (name, Ref)) \<in> set (zip [0..<length fnArgs] fnArgs)"
    using i_bound fnArg_eq assms(2) by (auto simp: set_zip intro!: exI[of _ i])
  hence "\<exists>lval. refResults ! i = Inr lval"
    using fold_process_one_arg_ref_ok[OF assms(1) _ _ ] assms(2,3,4) by auto
  moreover have "refResults ! i = f argTm"
    using assms(5) argTm_eq i_bound assms(3)
    using nth_map by blast
  ultimately show ?thesis by simp
qed

lemma fold_process_one_arg_all_ok:
  assumes "fold process_one_arg (zip args (zip refResults valResults)) acc = Inr finalState"
    and "length args = length refResults"
    and "length refResults = length valResults"
    and "valResult \<in> set valResults"
  shows "\<exists>val. valResult = Inr val"
  using assms
proof (induction args arbitrary: refResults valResults acc)
  case Nil
  then show ?case by simp
next
  case (Cons arg args)
  from Cons.prems(2,3) obtain refResult refResults' valResult' valResults'
    where refResults_eq: "refResults = refResult # refResults'"
      and valResults_eq: "valResults = valResult' # valResults'"
      and len_ref': "length args = length refResults'"
      and len_val': "length refResults' = length valResults'"
    by (cases refResults; cases valResults) auto

  obtain name vr where arg_eq: "arg = (name, vr)" by (cases arg)

  let ?step = "process_one_arg ((name, vr), refResult, valResult') acc"

  have fold_eq: "fold process_one_arg (zip (arg # args) (zip refResults valResults)) acc
               = fold process_one_arg (zip args (zip refResults' valResults')) ?step"
    using refResults_eq valResults_eq arg_eq by simp

  show ?case
  proof (cases valResult')
    case (Inl err)
    hence "\<exists>e. ?step = Inl e" using process_one_arg_val_error by simp
    then obtain e where "?step = Inl e" by blast
    hence "fold process_one_arg (zip args (zip refResults' valResults')) ?step = Inl e"
      by (simp add: fold_process_one_arg_error)
    hence "fold process_one_arg (zip (arg # args) (zip refResults valResults)) acc = Inl e"
      using fold_eq by simp
    thus ?thesis using Cons.prems(1) by simp
  next
    case (Inr val')
    show ?thesis
    proof (cases "valResult \<in> set valResults'")
      case True
      have fold_tail_ok: "fold process_one_arg (zip args (zip refResults' valResults')) ?step = Inr finalState"
        using Cons.prems(1) fold_eq by simp
      then obtain finalState' where
        fold_ok: "fold process_one_arg (zip args (zip refResults' valResults')) ?step = Inr finalState'"
        by blast
      (* We need acc to be Inr for ?step to potentially be Inr *)
      have step_ok: "\<exists>st. ?step = Inr st"
      proof (cases acc)
        case (Inl err)
        hence "?step = Inl err" by simp
        hence "fold process_one_arg (zip args (zip refResults' valResults')) ?step = Inl err"
          by (simp add: fold_process_one_arg_error)
        thus ?thesis using fold_ok by simp
      next
        case (Inr st)
        show ?thesis using Inr \<open>valResult' = Inr val'\<close> arg_eq
          by (metis fold_ok fold_process_one_arg_error sumE)
      qed
      then obtain st' where step_eq: "?step = Inr st'" by blast
      thus ?thesis using Cons.IH[OF _ len_ref' len_val' True] fold_ok step_eq fold_tail_ok
        by blast
    next
      case False
      hence "valResult = valResult'" using Cons.prems(4) valResults_eq by simp
      thus ?thesis using Inr by simp
    qed
  qed
qed

lemma process_one_arg_more_fuel:
  assumes "interp_term f state argTm \<noteq> Inl InsufficientFuel
            \<longrightarrow> (\<forall>f' \<ge> f. interp_term f' state argTm = interp_term f state argTm)"
    and "interp_lvalue f state argTm \<noteq> Inl InsufficientFuel
            \<longrightarrow> (\<forall>f' \<ge> f. interp_lvalue f' state argTm = interp_lvalue f state argTm)"
    and "process_one_arg (fnArg, interp_lvalue f state argTm, interp_term f state argTm) acc
            \<noteq> Inl InsufficientFuel"
  shows "\<forall>f' \<ge> f.
      process_one_arg (fnArg, interp_lvalue f' state argTm, interp_term f' state argTm) acc
    = process_one_arg (fnArg, interp_lvalue f state argTm, interp_term f state argTm) acc"
proof (cases acc)
  case (Inl err)
  then show ?thesis by simp
next
  case State: (Inr st)
  show ?thesis proof (cases fnArg)
    case (Pair name argType)
    show ?thesis proof (cases argType)
      case Var
      show ?thesis proof (cases "interp_term f state argTm")
        case (Inl err)
        (* For Var, the term result matters. If it's Inl err, that error propagates. *)
        (* The assumption says result \<noteq> InsufficientFuel, so err \<noteq> InsufficientFuel *)
        hence "err \<noteq> InsufficientFuel" using assms(3) State Pair Var by simp
        (* So interp_term f state argTm = Inl err where err \<noteq> InsufficientFuel *)
        (* This means interp_term f state argTm \<noteq> Inl InsufficientFuel, so IH applies *)
        hence "\<forall>f'\<ge>f. interp_term f' state argTm = interp_term f state argTm"
          using assms(1) Inl by auto
        thus ?thesis using Inl State Pair Var by simp
      next
        case (Inr val)
        (* Term succeeded with value val *)
        (* process_one_arg returns Inr state', so no error *)
        (* Need to show term result stays the same with more fuel *)
        have "interp_term f state argTm \<noteq> Inl InsufficientFuel" using Inr by simp
        hence "\<forall>f'\<ge>f. interp_term f' state argTm = interp_term f state argTm"
          using assms(1) by blast
        thus ?thesis using Inr State Pair Var by simp
      qed
    next
      case Ref
      show ?thesis proof (cases "interp_lvalue f state argTm")
        case (Inl err)
        (* For Ref, the lvalue result matters. If it's Inl err, that error propagates. *)
        hence "err \<noteq> InsufficientFuel" using assms(3) State Pair Ref by simp
        hence "\<forall>f'\<ge>f. interp_lvalue f' state argTm = interp_lvalue f state argTm"
          using assms(2) Inl by auto
        thus ?thesis using Inl State Pair Ref by simp
      next
        case (Inr lval)
        (* Lvalue succeeded - now we also need to check the term result *)
        have "interp_lvalue f state argTm \<noteq> Inl InsufficientFuel" using Inr by simp
        hence lv_eq: "\<forall>f'\<ge>f. interp_lvalue f' state argTm = interp_lvalue f state argTm"
          using assms(2) by blast
        hence lv_eq': "\<forall>f'\<ge>f. interp_lvalue f' state argTm = Inr lval"
          using Inr by simp
        (* Destruct lval to match the pattern *)
        obtain addr path where lval_eq: "lval = (addr, path)" by (cases lval)
        (* Now case-analyze the term result *)
        show ?thesis
        proof (cases "interp_term f state argTm")
          case (Inl err')
          (* Term evaluation failed - this will cause process_one_arg to fail *)
          hence "err' \<noteq> InsufficientFuel" using assms(3) State Pair Ref lval_eq Inr by simp
          hence tm_eq: "\<forall>f'\<ge>f. interp_term f' state argTm = Inl err'"
            using assms(1) Inl by auto
          thus ?thesis using State Pair Ref lv_eq' lval_eq Inl by simp
        next
          case (Inr val)
          (* Term evaluation succeeded *)
          have "interp_term f state argTm \<noteq> Inl InsufficientFuel" using Inr by simp
          hence tm_eq: "\<forall>f'\<ge>f. interp_term f' state argTm = Inr val"
            using assms(1) Inr by simp
          (* Now both lvalue and term results are the same for all f' >= f *)
          thus ?thesis using State Pair Ref lv_eq' lval_eq tm_eq by simp
        qed
      qed
    qed
  qed
qed

lemma fold_process_one_arg_more_fuel:
  assumes "\<forall>argTm \<in> set argTms.
            interp_term f state argTm \<noteq> Inl InsufficientFuel
              \<longrightarrow> (\<forall>f' \<ge> f. interp_term f' state argTm = interp_term f state argTm)"
    and "\<forall>argTm \<in> set argTms.
            interp_lvalue f state argTm \<noteq> Inl InsufficientFuel
              \<longrightarrow> (\<forall>f' \<ge> f. interp_lvalue f' state argTm = interp_lvalue f state argTm)"
    and "length argTms = length fnArgs"
    and "fold process_one_arg
            (zip fnArgs (zip (map (interp_lvalue f state) argTms)
                             (map (interp_term f state) argTms))) acc \<noteq> Inl InsufficientFuel"
  shows "\<forall>f' \<ge> f. fold process_one_arg
            (zip fnArgs (zip (map (interp_lvalue f' state) argTms)
                             (map (interp_term f' state) argTms))) acc
       = fold process_one_arg
            (zip fnArgs (zip (map (interp_lvalue f state) argTms)
                             (map (interp_term f state) argTms))) acc"
  using assms
proof (induct argTms arbitrary: fnArgs acc)
  case Nil
  then show ?case by simp
next
  case (Cons argTm argTms)
  (* Extract fnArg and fnArgs from the length assumption *)
  from Cons.prems(3) obtain fnArg fnArgs' where fnArgs_eq: "fnArgs = fnArg # fnArgs'"
    and len_tail: "length argTms = length fnArgs'"
    by (cases fnArgs) auto
  (* First step: process_one_arg for the head *)
  let ?lv_f = "interp_lvalue f state argTm"
  let ?tm_f = "interp_term f state argTm"
  let ?step_f = "process_one_arg (fnArg, ?lv_f, ?tm_f) acc"

  (* The fold for fuel f doesn't return InsufficientFuel *)
  have fold_noFuel: "fold process_one_arg
      (zip (fnArg # fnArgs') (zip (map (interp_lvalue f state) (argTm # argTms))
                                  (map (interp_term f state) (argTm # argTms)))) acc
      \<noteq> Inl InsufficientFuel"
    using Cons.prems(4) fnArgs_eq by simp

  (* This means the first step doesn't return InsufficientFuel (if it did, fold would propagate it) *)
  have step_noFuel: "?step_f \<noteq> Inl InsufficientFuel"
  proof (rule ccontr)
    assume "\<not> ?step_f \<noteq> Inl InsufficientFuel"
    hence step_eq: "?step_f = Inl InsufficientFuel" by simp
    have "fold process_one_arg
        (zip (fnArg # fnArgs') (zip (map (interp_lvalue f state) (argTm # argTms))
                                    (map (interp_term f state) (argTm # argTms)))) acc
        = fold process_one_arg (zip fnArgs' (zip (map (interp_lvalue f state) argTms)
                                                 (map (interp_term f state) argTms))) ?step_f"
      by simp
    also have "... = Inl InsufficientFuel"
      using step_eq fold_process_one_arg_error by simp
    finally show False using fold_noFuel by simp
  qed

  (* IH premises for argTm *)
  have tm_IH: "interp_term f state argTm \<noteq> Inl InsufficientFuel
                \<longrightarrow> (\<forall>f'\<ge>f. interp_term f' state argTm = interp_term f state argTm)"
    using Cons.prems(1)
    by (metis list.set_intros(1))
  have lv_IH: "interp_lvalue f state argTm \<noteq> Inl InsufficientFuel
                \<longrightarrow> (\<forall>f'\<ge>f. interp_lvalue f' state argTm = interp_lvalue f state argTm)"
    using Cons.prems(2)
    by (metis list.set_intros(1))

  (* Apply process_one_arg_more_fuel *)
  have step_eq: "\<forall>f'\<ge>f. process_one_arg (fnArg, interp_lvalue f' state argTm, interp_term f' state argTm) acc
                       = ?step_f"
    using process_one_arg_more_fuel[OF tm_IH lv_IH step_noFuel] by blast

  show ?case
  proof (cases ?step_f)
    case (Inl err)
    (* First step returns error, fold returns same error *)
    hence "err \<noteq> InsufficientFuel" using step_noFuel by simp
    have step_eq': "\<forall>f'\<ge>f. process_one_arg (fnArg, interp_lvalue f' state argTm, interp_term f' state argTm) acc = Inl err"
      using step_eq Inl by simp
    (* Both folds have Inl err as accumulator after first step, so both equal Inl err *)
    have "\<forall>f'\<ge>f. fold process_one_arg (zip fnArgs' (zip (map (interp_lvalue f' state) argTms)
                                                        (map (interp_term f' state) argTms))) (Inl err) = Inl err"
      by (simp add: fold_process_one_arg_error)
    thus ?thesis using Inl fnArgs_eq step_eq' by (simp add: fold_process_one_arg_error)
  next
    case (Inr acc')
    (* First step succeeds with new accumulator acc' *)
    (* Need to apply IH on the tail *)
    have tail_noFuel: "fold process_one_arg
        (zip fnArgs' (zip (map (interp_lvalue f state) argTms)
                          (map (interp_term f state) argTms))) (Inr acc')
        \<noteq> Inl InsufficientFuel"
      using fold_noFuel Inr by simp
    have tail_tm_IH: "\<forall>argTm\<in>set argTms. interp_term f state argTm \<noteq> Inl InsufficientFuel
                        \<longrightarrow> (\<forall>f'\<ge>f. interp_term f' state argTm = interp_term f state argTm)"
      using Cons.prems(1)
      by (meson list.set_intros(2))
    have tail_lv_IH: "\<forall>argTm\<in>set argTms. interp_lvalue f state argTm \<noteq> Inl InsufficientFuel
                        \<longrightarrow> (\<forall>f'\<ge>f. interp_lvalue f' state argTm = interp_lvalue f state argTm)"
      using Cons.prems(2)
      by (meson list.set_intros(2))
    have tail_eq: "\<forall>f'\<ge>f. fold process_one_arg
          (zip fnArgs' (zip (map (interp_lvalue f' state) argTms)
                            (map (interp_term f' state) argTms))) (Inr acc')
        = fold process_one_arg
          (zip fnArgs' (zip (map (interp_lvalue f state) argTms)
                            (map (interp_term f state) argTms))) (Inr acc')"
      using Cons.hyps[OF tail_tm_IH tail_lv_IH len_tail tail_noFuel] by blast
    show ?thesis
    proof (intro allI impI)
      fix f' assume "f' \<ge> f"
      have "process_one_arg (fnArg, interp_lvalue f' state argTm, interp_term f' state argTm) acc = Inr acc'"
        using step_eq Inr \<open>f' \<ge> f\<close> by simp
      moreover have "fold process_one_arg
          (zip fnArgs' (zip (map (interp_lvalue f' state) argTms)
                            (map (interp_term f' state) argTms))) (Inr acc')
        = fold process_one_arg
          (zip fnArgs' (zip (map (interp_lvalue f state) argTms)
                            (map (interp_term f state) argTms))) (Inr acc')"
        using tail_eq \<open>f' \<ge> f\<close> by blast
      ultimately show "fold process_one_arg
          (zip fnArgs (zip (map (interp_lvalue f' state) (argTm # argTms))
                                      (map (interp_term f' state) (argTm # argTms)))) acc
        = fold process_one_arg
          (zip fnArgs (zip (map (interp_lvalue f state) (argTm # argTms))
                                      (map (interp_term f state) (argTm # argTms)))) acc"
        using Inr fnArgs_eq by simp
    qed
  qed
qed


(* ========================================================================== *)
(* Fuel monotonicity lemmas *)
(* ========================================================================== *)

(* These lemmas state that if an interpreter function does not return
   InsufficientFuel for some fuel value f, then it returns the same result
   for any greater fuel value f'. *)

lemma interp_fuel_mono:
  shows interp_term_mono:
            "interp_term f (state :: 'w InterpState) tm \<noteq> Inl InsufficientFuel
               \<Longrightarrow> \<forall>f'\<ge>f. interp_term f' state tm = interp_term f state tm"
    and interp_term_list_mono:
            "interp_term_list f (state :: 'w InterpState) tms \<noteq> Inl InsufficientFuel
               \<Longrightarrow> \<forall>f'\<ge>f. interp_term_list f' state tms = interp_term_list f state tms"
    and interp_lvalue_mono:
            "interp_lvalue f (state :: 'w InterpState) tm \<noteq> Inl InsufficientFuel
               \<Longrightarrow> \<forall>f'\<ge>f. interp_lvalue f' state tm = interp_lvalue f state tm"
    and interp_statement_mono:
            "interp_statement f (state :: 'w InterpState) stmt \<noteq> Inl InsufficientFuel
               \<Longrightarrow> \<forall>f'\<ge>f. interp_statement f' state stmt = interp_statement f state stmt"
    and interp_statement_list_mono:
            "interp_statement_list f (state :: 'w InterpState) stmts \<noteq> Inl InsufficientFuel
               \<Longrightarrow> \<forall>f'\<ge>f. interp_statement_list f' state stmts = interp_statement_list f state stmts"
    and interp_function_call_mono:
            "interp_function_call f (state :: 'w InterpState) fnName argTms \<noteq> Inl InsufficientFuel
               \<Longrightarrow> \<forall>f'\<ge>f. interp_function_call f' state fnName argTms
                    = interp_function_call f state fnName argTms"
proof (induction rule: interp_term_interp_term_list_interp_lvalue_interp_statement_interp_statement_list_interp_function_call.induct)
  (* ---- Base cases: fuel = 0 ---- *)
  (* interp_term 0 *)
  case (1 uu uv)
  then show ?case by simp
next
  (* interp_term (Suc _) LitBool *)
  case (2 uw ux b)
  then show ?case
    by (metis Suc_le_D interp_term.simps(2))
next
  (* interp_term (Suc _) LitInt *)
  case (3 uy uz i)
  then show ?case
    by (metis Suc_le_D interp_term.simps(3))
next
  (* interp_term (Suc fuel) LitArray *)
  case (4 fuel state tms)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term (Suc fuel) state (CoreTm_LitArray tms) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term_list fuel state tms \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    with "4.IH" have IH: "\<forall>f'\<ge>fuel. interp_term_list f' state tms = interp_term_list fuel state tms"
      by blast
    from IH f''_ge have "interp_term_list f'' state tms = interp_term_list fuel state tms"
      by blast
    with f'_eq show "interp_term f' state (CoreTm_LitArray tms) = interp_term (Suc fuel) state (CoreTm_LitArray tms)"
      by simp
  qed
next
  (* interp_term (Suc _) Var *)
  case (5 va state varName)
  then show ?case
    by (metis Suc_le_D interp_term.simps(5))
next
  (* interp_term (Suc fuel) Cast *)
  case (6 fuel state targetTy tm)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term (Suc fuel) state (CoreTm_Cast targetTy tm) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term fuel state tm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH: "\<forall>f'\<ge>fuel. interp_term f' state tm = interp_term fuel state tm"
      using "6.IH" by blast
    from IH f''_ge have "interp_term f'' state tm = interp_term fuel state tm"
      by blast
    with f'_eq show "interp_term f' state (CoreTm_Cast targetTy tm) = interp_term (Suc fuel) state (CoreTm_Cast targetTy tm)"
      by simp
  qed
next
  (* interp_term (Suc fuel) Unop *)
  case (7 fuel state op tm)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term (Suc fuel) state (CoreTm_Unop op tm) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term fuel state tm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH: "\<forall>f'\<ge>fuel. interp_term f' state tm = interp_term fuel state tm"
      using "7.IH" by blast
    from IH f''_ge have "interp_term f'' state tm = interp_term fuel state tm"
      by blast
    with f'_eq show "interp_term f' state (CoreTm_Unop op tm) = interp_term (Suc fuel) state (CoreTm_Unop op tm)"
      by simp
  qed
next
  (* interp_term (Suc fuel) Binop *)
  case (8 fuel state op lhsTm rhsTm)
  then show ?case
  proof (intro allI impI)
    fix f' assume f'_ge: "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term (Suc fuel) state (CoreTm_Binop op lhsTm rhsTm) \<noteq> Inl InsufficientFuel"
    hence lhs_noFuel: "interp_term fuel state lhsTm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH_lhs: "\<forall>f'\<ge>fuel. interp_term f' state lhsTm = interp_term fuel state lhsTm"
      using "8.IH"(1) by blast
    show "interp_term f' state (CoreTm_Binop op lhsTm rhsTm) = interp_term (Suc fuel) state (CoreTm_Binop op lhsTm rhsTm)"
    proof (cases "interp_term fuel state lhsTm")
      case (Inl err)
      hence "interp_term f'' state lhsTm = Inl err" using IH_lhs f''_ge by metis
      thus ?thesis using Inl f'_eq by simp
    next
      case (Inr lhsVal)
      hence rhs_noFuel: "interp_term fuel state rhsTm \<noteq> Inl InsufficientFuel"
        using noFuel by (auto split: sum.splits)
      hence IH_rhs: "\<forall>f'\<ge>fuel. interp_term f' state rhsTm = interp_term fuel state rhsTm"
        using "8.IH"(2) Inr by blast
      have "interp_term f'' state lhsTm = Inr lhsVal" using IH_lhs Inr f''_ge by auto
      moreover have "interp_term f'' state rhsTm = interp_term fuel state rhsTm" using IH_rhs f''_ge by metis
      ultimately show ?thesis using f'_eq Inr by simp
    qed
  qed
next
  (* interp_term (Suc fuel) Let *)
  case (9 fuel state varName rhsTm bodyTm)
  then show ?case
  proof (intro allI impI)
    fix f' assume f'_ge: "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term (Suc fuel) state (CoreTm_Let varName rhsTm bodyTm) \<noteq> Inl InsufficientFuel"
    hence rhs_noFuel: "interp_term fuel state rhsTm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits prod.splits)
    hence IH_rhs: "\<forall>f'\<ge>fuel. interp_term f' state rhsTm = interp_term fuel state rhsTm"
      using "9.IH"(1) by blast
    show "interp_term f' state (CoreTm_Let varName rhsTm bodyTm) = interp_term (Suc fuel) state (CoreTm_Let varName rhsTm bodyTm)"
    proof (cases "interp_term fuel state rhsTm")
      case (Inl err)
      hence "interp_term f'' state rhsTm = Inl err" using IH_rhs f''_ge by metis
      thus ?thesis using Inl f'_eq by simp
    next
      case (Inr rhsVal)
      define state' addr where "state' = fst (alloc_store state rhsVal)"
                           and "addr = snd (alloc_store state rhsVal)"
      define state'' where "state'' = state' \<lparr> IS_Locals := fmupd varName addr (IS_Locals state') \<rparr>"
      hence body_noFuel: "interp_term fuel state'' bodyTm \<noteq> Inl InsufficientFuel"
        using noFuel Inr state'_def addr_def
        by (auto simp add: case_prod_beta split: sum.splits)
      have IH_body: "\<forall>f'\<ge>fuel. interp_term f' state'' bodyTm = interp_term fuel state'' bodyTm"
        using "9.IH"(2) Inr state'_def addr_def state''_def body_noFuel
        by (metis fst_eqD snd_eqD surj_pair)
      have "interp_term f'' state rhsTm = Inr rhsVal" using IH_rhs Inr f''_ge by auto
      moreover have "interp_term f'' state'' bodyTm = interp_term fuel state'' bodyTm"
        using IH_body f''_ge by metis
      ultimately show ?thesis using f'_eq Inr state'_def addr_def state''_def
        by (simp add: case_prod_beta)
    qed
  qed
next
  (* interp_term (Suc fuel) FunctionCall *)
  case (10 fuel state fnName argTypes argTms)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term (Suc fuel) state (CoreTm_FunctionCall fnName argTypes argTms) \<noteq> Inl InsufficientFuel"
    show "interp_term f' state (CoreTm_FunctionCall fnName argTypes argTms) =
          interp_term (Suc fuel) state (CoreTm_FunctionCall fnName argTypes argTms)"
    proof (cases "is_pure_fun state fnName")
      case False
      thus ?thesis using f'_eq by simp
    next
      case True
      hence fc_noFuel: "interp_function_call fuel state fnName argTms \<noteq> Inl InsufficientFuel"
        using noFuel by (auto split: sum.splits)
      hence IH_fc: "\<forall>f'\<ge>fuel. interp_function_call f' state fnName argTms = interp_function_call fuel state fnName argTms"
        using "10.IH" True by blast
      from IH_fc f''_ge have "interp_function_call f'' state fnName argTms = interp_function_call fuel state fnName argTms"
        by metis
      with f'_eq True show ?thesis by simp
    qed
  qed
next
  (* interp_term (Suc fuel) VariantCtor *)
  case (11 fuel state ctorName vb payloadTm)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term (Suc fuel) state (CoreTm_VariantCtor ctorName vb payloadTm) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term fuel state payloadTm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH: "\<forall>f'\<ge>fuel. interp_term f' state payloadTm = interp_term fuel state payloadTm"
      using "11.IH" by blast
    from IH f''_ge have "interp_term f'' state payloadTm = interp_term fuel state payloadTm"
      by metis
    with f'_eq show "interp_term f' state (CoreTm_VariantCtor ctorName vb payloadTm) =
          interp_term (Suc fuel) state (CoreTm_VariantCtor ctorName vb payloadTm)"
      by simp
  qed
next
  (* interp_term (Suc fuel) Record *)
  case (12 fuel state nameTermPairs)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term (Suc fuel) state (CoreTm_Record nameTermPairs) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term_list fuel state (map snd nameTermPairs) \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH: "\<forall>f'\<ge>fuel. interp_term_list f' state (map snd nameTermPairs) = interp_term_list fuel state (map snd nameTermPairs)"
      using "12.IH" by blast
    from IH f''_ge have "interp_term_list f'' state (map snd nameTermPairs) = interp_term_list fuel state (map snd nameTermPairs)"
      by metis
    with f'_eq show "interp_term f' state (CoreTm_Record nameTermPairs) = interp_term (Suc fuel) state (CoreTm_Record nameTermPairs)"
      by simp
  qed
next
  (* interp_term (Suc fuel) RecordProj *)
  case (13 fuel state tm fldName)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term (Suc fuel) state (CoreTm_RecordProj tm fldName) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term fuel state tm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH: "\<forall>f'\<ge>fuel. interp_term f' state tm = interp_term fuel state tm"
      using "13.IH" by blast
    from IH f''_ge have "interp_term f'' state tm = interp_term fuel state tm"
      by metis
    with f'_eq show "interp_term f' state (CoreTm_RecordProj tm fldName) = interp_term (Suc fuel) state (CoreTm_RecordProj tm fldName)"
      by simp
  qed
next
  (* interp_term (Suc fuel) VariantProj *)
  case (14 fuel state tm expectedCtorName)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term (Suc fuel) state (CoreTm_VariantProj tm expectedCtorName) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term fuel state tm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH: "\<forall>f'\<ge>fuel. interp_term f' state tm = interp_term fuel state tm"
      using "14.IH" by blast
    from IH f''_ge have "interp_term f'' state tm = interp_term fuel state tm"
      by metis
    with f'_eq show "interp_term f' state (CoreTm_VariantProj tm expectedCtorName) = interp_term (Suc fuel) state (CoreTm_VariantProj tm expectedCtorName)"
      by simp
  qed
next
  (* interp_term (Suc fuel) ArrayProj *)
  case (15 fuel state arrayTm idxTms)
  then show ?case
  proof (intro allI impI)
    fix f' assume f'_ge: "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term (Suc fuel) state (CoreTm_ArrayProj arrayTm idxTms) \<noteq> Inl InsufficientFuel"
    hence arr_noFuel: "interp_term fuel state arrayTm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH_arr: "\<forall>f'\<ge>fuel. interp_term f' state arrayTm = interp_term fuel state arrayTm"
      using "15.IH"(1) by blast
    show "interp_term f' state (CoreTm_ArrayProj arrayTm idxTms) = interp_term (Suc fuel) state (CoreTm_ArrayProj arrayTm idxTms)"
    proof (cases "interp_term fuel state arrayTm")
      case (Inl err)
      hence "interp_term f'' state arrayTm = Inl err" using IH_arr f''_ge by metis
      thus ?thesis using Inl f'_eq by simp
    next
      case (Inr arrVal)
      show ?thesis
      proof (cases arrVal)
        case (CV_Array sizes elemMap)
        hence idx_noFuel: "interp_term_list fuel state idxTms \<noteq> Inl InsufficientFuel"
          using noFuel Inr by (auto split: sum.splits)
        hence IH_idx: "\<forall>f'\<ge>fuel. interp_term_list f' state idxTms = interp_term_list fuel state idxTms"
          using "15.IH"(2) Inr CV_Array by blast
        have "interp_term f'' state arrayTm = Inr arrVal" using IH_arr Inr f''_ge by metis
        moreover have "interp_term_list f'' state idxTms = interp_term_list fuel state idxTms"
          using IH_idx f''_ge by metis
        ultimately show ?thesis using f'_eq Inr CV_Array by simp
      next
        case (CV_Bool x1)
        have "interp_term f'' state arrayTm = Inr arrVal" using IH_arr Inr f''_ge by metis
        thus ?thesis using f'_eq CV_Bool Inr by simp
      next
        case (CV_FiniteInt x21 x22 x23)
        have "interp_term f'' state arrayTm = Inr arrVal" using IH_arr Inr f''_ge by metis
        thus ?thesis using f'_eq CV_FiniteInt Inr by simp
      next
        case (CV_Record x4)
        have "interp_term f'' state arrayTm = Inr arrVal" using IH_arr Inr f''_ge by metis
        thus ?thesis using f'_eq CV_Record Inr by simp
      next
        case (CV_Variant x51 x52)
        have "interp_term f'' state arrayTm = Inr arrVal" using IH_arr Inr f''_ge by metis
        thus ?thesis using f'_eq CV_Variant Inr by simp
      qed
    qed
  qed
next
  (* interp_term (Suc fuel) Match *)
  case (16 fuel state scrutTm arms)
  then show ?case
  proof (intro allI impI)
    fix f' assume f'_ge: "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term (Suc fuel) state (CoreTm_Match scrutTm arms) \<noteq> Inl InsufficientFuel"
    hence scrut_noFuel: "interp_term fuel state scrutTm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH_scrut: "\<forall>f'\<ge>fuel. interp_term f' state scrutTm = interp_term fuel state scrutTm"
      using "16.IH"(1) by blast
    show "interp_term f' state (CoreTm_Match scrutTm arms) = interp_term (Suc fuel) state (CoreTm_Match scrutTm arms)"
    proof (cases "interp_term fuel state scrutTm")
      case (Inl err)
      hence "interp_term f'' state scrutTm = Inl err" using IH_scrut f''_ge by metis
      thus ?thesis using Inl f'_eq by simp
    next
      case (Inr scrutVal)
      show ?thesis
      proof (cases "find_matching_arm scrutVal arms")
        case (Inl err)
        hence "interp_term f'' state scrutTm = Inr scrutVal" using IH_scrut Inr f''_ge by metis
        thus ?thesis using f'_eq Inr Inl by simp
      next
        case (Inr armTm)
        hence arm_noFuel: "interp_term fuel state armTm \<noteq> Inl InsufficientFuel"
          using noFuel \<open>interp_term fuel state scrutTm = Inr scrutVal\<close>
          by (auto split: sum.splits)
        hence IH_arm: "\<forall>f'\<ge>fuel. interp_term f' state armTm = interp_term fuel state armTm"
          using "16.IH"(2) \<open>interp_term fuel state scrutTm = Inr scrutVal\<close> Inr by blast
        have "interp_term f'' state scrutTm = interp_term fuel state scrutTm" using IH_scrut f''_ge by metis
        moreover have "interp_term f'' state armTm = interp_term fuel state armTm" using IH_arm f''_ge by metis
        ultimately show ?thesis using f'_eq \<open>interp_term fuel state scrutTm = Inr scrutVal\<close> Inr by simp
      qed
    qed
  qed
next
  (* interp_term (Suc fuel) Sizeof *)
  case (17 fuel state tm)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term (Suc fuel) state (CoreTm_Sizeof tm) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term fuel state tm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH: "\<forall>f'\<ge>fuel. interp_term f' state tm = interp_term fuel state tm"
      using "17.IH" by blast
    from IH f''_ge have "interp_term f'' state tm = interp_term fuel state tm"
      by metis
    with f'_eq show "interp_term f' state (CoreTm_Sizeof tm) = interp_term (Suc fuel) state (CoreTm_Sizeof tm)"
      by simp
  qed
next
  (* interp_term (Suc _) Quantifier - always TypeError *)
  case (18 vc state vd ve vf vg)
  then show ?case
    by (metis Suc_le_D interp_term.simps(18))
next
  (* interp_term (Suc _) Allocated - always TypeError *)
  case (19 vh vi vj)
  then show ?case
    by (metis Suc_le_D interp_term.simps(19))
next
  (* interp_term (Suc _) Old - always TypeError *)
  case (20 vk vl vm)
  then show ?case
    by (metis Suc_le_D interp_term.simps(20))
next
  (* interp_lvalue 0 *)
  case (21 vn vo)
  then show ?case by simp
next
  (* interp_lvalue (Suc fuel) *)
  case (22 fuel state tm)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_lvalue (Suc fuel) state tm \<noteq> Inl InsufficientFuel"
    show "interp_lvalue f' state tm = interp_lvalue (Suc fuel) state tm"
    proof (cases tm)
      case (CoreTm_Var varName)
      thus ?thesis using f'_eq by simp
    next
      case (CoreTm_RecordProj tm' fldName)
      hence sub_noFuel: "interp_lvalue fuel state tm' \<noteq> Inl InsufficientFuel"
        using noFuel by (auto split: sum.splits)
      hence IH: "\<forall>f'\<ge>fuel. interp_lvalue f' state tm' = interp_lvalue fuel state tm'"
        using "22.IH"(1) CoreTm_RecordProj by blast
      from IH f''_ge have "interp_lvalue f'' state tm' = interp_lvalue fuel state tm'"
        by metis
      thus ?thesis using f'_eq CoreTm_RecordProj by simp
    next
      case (CoreTm_VariantProj tm' ctorName)
      hence sub_noFuel: "interp_lvalue fuel state tm' \<noteq> Inl InsufficientFuel"
        using noFuel by (auto split: sum.splits)
      hence IH: "\<forall>f'\<ge>fuel. interp_lvalue f' state tm' = interp_lvalue fuel state tm'"
        using "22.IH"(2) CoreTm_VariantProj by blast
      from IH f''_ge have "interp_lvalue f'' state tm' = interp_lvalue fuel state tm'"
        by metis
      thus ?thesis using f'_eq CoreTm_VariantProj by simp
    next
      case (CoreTm_ArrayProj tm' indexTms)
      hence lv_noFuel: "interp_lvalue fuel state tm' \<noteq> Inl InsufficientFuel"
        using noFuel by (auto split: sum.splits)
      hence IH_lv: "\<forall>f'\<ge>fuel. interp_lvalue f' state tm' = interp_lvalue fuel state tm'"
        using "22.IH"(3) CoreTm_ArrayProj by blast
      show ?thesis
      proof (cases "interp_lvalue fuel state tm'")
        case (Inl err)
        hence "interp_lvalue f'' state tm' = Inl err" using IH_lv f''_ge by metis
        thus ?thesis using f'_eq CoreTm_ArrayProj Inl by simp
      next
        case (Inr addrPath)
        hence idx_noFuel: "interp_term_list fuel state indexTms \<noteq> Inl InsufficientFuel"
          using noFuel CoreTm_ArrayProj by (auto split: sum.splits)
        hence IH_idx: "\<forall>f'\<ge>fuel. interp_term_list f' state indexTms = interp_term_list fuel state indexTms"
          using "22.IH"(4) CoreTm_ArrayProj Inr
          by (metis prod.exhaust)
        have "interp_lvalue f'' state tm' = Inr addrPath" using IH_lv Inr f''_ge by metis
        moreover have "interp_term_list f'' state indexTms = interp_term_list fuel state indexTms"
          using IH_idx f''_ge by metis
        ultimately show ?thesis using f'_eq CoreTm_ArrayProj Inr by simp
      qed
    next
      case (CoreTm_LitBool x)
      thus ?thesis using f'_eq by simp
    next
      case (CoreTm_LitInt x)
      thus ?thesis using f'_eq by simp
    next
      case (CoreTm_LitArray x)
      thus ?thesis using f'_eq by simp
    next
      case (CoreTm_Cast x1 x2)
      thus ?thesis using f'_eq by simp
    next
      case (CoreTm_Unop x1 x2)
      thus ?thesis using f'_eq by simp
    next
      case (CoreTm_Binop x1 x2 x3)
      thus ?thesis using f'_eq by simp
    next
      case (CoreTm_Let x1 x2 x3)
      thus ?thesis using f'_eq by simp
    next
      case (CoreTm_FunctionCall x1 x2 x3)
      thus ?thesis using f'_eq by simp
    next
      case (CoreTm_VariantCtor x1 x2 x3)
      thus ?thesis using f'_eq by simp
    next
      case (CoreTm_Record x)
      thus ?thesis using f'_eq by simp
    next
      case (CoreTm_Match x1 x2)
      thus ?thesis using f'_eq by simp
    next
      case (CoreTm_Sizeof x)
      thus ?thesis using f'_eq by simp
    next
      case (CoreTm_Quantifier x1 x2 x3 x4)
      thus ?thesis using f'_eq by simp
    next
      case (CoreTm_Allocated x)
      thus ?thesis using f'_eq by simp
    next
      case (CoreTm_Old x)
      thus ?thesis using f'_eq by simp
    qed
  qed
next
  (* interp_term_list 0 *)
  case (23 vp vq)
  then show ?case by simp
next
  (* interp_term_list (Suc _) [] *)
  case (24 vr vs)
  then show ?case
    by (metis Suc_le_D interp_term_list.simps(2))
next
  (* interp_term_list (Suc fuel) (tm # tms) *)
  case (25 fuel state tm tms)
  then show ?case
  proof (intro allI impI)
    fix f' assume f'_ge: "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term_list (Suc fuel) state (tm # tms) \<noteq> Inl InsufficientFuel"
    hence tm_noFuel: "interp_term fuel state tm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH_tm: "\<forall>f'\<ge>fuel. interp_term f' state tm = interp_term fuel state tm"
      using "25.IH"(1) by blast
    show "interp_term_list f' state (tm # tms) = interp_term_list (Suc fuel) state (tm # tms)"
    proof (cases "interp_term fuel state tm")
      case (Inl err)
      hence "interp_term f'' state tm = Inl err" using IH_tm f''_ge by metis
      thus ?thesis using Inl f'_eq by simp
    next
      case (Inr val)
      hence tms_noFuel: "interp_term_list fuel state tms \<noteq> Inl InsufficientFuel"
        using noFuel by (auto split: sum.splits)
      hence IH_tms: "\<forall>f'\<ge>fuel. interp_term_list f' state tms = interp_term_list fuel state tms"
        using "25.IH"(2) Inr by blast
      have "interp_term f'' state tm = Inr val" using IH_tm Inr f''_ge by metis
      moreover have "interp_term_list f'' state tms = interp_term_list fuel state tms"
        using IH_tms f''_ge by metis
      ultimately show ?thesis using f'_eq Inr by simp
    qed
  qed
next
  (* interp_statement 0 *)
  case (26 vt vu)
  then show ?case by simp
next
  (* interp_statement (Suc _) VarDecl Ghost *)
  case (27 vv state vw vx vy vz)
  then show ?case
    by (metis Suc_le_D interp_statement.simps(2))
next
  (* interp_statement (Suc fuel) VarDecl NotGhost Var *)
  case (28 fuel state varName wa initialTm)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_statement (Suc fuel) state (CoreStmt_VarDecl NotGhost varName Var wa initialTm) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term fuel state initialTm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits prod.splits)
    hence IH: "\<forall>f'\<ge>fuel. interp_term f' state initialTm = interp_term fuel state initialTm"
      using "28.IH" by blast
    from IH f''_ge have "interp_term f'' state initialTm = interp_term fuel state initialTm"
      by metis
    with f'_eq show "interp_statement f' state (CoreStmt_VarDecl NotGhost varName Var wa initialTm) =
          interp_statement (Suc fuel) state (CoreStmt_VarDecl NotGhost varName Var wa initialTm)"
      by simp
  qed
next
  (* interp_statement (Suc fuel) VarDecl NotGhost Ref *)
  case (29 fuel state varName wb lvalueTm)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_statement (Suc fuel) state (CoreStmt_VarDecl NotGhost varName Ref wb lvalueTm) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_lvalue fuel state lvalueTm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH: "\<forall>f'\<ge>fuel. interp_lvalue f' state lvalueTm = interp_lvalue fuel state lvalueTm"
      using "29.IH" by blast
    from IH f''_ge have "interp_lvalue f'' state lvalueTm = interp_lvalue fuel state lvalueTm"
      by metis
    with f'_eq show "interp_statement f' state (CoreStmt_VarDecl NotGhost varName Ref wb lvalueTm) =
          interp_statement (Suc fuel) state (CoreStmt_VarDecl NotGhost varName Ref wb lvalueTm)"
      by simp
  qed
next
  (* interp_statement (Suc _) Assign Ghost *)
  case (30 wc state wd we)
  then show ?case
    by (metis Suc_le_D interp_statement.simps(5))
next
  (* interp_statement (Suc fuel) Assign NotGhost *)
  case (31 fuel state lhsLvalue rhsTm)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_statement (Suc fuel) state (CoreStmt_Assign NotGhost lhsLvalue rhsTm) \<noteq> Inl InsufficientFuel"
    hence lhs_noFuel: "interp_lvalue fuel state lhsLvalue \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH_lhs: "\<forall>f'\<ge>fuel. interp_lvalue f' state lhsLvalue = interp_lvalue fuel state lhsLvalue"
      using "31.IH"(1) by blast
    show "interp_statement f' state (CoreStmt_Assign NotGhost lhsLvalue rhsTm) =
          interp_statement (Suc fuel) state (CoreStmt_Assign NotGhost lhsLvalue rhsTm)"
    proof (cases "interp_lvalue fuel state lhsLvalue")
      case (Inl err)
      hence "interp_lvalue f'' state lhsLvalue = Inl err" using IH_lhs f''_ge by metis
      thus ?thesis using Inl f'_eq by simp
    next
      case (Inr addrPath)
      obtain addr path where addrPath_eq: "addrPath = (addr, path)" by (cases addrPath)
      show ?thesis
      proof (cases "\<exists>fnName argTypes argTms. rhsTm = CoreTm_FunctionCall fnName argTypes argTms")
        case True
        then obtain fnName argTypes argTms where rhsTm_eq: "rhsTm = CoreTm_FunctionCall fnName argTypes argTms"
          by blast
        hence fc_noFuel: "interp_function_call fuel state fnName argTms \<noteq> Inl InsufficientFuel"
          using noFuel Inr addrPath_eq by (auto split: sum.splits)
        hence IH_fc: "\<forall>f'\<ge>fuel. interp_function_call f' state fnName argTms = interp_function_call fuel state fnName argTms"
          using Inr addrPath_eq rhsTm_eq
          by (meson "31.IH"(11))
        have "interp_lvalue f'' state lhsLvalue = Inr addrPath" using IH_lhs Inr f''_ge by metis
        moreover have "interp_function_call f'' state fnName argTms = interp_function_call fuel state fnName argTms"
          using IH_fc f''_ge by metis
        ultimately show ?thesis using f'_eq rhsTm_eq Inr addrPath_eq by simp
      next
        case notFunCall: False
        hence rhs_noFuel: "interp_term fuel state rhsTm \<noteq> Inl InsufficientFuel"
          using noFuel Inr addrPath_eq by (auto split: sum.splits CoreTerm.splits)
        hence IH_rhs: "\<forall>f'\<ge>fuel. interp_term f' state rhsTm = interp_term fuel state rhsTm"
          using "31.IH"(3) Inr addrPath_eq notFunCall
          by (metis "31.IH"(10,12,13,14,15,16,17,18,19,2,20,4,5,6,7,8,9) CoreTerm.exhaust)
        have "interp_lvalue f'' state lhsLvalue = Inr addrPath" using IH_lhs Inr f''_ge by metis
        moreover have "interp_term f'' state rhsTm = interp_term fuel state rhsTm"
          using IH_rhs f''_ge by metis
        ultimately show ?thesis using f'_eq notFunCall Inr addrPath_eq by (cases rhsTm; simp)
      qed
    qed
  qed
next
  (* interp_statement (Suc _) Swap Ghost *)
  case (32 wf state wg wh)
  then show ?case
    by (metis Suc_le_D interp_statement.simps(7))
next
  (* interp_statement (Suc fuel) Swap NotGhost *)
  case (33 fuel state lhsTm rhsTm)
  then show ?case
  proof (intro allI impI)
    fix f' assume f'_ge: "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_statement (Suc fuel) state (CoreStmt_Swap NotGhost lhsTm rhsTm) \<noteq> Inl InsufficientFuel"
    hence lhs_noFuel: "interp_lvalue fuel state lhsTm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH_lhs: "\<forall>f'\<ge>fuel. interp_lvalue f' state lhsTm = interp_lvalue fuel state lhsTm"
      using "33.IH"(1) by blast
    show "interp_statement f' state (CoreStmt_Swap NotGhost lhsTm rhsTm) =
          interp_statement (Suc fuel) state (CoreStmt_Swap NotGhost lhsTm rhsTm)"
    proof (cases "interp_lvalue fuel state lhsTm")
      case (Inl err)
      hence "interp_lvalue f'' state lhsTm = Inl err" using IH_lhs f''_ge by metis
      thus ?thesis using Inl f'_eq by simp
    next
      case (Inr lhsLvalue)
      hence rhs_noFuel: "interp_lvalue fuel state rhsTm \<noteq> Inl InsufficientFuel"
        using noFuel by (auto split: sum.splits)
      hence IH_rhs: "\<forall>f'\<ge>fuel. interp_lvalue f' state rhsTm = interp_lvalue fuel state rhsTm"
        using "33.IH"(2) Inr by blast
      have "interp_lvalue f'' state lhsTm = Inr lhsLvalue" using IH_lhs Inr f''_ge by metis
      moreover have "interp_lvalue f'' state rhsTm = interp_lvalue fuel state rhsTm"
        using IH_rhs f''_ge by metis
      ultimately show ?thesis using f'_eq Inr by simp
    qed
  qed
next
  (* interp_statement (Suc fuel) Return *)
  case (34 fuel state tm)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_statement (Suc fuel) state (CoreStmt_Return tm) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term fuel state tm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH: "\<forall>f'\<ge>fuel. interp_term f' state tm = interp_term fuel state tm"
      using "34.IH" by blast
    from IH f''_ge have "interp_term f'' state tm = interp_term fuel state tm"
      by metis
    with f'_eq show "interp_statement f' state (CoreStmt_Return tm) = interp_statement (Suc fuel) state (CoreStmt_Return tm)"
      by simp
  qed
next
  (* interp_statement (Suc _) While Ghost *)
  case (35 wi state wj wk wl wm)
  then show ?case
    by (metis Suc_le_D interp_statement.simps(10))
next
  (* interp_statement (Suc fuel) While NotGhost *)
  case (36 fuel state condTm invars decr bodyStmts)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_statement (Suc fuel) state (CoreStmt_While NotGhost condTm invars decr bodyStmts) \<noteq> Inl InsufficientFuel"
    hence cond_noFuel: "interp_term fuel state condTm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH_cond: "\<forall>f'\<ge>fuel. interp_term f' state condTm = interp_term fuel state condTm"
      using "36.IH"(1) by blast
    show "interp_statement f' state (CoreStmt_While NotGhost condTm invars decr bodyStmts) =
          interp_statement (Suc fuel) state (CoreStmt_While NotGhost condTm invars decr bodyStmts)"
    proof (cases "interp_term fuel state condTm")
      case (Inl err)
      hence "interp_term f'' state condTm = Inl err" using IH_cond f''_ge by metis
      thus ?thesis using Inl f'_eq by simp
    next
      case (Inr condVal)
      show ?thesis
      proof (cases condVal)
        case (CV_Bool b)
        show ?thesis
        proof (cases b)
          case True
          hence body_noFuel: "interp_statement_list fuel state bodyStmts \<noteq> Inl InsufficientFuel"
            using noFuel Inr CV_Bool by (auto split: sum.splits ExecResult.splits)
          hence IH_body: "\<forall>f'\<ge>fuel. interp_statement_list f' state bodyStmts = interp_statement_list fuel state bodyStmts"
            using "36.IH"(2) Inr CV_Bool True by blast
          have cond_fuel: "interp_term fuel state condTm = Inr (CV_Bool True)"
            using Inr CV_Bool True by simp
          have cond_f'': "interp_term f'' state condTm = Inr (CV_Bool True)"
            using IH_cond cond_fuel f''_ge by simp
          show ?thesis
          proof (cases "interp_statement_list fuel state bodyStmts")
            case (Inl err)
            hence "interp_statement_list f'' state bodyStmts = Inl err" using IH_body f''_ge by metis
            thus ?thesis using Inl f'_eq cond_f'' cond_fuel by simp
          next
            case (Inr result)
            show ?thesis
            proof (cases result)
              case (Continue state')
              hence loop_noFuel: "interp_statement fuel (restore_scope state state')
                                    (CoreStmt_While NotGhost condTm invars decr bodyStmts) \<noteq> Inl InsufficientFuel"
                using noFuel cond_fuel \<open>interp_statement_list fuel state bodyStmts = Inr result\<close>
                by auto
              hence IH_loop: "\<forall>f'\<ge>fuel. interp_statement f' (restore_scope state state')
                                          (CoreStmt_While NotGhost condTm invars decr bodyStmts) =
                                        interp_statement fuel (restore_scope state state')
                                          (CoreStmt_While NotGhost condTm invars decr bodyStmts)"
                using "36.IH"(3) Inr CV_Bool True \<open>interp_statement_list fuel state bodyStmts = Inr result\<close> Continue
                by (metis cond_fuel)
              have body_fuel: "interp_statement_list fuel state bodyStmts = Inr (Continue state')"
                using \<open>interp_statement_list fuel state bodyStmts = Inr result\<close> Continue by simp
              have "interp_term f'' state condTm = Inr (CV_Bool True)"
                using cond_f'' by simp
              moreover have "interp_statement_list f'' state bodyStmts = Inr (Continue state')"
                using IH_body body_fuel f''_ge by metis
              moreover have "interp_statement f'' (restore_scope state state')
                              (CoreStmt_While NotGhost condTm invars decr bodyStmts) =
                            interp_statement fuel (restore_scope state state')
                              (CoreStmt_While NotGhost condTm invars decr bodyStmts)"
                using IH_loop f''_ge by metis
              ultimately show ?thesis using f'_eq cond_fuel body_fuel by simp
            next
              case (Return state' retVal)
              have body_fuel: "interp_statement_list fuel state bodyStmts = Inr (Return state' retVal)"
                using \<open>interp_statement_list fuel state bodyStmts = Inr result\<close> Return by simp
              have "interp_term f'' state condTm = Inr (CV_Bool True)"
                using cond_f'' by simp
              moreover have "interp_statement_list f'' state bodyStmts = Inr (Return state' retVal)"
                using IH_body body_fuel f''_ge by metis
              ultimately show ?thesis using f'_eq cond_fuel body_fuel by simp
            qed
          qed
        next
          case False
          have cond_fuel: "interp_term fuel state condTm = Inr (CV_Bool False)"
            using Inr CV_Bool False by simp
          have "interp_term f'' state condTm = Inr (CV_Bool False)" using IH_cond cond_fuel f''_ge by metis
          thus ?thesis using f'_eq cond_fuel by simp
        qed
      next
        case (CV_FiniteInt x21 x22 x23)
        have "interp_term f'' state condTm = Inr condVal" using IH_cond Inr f''_ge by metis
        thus ?thesis using f'_eq CV_FiniteInt Inr by simp
      next
        case (CV_Record x4)
        have "interp_term f'' state condTm = Inr condVal" using IH_cond Inr f''_ge by metis
        thus ?thesis using f'_eq CV_Record Inr by simp
      next
        case (CV_Variant x51 x52)
        have "interp_term f'' state condTm = Inr condVal" using IH_cond Inr f''_ge by metis
        thus ?thesis using f'_eq CV_Variant Inr by simp
      next
        case (CV_Array x61 x62)
        have "interp_term f'' state condTm = Inr condVal" using IH_cond Inr f''_ge by metis
        thus ?thesis using f'_eq CV_Array Inr by simp
      qed
    qed
  qed
next
  (* interp_statement (Suc _) Match Ghost *)
  case (37 wn state wo wp)
  then show ?case
    by (metis Suc_le_D interp_statement.simps(12))
next
  (* interp_statement (Suc fuel) Match NotGhost *)
  case (38 fuel state scrutTm arms)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_statement (Suc fuel) state (CoreStmt_Match NotGhost scrutTm arms) \<noteq> Inl InsufficientFuel"
    hence scrut_noFuel: "interp_term fuel state scrutTm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH_scrut: "\<forall>f'\<ge>fuel. interp_term f' state scrutTm = interp_term fuel state scrutTm"
      using "38.IH"(1) by blast
    show "interp_statement f' state (CoreStmt_Match NotGhost scrutTm arms) =
          interp_statement (Suc fuel) state (CoreStmt_Match NotGhost scrutTm arms)"
    proof (cases "interp_term fuel state scrutTm")
      case (Inl err)
      hence "interp_term f'' state scrutTm = Inl err" using IH_scrut f''_ge by metis
      thus ?thesis using Inl f'_eq by simp
    next
      case (Inr scrutVal)
      show ?thesis
      proof (cases "find_matching_arm scrutVal arms")
        case (Inl err)
        have "interp_term f'' state scrutTm = Inr scrutVal" using IH_scrut Inr f''_ge by metis
        thus ?thesis using f'_eq Inr Inl by simp
      next
        case (Inr armStmts)
        hence arm_noFuel: "interp_statement_list fuel state armStmts \<noteq> Inl InsufficientFuel"
          using noFuel \<open>interp_term fuel state scrutTm = Inr scrutVal\<close>
          by (auto split: sum.splits)
        hence IH_arm: "\<forall>f'\<ge>fuel. interp_statement_list f' state armStmts = interp_statement_list fuel state armStmts"
          using "38.IH"(2) \<open>interp_term fuel state scrutTm = Inr scrutVal\<close> Inr by blast
        have "interp_term f'' state scrutTm = Inr scrutVal" using IH_scrut \<open>interp_term fuel state scrutTm = Inr scrutVal\<close> f''_ge by metis
        moreover have "interp_statement_list f'' state armStmts = interp_statement_list fuel state armStmts"
          using IH_arm f''_ge by metis
        ultimately show ?thesis using f'_eq \<open>interp_term fuel state scrutTm = Inr scrutVal\<close> Inr by simp
      qed
    qed
  qed
next
  (* interp_statement (Suc fuel) Assert *)
  case (39 fuel state wq wr)
  then show ?case
    by (metis Suc_le_D interp_statement.simps(14))
next
  (* interp_statement (Suc fuel) Assume *)
  case (40 fuel state ws)
  then show ?case
    by (metis Suc_le_D interp_statement.simps(15))
next
  (* interp_statement (Suc fuel) ShowHide *)
  case (41 fuel state wt wu)
  then show ?case
    by (metis Suc_le_D interp_statement.simps(16))
next
  (* interp_statement (Suc fuel) Fix - always TypeError *)
  case (42 fuel wv ww wx)
  then show ?case
    by (metis Suc_le_D interp_statement.simps(17))
next
  (* interp_statement (Suc fuel) Obtain - always TypeError *)
  case (43 fuel wy wz xa xb)
  then show ?case
    by (metis Suc_le_D interp_statement.simps(18))
next
  (* interp_statement (Suc fuel) Use - always TypeError *)
  case (44 fuel xc xd)
  then show ?case
    by (metis Suc_le_D interp_statement.simps(19))
next
  (* interp_statement_list 0 *)
  case (45 xe xf)
  then show ?case by simp
next
  (* interp_statement_list (Suc _) [] *)
  case (46 xg state)
  then show ?case
    by (metis Suc_le_D interp_statement_list.simps(2))
next
  (* interp_statement_list (Suc fuel) (stmt # stmts) *)
  case (47 fuel state stmt stmts)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_statement_list (Suc fuel) state (stmt # stmts) \<noteq> Inl InsufficientFuel"
    hence stmt_noFuel: "interp_statement fuel state stmt \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits ExecResult.splits)
    hence IH_stmt: "\<forall>f'\<ge>fuel. interp_statement f' state stmt = interp_statement fuel state stmt"
      using "47.IH"(1) by blast
    show "interp_statement_list f' state (stmt # stmts) =
          interp_statement_list (Suc fuel) state (stmt # stmts)"
    proof (cases "interp_statement fuel state stmt")
      case (Inl err)
      have stmt_fuel: "interp_statement fuel state stmt = Inl err" using Inl by simp
      have "interp_statement f'' state stmt = Inl err" using IH_stmt stmt_fuel f''_ge by metis
      thus ?thesis using f'_eq stmt_fuel by simp
    next
      case (Inr result)
      show ?thesis
      proof (cases result)
        case (Continue state')
        have stmt_fuel: "interp_statement fuel state stmt = Inr (Continue state')"
          using Inr Continue by simp
        hence stmts_noFuel: "interp_statement_list fuel state' stmts \<noteq> Inl InsufficientFuel"
          using noFuel by (auto split: sum.splits)
        hence IH_stmts: "\<forall>f'\<ge>fuel. interp_statement_list f' state' stmts = interp_statement_list fuel state' stmts"
          using "47.IH"(2) Inr Continue by blast
        have "interp_statement f'' state stmt = Inr (Continue state')"
          using IH_stmt stmt_fuel f''_ge by metis
        moreover have "interp_statement_list f'' state' stmts = interp_statement_list fuel state' stmts"
          using IH_stmts f''_ge by metis
        ultimately show ?thesis using f'_eq stmt_fuel by simp
      next
        case (Return state' retVal)
        have stmt_fuel: "interp_statement fuel state stmt = Inr (Return state' retVal)"
          using Inr Return by simp
        have "interp_statement f'' state stmt = Inr (Return state' retVal)"
          using IH_stmt stmt_fuel f''_ge by metis
        thus ?thesis using f'_eq stmt_fuel by simp
      qed
    qed
  qed
next
  (* interp_function_call 0 *)
  case (48 xh xi xj)
  then show ?case by simp
next
  (* interp_function_call (Suc fuel) *)
  case (49 fuel state fnName argTms)
  then show ?case
  proof (intro allI impI)
    fix f' assume f'_ge: "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_function_call (Suc fuel) state fnName argTms \<noteq> Inl InsufficientFuel"

    show "interp_function_call f' state fnName argTms =
          interp_function_call (Suc fuel) state fnName argTms"
    proof (cases "fmlookup (IS_Functions state) fnName")
      case None
      thus ?thesis using f'_eq by simp
    next
      case (Some fn)
      show ?thesis
      proof (cases "length argTms \<noteq> length (IF_Args fn)")
        case True
        thus ?thesis using Some f'_eq by simp
      next
        case False
        (* Abbreviations for clarity *)
        let ?refResults = "map (interp_lvalue fuel state) argTms"
        let ?valResults = "map (interp_term fuel state) argTms"
        let ?fnArgs = "IF_Args fn"
        let ?clearedState = "state \<lparr> IS_Locals := fmempty, IS_Refs := fmempty \<rparr>"

        have len_eq: "length ?fnArgs = length argTms" using False by simp
        hence len_ref: "length ?fnArgs = length ?refResults" by simp
        hence len_val: "length ?refResults = length ?valResults" by simp

        have fold_noFuel: "fold process_one_arg (zip ?fnArgs (zip (map (interp_lvalue fuel state) argTms)
                (map (interp_term fuel state) argTms))) (Inr ?clearedState)
              \<noteq> Inl InsufficientFuel"
          using noFuel Some False by (auto simp: Let_def split: sum.splits ExecResult.splits)

        (* Establish IH premises for fold_process_one_arg_more_fuel *)
        have tm_IH: "\<forall>argTm \<in> set argTms.
                      interp_term fuel state argTm \<noteq> Inl InsufficientFuel
                        \<longrightarrow> (\<forall>f' \<ge> fuel. interp_term f' state argTm = interp_term fuel state argTm)"
          using "49.IH"(1) Some by (meson "49.IH"(2) False)
        have lv_IH: "\<forall>argTm \<in> set argTms.
                      interp_lvalue fuel state argTm \<noteq> Inl InsufficientFuel
                        \<longrightarrow> (\<forall>f' \<ge> fuel. interp_lvalue f' state argTm = interp_lvalue fuel state argTm)"
          using "49.IH"(2) Some by (meson "49.IH"(1) False)

        (* Use fold_process_one_arg_more_fuel *)
        have fold_all: "\<forall>f' \<ge> fuel. fold process_one_arg (zip ?fnArgs (zip (map (interp_lvalue f' state) argTms)
                                                              (map (interp_term f' state) argTms))) (Inr ?clearedState) =
                       fold process_one_arg (zip ?fnArgs (zip ?refResults ?valResults)) (Inr ?clearedState)"
          using fold_process_one_arg_more_fuel[OF tm_IH lv_IH _ fold_noFuel] len_eq by argo
        hence fold_eq: "fold process_one_arg (zip ?fnArgs (zip (map (interp_lvalue f'' state) argTms)
                                                              (map (interp_term f'' state) argTms))) (Inr ?clearedState) =
                       fold process_one_arg (zip ?fnArgs (zip ?refResults ?valResults)) (Inr ?clearedState)"
          using f''_ge by blast

        show ?thesis
        proof (cases "fold process_one_arg (zip ?fnArgs (zip ?refResults ?valResults)) (Inr ?clearedState)")
          case (Inl err)
          thus ?thesis using Some False f'_eq fold_eq by (simp add: Let_def)
        next
          case PreCall: (Inr preCallState)
          (* Now case-analyze on whether the function is internal or external *)
          show ?thesis
          proof (cases "IF_Body fn")
            case (Inl bodyStmts)
            (* Internal function: execute body statements *)
            hence body_noFuel: "interp_statement_list fuel preCallState bodyStmts \<noteq> Inl InsufficientFuel"
              using noFuel Some False PreCall by (auto split: sum.splits ExecResult.splits simp: Let_def)
            hence IH_body: "\<forall>f'\<ge>fuel. interp_statement_list f' preCallState bodyStmts =
                                      interp_statement_list fuel preCallState bodyStmts"
              using "49.IH"(3) Some False PreCall Inl by blast
            have "interp_statement_list f'' preCallState bodyStmts =
                  interp_statement_list fuel preCallState bodyStmts"
              using IH_body f''_ge by metis
            thus ?thesis using Some False PreCall f'_eq fold_eq Inl by (simp add: Let_def)
          next
            case (Inr externFun)
            (* External function: the result depends on valResults and refResults directly,
               not on the fold result (preCallState). We need to show these maps are equal. *)

            (* From fold success (Inr preCallState), all process_one_arg calls succeeded.
               This means all term evaluations returned Inr _ (not Inl InsufficientFuel). *)

            have all_terms_ok: "\<forall>argTm \<in> set argTms. \<exists>v. interp_term fuel state argTm = Inr v"
            proof (rule ballI)
              fix argTm
              assume "argTm \<in> set argTms"
              then obtain valResult 
                where "valResult \<in> set (map (interp_term fuel state) argTms)"
                and "valResult = interp_term fuel state argTm"
                by simp
              then have "\<exists>val. valResult = Inr val"
                using PreCall fold_process_one_arg_all_ok len_ref len_val by blast
              thus "\<exists>v. interp_term fuel state argTm = Inr v"
                by (simp add: \<open>valResult = interp_term fuel state argTm\<close>) 
            qed

            (* From all_terms_ok, no term eval returned InsufficientFuel *)
            have terms_not_insuff: "\<forall>argTm \<in> set argTms. interp_term fuel state argTm \<noteq> Inl InsufficientFuel"
              using all_terms_ok by auto

            (* By tm_IH, all term evaluations are equal for f'' and fuel *)
            have valResults_eq: "map (interp_term f'' state) argTms = ?valResults"
            proof (rule map_eq_conv[THEN iffD2], rule ballI)
              fix argTm assume "argTm \<in> set argTms"
              from tm_IH this terms_not_insuff f''_ge
              show "interp_term f'' state argTm = interp_term fuel state argTm" by blast
            qed

            (* For Ref arguments, lvalue must have succeeded (not InsufficientFuel) *)
            have ref_lvalues_ok: "\<forall>argTm \<in> set argTms. \<forall>name.
                (argTm, (name, Ref)) \<in> set (zip argTms ?fnArgs)
                \<longrightarrow> (\<exists>lval. interp_lvalue fuel state argTm = Inr lval)"
            proof (intro ballI allI impI)
              fix argTm name
              assume "argTm \<in> set argTms"
                and in_zip: "(argTm, (name, Ref)) \<in> set (zip argTms ?fnArgs)"
              show "\<exists>lval. interp_lvalue fuel state argTm = Inr lval"
                using fold_process_one_arg_ref_lvalue_ok[OF PreCall len_eq _ len_val refl in_zip]
                  len_ref by simp
            qed

            (* For Ref arguments, lvalue results are equal (they didn't return InsufficientFuel) *)
            have ref_lvalues_eq: "\<forall>i < length argTms. snd (?fnArgs ! i) = Ref \<longrightarrow>
                interp_lvalue f'' state (argTms ! i) = interp_lvalue fuel state (argTms ! i)"
            proof (intro allI impI)
              fix i assume i_bound: "i < length argTms" and is_ref: "snd (?fnArgs ! i) = Ref"
              obtain argName where fnArg_eq: "?fnArgs ! i = (argName, Ref)"
                using is_ref by (cases "?fnArgs ! i") auto
              have argTm_in: "argTms ! i \<in> set argTms" using i_bound by simp
              have "(argTms ! i, (argName, Ref)) \<in> set (zip argTms ?fnArgs)"
                using i_bound fnArg_eq len_eq by (auto simp: set_zip intro!: exI[of _ i])
              hence "\<exists>lval. interp_lvalue fuel state (argTms ! i) = Inr lval"
                using ref_lvalues_ok argTm_in by blast
              hence "interp_lvalue fuel state (argTms ! i) \<noteq> Inl InsufficientFuel" by auto
              thus "interp_lvalue f'' state (argTms ! i) = interp_lvalue fuel state (argTms ! i)"
                using lv_IH argTm_in f''_ge by blast
            qed

            (* The filtered refs (for Ref args only) are equal *)
            let ?filter_refs = "\<lambda>refResults. map (\<lambda>((_, vr), refResult).
                                    if vr = Ref then refResult else Inl TypeError)
                                  (zip ?fnArgs refResults)"
            have filtered_refs_eq: "?filter_refs (map (interp_lvalue f'' state) argTms) =
                                    ?filter_refs ?refResults"
            proof (rule nth_equalityI)
              show "length (?filter_refs (map (interp_lvalue f'' state) argTms)) =
                    length (?filter_refs ?refResults)"
                by simp
            next
              fix i assume "i < length (?filter_refs (map (interp_lvalue f'' state) argTms))"
              hence i_bound: "i < length ?fnArgs" by simp
              hence i_bound': "i < length argTms" using len_eq by simp
              obtain argName argVr where fnArg_eq: "?fnArgs ! i = (argName, argVr)"
                by (cases "?fnArgs ! i")
              show "?filter_refs (map (interp_lvalue f'' state) argTms) ! i =
                    ?filter_refs ?refResults ! i"
              proof (cases argVr)
                case Var
                thus ?thesis using i_bound fnArg_eq len_eq by simp
              next
                case Ref
                have "interp_lvalue f'' state (argTms ! i) = interp_lvalue fuel state (argTms ! i)"
                  using ref_lvalues_eq i_bound' Ref fnArg_eq by simp
                thus ?thesis using i_bound fnArg_eq Ref len_eq i_bound' by simp
              qed
            qed

            (* Now show the full expressions are equal *)
            have rights_vals_eq: "rights (map (interp_term f'' state) argTms) = rights ?valResults"
              using valResults_eq by metis

            have rights_refs_eq: "rights (?filter_refs (map (interp_lvalue f'' state) argTms)) =
                                  rights (?filter_refs ?refResults)"
              using filtered_refs_eq by simp

            (* Rewrite fold_eq using valResults_eq to get the fold result in terms of f'' *)
            have fold_eq': "fold process_one_arg (zip ?fnArgs (zip (map (interp_lvalue f'' state) argTms)
                                                              (map (interp_term f'' state) argTms))) (Inr ?clearedState) =
                           Inr preCallState"
              using fold_eq PreCall valResults_eq by argo

            (* Both LHS and RHS compute the same result for external functions *)
            show ?thesis using Some False Inr f'_eq fold_eq' PreCall
                               rights_vals_eq rights_refs_eq filtered_refs_eq
              by (simp add: Let_def)
          qed
        qed
      qed
    qed
  qed
qed

end
