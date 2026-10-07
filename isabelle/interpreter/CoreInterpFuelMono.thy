theory CoreInterpFuelMono
  imports CoreInterp
begin

(* Fuel monotonicity for the interpreter: if an interpreter function returns a
   non-InsufficientFuel result at some depth and/or fuel, then it returns the
   same result at any greater depth and/or fuel.

   Also, non-InsufficientFuel results are unique: if two interpreter runs differ
   only in the depth and/or fuel used, and both give a non-InsufficientFuel result,
   then those two results are equal. 

   See "Convenient forms" below for the most convenient statements of these lemmas.
*)


(* ========================================================================== *)
(* Helper lemmas about process_one_arg and fold *)
(* ========================================================================== *)

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

(* process_one_arg gives the same answer on two pairs of argument results, if
   the second pair agrees with the first wherever the first is not out of fuel. *)
lemma process_one_arg_agree:
  assumes "tmRes \<noteq> Inl InsufficientFuel \<longrightarrow> tmRes' = tmRes"
    and "lvRes \<noteq> Inl InsufficientFuel \<longrightarrow> lvRes' = lvRes"
    and "process_one_arg (fnArg, lvRes, tmRes) acc \<noteq> Inl InsufficientFuel"
  shows "process_one_arg (fnArg, lvRes', tmRes') acc = process_one_arg (fnArg, lvRes, tmRes) acc"
proof (cases acc)
  case (Inl err)
  then show ?thesis by simp
next
  case State: (Inr st)
  obtain name vr where fields: "fnArg = (name, vr)" by (cases fnArg)
  show ?thesis
  proof (cases vr)
    case Var
    show ?thesis
    proof (cases tmRes)
      case (Inl err)
      hence "err \<noteq> InsufficientFuel" using assms(3) State fields Var by simp
      hence "tmRes' = tmRes" using assms(1) Inl by simp
      thus ?thesis using Inl State fields Var by simp
    next
      case (Inr val)
      hence "tmRes' = tmRes" using assms(1) by simp
      thus ?thesis using Inr State fields Var by simp
    qed
  next
    case Ref
    show ?thesis
    proof (cases lvRes)
      case (Inl err)
      hence "err \<noteq> InsufficientFuel" using assms(3) State fields Ref by simp
      hence "lvRes' = lvRes" using assms(2) Inl by simp
      thus ?thesis using Inl State fields Ref by simp
    next
      case (Inr lval)
      hence lv_eq: "lvRes' = Inr lval" using assms(2) by simp
      obtain addr path where lval_eq: "lval = (addr, path)" by (cases lval)
      show ?thesis
      proof (cases tmRes)
        case (Inl err')
        hence "err' \<noteq> InsufficientFuel" using assms(3) State fields Ref lval_eq Inr by simp
        hence "tmRes' = Inl err'" using assms(1) Inl by simp
        thus ?thesis using State fields Ref lv_eq Inr lval_eq Inl by simp
      next
        case tmOk: (Inr val)
        hence "tmRes' = Inr val" using assms(1) by simp
        thus ?thesis using State fields Ref lv_eq Inr lval_eq tmOk by simp
      qed
    qed
  qed
qed

lemma fold_process_one_arg_agree:
  assumes "\<forall>a \<in> set argTms. tm a \<noteq> Inl InsufficientFuel \<longrightarrow> tm' a = tm a"
    and "\<forall>a \<in> set argTms. lv a \<noteq> Inl InsufficientFuel \<longrightarrow> lv' a = lv a"
    and "length argTms = length fnArgs"
    and "fold process_one_arg (zip fnArgs (zip (map lv argTms) (map tm argTms))) acc
            \<noteq> Inl InsufficientFuel"
  shows "fold process_one_arg (zip fnArgs (zip (map lv' argTms) (map tm' argTms))) acc
       = fold process_one_arg (zip fnArgs (zip (map lv argTms) (map tm argTms))) acc"
  using assms
proof (induct argTms arbitrary: fnArgs acc)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  from Cons.prems(3) obtain fnArg fnArgs' where fnArgs_eq: "fnArgs = fnArg # fnArgs'"
    and len_tail: "length as = length fnArgs'"
    by (cases fnArgs) auto
  let ?step = "process_one_arg (fnArg, lv a, tm a) acc"

  have fold_noFuel: "fold process_one_arg (zip fnArgs' (zip (map lv as) (map tm as))) ?step
                      \<noteq> Inl InsufficientFuel"
    using Cons.prems(4) fnArgs_eq by simp

  (* The first step is not out of fuel, since the fold would propagate that *)
  have step_noFuel: "?step \<noteq> Inl InsufficientFuel"
  proof
    assume "?step = Inl InsufficientFuel"
    thus False using fold_noFuel by (simp add: fold_process_one_arg_error)
  qed

  have step_eq: "process_one_arg (fnArg, lv' a, tm' a) acc = ?step"
    by (rule process_one_arg_agree[OF _ _ step_noFuel]) (use Cons.prems(1,2) in simp_all)

  have tail_eq: "fold process_one_arg (zip fnArgs' (zip (map lv' as) (map tm' as))) ?step
               = fold process_one_arg (zip fnArgs' (zip (map lv as) (map tm as))) ?step"
    by (rule Cons.hyps[OF _ _ len_tail fold_noFuel]) (use Cons.prems(1,2) in simp_all)

  show ?case using fnArgs_eq step_eq tail_eq by simp
qed

(* If the fold succeeds on the first family of results, then the second family
   has the same term results, and the same lvalue results at the Ref arguments.
   (An extern function call reads these directly, not through the fold.) *)
lemma fold_process_one_arg_ok_results_agree:
  assumes tm_agree: "\<forall>a \<in> set argTms. tm a \<noteq> Inl InsufficientFuel \<longrightarrow> tm' a = tm a"
    and lv_agree: "\<forall>a \<in> set argTms. lv a \<noteq> Inl InsufficientFuel \<longrightarrow> lv' a = lv a"
    and len_eq: "length fnArgs = length argTms"
    and ok: "fold process_one_arg (zip fnArgs (zip (map lv argTms) (map tm argTms))) acc
              = Inr finalState"
  shows "map tm' argTms = map tm argTms"
    and "map (\<lambda>((_, vr), refResult). if vr = Ref then refResult else Inl TypeError)
             (zip fnArgs (map lv' argTms))
       = map (\<lambda>((_, vr), refResult). if vr = Ref then refResult else Inl TypeError)
             (zip fnArgs (map lv argTms))"
proof -
  have len_ref: "length fnArgs = length (map lv argTms)" using len_eq by simp
  have len_val: "length (map lv argTms) = length (map tm argTms)" by simp

  (* The fold succeeded, so every term result is a value *)
  show "map tm' argTms = map tm argTms"
  proof (rule map_eq_conv[THEN iffD2], rule ballI)
    fix a assume a_in: "a \<in> set argTms"
    hence "tm a \<in> set (map tm argTms)" by simp
    hence "\<exists>val. tm a = Inr val"
      using fold_process_one_arg_all_ok[OF ok len_ref len_val] by blast
    thus "tm' a = tm a" using tm_agree a_in by auto
  qed

  (* For a Ref argument, the lvalue result is a value too *)
  let ?filter_refs = "\<lambda>refResults. map (\<lambda>((_, vr), refResult).
                          if vr = Ref then refResult else Inl TypeError)
                        (zip fnArgs refResults)"
  show "?filter_refs (map lv' argTms) = ?filter_refs (map lv argTms)"
  proof (rule nth_equalityI)
    show "length (?filter_refs (map lv' argTms)) = length (?filter_refs (map lv argTms))"
      by simp
  next
    fix i assume "i < length (?filter_refs (map lv' argTms))"
    hence i_bound: "i < length fnArgs" by simp
    hence i_bound': "i < length argTms" using len_eq by simp
    obtain argName argVr where fnArg_eq: "fnArgs ! i = (argName, argVr)"
      by (cases "fnArgs ! i")
    show "?filter_refs (map lv' argTms) ! i = ?filter_refs (map lv argTms) ! i"
    proof (cases argVr)
      case Var
      thus ?thesis using i_bound i_bound' fnArg_eq by simp
    next
      case Ref
      have a_in: "argTms ! i \<in> set argTms" using i_bound' by simp
      have in_zip: "(argTms ! i, (argName, Ref)) \<in> set (zip argTms fnArgs)"
        using i_bound' fnArg_eq Ref len_eq by (auto simp: set_zip intro!: exI[of _ i])
      have "\<exists>lval. lv (argTms ! i) = Inr lval"
        using fold_process_one_arg_ref_lvalue_ok[OF ok len_eq _ len_val refl in_zip] by simp
      hence "lv' (argTms ! i) = lv (argTms ! i)" using lv_agree a_in by auto
      thus ?thesis using i_bound i_bound' fnArg_eq Ref by simp
    qed
  qed
qed


(* ========================================================================== *)
(* Fuel monotonicity for default_value *)
(* ========================================================================== *)

lemma default_value_fuel_mono:
  shows default_value_mono:
          "default_value f (state :: 'w InterpState) ty \<noteq> Inl InsufficientFuel
             \<Longrightarrow> \<forall>f'\<ge>f. default_value f' state ty = default_value f state ty"
    and default_value_list_mono:
          "default_value_list f (state :: 'w InterpState) tys \<noteq> Inl InsufficientFuel
             \<Longrightarrow> \<forall>f'\<ge>f. default_value_list f' state tys = default_value_list f state tys"
proof (induction rule: default_value_default_value_list.induct)
  case (1 uu uv)
  then show ?case by simp
next
  case (2 uw ux)
  then show ?case by (metis Suc_le_D default_value.simps(2))
next
  case (3 uy uz sign bits)
  then show ?case by (metis Suc_le_D default_value.simps(3))
next
  case (4 fuel state flds)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "default_value (Suc fuel) state (CoreTy_Record flds) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "default_value_list fuel state (map snd flds) \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    with "4.IH" have IH: "\<forall>f'\<ge>fuel. default_value_list f' state (map snd flds)
                                       = default_value_list fuel state (map snd flds)" by blast
    from IH f''_ge have
      "default_value_list f'' state (map snd flds) = default_value_list fuel state (map snd flds)"
      by blast
    with f'_eq show "default_value f' state (CoreTy_Record flds)
                       = default_value (Suc fuel) state (CoreTy_Record flds)" by simp
  qed
next
  case (5 fuel state dtName tyArgs)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "default_value (Suc fuel) state (CoreTy_Datatype dtName tyArgs)
                     \<noteq> Inl InsufficientFuel"
    show "default_value f' state (CoreTy_Datatype dtName tyArgs)
            = default_value (Suc fuel) state (CoreTy_Datatype dtName tyArgs)"
    proof (cases "fmlookup (IS_DefaultCtors state) dtName")
      case None
      thus ?thesis using f'_eq by simp
    next
      case (Some triple)
      obtain ctorName rest where pair1: "(ctorName, rest) = triple" by (cases triple) auto
      obtain tyvars payloadTy where pair2: "(tyvars, payloadTy) = rest" by (cases rest) auto
      from pair1 pair2 have triple_eq: "triple = (ctorName, tyvars, payloadTy)" by simp
      show ?thesis
      proof (cases "length tyvars = length tyArgs")
        case False
        thus ?thesis using Some triple_eq f'_eq by simp
      next
        case True
        let ?subst = "fmap_of_list (zip tyvars tyArgs)"
        let ?substTy = "apply_subst ?subst payloadTy"
        from noFuel Some triple_eq True
        have sub_noFuel: "default_value fuel state ?substTy \<noteq> Inl InsufficientFuel"
          by (auto simp: Let_def split: sum.splits)
        from "5.IH"[OF Some pair1 pair2 True refl refl sub_noFuel]
        have IH: "\<forall>f'\<ge>fuel. default_value f' state ?substTy = default_value fuel state ?substTy" .
        from IH f''_ge have
          "default_value f'' state ?substTy = default_value fuel state ?substTy" by blast
        with f'_eq Some triple_eq True show ?thesis by (simp add: Let_def)
      qed
    qed
  qed
next
  case (6 fuel state elemTy dims)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "default_value (Suc fuel) state (CoreTy_Array elemTy dims)
                     \<noteq> Inl InsufficientFuel"
    show "default_value f' state (CoreTy_Array elemTy dims)
            = default_value (Suc fuel) state (CoreTy_Array elemTy dims)"
    proof (cases "list_all (\<lambda>d. dim_category d = DimCat_Fixed) dims")
      case False
      thus ?thesis using f'_eq by simp
    next
      case True
      with noFuel have sub_noFuel: "default_value fuel state elemTy \<noteq> Inl InsufficientFuel"
        by (auto simp: Let_def split: sum.splits)
      from "6.IH"[OF True refl sub_noFuel]
      have IH: "\<forall>f'\<ge>fuel. default_value f' state elemTy = default_value fuel state elemTy" .
      from IH f''_ge have "default_value f'' state elemTy = default_value fuel state elemTy"
        by blast
      with f'_eq True show ?thesis by (simp add: Let_def)
    qed
  qed
next
  case (7 va vb) then show ?case by (metis Suc_le_D default_value.simps(7))
next
  case (8 vc vd) then show ?case by (metis Suc_le_D default_value.simps(8))
next
  case (9 ve vf vg) then show ?case by (metis Suc_le_D default_value.simps(9))
next
  case (10 vh vi) then show ?case by simp
next
  case (11 vj vk) then show ?case by (metis Suc_le_D default_value_list.simps(2))
next
  case (12 fuel state ty tys)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "default_value_list (Suc fuel) state (ty # tys) \<noteq> Inl InsufficientFuel"
    hence head_noFuel: "default_value fuel state ty \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH_head: "\<forall>f'\<ge>fuel. default_value f' state ty = default_value fuel state ty"
      using "12.IH"(1) by blast
    show "default_value_list f' state (ty # tys)
            = default_value_list (Suc fuel) state (ty # tys)"
    proof (cases "default_value fuel state ty")
      case (Inl err)
      hence "default_value f'' state ty = Inl err" using IH_head f''_ge by metis
      thus ?thesis using f'_eq Inl by simp
    next
      case (Inr v)
      from noFuel Inr have tail_noFuel:
        "default_value_list fuel state tys \<noteq> Inl InsufficientFuel"
        by (auto split: sum.splits)
      hence IH_tail:
        "\<forall>f'\<ge>fuel. default_value_list f' state tys = default_value_list fuel state tys"
        using "12.IH"(2) Inr by blast
      have "default_value f'' state ty = Inr v" using IH_head Inr f''_ge by metis
      moreover have "default_value_list f'' state tys = default_value_list fuel state tys"
        using IH_tail f''_ge by metis
      ultimately show ?thesis using f'_eq Inr by simp
    qed
  qed
qed


(* ========================================================================== *)
(* Fuel monotonicity *)
(* ========================================================================== *)

lemma interp_fuel_mono:
  shows interp_term_fuel_mono:
            "interp_term d f (state :: 'w InterpState) tm \<noteq> Inl InsufficientFuel
               \<Longrightarrow> \<forall>f'\<ge>f. interp_term d f' state tm = interp_term d f state tm"
    and interp_term_list_fuel_mono:
            "interp_term_list d f (state :: 'w InterpState) tms \<noteq> Inl InsufficientFuel
               \<Longrightarrow> \<forall>f'\<ge>f. interp_term_list d f' state tms = interp_term_list d f state tms"
    and interp_writable_lvalue_fuel_mono:
            "interp_writable_lvalue d f (state :: 'w InterpState) tm \<noteq> Inl InsufficientFuel
               \<Longrightarrow> \<forall>f'\<ge>f. interp_writable_lvalue d f' state tm = interp_writable_lvalue d f state tm"
    and interp_statement_fuel_mono:
            "interp_statement d f (state :: 'w InterpState) stmt \<noteq> Inl InsufficientFuel
               \<Longrightarrow> \<forall>f'\<ge>f. interp_statement d f' state stmt = interp_statement d f state stmt"
    and interp_statement_list_fuel_mono:
            "interp_statement_list d f (state :: 'w InterpState) stmts \<noteq> Inl InsufficientFuel
               \<Longrightarrow> \<forall>f'\<ge>f. interp_statement_list d f' state stmts = interp_statement_list d f state stmts"
    and interp_function_call_fuel_mono:
            "interp_function_call d f (state :: 'w InterpState) fnName argTys argTms \<noteq> Inl InsufficientFuel
               \<Longrightarrow> \<forall>f'\<ge>f. interp_function_call d f' state fnName argTys argTms
                    = interp_function_call d f state fnName argTys argTms"
proof (induction rule: interp_term_interp_term_list_interp_writable_lvalue_interp_statement_interp_statement_list_interp_function_call.induct)
  (* interp_term, fuel = 0 *)
  case (1 d state tm)
  then show ?case by simp
next
  (* LitBool *)
  case (2 d fuel state b)
  show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where "f' = Suc f''" using Suc_le_D by auto
    thus "interp_term d f' state (CoreTm_LitBool b)
            = interp_term d (Suc fuel) state (CoreTm_LitBool b)"
      by simp
  qed
next
  (* LitInt *)
  case (3 d fuel state i)
  show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where "f' = Suc f''" using Suc_le_D by auto
    thus "interp_term d f' state (CoreTm_LitInt i)
            = interp_term d (Suc fuel) state (CoreTm_LitInt i)"
      by simp
  qed
next
  (* LitArray *)
  case (4 d fuel state elemTy tms)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term d (Suc fuel) state (CoreTm_LitArray elemTy tms) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term_list d fuel state tms \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    with "4.IH" have IH: "\<forall>f'\<ge>fuel. interp_term_list d f' state tms = interp_term_list d fuel state tms"
      by blast
    from IH f''_ge have "interp_term_list d f'' state tms = interp_term_list d fuel state tms"
      by blast
    with f'_eq show "interp_term d f' state (CoreTm_LitArray elemTy tms)
                       = interp_term d (Suc fuel) state (CoreTm_LitArray elemTy tms)"
      by simp
  qed
next
  (* Var *)
  case (5 d fuel state varName)
  show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where "f' = Suc f''" using Suc_le_D by auto
    thus "interp_term d f' state (CoreTm_Var varName)
            = interp_term d (Suc fuel) state (CoreTm_Var varName)"
      by simp
  qed
next
  (* Cast *)
  case (6 d fuel state targetTy tm)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term d (Suc fuel) state (CoreTm_Cast targetTy tm) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term d fuel state tm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH: "\<forall>f'\<ge>fuel. interp_term d f' state tm = interp_term d fuel state tm"
      using "6.IH" by blast
    from IH f''_ge have "interp_term d f'' state tm = interp_term d fuel state tm"
      by blast
    with f'_eq show "interp_term d f' state (CoreTm_Cast targetTy tm)
                       = interp_term d (Suc fuel) state (CoreTm_Cast targetTy tm)"
      by simp
  qed
next
  (* Unop *)
  case (7 d fuel state op tm)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term d (Suc fuel) state (CoreTm_Unop op tm) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term d fuel state tm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH: "\<forall>f'\<ge>fuel. interp_term d f' state tm = interp_term d fuel state tm"
      using "7.IH" by blast
    from IH f''_ge have "interp_term d f'' state tm = interp_term d fuel state tm"
      by blast
    with f'_eq show "interp_term d f' state (CoreTm_Unop op tm)
                       = interp_term d (Suc fuel) state (CoreTm_Unop op tm)"
      by simp
  qed
next
  (* Binop *)
  case (8 d fuel state op lhsTm rhsTm)
  then show ?case
  proof (intro allI impI)
    fix f' assume f'_ge: "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term d (Suc fuel) state (CoreTm_Binop op lhsTm rhsTm) \<noteq> Inl InsufficientFuel"
    hence lhs_noFuel: "interp_term d fuel state lhsTm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH_lhs: "\<forall>f'\<ge>fuel. interp_term d f' state lhsTm = interp_term d fuel state lhsTm"
      using "8.IH"(1) by blast
    show "interp_term d f' state (CoreTm_Binop op lhsTm rhsTm)
            = interp_term d (Suc fuel) state (CoreTm_Binop op lhsTm rhsTm)"
    proof (cases "interp_term d fuel state lhsTm")
      case (Inl err)
      hence "interp_term d f'' state lhsTm = Inl err" using IH_lhs f''_ge by metis
      thus ?thesis using Inl f'_eq by simp
    next
      case (Inr lhsVal)
      have lhs_f'': "interp_term d f'' state lhsTm = Inr lhsVal" using IH_lhs Inr f''_ge by auto
      show ?thesis
      proof (cases "short_circuit op lhsVal")
        case (Some result)
        (* Short-circuit: the rhs is not evaluated, so the result is fuel-independent *)
        then show ?thesis using Inr lhs_f'' f'_eq by simp
      next
        case None
        hence rhs_noFuel: "interp_term d fuel state rhsTm \<noteq> Inl InsufficientFuel"
          using noFuel Inr by (auto split: sum.splits)
        hence IH_rhs: "\<forall>f'\<ge>fuel. interp_term d f' state rhsTm = interp_term d fuel state rhsTm"
          using "8.IH"(2) Inr None by blast
        have "interp_term d f'' state rhsTm = interp_term d fuel state rhsTm"
          using IH_rhs f''_ge by metis
        then show ?thesis using f'_eq Inr None lhs_f'' by simp
      qed
    qed
  qed
next
  (* Let *)
  case (9 d fuel state varName rhsTm bodyTm)
  then show ?case
  proof (intro allI impI)
    fix f' assume f'_ge: "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term d (Suc fuel) state (CoreTm_Let varName rhsTm bodyTm) \<noteq> Inl InsufficientFuel"
    hence rhs_noFuel: "interp_term d fuel state rhsTm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits prod.splits)
    hence IH_rhs: "\<forall>f'\<ge>fuel. interp_term d f' state rhsTm = interp_term d fuel state rhsTm"
      using "9.IH"(1) by blast
    show "interp_term d f' state (CoreTm_Let varName rhsTm bodyTm)
            = interp_term d (Suc fuel) state (CoreTm_Let varName rhsTm bodyTm)"
    proof (cases "interp_term d fuel state rhsTm")
      case (Inl err)
      hence "interp_term d f'' state rhsTm = Inl err" using IH_rhs f''_ge by metis
      thus ?thesis using Inl f'_eq by simp
    next
      case (Inr rhsVal)
      let ?state'' = "bind_const_local varName rhsVal state"
      have body_noFuel: "interp_term d fuel ?state'' bodyTm \<noteq> Inl InsufficientFuel"
        using noFuel Inr by (simp del: bind_const_local.simps)
      have IH_body: "\<forall>f'\<ge>fuel. interp_term d f' ?state'' bodyTm = interp_term d fuel ?state'' bodyTm"
        using "9.IH"(2)[OF Inr] body_noFuel by blast
      have "interp_term d f'' state rhsTm = Inr rhsVal" using IH_rhs Inr f''_ge by auto
      moreover have "interp_term d f'' ?state'' bodyTm = interp_term d fuel ?state'' bodyTm"
        using IH_body f''_ge by metis
      ultimately show ?thesis using f'_eq Inr
        by (simp del: bind_const_local.simps)
    qed
  qed
next
  (* FunctionCall *)
  case (10 d fuel state fnName argTypes argTms)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term d (Suc fuel) state (CoreTm_FunctionCall fnName argTypes argTms) \<noteq> Inl InsufficientFuel"
    show "interp_term d f' state (CoreTm_FunctionCall fnName argTypes argTms) =
          interp_term d (Suc fuel) state (CoreTm_FunctionCall fnName argTypes argTms)"
    proof (cases "is_pure_fun state fnName")
      case False
      thus ?thesis using f'_eq by simp
    next
      case True
      hence fc_noFuel: "interp_function_call d fuel state fnName argTypes argTms \<noteq> Inl InsufficientFuel"
        using noFuel by (auto split: sum.splits)
      hence IH_fc: "\<forall>f'\<ge>fuel. interp_function_call d f' state fnName argTypes argTms
                                = interp_function_call d fuel state fnName argTypes argTms"
        using "10.IH" True by blast
      from IH_fc f''_ge have "interp_function_call d f'' state fnName argTypes argTms
                                = interp_function_call d fuel state fnName argTypes argTms"
        by metis
      with f'_eq True show ?thesis by simp
    qed
  qed
next
  (* VariantCtor *)
  case (11 d fuel state ctorName tyArgs payloadTm)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term d (Suc fuel) state (CoreTm_VariantCtor ctorName tyArgs payloadTm) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term d fuel state payloadTm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH: "\<forall>f'\<ge>fuel. interp_term d f' state payloadTm = interp_term d fuel state payloadTm"
      using "11.IH" by blast
    from IH f''_ge have "interp_term d f'' state payloadTm = interp_term d fuel state payloadTm"
      by metis
    with f'_eq show "interp_term d f' state (CoreTm_VariantCtor ctorName tyArgs payloadTm) =
          interp_term d (Suc fuel) state (CoreTm_VariantCtor ctorName tyArgs payloadTm)"
      by simp
  qed
next
  (* Record *)
  case (12 d fuel state nameTermPairs)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term d (Suc fuel) state (CoreTm_Record nameTermPairs) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term_list d fuel state (map snd nameTermPairs) \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH: "\<forall>f'\<ge>fuel. interp_term_list d f' state (map snd nameTermPairs)
                             = interp_term_list d fuel state (map snd nameTermPairs)"
      using "12.IH" by blast
    from IH f''_ge have "interp_term_list d f'' state (map snd nameTermPairs)
                           = interp_term_list d fuel state (map snd nameTermPairs)"
      by metis
    with f'_eq show "interp_term d f' state (CoreTm_Record nameTermPairs)
                       = interp_term d (Suc fuel) state (CoreTm_Record nameTermPairs)"
      by simp
  qed
next
  (* RecordProj *)
  case (13 d fuel state tm fldName)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term d (Suc fuel) state (CoreTm_RecordProj tm fldName) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term d fuel state tm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH: "\<forall>f'\<ge>fuel. interp_term d f' state tm = interp_term d fuel state tm"
      using "13.IH" by blast
    from IH f''_ge have "interp_term d f'' state tm = interp_term d fuel state tm"
      by metis
    with f'_eq show "interp_term d f' state (CoreTm_RecordProj tm fldName)
                       = interp_term d (Suc fuel) state (CoreTm_RecordProj tm fldName)"
      by simp
  qed
next
  (* VariantProj *)
  case (14 d fuel state tm expectedCtorName)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term d (Suc fuel) state (CoreTm_VariantProj tm expectedCtorName) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term d fuel state tm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH: "\<forall>f'\<ge>fuel. interp_term d f' state tm = interp_term d fuel state tm"
      using "14.IH" by blast
    from IH f''_ge have "interp_term d f'' state tm = interp_term d fuel state tm"
      by metis
    with f'_eq show "interp_term d f' state (CoreTm_VariantProj tm expectedCtorName)
                       = interp_term d (Suc fuel) state (CoreTm_VariantProj tm expectedCtorName)"
      by simp
  qed
next
  (* ArrayProj *)
  case (15 d fuel state arrayTm idxTms)
  then show ?case
  proof (intro allI impI)
    fix f' assume f'_ge: "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term d (Suc fuel) state (CoreTm_ArrayProj arrayTm idxTms) \<noteq> Inl InsufficientFuel"
    hence arr_noFuel: "interp_term d fuel state arrayTm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH_arr: "\<forall>f'\<ge>fuel. interp_term d f' state arrayTm = interp_term d fuel state arrayTm"
      using "15.IH"(1) by blast
    show "interp_term d f' state (CoreTm_ArrayProj arrayTm idxTms)
            = interp_term d (Suc fuel) state (CoreTm_ArrayProj arrayTm idxTms)"
    proof (cases "interp_term d fuel state arrayTm")
      case (Inl err)
      hence "interp_term d f'' state arrayTm = Inl err" using IH_arr f''_ge by metis
      thus ?thesis using Inl f'_eq by simp
    next
      case (Inr arrVal)
      show ?thesis
      proof (cases arrVal)
        case (CV_Array sizes elemMap)
        hence idx_noFuel: "interp_term_list d fuel state idxTms \<noteq> Inl InsufficientFuel"
          using noFuel Inr by (auto split: sum.splits)
        hence IH_idx: "\<forall>f'\<ge>fuel. interp_term_list d f' state idxTms = interp_term_list d fuel state idxTms"
          using "15.IH"(2) Inr CV_Array by blast
        have "interp_term d f'' state arrayTm = Inr arrVal" using IH_arr Inr f''_ge by metis
        moreover have "interp_term_list d f'' state idxTms = interp_term_list d fuel state idxTms"
          using IH_idx f''_ge by metis
        ultimately show ?thesis using f'_eq Inr CV_Array by simp
      next
        case (CV_Bool x1)
        have "interp_term d f'' state arrayTm = Inr arrVal" using IH_arr Inr f''_ge by metis
        thus ?thesis using f'_eq CV_Bool Inr by simp
      next
        case (CV_FiniteInt x21 x22 x23)
        have "interp_term d f'' state arrayTm = Inr arrVal" using IH_arr Inr f''_ge by metis
        thus ?thesis using f'_eq CV_FiniteInt Inr by simp
      next
        case (CV_Record x4)
        have "interp_term d f'' state arrayTm = Inr arrVal" using IH_arr Inr f''_ge by metis
        thus ?thesis using f'_eq CV_Record Inr by simp
      next
        case (CV_Variant x51 x52)
        have "interp_term d f'' state arrayTm = Inr arrVal" using IH_arr Inr f''_ge by metis
        thus ?thesis using f'_eq CV_Variant Inr by simp
      next
        case (CV_Int x7)
        have "interp_term d f'' state arrayTm = Inr arrVal" using IH_arr Inr f''_ge by metis
        thus ?thesis using f'_eq CV_Int Inr by simp
      next
        case (CV_Real x8)
        have "interp_term d f'' state arrayTm = Inr arrVal" using IH_arr Inr f''_ge by metis
        thus ?thesis using f'_eq CV_Real Inr by simp
      qed
    qed
  qed
next
  (* Match *)
  case (16 d fuel state scrutTm arms)
  then show ?case
  proof (intro allI impI)
    fix f' assume f'_ge: "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term d (Suc fuel) state (CoreTm_Match scrutTm arms) \<noteq> Inl InsufficientFuel"
    hence scrut_noFuel: "interp_term d fuel state scrutTm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH_scrut: "\<forall>f'\<ge>fuel. interp_term d f' state scrutTm = interp_term d fuel state scrutTm"
      using "16.IH"(1) by blast
    show "interp_term d f' state (CoreTm_Match scrutTm arms)
            = interp_term d (Suc fuel) state (CoreTm_Match scrutTm arms)"
    proof (cases "interp_term d fuel state scrutTm")
      case (Inl err)
      hence "interp_term d f'' state scrutTm = Inl err" using IH_scrut f''_ge by metis
      thus ?thesis using Inl f'_eq by simp
    next
      case (Inr scrutVal)
      show ?thesis
      proof (cases "find_matching_arm scrutVal arms")
        case (Inl err)
        hence "interp_term d f'' state scrutTm = Inr scrutVal" using IH_scrut Inr f''_ge by metis
        thus ?thesis using f'_eq Inr Inl by simp
      next
        case (Inr armTm)
        hence arm_noFuel: "interp_term d fuel state armTm \<noteq> Inl InsufficientFuel"
          using noFuel \<open>interp_term d fuel state scrutTm = Inr scrutVal\<close>
          by (auto split: sum.splits)
        hence IH_arm: "\<forall>f'\<ge>fuel. interp_term d f' state armTm = interp_term d fuel state armTm"
          using "16.IH"(2) \<open>interp_term d fuel state scrutTm = Inr scrutVal\<close> Inr by blast
        have "interp_term d f'' state scrutTm = interp_term d fuel state scrutTm"
          using IH_scrut f''_ge by metis
        moreover have "interp_term d f'' state armTm = interp_term d fuel state armTm"
          using IH_arm f''_ge by metis
        ultimately show ?thesis
          using f'_eq \<open>interp_term d fuel state scrutTm = Inr scrutVal\<close> Inr by simp
      qed
    qed
  qed
next
  (* Sizeof *)
  case (17 d fuel state tm)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term d (Suc fuel) state (CoreTm_Sizeof tm) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term d fuel state tm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH: "\<forall>f'\<ge>fuel. interp_term d f' state tm = interp_term d fuel state tm"
      using "17.IH" by blast
    from IH f''_ge have "interp_term d f'' state tm = interp_term d fuel state tm"
      by metis
    with f'_eq show "interp_term d f' state (CoreTm_Sizeof tm)
                       = interp_term d (Suc fuel) state (CoreTm_Sizeof tm)"
      by simp
  qed
next
  (* Quantifier, depth = 0: always InsufficientFuel *)
  case (18 fuel state quant varName varTy bodyTm)
  then show ?case by simp
next
  (* Quantifier, depth > 0: the result does not mention the fuel *)
  case (19 d fuel state quant varName varTy bodyTm)
  show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where "f' = Suc f''" using Suc_le_D by auto
    thus "interp_term (Suc d) f' state (CoreTm_Quantifier quant varName varTy bodyTm)
            = interp_term (Suc d) (Suc fuel) state (CoreTm_Quantifier quant varName varTy bodyTm)"
      by simp
  qed
next
  (* Allocated: always false *)
  case (20 d fuel state tm)
  show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where "f' = Suc f''" using Suc_le_D by auto
    thus "interp_term d f' state (CoreTm_Allocated tm)
            = interp_term d (Suc fuel) state (CoreTm_Allocated tm)"
      by simp
  qed
next
  (* Old *)
  case (21 d fuel state tm)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term d (Suc fuel) state (CoreTm_Old tm) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term d fuel state tm \<noteq> Inl InsufficientFuel"
      by simp
    hence IH: "\<forall>f'\<ge>fuel. interp_term d f' state tm = interp_term d fuel state tm"
      using "21.IH" by blast
    from IH f''_ge have "interp_term d f'' state tm = interp_term d fuel state tm"
      by metis
    with f'_eq show "interp_term d f' state (CoreTm_Old tm)
                       = interp_term d (Suc fuel) state (CoreTm_Old tm)"
      by simp
  qed
next
  (* Default - dispatches to default_value *)
  case (22 d fuel state ty)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term d (Suc fuel) state (CoreTm_Default ty) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel:
      "default_value fuel state (apply_subst (IS_TyArgs state) ty) \<noteq> Inl InsufficientFuel"
      by simp
    from default_value_fuel_mono(1)[OF sub_noFuel] f''_ge
    have "default_value f'' state (apply_subst (IS_TyArgs state) ty)
            = default_value fuel state (apply_subst (IS_TyArgs state) ty)" by blast
    with f'_eq show "interp_term d f' state (CoreTm_Default ty)
                       = interp_term d (Suc fuel) state (CoreTm_Default ty)" by simp
  qed
next
  (* interp_writable_lvalue, fuel = 0 *)
  case (23 d state tm)
  then show ?case by simp
next
  (* interp_writable_lvalue, fuel > 0 *)
  case (24 d fuel state tm)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_writable_lvalue d (Suc fuel) state tm \<noteq> Inl InsufficientFuel"
    show "interp_writable_lvalue d f' state tm = interp_writable_lvalue d (Suc fuel) state tm"
    proof (cases tm)
      case (CoreTm_Var varName)
      thus ?thesis using f'_eq by simp
    next
      case (CoreTm_RecordProj tm' fldName)
      hence sub_noFuel: "interp_writable_lvalue d fuel state tm' \<noteq> Inl InsufficientFuel"
        using noFuel by (auto split: sum.splits)
      hence IH: "\<forall>f'\<ge>fuel. interp_writable_lvalue d f' state tm' = interp_writable_lvalue d fuel state tm'"
        using "24.IH"(2) CoreTm_RecordProj by blast
      from IH f''_ge have "interp_writable_lvalue d f'' state tm' = interp_writable_lvalue d fuel state tm'"
        by metis
      thus ?thesis using f'_eq CoreTm_RecordProj by simp
    next
      case (CoreTm_VariantProj tm' ctorName)
      hence sub_noFuel: "interp_writable_lvalue d fuel state tm' \<noteq> Inl InsufficientFuel"
        using noFuel by (auto split: sum.splits)
      hence IH: "\<forall>f'\<ge>fuel. interp_writable_lvalue d f' state tm' = interp_writable_lvalue d fuel state tm'"
        using "24.IH"(3) CoreTm_VariantProj by blast
      from IH f''_ge have "interp_writable_lvalue d f'' state tm' = interp_writable_lvalue d fuel state tm'"
        by metis
      thus ?thesis using f'_eq CoreTm_VariantProj by simp
    next
      case (CoreTm_ArrayProj tm' indexTms)
      hence lv_noFuel: "interp_writable_lvalue d fuel state tm' \<noteq> Inl InsufficientFuel"
        using noFuel by (auto split: sum.splits)
      hence IH_lv: "\<forall>f'\<ge>fuel. interp_writable_lvalue d f' state tm' = interp_writable_lvalue d fuel state tm'"
        using "24.IH"(4) CoreTm_ArrayProj by blast
      show ?thesis
      proof (cases "interp_writable_lvalue d fuel state tm'")
        case (Inl err)
        hence "interp_writable_lvalue d f'' state tm' = Inl err" using IH_lv f''_ge by metis
        thus ?thesis using f'_eq CoreTm_ArrayProj Inl by simp
      next
        case (Inr addrPath)
        hence idx_noFuel: "interp_term_list d fuel state indexTms \<noteq> Inl InsufficientFuel"
          using noFuel CoreTm_ArrayProj by (auto split: sum.splits)
        hence IH_idx: "\<forall>f'\<ge>fuel. interp_term_list d f' state indexTms = interp_term_list d fuel state indexTms"
          using "24.IH"(5) CoreTm_ArrayProj Inr
          by (metis prod.exhaust)
        have "interp_writable_lvalue d f'' state tm' = Inr addrPath" using IH_lv Inr f''_ge by metis
        moreover have "interp_term_list d f'' state indexTms = interp_term_list d fuel state indexTms"
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
      case (CoreTm_LitArray x1 x2)
      thus ?thesis using f'_eq by simp
    next
      case (CoreTm_Cast targetTy tm')
      show ?thesis
      proof (cases targetTy)
        case (CoreTy_Array elemTy dims)
        hence lv_noFuel: "interp_writable_lvalue d fuel state tm' \<noteq> Inl InsufficientFuel"
          using noFuel CoreTm_Cast by (auto split: sum.splits)
        hence IH: "\<forall>f'\<ge>fuel. interp_writable_lvalue d f' state tm' = interp_writable_lvalue d fuel state tm'"
          using "24.IH"(1) CoreTm_Cast CoreTy_Array by blast
        from IH f''_ge have "interp_writable_lvalue d f'' state tm' = interp_writable_lvalue d fuel state tm'"
          by metis
        thus ?thesis using f'_eq CoreTm_Cast CoreTy_Array by simp
      qed (simp_all add: f'_eq CoreTm_Cast)
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
    next
      case (CoreTm_Default x)
      thus ?thesis using f'_eq by simp
    qed
  qed
next
  (* interp_term_list, fuel = 0 *)
  case (25 d state tms)
  then show ?case by simp
next
  (* interp_term_list, empty list *)
  case (26 d fuel state)
  show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where "f' = Suc f''" using Suc_le_D by auto
    thus "interp_term_list d f' state [] = interp_term_list d (Suc fuel) state []"
      by simp
  qed
next
  (* interp_term_list, cons *)
  case (27 d fuel state tm tms)
  then show ?case
  proof (intro allI impI)
    fix f' assume f'_ge: "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_term_list d (Suc fuel) state (tm # tms) \<noteq> Inl InsufficientFuel"
    hence tm_noFuel: "interp_term d fuel state tm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH_tm: "\<forall>f'\<ge>fuel. interp_term d f' state tm = interp_term d fuel state tm"
      using "27.IH"(1) by blast
    show "interp_term_list d f' state (tm # tms) = interp_term_list d (Suc fuel) state (tm # tms)"
    proof (cases "interp_term d fuel state tm")
      case (Inl err)
      hence "interp_term d f'' state tm = Inl err" using IH_tm f''_ge by metis
      thus ?thesis using Inl f'_eq by simp
    next
      case (Inr val)
      hence tms_noFuel: "interp_term_list d fuel state tms \<noteq> Inl InsufficientFuel"
        using noFuel by (auto split: sum.splits)
      hence IH_tms: "\<forall>f'\<ge>fuel. interp_term_list d f' state tms = interp_term_list d fuel state tms"
        using "27.IH"(2) Inr by blast
      have "interp_term d f'' state tm = Inr val" using IH_tm Inr f''_ge by metis
      moreover have "interp_term_list d f'' state tms = interp_term_list d fuel state tms"
        using IH_tms f''_ge by metis
      ultimately show ?thesis using f'_eq Inr by simp
    qed
  qed
next
  (* interp_statement, fuel = 0 *)
  case (28 d state stmt)
  then show ?case by simp
next
  (* VarDecl Var.
     The initializer is an ordinary (pure) term; just one interp_term sub-call. *)
  case (29 d fuel state declGhost varName varTy initialTm)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_statement d (Suc fuel) state
                      (CoreStmt_VarDecl declGhost varName Var varTy initialTm) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term d fuel state initialTm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits prod.splits)
    hence IH: "\<forall>f'\<ge>fuel. interp_term d f' state initialTm = interp_term d fuel state initialTm"
      using "29.IH"(1) by blast
    from IH f''_ge have tm_eq: "interp_term d f'' state initialTm = interp_term d fuel state initialTm"
      by metis
    with f'_eq show "interp_statement d f' state (CoreStmt_VarDecl declGhost varName Var varTy initialTm) =
          interp_statement d (Suc fuel) state (CoreStmt_VarDecl declGhost varName Var varTy initialTm)"
      by simp
  qed
next
  (* VarDeclCall.
     Runs the call then applies the optional cast; only the call uses fuel. *)
  case (30 d fuel state declGhost varName varTy castOpt fnName argTys argTms)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_statement d (Suc fuel) state
                      (CoreStmt_VarDeclCall declGhost varName varTy castOpt fnName argTys argTms)
                        \<noteq> Inl InsufficientFuel"
    hence fc_noFuel: "interp_function_call d fuel state fnName argTys argTms \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits prod.splits)
    hence IH_fc: "\<forall>f'\<ge>fuel. interp_function_call d f' state fnName argTys argTms
                              = interp_function_call d fuel state fnName argTys argTms"
      using "30.IH" by blast
    from IH_fc f''_ge have
      "interp_function_call d f'' state fnName argTys argTms
         = interp_function_call d fuel state fnName argTys argTms"
      by metis
    with f'_eq show "interp_statement d f' state
                       (CoreStmt_VarDeclCall declGhost varName varTy castOpt fnName argTys argTms) =
          interp_statement d (Suc fuel) state
                       (CoreStmt_VarDeclCall declGhost varName varTy castOpt fnName argTys argTms)"
      by (simp split: sum.splits prod.splits)
  qed
next
  (* VarDecl Ref *)
  case (31 d fuel state declGhost varName varTy lvalueTm)
  then show ?case
  proof (intro allI impI)
    fix f' assume f'_ge: "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_statement d (Suc fuel) state
                      (CoreStmt_VarDecl declGhost varName Ref varTy lvalueTm) \<noteq> Inl InsufficientFuel"
    show "interp_statement d f' state (CoreStmt_VarDecl declGhost varName Ref varTy lvalueTm) =
          interp_statement d (Suc fuel) state (CoreStmt_VarDecl declGhost varName Ref varTy lvalueTm)"
    proof (cases "lvalue_base_name lvalueTm")
      case None
      (* Not a syntactic lvalue: both sides return TypeError *)
      then show ?thesis using f'_eq by simp
    next
      case (Some baseName)
      show ?thesis
      proof (cases "baseName |\<in>| IS_ConstLocals state
                    \<or> (fmlookup (IS_Locals state) baseName = None
                       \<and> fmlookup (IS_Refs state) baseName = None)")
        case True
        (* Const or global: both sides use interp_term *)
        have tm_noFuel: "interp_term d fuel state lvalueTm \<noteq> Inl InsufficientFuel"
          using noFuel Some True by (auto split: sum.splits prod.splits)
        have IH_tm: "\<forall>f'\<ge>fuel. interp_term d f' state lvalueTm = interp_term d fuel state lvalueTm"
          using "31.IH" Some True tm_noFuel by blast
        from IH_tm f''_ge
        have "interp_term d f'' state lvalueTm = interp_term d fuel state lvalueTm" by metis
        then show ?thesis using f'_eq Some True by simp
      next
        case False
        (* Not const: both sides use interp_writable_lvalue *)
        have lv_noFuel: "interp_writable_lvalue d fuel state lvalueTm \<noteq> Inl InsufficientFuel"
          using noFuel Some False by (auto split: sum.splits)
        have IH_lv: "\<forall>f'\<ge>fuel. interp_writable_lvalue d f' state lvalueTm
                                  = interp_writable_lvalue d fuel state lvalueTm"
          using "31.IH" Some False lv_noFuel by blast
        from IH_lv f''_ge
        have "interp_writable_lvalue d f'' state lvalueTm = interp_writable_lvalue d fuel state lvalueTm"
          by metis
        then show ?thesis using f'_eq Some False by (auto split: sum.splits)
      qed
    qed
  qed
next
  (* Assign.
     The rhs is an ordinary (pure) term: resolve the lhs, then interp_term. *)
  case (32 d fuel state assignGhost lhsLvalue rhsTm)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_statement d (Suc fuel) state (CoreStmt_Assign assignGhost lhsLvalue rhsTm)
                      \<noteq> Inl InsufficientFuel"
    hence lhs_noFuel: "interp_writable_lvalue d fuel state lhsLvalue \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH_lhs: "\<forall>f'\<ge>fuel. interp_writable_lvalue d f' state lhsLvalue
                               = interp_writable_lvalue d fuel state lhsLvalue"
      using "32.IH"(1) by blast
    show "interp_statement d f' state (CoreStmt_Assign assignGhost lhsLvalue rhsTm) =
          interp_statement d (Suc fuel) state (CoreStmt_Assign assignGhost lhsLvalue rhsTm)"
    proof (cases "interp_writable_lvalue d fuel state lhsLvalue")
      case (Inl err)
      hence "interp_writable_lvalue d f'' state lhsLvalue = Inl err" using IH_lhs f''_ge by metis
      thus ?thesis using Inl f'_eq by simp
    next
      case (Inr addrPath)
      obtain addr path where addrPath_eq: "addrPath = (addr, path)" by (cases addrPath)
      hence rhs_noFuel: "interp_term d fuel state rhsTm \<noteq> Inl InsufficientFuel"
        using noFuel Inr by (auto split: sum.splits)
      hence IH_rhs: "\<forall>f'\<ge>fuel. interp_term d f' state rhsTm = interp_term d fuel state rhsTm"
        using "32.IH"(2) Inr addrPath_eq by blast
      have "interp_writable_lvalue d f'' state lhsLvalue = Inr addrPath" using IH_lhs Inr f''_ge by metis
      moreover have "interp_term d f'' state rhsTm = interp_term d fuel state rhsTm"
        using IH_rhs f''_ge by metis
      ultimately show ?thesis using f'_eq Inr addrPath_eq by simp
    qed
  qed
next
  (* AssignCall.
     Resolve the lhs, run the call, apply the cast, store. *)
  case (33 d fuel state assignGhost lhsLvalue castOpt fnName argTys argTms)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_statement d (Suc fuel) state
                      (CoreStmt_AssignCall assignGhost lhsLvalue castOpt fnName argTys argTms)
                        \<noteq> Inl InsufficientFuel"
    hence lhs_noFuel: "interp_writable_lvalue d fuel state lhsLvalue \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH_lhs: "\<forall>f'\<ge>fuel. interp_writable_lvalue d f' state lhsLvalue
                               = interp_writable_lvalue d fuel state lhsLvalue"
      using "33.IH"(1) by blast
    show "interp_statement d f' state
            (CoreStmt_AssignCall assignGhost lhsLvalue castOpt fnName argTys argTms) =
          interp_statement d (Suc fuel) state
            (CoreStmt_AssignCall assignGhost lhsLvalue castOpt fnName argTys argTms)"
    proof (cases "interp_writable_lvalue d fuel state lhsLvalue")
      case (Inl err)
      hence "interp_writable_lvalue d f'' state lhsLvalue = Inl err" using IH_lhs f''_ge by metis
      thus ?thesis using Inl f'_eq by simp
    next
      case (Inr addrPath)
      obtain addr path where addrPath_eq: "addrPath = (addr, path)" by (cases addrPath)
      hence fc_noFuel: "interp_function_call d fuel state fnName argTys argTms \<noteq> Inl InsufficientFuel"
        using noFuel Inr by (auto split: sum.splits prod.splits)
      hence IH_fc: "\<forall>f'\<ge>fuel. interp_function_call d f' state fnName argTys argTms
                                = interp_function_call d fuel state fnName argTys argTms"
        using "33.IH"(2) addrPath_eq Inr by blast
      have "interp_writable_lvalue d f'' state lhsLvalue = Inr addrPath" using IH_lhs Inr f''_ge by metis
      moreover have "interp_function_call d f'' state fnName argTys argTms
                       = interp_function_call d fuel state fnName argTys argTms"
        using IH_fc f''_ge by metis
      ultimately show ?thesis using f'_eq Inr addrPath_eq by (simp split: sum.splits prod.splits)
    qed
  qed
next
  (* Swap *)
  case (34 d fuel state swapGhost lhsTm rhsTm)
  then show ?case
  proof (intro allI impI)
    fix f' assume f'_ge: "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_statement d (Suc fuel) state (CoreStmt_Swap swapGhost lhsTm rhsTm)
                      \<noteq> Inl InsufficientFuel"
    hence lhs_noFuel: "interp_writable_lvalue d fuel state lhsTm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH_lhs: "\<forall>f'\<ge>fuel. interp_writable_lvalue d f' state lhsTm
                               = interp_writable_lvalue d fuel state lhsTm"
      using "34.IH"(1) by blast
    show "interp_statement d f' state (CoreStmt_Swap swapGhost lhsTm rhsTm) =
          interp_statement d (Suc fuel) state (CoreStmt_Swap swapGhost lhsTm rhsTm)"
    proof (cases "interp_writable_lvalue d fuel state lhsTm")
      case (Inl err)
      hence "interp_writable_lvalue d f'' state lhsTm = Inl err" using IH_lhs f''_ge by metis
      thus ?thesis using Inl f'_eq by simp
    next
      case (Inr lhsLvalue)
      hence rhs_noFuel: "interp_writable_lvalue d fuel state rhsTm \<noteq> Inl InsufficientFuel"
        using noFuel by (auto split: sum.splits)
      hence IH_rhs: "\<forall>f'\<ge>fuel. interp_writable_lvalue d f' state rhsTm
                                 = interp_writable_lvalue d fuel state rhsTm"
        using "34.IH"(2) Inr by blast
      have "interp_writable_lvalue d f'' state lhsTm = Inr lhsLvalue" using IH_lhs Inr f''_ge by metis
      moreover have "interp_writable_lvalue d f'' state rhsTm = interp_writable_lvalue d fuel state rhsTm"
        using IH_rhs f''_ge by metis
      ultimately show ?thesis using f'_eq Inr by simp
    qed
  qed
next
  (* Return *)
  case (35 d fuel state tm)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_statement d (Suc fuel) state (CoreStmt_Return tm) \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term d fuel state tm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH: "\<forall>f'\<ge>fuel. interp_term d f' state tm = interp_term d fuel state tm"
      using "35.IH" by blast
    from IH f''_ge have "interp_term d f'' state tm = interp_term d fuel state tm"
      by metis
    with f'_eq show "interp_statement d f' state (CoreStmt_Return tm)
                       = interp_statement d (Suc fuel) state (CoreStmt_Return tm)"
      by simp
  qed
next
  (* While *)
  case (36 d fuel state whileGhost condTm invars decr bodyStmts)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_statement d (Suc fuel) state
                      (CoreStmt_While whileGhost condTm invars decr bodyStmts) \<noteq> Inl InsufficientFuel"
    hence "interp_term_list d fuel state invars \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence invs_eq: "interp_term_list d f'' state invars = interp_term_list d fuel state invars"
      using "36.IH"(1) f''_ge by blast
    show "interp_statement d f' state (CoreStmt_While whileGhost condTm invars decr bodyStmts) =
          interp_statement d (Suc fuel) state (CoreStmt_While whileGhost condTm invars decr bodyStmts)"
    proof (cases "interp_term_list d fuel state invars")
      case (Inl err)
      thus ?thesis using invs_eq f'_eq by simp
    next
      case Invs: (Inr invarVals)
      show ?thesis
      proof (cases "invariants_error invarVals")
        case (Some err)
        thus ?thesis using Invs invs_eq f'_eq by simp
      next
        case InvsOk: None
        \<comment> \<open>The invariants hold, at both fuels. From here on the loop runs as
            it would without them. \<close>
        have invs_f'': "interp_term_list d f'' state invars = Inr invarVals"
          using invs_eq Invs by simp
        note [simp] = Invs InvsOk invs_f''
        have cond_noFuel: "interp_term d fuel state condTm \<noteq> Inl InsufficientFuel"
          using noFuel by (auto split: sum.splits)
        hence IH_cond: "\<forall>f'\<ge>fuel. interp_term d f' state condTm = interp_term d fuel state condTm"
          using "36.IH"(2)[OF Invs InvsOk] by blast
        show ?thesis
        proof (cases "interp_term d fuel state condTm")
          case (Inl err)
          hence "interp_term d f'' state condTm = Inl err" using IH_cond f''_ge by metis
          thus ?thesis using Inl f'_eq by simp
        next
          case (Inr condVal)
          show ?thesis
          proof (cases condVal)
            case (CV_Bool b)
            show ?thesis
            proof (cases b)
              case True
              hence body_noFuel: "interp_statement_list d fuel state bodyStmts \<noteq> Inl InsufficientFuel"
                using noFuel Inr CV_Bool by (auto split: sum.splits ExecResult.splits)
              hence IH_body: "\<forall>f'\<ge>fuel. interp_statement_list d f' state bodyStmts
                                          = interp_statement_list d fuel state bodyStmts"
                using "36.IH"(3)[OF Invs InvsOk] Inr CV_Bool True by blast
              have cond_fuel: "interp_term d fuel state condTm = Inr (CV_Bool True)"
                using Inr CV_Bool True by simp
              have cond_f'': "interp_term d f'' state condTm = Inr (CV_Bool True)"
                using IH_cond cond_fuel f''_ge by simp
              show ?thesis
              proof (cases "interp_statement_list d fuel state bodyStmts")
                case (Inl err)
                hence "interp_statement_list d f'' state bodyStmts = Inl err" using IH_body f''_ge by metis
                thus ?thesis using Inl f'_eq cond_f'' cond_fuel by simp
              next
                case (Inr result)
                show ?thesis
                proof (cases result)
                  case (Continue state')
                  hence loop_noFuel: "interp_statement d fuel (restore_scope state state')
                                        (CoreStmt_While whileGhost condTm invars decr bodyStmts)
                                      \<noteq> Inl InsufficientFuel"
                    using noFuel cond_fuel \<open>interp_statement_list d fuel state bodyStmts = Inr result\<close>
                    by auto
                  hence IH_loop: "\<forall>f'\<ge>fuel. interp_statement d f' (restore_scope state state')
                                              (CoreStmt_While whileGhost condTm invars decr bodyStmts) =
                                            interp_statement d fuel (restore_scope state state')
                                              (CoreStmt_While whileGhost condTm invars decr bodyStmts)"
                    using "36.IH"(4)[OF Invs InvsOk] Inr CV_Bool True
                          \<open>interp_statement_list d fuel state bodyStmts = Inr result\<close> Continue
                    by (metis cond_fuel)
                  have body_fuel: "interp_statement_list d fuel state bodyStmts = Inr (Continue state')"
                    using \<open>interp_statement_list d fuel state bodyStmts = Inr result\<close> Continue by simp
                  have "interp_term d f'' state condTm = Inr (CV_Bool True)"
                    using cond_f'' by simp
                  moreover have "interp_statement_list d f'' state bodyStmts = Inr (Continue state')"
                    using IH_body body_fuel f''_ge by metis
                  moreover have "interp_statement d f'' (restore_scope state state')
                                  (CoreStmt_While whileGhost condTm invars decr bodyStmts) =
                                interp_statement d fuel (restore_scope state state')
                                  (CoreStmt_While whileGhost condTm invars decr bodyStmts)"
                    using IH_loop f''_ge by metis
                  ultimately show ?thesis using f'_eq cond_fuel body_fuel by simp
                next
                  case (Return state' retVal)
                  have body_fuel: "interp_statement_list d fuel state bodyStmts = Inr (Return state' retVal)"
                    using \<open>interp_statement_list d fuel state bodyStmts = Inr result\<close> Return by simp
                  have "interp_term d f'' state condTm = Inr (CV_Bool True)"
                    using cond_f'' by simp
                  moreover have "interp_statement_list d f'' state bodyStmts = Inr (Return state' retVal)"
                    using IH_body body_fuel f''_ge by metis
                  ultimately show ?thesis using f'_eq cond_fuel body_fuel by simp
                qed
              qed
            next
              case False
              have cond_fuel: "interp_term d fuel state condTm = Inr (CV_Bool False)"
                using Inr CV_Bool False by simp
              have "interp_term d f'' state condTm = Inr (CV_Bool False)"
                using IH_cond cond_fuel f''_ge by metis
              thus ?thesis using f'_eq cond_fuel by simp
            qed
          next
            case (CV_FiniteInt x21 x22 x23)
            have "interp_term d f'' state condTm = Inr condVal" using IH_cond Inr f''_ge by metis
            thus ?thesis using f'_eq CV_FiniteInt Inr by simp
          next
            case (CV_Record x4)
            have "interp_term d f'' state condTm = Inr condVal" using IH_cond Inr f''_ge by metis
            thus ?thesis using f'_eq CV_Record Inr by simp
          next
            case (CV_Variant x51 x52)
            have "interp_term d f'' state condTm = Inr condVal" using IH_cond Inr f''_ge by metis
            thus ?thesis using f'_eq CV_Variant Inr by simp
          next
            case (CV_Array x61 x62)
            have "interp_term d f'' state condTm = Inr condVal" using IH_cond Inr f''_ge by metis
            thus ?thesis using f'_eq CV_Array Inr by simp
          next
            case (CV_Int x7)
            have "interp_term d f'' state condTm = Inr condVal" using IH_cond Inr f''_ge by metis
            thus ?thesis using f'_eq CV_Int Inr by simp
          next
            case (CV_Real x8)
            have "interp_term d f'' state condTm = Inr condVal" using IH_cond Inr f''_ge by metis
            thus ?thesis using f'_eq CV_Real Inr by simp
          qed
        qed
      qed
    qed
  qed
next
  (* Match *)
  case (37 d fuel state matchGhost scrutTm arms)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_statement d (Suc fuel) state (CoreStmt_Match matchGhost scrutTm arms)
                      \<noteq> Inl InsufficientFuel"
    hence scrut_noFuel: "interp_term d fuel state scrutTm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH_scrut: "\<forall>f'\<ge>fuel. interp_term d f' state scrutTm = interp_term d fuel state scrutTm"
      using "37.IH"(1) by blast
    show "interp_statement d f' state (CoreStmt_Match matchGhost scrutTm arms) =
          interp_statement d (Suc fuel) state (CoreStmt_Match matchGhost scrutTm arms)"
    proof (cases "interp_term d fuel state scrutTm")
      case (Inl err)
      hence "interp_term d f'' state scrutTm = Inl err" using IH_scrut f''_ge by metis
      thus ?thesis using Inl f'_eq by simp
    next
      case (Inr scrutVal)
      show ?thesis
      proof (cases "find_matching_arm scrutVal arms")
        case (Inl err)
        have "interp_term d f'' state scrutTm = Inr scrutVal" using IH_scrut Inr f''_ge by metis
        thus ?thesis using f'_eq Inr Inl by simp
      next
        case (Inr armStmts)
        hence arm_noFuel: "interp_statement_list d fuel state armStmts \<noteq> Inl InsufficientFuel"
          using noFuel \<open>interp_term d fuel state scrutTm = Inr scrutVal\<close>
          by (auto split: sum.splits)
        hence IH_arm: "\<forall>f'\<ge>fuel. interp_statement_list d f' state armStmts
                                   = interp_statement_list d fuel state armStmts"
          using "37.IH"(2) \<open>interp_term d fuel state scrutTm = Inr scrutVal\<close> Inr by blast
        have "interp_term d f'' state scrutTm = Inr scrutVal"
          using IH_scrut \<open>interp_term d fuel state scrutTm = Inr scrutVal\<close> f''_ge by metis
        moreover have "interp_statement_list d f'' state armStmts
                         = interp_statement_list d fuel state armStmts"
          using IH_arm f''_ge by metis
        ultimately show ?thesis
          using f'_eq \<open>interp_term d fuel state scrutTm = Inr scrutVal\<close> Inr by simp
      qed
    qed
  qed
next
  (* Assert with a condition: evaluates the condition *)
  case (38 d fuel state condTm proofBody)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_statement d (Suc fuel) state (CoreStmt_Assert (Some condTm) proofBody)
                      \<noteq> Inl InsufficientFuel"
    hence sub_noFuel: "interp_term d fuel state condTm \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits)
    hence IH: "\<forall>f'\<ge>fuel. interp_term d f' state condTm = interp_term d fuel state condTm"
      using "38.IH" by blast
    from IH f''_ge have "interp_term d f'' state condTm = interp_term d fuel state condTm"
      by metis
    with f'_eq show "interp_statement d f' state (CoreStmt_Assert (Some condTm) proofBody)
                       = interp_statement d (Suc fuel) state (CoreStmt_Assert (Some condTm) proofBody)"
      by simp
  qed
next
  (* Assert without a condition: always TypeError *)
  case (39 d fuel state proofBody)
  show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where "f' = Suc f''" using Suc_le_D by auto
    thus "interp_statement d f' state (CoreStmt_Assert None proofBody)
            = interp_statement d (Suc fuel) state (CoreStmt_Assert None proofBody)"
      by simp
  qed
next
  (* Assume: a no-op *)
  case (40 d fuel state tm)
  show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where "f' = Suc f''" using Suc_le_D by auto
    thus "interp_statement d f' state (CoreStmt_Assume tm)
            = interp_statement d (Suc fuel) state (CoreStmt_Assume tm)"
      by simp
  qed
next
  (* ShowHide: a no-op *)
  case (41 d fuel state showOrHide name)
  show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where "f' = Suc f''" using Suc_le_D by auto
    thus "interp_statement d f' state (CoreStmt_ShowHide showOrHide name)
            = interp_statement d (Suc fuel) state (CoreStmt_ShowHide showOrHide name)"
      by simp
  qed
next
  (* Obtain, depth = 0: always InsufficientFuel *)
  case (42 fuel state varName varTy condTm)
  then show ?case by simp
next
  (* Obtain, depth > 0: the result does not mention the fuel *)
  case (43 d fuel state varName varTy condTm)
  show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where "f' = Suc f''" using Suc_le_D by auto
    thus "interp_statement (Suc d) f' state (CoreStmt_Obtain varName varTy condTm)
            = interp_statement (Suc d) (Suc fuel) state (CoreStmt_Obtain varName varTy condTm)"
      by simp
  qed
next
  (* Fix: always TypeError *)
  case (44 d fuel state varName varTy)
  show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where "f' = Suc f''" using Suc_le_D by auto
    thus "interp_statement d f' state (CoreStmt_Fix varName varTy)
            = interp_statement d (Suc fuel) state (CoreStmt_Fix varName varTy)"
      by simp
  qed
next
  (* Use: always TypeError *)
  case (45 d fuel state tm)
  show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where "f' = Suc f''" using Suc_le_D by auto
    thus "interp_statement d f' state (CoreStmt_Use tm)
            = interp_statement d (Suc fuel) state (CoreStmt_Use tm)"
      by simp
  qed
next
  (* Block - runs the body list in a fresh scope. *)
  case (46 d fuel state body)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_statement d (Suc fuel) state (CoreStmt_Block body) \<noteq> Inl InsufficientFuel"
    hence body_noFuel: "interp_statement_list d fuel state body \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits ExecResult.splits)
    hence IH_body: "\<forall>f'\<ge>fuel. interp_statement_list d f' state body
                                = interp_statement_list d fuel state body"
      using "46.IH" by blast
    have body_f'': "interp_statement_list d f'' state body = interp_statement_list d fuel state body"
      using IH_body f''_ge by metis
    show "interp_statement d f' state (CoreStmt_Block body) =
          interp_statement d (Suc fuel) state (CoreStmt_Block body)"
      using f'_eq body_f'' by simp
  qed
next
  (* interp_statement_list, fuel = 0 *)
  case (47 d state stmts)
  then show ?case by simp
next
  (* interp_statement_list, empty list *)
  case (48 d fuel state)
  show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where "f' = Suc f''" using Suc_le_D by auto
    thus "interp_statement_list d f' state [] = interp_statement_list d (Suc fuel) state []"
      by simp
  qed
next
  (* interp_statement_list, cons *)
  case (49 d fuel state stmt stmts)
  then show ?case
  proof (intro allI impI)
    fix f' assume "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_statement_list d (Suc fuel) state (stmt # stmts) \<noteq> Inl InsufficientFuel"
    hence stmt_noFuel: "interp_statement d fuel state stmt \<noteq> Inl InsufficientFuel"
      by (auto split: sum.splits ExecResult.splits)
    hence IH_stmt: "\<forall>f'\<ge>fuel. interp_statement d f' state stmt = interp_statement d fuel state stmt"
      using "49.IH"(1) by blast
    show "interp_statement_list d f' state (stmt # stmts) =
          interp_statement_list d (Suc fuel) state (stmt # stmts)"
    proof (cases "interp_statement d fuel state stmt")
      case (Inl err)
      have stmt_fuel: "interp_statement d fuel state stmt = Inl err" using Inl by simp
      have "interp_statement d f'' state stmt = Inl err" using IH_stmt stmt_fuel f''_ge by metis
      thus ?thesis using f'_eq stmt_fuel by simp
    next
      case (Inr result)
      show ?thesis
      proof (cases result)
        case (Continue state')
        have stmt_fuel: "interp_statement d fuel state stmt = Inr (Continue state')"
          using Inr Continue by simp
        hence stmts_noFuel: "interp_statement_list d fuel state' stmts \<noteq> Inl InsufficientFuel"
          using noFuel by (auto split: sum.splits)
        hence IH_stmts: "\<forall>f'\<ge>fuel. interp_statement_list d f' state' stmts
                                     = interp_statement_list d fuel state' stmts"
          using "49.IH"(2) Inr Continue by blast
        have "interp_statement d f'' state stmt = Inr (Continue state')"
          using IH_stmt stmt_fuel f''_ge by metis
        moreover have "interp_statement_list d f'' state' stmts = interp_statement_list d fuel state' stmts"
          using IH_stmts f''_ge by metis
        ultimately show ?thesis using f'_eq stmt_fuel by simp
      next
        case (Return state' retVal)
        have stmt_fuel: "interp_statement d fuel state stmt = Inr (Return state' retVal)"
          using Inr Return by simp
        have "interp_statement d f'' state stmt = Inr (Return state' retVal)"
          using IH_stmt stmt_fuel f''_ge by metis
        thus ?thesis using f'_eq stmt_fuel by simp
      qed
    qed
  qed
next
  (* interp_function_call, fuel = 0 *)
  case (50 d state fnName argTys argTms)
  then show ?case by simp
next
  (* interp_function_call, fuel > 0 *)
  case (51 d fuel state fnName argTys argTms)
  then show ?case
  proof (intro allI impI)
    fix f' assume f'_ge: "f' \<ge> Suc fuel"
    then obtain f'' where f'_eq: "f' = Suc f''" and f''_ge: "f'' \<ge> fuel"
      using Suc_le_D by auto
    assume noFuel: "interp_function_call d (Suc fuel) state fnName argTys argTms \<noteq> Inl InsufficientFuel"

    show "interp_function_call d f' state fnName argTys argTms =
          interp_function_call d (Suc fuel) state fnName argTys argTms"
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
        show ?thesis
        proof (cases "length argTys \<noteq> length (IF_TyArgs fn)")
          case True
          thus ?thesis using Some False f'_eq by simp
        next
          case tyLen: False
          (* Abbreviations for clarity *)
          let ?refResults = "map (interp_writable_lvalue d fuel state) argTms"
          let ?valResults = "map (interp_term d fuel state) argTms"
          let ?fnArgs = "IF_Args fn"
          let ?calleeTyArgs = "fmap_of_list (zip (IF_TyArgs fn) (map (apply_subst (IS_TyArgs state)) argTys))"
          let ?clearedState = "state \<lparr> IS_Locals := fmempty, IS_Refs := fmempty,
                                         IS_ConstLocals := {||},
                                         IS_TyArgs := ?calleeTyArgs \<rparr>"

          have len_eq: "length ?fnArgs = length argTms" using False by simp

          have fold_noFuel: "fold process_one_arg (zip ?fnArgs (zip (map (interp_writable_lvalue d fuel state) argTms)
                  (map (interp_term d fuel state) argTms))) (Inr ?clearedState)
                \<noteq> Inl InsufficientFuel"
            using noFuel Some False tyLen by (auto simp: Let_def split: sum.splits ExecResult.splits)

          have tm_IH: "\<forall>argTm \<in> set argTms.
                        interp_term d fuel state argTm \<noteq> Inl InsufficientFuel
                          \<longrightarrow> (\<forall>f' \<ge> fuel. interp_term d f' state argTm = interp_term d fuel state argTm)"
            using "51.IH"(2) False Some tyLen by blast
          have lv_IH: "\<forall>argTm \<in> set argTms.
                        interp_writable_lvalue d fuel state argTm \<noteq> Inl InsufficientFuel
                          \<longrightarrow> (\<forall>f' \<ge> fuel. interp_writable_lvalue d f' state argTm
                                               = interp_writable_lvalue d fuel state argTm)"
            using "51.IH"(1) False Some tyLen by blast
          have tm_agree: "\<forall>argTm \<in> set argTms.
                        interp_term d fuel state argTm \<noteq> Inl InsufficientFuel
                          \<longrightarrow> interp_term d f'' state argTm = interp_term d fuel state argTm"
            using tm_IH f''_ge by blast
          have lv_agree: "\<forall>argTm \<in> set argTms.
                        interp_writable_lvalue d fuel state argTm \<noteq> Inl InsufficientFuel
                          \<longrightarrow> interp_writable_lvalue d f'' state argTm
                                = interp_writable_lvalue d fuel state argTm"
            using lv_IH f''_ge by blast

          have fold_eq: "fold process_one_arg (zip ?fnArgs (zip (map (interp_writable_lvalue d f'' state) argTms)
                                                                (map (interp_term d f'' state) argTms))) (Inr ?clearedState) =
                         fold process_one_arg (zip ?fnArgs (zip ?refResults ?valResults)) (Inr ?clearedState)"
            by (rule fold_process_one_arg_agree[OF tm_agree lv_agree _ fold_noFuel]) (simp add: len_eq)

          show ?thesis
          proof (cases "fold process_one_arg (zip ?fnArgs (zip ?refResults ?valResults)) (Inr ?clearedState)")
            case (Inl err)
            thus ?thesis using Some False tyLen f'_eq fold_eq by (simp add: Let_def)
          next
            case PreCall: (Inr preCallState)
            (* Now case-analyze on whether the function is internal or external *)
            show ?thesis
            proof (cases "IF_Body fn")
              case (Inl bodyStmts)
              (* Internal function: execute body statements *)
              hence body_noFuel: "interp_statement_list d fuel preCallState bodyStmts \<noteq> Inl InsufficientFuel"
                using noFuel Some False tyLen PreCall by (auto split: sum.splits ExecResult.splits simp: Let_def)
              hence IH_body: "\<forall>f'\<ge>fuel. interp_statement_list d f' preCallState bodyStmts =
                                        interp_statement_list d fuel preCallState bodyStmts"
                using "51.IH"(3) Some False tyLen PreCall Inl by blast
              have "interp_statement_list d f'' preCallState bodyStmts =
                    interp_statement_list d fuel preCallState bodyStmts"
                using IH_body f''_ge by metis
              thus ?thesis using Some False tyLen PreCall f'_eq fold_eq Inl by (simp add: Let_def)
            next
              case (Inr externFun)
              (* External function: the result depends on valResults and refResults directly,
                 not on the fold result (preCallState). We need to show these maps are equal. *)
              let ?filter_refs = "\<lambda>refResults. map (\<lambda>((_, vr), refResult).
                                      if vr = Ref then refResult else Inl TypeError)
                                    (zip ?fnArgs refResults)"
              have valResults_eq: "map (interp_term d f'' state) argTms = ?valResults"
                by (rule fold_process_one_arg_ok_results_agree(1)[OF tm_agree lv_agree len_eq PreCall])
              have filtered_refs_eq: "?filter_refs (map (interp_writable_lvalue d f'' state) argTms) =
                                      ?filter_refs ?refResults"
                by (rule fold_process_one_arg_ok_results_agree(2)[OF tm_agree lv_agree len_eq PreCall])

              (* Now show the full expressions are equal *)
              have rights_vals_eq: "rights (map (interp_term d f'' state) argTms) = rights ?valResults"
                using valResults_eq by metis

              have rights_refs_eq: "rights (?filter_refs (map (interp_writable_lvalue d f'' state) argTms)) =
                                    rights (?filter_refs ?refResults)"
                using filtered_refs_eq by simp

              (* Rewrite fold_eq using valResults_eq to get the fold result in terms of f'' *)
              have fold_eq': "fold process_one_arg (zip ?fnArgs (zip (map (interp_writable_lvalue d f'' state) argTms)
                                                                (map (interp_term d f'' state) argTms))) (Inr ?clearedState) =
                             Inr preCallState"
                using fold_eq PreCall valResults_eq by argo

              (* Both LHS and RHS compute the same result for external functions *)
              show ?thesis using Some False tyLen Inr f'_eq fold_eq' PreCall
                                 rights_vals_eq rights_refs_eq filtered_refs_eq
                by (simp add: Let_def)
            qed
          qed
        qed
      qed
    qed
  qed
qed


(* ========================================================================== *)
(* Helper lemmas for depth monotonicity *)
(* ========================================================================== *)

(* converged g = converged f, if g agrees with f wherever f is not out of fuel,
   and g is fuel-monotone. (g may stop being out of fuel earlier than f does, so
   the two least fuels can differ; monotonicity of g bridges the gap.) *)
lemma converged_agree:
  assumes agree: "\<And>m. f m \<noteq> Inl InsufficientFuel \<Longrightarrow> g m = f m"
    and g_mono: "\<And>m m'. g m \<noteq> Inl InsufficientFuel \<Longrightarrow> m \<le> m' \<Longrightarrow> g m' = g m"
    and conv: "converged f \<noteq> Inl InsufficientFuel"
  shows "converged g = converged f"
proof -
  have ex_f: "\<exists>m. f m \<noteq> Inl InsufficientFuel"
  proof (rule ccontr)
    assume "\<not> (\<exists>m. f m \<noteq> Inl InsufficientFuel)"
    hence "converged f = Inl InsufficientFuel" by (simp add: converged_def)
    thus False using conv by simp
  qed
  define mf where "mf = (LEAST m. f m \<noteq> Inl InsufficientFuel)"
  have f_mf: "f mf \<noteq> Inl InsufficientFuel"
    unfolding mf_def using ex_f by (rule LeastI_ex)
  have conv_f: "converged f = f mf"
    using ex_f by (simp add: converged_def mf_def)
  have g_mf: "g mf = f mf" using agree f_mf by simp
  hence g_mf_ne: "g mf \<noteq> Inl InsufficientFuel" using f_mf by simp
  hence ex_g: "\<exists>m. g m \<noteq> Inl InsufficientFuel" by blast
  define mg where "mg = (LEAST m. g m \<noteq> Inl InsufficientFuel)"
  have g_mg: "g mg \<noteq> Inl InsufficientFuel"
    unfolding mg_def using ex_g by (rule LeastI_ex)
  have mg_le: "mg \<le> mf"
    unfolding mg_def using g_mf_ne by (rule Least_le)
  have conv_g: "converged g = g mg"
    using ex_g by (simp add: converged_def mg_def)
  have "g mf = g mg" using g_mono[OF g_mg mg_le] .
  thus ?thesis using conv_f conv_g g_mf by simp
qed

(* If instances_error does not report InsufficientFuel, no instance is out of fuel. *)
lemma instances_error_no_fuel:
  assumes "instances_error vals r \<noteq> Some InsufficientFuel"
    and "v \<in> vals"
  shows "r v \<noteq> Inl InsufficientFuel"
  using assms by (auto simp: instances_error_def split: if_splits)

lemma eval_quantifier_agree:
  assumes agree: "\<And>v. r v \<noteq> Inl InsufficientFuel \<Longrightarrow> r' v = r v"
    and ne: "eval_quantifier quant vals r \<noteq> Inl InsufficientFuel"
  shows "eval_quantifier quant vals r' = eval_quantifier quant vals r"
proof -
  have ie_ne: "instances_error vals r \<noteq> Some InsufficientFuel"
    using ne by (auto simp: eval_quantifier_def)
  have eq: "r' v = r v" if "v \<in> vals" for v
    using agree instances_error_no_fuel[OF ie_ne that] by blast
  have ie: "instances_error vals r' = instances_error vals r"
    by (simp add: instances_error_def eq cong: if_cong)
  have all: "(\<forall>v \<in> vals. r' v = Inr (CV_Bool True)) = (\<forall>v \<in> vals. r v = Inr (CV_Bool True))"
    by (simp add: eq)
  have ex: "(\<exists>v \<in> vals. r' v = Inr (CV_Bool True)) = (\<exists>v \<in> vals. r v = Inr (CV_Bool True))"
    by (simp add: eq)
  show ?thesis
    unfolding eval_quantifier_def ie all ex by (rule refl)
qed

lemma choose_witness_agree:
  assumes agree: "\<And>v. r v \<noteq> Inl InsufficientFuel \<Longrightarrow> r' v = r v"
    and ne: "choose_witness vals r \<noteq> Inl InsufficientFuel"
  shows "choose_witness vals r' = choose_witness vals r"
proof -
  have ie_ne: "instances_error vals r \<noteq> Some InsufficientFuel"
    using ne by (auto simp: choose_witness_def)
  have eq: "r' v = r v" if "v \<in> vals" for v
    using agree instances_error_no_fuel[OF ie_ne that] by blast
  have ie: "instances_error vals r' = instances_error vals r"
    by (simp add: instances_error_def eq cong: if_cong)
  have ex: "(\<exists>v \<in> vals. r' v = Inr (CV_Bool True)) = (\<exists>v \<in> vals. r v = Inr (CV_Bool True))"
    by (simp add: eq)
  have some: "(SOME v. v \<in> vals \<and> r' v = Inr (CV_Bool True))
                = (SOME v. v \<in> vals \<and> r v = Inr (CV_Bool True))"
    by (simp add: eq cong: conj_cong)
  show ?thesis
    unfolding choose_witness_def ie ex some by (rule refl)
qed


(* ========================================================================== *)
(* Depth monotonicity *)
(* ========================================================================== *)

(* At a fixed fuel, if an interpreter function returns a non-InsufficientFuel
   result at some depth d, then it returns the same result at any greater depth. *)

lemma interp_depth_mono:
  shows interp_term_depth_mono:
            "interp_term d f (state :: 'w InterpState) tm \<noteq> Inl InsufficientFuel
               \<Longrightarrow> \<forall>d'\<ge>d. interp_term d' f state tm = interp_term d f state tm"
    and interp_term_list_depth_mono:
            "interp_term_list d f (state :: 'w InterpState) tms \<noteq> Inl InsufficientFuel
               \<Longrightarrow> \<forall>d'\<ge>d. interp_term_list d' f state tms = interp_term_list d f state tms"
    and interp_writable_lvalue_depth_mono:
            "interp_writable_lvalue d f (state :: 'w InterpState) tm \<noteq> Inl InsufficientFuel
               \<Longrightarrow> \<forall>d'\<ge>d. interp_writable_lvalue d' f state tm = interp_writable_lvalue d f state tm"
    and interp_statement_depth_mono:
            "interp_statement d f (state :: 'w InterpState) stmt \<noteq> Inl InsufficientFuel
               \<Longrightarrow> \<forall>d'\<ge>d. interp_statement d' f state stmt = interp_statement d f state stmt"
    and interp_statement_list_depth_mono:
            "interp_statement_list d f (state :: 'w InterpState) stmts \<noteq> Inl InsufficientFuel
               \<Longrightarrow> \<forall>d'\<ge>d. interp_statement_list d' f state stmts = interp_statement_list d f state stmts"
    and interp_function_call_depth_mono:
            "interp_function_call d f (state :: 'w InterpState) fnName argTys argTms \<noteq> Inl InsufficientFuel
               \<Longrightarrow> \<forall>d'\<ge>d. interp_function_call d' f state fnName argTys argTms
                    = interp_function_call d f state fnName argTys argTms"
proof (induction rule: interp_term_interp_term_list_interp_writable_lvalue_interp_statement_interp_statement_list_interp_function_call.induct)
  (* interp_term, fuel = 0 *)
  case 1 then show ?case by simp
next
  (* LitBool *)
  case 2 then show ?case by simp
next
  (* LitInt *)
  case 3 then show ?case by simp
next
  (* LitArray *)
  case (4 d fuel state elemTy tms)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_term_list d fuel state tms \<noteq> Inl InsufficientFuel"
      using "4.prems" by (auto split: sum.splits)
    hence "interp_term_list d' fuel state tms = interp_term_list d fuel state tms"
      using "4.IH" d'_ge by blast
    thus "interp_term d' (Suc fuel) state (CoreTm_LitArray elemTy tms)
            = interp_term d (Suc fuel) state (CoreTm_LitArray elemTy tms)"
      by simp
  qed
next
  (* Var *)
  case 5 then show ?case by simp
next
  (* Cast *)
  case (6 d fuel state targetTy tm)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_term d fuel state tm \<noteq> Inl InsufficientFuel"
      using "6.prems" by (auto split: sum.splits)
    hence "interp_term d' fuel state tm = interp_term d fuel state tm"
      using "6.IH" d'_ge by blast
    thus "interp_term d' (Suc fuel) state (CoreTm_Cast targetTy tm)
            = interp_term d (Suc fuel) state (CoreTm_Cast targetTy tm)"
      by simp
  qed
next
  (* Unop *)
  case (7 d fuel state op tm)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_term d fuel state tm \<noteq> Inl InsufficientFuel"
      using "7.prems" by (auto split: sum.splits)
    hence "interp_term d' fuel state tm = interp_term d fuel state tm"
      using "7.IH" d'_ge by blast
    thus "interp_term d' (Suc fuel) state (CoreTm_Unop op tm)
            = interp_term d (Suc fuel) state (CoreTm_Unop op tm)"
      by simp
  qed
next
  (* Binop *)
  case (8 d fuel state op lhsTm rhsTm)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_term d fuel state lhsTm \<noteq> Inl InsufficientFuel"
      using "8.prems" by (auto split: sum.splits)
    hence lhs_eq: "interp_term d' fuel state lhsTm = interp_term d fuel state lhsTm"
      using "8.IH"(1) d'_ge by blast
    show "interp_term d' (Suc fuel) state (CoreTm_Binop op lhsTm rhsTm)
            = interp_term d (Suc fuel) state (CoreTm_Binop op lhsTm rhsTm)"
    proof (cases "interp_term d fuel state lhsTm")
      case (Inl err)
      thus ?thesis using lhs_eq by simp
    next
      case (Inr lhsVal)
      show ?thesis
      proof (cases "short_circuit op lhsVal")
        case (Some result)
        (* Short-circuit: the rhs is not evaluated *)
        thus ?thesis using Inr lhs_eq by simp
      next
        case None
        hence "interp_term d fuel state rhsTm \<noteq> Inl InsufficientFuel"
          using "8.prems" Inr by (auto split: sum.splits)
        hence "interp_term d' fuel state rhsTm = interp_term d fuel state rhsTm"
          using "8.IH"(2) Inr None d'_ge by blast
        thus ?thesis using Inr None lhs_eq by simp
      qed
    qed
  qed
next
  (* Let *)
  case (9 d fuel state varName rhsTm bodyTm)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_term d fuel state rhsTm \<noteq> Inl InsufficientFuel"
      using "9.prems" by (auto split: sum.splits prod.splits)
    hence rhs_eq: "interp_term d' fuel state rhsTm = interp_term d fuel state rhsTm"
      using "9.IH"(1) d'_ge by blast
    show "interp_term d' (Suc fuel) state (CoreTm_Let varName rhsTm bodyTm)
            = interp_term d (Suc fuel) state (CoreTm_Let varName rhsTm bodyTm)"
    proof (cases "interp_term d fuel state rhsTm")
      case (Inl err)
      thus ?thesis using rhs_eq by simp
    next
      case (Inr rhsVal)
      let ?state'' = "bind_const_local varName rhsVal state"
      have body_noFuel: "interp_term d fuel ?state'' bodyTm \<noteq> Inl InsufficientFuel"
        using "9.prems" Inr by (simp del: bind_const_local.simps)
      have IH_body: "\<forall>d'\<ge>d. interp_term d' fuel ?state'' bodyTm = interp_term d fuel ?state'' bodyTm"
        using "9.IH"(2)[OF Inr] body_noFuel by blast
      have "interp_term d' fuel state rhsTm = Inr rhsVal" using rhs_eq Inr by simp
      moreover have "interp_term d' fuel ?state'' bodyTm = interp_term d fuel ?state'' bodyTm"
        using IH_body d'_ge by metis
      ultimately show ?thesis using Inr
        by (simp del: bind_const_local.simps)
    qed
  qed
next
  (* FunctionCall *)
  case (10 d fuel state fnName argTypes argTms)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    show "interp_term d' (Suc fuel) state (CoreTm_FunctionCall fnName argTypes argTms) =
          interp_term d (Suc fuel) state (CoreTm_FunctionCall fnName argTypes argTms)"
    proof (cases "is_pure_fun state fnName")
      case False
      thus ?thesis by simp
    next
      case True
      hence "interp_function_call d fuel state fnName argTypes argTms \<noteq> Inl InsufficientFuel"
        using "10.prems" by (auto split: sum.splits)
      hence "interp_function_call d' fuel state fnName argTypes argTms
               = interp_function_call d fuel state fnName argTypes argTms"
        using "10.IH" True d'_ge by blast
      thus ?thesis using True by simp
    qed
  qed
next
  (* VariantCtor *)
  case (11 d fuel state ctorName tyArgs payloadTm)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_term d fuel state payloadTm \<noteq> Inl InsufficientFuel"
      using "11.prems" by (auto split: sum.splits)
    hence "interp_term d' fuel state payloadTm = interp_term d fuel state payloadTm"
      using "11.IH" d'_ge by blast
    thus "interp_term d' (Suc fuel) state (CoreTm_VariantCtor ctorName tyArgs payloadTm) =
          interp_term d (Suc fuel) state (CoreTm_VariantCtor ctorName tyArgs payloadTm)"
      by simp
  qed
next
  (* Record *)
  case (12 d fuel state nameTermPairs)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_term_list d fuel state (map snd nameTermPairs) \<noteq> Inl InsufficientFuel"
      using "12.prems" by (auto split: sum.splits)
    hence "interp_term_list d' fuel state (map snd nameTermPairs)
             = interp_term_list d fuel state (map snd nameTermPairs)"
      using "12.IH" d'_ge by blast
    thus "interp_term d' (Suc fuel) state (CoreTm_Record nameTermPairs)
            = interp_term d (Suc fuel) state (CoreTm_Record nameTermPairs)"
      by simp
  qed
next
  (* RecordProj *)
  case (13 d fuel state tm fldName)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_term d fuel state tm \<noteq> Inl InsufficientFuel"
      using "13.prems" by (auto split: sum.splits)
    hence "interp_term d' fuel state tm = interp_term d fuel state tm"
      using "13.IH" d'_ge by blast
    thus "interp_term d' (Suc fuel) state (CoreTm_RecordProj tm fldName)
            = interp_term d (Suc fuel) state (CoreTm_RecordProj tm fldName)"
      by simp
  qed
next
  (* VariantProj *)
  case (14 d fuel state tm expectedCtorName)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_term d fuel state tm \<noteq> Inl InsufficientFuel"
      using "14.prems" by (auto split: sum.splits)
    hence "interp_term d' fuel state tm = interp_term d fuel state tm"
      using "14.IH" d'_ge by blast
    thus "interp_term d' (Suc fuel) state (CoreTm_VariantProj tm expectedCtorName)
            = interp_term d (Suc fuel) state (CoreTm_VariantProj tm expectedCtorName)"
      by simp
  qed
next
  (* ArrayProj *)
  case (15 d fuel state arrayTm idxTms)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_term d fuel state arrayTm \<noteq> Inl InsufficientFuel"
      using "15.prems" by (auto split: sum.splits)
    hence arr_eq: "interp_term d' fuel state arrayTm = interp_term d fuel state arrayTm"
      using "15.IH"(1) d'_ge by blast
    show "interp_term d' (Suc fuel) state (CoreTm_ArrayProj arrayTm idxTms)
            = interp_term d (Suc fuel) state (CoreTm_ArrayProj arrayTm idxTms)"
    proof (cases "interp_term d fuel state arrayTm")
      case (Inl err)
      thus ?thesis using arr_eq by simp
    next
      case (Inr arrVal)
      show ?thesis
      proof (cases arrVal)
        case (CV_Array sizes elemMap)
        hence "interp_term_list d fuel state idxTms \<noteq> Inl InsufficientFuel"
          using "15.prems" Inr by (auto split: sum.splits)
        hence "interp_term_list d' fuel state idxTms = interp_term_list d fuel state idxTms"
          using "15.IH"(2) Inr CV_Array d'_ge by blast
        thus ?thesis using arr_eq Inr CV_Array by simp
      qed (use arr_eq Inr in simp_all)
    qed
  qed
next
  (* Match *)
  case (16 d fuel state scrutTm arms)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_term d fuel state scrutTm \<noteq> Inl InsufficientFuel"
      using "16.prems" by (auto split: sum.splits)
    hence scrut_eq: "interp_term d' fuel state scrutTm = interp_term d fuel state scrutTm"
      using "16.IH"(1) d'_ge by blast
    show "interp_term d' (Suc fuel) state (CoreTm_Match scrutTm arms)
            = interp_term d (Suc fuel) state (CoreTm_Match scrutTm arms)"
    proof (cases "interp_term d fuel state scrutTm")
      case (Inl err)
      thus ?thesis using scrut_eq by simp
    next
      case Scrut: (Inr scrutVal)
      show ?thesis
      proof (cases "find_matching_arm scrutVal arms")
        case (Inl err)
        thus ?thesis using Scrut scrut_eq by simp
      next
        case (Inr armTm)
        hence "interp_term d fuel state armTm \<noteq> Inl InsufficientFuel"
          using "16.prems" Scrut by (auto split: sum.splits)
        hence "interp_term d' fuel state armTm = interp_term d fuel state armTm"
          using "16.IH"(2) Scrut Inr d'_ge by blast
        thus ?thesis using Scrut Inr scrut_eq by simp
      qed
    qed
  qed
next
  (* Sizeof *)
  case (17 d fuel state tm)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_term d fuel state tm \<noteq> Inl InsufficientFuel"
      using "17.prems" by (auto split: sum.splits)
    hence "interp_term d' fuel state tm = interp_term d fuel state tm"
      using "17.IH" d'_ge by blast
    thus "interp_term d' (Suc fuel) state (CoreTm_Sizeof tm)
            = interp_term d (Suc fuel) state (CoreTm_Sizeof tm)"
      by simp
  qed
next
  (* Quantifier, depth = 0: always InsufficientFuel *)
  case 18 then show ?case by simp
next
  (* Quantifier, depth > 0. No instance of the body is out of fuel, so each
     instance has the same converged result at the greater depth. *)
  case (19 d fuel state quant varName varTy bodyTm)
  show ?case
  proof (intro allI impI)
    fix d' assume "d' \<ge> Suc d"
    then obtain d'' where d'_eq: "d' = Suc d''" and d''_ge: "d'' \<ge> d"
      using Suc_le_D by auto
    let ?vals = "values_of_type state (apply_subst (IS_TyArgs state) varTy)"
    let ?r = "\<lambda>dd v. converged (\<lambda>m. interp_term dd m (bind_const_local varName v state) bodyTm)"
    have ne: "eval_quantifier quant ?vals (?r d) \<noteq> Inl InsufficientFuel"
      using "19.prems" by simp
    have agree: "?r d'' v = ?r d v" if "?r d v \<noteq> Inl InsufficientFuel" for v
    proof (rule converged_agree[OF _ _ that])
      fix m
      assume "interp_term d m (bind_const_local varName v state) bodyTm \<noteq> Inl InsufficientFuel"
      thus "interp_term d'' m (bind_const_local varName v state) bodyTm
              = interp_term d m (bind_const_local varName v state) bodyTm"
        using "19.IH" d''_ge by blast
    next
      fix m m'
      assume "interp_term d'' m (bind_const_local varName v state) bodyTm \<noteq> Inl InsufficientFuel"
        and "m \<le> m'"
      thus "interp_term d'' m' (bind_const_local varName v state) bodyTm
              = interp_term d'' m (bind_const_local varName v state) bodyTm"
        using interp_term_fuel_mono by blast
    qed
    have eq: "eval_quantifier quant ?vals (?r d'') = eval_quantifier quant ?vals (?r d)"
    proof (rule eval_quantifier_agree[OF _ ne])
      fix v assume "?r d v \<noteq> Inl InsufficientFuel"
      thus "?r d'' v = ?r d v" by (rule agree)
    qed
    show "interp_term d' (Suc fuel) state (CoreTm_Quantifier quant varName varTy bodyTm)
            = interp_term (Suc d) (Suc fuel) state (CoreTm_Quantifier quant varName varTy bodyTm)"
      using d'_eq eq by simp
  qed
next
  (* Allocated: always false *)
  case 20 then show ?case by simp
next
  (* Old *)
  case (21 d fuel state tm)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_term d fuel state tm \<noteq> Inl InsufficientFuel"
      using "21.prems" by simp
    hence "interp_term d' fuel state tm = interp_term d fuel state tm"
      using "21.IH" d'_ge by blast
    thus "interp_term d' (Suc fuel) state (CoreTm_Old tm)
            = interp_term d (Suc fuel) state (CoreTm_Old tm)"
      by simp
  qed
next
  (* Default: default_value does not take a depth *)
  case 22 then show ?case by simp
next
  (* interp_writable_lvalue, fuel = 0 *)
  case 23 then show ?case by simp
next
  (* interp_writable_lvalue, fuel > 0 *)
  case (24 d fuel state tm)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    show "interp_writable_lvalue d' (Suc fuel) state tm = interp_writable_lvalue d (Suc fuel) state tm"
    proof (cases tm)
      case (CoreTm_RecordProj tm' fldName)
      hence "interp_writable_lvalue d fuel state tm' \<noteq> Inl InsufficientFuel"
        using "24.prems" by (auto split: sum.splits)
      hence "interp_writable_lvalue d' fuel state tm' = interp_writable_lvalue d fuel state tm'"
        using "24.IH"(2) CoreTm_RecordProj d'_ge by blast
      thus ?thesis using CoreTm_RecordProj by simp
    next
      case (CoreTm_VariantProj tm' ctorName)
      hence "interp_writable_lvalue d fuel state tm' \<noteq> Inl InsufficientFuel"
        using "24.prems" by (auto split: sum.splits)
      hence "interp_writable_lvalue d' fuel state tm' = interp_writable_lvalue d fuel state tm'"
        using "24.IH"(3) CoreTm_VariantProj d'_ge by blast
      thus ?thesis using CoreTm_VariantProj by simp
    next
      case (CoreTm_ArrayProj tm' indexTms)
      hence "interp_writable_lvalue d fuel state tm' \<noteq> Inl InsufficientFuel"
        using "24.prems" by (auto split: sum.splits)
      hence lv_eq: "interp_writable_lvalue d' fuel state tm' = interp_writable_lvalue d fuel state tm'"
        using "24.IH"(4) CoreTm_ArrayProj d'_ge by blast
      show ?thesis
      proof (cases "interp_writable_lvalue d fuel state tm'")
        case (Inl err)
        thus ?thesis using CoreTm_ArrayProj lv_eq by simp
      next
        case (Inr addrPath)
        hence "interp_term_list d fuel state indexTms \<noteq> Inl InsufficientFuel"
          using "24.prems" CoreTm_ArrayProj by (auto split: sum.splits)
        hence IH_idx: "\<forall>d'\<ge>d. interp_term_list d' fuel state indexTms = interp_term_list d fuel state indexTms"
          using "24.IH"(5) CoreTm_ArrayProj Inr
          by (metis prod.exhaust)
        hence "interp_term_list d' fuel state indexTms = interp_term_list d fuel state indexTms"
          using d'_ge by blast
        thus ?thesis using CoreTm_ArrayProj Inr lv_eq by simp
      qed
    next
      case (CoreTm_Cast targetTy tm')
      show ?thesis
      proof (cases targetTy)
        case (CoreTy_Array elemTy dims)
        hence "interp_writable_lvalue d fuel state tm' \<noteq> Inl InsufficientFuel"
          using "24.prems" CoreTm_Cast by (auto split: sum.splits)
        hence "interp_writable_lvalue d' fuel state tm' = interp_writable_lvalue d fuel state tm'"
          using "24.IH"(1) CoreTm_Cast CoreTy_Array d'_ge by blast
        thus ?thesis using CoreTm_Cast CoreTy_Array by simp
      qed (simp_all add: CoreTm_Cast)
    qed simp_all
  qed
next
  (* interp_term_list, fuel = 0 *)
  case 25 then show ?case by simp
next
  (* interp_term_list, empty list *)
  case 26 then show ?case by simp
next
  (* interp_term_list, cons *)
  case (27 d fuel state tm tms)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_term d fuel state tm \<noteq> Inl InsufficientFuel"
      using "27.prems" by (auto split: sum.splits)
    hence tm_eq: "interp_term d' fuel state tm = interp_term d fuel state tm"
      using "27.IH"(1) d'_ge by blast
    show "interp_term_list d' (Suc fuel) state (tm # tms) = interp_term_list d (Suc fuel) state (tm # tms)"
    proof (cases "interp_term d fuel state tm")
      case (Inl err)
      thus ?thesis using tm_eq by simp
    next
      case (Inr val)
      hence "interp_term_list d fuel state tms \<noteq> Inl InsufficientFuel"
        using "27.prems" by (auto split: sum.splits)
      hence "interp_term_list d' fuel state tms = interp_term_list d fuel state tms"
        using "27.IH"(2) Inr d'_ge by blast
      thus ?thesis using Inr tm_eq by simp
    qed
  qed
next
  (* interp_statement, fuel = 0 *)
  case 28 then show ?case by simp
next
  (* VarDecl Var *)
  case (29 d fuel state declGhost varName varTy initialTm)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_term d fuel state initialTm \<noteq> Inl InsufficientFuel"
      using "29.prems" by (auto split: sum.splits prod.splits)
    hence "interp_term d' fuel state initialTm = interp_term d fuel state initialTm"
      using "29.IH"(1) d'_ge by blast
    thus "interp_statement d' (Suc fuel) state (CoreStmt_VarDecl declGhost varName Var varTy initialTm) =
          interp_statement d (Suc fuel) state (CoreStmt_VarDecl declGhost varName Var varTy initialTm)"
      by simp
  qed
next
  (* VarDeclCall *)
  case (30 d fuel state declGhost varName varTy castOpt fnName argTys argTms)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_function_call d fuel state fnName argTys argTms \<noteq> Inl InsufficientFuel"
      using "30.prems" by (auto split: sum.splits prod.splits)
    hence "interp_function_call d' fuel state fnName argTys argTms
             = interp_function_call d fuel state fnName argTys argTms"
      using "30.IH" d'_ge by blast
    thus "interp_statement d' (Suc fuel) state
            (CoreStmt_VarDeclCall declGhost varName varTy castOpt fnName argTys argTms) =
          interp_statement d (Suc fuel) state
            (CoreStmt_VarDeclCall declGhost varName varTy castOpt fnName argTys argTms)"
      by (simp split: sum.splits prod.splits)
  qed
next
  (* VarDecl Ref *)
  case (31 d fuel state declGhost varName varTy lvalueTm)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    show "interp_statement d' (Suc fuel) state (CoreStmt_VarDecl declGhost varName Ref varTy lvalueTm) =
          interp_statement d (Suc fuel) state (CoreStmt_VarDecl declGhost varName Ref varTy lvalueTm)"
    proof (cases "lvalue_base_name lvalueTm")
      case None
      then show ?thesis by simp
    next
      case (Some baseName)
      show ?thesis
      proof (cases "baseName |\<in>| IS_ConstLocals state
                    \<or> (fmlookup (IS_Locals state) baseName = None
                       \<and> fmlookup (IS_Refs state) baseName = None)")
        case True
        (* Const or global: both sides use interp_term *)
        have tm_noFuel: "interp_term d fuel state lvalueTm \<noteq> Inl InsufficientFuel"
          using "31.prems" Some True by (auto split: sum.splits prod.splits)
        have IH_tm: "\<forall>d'\<ge>d. interp_term d' fuel state lvalueTm = interp_term d fuel state lvalueTm"
          using "31.IH" Some True tm_noFuel by blast
        from IH_tm d'_ge
        have "interp_term d' fuel state lvalueTm = interp_term d fuel state lvalueTm" by metis
        then show ?thesis using Some True by simp
      next
        case False
        (* Not const: both sides use interp_writable_lvalue *)
        have lv_noFuel: "interp_writable_lvalue d fuel state lvalueTm \<noteq> Inl InsufficientFuel"
          using "31.prems" Some False by (auto split: sum.splits)
        have IH_lv: "\<forall>d'\<ge>d. interp_writable_lvalue d' fuel state lvalueTm
                                = interp_writable_lvalue d fuel state lvalueTm"
          using "31.IH" Some False lv_noFuel by blast
        from IH_lv d'_ge
        have "interp_writable_lvalue d' fuel state lvalueTm = interp_writable_lvalue d fuel state lvalueTm"
          by metis
        then show ?thesis using Some False by (auto split: sum.splits)
      qed
    qed
  qed
next
  (* Assign *)
  case (32 d fuel state assignGhost lhsLvalue rhsTm)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_writable_lvalue d fuel state lhsLvalue \<noteq> Inl InsufficientFuel"
      using "32.prems" by (auto split: sum.splits)
    hence lhs_eq: "interp_writable_lvalue d' fuel state lhsLvalue
                     = interp_writable_lvalue d fuel state lhsLvalue"
      using "32.IH"(1) d'_ge by blast
    show "interp_statement d' (Suc fuel) state (CoreStmt_Assign assignGhost lhsLvalue rhsTm) =
          interp_statement d (Suc fuel) state (CoreStmt_Assign assignGhost lhsLvalue rhsTm)"
    proof (cases "interp_writable_lvalue d fuel state lhsLvalue")
      case (Inl err)
      thus ?thesis using lhs_eq by simp
    next
      case (Inr addrPath)
      obtain addr path where addrPath_eq: "addrPath = (addr, path)" by (cases addrPath)
      hence "interp_term d fuel state rhsTm \<noteq> Inl InsufficientFuel"
        using "32.prems" Inr by (auto split: sum.splits)
      hence "interp_term d' fuel state rhsTm = interp_term d fuel state rhsTm"
        using "32.IH"(2) Inr addrPath_eq d'_ge by blast
      thus ?thesis using Inr addrPath_eq lhs_eq by simp
    qed
  qed
next
  (* AssignCall *)
  case (33 d fuel state assignGhost lhsLvalue castOpt fnName argTys argTms)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_writable_lvalue d fuel state lhsLvalue \<noteq> Inl InsufficientFuel"
      using "33.prems" by (auto split: sum.splits)
    hence lhs_eq: "interp_writable_lvalue d' fuel state lhsLvalue
                     = interp_writable_lvalue d fuel state lhsLvalue"
      using "33.IH"(1) d'_ge by blast
    show "interp_statement d' (Suc fuel) state
            (CoreStmt_AssignCall assignGhost lhsLvalue castOpt fnName argTys argTms) =
          interp_statement d (Suc fuel) state
            (CoreStmt_AssignCall assignGhost lhsLvalue castOpt fnName argTys argTms)"
    proof (cases "interp_writable_lvalue d fuel state lhsLvalue")
      case (Inl err)
      thus ?thesis using lhs_eq by simp
    next
      case (Inr addrPath)
      obtain addr path where addrPath_eq: "addrPath = (addr, path)" by (cases addrPath)
      hence "interp_function_call d fuel state fnName argTys argTms \<noteq> Inl InsufficientFuel"
        using "33.prems" Inr by (auto split: sum.splits prod.splits)
      hence "interp_function_call d' fuel state fnName argTys argTms
               = interp_function_call d fuel state fnName argTys argTms"
        using "33.IH"(2) addrPath_eq Inr d'_ge by blast
      thus ?thesis using Inr addrPath_eq lhs_eq by (simp split: sum.splits prod.splits)
    qed
  qed
next
  (* Swap *)
  case (34 d fuel state swapGhost lhsTm rhsTm)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_writable_lvalue d fuel state lhsTm \<noteq> Inl InsufficientFuel"
      using "34.prems" by (auto split: sum.splits)
    hence lhs_eq: "interp_writable_lvalue d' fuel state lhsTm
                     = interp_writable_lvalue d fuel state lhsTm"
      using "34.IH"(1) d'_ge by blast
    show "interp_statement d' (Suc fuel) state (CoreStmt_Swap swapGhost lhsTm rhsTm) =
          interp_statement d (Suc fuel) state (CoreStmt_Swap swapGhost lhsTm rhsTm)"
    proof (cases "interp_writable_lvalue d fuel state lhsTm")
      case (Inl err)
      thus ?thesis using lhs_eq by simp
    next
      case (Inr lhsLvalue)
      hence "interp_writable_lvalue d fuel state rhsTm \<noteq> Inl InsufficientFuel"
        using "34.prems" by (auto split: sum.splits)
      hence "interp_writable_lvalue d' fuel state rhsTm = interp_writable_lvalue d fuel state rhsTm"
        using "34.IH"(2) Inr d'_ge by blast
      thus ?thesis using Inr lhs_eq by simp
    qed
  qed
next
  (* Return *)
  case (35 d fuel state tm)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_term d fuel state tm \<noteq> Inl InsufficientFuel"
      using "35.prems" by (auto split: sum.splits)
    hence "interp_term d' fuel state tm = interp_term d fuel state tm"
      using "35.IH" d'_ge by blast
    thus "interp_statement d' (Suc fuel) state (CoreStmt_Return tm)
            = interp_statement d (Suc fuel) state (CoreStmt_Return tm)"
      by simp
  qed
next
  (* While *)
  case (36 d fuel state whileGhost condTm invars decr bodyStmts)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_term_list d fuel state invars \<noteq> Inl InsufficientFuel"
      using "36.prems" by (auto split: sum.splits)
    hence invs_eq: "interp_term_list d' fuel state invars = interp_term_list d fuel state invars"
      using "36.IH"(1) d'_ge by blast
    show "interp_statement d' (Suc fuel) state (CoreStmt_While whileGhost condTm invars decr bodyStmts) =
          interp_statement d (Suc fuel) state (CoreStmt_While whileGhost condTm invars decr bodyStmts)"
    proof (cases "interp_term_list d fuel state invars")
      case (Inl err)
      thus ?thesis using invs_eq by simp
    next
      case Invs: (Inr invarVals)
      show ?thesis
      proof (cases "invariants_error invarVals")
        case (Some err)
        thus ?thesis using Invs invs_eq by simp
      next
        case InvsOk: None
        \<comment> \<open>The invariants hold, at both depths. From here on the loop runs as
            it would without them. \<close>
        have invs_d': "interp_term_list d' fuel state invars = Inr invarVals"
          using invs_eq Invs by simp
        note [simp] = Invs InvsOk invs_d'
        have "interp_term d fuel state condTm \<noteq> Inl InsufficientFuel"
          using "36.prems" by (auto split: sum.splits)
        hence cond_eq: "interp_term d' fuel state condTm = interp_term d fuel state condTm"
          using "36.IH"(2)[OF Invs InvsOk] d'_ge by blast
        show ?thesis
        proof (cases "interp_term d fuel state condTm")
          case (Inl err)
          thus ?thesis using cond_eq by simp
        next
          case (Inr condVal)
          show ?thesis
          proof (cases condVal)
            case (CV_Bool b)
            show ?thesis
            proof (cases b)
              case True
              have cond_d: "interp_term d fuel state condTm = Inr (CV_Bool True)"
                using Inr CV_Bool True by simp
              have cond_d': "interp_term d' fuel state condTm = Inr (CV_Bool True)"
                using cond_eq cond_d by simp
              have body_noFuel: "interp_statement_list d fuel state bodyStmts \<noteq> Inl InsufficientFuel"
                using "36.prems" Inr CV_Bool True by (auto split: sum.splits ExecResult.splits)
              hence IH_body: "\<forall>d'\<ge>d. interp_statement_list d' fuel state bodyStmts
                                        = interp_statement_list d fuel state bodyStmts"
                using "36.IH"(3)[OF Invs InvsOk] Inr CV_Bool True by blast
              hence body_eq: "interp_statement_list d' fuel state bodyStmts
                                = interp_statement_list d fuel state bodyStmts"
                using d'_ge by blast
              show ?thesis
              proof (cases "interp_statement_list d fuel state bodyStmts")
                case (Inl err)
                thus ?thesis using body_eq cond_d cond_d' by simp
              next
                case Body: (Inr result)
                show ?thesis
                proof (cases result)
                  case (Continue state')
                  have body_d: "interp_statement_list d fuel state bodyStmts = Inr (Continue state')"
                    using Body Continue by simp
                  have body_d': "interp_statement_list d' fuel state bodyStmts = Inr (Continue state')"
                    using body_eq body_d by simp
                  have loop_noFuel: "interp_statement d fuel (restore_scope state state')
                                        (CoreStmt_While whileGhost condTm invars decr bodyStmts)
                                      \<noteq> Inl InsufficientFuel"
                    using "36.prems" cond_d body_d by auto
                  hence IH_loop: "\<forall>d'\<ge>d. interp_statement d' fuel (restore_scope state state')
                                              (CoreStmt_While whileGhost condTm invars decr bodyStmts) =
                                            interp_statement d fuel (restore_scope state state')
                                              (CoreStmt_While whileGhost condTm invars decr bodyStmts)"
                    using "36.IH"(4)[OF Invs InvsOk] Inr CV_Bool True Body Continue
                    by metis
                  have "interp_statement d' fuel (restore_scope state state')
                          (CoreStmt_While whileGhost condTm invars decr bodyStmts) =
                        interp_statement d fuel (restore_scope state state')
                          (CoreStmt_While whileGhost condTm invars decr bodyStmts)"
                    using IH_loop d'_ge by metis
                  thus ?thesis using cond_d cond_d' body_d body_d' by simp
                next
                  case (Return state' retVal)
                  have body_d: "interp_statement_list d fuel state bodyStmts = Inr (Return state' retVal)"
                    using Body Return by simp
                  have "interp_statement_list d' fuel state bodyStmts = Inr (Return state' retVal)"
                    using body_eq body_d by simp
                  thus ?thesis using cond_d cond_d' body_d by simp
                qed
              qed
            next
              case False
              have cond_d: "interp_term d fuel state condTm = Inr (CV_Bool False)"
                using Inr CV_Bool False by simp
              have "interp_term d' fuel state condTm = Inr (CV_Bool False)"
                using cond_eq cond_d by simp
              thus ?thesis using cond_d by simp
            qed
          qed (use cond_eq Inr in simp_all)
        qed
      qed
    qed
  qed
next
  (* Match *)
  case (37 d fuel state matchGhost scrutTm arms)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_term d fuel state scrutTm \<noteq> Inl InsufficientFuel"
      using "37.prems" by (auto split: sum.splits)
    hence scrut_eq: "interp_term d' fuel state scrutTm = interp_term d fuel state scrutTm"
      using "37.IH"(1) d'_ge by blast
    show "interp_statement d' (Suc fuel) state (CoreStmt_Match matchGhost scrutTm arms) =
          interp_statement d (Suc fuel) state (CoreStmt_Match matchGhost scrutTm arms)"
    proof (cases "interp_term d fuel state scrutTm")
      case (Inl err)
      thus ?thesis using scrut_eq by simp
    next
      case Scrut: (Inr scrutVal)
      show ?thesis
      proof (cases "find_matching_arm scrutVal arms")
        case (Inl err)
        thus ?thesis using Scrut scrut_eq by simp
      next
        case (Inr armStmts)
        hence "interp_statement_list d fuel state armStmts \<noteq> Inl InsufficientFuel"
          using "37.prems" Scrut by (auto split: sum.splits)
        hence "interp_statement_list d' fuel state armStmts
                 = interp_statement_list d fuel state armStmts"
          using "37.IH"(2) Scrut Inr d'_ge by blast
        thus ?thesis using Scrut Inr scrut_eq by simp
      qed
    qed
  qed
next
  (* Assert with a condition: evaluates the condition *)
  case (38 d fuel state condTm proofBody)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_term d fuel state condTm \<noteq> Inl InsufficientFuel"
      using "38.prems" by (auto split: sum.splits)
    hence "interp_term d' fuel state condTm = interp_term d fuel state condTm"
      using "38.IH" d'_ge by blast
    thus "interp_statement d' (Suc fuel) state (CoreStmt_Assert (Some condTm) proofBody)
            = interp_statement d (Suc fuel) state (CoreStmt_Assert (Some condTm) proofBody)"
      by simp
  qed
next
  (* Assert without a condition: always TypeError *)
  case 39 then show ?case by simp
next
  (* Assume: a no-op *)
  case 40 then show ?case by simp
next
  (* ShowHide: a no-op *)
  case 41 then show ?case by simp
next
  (* Obtain, depth = 0: always InsufficientFuel *)
  case 42 then show ?case by simp
next
  (* Obtain, depth > 0: as for Quantifier *)
  case (43 d fuel state varName varTy condTm)
  show ?case
  proof (intro allI impI)
    fix d' assume "d' \<ge> Suc d"
    then obtain d'' where d'_eq: "d' = Suc d''" and d''_ge: "d'' \<ge> d"
      using Suc_le_D by auto
    let ?vals = "values_of_type state (apply_subst (IS_TyArgs state) varTy)"
    let ?r = "\<lambda>dd v. converged (\<lambda>m. interp_term dd m (bind_mutable_local varName v state) condTm)"
    have ne: "choose_witness ?vals (?r d) \<noteq> Inl InsufficientFuel"
      using "43.prems" by (auto split: sum.splits)
    have agree: "?r d'' v = ?r d v" if "?r d v \<noteq> Inl InsufficientFuel" for v
    proof (rule converged_agree[OF _ _ that])
      fix m
      assume "interp_term d m (bind_mutable_local varName v state) condTm \<noteq> Inl InsufficientFuel"
      thus "interp_term d'' m (bind_mutable_local varName v state) condTm
              = interp_term d m (bind_mutable_local varName v state) condTm"
        using "43.IH" d''_ge by blast
    next
      fix m m'
      assume "interp_term d'' m (bind_mutable_local varName v state) condTm \<noteq> Inl InsufficientFuel"
        and "m \<le> m'"
      thus "interp_term d'' m' (bind_mutable_local varName v state) condTm
              = interp_term d'' m (bind_mutable_local varName v state) condTm"
        using interp_term_fuel_mono by blast
    qed
    have eq: "choose_witness ?vals (?r d'') = choose_witness ?vals (?r d)"
    proof (rule choose_witness_agree[OF _ ne])
      fix v assume "?r d v \<noteq> Inl InsufficientFuel"
      thus "?r d'' v = ?r d v" by (rule agree)
    qed
    show "interp_statement d' (Suc fuel) state (CoreStmt_Obtain varName varTy condTm)
            = interp_statement (Suc d) (Suc fuel) state (CoreStmt_Obtain varName varTy condTm)"
      using d'_eq eq by simp
  qed
next
  (* Fix: always TypeError *)
  case 44 then show ?case by simp
next
  (* Use: always TypeError *)
  case 45 then show ?case by simp
next
  (* Block *)
  case (46 d fuel state body)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_statement_list d fuel state body \<noteq> Inl InsufficientFuel"
      using "46.prems" by (auto split: sum.splits ExecResult.splits)
    hence "interp_statement_list d' fuel state body = interp_statement_list d fuel state body"
      using "46.IH" d'_ge by blast
    thus "interp_statement d' (Suc fuel) state (CoreStmt_Block body) =
          interp_statement d (Suc fuel) state (CoreStmt_Block body)"
      by simp
  qed
next
  (* interp_statement_list, fuel = 0 *)
  case 47 then show ?case by simp
next
  (* interp_statement_list, empty list *)
  case 48 then show ?case by simp
next
  (* interp_statement_list, cons *)
  case (49 d fuel state stmt stmts)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    have "interp_statement d fuel state stmt \<noteq> Inl InsufficientFuel"
      using "49.prems" by (auto split: sum.splits ExecResult.splits)
    hence stmt_eq: "interp_statement d' fuel state stmt = interp_statement d fuel state stmt"
      using "49.IH"(1) d'_ge by blast
    show "interp_statement_list d' (Suc fuel) state (stmt # stmts) =
          interp_statement_list d (Suc fuel) state (stmt # stmts)"
    proof (cases "interp_statement d fuel state stmt")
      case (Inl err)
      thus ?thesis using stmt_eq by simp
    next
      case (Inr result)
      show ?thesis
      proof (cases result)
        case (Continue state')
        have stmt_d: "interp_statement d fuel state stmt = Inr (Continue state')"
          using Inr Continue by simp
        hence "interp_statement_list d fuel state' stmts \<noteq> Inl InsufficientFuel"
          using "49.prems" by (auto split: sum.splits)
        hence "interp_statement_list d' fuel state' stmts = interp_statement_list d fuel state' stmts"
          using "49.IH"(2) Inr Continue d'_ge by blast
        thus ?thesis using stmt_d stmt_eq by simp
      next
        case (Return state' retVal)
        have stmt_d: "interp_statement d fuel state stmt = Inr (Return state' retVal)"
          using Inr Return by simp
        thus ?thesis using stmt_eq by simp
      qed
    qed
  qed
next
  (* interp_function_call, fuel = 0 *)
  case 50 then show ?case by simp
next
  (* interp_function_call, fuel > 0 *)
  case (51 d fuel state fnName argTys argTms)
  show ?case
  proof (intro allI impI)
    fix d' assume d'_ge: "d' \<ge> d"
    note noFuel = "51.prems"

    show "interp_function_call d' (Suc fuel) state fnName argTys argTms =
          interp_function_call d (Suc fuel) state fnName argTys argTms"
    proof (cases "fmlookup (IS_Functions state) fnName")
      case None
      thus ?thesis by simp
    next
      case (Some fn)
      show ?thesis
      proof (cases "length argTms \<noteq> length (IF_Args fn)")
        case True
        thus ?thesis using Some by simp
      next
        case False
        show ?thesis
        proof (cases "length argTys \<noteq> length (IF_TyArgs fn)")
          case True
          thus ?thesis using Some False by simp
        next
          case tyLen: False
          let ?refResults = "map (interp_writable_lvalue d fuel state) argTms"
          let ?valResults = "map (interp_term d fuel state) argTms"
          let ?fnArgs = "IF_Args fn"
          let ?calleeTyArgs = "fmap_of_list (zip (IF_TyArgs fn) (map (apply_subst (IS_TyArgs state)) argTys))"
          let ?clearedState = "state \<lparr> IS_Locals := fmempty, IS_Refs := fmempty,
                                         IS_ConstLocals := {||},
                                         IS_TyArgs := ?calleeTyArgs \<rparr>"

          have len_eq: "length ?fnArgs = length argTms" using False by simp

          have fold_noFuel: "fold process_one_arg (zip ?fnArgs (zip (map (interp_writable_lvalue d fuel state) argTms)
                  (map (interp_term d fuel state) argTms))) (Inr ?clearedState)
                \<noteq> Inl InsufficientFuel"
            using noFuel Some False tyLen by (auto simp: Let_def split: sum.splits ExecResult.splits)

          have tm_IH: "\<forall>argTm \<in> set argTms.
                        interp_term d fuel state argTm \<noteq> Inl InsufficientFuel
                          \<longrightarrow> (\<forall>d' \<ge> d. interp_term d' fuel state argTm = interp_term d fuel state argTm)"
            using "51.IH"(2) False Some tyLen by blast
          have lv_IH: "\<forall>argTm \<in> set argTms.
                        interp_writable_lvalue d fuel state argTm \<noteq> Inl InsufficientFuel
                          \<longrightarrow> (\<forall>d' \<ge> d. interp_writable_lvalue d' fuel state argTm
                                            = interp_writable_lvalue d fuel state argTm)"
            using "51.IH"(1) False Some tyLen by blast
          have tm_agree: "\<forall>argTm \<in> set argTms.
                        interp_term d fuel state argTm \<noteq> Inl InsufficientFuel
                          \<longrightarrow> interp_term d' fuel state argTm = interp_term d fuel state argTm"
            using tm_IH d'_ge by blast
          have lv_agree: "\<forall>argTm \<in> set argTms.
                        interp_writable_lvalue d fuel state argTm \<noteq> Inl InsufficientFuel
                          \<longrightarrow> interp_writable_lvalue d' fuel state argTm
                                = interp_writable_lvalue d fuel state argTm"
            using lv_IH d'_ge by blast

          have fold_eq: "fold process_one_arg (zip ?fnArgs (zip (map (interp_writable_lvalue d' fuel state) argTms)
                                                                (map (interp_term d' fuel state) argTms))) (Inr ?clearedState) =
                         fold process_one_arg (zip ?fnArgs (zip ?refResults ?valResults)) (Inr ?clearedState)"
            by (rule fold_process_one_arg_agree[OF tm_agree lv_agree _ fold_noFuel]) (simp add: len_eq)

          show ?thesis
          proof (cases "fold process_one_arg (zip ?fnArgs (zip ?refResults ?valResults)) (Inr ?clearedState)")
            case (Inl err)
            thus ?thesis using Some False tyLen fold_eq by (simp add: Let_def)
          next
            case PreCall: (Inr preCallState)
            show ?thesis
            proof (cases "IF_Body fn")
              case (Inl bodyStmts)
              (* Internal function: execute body statements *)
              hence body_noFuel: "interp_statement_list d fuel preCallState bodyStmts \<noteq> Inl InsufficientFuel"
                using noFuel Some False tyLen PreCall by (auto split: sum.splits ExecResult.splits simp: Let_def)
              hence IH_body: "\<forall>d'\<ge>d. interp_statement_list d' fuel preCallState bodyStmts =
                                      interp_statement_list d fuel preCallState bodyStmts"
                using "51.IH"(3) Some False tyLen PreCall Inl by blast
              have "interp_statement_list d' fuel preCallState bodyStmts =
                    interp_statement_list d fuel preCallState bodyStmts"
                using IH_body d'_ge by metis
              thus ?thesis using Some False tyLen PreCall fold_eq Inl by (simp add: Let_def)
            next
              case (Inr externFun)
              (* External function: the result depends on valResults and refResults
                 directly, so we need these to be the same at both depths. *)
              let ?filter_refs = "\<lambda>refResults. map (\<lambda>((_, vr), refResult).
                                      if vr = Ref then refResult else Inl TypeError)
                                    (zip ?fnArgs refResults)"
              have valResults_eq: "map (interp_term d' fuel state) argTms = ?valResults"
                by (rule fold_process_one_arg_ok_results_agree(1)[OF tm_agree lv_agree len_eq PreCall])
              have filtered_refs_eq: "?filter_refs (map (interp_writable_lvalue d' fuel state) argTms) =
                                      ?filter_refs ?refResults"
                by (rule fold_process_one_arg_ok_results_agree(2)[OF tm_agree lv_agree len_eq PreCall])

              have rights_vals_eq: "rights (map (interp_term d' fuel state) argTms) = rights ?valResults"
                using valResults_eq by metis

              have rights_refs_eq: "rights (?filter_refs (map (interp_writable_lvalue d' fuel state) argTms)) =
                                    rights (?filter_refs ?refResults)"
                using filtered_refs_eq by simp

              have fold_eq': "fold process_one_arg (zip ?fnArgs (zip (map (interp_writable_lvalue d' fuel state) argTms)
                                                                (map (interp_term d' fuel state) argTms))) (Inr ?clearedState) =
                             Inr preCallState"
                using fold_eq PreCall valResults_eq by argo

              show ?thesis using Some False tyLen Inr fold_eq' PreCall
                                 rights_vals_eq rights_refs_eq filtered_refs_eq
                by (simp add: Let_def)
            qed
          qed
        qed
      qed
    qed
  qed
qed


(* ========================================================================== *)
(* Convenient forms *)
(* ========================================================================== *)

(* If a run gives a non-InsufficientFuel result, then it gives the same result
   with more fuel. *)

lemma interp_term_more_fuel:
  "interp_term d f state tm = r \<Longrightarrow> r \<noteq> Inl InsufficientFuel \<Longrightarrow> f \<le> f'
     \<Longrightarrow> interp_term d f' state tm = r"
  using interp_term_fuel_mono by blast

lemma interp_statement_more_fuel:
  "interp_statement d f state stmt = r \<Longrightarrow> r \<noteq> Inl InsufficientFuel \<Longrightarrow> f \<le> f'
     \<Longrightarrow> interp_statement d f' state stmt = r"
  using interp_statement_fuel_mono by blast

lemma interp_statement_list_more_fuel:
  "interp_statement_list d f state stmts = r \<Longrightarrow> r \<noteq> Inl InsufficientFuel \<Longrightarrow> f \<le> f'
     \<Longrightarrow> interp_statement_list d f' state stmts = r"
  using interp_statement_list_fuel_mono by blast

lemma interp_function_call_more_fuel:
  "interp_function_call d f state fnName argTys argTms = r \<Longrightarrow> r \<noteq> Inl InsufficientFuel \<Longrightarrow> f \<le> f'
     \<Longrightarrow> interp_function_call d f' state fnName argTys argTms = r"
  using interp_function_call_fuel_mono by blast

(* Likewise, it gives the same result with more depth. *)

lemma interp_term_more_depth:
  "interp_term d f state tm = r \<Longrightarrow> r \<noteq> Inl InsufficientFuel \<Longrightarrow> d \<le> d'
     \<Longrightarrow> interp_term d' f state tm = r"
  using interp_term_depth_mono by blast

lemma interp_statement_more_depth:
  "interp_statement d f state stmt = r \<Longrightarrow> r \<noteq> Inl InsufficientFuel \<Longrightarrow> d \<le> d'
     \<Longrightarrow> interp_statement d' f state stmt = r"
  using interp_statement_depth_mono by blast

lemma interp_statement_list_more_depth:
  "interp_statement_list d f state stmts = r \<Longrightarrow> r \<noteq> Inl InsufficientFuel \<Longrightarrow> d \<le> d'
     \<Longrightarrow> interp_statement_list d' f state stmts = r"
  using interp_statement_list_depth_mono by blast

lemma interp_function_call_more_depth:
  "interp_function_call d f state fnName argTys argTms = r \<Longrightarrow> r \<noteq> Inl InsufficientFuel \<Longrightarrow> d \<le> d'
     \<Longrightarrow> interp_function_call d' f state fnName argTys argTms = r"
  using interp_function_call_depth_mono by blast

(* Both at once: the same result with more depth and more fuel. *)

lemma interp_term_more_depth_fuel:
  assumes "interp_term d f state tm = r" and "r \<noteq> Inl InsufficientFuel"
    and "d \<le> d'" and "f \<le> f'"
  shows "interp_term d' f' state tm = r"
  using interp_term_more_fuel[OF interp_term_more_depth[OF assms(1,2,3)] assms(2,4)] .

lemma interp_statement_more_depth_fuel:
  assumes "interp_statement d f state stmt = r" and "r \<noteq> Inl InsufficientFuel"
    and "d \<le> d'" and "f \<le> f'"
  shows "interp_statement d' f' state stmt = r"
  using interp_statement_more_fuel[OF interp_statement_more_depth[OF assms(1,2,3)] assms(2,4)] .

lemma interp_statement_list_more_depth_fuel:
  assumes "interp_statement_list d f state stmts = r" and "r \<noteq> Inl InsufficientFuel"
    and "d \<le> d'" and "f \<le> f'"
  shows "interp_statement_list d' f' state stmts = r"
  using interp_statement_list_more_fuel[OF interp_statement_list_more_depth[OF assms(1,2,3)] assms(2,4)] .

lemma interp_function_call_more_depth_fuel:
  assumes "interp_function_call d f state fnName argTys argTms = r" and "r \<noteq> Inl InsufficientFuel"
    and "d \<le> d'" and "f \<le> f'"
  shows "interp_function_call d' f' state fnName argTys argTms = r"
  using interp_function_call_more_fuel[OF interp_function_call_more_depth[OF assms(1,2,3)] assms(2,4)] .

(* Uniqueness: if two runs differ only in depth and fuel, and neither runs out of fuel,
   then the results are the same. *)

lemma interp_term_unique:
  assumes "interp_term d1 f1 state tm = r1" and "r1 \<noteq> Inl InsufficientFuel"
    and "interp_term d2 f2 state tm = r2" and "r2 \<noteq> Inl InsufficientFuel"
  shows "r1 = r2"
proof -
  have "interp_term (max d1 d2) (max f1 f2) state tm = r1"
    by (rule interp_term_more_depth_fuel[OF assms(1,2)]) simp_all
  moreover have "interp_term (max d1 d2) (max f1 f2) state tm = r2"
    by (rule interp_term_more_depth_fuel[OF assms(3,4)]) simp_all
  ultimately show ?thesis by simp
qed

lemma interp_statement_unique:
  assumes "interp_statement d1 f1 state stmt = r1" and "r1 \<noteq> Inl InsufficientFuel"
    and "interp_statement d2 f2 state stmt = r2" and "r2 \<noteq> Inl InsufficientFuel"
  shows "r1 = r2"
proof -
  have "interp_statement (max d1 d2) (max f1 f2) state stmt = r1"
    by (rule interp_statement_more_depth_fuel[OF assms(1,2)]) simp_all
  moreover have "interp_statement (max d1 d2) (max f1 f2) state stmt = r2"
    by (rule interp_statement_more_depth_fuel[OF assms(3,4)]) simp_all
  ultimately show ?thesis by simp
qed

lemma interp_statement_list_unique:
  assumes "interp_statement_list d1 f1 state stmts = r1" and "r1 \<noteq> Inl InsufficientFuel"
    and "interp_statement_list d2 f2 state stmts = r2" and "r2 \<noteq> Inl InsufficientFuel"
  shows "r1 = r2"
proof -
  have "interp_statement_list (max d1 d2) (max f1 f2) state stmts = r1"
    by (rule interp_statement_list_more_depth_fuel[OF assms(1,2)]) simp_all
  moreover have "interp_statement_list (max d1 d2) (max f1 f2) state stmts = r2"
    by (rule interp_statement_list_more_depth_fuel[OF assms(3,4)]) simp_all
  ultimately show ?thesis by simp
qed

lemma interp_function_call_unique:
  assumes "interp_function_call d1 f1 state fnName argTys argTms = r1" and "r1 \<noteq> Inl InsufficientFuel"
    and "interp_function_call d2 f2 state fnName argTys argTms = r2" and "r2 \<noteq> Inl InsufficientFuel"
  shows "r1 = r2"
proof -
  have "interp_function_call (max d1 d2) (max f1 f2) state fnName argTys argTms = r1"
    by (rule interp_function_call_more_depth_fuel[OF assms(1,2)]) simp_all
  moreover have "interp_function_call (max d1 d2) (max f1 f2) state fnName argTys argTms = r2"
    by (rule interp_function_call_more_depth_fuel[OF assms(3,4)]) simp_all
  ultimately show ?thesis by simp
qed

end
