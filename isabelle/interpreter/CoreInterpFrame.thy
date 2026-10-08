theory CoreInterpFrame
  imports CoreInterpPreservation
begin

(* The frame property of the interpreter: which parts of the store a statement
   or a function call can change.

    - Running a statement changes only the store cells that the current frame
      refers to (the cells of its locals and the cells its refs point into),
      and the cells it allocates itself. See frame_step.

    - A function call returns the caller's locals, refs, const-locals and type
      arguments unchanged, leaves the store at the same length, and changes
      only the cells of the lvalues passed as Ref arguments. See
      interp_function_call_frame.

   These are facts about the interpreter alone; no typing is involved. *)


(* ========================================================================== *)
(* The addresses a frame refers to *)
(* ========================================================================== *)

(* The store addresses that the current frame refers to: the cells of its
   local variables, and the cells that its refs point into. *)
definition frame_addrs :: "'w InterpState \<Rightarrow> nat set" where
  "frame_addrs state =
    {a. \<exists>name. fmlookup (IS_Locals state) name = Some a} \<union>
    {a. \<exists>name path. fmlookup (IS_Refs state) name = Some (a, path)}"

lemma frame_addrs_localI:
  "fmlookup (IS_Locals state) name = Some a \<Longrightarrow> a \<in> frame_addrs state"
  unfolding frame_addrs_def by blast

lemma frame_addrs_refI:
  "fmlookup (IS_Refs state) name = Some (a, path) \<Longrightarrow> a \<in> frame_addrs state"
  unfolding frame_addrs_def by blast

lemma frame_addrs_eqI:
  assumes "IS_Locals state' = IS_Locals state"
    and "IS_Refs state' = IS_Refs state"
  shows "frame_addrs state' = frame_addrs state"
  using assms by (simp add: frame_addrs_def)

(* Binding a name as a local at addr adds at most addr. *)
lemma frame_addrs_bind_local:
  assumes "IS_Locals state' = fmupd name addr (IS_Locals state)"
    and "IS_Refs state' = fmdrop name (IS_Refs state)"
  shows "frame_addrs state' \<subseteq> insert addr (frame_addrs state)"
  unfolding frame_addrs_def using assms by (auto split: if_splits)

(* Binding a name as a ref into addr adds at most addr. *)
lemma frame_addrs_bind_ref:
  assumes "IS_Locals state' = fmdrop name (IS_Locals state)"
    and "IS_Refs state' = fmupd name (addr, path) (IS_Refs state)"
  shows "frame_addrs state' \<subseteq> insert addr (frame_addrs state)"
  unfolding frame_addrs_def using assms by (auto split: if_splits)

(* The address of the store cell that a variable name denotes: its own cell if
   it is a local, or the cell it points into if it is a ref. *)
definition var_addr :: "'w InterpState \<Rightarrow> string \<Rightarrow> nat option" where
  "var_addr state name =
    (case fmlookup (IS_Locals state) name of
      Some addr \<Rightarrow> Some addr
    | None \<Rightarrow> map_option fst (fmlookup (IS_Refs state) name))"

lemma var_addr_in_frame:
  assumes "var_addr state name = Some a"
  shows "a \<in> frame_addrs state"
proof (cases "fmlookup (IS_Locals state) name")
  case (Some a')
  with assms have "a' = a" by (simp add: var_addr_def)
  with Some show ?thesis by (auto intro: frame_addrs_localI)
next
  case None
  with assms obtain path where "fmlookup (IS_Refs state) name = Some (a, path)"
    by (cases "fmlookup (IS_Refs state) name") (auto simp: var_addr_def)
  then show ?thesis by (rule frame_addrs_refI)
qed

(* Every address the frame refers to is inside the store. *)
definition addrs_in_bounds :: "'w InterpState \<Rightarrow> bool" where
  "addrs_in_bounds state \<equiv> \<forall>a \<in> frame_addrs state. a < length (IS_Store state)"


(* ========================================================================== *)
(* The frame relation between two states *)
(* ========================================================================== *)

(* state' can be reached from state by running statements in the same frame:

    - the store has not shrunk;
    - the cells of state that its frame does not refer to are unchanged;
    - the frame of state' refers only to addresses that the frame of state
      referred to, or that have been allocated since. *)
definition frame_step :: "'w InterpState \<Rightarrow> 'w InterpState \<Rightarrow> bool" where
  "frame_step state state' \<equiv>
    length (IS_Store state) \<le> length (IS_Store state') \<and>
    (\<forall>a < length (IS_Store state). a \<notin> frame_addrs state \<longrightarrow>
        IS_Store state' ! a = IS_Store state ! a) \<and>
    (\<forall>a \<in> frame_addrs state'. a \<in> frame_addrs state \<or>
        (length (IS_Store state) \<le> a \<and> a < length (IS_Store state')))"

lemma frame_stepI:
  assumes "length (IS_Store state) \<le> length (IS_Store state')"
    and "\<And>a. a < length (IS_Store state) \<Longrightarrow> a \<notin> frame_addrs state
              \<Longrightarrow> IS_Store state' ! a = IS_Store state ! a"
    and "\<And>a. a \<in> frame_addrs state'
              \<Longrightarrow> a \<in> frame_addrs state \<or>
                  (length (IS_Store state) \<le> a \<and> a < length (IS_Store state'))"
  shows "frame_step state state'"
  unfolding frame_step_def
proof (intro conjI allI impI ballI)
  show "length (IS_Store state) \<le> length (IS_Store state')" by (rule assms(1))
next
  fix a assume "a < length (IS_Store state)" and "a \<notin> frame_addrs state"
  then show "IS_Store state' ! a = IS_Store state ! a" by (rule assms(2))
next
  fix a assume "a \<in> frame_addrs state'"
  then show "a \<in> frame_addrs state \<or>
             (length (IS_Store state) \<le> a \<and> a < length (IS_Store state'))"
    by (rule assms(3))
qed

lemma frame_stepD:
  assumes "frame_step state state'"
  shows "length (IS_Store state) \<le> length (IS_Store state')"
    and "\<And>a. a < length (IS_Store state) \<Longrightarrow> a \<notin> frame_addrs state
              \<Longrightarrow> IS_Store state' ! a = IS_Store state ! a"
    and "\<And>a. a \<in> frame_addrs state'
              \<Longrightarrow> a \<in> frame_addrs state \<or>
                  (length (IS_Store state) \<le> a \<and> a < length (IS_Store state'))"
  using assms unfolding frame_step_def by blast+

lemma frame_step_refl:
  "frame_step state state"
  unfolding frame_step_def by auto

lemma frame_step_trans:
  assumes "frame_step s1 s2" and "frame_step s2 s3"
  shows "frame_step s1 s3"
proof (rule frame_stepI)
  show "length (IS_Store s1) \<le> length (IS_Store s3)"
    using frame_stepD(1)[OF assms(1)] frame_stepD(1)[OF assms(2)] by simp
next
  fix a assume lt: "a < length (IS_Store s1)" and notin: "a \<notin> frame_addrs s1"
  have lt2: "a < length (IS_Store s2)"
    using lt frame_stepD(1)[OF assms(1)] by simp
  have notin2: "a \<notin> frame_addrs s2"
  proof
    assume "a \<in> frame_addrs s2"
    from frame_stepD(3)[OF assms(1) this] lt notin show False by auto
  qed
  from frame_stepD(2)[OF assms(2) lt2 notin2] frame_stepD(2)[OF assms(1) lt notin]
  show "IS_Store s3 ! a = IS_Store s1 ! a" by simp
next
  fix a assume "a \<in> frame_addrs s3"
  from frame_stepD(3)[OF assms(2) this]
  show "a \<in> frame_addrs s1 \<or> (length (IS_Store s1) \<le> a \<and> a < length (IS_Store s3))"
  proof
    assume "a \<in> frame_addrs s2"
    from frame_stepD(3)[OF assms(1) this] frame_stepD(1)[OF assms(2)]
    show ?thesis by auto
  next
    assume "length (IS_Store s2) \<le> a \<and> a < length (IS_Store s3)"
    with frame_stepD(1)[OF assms(1)] show ?thesis by auto
  qed
qed

(* The frame relation preserves "every address is inside the store". *)
lemma frame_step_addrs_in_bounds:
  assumes "frame_step state state'" and "addrs_in_bounds state"
  shows "addrs_in_bounds state'"
  unfolding addrs_in_bounds_def
proof
  fix a assume "a \<in> frame_addrs state'"
  from frame_stepD(3)[OF assms(1) this]
  show "a < length (IS_Store state')"
  proof
    assume "a \<in> frame_addrs state"
    with assms(2) have "a < length (IS_Store state)"
      by (auto simp: addrs_in_bounds_def)
    with frame_stepD(1)[OF assms(1)] show ?thesis by simp
  next
    assume "length (IS_Store state) \<le> a \<and> a < length (IS_Store state')"
    then show ?thesis by simp
  qed
qed

(* Allocating a fresh cell and binding a name to it. *)
lemma frame_step_bind_fresh:
  assumes "IS_Store state' = IS_Store state @ [v]"
    and "IS_Locals state' = fmupd name (length (IS_Store state)) (IS_Locals state)"
    and "IS_Refs state' = fmdrop name (IS_Refs state)"
  shows "frame_step state state'"
proof (rule frame_stepI)
  show "length (IS_Store state) \<le> length (IS_Store state')"
    using assms(1) by simp
next
  fix a assume "a < length (IS_Store state)" and "a \<notin> frame_addrs state"
  then show "IS_Store state' ! a = IS_Store state ! a"
    using assms(1) by (simp add: nth_append)
next
  fix a assume "a \<in> frame_addrs state'"
  with frame_addrs_bind_local[OF assms(2,3)]
  have "a = length (IS_Store state) \<or> a \<in> frame_addrs state" by auto
  then show "a \<in> frame_addrs state \<or>
             (length (IS_Store state) \<le> a \<and> a < length (IS_Store state'))"
    using assms(1) by auto
qed

(* Binding a name as a ref into a cell the frame already refers to. *)
lemma frame_step_bind_ref:
  assumes "IS_Store state' = IS_Store state"
    and "IS_Locals state' = fmdrop name (IS_Locals state)"
    and "IS_Refs state' = fmupd name (addr, path) (IS_Refs state)"
    and "addr \<in> frame_addrs state"
  shows "frame_step state state'"
proof (rule frame_stepI)
  show "length (IS_Store state) \<le> length (IS_Store state')"
    using assms(1) by simp
next
  fix a assume "a < length (IS_Store state)" and "a \<notin> frame_addrs state"
  show "IS_Store state' ! a = IS_Store state ! a"
    using assms(1) by simp
next
  fix a assume "a \<in> frame_addrs state'"
  with frame_addrs_bind_ref[OF assms(2,3)] assms(4)
  have "a \<in> frame_addrs state" by auto
  then show "a \<in> frame_addrs state \<or>
             (length (IS_Store state) \<le> a \<and> a < length (IS_Store state'))"
    by simp
qed

(* Writing to a cell the frame refers to. *)
lemma frame_step_store_update:
  assumes "IS_Store state' = (IS_Store state)[addr := v]"
    and "IS_Locals state' = IS_Locals state"
    and "IS_Refs state' = IS_Refs state"
    and "addr \<in> frame_addrs state"
  shows "frame_step state state'"
proof (rule frame_stepI)
  show "length (IS_Store state) \<le> length (IS_Store state')"
    using assms(1) by simp
next
  fix a assume "a < length (IS_Store state)" and notin: "a \<notin> frame_addrs state"
  from notin assms(4) have "addr \<noteq> a" by auto
  then show "IS_Store state' ! a = IS_Store state ! a"
    using assms(1) by simp
next
  fix a assume "a \<in> frame_addrs state'"
  then have "a \<in> frame_addrs state"
    using frame_addrs_eqI[OF assms(2,3)] by simp
  then show "a \<in> frame_addrs state \<or>
             (length (IS_Store state) \<le> a \<and> a < length (IS_Store state'))"
    by simp
qed

(* Leaving a scope: the frame goes back to what it was, and the cells
   allocated inside the scope are dropped. *)
lemma frame_step_restore_scope:
  assumes "frame_step state state'"
  shows "frame_step state (restore_scope state state')"
proof (rule frame_stepI)
  show "length (IS_Store state) \<le> length (IS_Store (restore_scope state state'))"
    using frame_stepD(1)[OF assms] by simp
next
  fix a assume lt: "a < length (IS_Store state)" and notin: "a \<notin> frame_addrs state"
  from frame_stepD(2)[OF assms lt notin] lt
  show "IS_Store (restore_scope state state') ! a = IS_Store state ! a" by simp
next
  fix a assume "a \<in> frame_addrs (restore_scope state state')"
  then have "a \<in> frame_addrs state" by (simp add: frame_addrs_def)
  then show "a \<in> frame_addrs state \<or>
             (length (IS_Store state) \<le> a
              \<and> a < length (IS_Store (restore_scope state state')))"
    by simp
qed

lemma frame_step_bind_mutable_local:
  "frame_step state (bind_mutable_local varName val state)"
  by (rule frame_step_bind_fresh[where v = val and name = varName])
     (simp_all add: Let_def)


(* ========================================================================== *)
(* Writable lvalues *)
(* ========================================================================== *)

(* The address of a writable lvalue is the address of its base variable. *)
lemma interp_writable_lvalue_addr:
  assumes "interp_writable_lvalue d fuel state tm = Inr (addr, path)"
  shows "\<exists>name. lvalue_base_name tm = Some name \<and> var_addr state name = Some addr"
  using assms
proof (induction fuel arbitrary: tm path)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases tm)
    case (CoreTm_Var varName)
    with Suc.prems show ?thesis
      by (auto simp: var_addr_def split: if_splits option.splits prod.splits)
  next
    case (CoreTm_RecordProj tm' fldName)
    with Suc.prems obtain path' where
      sub: "interp_writable_lvalue d fuel state tm' = Inr (addr, path')"
      by (auto split: sum.splits prod.splits)
    from Suc.IH[OF sub] CoreTm_RecordProj show ?thesis by simp
  next
    case (CoreTm_VariantProj tm' ctorName)
    with Suc.prems obtain path' where
      sub: "interp_writable_lvalue d fuel state tm' = Inr (addr, path')"
      by (auto split: sum.splits prod.splits)
    from Suc.IH[OF sub] CoreTm_VariantProj show ?thesis by simp
  next
    case (CoreTm_ArrayProj tm' idxTms)
    with Suc.prems obtain path' where
      sub: "interp_writable_lvalue d fuel state tm' = Inr (addr, path')"
      by (auto split: sum.splits prod.splits)
    from Suc.IH[OF sub] CoreTm_ArrayProj show ?thesis by simp
  next
    case (CoreTm_Cast targetTy tm')
    with Suc.prems obtain elemTy dims path' where
      ty_eq: "targetTy = CoreTy_Array elemTy dims" and
      sub: "interp_writable_lvalue d fuel state tm' = Inr (addr, path')"
      by (auto split: CoreType.splits sum.splits prod.splits)
    from Suc.IH[OF sub] CoreTm_Cast ty_eq show ?thesis by simp
  qed (use Suc.prems in simp_all)
qed

lemma interp_writable_lvalue_in_frame:
  assumes "interp_writable_lvalue d fuel state tm = Inr (addr, path)"
  shows "addr \<in> frame_addrs state"
  using interp_writable_lvalue_addr[OF assms] var_addr_in_frame by blast


(* ========================================================================== *)
(* Swap *)
(* ========================================================================== *)

lemma perform_swap_frame:
  assumes "perform_swap state (addr1, path1) (addr2, path2) = Inr state'"
    and "addr1 \<in> frame_addrs state"
    and "addr2 \<in> frame_addrs state"
  shows "frame_step state state'"
proof -
  from assms(1)[symmetric] obtain new_val1 new_val2 where
    store': "IS_Store state' = (IS_Store state)[addr1 := new_val1, addr2 := new_val2]" and
    locals': "IS_Locals state' = IS_Locals state" and
    refs': "IS_Refs state' = IS_Refs state"
    by (auto simp: Let_def split: sum.splits)
  show ?thesis
  proof (rule frame_stepI)
    show "length (IS_Store state) \<le> length (IS_Store state')"
      using store' by simp
  next
    fix a assume "a < length (IS_Store state)" and notin: "a \<notin> frame_addrs state"
    from notin assms(2,3) have "addr1 \<noteq> a" and "addr2 \<noteq> a" by auto
    then show "IS_Store state' ! a = IS_Store state ! a"
      using store' by simp
  next
    fix a assume "a \<in> frame_addrs state'"
    then have "a \<in> frame_addrs state"
      using frame_addrs_eqI[OF locals' refs'] by simp
    then show "a \<in> frame_addrs state \<or>
               (length (IS_Store state) \<le> a \<and> a < length (IS_Store state'))"
      by simp
  qed
qed


(* ========================================================================== *)
(* Binding the arguments of a call *)
(* ========================================================================== *)

(* The addresses of the lvalues passed as Ref arguments, given the list of
   (parameter, lvalue result, value result) triples that process_one_arg
   consumes. *)
definition ref_arg_addrs ::
    "((string \<times> VarOrRef)
      \<times> (InterpError + nat \<times> LValuePath list)
      \<times> (InterpError + CoreValue)) list \<Rightarrow> nat set" where
  "ref_arg_addrs argTuples =
    {a. \<exists>name path valRes.
          ((name, Ref), Inr (a, path), valRes) \<in> set argTuples}"

(* Binding one argument only appends to the store. The new frame refers to
   what the old one did, plus either a freshly allocated cell (Var parameter)
   or the address of the lvalue passed (Ref parameter). *)
lemma process_one_arg_frame:
  assumes "process_one_arg arg (Inr state) = Inr state'"
  shows "(\<exists>extra. IS_Store state' = IS_Store state @ extra) \<and>
         (\<forall>a \<in> frame_addrs state'.
            a \<in> frame_addrs state \<or> a \<in> ref_arg_addrs [arg] \<or>
            (length (IS_Store state) \<le> a \<and> a < length (IS_Store state')))"
proof -
  obtain name vr refRes valRes where arg_eq: "arg = ((name, vr), refRes, valRes)"
    by (cases arg) auto
  show ?thesis
  proof (cases vr)
    case Var
    show ?thesis
    proof (cases valRes)
      case (Inl err)
      with arg_eq Var assms show ?thesis by simp
    next
      case (Inr val)
      from arg_eq Var Inr assms[symmetric] have
        store': "IS_Store state' = IS_Store state @ [val]" and
        locals': "IS_Locals state' = fmupd name (length (IS_Store state)) (IS_Locals state)" and
        refs': "IS_Refs state' = fmdrop name (IS_Refs state)"
        by (simp_all add: Let_def)
      have step: "frame_step state state'"
        by (rule frame_step_bind_fresh[OF store' locals' refs'])
      show ?thesis
      proof (intro conjI ballI)
        show "\<exists>extra. IS_Store state' = IS_Store state @ extra"
          using store' by blast
      next
        fix a assume "a \<in> frame_addrs state'"
        from frame_stepD(3)[OF step this]
        show "a \<in> frame_addrs state \<or> a \<in> ref_arg_addrs [arg] \<or>
              (length (IS_Store state) \<le> a \<and> a < length (IS_Store state'))"
          by blast
      qed
    qed
  next
    case Ref
    show ?thesis
    proof (cases refRes)
      case (Inl err)
      with arg_eq Ref assms show ?thesis by simp
    next
      case refInr: (Inr addrPath)
      obtain addr path where addrPath_eq: "addrPath = (addr, path)" by (cases addrPath)
      show ?thesis
      proof (cases valRes)
        case (Inl err)
        with arg_eq Ref refInr addrPath_eq assms show ?thesis by simp
      next
        case (Inr v)
        from arg_eq Ref refInr addrPath_eq Inr assms[symmetric] have
          store': "IS_Store state' = IS_Store state" and
          locals': "IS_Locals state' = fmdrop name (IS_Locals state)" and
          refs': "IS_Refs state' = fmupd name (addr, path) (IS_Refs state)"
          by simp_all
        have in_refs: "addr \<in> ref_arg_addrs [arg]"
          using arg_eq Ref refInr addrPath_eq by (auto simp: ref_arg_addrs_def)
        show ?thesis
        proof (intro conjI ballI)
          show "\<exists>extra. IS_Store state' = IS_Store state @ extra"
            using store' by simp
        next
          fix a assume "a \<in> frame_addrs state'"
          with frame_addrs_bind_ref[OF locals' refs']
          have "a = addr \<or> a \<in> frame_addrs state" by auto
          then show "a \<in> frame_addrs state \<or> a \<in> ref_arg_addrs [arg] \<or>
                     (length (IS_Store state) \<le> a \<and> a < length (IS_Store state'))"
            using in_refs by blast
        qed
      qed
    qed
  qed
qed

lemma fold_process_one_arg_frame:
  assumes "fold process_one_arg argTuples (Inr state) = Inr state'"
  shows "(\<exists>extra. IS_Store state' = IS_Store state @ extra) \<and>
         (\<forall>a \<in> frame_addrs state'.
            a \<in> frame_addrs state \<or> a \<in> ref_arg_addrs argTuples \<or>
            (length (IS_Store state) \<le> a \<and> a < length (IS_Store state')))"
  using assms
proof (induction argTuples arbitrary: state)
  case Nil
  then show ?case by auto
next
  case (Cons arg rest)
  show ?case
  proof (cases "process_one_arg arg (Inr state)")
    case (Inl err)
    then have "fold process_one_arg (arg # rest) (Inr state) = Inl err"
      by (simp add: fold_process_one_arg_error)
    with Cons.prems show ?thesis by simp
  next
    case (Inr mid)
    from Inr Cons.prems have rest_eq: "fold process_one_arg rest (Inr mid) = Inr state'"
      by simp
    note step = process_one_arg_frame[OF Inr]
    note tail = Cons.IH[OF rest_eq]
    from step obtain extra1 where s1: "IS_Store mid = IS_Store state @ extra1" by blast
    from tail obtain extra2 where s2: "IS_Store state' = IS_Store mid @ extra2" by blast
    have len1: "length (IS_Store state) \<le> length (IS_Store mid)" using s1 by simp
    have len2: "length (IS_Store mid) \<le> length (IS_Store state')" using s2 by simp
    have sub1: "ref_arg_addrs [arg] \<subseteq> ref_arg_addrs (arg # rest)"
      and sub2: "ref_arg_addrs rest \<subseteq> ref_arg_addrs (arg # rest)"
      by (auto simp: ref_arg_addrs_def)
    show ?thesis
    proof (intro conjI ballI)
      show "\<exists>extra. IS_Store state' = IS_Store state @ extra"
        using s1 s2 by simp
    next
      fix a assume a_in: "a \<in> frame_addrs state'"
      from tail a_in
      have from_tail: "a \<in> frame_addrs mid \<or> a \<in> ref_arg_addrs rest \<or>
                       (length (IS_Store mid) \<le> a \<and> a < length (IS_Store state'))"
        by blast
      from step
      have from_step: "a \<in> frame_addrs mid \<longrightarrow>
                       a \<in> frame_addrs state \<or> a \<in> ref_arg_addrs [arg] \<or>
                       (length (IS_Store state) \<le> a \<and> a < length (IS_Store mid))"
        by blast
      from from_tail from_step sub1 sub2 len1 len2
      show "a \<in> frame_addrs state \<or> a \<in> ref_arg_addrs (arg # rest) \<or>
            (length (IS_Store state) \<le> a \<and> a < length (IS_Store state'))"
        by auto
    qed
  qed
qed

(* A Ref-argument address comes from some argument position whose parameter
   is a Ref and whose lvalue evaluated to that address. *)
lemma ref_arg_addrs_zip:
  assumes "a \<in> ref_arg_addrs (zip args (zip refResults valResults))"
  shows "\<exists>i path. i < length args \<and> i < length refResults \<and>
                  snd (args ! i) = Ref \<and> refResults ! i = Inr (a, path)"
proof -
  from assms obtain name path valRes where
    "((name, Ref), Inr (a, path), valRes) \<in> set (zip args (zip refResults valResults))"
    unfolding ref_arg_addrs_def by blast
  then obtain i where i: "args ! i = (name, Ref)" "refResults ! i = Inr (a, path)"
                         "i < length args" "i < length refResults"
    by (auto simp: in_set_zip)
  have "i < length args \<and> i < length refResults \<and>
        snd (args ! i) = Ref \<and> refResults ! i = Inr (a, path)"
    using i by simp
  then show ?thesis by blast
qed


(* ========================================================================== *)
(* Ref updates of an extern function *)
(* ========================================================================== *)

lemma rights_set:
  "set (rights xs) = {x. Inr x \<in> set xs}"
  by (induction xs rule: rights.induct) auto

(* The lvalues that an extern function may update are those passed in Ref
   argument positions. *)
lemma extern_refs_addrs:
  assumes "(a, path) \<in> set (rights (map (\<lambda>((_, vr), refResult).
                                            if vr = Ref then refResult else Inl TypeError)
                                         (zip args refResults)))"
  shows "\<exists>i. i < length args \<and> i < length refResults \<and>
             snd (args ! i) = Ref \<and> refResults ! i = Inr (a, path)"
proof -
  from assms obtain name where
    "((name, Ref), Inr (a, path)) \<in> set (zip args refResults)"
    by (auto simp: rights_set split: if_splits)
  then obtain i where i: "args ! i = (name, Ref)" "refResults ! i = Inr (a, path)"
                         "i < length args" "i < length refResults"
    by (auto simp: in_set_zip)
  have "i < length args \<and> i < length refResults \<and>
        snd (args ! i) = Ref \<and> refResults ! i = Inr (a, path)"
    using i by simp
  then show ?thesis by blast
qed

(* apply_ref_updates changes only the store, keeps its length, and writes only
   to the addresses of the given lvalues. *)
lemma apply_ref_updates_frame:
  assumes "apply_ref_updates state lvs vals = Inr state'"
  shows "IS_Locals state' = IS_Locals state \<and>
         IS_Refs state' = IS_Refs state \<and>
         IS_ConstLocals state' = IS_ConstLocals state \<and>
         IS_TyArgs state' = IS_TyArgs state \<and>
         length (IS_Store state') = length (IS_Store state) \<and>
         (\<forall>a. a \<notin> fst ` set lvs \<longrightarrow> IS_Store state' ! a = IS_Store state ! a)"
  using assms
proof (induction lvs arbitrary: state vals)
  case Nil
  then show ?case by (cases vals) simp_all
next
  case (Cons lv rest)
  obtain addr path where lv_eq: "lv = (addr, path)" by (cases lv)
  from Cons.prems obtain v vs where vals_eq: "vals = v # vs"
    by (cases vals) (simp_all add: lv_eq)
  from Cons.prems obtain updated where
    rest_eq: "apply_ref_updates (state \<lparr> IS_Store := (IS_Store state)[addr := updated] \<rparr>)
                rest vs = Inr state'"
    unfolding lv_eq vals_eq by (auto simp: Let_def split: sum.splits)
  note IH = Cons.IH[OF rest_eq]
  have same: "\<forall>a. a \<notin> fst ` set (lv # rest) \<longrightarrow> IS_Store state' ! a = IS_Store state ! a"
  proof (intro allI impI)
    fix a assume "a \<notin> fst ` set (lv # rest)"
    then have ne: "addr \<noteq> a" and notin: "a \<notin> fst ` set rest"
      by (auto simp: lv_eq)
    from IH notin have "IS_Store state' ! a = (IS_Store state)[addr := updated] ! a"
      by auto
    then show "IS_Store state' ! a = IS_Store state ! a" using ne by simp
  qed
  from IH same show ?case by simp
qed


(* ========================================================================== *)
(* The frame property of a call *)
(* ========================================================================== *)

(* The addresses of the lvalues passed as Ref arguments in a call of fnName
   with arguments argTms: the addresses of the base variables of the argument
   terms in Ref parameter positions. *)
definition call_ref_addrs :: "'w InterpState \<Rightarrow> string \<Rightarrow> CoreTerm list \<Rightarrow> nat set" where
  "call_ref_addrs state fnName argTms =
    {a. \<exists>f i name.
          fmlookup (IS_Functions state) fnName = Some f \<and>
          i < length argTms \<and> i < length (IF_Args f) \<and>
          snd (IF_Args f ! i) = Ref \<and>
          lvalue_base_name (argTms ! i) = Some name \<and>
          var_addr state name = Some a}"

lemma call_ref_addrs_subset:
  "call_ref_addrs state fnName argTms \<subseteq> frame_addrs state"
  by (auto simp: call_ref_addrs_def intro: var_addr_in_frame)

lemma ref_result_in_call_ref_addrs:
  assumes "fmlookup (IS_Functions state) fnName = Some f"
    and "i < length (IF_Args f)"
    and "i < length argTms"
    and "snd (IF_Args f ! i) = Ref"
    and "map (interp_writable_lvalue d fuel state) argTms ! i = Inr (a, path)"
  shows "a \<in> call_ref_addrs state fnName argTms"
proof -
  from assms(3,5) have "interp_writable_lvalue d fuel state (argTms ! i) = Inr (a, path)"
    by simp
  from interp_writable_lvalue_addr[OF this] obtain name where
    "lvalue_base_name (argTms ! i) = Some name" and "var_addr state name = Some a"
    by blast
  with assms(1,2,3,4) show ?thesis
    unfolding call_ref_addrs_def by blast
qed

(* state' is the caller's state after a call of fnName with arguments argTms
   made from state: the caller's frame is as it was, the store has the same
   length, and only the cells passed as Ref arguments may have changed. *)
definition call_frame ::
    "'w InterpState \<Rightarrow> string \<Rightarrow> CoreTerm list \<Rightarrow> 'w InterpState \<Rightarrow> bool" where
  "call_frame state fnName argTms state' \<equiv>
    IS_Locals state' = IS_Locals state \<and>
    IS_Refs state' = IS_Refs state \<and>
    IS_ConstLocals state' = IS_ConstLocals state \<and>
    IS_TyArgs state' = IS_TyArgs state \<and>
    length (IS_Store state') = length (IS_Store state) \<and>
    (\<forall>a < length (IS_Store state). a \<notin> call_ref_addrs state fnName argTms \<longrightarrow>
        IS_Store state' ! a = IS_Store state ! a)"

lemma call_frame_frame_addrs:
  assumes "call_frame state fnName argTms state'"
  shows "frame_addrs state' = frame_addrs state"
  using assms by (simp add: call_frame_def frame_addrs_def)

lemma call_frame_frame_step:
  assumes "call_frame state fnName argTms state'"
  shows "frame_step state state'"
proof (rule frame_stepI)
  show "length (IS_Store state) \<le> length (IS_Store state')"
    using assms by (simp add: call_frame_def)
next
  fix a assume lt: "a < length (IS_Store state)" and notin: "a \<notin> frame_addrs state"
  from notin have "a \<notin> call_ref_addrs state fnName argTms"
    using call_ref_addrs_subset by blast
  with assms lt show "IS_Store state' ! a = IS_Store state ! a"
    by (auto simp: call_frame_def)
next
  fix a assume "a \<in> frame_addrs state'"
  then have "a \<in> frame_addrs state"
    using call_frame_frame_addrs[OF assms] by simp
  then show "a \<in> frame_addrs state \<or>
             (length (IS_Store state) \<le> a \<and> a < length (IS_Store state'))"
    by simp
qed


(* ========================================================================== *)
(* The main frame lemma *)
(* ========================================================================== *)

(* All three statements are proved simultaneously by induction on the fuel.
   The depth is fixed: the statement, statement-list and function-call
   functions only ever call each other at the same depth. (Terms do not return
   a state, so nothing needs to be proved about them.) *)
lemma interp_frame:
  shows "\<forall>(state :: 'w InterpState) res.
           interp_statement d fuel state stmt = Inr res \<longrightarrow>
             frame_step state (result_state res)"
    and "\<forall>(state :: 'w InterpState) res.
           interp_statement_list d fuel state stmts = Inr res \<longrightarrow>
             frame_step state (result_state res)"
    and "\<forall>(state :: 'w InterpState) state' retVal.
           interp_function_call d fuel state fnName argTys argTms = Inr (state', retVal) \<longrightarrow>
             call_frame state fnName argTms state'"
proof (induction fuel arbitrary: stmt stmts fnName argTys argTms rule: nat.induct)
  case zero
  {
    case 1 show ?case by simp
  next
    case 2 show ?case by simp
  next
    case 3 show ?case by simp
  }
next
  case (Suc fuel)
  note IH_stmt = Suc.IH(1)
  note IH_stmt_list = Suc.IH(2)
  note IH_call = Suc.IH(3)
  {
    case (1 stmt) show ?case
    proof (intro allI impI)
      fix state :: "'w InterpState" and res :: "'w ExecResult"
      assume H: "interp_statement d (Suc fuel) state stmt = Inr res"
      show "frame_step state (result_state res)"
      proof (cases stmt)
        case (CoreStmt_VarDecl g varName vr ty initTm)
        show ?thesis
        proof (cases vr)
          case Var
          from Var H CoreStmt_VarDecl obtain initVal where
            iv: "interp_term d fuel state initTm = Inr initVal"
            by (auto split: sum.splits)
          from Var H[symmetric] CoreStmt_VarDecl iv have
            store': "IS_Store (result_state res) = IS_Store state @ [initVal]" and
            locals': "IS_Locals (result_state res)
                        = fmupd varName (length (IS_Store state)) (IS_Locals state)" and
            refs': "IS_Refs (result_state res) = fmdrop varName (IS_Refs state)"
            by (simp_all add: Let_def)
          show ?thesis by (rule frame_step_bind_fresh[OF store' locals' refs'])
        next
          case Ref
          \<comment> \<open>Two branches: const-base (copy) or writable-base (alias). \<close>
          from Ref H CoreStmt_VarDecl obtain baseName where
            base: "lvalue_base_name initTm = Some baseName"
            by (cases "lvalue_base_name initTm") simp_all
          show ?thesis
          proof (cases "baseName |\<in>| IS_ConstLocals state
                        \<or> (fmlookup (IS_Locals state) baseName = None
                           \<and> fmlookup (IS_Refs state) baseName = None)")
            case True
            with Ref H CoreStmt_VarDecl base obtain val where
              iv: "interp_term d fuel state initTm = Inr val"
              by (auto split: sum.splits)
            from Ref H[symmetric] CoreStmt_VarDecl base True iv have
              store': "IS_Store (result_state res) = IS_Store state @ [val]" and
              locals': "IS_Locals (result_state res)
                          = fmupd varName (length (IS_Store state)) (IS_Locals state)" and
              refs': "IS_Refs (result_state res) = fmdrop varName (IS_Refs state)"
              by (simp_all add: Let_def)
            show ?thesis by (rule frame_step_bind_fresh[OF store' locals' refs'])
          next
            case False
            with Ref H CoreStmt_VarDecl base obtain addrPath where
              lv: "interp_writable_lvalue d fuel state initTm = Inr addrPath"
              by (auto split: sum.splits)
            obtain addr path where ap: "addrPath = (addr, path)" by (cases addrPath)
            from lv ap have lv': "interp_writable_lvalue d fuel state initTm = Inr (addr, path)"
              by simp
            have addr_in: "addr \<in> frame_addrs state"
              by (rule interp_writable_lvalue_in_frame[OF lv'])
            from Ref H[symmetric] CoreStmt_VarDecl base False lv' have
              store': "IS_Store (result_state res) = IS_Store state" and
              locals': "IS_Locals (result_state res) = fmdrop varName (IS_Locals state)" and
              refs': "IS_Refs (result_state res) = fmupd varName (addr, path) (IS_Refs state)"
              by simp_all
            show ?thesis by (rule frame_step_bind_ref[OF store' locals' refs' addr_in])
          qed
        qed
      next
        case (CoreStmt_VarDeclCall g varName varTy castOpt fnName argTys argTms)
        \<comment> \<open>Run the call (giving newState), apply the cast, then alloc and bind. \<close>
        from H CoreStmt_VarDeclCall obtain newState retVal where
          call: "interp_function_call d fuel state fnName argTys argTms = Inr (newState, retVal)"
          by (auto split: sum.splits prod.splits)
        from IH_call call have cf: "call_frame state fnName argTms newState" by blast
        from H CoreStmt_VarDeclCall call obtain initVal where
          cast: "apply_cast_opt castOpt retVal = Inr initVal"
          by (auto split: sum.splits)
        from H[symmetric] CoreStmt_VarDeclCall call cast have
          store': "IS_Store (result_state res) = IS_Store newState @ [initVal]" and
          locals': "IS_Locals (result_state res)
                      = fmupd varName (length (IS_Store newState)) (IS_Locals newState)" and
          refs': "IS_Refs (result_state res) = fmdrop varName (IS_Refs newState)"
          by (simp_all add: Let_def)
        have "frame_step newState (result_state res)"
          by (rule frame_step_bind_fresh[OF store' locals' refs'])
        with call_frame_frame_step[OF cf] show ?thesis by (rule frame_step_trans)
      next
        case (CoreStmt_Fix _ _) with H show ?thesis by simp
      next
        case (CoreStmt_Obtain varName varTy condTm)
        show ?thesis
        proof (cases d)
          case d_zero: 0
          with H CoreStmt_Obtain show ?thesis by simp
        next
          case d_Suc: (Suc d')
          from H[symmetric] CoreStmt_Obtain d_Suc obtain witness where
            res_eq: "res = Continue (bind_mutable_local varName witness state)"
            by (auto simp del: bind_mutable_local.simps split: sum.splits)
          show ?thesis
            by (simp only: res_eq result_state.simps frame_step_bind_mutable_local)
        qed
      next
        case (CoreStmt_Use _) with H show ?thesis by simp
      next
        case (CoreStmt_Assign g lhsLv rhsTm)
        from H CoreStmt_Assign obtain addr path where
          lv: "interp_writable_lvalue d fuel state lhsLv = Inr (addr, path)"
          by (auto split: sum.splits)
        from H CoreStmt_Assign lv obtain rhsVal where
          rv: "interp_term d fuel state rhsTm = Inr rhsVal"
          by (auto split: sum.splits)
        from H CoreStmt_Assign lv rv obtain newVal where
          upd: "update_value_at_path (IS_Store state ! addr) path rhsVal = Inr newVal"
          by (auto simp: Let_def split: sum.splits)
        from H[symmetric] CoreStmt_Assign lv rv upd have
          store': "IS_Store (result_state res) = (IS_Store state)[addr := newVal]" and
          locals': "IS_Locals (result_state res) = IS_Locals state" and
          refs': "IS_Refs (result_state res) = IS_Refs state"
          by (simp_all add: Let_def)
        have addr_in: "addr \<in> frame_addrs state"
          by (rule interp_writable_lvalue_in_frame[OF lv])
        show ?thesis by (rule frame_step_store_update[OF store' locals' refs' addr_in])
      next
        case (CoreStmt_AssignCall g lhsLv castOpt fnName argTys argTms)
        \<comment> \<open>Resolve lhs, run the call (newState), apply cast, store. \<close>
        from H CoreStmt_AssignCall obtain addr path where
          lv: "interp_writable_lvalue d fuel state lhsLv = Inr (addr, path)"
          by (auto split: sum.splits)
        from H CoreStmt_AssignCall lv obtain newState retVal where
          call: "interp_function_call d fuel state fnName argTys argTms = Inr (newState, retVal)"
          by (auto split: sum.splits prod.splits)
        from IH_call call have cf: "call_frame state fnName argTms newState" by blast
        from H CoreStmt_AssignCall lv call obtain rhsVal where
          cast: "apply_cast_opt castOpt retVal = Inr rhsVal"
          by (auto split: sum.splits)
        from H CoreStmt_AssignCall lv call cast obtain newVal where
          upd: "update_value_at_path (IS_Store newState ! addr) path rhsVal = Inr newVal"
          by (auto simp: Let_def split: sum.splits)
        from H[symmetric] CoreStmt_AssignCall lv call cast upd have
          store': "IS_Store (result_state res) = (IS_Store newState)[addr := newVal]" and
          locals': "IS_Locals (result_state res) = IS_Locals newState" and
          refs': "IS_Refs (result_state res) = IS_Refs newState"
          by (simp_all add: Let_def)
        have "addr \<in> frame_addrs state"
          by (rule interp_writable_lvalue_in_frame[OF lv])
        then have addr_in: "addr \<in> frame_addrs newState"
          using call_frame_frame_addrs[OF cf] by simp
        have "frame_step newState (result_state res)"
          by (rule frame_step_store_update[OF store' locals' refs' addr_in])
        with call_frame_frame_step[OF cf] show ?thesis by (rule frame_step_trans)
      next
        case (CoreStmt_Swap g lhsTm rhsTm)
        from H CoreStmt_Swap obtain lhsLv where
          lhs: "interp_writable_lvalue d fuel state lhsTm = Inr lhsLv"
          by (auto split: sum.splits)
        with H CoreStmt_Swap obtain rhsLv where
          rhs: "interp_writable_lvalue d fuel state rhsTm = Inr rhsLv"
          by (auto split: sum.splits)
        with H CoreStmt_Swap lhs obtain newState where
          sw: "perform_swap state lhsLv rhsLv = Inr newState"
          and res_eq: "res = Continue newState"
          by (auto split: sum.splits)
        obtain addr1 path1 where l_eq: "lhsLv = (addr1, path1)" by (cases lhsLv)
        obtain addr2 path2 where r_eq: "rhsLv = (addr2, path2)" by (cases rhsLv)
        have a1: "addr1 \<in> frame_addrs state"
          by (rule interp_writable_lvalue_in_frame[OF lhs[unfolded l_eq]])
        have a2: "addr2 \<in> frame_addrs state"
          by (rule interp_writable_lvalue_in_frame[OF rhs[unfolded r_eq]])
        have "frame_step state newState"
          by (rule perform_swap_frame[OF sw[unfolded l_eq r_eq] a1 a2])
        with res_eq show ?thesis by simp
      next
        case (CoreStmt_Return tm)
        with H obtain val where
          "interp_term d fuel state tm = Inr val"
          and res_eq: "res = Return state val"
          by (auto split: sum.splits)
        then show ?thesis by (simp add: frame_step_refl)
      next
        case (CoreStmt_Assert condOpt proofBody)
        show ?thesis
        proof (cases condOpt)
          case None
          with H CoreStmt_Assert show ?thesis by simp
        next
          case (Some condTm)
          from H CoreStmt_Assert Some obtain condVal where
            cv: "interp_term d fuel state condTm = Inr condVal"
            by (auto split: sum.splits)
          have "res = Continue state"
          proof (cases condVal)
            case (CV_Bool b)
            with H CoreStmt_Assert Some cv show ?thesis by (cases b) simp_all
          next
            case CV_FiniteInt with H CoreStmt_Assert Some cv show ?thesis by simp
          next
            case CV_Variant with H CoreStmt_Assert Some cv show ?thesis by simp
          next
            case CV_Record with H CoreStmt_Assert Some cv show ?thesis by simp
          next
            case CV_Array with H CoreStmt_Assert Some cv show ?thesis by simp
          next
            case CV_Int with H CoreStmt_Assert Some cv show ?thesis by simp
          next
            case CV_Real with H CoreStmt_Assert Some cv show ?thesis by simp
          qed
          then show ?thesis by (simp add: frame_step_refl)
        qed
      next
        case (CoreStmt_Assume _) with H
        have "res = Continue state" by simp
        then show ?thesis by (simp add: frame_step_refl)
      next
        case (CoreStmt_While g condTm invars decr bodyStmts)
        \<comment> \<open>The run succeeded, so the invariants were evaluated and all held. \<close>
        from H CoreStmt_While obtain invarVals where
          iv: "interp_term_list d fuel state invars = Inr invarVals" and
          ie: "invariants_error invarVals = None"
          by (auto split: sum.splits option.splits)
        note [simp] = iv ie
        from H CoreStmt_While obtain condVal where
          cv: "interp_term d fuel state condTm = Inr condVal"
          by (auto split: sum.splits)
        show ?thesis
        proof (cases condVal)
          case (CV_Bool b)
          show ?thesis
          proof (cases b)
            case False
            with CoreStmt_While H cv CV_Bool
            have "res = Continue state" by simp
            then show ?thesis by (simp add: frame_step_refl)
          next
            case True
            \<comment> \<open>The decreases-term (if any) was evaluated before the body. \<close>
            with CoreStmt_While H cv CV_Bool
            obtain decrVal where
              dv: "eval_decreases (interp_term d fuel state) decr = Inr decrVal"
              by (auto split: sum.splits)
            note [simp] = dv
            from CoreStmt_While H cv CV_Bool True
            obtain bodyRes where
              body: "interp_statement_list d fuel state bodyStmts = Inr bodyRes"
              by (auto split: sum.splits)
            from IH_stmt_list body
            have body_fs: "frame_step state (result_state bodyRes)" by blast
            show ?thesis
            proof (cases bodyRes)
              case (Continue state1)
              let ?rs = "restore_scope state state1"
              from body_fs Continue have fs1: "frame_step state state1" by simp
              have fs_rs: "frame_step state ?rs"
                by (rule frame_step_restore_scope[OF fs1])
              \<comment> \<open>The decreases-term was evaluated again after the body, and the
                  check passed. \<close>
              from CoreStmt_While H cv CV_Bool True body Continue
              obtain decrVal' where
                dv': "eval_decreases (interp_term d fuel ?rs) decr = Inr decrVal'" and
                de: "decreases_error decrVal decrVal' = None"
                by (auto split: sum.splits option.splits)
              from CoreStmt_While H cv CV_Bool True body Continue dv' de
              have rec_eq: "interp_statement d fuel ?rs
                               (CoreStmt_While g condTm invars decr bodyStmts) = Inr res"
                by simp
              from IH_stmt rec_eq
              have "frame_step ?rs (result_state res)" by blast
              with fs_rs show ?thesis by (rule frame_step_trans)
            next
              case (Return state1 v)
              from body_fs Return have fs1: "frame_step state state1" by simp
              from CoreStmt_While H cv CV_Bool True body Return
              have res_eq: "res = Return (restore_scope state state1) v"
                by simp
              show ?thesis
                by (simp only: res_eq result_state.simps frame_step_restore_scope[OF fs1])
            qed
          qed
        next
          \<comment> \<open>Non-bool cond value: TypeError, contradicts H. \<close>
          case CV_FiniteInt with CoreStmt_While H cv show ?thesis by simp
        next
          case CV_Variant with CoreStmt_While H cv show ?thesis by simp
        next
          case CV_Record with CoreStmt_While H cv show ?thesis by simp
        next
          case CV_Array with CoreStmt_While H cv show ?thesis by simp
        next
          case CV_Int with CoreStmt_While H cv show ?thesis by simp
        next
          case CV_Real with CoreStmt_While H cv show ?thesis by simp
        qed
      next
        case (CoreStmt_Match g scrutTm arms)
        from H CoreStmt_Match obtain scrutVal where
          sv: "interp_term d fuel state scrutTm = Inr scrutVal"
          by (auto split: sum.splits)
        from H CoreStmt_Match sv obtain armStmts where
          arm: "find_matching_arm scrutVal arms = Inr armStmts"
          by (auto split: sum.splits)
        from H CoreStmt_Match sv arm obtain bodyRes where
          body: "interp_statement_list d fuel state armStmts = Inr bodyRes"
          by (auto split: sum.splits)
        from IH_stmt_list body
        have body_fs: "frame_step state (result_state bodyRes)" by blast
        show ?thesis
        proof (cases bodyRes)
          case (Continue state1)
          from body_fs Continue have fs1: "frame_step state state1" by simp
          from CoreStmt_Match H sv arm body Continue
          have res_eq: "res = Continue (restore_scope state state1)" by simp
          show ?thesis
            by (simp only: res_eq result_state.simps frame_step_restore_scope[OF fs1])
        next
          case (Return state1 v)
          from body_fs Return have fs1: "frame_step state state1" by simp
          from CoreStmt_Match H sv arm body Return
          have res_eq: "res = Return (restore_scope state state1) v" by simp
          show ?thesis
            by (simp only: res_eq result_state.simps frame_step_restore_scope[OF fs1])
        qed
      next
        case (CoreStmt_ShowHide _ _) with H
        have "res = Continue state" by simp
        then show ?thesis by (simp add: frame_step_refl)
      next
        case (CoreStmt_Block body)
        from H CoreStmt_Block obtain bodyRes where
          body: "interp_statement_list d fuel state body = Inr bodyRes"
          by (auto split: sum.splits)
        from IH_stmt_list body
        have body_fs: "frame_step state (result_state bodyRes)" by blast
        show ?thesis
        proof (cases bodyRes)
          case (Continue state1)
          from body_fs Continue have fs1: "frame_step state state1" by simp
          from CoreStmt_Block H body Continue
          have res_eq: "res = Continue (restore_scope state state1)" by simp
          show ?thesis
            by (simp only: res_eq result_state.simps frame_step_restore_scope[OF fs1])
        next
          case (Return state1 v)
          from body_fs Return have fs1: "frame_step state state1" by simp
          from CoreStmt_Block H body Return
          have res_eq: "res = Return (restore_scope state state1) v" by simp
          show ?thesis
            by (simp only: res_eq result_state.simps frame_step_restore_scope[OF fs1])
        qed
      qed
    qed
  next
    case (2 stmts) show ?case
    proof (intro allI impI)
      fix state :: "'w InterpState" and res :: "'w ExecResult"
      assume H: "interp_statement_list d (Suc fuel) state stmts = Inr res"
      show "frame_step state (result_state res)"
      proof (cases stmts)
        case Nil
        with H have "res = Continue state" by simp
        then show ?thesis by (simp add: frame_step_refl)
      next
        case (Cons stmt1 rest)
        with H obtain res1 where
          r1: "interp_statement d fuel state stmt1 = Inr res1"
          by (auto split: sum.splits)
        from IH_stmt r1 have fs1: "frame_step state (result_state res1)" by blast
        show ?thesis
        proof (cases res1)
          case (Continue state1)
          from fs1 Continue have step1: "frame_step state state1" by simp
          from Cons H r1 Continue
          have rec: "interp_statement_list d fuel state1 rest = Inr res" by simp
          from IH_stmt_list rec have step2: "frame_step state1 (result_state res)" by blast
          from step1 step2 show ?thesis by (rule frame_step_trans)
        next
          case (Return state1 v)
          from Cons H r1 Return have "res = Return state1 v" by simp
          with fs1 Return show ?thesis by simp
        qed
      qed
    qed
  next
    case (3 fnName argTys argTms) show ?case
    proof (intro allI impI)
      fix state :: "'w InterpState" and state' :: "'w InterpState" and retVal
      assume H: "interp_function_call d (Suc fuel) state fnName argTys argTms = Inr (state', retVal)"
      \<comment> \<open>Unfold the function-call body enough to name each intermediate state. \<close>
      obtain f where f_lookup: "fmlookup (IS_Functions state) fnName = Some f"
        using H by (cases "fmlookup (IS_Functions state) fnName") simp_all
      from H f_lookup have len_eq: "length argTms = length (IF_Args f)"
        by (cases "length argTms = length (IF_Args f)") simp_all
      from H f_lookup len_eq have tyLen_eq: "length argTys = length (IF_TyArgs f)"
        by (cases "length argTys = length (IF_TyArgs f)") simp_all
      let ?refResults = "map (interp_writable_lvalue d fuel state) argTms"
      let ?valResults = "map (interp_term d fuel state) argTms"
      let ?argTuples = "zip (IF_Args f) (zip ?refResults ?valResults)"
      let ?calleeTyArgs = "fmap_of_list (zip (IF_TyArgs f) (map (apply_subst (IS_TyArgs state)) argTys))"
      let ?clearedState = "state \<lparr> IS_Locals := fmempty, IS_Refs := fmempty,
                                     IS_ConstLocals := {||},
                                     IS_TyArgs := ?calleeTyArgs \<rparr>"
      obtain preCallState where
        fold_eq: "fold process_one_arg ?argTuples (Inr ?clearedState) = Inr preCallState"
        using H f_lookup len_eq tyLen_eq
        by (cases "fold process_one_arg ?argTuples (Inr ?clearedState)") (simp_all add: Let_def)

      \<comment> \<open>The callee's frame refers only to the Ref-argument addresses and to
          the cells freshly allocated for its Var parameters. \<close>
      note fold_frame = fold_process_one_arg_frame[OF fold_eq]
      have cleared_addrs: "frame_addrs ?clearedState = {}"
        by (simp add: frame_addrs_def)
      from fold_frame obtain extra where
        pre_store: "IS_Store preCallState = IS_Store state @ extra"
        by auto
      have len1: "length (IS_Store state) \<le> length (IS_Store preCallState)"
        using pre_store by simp
      have pre_addrs: "a \<in> ref_arg_addrs ?argTuples \<or>
                       (length (IS_Store state) \<le> a \<and> a < length (IS_Store preCallState))"
        if "a \<in> frame_addrs preCallState" for a
        using fold_frame cleared_addrs that by auto
      have ref_in: "a \<in> call_ref_addrs state fnName argTms"
        if "a \<in> ref_arg_addrs ?argTuples" for a
      proof -
        from ref_arg_addrs_zip[OF that] obtain i path where
          i: "i < length (IF_Args f)" "i < length ?refResults"
             "snd (IF_Args f ! i) = Ref" "?refResults ! i = Inr (a, path)"
          by blast
        from i(2) have i_lt: "i < length argTms" by simp
        show ?thesis
          by (rule ref_result_in_call_ref_addrs[OF f_lookup i(1) i_lt i(3) i(4)])
      qed

      show "call_frame state fnName argTms state'"
      proof (cases "IF_Body f")
        case (Inl bodyStmts)
        \<comment> \<open>Babylon body. \<close>
        from H f_lookup len_eq tyLen_eq fold_eq Inl
        obtain bodyRes where bodyEval:
          "interp_statement_list d fuel preCallState bodyStmts = Inr bodyRes"
          by (cases "interp_statement_list d fuel preCallState bodyStmts")
             (simp_all add: Let_def)
        show ?thesis
        proof (cases bodyRes)
          case (Continue _)
          with H f_lookup len_eq tyLen_eq fold_eq Inl bodyEval show ?thesis
            by (simp add: Let_def)
        next
          case (Return postCallState bodyRetVal)
          from IH_stmt_list bodyEval
          have "frame_step preCallState (result_state bodyRes)" by blast
          with Return have body_fs: "frame_step preCallState postCallState" by simp
          from H f_lookup len_eq tyLen_eq fold_eq Inl bodyEval Return
          have state'_eq: "state' = restore_scope state postCallState"
            by (simp add: Let_def)
          have len2: "length (IS_Store preCallState) \<le> length (IS_Store postCallState)"
            by (rule frame_stepD(1)[OF body_fs])
          have len: "length (IS_Store state) \<le> length (IS_Store postCallState)"
            using len1 len2 by simp
          show ?thesis
            unfolding call_frame_def
          proof (intro conjI allI impI)
            show "IS_Locals state' = IS_Locals state" using state'_eq by simp
            show "IS_Refs state' = IS_Refs state" using state'_eq by simp
            show "IS_ConstLocals state' = IS_ConstLocals state" using state'_eq by simp
            show "IS_TyArgs state' = IS_TyArgs state" using state'_eq by simp
            show "length (IS_Store state') = length (IS_Store state)"
              using state'_eq len by simp
          next
            fix a assume lt: "a < length (IS_Store state)"
              and notin: "a \<notin> call_ref_addrs state fnName argTms"
            \<comment> \<open>The cell is below the callee's fresh cells and is not a
                Ref-argument address, so the callee's frame does not refer to it. \<close>
            have lt_pre: "a < length (IS_Store preCallState)" using lt len1 by simp
            have notin_pre: "a \<notin> frame_addrs preCallState"
            proof
              assume "a \<in> frame_addrs preCallState"
              from pre_addrs[OF this] lt have "a \<in> ref_arg_addrs ?argTuples" by auto
              from ref_in[OF this] notin show False by simp
            qed
            from frame_stepD(2)[OF body_fs lt_pre notin_pre]
            have "IS_Store postCallState ! a = IS_Store preCallState ! a" .
            also have "IS_Store preCallState ! a = IS_Store state ! a"
              using pre_store lt by (simp add: nth_append)
            finally have "IS_Store postCallState ! a = IS_Store state ! a" .
            then show "IS_Store state' ! a = IS_Store state ! a"
              using state'_eq lt by simp
          qed
        qed
      next
        case (Inr externFun)
        \<comment> \<open>Extern function. \<close>
        let ?vals = "rights ?valResults"
        let ?refs = "rights (map (\<lambda>((_, vr), refResult).
                                      if vr = Ref then refResult else Inl TypeError)
                                 (zip (IF_Args f) ?refResults))"
        obtain newWorld refUpdates externRetVal where
          ext_eq: "externFun (IS_World state) ?vals = (newWorld, refUpdates, externRetVal)"
          by (cases "externFun (IS_World state) ?vals") auto
        let ?stateW = "state \<lparr> IS_World := newWorld \<rparr>"
        from H f_lookup len_eq tyLen_eq fold_eq Inr ext_eq
        obtain finalState where final_eq:
          "apply_ref_updates ?stateW ?refs refUpdates = Inr finalState"
          and state'_eq: "state' = finalState" and "retVal = externRetVal"
          by (cases "apply_ref_updates ?stateW ?refs refUpdates") (simp_all add: Let_def)
        note upd = apply_ref_updates_frame[OF final_eq]
        show ?thesis
          unfolding call_frame_def
        proof (intro conjI allI impI)
          show "IS_Locals state' = IS_Locals state" using upd state'_eq by simp
          show "IS_Refs state' = IS_Refs state" using upd state'_eq by simp
          show "IS_ConstLocals state' = IS_ConstLocals state" using upd state'_eq by simp
          show "IS_TyArgs state' = IS_TyArgs state" using upd state'_eq by simp
          show "length (IS_Store state') = length (IS_Store state)"
            using upd state'_eq by simp
        next
          fix a assume lt: "a < length (IS_Store state)"
            and notin: "a \<notin> call_ref_addrs state fnName argTms"
          have notin_refs: "a \<notin> fst ` set ?refs"
          proof
            assume "a \<in> fst ` set ?refs"
            then obtain path where "(a, path) \<in> set ?refs" by auto
            from extern_refs_addrs[OF this] obtain i where
              i: "i < length (IF_Args f)" "i < length ?refResults"
                 "snd (IF_Args f ! i) = Ref" "?refResults ! i = Inr (a, path)"
              by blast
            from i(2) have i_lt: "i < length argTms" by simp
            from ref_result_in_call_ref_addrs[OF f_lookup i(1) i_lt i(3) i(4)] notin
            show False by simp
          qed
          from upd have "\<forall>a. a \<notin> fst ` set ?refs
                              \<longrightarrow> IS_Store finalState ! a = IS_Store ?stateW ! a"
            by blast
          with notin_refs have "IS_Store finalState ! a = IS_Store ?stateW ! a" by blast
          then show "IS_Store state' ! a = IS_Store state ! a"
            using state'_eq by simp
        qed
      qed
    qed
  }
qed


(* ========================================================================== *)
(* Corollaries, in the form that callers use *)
(* ========================================================================== *)

theorem interp_statement_frame:
  assumes "interp_statement d fuel state stmt = Inr res"
  shows "frame_step state (result_state res)"
  by (rule interp_frame(1)[rule_format, OF assms])

theorem interp_statement_list_frame:
  assumes "interp_statement_list d fuel state stmts = Inr res"
  shows "frame_step state (result_state res)"
  by (rule interp_frame(2)[rule_format, OF assms])

(* The frame lemma for calls: the caller gets its frame back unchanged, the
   store keeps its length, and a cell can only have changed if it was passed
   as a Ref argument. *)
theorem interp_function_call_frame:
  assumes "interp_function_call d fuel state fnName argTys argTms = Inr (state', retVal)"
  shows "IS_Locals state' = IS_Locals state"
    and "IS_Refs state' = IS_Refs state"
    and "IS_ConstLocals state' = IS_ConstLocals state"
    and "IS_TyArgs state' = IS_TyArgs state"
    and "length (IS_Store state') = length (IS_Store state)"
    and "\<And>a. a < length (IS_Store state) \<Longrightarrow> a \<notin> call_ref_addrs state fnName argTms
              \<Longrightarrow> IS_Store state' ! a = IS_Store state ! a"
proof -
  have cf: "call_frame state fnName argTms state'"
    by (rule interp_frame(3)[rule_format, OF assms])
  show "IS_Locals state' = IS_Locals state" using cf by (simp add: call_frame_def)
  show "IS_Refs state' = IS_Refs state" using cf by (simp add: call_frame_def)
  show "IS_ConstLocals state' = IS_ConstLocals state" using cf by (simp add: call_frame_def)
  show "IS_TyArgs state' = IS_TyArgs state" using cf by (simp add: call_frame_def)
  show "length (IS_Store state') = length (IS_Store state)"
    using cf by (simp add: call_frame_def)
  show "\<And>a. a < length (IS_Store state) \<Longrightarrow> a \<notin> call_ref_addrs state fnName argTms
            \<Longrightarrow> IS_Store state' ! a = IS_Store state ! a"
    using cf by (auto simp: call_frame_def)
qed

corollary interp_function_call_frame_step:
  assumes "interp_function_call d fuel state fnName argTys argTms = Inr (state', retVal)"
  shows "frame_step state state'"
  by (rule call_frame_frame_step[OF interp_frame(3)[rule_format, OF assms]])

(* "Every address the frame refers to is inside the store" is preserved by
   statements and by calls. *)

corollary interp_statement_addrs_in_bounds:
  assumes "interp_statement d fuel state stmt = Inr res"
    and "addrs_in_bounds state"
  shows "addrs_in_bounds (result_state res)"
  by (rule frame_step_addrs_in_bounds[OF interp_statement_frame[OF assms(1)] assms(2)])

corollary interp_statement_list_addrs_in_bounds:
  assumes "interp_statement_list d fuel state stmts = Inr res"
    and "addrs_in_bounds state"
  shows "addrs_in_bounds (result_state res)"
  by (rule frame_step_addrs_in_bounds[OF interp_statement_list_frame[OF assms(1)] assms(2)])

corollary interp_function_call_addrs_in_bounds:
  assumes "interp_function_call d fuel state fnName argTys argTms = Inr (state', retVal)"
    and "addrs_in_bounds state"
  shows "addrs_in_bounds state'"
  by (rule frame_step_addrs_in_bounds[OF interp_function_call_frame_step[OF assms(1)] assms(2)])

end
