theory EraseGhostStmtTyping
  imports EraseGhostTyping "../core/CoreStmtTypecheck"
begin

(* Typing after ghost erasure: statements.

   A statement list typed in NotGhost mode in env is, after erasure, typed in
   NotGhost mode in any envE with tyenv_erased env envE; and the two result
   environments are again related by tyenv_erased. *)


(* ========================================================================== *)
(* More about the relation between the two environments *)
(* ========================================================================== *)

(* The relation does not read TE_ProofTopLevel. *)
lemma tyenv_erased_TE_ProofTopLevel [simp]:
  "tyenv_erased (env \<lparr> TE_ProofTopLevel := a \<rparr>) (envE \<lparr> TE_ProofTopLevel := b \<rparr>)
     = tyenv_erased env envE"
proof -
  have d: "tyenv_decls_erased (env \<lparr> TE_ProofTopLevel := a \<rparr>) (envE \<lparr> TE_ProofTopLevel := b \<rparr>)
             = tyenv_decls_erased env envE"
    by (rule tyenv_decls_erased_cong) simp_all
  show ?thesis
    unfolding tyenv_erased_def d by (simp add: tyenv_var_ghost_def)
qed

(* Binding a new ghost local, on the left side only. This is what a deleted
   ghost declaration does. *)
lemma tyenv_erased_add_ghost_var:
  assumes rel: "tyenv_erased env envE"
    and others: "\<And>name. name \<noteq> varName \<Longrightarrow>
                   (name |\<in>| cs \<longleftrightarrow> name |\<in>| TE_ConstLocals env)"
  shows "tyenv_erased
           (env \<lparr> TE_LocalVars := fmupd varName ty (TE_LocalVars env),
                  TE_GhostLocals := finsert varName (TE_GhostLocals env),
                  TE_ConstLocals := cs \<rparr>)
           envE"
    (is "tyenv_erased ?env' envE")
proof -
  have d: "tyenv_decls_erased ?env' envE = tyenv_decls_erased env envE"
    by (rule tyenv_decls_erased_cong) simp_all
  have decls: "tyenv_decls_erased ?env' envE"
    unfolding d by (rule tyenv_erased_decls[OF rel])
  have ret: "TE_ReturnType envE = TE_ReturnType ?env'"
    and fg: "TE_FunctionGhost envE = TE_FunctionGhost ?env'"
    and gl: "TE_GhostLocals envE = {||}"
    using rel unfolding tyenv_erased_def by simp_all
  have locals: "fmlookup (TE_LocalVars envE) name = fmlookup (TE_LocalVars ?env') name
                \<and> (name |\<in>| TE_ConstLocals envE \<longleftrightarrow> name |\<in>| TE_ConstLocals ?env')"
    if ng: "\<not> tyenv_var_ghost ?env' name" for name
  proof -
    have ne: "name \<noteq> varName"
      using ng unfolding tyenv_var_ghost_def by auto
    have ng0: "\<not> tyenv_var_ghost env name"
      using ng ne unfolding tyenv_var_ghost_def by simp
    show ?thesis
      using ne others[OF ne]
            tyenv_erased_local_lookup[OF rel ng0] tyenv_erased_const_local[OF rel ng0]
      by simp
  qed
  show ?thesis
    unfolding tyenv_erased_def using decls ret fg gl locals by blast
qed

lemma tyenv_erased_var_writable:
  assumes rel: "tyenv_erased env envE" and ng: "\<not> tyenv_var_ghost env name"
  shows "tyenv_var_writable envE name = tyenv_var_writable env name"
  unfolding tyenv_var_writable_def
  using tyenv_erased_local_lookup[OF rel ng] tyenv_erased_const_local[OF rel ng]
  by simp


(* ========================================================================== *)
(* Lvalues, casts and impure calls *)
(* ========================================================================== *)

(* A term typed in NotGhost mode is a writable lvalue in envE exactly when it is
   one in env: its base variable is not ghost. *)
lemma is_writable_lvalue_erased:
  assumes rel: "tyenv_erased env envE"
  shows "core_term_type env NotGhost tm = Some ty
           \<Longrightarrow> is_writable_lvalue envE tm = is_writable_lvalue env tm"
proof (induction tm arbitrary: ty)
  case (CoreTm_Var name)
  from CoreTm_Var.prems have ng: "\<not> tyenv_var_ghost env name"
    by (auto split: option.splits if_splits)
  show ?case by (simp add: tyenv_erased_var_writable[OF rel ng])
next
  case (CoreTm_Cast targetTy operand)
  from CoreTm_Cast.prems obtain operandTy where
      "core_term_type env NotGhost operand = Some operandTy"
    by (auto split: option.splits)
  from CoreTm_Cast.IH[OF this] show ?case by simp
next
  case (CoreTm_RecordProj tm fldName)
  from CoreTm_RecordProj.prems obtain t where
      "core_term_type env NotGhost tm = Some t"
    by (auto split: option.splits)
  from CoreTm_RecordProj.IH[OF this] show ?case by simp
next
  case (CoreTm_ArrayProj arr idxTms)
  from CoreTm_ArrayProj.prems obtain t where
      "core_term_type env NotGhost arr = Some t"
    by (auto split: option.splits)
  from CoreTm_ArrayProj.IH(1)[OF this] show ?case by simp
next
  case (CoreTm_VariantProj tm ctorName)
  from CoreTm_VariantProj.prems obtain t where
      "core_term_type env NotGhost tm = Some t"
    by (auto split: option.splits)
  from CoreTm_VariantProj.IH[OF this] show ?case by simp
qed simp_all

lemma cast_result_type_erased:
  assumes rel: "tyenv_erased env envE"
    and c: "cast_result_type env NotGhost retTy castOpt = Some ty"
  shows "cast_result_type envE NotGhost retTy castOpt = Some ty"
proof (cases castOpt)
  case None
  then show ?thesis using c by (simp add: cast_result_type_def)
next
  case (Some t)
  from c Some have
      co: "cast_ok env retTy t" and
      rt: "is_runtime_type env t" and
      ty_eq: "ty = t"
    by (auto simp: cast_result_type_def split: if_splits)
  have wk: "is_well_kinded env t" by (rule cast_ok_well_kinded[OF co])
  note tt = tyenv_erased_runtime_type[OF rel wk rt]
  have coE: "cast_ok envE retTy t"
    using co tt unfolding cast_ok_def by blast
  show ?thesis using Some coE tt ty_eq by (simp add: cast_result_type_def)
qed

lemma core_impure_call_type_erased:
  assumes rel: "tyenv_erased env envE" and wf: "tyenv_well_formed env"
    and ct: "core_impure_call_type env NotGhost fnName tyArgs tmArgs = Some ty"
  shows "core_impure_call_type envE NotGhost fnName tyArgs tmArgs = Some ty"
proof -
  from ct obtain funInfo where
      fn: "fmlookup (TE_Functions env) fnName = Some funInfo"
    by (auto simp: core_impure_call_type_def split: option.splits)
  let ?sub = "fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)"
  let ?expected = "map (\<lambda>(ty, _). apply_subst ?sub ty) (FI_TmArgs funInfo)"
  let ?vors = "map (\<lambda>(_, vor, _). vor) (FI_TmArgs funInfo)"
  let ?ok = "\<lambda>e. (\<lambda>(tm, vor) expectedTy.
               case vor of
                 Var \<Rightarrow>
                   (case core_term_type e NotGhost tm of
                      None \<Rightarrow> False
                    | Some actualTy \<Rightarrow> actualTy = expectedTy)
               | Ref \<Rightarrow>
                   is_writable_lvalue e tm
                   \<and> ghost_lvalue_ok e NotGhost tm
                   \<and> core_term_type e NotGhost tm = Some expectedTy)"
  from ct fn have
      len_ty: "length tyArgs = length (FI_TyArgs funInfo)" and
      wks: "list_all (is_well_kinded env) tyArgs" and
      cps: "list_all is_complete_type tyArgs" and
      rts: "list_all (is_runtime_type env) tyArgs" and
      ng: "FI_Ghost funInfo \<noteq> Ghost" and
      len_tm: "length tmArgs = length (FI_TmArgs funInfo)" and
      args: "list_all2 (?ok env) (zip tmArgs ?vors) ?expected" and
      ty_eq: "ty = apply_subst ?sub (FI_ReturnType funInfo)"
    by (auto simp: core_impure_call_type_def Let_def split: if_splits)
  have ngN: "FI_Ghost funInfo = NotGhost"
    using ng by (cases "FI_Ghost funInfo") simp_all
  have fnE: "fmlookup (TE_Functions envE) fnName = Some funInfo"
    by (rule tyenv_erased_fun_lookup[OF rel fn ngN])
  note tysE = tyenv_erased_runtime_type_list[OF rel wks rts]
  have argsE: "list_all2 (?ok envE) (zip tmArgs ?vors) ?expected"
    using args
  proof (rule list.rel_mono_strong)
    fix p ety
    assume h: "?ok env p ety"
    obtain tm vor where p: "p = (tm, vor)" by (cases p)
    show "?ok envE p ety"
    proof (cases vor)
      case Var
      from h p Var have "core_term_type env NotGhost tm = Some ety"
        by (simp split: option.splits)
      hence "core_term_type envE NotGhost tm = Some ety"
        by (rule core_term_type_erased[OF _ wf rel])
      thus ?thesis using p Var by simp
    next
      case Ref
      from h p Ref have
          w: "is_writable_lvalue env tm" and
          t: "core_term_type env NotGhost tm = Some ety"
        by simp_all
      have tE: "core_term_type envE NotGhost tm = Some ety"
        by (rule core_term_type_erased[OF t wf rel])
      have wE: "is_writable_lvalue envE tm"
        using is_writable_lvalue_erased[OF rel t] w by simp
      show ?thesis using p Ref tE wE by simp
    qed
  qed
  show ?thesis
    using fnE len_ty tysE cps ngN len_tm argsE ty_eq
    by (simp add: core_impure_call_type_def Let_def)
qed


(* ========================================================================== *)
(* Statement lists *)
(* ========================================================================== *)

lemma core_statement_list_type_append:
  "core_statement_list_type env ghost (stmts1 @ stmts2)
     = (case core_statement_list_type env ghost stmts1 of
          None \<Rightarrow> None
        | Some env1 \<Rightarrow> core_statement_list_type env1 ghost stmts2)"
  by (induction stmts1 arbitrary: env) (simp_all split: option.splits)

(* The two ways a single statement is erased: to nothing, or to one statement. *)

lemma erased_typed_none:
  assumes "tyenv_erased env' envE"
  shows "\<exists>envE'. core_statement_list_type envE NotGhost [] = Some envE'
                 \<and> tyenv_erased env' envE'"
  using assms by simp

lemma erased_typed_single:
  assumes "core_statement_type envE NotGhost stmtE = Some envE'"
    and "tyenv_erased env' envE'"
  shows "\<exists>envE'. core_statement_list_type envE NotGhost [stmtE] = Some envE'
                 \<and> tyenv_erased env' envE'"
  using assms by simp

(* A statement list, given the result for each of its statements. *)
lemma erase_ghost_statement_list_typed_aux:
  "core_statement_list_type env NotGhost stmts = Some env'
     \<Longrightarrow> tyenv_well_formed env
     \<Longrightarrow> tyenv_erased env envE
     \<Longrightarrow> (\<And>stmt env envE env'.
            stmt \<in> set stmts
            \<Longrightarrow> core_statement_type env NotGhost stmt = Some env'
            \<Longrightarrow> tyenv_well_formed env
            \<Longrightarrow> tyenv_erased env envE
            \<Longrightarrow> \<exists>envE'. core_statement_list_type envE NotGhost (erase_ghost_statement stmt)
                            = Some envE'
                         \<and> tyenv_erased env' envE')
     \<Longrightarrow> \<exists>envE'. core_statement_list_type envE NotGhost
                     (erase_ghost_statement_list stmts) = Some envE'
                  \<and> tyenv_erased env' envE'"
proof (induction stmts arbitrary: env envE)
  case Nil
  then show ?case by simp
next
  case (Cons stmt stmts)
  from Cons.prems(1) obtain envMid where
      head: "core_statement_type env NotGhost stmt = Some envMid" and
      tail: "core_statement_list_type envMid NotGhost stmts = Some env'"
    by (auto split: option.splits)
  have sin: "stmt \<in> set (stmt # stmts)" by simp
  from Cons.prems(4)[OF sin head Cons.prems(2) Cons.prems(3)] obtain envEMid where
      headE: "core_statement_list_type envE NotGhost (erase_ghost_statement stmt)
                = Some envEMid" and
      relMid: "tyenv_erased envMid envEMid"
    by blast
  have wfMid: "tyenv_well_formed envMid"
    by (rule core_statement_type_preserves_well_formed[OF head Cons.prems(2)])
  have each': "\<And>s env envE env'.
        s \<in> set stmts
        \<Longrightarrow> core_statement_type env NotGhost s = Some env'
        \<Longrightarrow> tyenv_well_formed env
        \<Longrightarrow> tyenv_erased env envE
        \<Longrightarrow> \<exists>envE'. core_statement_list_type envE NotGhost (erase_ghost_statement s)
                        = Some envE'
                     \<and> tyenv_erased env' envE'"
  proof -
    fix s env envE env'
    assume s_in: "s \<in> set stmts"
      and t: "core_statement_type env NotGhost s = Some env'"
      and w: "tyenv_well_formed env"
      and r: "tyenv_erased env envE"
    have s_in': "s \<in> set (stmt # stmts)" using s_in by simp
    show "\<exists>envE'. core_statement_list_type envE NotGhost (erase_ghost_statement s)
                    = Some envE'
                  \<and> tyenv_erased env' envE'"
      by (rule Cons.prems(4)[OF s_in' t w r])
  qed
  from Cons.IH[OF tail wfMid relMid each'] obtain envE' where
      tailE: "core_statement_list_type envEMid NotGhost (erase_ghost_statement_list stmts)
                = Some envE'" and
      rel': "tyenv_erased env' envE'"
    by fastforce
  have "core_statement_list_type envE NotGhost
          (erase_ghost_statement stmt @ erase_ghost_statement_list stmts) = Some envE'"
    by (simp add: core_statement_list_type_append headE tailE)
  thus ?case using rel' by auto
qed


(* ========================================================================== *)
(* Statements *)
(* ========================================================================== *)

lemma erase_ghost_statement_typed:
  "core_statement_type env NotGhost stmt = Some env'
     \<Longrightarrow> tyenv_well_formed env
     \<Longrightarrow> tyenv_erased env envE
     \<Longrightarrow> \<exists>envE'. core_statement_list_type envE NotGhost (erase_ghost_statement stmt)
                     = Some envE'
                  \<and> tyenv_erased env' envE'"
proof (induction stmt arbitrary: env envE env')
  case (CoreStmt_VarDecl declGhost varName vr varTy initTm)
  note T = CoreStmt_VarDecl.prems(1) and wf = CoreStmt_VarDecl.prems(2)
    and rel = CoreStmt_VarDecl.prems(3)
  show ?case
  proof (cases declGhost)
    case Ghost
    have "tyenv_erased env' envE"
    proof (cases vr)
      case Var
      from T Ghost Var have e:
        "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                      TE_GhostLocals := finsert varName (TE_GhostLocals env),
                      TE_ConstLocals := TE_ConstLocals env |-| {|varName|} \<rparr>"
        by (auto split: if_splits)
      show ?thesis unfolding e by (rule tyenv_erased_add_ghost_var[OF rel]) simp
    next
      case Ref
      from T Ghost Ref have e:
        "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                      TE_GhostLocals := finsert varName (TE_GhostLocals env),
                      TE_ConstLocals := (if is_writable_lvalue env initTm
                                         then TE_ConstLocals env |-| {|varName|}
                                         else finsert varName (TE_ConstLocals env)) \<rparr>"
        by (auto split: if_splits)
      show ?thesis unfolding e by (rule tyenv_erased_add_ghost_var[OF rel]) simp
    qed
    hence "\<exists>envE'. core_statement_list_type envE NotGhost [] = Some envE'
                   \<and> tyenv_erased env' envE'"
      by (rule erased_typed_none)
    thus ?thesis using Ghost by simp
  next
    case NotGhost
    show ?thesis
    proof (cases vr)
      case Var
      from T NotGhost Var have
          wk: "is_well_kinded env varTy" and
          rt: "is_runtime_type env varTy" and
          cp: "is_complete_type varTy" and
          it: "core_term_type env NotGhost initTm = Some varTy" and
          e: "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                           TE_GhostLocals := TE_GhostLocals env |-| {|varName|},
                           TE_ConstLocals := TE_ConstLocals env |-| {|varName|} \<rparr>"
        by (auto split: if_splits)
      note tt = tyenv_erased_runtime_type[OF rel wk rt]
      have itE: "core_term_type envE NotGhost initTm = Some varTy"
        by (rule core_term_type_erased[OF it wf rel])
      have sE: "core_statement_type envE NotGhost
                  (CoreStmt_VarDecl NotGhost varName Var varTy initTm)
                = Some (envE \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars envE),
                                TE_GhostLocals := TE_GhostLocals envE |-| {|varName|},
                                TE_ConstLocals := TE_ConstLocals envE |-| {|varName|} \<rparr>)"
        using tt cp itE by simp
      have relE: "tyenv_erased env'
                    (envE \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars envE),
                            TE_GhostLocals := TE_GhostLocals envE |-| {|varName|},
                            TE_ConstLocals := TE_ConstLocals envE |-| {|varName|} \<rparr>)"
        unfolding e by (rule tyenv_erased_add_var[OF rel]) simp_all
      from erased_typed_single[OF sE relE] show ?thesis using NotGhost Var by simp
    next
      case Ref
      from T NotGhost Ref have
          wk: "is_well_kinded env varTy" and
          rt: "is_runtime_type env varTy" and
          lv: "is_lvalue initTm" and
          it: "core_term_type env NotGhost initTm = Some varTy" and
          e: "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                           TE_GhostLocals := TE_GhostLocals env |-| {|varName|},
                           TE_ConstLocals := (if is_writable_lvalue env initTm
                                              then TE_ConstLocals env |-| {|varName|}
                                              else finsert varName (TE_ConstLocals env)) \<rparr>"
        by (auto split: if_splits)
      note tt = tyenv_erased_runtime_type[OF rel wk rt]
      have itE: "core_term_type envE NotGhost initTm = Some varTy"
        by (rule core_term_type_erased[OF it wf rel])
      have wE: "is_writable_lvalue envE initTm = is_writable_lvalue env initTm"
        by (rule is_writable_lvalue_erased[OF rel it])
      have sE: "core_statement_type envE NotGhost
                  (CoreStmt_VarDecl NotGhost varName Ref varTy initTm)
                = Some (envE \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars envE),
                                TE_GhostLocals := TE_GhostLocals envE |-| {|varName|},
                                TE_ConstLocals :=
                                  (if is_writable_lvalue env initTm
                                   then TE_ConstLocals envE |-| {|varName|}
                                   else finsert varName (TE_ConstLocals envE)) \<rparr>)"
        using tt lv itE wE by simp
      have relE: "tyenv_erased env'
                    (envE \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars envE),
                            TE_GhostLocals := TE_GhostLocals envE |-| {|varName|},
                            TE_ConstLocals :=
                              (if is_writable_lvalue env initTm
                               then TE_ConstLocals envE |-| {|varName|}
                               else finsert varName (TE_ConstLocals envE)) \<rparr>)"
        unfolding e by (rule tyenv_erased_add_var[OF rel]) simp_all
      from erased_typed_single[OF sE relE] show ?thesis using NotGhost Ref by simp
    qed
  qed
next
  case (CoreStmt_VarDeclCall declGhost varName varTy castOpt fnName tyArgs argTms)
  note T = CoreStmt_VarDeclCall.prems(1) and wf = CoreStmt_VarDeclCall.prems(2)
    and rel = CoreStmt_VarDeclCall.prems(3)
  show ?case
  proof (cases declGhost)
    case Ghost
    from T Ghost have e:
      "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                    TE_GhostLocals := finsert varName (TE_GhostLocals env),
                    TE_ConstLocals := TE_ConstLocals env |-| {|varName|} \<rparr>"
      by (auto split: if_splits option.splits)
    have "tyenv_erased env' envE"
      unfolding e by (rule tyenv_erased_add_ghost_var[OF rel]) simp
    hence "\<exists>envE'. core_statement_list_type envE NotGhost [] = Some envE'
                   \<and> tyenv_erased env' envE'"
      by (rule erased_typed_none)
    thus ?thesis using Ghost by simp
  next
    case NotGhost
    from T NotGhost obtain retTy where
        wk: "is_well_kinded env varTy" and
        rt: "is_runtime_type env varTy" and
        cp: "is_complete_type varTy" and
        ct: "core_impure_call_type env NotGhost fnName tyArgs argTms = Some retTy" and
        cast: "cast_result_type env NotGhost retTy castOpt = Some varTy" and
        e: "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                         TE_GhostLocals := TE_GhostLocals env |-| {|varName|},
                         TE_ConstLocals := TE_ConstLocals env |-| {|varName|} \<rparr>"
      by (auto split: if_splits option.splits)
    note tt = tyenv_erased_runtime_type[OF rel wk rt]
    have ctE: "core_impure_call_type envE NotGhost fnName tyArgs argTms = Some retTy"
      by (rule core_impure_call_type_erased[OF rel wf ct])
    have castE: "cast_result_type envE NotGhost retTy castOpt = Some varTy"
      by (rule cast_result_type_erased[OF rel cast])
    have sE: "core_statement_type envE NotGhost
                (CoreStmt_VarDeclCall NotGhost varName varTy castOpt fnName tyArgs argTms)
              = Some (envE \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars envE),
                              TE_GhostLocals := TE_GhostLocals envE |-| {|varName|},
                              TE_ConstLocals := TE_ConstLocals envE |-| {|varName|} \<rparr>)"
      using tt cp ctE castE by simp
    have relE: "tyenv_erased env'
                  (envE \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars envE),
                          TE_GhostLocals := TE_GhostLocals envE |-| {|varName|},
                          TE_ConstLocals := TE_ConstLocals envE |-| {|varName|} \<rparr>)"
      unfolding e by (rule tyenv_erased_add_var[OF rel]) simp_all
    from erased_typed_single[OF sE relE] show ?thesis using NotGhost by simp
  qed
next
  case (CoreStmt_Fix varName varTy)
  from CoreStmt_Fix.prems(1) have False
    by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
  thus ?case by blast
next
  case (CoreStmt_Obtain varName varTy condTm)
  note rel = CoreStmt_Obtain.prems(3)
  from CoreStmt_Obtain.prems(1) have e:
    "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                  TE_GhostLocals := finsert varName (TE_GhostLocals env),
                  TE_ConstLocals := TE_ConstLocals env |-| {|varName|} \<rparr>"
    by (auto simp: Let_def split: if_splits)
  have "tyenv_erased env' envE"
    unfolding e by (rule tyenv_erased_add_ghost_var[OF rel]) simp
  thus ?case by simp
next
  case (CoreStmt_Use witnessTm)
  from CoreStmt_Use.prems(1) have False
    by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
  thus ?case by blast
next
  case (CoreStmt_Assign assignGhost lhsTm rhsTm)
  note T = CoreStmt_Assign.prems(1) and wf = CoreStmt_Assign.prems(2)
    and rel = CoreStmt_Assign.prems(3)
  show ?case
  proof (cases assignGhost)
    case Ghost
    from T Ghost have "env' = env" by (auto split: if_splits option.splits)
    thus ?thesis using Ghost rel by simp
  next
    case NotGhost
    from T NotGhost obtain lhsTy where
        w: "is_writable_lvalue env lhsTm" and
        lt: "core_term_type env NotGhost lhsTm = Some lhsTy" and
        cp: "is_complete_type lhsTy" and
        rt: "core_term_type env NotGhost rhsTm = Some lhsTy" and
        e: "env' = env"
      by (auto split: if_splits option.splits)
    have wE: "is_writable_lvalue envE lhsTm"
      using is_writable_lvalue_erased[OF rel lt] w by simp
    have ltE: "core_term_type envE NotGhost lhsTm = Some lhsTy"
      by (rule core_term_type_erased[OF lt wf rel])
    have rtE: "core_term_type envE NotGhost rhsTm = Some lhsTy"
      by (rule core_term_type_erased[OF rt wf rel])
    have sE: "core_statement_type envE NotGhost (CoreStmt_Assign NotGhost lhsTm rhsTm)
                = Some envE"
      using wE ltE cp rtE by simp
    have relE: "tyenv_erased env' envE" using rel e by simp
    from erased_typed_single[OF sE relE] show ?thesis using NotGhost by simp
  qed
next
  case (CoreStmt_AssignCall assignGhost lhsTm castOpt fnName tyArgs argTms)
  note T = CoreStmt_AssignCall.prems(1) and wf = CoreStmt_AssignCall.prems(2)
    and rel = CoreStmt_AssignCall.prems(3)
  show ?case
  proof (cases assignGhost)
    case Ghost
    from T Ghost have "env' = env" by (auto split: if_splits option.splits)
    thus ?thesis using Ghost rel by simp
  next
    case NotGhost
    from T NotGhost have w: "is_writable_lvalue env lhsTm"
      by (simp split: if_splits)
    from T NotGhost w obtain lhsTy where
        lt: "core_term_type env NotGhost lhsTm = Some lhsTy"
      by (cases "core_term_type env NotGhost lhsTm") simp_all
    from T NotGhost w lt obtain retTy where
        ct: "core_impure_call_type env NotGhost fnName tyArgs argTms = Some retTy"
      by (cases "core_impure_call_type env NotGhost fnName tyArgs argTms") simp_all
    from T NotGhost w lt ct have
        cp: "is_complete_type lhsTy" and
        cast: "cast_result_type env NotGhost retTy castOpt = Some lhsTy" and
        e: "env' = env"
      by (simp_all split: if_splits)
    have wE: "is_writable_lvalue envE lhsTm"
      using is_writable_lvalue_erased[OF rel lt] w by simp
    have ltE: "core_term_type envE NotGhost lhsTm = Some lhsTy"
      by (rule core_term_type_erased[OF lt wf rel])
    have ctE: "core_impure_call_type envE NotGhost fnName tyArgs argTms = Some retTy"
      by (rule core_impure_call_type_erased[OF rel wf ct])
    have castE: "cast_result_type envE NotGhost retTy castOpt = Some lhsTy"
      by (rule cast_result_type_erased[OF rel cast])
    have sE: "core_statement_type envE NotGhost
                (CoreStmt_AssignCall NotGhost lhsTm castOpt fnName tyArgs argTms)
              = Some envE"
      using wE ltE ctE cp castE by simp
    have relE: "tyenv_erased env' envE" using rel e by simp
    from erased_typed_single[OF sE relE] show ?thesis using NotGhost by simp
  qed
next
  case (CoreStmt_Swap swapGhost lhsTm rhsTm)
  note T = CoreStmt_Swap.prems(1) and wf = CoreStmt_Swap.prems(2)
    and rel = CoreStmt_Swap.prems(3)
  show ?case
  proof (cases swapGhost)
    case Ghost
    from T Ghost have "env' = env" by (auto split: if_splits option.splits)
    thus ?thesis using Ghost rel by simp
  next
    case NotGhost
    from T NotGhost obtain lhsTy where
        wl: "is_writable_lvalue env lhsTm" and
        wr: "is_writable_lvalue env rhsTm" and
        lt: "core_term_type env NotGhost lhsTm = Some lhsTy" and
        cp: "is_complete_type lhsTy" and
        rt: "core_term_type env NotGhost rhsTm = Some lhsTy" and
        e: "env' = env"
      by (auto split: if_splits option.splits)
    have wlE: "is_writable_lvalue envE lhsTm"
      using is_writable_lvalue_erased[OF rel lt] wl by simp
    have wrE: "is_writable_lvalue envE rhsTm"
      using is_writable_lvalue_erased[OF rel rt] wr by simp
    have ltE: "core_term_type envE NotGhost lhsTm = Some lhsTy"
      by (rule core_term_type_erased[OF lt wf rel])
    have rtE: "core_term_type envE NotGhost rhsTm = Some lhsTy"
      by (rule core_term_type_erased[OF rt wf rel])
    have sE: "core_statement_type envE NotGhost (CoreStmt_Swap NotGhost lhsTm rhsTm)
                = Some envE"
      using wlE wrE ltE cp rtE by simp
    have relE: "tyenv_erased env' envE" using rel e by simp
    from erased_typed_single[OF sE relE] show ?thesis using NotGhost by simp
  qed
next
  case (CoreStmt_Return tm)
  note T = CoreStmt_Return.prems(1) and wf = CoreStmt_Return.prems(2)
    and rel = CoreStmt_Return.prems(3)
  from T have
      fg: "TE_FunctionGhost env = NotGhost" and
      t: "core_term_type env NotGhost tm = Some (TE_ReturnType env)" and
      e: "env' = env"
    by (auto split: if_splits)
  have fgE: "TE_FunctionGhost envE = NotGhost"
    using rel fg unfolding tyenv_erased_def by simp
  have retE: "TE_ReturnType envE = TE_ReturnType env"
    using rel unfolding tyenv_erased_def by simp
  have tE: "core_term_type envE NotGhost tm = Some (TE_ReturnType env)"
    by (rule core_term_type_erased[OF t wf rel])
  have sE: "core_statement_type envE NotGhost (CoreStmt_Return tm) = Some envE"
    using fgE retE tE by simp
  have relE: "tyenv_erased env' envE" using rel e by simp
  from erased_typed_single[OF sE relE] show ?case by simp
next
  case (CoreStmt_Assert condOpt proofBody)
  from CoreStmt_Assert.prems(1) have "env' = env"
    by (auto simp: Let_def split: if_splits option.splits)
  thus ?case using CoreStmt_Assert.prems(3) by simp
next
  case (CoreStmt_Assume tm)
  from CoreStmt_Assume.prems(1) have "env' = env" by (auto split: if_splits)
  thus ?case using CoreStmt_Assume.prems(3) by simp
next
  case (CoreStmt_While whileGhost condTm invars decrTm body)
  note T = CoreStmt_While.prems(1) and wf = CoreStmt_While.prems(2)
    and rel = CoreStmt_While.prems(3)
  show ?case
  proof (cases whileGhost)
    case Ghost
    from T Ghost have "env' = env"
      by (auto split: if_splits option.splits CoreType.splits)
    thus ?thesis using Ghost rel by simp
  next
    case NotGhost
    from T NotGhost obtain bodyEnv where
        c: "core_term_type env NotGhost condTm = Some CoreTy_Bool" and
        b: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) NotGhost body
              = Some bodyEnv" and
        e: "env' = env"
      by (auto split: if_splits option.splits CoreType.splits)
    have wfB: "tyenv_well_formed (env \<lparr> TE_ProofTopLevel := False \<rparr>)"
      by (rule tyenv_well_formed_TE_ProofTopLevel_irrelevant[OF wf])
    have relB: "tyenv_erased (env \<lparr> TE_ProofTopLevel := False \<rparr>)
                             (envE \<lparr> TE_ProofTopLevel := False \<rparr>)"
      using rel by simp
    have "\<exists>envE'. core_statement_list_type (envE \<lparr> TE_ProofTopLevel := False \<rparr>) NotGhost
                     (erase_ghost_statement_list body) = Some envE'
                  \<and> tyenv_erased bodyEnv envE'"
      by (rule erase_ghost_statement_list_typed_aux[OF b wfB relB])
         (rule CoreStmt_While.IH)
    then obtain bodyEnvE where
        bE: "core_statement_list_type (envE \<lparr> TE_ProofTopLevel := False \<rparr>) NotGhost
               (erase_ghost_statement_list body) = Some bodyEnvE"
      by blast
    have cE: "core_term_type envE NotGhost condTm = Some CoreTy_Bool"
      by (rule core_term_type_erased[OF c wf rel])
    have sE: "core_statement_type envE NotGhost
                (CoreStmt_While NotGhost condTm [] (CoreTm_LitBool False)
                   (erase_ghost_statement_list body))
              = Some envE"
      using cE bE by simp
    have relE: "tyenv_erased env' envE" using rel e by simp
    from erased_typed_single[OF sE relE] show ?thesis using NotGhost by simp
  qed
next
  case (CoreStmt_Match matchGhost scrut arms)
  note T = CoreStmt_Match.prems(1) and wf = CoreStmt_Match.prems(2)
    and rel = CoreStmt_Match.prems(3)
  show ?case
  proof (cases matchGhost)
    case Ghost
    from T Ghost have "env' = env"
      by (auto simp: Let_def split: if_splits option.splits)
    thus ?thesis using Ghost rel by simp
  next
    case NotGhost
    from T NotGhost obtain scrutTy where
        s: "core_term_type env NotGhost scrut = Some scrutTy" and
        pats: "list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst arms)" and
        bodies: "list_all (\<lambda>body. core_statement_list_type
                                     (env \<lparr> TE_ProofTopLevel := False \<rparr>) NotGhost body
                                   \<noteq> None)
                          (map snd arms)" and
        e: "env' = env"
      by (auto simp: Let_def split: if_splits option.splits)
    define armsE where
      "armsE = map (\<lambda>(pat, body). (pat, erase_ghost_statement_list body)) arms"
    have fst_eq: "map fst armsE = map fst arms"
      unfolding armsE_def by (induction arms) auto
    have wfB: "tyenv_well_formed (env \<lparr> TE_ProofTopLevel := False \<rparr>)"
      by (rule tyenv_well_formed_TE_ProofTopLevel_irrelevant[OF wf])
    have relB: "tyenv_erased (env \<lparr> TE_ProofTopLevel := False \<rparr>)
                             (envE \<lparr> TE_ProofTopLevel := False \<rparr>)"
      using rel by simp
    have sE': "core_term_type envE NotGhost scrut = Some scrutTy"
      by (rule core_term_type_erased[OF s wf rel])
    have srt: "is_runtime_type env scrutTy"
      by (rule core_term_type_notghost_runtime[OF s wf])
    have patsE: "list_all (\<lambda>p. pattern_compatible envE p scrutTy) (map fst armsE)"
      unfolding fst_eq list_all_iff
    proof
      fix p assume pin: "p \<in> set (map fst arms)"
      have pc: "pattern_compatible env p scrutTy"
        using pats pin by (auto simp: list_all_iff)
      show "pattern_compatible envE p scrutTy"
        by (rule pattern_compatible_erased[OF rel wf pc srt])
    qed
    have bodiesE: "list_all (\<lambda>body. core_statement_list_type
                                      (envE \<lparr> TE_ProofTopLevel := False \<rparr>) NotGhost body
                                    \<noteq> None)
                            (map snd armsE)"
      unfolding list_all_iff
    proof
      fix bodyE assume "bodyE \<in> set (map snd armsE)"
      then obtain pat body where
          ain: "(pat, body) \<in> set arms" and
          bodyE: "bodyE = erase_ghost_statement_list body"
        unfolding armsE_def by auto
      have "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) NotGhost body
              \<noteq> None"
        using bodies ain by (force simp: list_all_iff)
      then obtain bodyEnv where
          b: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) NotGhost body
                = Some bodyEnv"
        by auto
      have sn: "body \<in> Basic_BNFs.snds (pat, body)" by simp
      have "\<exists>envE'. core_statement_list_type (envE \<lparr> TE_ProofTopLevel := False \<rparr>) NotGhost
                       (erase_ghost_statement_list body) = Some envE'
                    \<and> tyenv_erased bodyEnv envE'"
        by (rule erase_ghost_statement_list_typed_aux[OF b wfB relB])
           (rule CoreStmt_Match.IH[OF ain sn])
      thus "core_statement_list_type (envE \<lparr> TE_ProofTopLevel := False \<rparr>) NotGhost bodyE
              \<noteq> None"
        using bodyE by auto
    qed
    have sE: "core_statement_type envE NotGhost (CoreStmt_Match NotGhost scrut armsE)
                = Some envE"
      using sE' patsE bodiesE by (simp add: Let_def)
    have relE: "tyenv_erased env' envE" using rel e by simp
    from erased_typed_single[OF sE relE] show ?thesis
      using NotGhost by (simp add: armsE_def)
  qed
next
  case (CoreStmt_ShowHide sh name)
  from CoreStmt_ShowHide.prems(1) have "env' = env" by simp
  thus ?case using CoreStmt_ShowHide.prems(3) by simp
next
  case (CoreStmt_Block body)
  note T = CoreStmt_Block.prems(1) and wf = CoreStmt_Block.prems(2)
    and rel = CoreStmt_Block.prems(3)
  from T obtain bodyEnv where
      b: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) NotGhost body
            = Some bodyEnv" and
      e: "env' = env"
    by (auto split: option.splits)
  have wfB: "tyenv_well_formed (env \<lparr> TE_ProofTopLevel := False \<rparr>)"
    by (rule tyenv_well_formed_TE_ProofTopLevel_irrelevant[OF wf])
  have relB: "tyenv_erased (env \<lparr> TE_ProofTopLevel := False \<rparr>)
                           (envE \<lparr> TE_ProofTopLevel := False \<rparr>)"
    using rel by simp
  have "\<exists>envE'. core_statement_list_type (envE \<lparr> TE_ProofTopLevel := False \<rparr>) NotGhost
                   (erase_ghost_statement_list body) = Some envE'
                \<and> tyenv_erased bodyEnv envE'"
    by (rule erase_ghost_statement_list_typed_aux[OF b wfB relB])
       (rule CoreStmt_Block.IH)
  then obtain bodyEnvE where
      bE: "core_statement_list_type (envE \<lparr> TE_ProofTopLevel := False \<rparr>) NotGhost
             (erase_ghost_statement_list body) = Some bodyEnvE"
    by blast
  have sE: "core_statement_type envE NotGhost
              (CoreStmt_Block (erase_ghost_statement_list body)) = Some envE"
    using bE by simp
  have relE: "tyenv_erased env' envE" using rel e by simp
  from erased_typed_single[OF sE relE] show ?case by simp
qed

(* Erased code is typed in NotGhost mode, in the erased environment. *)
theorem erase_ghost_statement_list_typed:
  assumes "core_statement_list_type env NotGhost stmts = Some env'"
    and "tyenv_well_formed env"
    and "tyenv_erased env envE"
  shows "\<exists>envE'. core_statement_list_type envE NotGhost (erase_ghost_statement_list stmts)
                   = Some envE'
                 \<and> tyenv_erased env' envE'"
  by (rule erase_ghost_statement_list_typed_aux[OF assms])
     (rule erase_ghost_statement_typed)

end
