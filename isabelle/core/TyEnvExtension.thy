theory TyEnvExtension
  imports CoreStmtTypecheck
begin

(* ========================================================================== *)
(* Environment extension along the declaration axes                           *)
(*                                                                            *)
(* tyenv_extends env env' says env' is env with (possibly) MORE global        *)
(* variables, functions, datatypes and data constructors - and everything     *)
(* else unchanged. This is the weakening axis needed by linking's             *)
(* whole-program well-typedness theorem: a term or statement that typechecks  *)
(* against one module's environment must still typecheck against the linked   *)
(* program's larger environment. Link success guarantees the extension is     *)
(* disjoint, so nothing already present is ever redefined - which is why the  *)
(* growing fields only need lookup preservation, not equality.                *)
(*                                                                            *)
(* This is deliberately orthogonal to the existing type-variable weakening    *)
(* (core_term_type_irrelevant_tyvar etc.): TE_TypeVars / TE_RuntimeTypeVars   *)
(* are pinned EQUAL here, and the linking proof composes the two axes.        *)
(*                                                                            *)
(* The ghost markers need care: the typechecker consults them negatively      *)
(* (a NotGhost read of variable x requires x NOT ghost; a NotGhost use of     *)
(* datatype d requires d NOT ghost), so blanket growth would be unsound.      *)
(* Instead we require the ghost status of every name in the OLD maps to be    *)
(* unchanged; new names may have either status. A successful lookup only      *)
(* ever interrogates old names, so this suffices.                             *)
(*                                                                            *)
(* TE_AbstractTypes is left unconstrained: no typechecking function reads it  *)
(* (it feeds tyenv_well_formed only).                                         *)
(* ========================================================================== *)

definition tyenv_extends :: "CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "tyenv_extends env env' = (
     \<comment> \<open>Scope fields: identical.\<close>
     TE_LocalVars env' = TE_LocalVars env
   \<and> TE_GhostLocals env' = TE_GhostLocals env
   \<and> TE_ConstLocals env' = TE_ConstLocals env
   \<and> TE_TypeVars env' = TE_TypeVars env
   \<and> TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env
   \<and> TE_ReturnType env' = TE_ReturnType env
   \<and> TE_FunctionGhost env' = TE_FunctionGhost env
   \<and> TE_ProofGoal env' = TE_ProofGoal env
   \<and> TE_ProofTopLevel env' = TE_ProofTopLevel env
     \<comment> \<open>Declaration maps: every old entry survives unchanged.\<close>
   \<and> (\<forall>name ty. fmlookup (TE_GlobalVars env) name = Some ty \<longrightarrow>
        fmlookup (TE_GlobalVars env') name = Some ty)
   \<and> (\<forall>name info. fmlookup (TE_Functions env) name = Some info \<longrightarrow>
        fmlookup (TE_Functions env') name = Some info)
   \<and> (\<forall>name n. fmlookup (TE_Datatypes env) name = Some n \<longrightarrow>
        fmlookup (TE_Datatypes env') name = Some n)
   \<and> (\<forall>name entry. fmlookup (TE_DataCtors env) name = Some entry \<longrightarrow>
        fmlookup (TE_DataCtors env') name = Some entry)
   \<and> (\<forall>name ctors. fmlookup (TE_DataCtorsByType env) name = Some ctors \<longrightarrow>
        fmlookup (TE_DataCtorsByType env') name = Some ctors)
     \<comment> \<open>Ghost markers: unchanged on the old domains.\<close>
   \<and> (\<forall>name. name |\<in>| fmdom (TE_GlobalVars env) \<longrightarrow>
        (name |\<in>| TE_GhostGlobals env' \<longleftrightarrow> name |\<in>| TE_GhostGlobals env))
   \<and> (\<forall>name. name |\<in>| fmdom (TE_Datatypes env) \<longrightarrow>
        (name |\<in>| TE_GhostDatatypes env' \<longleftrightarrow> name |\<in>| TE_GhostDatatypes env)))"

lemma tyenv_extends_refl [simp]:
  "tyenv_extends env env"
  unfolding tyenv_extends_def by simp


(* ========================================================================== *)
(* Variable lookup under extension                                            *)
(* ========================================================================== *)

(* A successful variable lookup is preserved: locals are unchanged, and a
   global hit survives because old global entries survive. *)
lemma tyenv_extends_lookup_var:
  assumes ext: "tyenv_extends env env'"
    and lk: "tyenv_lookup_var env name = Some ty"
  shows "tyenv_lookup_var env' name = Some ty"
proof -
  have leq: "TE_LocalVars env' = TE_LocalVars env"
    using ext unfolding tyenv_extends_def by blast
  show ?thesis
  proof (cases "fmlookup (TE_LocalVars env) name")
    case (Some lty)
    then show ?thesis using lk leq unfolding tyenv_lookup_var_def by simp
  next
    case None
    then have "fmlookup (TE_GlobalVars env) name = Some ty"
      using lk unfolding tyenv_lookup_var_def by simp
    then have "fmlookup (TE_GlobalVars env') name = Some ty"
      using ext unfolding tyenv_extends_def by blast
    then show ?thesis using None leq unfolding tyenv_lookup_var_def by simp
  qed
qed

(* The ghost status of a successfully-looked-up variable is unchanged: for a
   local hit the ghost-locals set is equal; for a global hit the name is in
   the old global domain, where ghost status is preserved by definition. *)
lemma tyenv_extends_var_ghost:
  assumes ext: "tyenv_extends env env'"
    and lk: "tyenv_lookup_var env name = Some ty"
  shows "tyenv_var_ghost env' name = tyenv_var_ghost env name"
proof -
  have leq: "TE_LocalVars env' = TE_LocalVars env"
    and geq: "TE_GhostLocals env' = TE_GhostLocals env"
    using ext unfolding tyenv_extends_def by blast+
  show ?thesis
  proof (cases "fmlookup (TE_LocalVars env) name")
    case (Some lty)
    then show ?thesis using leq geq unfolding tyenv_var_ghost_def by simp
  next
    case None
    then have "fmlookup (TE_GlobalVars env) name = Some ty"
      using lk unfolding tyenv_lookup_var_def by simp
    then have dom: "name |\<in>| fmdom (TE_GlobalVars env)"
      by (simp add: fmdomI)
    have "name |\<in>| TE_GhostGlobals env' \<longleftrightarrow> name |\<in>| TE_GhostGlobals env"
      using ext dom unfolding tyenv_extends_def by blast
    then show ?thesis using None leq unfolding tyenv_var_ghost_def by simp
  qed
qed


(* ========================================================================== *)
(* Kind and runtime checks under extension                                    *)
(* ========================================================================== *)

(* Well-kindedness is monotone under extension: the datatype lookups it makes
   all succeed in env, hence give the same answer in env', and TE_TypeVars is
   unchanged. *)
lemma is_well_kinded_tyenv_extends:
  assumes ext: "tyenv_extends env env'"
    and wk: "is_well_kinded env ty"
  shows "is_well_kinded env' ty"
  using wk
proof (induction ty)
  case (CoreTy_Datatype name argTypes)
  then obtain numTyVars where
    dt: "fmlookup (TE_Datatypes env) name = Some numTyVars" and
    len: "length argTypes = numTyVars" and
    args: "list_all (is_well_kinded env) argTypes"
    by (auto split: option.splits)
  have dt': "fmlookup (TE_Datatypes env') name = Some numTyVars"
    using ext dt unfolding tyenv_extends_def by blast
  have args': "list_all (is_well_kinded env') argTypes"
    using CoreTy_Datatype.IH args by (simp add: list_all_iff)
  show ?case using dt' len args' by simp
next
  case (CoreTy_Record flds)
  have "\<And>a b. (a, b) \<in> set flds \<Longrightarrow> is_well_kinded env' b"
  proof -
    fix a b assume mem: "(a, b) \<in> set flds"
    from mem CoreTy_Record.prems have "is_well_kinded env b"
      by (auto simp: list_all_iff)
    with CoreTy_Record.IH[OF mem] show "is_well_kinded env' b"
      by (simp add: snds.intros)
  qed
  thus ?case using CoreTy_Record.prems by (auto simp: list_all_iff)
next
  case (CoreTy_Array elemTy dims)
  thus ?case by auto
next
  case (CoreTy_Var n)
  have "TE_TypeVars env' = TE_TypeVars env"
    using ext unfolding tyenv_extends_def by blast
  then show ?case using CoreTy_Var.prems by simp
qed simp_all

(* Runtime-ness transfers for WELL-KINDED types: well-kindedness pins every
   datatype name in the type into the old datatype domain, where the ghost
   marker is unchanged; TE_RuntimeTypeVars is equal. (The well-kindedness
   hypothesis cannot be dropped: an unknown datatype's ghost status is
   unconstrained in env'.) *)
lemma is_runtime_type_tyenv_extends:
  assumes ext: "tyenv_extends env env'"
    and wk: "is_well_kinded env ty"
    and rt: "is_runtime_type env ty"
  shows "is_runtime_type env' ty"
  using wk rt
proof (induction ty)
  case (CoreTy_Datatype name argTypes)
  from CoreTy_Datatype.prems(1) obtain numTyVars where
    dt: "fmlookup (TE_Datatypes env) name = Some numTyVars" and
    args_wk: "list_all (is_well_kinded env) argTypes"
    by (auto split: option.splits)
  from CoreTy_Datatype.prems(2) have
    ng: "name |\<notin>| TE_GhostDatatypes env" and
    args_rt: "list_all (is_runtime_type env) argTypes"
    by auto
  have dom: "name |\<in>| fmdom (TE_Datatypes env)"
    using dt by (simp add: fmdomI)
  have ng': "name |\<notin>| TE_GhostDatatypes env'"
    using ext dom ng unfolding tyenv_extends_def by blast
  have args_rt': "list_all (is_runtime_type env') argTypes"
    using CoreTy_Datatype.IH args_wk args_rt by (simp add: list_all_iff)
  show ?case using ng' args_rt' by simp
next
  case (CoreTy_Record flds)
  have each: "\<And>a b. (a, b) \<in> set flds \<Longrightarrow> is_runtime_type env' b"
  proof -
    fix a b assume mem: "(a, b) \<in> set flds"
    from mem CoreTy_Record.prems(1) have "is_well_kinded env b"
      by (auto simp: list_all_iff)
    moreover from mem CoreTy_Record.prems(2) have "is_runtime_type env b"
      by (auto simp: list_all_iff)
    ultimately show "is_runtime_type env' b"
      using CoreTy_Record.IH[OF mem] by (simp add: snds.intros)
  qed
  then show ?case by (auto simp: list_all_iff)
next
  case (CoreTy_Array elemTy dims)
  then show ?case by auto
next
  case (CoreTy_Var n)
  have "TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env"
    using ext unfolding tyenv_extends_def by blast
  then show ?case using CoreTy_Var.prems by simp
qed simp_all


(* ========================================================================== *)
(* Pattern compatibility under extension                                      *)
(* ========================================================================== *)

(* pattern_compatible only consults TE_DataCtors, positively (a failed lookup
   means incompatible), so success is preserved. *)
lemma pattern_compatible_tyenv_extends:
  assumes ext: "tyenv_extends env env'"
    and pc: "pattern_compatible env p ty"
  shows "pattern_compatible env' p ty"
  using pc
proof (induction p arbitrary: ty)
  case (CorePat_Variant ctorName payloadPat)
  from CorePat_Variant.prems obtain dtName tyvars payloadTy where
    ctor: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payloadTy)"
    by (auto split: option.splits)
  show ?case
  proof (cases ty)
    case (CoreTy_Datatype tyName tyArgs)
    with CorePat_Variant.prems ctor have
      name_eq: "tyName = dtName" and
      len_eq: "length tyArgs = length tyvars" and
      pc_payload: "pattern_compatible env payloadPat
                     (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
      by auto
    have ctor': "fmlookup (TE_DataCtors env') ctorName = Some (dtName, tyvars, payloadTy)"
      using ext ctor unfolding tyenv_extends_def by blast
    have pc_payload': "pattern_compatible env' payloadPat
                         (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
      using CorePat_Variant.IH pc_payload by blast
    show ?thesis using CoreTy_Datatype ctor' name_eq len_eq pc_payload' by simp
  qed (use CorePat_Variant.prems ctor in \<open>auto split: option.splits\<close>)
next
  case (CorePat_Record pflds)
  show ?case
  proof (cases ty)
    case (CoreTy_Record fldTys)
    with CorePat_Record.prems have la2:
      "list_all2 (\<lambda>(pn, p) (fn, fty). pn = fn \<and> pattern_compatible env p fty) pflds fldTys"
      by simp
    have len_eq: "length pflds = length fldTys"
      using la2 by (rule list_all2_lengthD)
    have IH_elem: "\<And>pn p fty. (pn, p) \<in> set pflds \<Longrightarrow> pattern_compatible env p fty \<Longrightarrow>
                               pattern_compatible env' p fty"
    proof -
      fix pn p fty assume mem: "(pn, p) \<in> set pflds" and pc1: "pattern_compatible env p fty"
      have "p \<in> Basic_BNFs.snds (pn, p)" by (simp add: snds.intros)
      then show "pattern_compatible env' p fty"
        using CorePat_Record.IH[OF mem] pc1 by blast
    qed
    have la2': "list_all2 (\<lambda>(pn, p) (fn, fty). pn = fn \<and> pattern_compatible env' p fty)
                          pflds fldTys"
      unfolding list_all2_conv_all_nth case_prod_beta
    proof (rule conjI)
      show "length pflds = length fldTys" by (rule len_eq)
    next
      show "\<forall>i<length pflds. fst (pflds ! i) = fst (fldTys ! i) \<and>
              pattern_compatible env' (snd (pflds ! i)) (snd (fldTys ! i))"
      proof (intro allI impI)
        fix i assume i_lt: "i < length pflds"
        have pi: "fst (pflds ! i) = fst (fldTys ! i) \<and>
                  pattern_compatible env (snd (pflds ! i)) (snd (fldTys ! i))"
          using la2 i_lt unfolding list_all2_conv_all_nth case_prod_beta by blast
        have mem: "(fst (pflds ! i), snd (pflds ! i)) \<in> set pflds"
          using i_lt by (metis nth_mem prod.collapse)
        have "pattern_compatible env' (snd (pflds ! i)) (snd (fldTys ! i))"
          using IH_elem[OF mem] pi by blast
        then show "fst (pflds ! i) = fst (fldTys ! i) \<and>
                   pattern_compatible env' (snd (pflds ! i)) (snd (fldTys ! i))"
          using pi by blast
      qed
    qed
    show ?thesis using CoreTy_Record la2' by simp
  qed (use CorePat_Record.prems in auto)
qed auto


(* ========================================================================== *)
(* Term typechecking under extension                                          *)
(*                                                                            *)
(* The tyenv_ctors_consistent hypothesis serves exactly one purpose: in the   *)
(* CoreTm_VariantCtor case the NotGhost rule checks that the constructor's    *)
(* datatype is not ghost, and to know that datatype's ghost status is         *)
(* preserved we must place it in the old datatype domain. In the linking      *)
(* application env is well-formed, so this hypothesis is freely available.    *)
(* ========================================================================== *)

lemma core_term_type_tyenv_extends:
  assumes "tyenv_extends env env'"
    and "tyenv_ctors_consistent env"
    and "core_term_type env ghost tm = Some ty"
  shows "core_term_type env' ghost tm = Some ty"
using assms proof (induction tm arbitrary: env env' ghost ty)
  case (CoreTm_LitArray elemTy tms)
  note ext = CoreTm_LitArray.prems(1) and cons = CoreTm_LitArray.prems(2)
  from CoreTm_LitArray.prems(3) have
    elemTy_wk: "is_well_kinded env elemTy" and
    elemTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env elemTy" and
    all_tms: "list_all (\<lambda>tm. core_term_type env ghost tm = Some elemTy) tms" and
    len_range: "int_in_range (int_range Unsigned IntBits_64) (int (length tms))" and
    ty_eq: "ty = CoreTy_Array elemTy [CoreDim_Fixed (int (length tms))]"
    by (auto split: if_splits)
  have elemTy_wk': "is_well_kinded env' elemTy"
    using is_well_kinded_tyenv_extends[OF ext elemTy_wk] .
  have elemTy_rt': "ghost = NotGhost \<longrightarrow> is_runtime_type env' elemTy"
    using elemTy_rt is_runtime_type_tyenv_extends[OF ext elemTy_wk] by blast
  have all_tms': "list_all (\<lambda>tm. core_term_type env' ghost tm = Some elemTy) tms"
    unfolding list_all_iff
  proof
    fix x assume x_in: "x \<in> set tms"
    have "core_term_type env ghost x = Some elemTy"
      using all_tms x_in by (simp add: list_all_iff)
    then show "core_term_type env' ghost x = Some elemTy"
      using CoreTm_LitArray.IH[OF x_in ext cons] by blast
  qed
  show ?case using elemTy_wk' elemTy_rt' all_tms' len_range ty_eq by simp
next
  case (CoreTm_Var name)
  from CoreTm_Var.prems(3) obtain vty where
    lk: "tyenv_lookup_var env name = Some vty" and
    gh: "ghost = NotGhost \<longrightarrow> \<not> tyenv_var_ghost env name" and
    ty_eq: "ty = vty"
    by (auto split: option.splits if_splits)
  have lk': "tyenv_lookup_var env' name = Some vty"
    using tyenv_extends_lookup_var[OF CoreTm_Var.prems(1) lk] .
  have gh': "tyenv_var_ghost env' name = tyenv_var_ghost env name"
    using tyenv_extends_var_ghost[OF CoreTm_Var.prems(1) lk] .
  show ?case using lk' gh gh' ty_eq by simp
next
  case (CoreTm_Cast targetTy tm)
  note ext = CoreTm_Cast.prems(1) and cons = CoreTm_Cast.prems(2)
  from CoreTm_Cast.prems(3) obtain operandTy where
    operand_ty: "core_term_type env ghost tm = Some operandTy" and
    operand_int: "is_integer_type operandTy" and
    target_int: "is_integer_type targetTy" and
    targetTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env targetTy" and
    ty_eq: "ty = targetTy"
    by (auto split: option.splits if_splits)
  have operand_ty': "core_term_type env' ghost tm = Some operandTy"
    using CoreTm_Cast.IH[OF ext cons operand_ty] .
  have targetTy_wk: "is_well_kinded env targetTy"
    using target_int is_integer_type_well_kinded by blast
  have targetTy_rt': "ghost = NotGhost \<longrightarrow> is_runtime_type env' targetTy"
    using targetTy_rt is_runtime_type_tyenv_extends[OF ext targetTy_wk] by blast
  show ?case using operand_ty' operand_int target_int targetTy_rt' ty_eq by simp
next
  case (CoreTm_Unop op operand)
  from CoreTm_Unop.prems(3) obtain operandTy where
    op_ty: "core_term_type env ghost operand = Some operandTy"
    by (auto split: option.splits)
  have op_ty': "core_term_type env' ghost operand = Some operandTy"
    using CoreTm_Unop.IH[OF CoreTm_Unop.prems(1,2) op_ty] .
  show ?case using CoreTm_Unop.prems(3) op_ty op_ty'
    by (auto split: option.splits CoreUnop.splits if_splits)
next
  case (CoreTm_Binop op lhs rhs)
  from CoreTm_Binop.prems(3) obtain lhsTy rhsTy where
    lhs_ty: "core_term_type env ghost lhs = Some lhsTy" and
    rhs_ty: "core_term_type env ghost rhs = Some rhsTy"
    by (auto split: option.splits)
  have lhs_ty': "core_term_type env' ghost lhs = Some lhsTy"
    using CoreTm_Binop.IH(1)[OF CoreTm_Binop.prems(1,2) lhs_ty] .
  have rhs_ty': "core_term_type env' ghost rhs = Some rhsTy"
    using CoreTm_Binop.IH(2)[OF CoreTm_Binop.prems(1,2) rhs_ty] .
  show ?case using CoreTm_Binop.prems(3) lhs_ty lhs_ty' rhs_ty rhs_ty'
    by (auto split: option.splits if_splits)
next
  case (CoreTm_Let var rhs body)
  note ext = CoreTm_Let.prems(1) and cons = CoreTm_Let.prems(2)
  from CoreTm_Let.prems(3) obtain rhsTy where
    rhs_ty: "core_term_type env ghost rhs = Some rhsTy" and
    body_ty: "core_term_type
        (env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
               TE_GhostLocals := (if ghost = Ghost then finsert var (TE_GhostLocals env)
                                   else fminus (TE_GhostLocals env) {|var|}),
               TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>)
        ghost body = Some ty"
    by (auto simp: Let_def split: option.splits)
  have rhs_ty': "core_term_type env' ghost rhs = Some rhsTy"
    using CoreTm_Let.IH(1)[OF ext cons rhs_ty] .
  let ?bodyEnv = "env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                        TE_GhostLocals := (if ghost = Ghost then finsert var (TE_GhostLocals env)
                                            else fminus (TE_GhostLocals env) {|var|}),
                        TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
  let ?bodyEnv' = "env' \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env'),
                          TE_GhostLocals := (if ghost = Ghost then finsert var (TE_GhostLocals env')
                                              else fminus (TE_GhostLocals env') {|var|}),
                          TE_ConstLocals := finsert var (TE_ConstLocals env') \<rparr>"
  have ext_body: "tyenv_extends ?bodyEnv ?bodyEnv'"
    using ext unfolding tyenv_extends_def by simp
  have cons_body: "tyenv_ctors_consistent ?bodyEnv"
    using cons unfolding tyenv_ctors_consistent_def by simp
  have body_ty': "core_term_type ?bodyEnv' ghost body = Some ty"
    using CoreTm_Let.IH(2)[OF ext_body cons_body body_ty] .
  show ?case using rhs_ty' body_ty' by (simp add: Let_def)
next
  case (CoreTm_Quantifier quant var varTy body)
  note ext = CoreTm_Quantifier.prems(1) and cons = CoreTm_Quantifier.prems(2)
  show ?case
  proof (cases ghost)
    case NotGhost
    with CoreTm_Quantifier.prems(3) show ?thesis by simp
  next
    case Ghost
    from Ghost CoreTm_Quantifier.prems(3) have wk: "is_well_kinded env varTy"
      by (auto simp: Let_def split: option.splits if_splits CoreType.splits)
    have wk': "is_well_kinded env' varTy"
      using is_well_kinded_tyenv_extends[OF ext wk] .
    from Ghost CoreTm_Quantifier.prems(3) obtain bodyTy where
      body_ty: "core_term_type
        (env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
               TE_GhostLocals := finsert var (TE_GhostLocals env) \<rparr>)
        Ghost body = Some bodyTy"
      and ty_eq: "ty = CoreTy_Bool" and body_bool: "bodyTy = CoreTy_Bool"
      by (auto simp: Let_def split: option.splits if_splits CoreType.splits)
    let ?bodyEnv = "env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                          TE_GhostLocals := finsert var (TE_GhostLocals env) \<rparr>"
    let ?bodyEnv' = "env' \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env'),
                            TE_GhostLocals := finsert var (TE_GhostLocals env') \<rparr>"
    have ext_body: "tyenv_extends ?bodyEnv ?bodyEnv'"
      using ext unfolding tyenv_extends_def by simp
    have cons_body: "tyenv_ctors_consistent ?bodyEnv"
      using cons unfolding tyenv_ctors_consistent_def by simp
    have body_ty': "core_term_type ?bodyEnv' Ghost body = Some bodyTy"
      using CoreTm_Quantifier.IH[OF ext_body cons_body body_ty] .
    show ?thesis using Ghost wk' body_ty' body_bool ty_eq by (simp add: Let_def)
  qed
next
  case (CoreTm_FunctionCall fnName tyArgs tmArgs)
  note ext = CoreTm_FunctionCall.prems(1) and cons = CoreTm_FunctionCall.prems(2)
  from CoreTm_FunctionCall.prems(3) obtain funInfo where
    fn_lk: "fmlookup (TE_Functions env) fnName = Some funInfo"
    by (auto split: option.splits)
  have fn_lk': "fmlookup (TE_Functions env') fnName = Some funInfo"
    using ext fn_lk unfolding tyenv_extends_def by blast
  have wk_mono: "\<And>t. is_well_kinded env t \<Longrightarrow> is_well_kinded env' t"
    using is_well_kinded_tyenv_extends[OF ext] by blast
  have rt_mono: "\<And>t. is_well_kinded env t \<Longrightarrow> is_runtime_type env t \<Longrightarrow> is_runtime_type env' t"
    using is_runtime_type_tyenv_extends[OF ext] by blast
  have la_wk: "list_all (is_well_kinded env) tyArgs \<Longrightarrow> list_all (is_well_kinded env') tyArgs"
    using wk_mono by (auto simp: list_all_iff)
  have la_rt: "list_all (is_well_kinded env) tyArgs \<Longrightarrow>
               list_all (is_runtime_type env) tyArgs \<Longrightarrow>
               list_all (is_runtime_type env') tyArgs"
    using rt_mono by (auto simp: list_all_iff)
  have IH: "\<And>tm ty. tm \<in> set tmArgs \<Longrightarrow> core_term_type env ghost tm = Some ty \<Longrightarrow>
                     core_term_type env' ghost tm = Some ty"
    using CoreTm_FunctionCall.IH ext cons by blast
  have la2_mono: "\<And>ys. list_all2 (\<lambda>tm expectedTy.
          (\<exists>y. core_term_type env ghost tm = Some y) \<and>
          (\<forall>x2. core_term_type env ghost tm = Some x2 \<longrightarrow> x2 = expectedTy)) tmArgs ys \<Longrightarrow>
        list_all2 (\<lambda>tm expectedTy.
          (\<exists>y. core_term_type env' ghost tm = Some y) \<and>
          (\<forall>x2. core_term_type env' ghost tm = Some x2 \<longrightarrow> x2 = expectedTy)) tmArgs ys"
    using IH by (fastforce simp: list_all2_iff in_set_zip)
  show ?case using CoreTm_FunctionCall.prems(3) fn_lk fn_lk' la_wk la_rt la2_mono
    by (auto split: option.splits if_splits simp: Let_def)
next
  case (CoreTm_VariantCtor ctorName tyArgs payload)
  note ext = CoreTm_VariantCtor.prems(1) and cons = CoreTm_VariantCtor.prems(2)
  from CoreTm_VariantCtor.prems(3) obtain dtName tyvars payloadTy where
    ctor_lk: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payloadTy)"
    by (auto split: option.splits)
  have ctor_lk': "fmlookup (TE_DataCtors env') ctorName = Some (dtName, tyvars, payloadTy)"
    using ext ctor_lk unfolding tyenv_extends_def by blast
  from CoreTm_VariantCtor.prems(3) ctor_lk have
    len_eq: "length tyArgs = length tyvars" and
    wk_args: "list_all (is_well_kinded env) tyArgs" and
    ng_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) tyArgs" and
    ng_dt: "ghost = NotGhost \<longrightarrow> dtName |\<notin>| TE_GhostDatatypes env" and
    payload_ty: "core_term_type env ghost payload
                   = Some (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)" and
    ty_eq: "ty = CoreTy_Datatype dtName tyArgs"
    by (auto simp: Let_def split: if_splits option.splits)
  have wk_args': "list_all (is_well_kinded env') tyArgs"
    using wk_args is_well_kinded_tyenv_extends[OF ext] by (auto simp: list_all_iff)
  have rt_args': "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env') tyArgs"
    using ng_rt wk_args is_runtime_type_tyenv_extends[OF ext] by (auto simp: list_all_iff)
  \<comment> \<open>The constructor's datatype lies in the old datatype domain (consistency),
      so its ghost marker is unchanged.\<close>
  have dom_dt: "dtName |\<in>| fmdom (TE_Datatypes env)"
    using cons ctor_lk unfolding tyenv_ctors_consistent_def by (metis fmdomI)
  have ng_dt': "ghost = NotGhost \<longrightarrow> dtName |\<notin>| TE_GhostDatatypes env'"
    using ng_dt ext dom_dt unfolding tyenv_extends_def by blast
  have ng_fail': "\<not> (ghost = NotGhost \<and> (\<not> list_all (is_runtime_type env') tyArgs
                       \<or> dtName |\<in>| TE_GhostDatatypes env'))"
    using rt_args' ng_dt' by auto
  have payload_ty': "core_term_type env' ghost payload
                       = Some (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
    using CoreTm_VariantCtor.IH[OF ext cons payload_ty] .
  show ?case using ctor_lk' len_eq wk_args' ng_fail' payload_ty' ty_eq
    by (simp add: Let_def)
next
  case (CoreTm_Record flds)
  note ext = CoreTm_Record.prems(1) and cons = CoreTm_Record.prems(2)
  from CoreTm_Record.prems(3) obtain tys where
    those_eq: "those (map (\<lambda>(name, tm). core_term_type env ghost tm) flds) = Some tys" and
    ty_eq: "ty = CoreTy_Record (zip (map fst flds) tys)"
    by (auto split: option.splits if_splits)
  have IH: "\<And>nm tm ty'. (nm, tm) \<in> set flds \<Longrightarrow> core_term_type env ghost tm = Some ty' \<Longrightarrow>
                         core_term_type env' ghost tm = Some ty'"
  proof -
    fix nm tm ty' assume mem: "(nm, tm) \<in> set flds"
      and t: "core_term_type env ghost tm = Some ty'"
    have "tm \<in> Basic_BNFs.snds (nm, tm)" by (simp add: snds.intros)
    then show "core_term_type env' ghost tm = Some ty'"
      using CoreTm_Record.IH[OF mem] ext cons t by blast
  qed
  from those_eq have la2: "list_all2 (\<lambda>x y. x = Some y)
                                      (map (\<lambda>(name, tm). core_term_type env ghost tm) flds) tys"
    using those_eq_Some by blast
  have all_some: "\<And>nm tm. (nm, tm) \<in> set flds \<Longrightarrow>
                          \<exists>ty'. core_term_type env ghost tm = Some ty'"
  proof -
    fix nm tm assume mem: "(nm, tm) \<in> set flds"
    then obtain i where i_lt: "i < length flds" and fld_i: "flds ! i = (nm, tm)"
      by (auto simp: in_set_conv_nth)
    from la2 i_lt have "map (\<lambda>(name, tm). core_term_type env ghost tm) flds ! i = Some (tys ! i)"
      by (auto simp: list_all2_conv_all_nth)
    thus "\<exists>ty'. core_term_type env ghost tm = Some ty'"
      using i_lt fld_i by simp
  qed
  have map_eq: "map (\<lambda>(name, y). core_term_type env' ghost y) flds =
                map (\<lambda>(name, y). core_term_type env ghost y) flds"
  proof (rule map_cong, simp)
    fix p assume p_in: "p \<in> set flds"
    obtain nm tm where p_eq: "p = (nm, tm)" by (cases p)
    from p_in p_eq all_some obtain ty' where
      tm_ty: "core_term_type env ghost tm = Some ty'" by blast
    from IH p_in p_eq tm_ty have
      tm_ty': "core_term_type env' ghost tm = Some ty'" by blast
    show "(case p of (name, y) \<Rightarrow> core_term_type env' ghost y) =
          (case p of (name, y) \<Rightarrow> core_term_type env ghost y)"
      using p_eq tm_ty tm_ty' by simp
  qed
  from CoreTm_Record.prems(3) show ?case by (auto simp: map_eq split: if_splits)
next
  case (CoreTm_RecordProj tm fldName)
  from CoreTm_RecordProj.prems(3) obtain fieldTypes where
    tm_ty: "core_term_type env ghost tm = Some (CoreTy_Record fieldTypes)" and
    ty_eq: "map_of fieldTypes fldName = Some ty"
    by (auto split: option.splits CoreType.splits)
  have tm_ty': "core_term_type env' ghost tm = Some (CoreTy_Record fieldTypes)"
    using CoreTm_RecordProj.IH[OF CoreTm_RecordProj.prems(1,2) tm_ty] .
  show ?case using tm_ty' ty_eq by simp
next
  case (CoreTm_ArrayProj arr idxTms)
  note ext = CoreTm_ArrayProj.prems(1) and cons = CoreTm_ArrayProj.prems(2)
  from CoreTm_ArrayProj.prems(3) obtain elemTy dims where
    arr_ty: "core_term_type env ghost arr = Some (CoreTy_Array elemTy dims)" and
    len_eq: "length idxTms = length dims" and
    idxs_ty: "list_all (\<lambda>tm. core_term_type env ghost tm =
                              Some (CoreTy_FiniteInt Unsigned IntBits_64)) idxTms" and
    ty_eq: "ty = elemTy"
    by (auto split: option.splits CoreType.splits if_splits)
  have arr_ty': "core_term_type env' ghost arr = Some (CoreTy_Array elemTy dims)"
    using CoreTm_ArrayProj.IH(1)[OF ext cons arr_ty] .
  have idxs_ty': "list_all (\<lambda>tm. core_term_type env' ghost tm =
                                  Some (CoreTy_FiniteInt Unsigned IntBits_64)) idxTms"
    unfolding list_all_iff
  proof
    fix x assume x_in: "x \<in> set idxTms"
    have "core_term_type env ghost x = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
      using idxs_ty x_in by (simp add: list_all_iff)
    then show "core_term_type env' ghost x = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
      using CoreTm_ArrayProj.IH(2)[OF x_in ext cons] by blast
  qed
  show ?case using arr_ty' len_eq idxs_ty' ty_eq by simp
next
  case (CoreTm_VariantProj tm ctorName)
  note ext = CoreTm_VariantProj.prems(1) and cons = CoreTm_VariantProj.prems(2)
  from CoreTm_VariantProj.prems(3) obtain dtName tyArgs dtName2 tyvars payloadTy where
    tm_ty: "core_term_type env ghost tm = Some (CoreTy_Datatype dtName tyArgs)" and
    ctor_lk: "fmlookup (TE_DataCtors env) ctorName = Some (dtName2, tyvars, payloadTy)" and
    name_eq: "dtName = dtName2" and
    len_eq: "length tyArgs = length tyvars" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy"
    by (auto split: option.splits CoreType.splits if_splits)
  have tm_ty': "core_term_type env' ghost tm = Some (CoreTy_Datatype dtName tyArgs)"
    using CoreTm_VariantProj.IH[OF ext cons tm_ty] .
  have ctor_lk': "fmlookup (TE_DataCtors env') ctorName = Some (dtName2, tyvars, payloadTy)"
    using ext ctor_lk unfolding tyenv_extends_def by blast
  show ?case using tm_ty' ctor_lk' name_eq len_eq ty_eq by simp
next
  case (CoreTm_Match scrut arms)
  note ext = CoreTm_Match.prems(1) and cons = CoreTm_Match.prems(2)
  from CoreTm_Match.prems(3) obtain scrutTy where
    scrut_ty: "core_term_type env ghost scrut = Some scrutTy"
    by (auto split: option.splits)
  have scrut_ty': "core_term_type env' ghost scrut = Some scrutTy"
    using CoreTm_Match.IH(1)[OF ext cons scrut_ty] .
  from CoreTm_Match.prems(3) scrut_ty have arms_nonempty: "arms \<noteq> []"
    by (auto split: option.splits if_splits)
  let ?pats = "map fst arms"
  from CoreTm_Match.prems(3) scrut_ty arms_nonempty have
    pat_compat: "list_all (\<lambda>p. pattern_compatible env p scrutTy) ?pats"
    by (auto split: option.splits if_splits simp: Let_def)
  have pat_compat': "list_all (\<lambda>p. pattern_compatible env' p scrutTy) ?pats"
    using pat_compat pattern_compatible_tyenv_extends[OF ext]
    by (auto simp: list_all_iff)
  have match_unfold: "core_term_type env ghost (CoreTm_Match scrut arms) =
    (let pats = map fst arms; bodies = map snd arms in
      if arms = [] then None
      else if \<not> list_all (\<lambda>p. pattern_compatible env p scrutTy) pats then None
      else (case core_term_type env ghost (snd (hd arms)) of
              None \<Rightarrow> None
            | Some resultTy \<Rightarrow>
                if list_all (\<lambda>body. core_term_type env ghost body = Some resultTy) (tl bodies)
                then Some resultTy
                else None))"
    using scrut_ty by simp
  from CoreTm_Match.prems(3) match_unfold arms_nonempty pat_compat
  obtain firstBodyTy where
    first_ty: "core_term_type env ghost (snd (hd arms)) = Some firstBodyTy" and
    ty_eq: "ty = firstBodyTy" and
    rest_ty: "list_all (\<lambda>body. core_term_type env ghost body = Some firstBodyTy)
                       (tl (map snd arms))"
    by (auto simp: Let_def split: option.splits if_splits)
  have hd_in: "snd (hd arms) \<in> snd ` set arms"
    using arms_nonempty by (cases arms) auto
  have bodies_IH: "\<And>body ty'. body \<in> snd ` set arms \<Longrightarrow>
                              core_term_type env ghost body = Some ty' \<Longrightarrow>
                              core_term_type env' ghost body = Some ty'"
    using CoreTm_Match.IH(2) ext cons by fastforce
  have first_ty': "core_term_type env' ghost (snd (hd arms)) = Some firstBodyTy"
    using bodies_IH[OF hd_in first_ty] .
  have tl_in: "\<And>body. body \<in> set (tl (map snd arms)) \<Longrightarrow> body \<in> snd ` set arms"
    by (cases arms) auto
  have rest_ty': "list_all (\<lambda>body. core_term_type env' ghost body = Some firstBodyTy)
                           (tl (map snd arms))"
    unfolding list_all_iff
  proof
    fix x assume x_in: "x \<in> set (tl (map snd arms))"
    have "core_term_type env ghost x = Some firstBodyTy"
      using rest_ty x_in by (simp add: list_all_iff)
    then show "core_term_type env' ghost x = Some firstBodyTy"
      using bodies_IH[OF tl_in[OF x_in]] by blast
  qed
  show ?case
    using scrut_ty' arms_nonempty pat_compat' first_ty' rest_ty' ty_eq
    by (simp add: Let_def)
next
  case (CoreTm_Sizeof tm)
  from CoreTm_Sizeof.prems(3) obtain elemTy dims where
    tm_ty: "core_term_type env ghost tm = Some (CoreTy_Array elemTy dims)"
    by (auto split: option.splits CoreType.splits if_splits)
  have tm_ty': "core_term_type env' ghost tm = Some (CoreTy_Array elemTy dims)"
    using CoreTm_Sizeof.IH[OF CoreTm_Sizeof.prems(1,2) tm_ty] .
  show ?case using CoreTm_Sizeof.prems(3) tm_ty tm_ty'
    by (auto split: option.splits CoreType.splits if_splits)
next
  case (CoreTm_Allocated tm)
  show ?case
  proof (cases ghost)
    case NotGhost
    with CoreTm_Allocated.prems(3) show ?thesis by simp
  next
    case Ghost
    with CoreTm_Allocated.prems(3) obtain tmTy where
      tm_ty: "core_term_type env Ghost tm = Some tmTy" and ty_eq: "ty = CoreTy_Bool"
      by (auto split: option.splits)
    have tm_ty': "core_term_type env' Ghost tm = Some tmTy"
      using CoreTm_Allocated.IH[OF CoreTm_Allocated.prems(1,2) tm_ty] .
    show ?thesis using Ghost tm_ty' ty_eq by simp
  qed
next
  case (CoreTm_Old tm)
  show ?case
  proof (cases ghost)
    case NotGhost
    with CoreTm_Old.prems(3) show ?thesis by simp
  next
    case Ghost
    then have "core_term_type env Ghost tm = Some ty"
      using CoreTm_Old.prems(3) by simp
    then have "core_term_type env' Ghost tm = Some ty"
      using CoreTm_Old.IH[OF CoreTm_Old.prems(1,2)] by blast
    then show ?thesis using Ghost by simp
  qed
next
  case (CoreTm_Default tyD)
  from CoreTm_Default.prems(3) have
    wk: "is_well_kinded env tyD" and
    rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env tyD" and
    ty_eq: "ty = tyD"
    by (auto split: if_splits)
  have wk': "is_well_kinded env' tyD"
    using is_well_kinded_tyenv_extends[OF CoreTm_Default.prems(1) wk] .
  have rt': "ghost = NotGhost \<longrightarrow> is_runtime_type env' tyD"
    using rt is_runtime_type_tyenv_extends[OF CoreTm_Default.prems(1) wk] by blast
  show ?case using wk' rt' ty_eq by simp
qed simp_all


(* ========================================================================== *)
(* Lvalue checks under extension                                              *)
(* ========================================================================== *)

(* Writability only reads TE_LocalVars and TE_ConstLocals, which are pinned
   equal, so it is a plain equality (globals - old or new - are never
   writable). *)
lemma is_writable_lvalue_tyenv_extends:
  assumes ext: "tyenv_extends env env'"
  shows "is_writable_lvalue env' tm = is_writable_lvalue env tm"
proof -
  have lv: "TE_LocalVars env' = TE_LocalVars env"
    and cl: "TE_ConstLocals env' = TE_ConstLocals env"
    using ext unfolding tyenv_extends_def by blast+
  show ?thesis
    by (induction tm) (auto simp: tyenv_var_writable_def lv cl)
qed

(* The base variable of a well-typed lvalue is bound: typing an lvalue
   ultimately types its base CoreTm_Var, whose rule performs the lookup. *)
lemma lvalue_base_name_lookup:
  assumes "lvalue_base_name tm = Some name"
    and "core_term_type env ghost tm = Some ty"
  shows "\<exists>vty. tyenv_lookup_var env name = Some vty"
  using assms
proof (induction tm arbitrary: ty)
  case (CoreTm_Var n)
  then show ?case by (auto split: option.splits if_splits)
next
  case (CoreTm_RecordProj tm fld)
  have base: "lvalue_base_name tm = Some name"
    using CoreTm_RecordProj.prems(1) by simp
  from CoreTm_RecordProj.prems(2) obtain fieldTypes where
    t: "core_term_type env ghost tm = Some (CoreTy_Record fieldTypes)"
    by (auto split: option.splits CoreType.splits)
  show ?case using CoreTm_RecordProj.IH[OF base t] .
next
  case (CoreTm_VariantProj tm ctorName)
  have base: "lvalue_base_name tm = Some name"
    using CoreTm_VariantProj.prems(1) by simp
  from CoreTm_VariantProj.prems(2) obtain tmTy where
    t: "core_term_type env ghost tm = Some tmTy"
    by (auto split: option.splits)
  show ?case using CoreTm_VariantProj.IH[OF base t] .
next
  case (CoreTm_ArrayProj arr idxTms)
  have base: "lvalue_base_name arr = Some name"
    using CoreTm_ArrayProj.prems(1) by simp
  from CoreTm_ArrayProj.prems(2) obtain arrTy where
    t: "core_term_type env ghost arr = Some arrTy"
    by (auto split: option.splits)
  show ?case using CoreTm_ArrayProj.IH(1)[OF base t] .
qed simp_all

(* The ghost-write discipline is preserved for lvalues that typecheck: the
   typing pins the base variable into the old environment, where its ghost
   status is unchanged. (Without the typing hypothesis this would be false:
   an unbound base name could be a ghost global of the extension.) *)
lemma ghost_lvalue_ok_tyenv_extends:
  assumes ext: "tyenv_extends env env'"
    and tm_ty: "core_term_type env ghost0 tm = Some ty"
    and ok: "ghost_lvalue_ok env ghost tm"
  shows "ghost_lvalue_ok env' ghost tm"
proof (cases ghost)
  case NotGhost
  then show ?thesis by simp
next
  case Ghost
  show ?thesis
  proof (cases "lvalue_base_name tm")
    case None
    with Ghost ok show ?thesis unfolding ghost_lvalue_ok_def by simp
  next
    case (Some name)
    with Ghost ok have vg: "tyenv_var_ghost env name"
      unfolding ghost_lvalue_ok_def by simp
    obtain vty where lk: "tyenv_lookup_var env name = Some vty"
      using lvalue_base_name_lookup[OF Some tm_ty] by blast
    have "tyenv_var_ghost env' name = tyenv_var_ghost env name"
      using tyenv_extends_var_ghost[OF ext lk] .
    with vg Some Ghost show ?thesis unfolding ghost_lvalue_ok_def by simp
  qed
qed


(* ========================================================================== *)
(* Impure calls and casts under extension                                     *)
(* ========================================================================== *)

(* Casts only check integer-ness (env-free) and, in NotGhost mode, that the
   target type is runtime - and an integer type's runtime-ness transfers
   because integer types are well-kinded in any env. *)
lemma cast_result_type_tyenv_extends:
  assumes ext: "tyenv_extends env env'"
    and c: "cast_result_type env ghost retTy castOpt = Some ty"
  shows "cast_result_type env' ghost retTy castOpt = Some ty"
proof (cases castOpt)
  case None
  with c show ?thesis by (simp add: cast_result_type_def)
next
  case (Some t)
  with c have int_ret: "is_integer_type retTy" and int_t: "is_integer_type t"
    and rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env t" and ty_eq: "ty = t"
    unfolding cast_result_type_def by (auto split: if_splits)
  have rt': "ghost = NotGhost \<longrightarrow> is_runtime_type env' t"
    using rt is_runtime_type_tyenv_extends[OF ext is_integer_type_well_kinded[OF int_t]]
    by blast
  show ?thesis using Some int_ret int_t rt' ty_eq
    unfolding cast_result_type_def by simp
qed

(* The impure-call check under extension. Mirrors
   core_impure_call_type_irrelevant_tyvar: extract with
   core_impure_call_type_fn_facts, transfer each embedded check, rebuild the
   per-argument Var/Ref list_all2 index-wise. *)
lemma core_impure_call_type_tyenv_extends:
  assumes ext: "tyenv_extends env env'"
    and cons: "tyenv_ctors_consistent env"
    and ct: "core_impure_call_type env ghost fnName tyArgs tmArgs = Some ty"
  shows "core_impure_call_type env' ghost fnName tyArgs tmArgs = Some ty"
proof -
  from core_impure_call_type_fn_facts[OF ct] obtain funInfo where
    fi: "fmlookup (TE_Functions env) fnName = Some funInfo" and
    len_ty: "length tyArgs = length (FI_TyArgs funInfo)" and
    wk: "list_all (is_well_kinded env) tyArgs" and
    rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) tyArgs" and
    fn_ng: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost" and
    len_tm: "length tmArgs = length (FI_TmArgs funInfo)" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo)" and
    l2_pure: "list_all2 (\<lambda>tm expectedTy.
                  case core_term_type env ghost tm of None \<Rightarrow> False
                  | Some actualTy \<Rightarrow> actualTy = expectedTy)
                tmArgs
                (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo))" and
    ref_lv: "\<forall>i < length tmArgs.
                snd (FI_TmArgs funInfo ! i) = Ref
                  \<longrightarrow> is_writable_lvalue env (tmArgs ! i)
                      \<and> ghost_lvalue_ok env ghost (tmArgs ! i)"
    by blast

  have fi': "fmlookup (TE_Functions env') fnName = Some funInfo"
    using ext fi unfolding tyenv_extends_def by blast
  have wk': "list_all (is_well_kinded env') tyArgs"
    using wk is_well_kinded_tyenv_extends[OF ext] by (fastforce simp: list_all_iff)
  have rt': "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env') tyArgs"
    using rt wk is_runtime_type_tyenv_extends[OF ext] by (fastforce simp: list_all_iff)
  have l2_pure': "list_all2 (\<lambda>tm expectedTy.
                  case core_term_type env' ghost tm of None \<Rightarrow> False
                  | Some actualTy \<Rightarrow> actualTy = expectedTy)
                tmArgs
                (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo))"
    using l2_pure core_term_type_tyenv_extends[OF ext cons]
    by (elim list_all2_mono) (auto split: option.splits)

  \<comment> \<open>Rebuild the full per-argument (Var/Ref) check for the extended env.\<close>
  let ?P' = "\<lambda>(tm, vor) expectedTy.
                 case vor of
                   Var \<Rightarrow> (case core_term_type env' ghost tm of None \<Rightarrow> False
                            | Some actualTy \<Rightarrow> actualTy = expectedTy)
                 | Ref \<Rightarrow> is_writable_lvalue env' tm
                          \<and> ghost_lvalue_ok env' ghost tm
                          \<and> core_term_type env' ghost tm = Some expectedTy"
  let ?zts = "zip tmArgs (map (\<lambda>(_, vor). vor) (FI_TmArgs funInfo))"
  let ?exps = "map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                    (FI_TmArgs funInfo)"
  have len_zts: "length ?zts = length ?exps" using len_tm by simp
  have nth_pred: "\<And>i. i < length ?zts \<Longrightarrow> ?P' (?zts ! i) (?exps ! i)"
  proof -
    fix i assume i_lt: "i < length ?zts"
    hence i_lt_tm: "i < length tmArgs" using len_tm by simp
    with len_tm have i_lt_fi: "i < length (FI_TmArgs funInfo)" by simp
    obtain ti vor where fi_arg: "FI_TmArgs funInfo ! i = (ti, vor)"
      by (cases "FI_TmArgs funInfo ! i") auto
    have zip_nth: "?zts ! i = (tmArgs ! i, vor)"
      using i_lt_tm i_lt_fi fi_arg by simp
    have exp_nth: "?exps ! i = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ti"
      using i_lt_fi fi_arg by simp
    have pure_env_i: "case core_term_type env ghost (tmArgs ! i) of None \<Rightarrow> False
                  | Some actualTy \<Rightarrow> actualTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ti"
      using list_all2_nthD[OF l2_pure] i_lt_tm len_tm exp_nth by metis
    have pure_i: "case core_term_type env' ghost (tmArgs ! i) of None \<Rightarrow> False
                  | Some actualTy \<Rightarrow> actualTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ti"
      using list_all2_nthD[OF l2_pure'] i_lt_tm len_tm exp_nth by metis
    show "?P' (?zts ! i) (?exps ! i)"
    proof (cases vor)
      case Var
      with zip_nth exp_nth pure_i show ?thesis by simp
    next
      case Ref
      have typed_env: "core_term_type env ghost (tmArgs ! i)
             = Some (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ti)"
        using pure_env_i by (auto split: option.splits)
      have "is_writable_lvalue env (tmArgs ! i)"
        using ref_lv i_lt_tm fi_arg Ref by simp
      hence writ': "is_writable_lvalue env' (tmArgs ! i)"
        using is_writable_lvalue_tyenv_extends[OF ext] by simp
      have "ghost_lvalue_ok env ghost (tmArgs ! i)"
        using ref_lv i_lt_tm fi_arg Ref by simp
      hence glv': "ghost_lvalue_ok env' ghost (tmArgs ! i)"
        using ghost_lvalue_ok_tyenv_extends[OF ext typed_env] by blast
      from pure_i have
        "core_term_type env' ghost (tmArgs ! i)
           = Some (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ti)"
        by (auto split: option.splits)
      with Ref zip_nth exp_nth writ' glv' show ?thesis by simp
    qed
  qed
  have l2_full': "list_all2 ?P' ?zts ?exps"
    using len_zts nth_pred by (simp add: list_all2_conv_all_nth)

  show ?thesis
    unfolding core_impure_call_type_def
    using fi' wk' rt' fn_ng len_ty len_tm l2_full' ty_eq
    by (auto simp: Let_def)
qed


(* ========================================================================== *)
(* Statement typechecking under extension                                     *)
(* ========================================================================== *)

(* tyenv_ctors_consistent only reads TE_DataCtors / TE_Datatypes, both of
   which are among the fixed fields, so it propagates along statement
   execution (used to thread the hypothesis through statement lists). *)
lemma tyenv_ctors_consistent_fixed_eq:
  assumes fe: "tyenv_fixed_eq env env'"
    and cons: "tyenv_ctors_consistent env"
  shows "tyenv_ctors_consistent env'"
proof -
  have "TE_DataCtors env' = TE_DataCtors env" and "TE_Datatypes env' = TE_Datatypes env"
    using fe unfolding tyenv_fixed_eq_def by simp_all
  then show ?thesis using cons unfolding tyenv_ctors_consistent_def by simp
qed

(* The statement-level weakening. Unlike the term level, the output
   environment is existential: env2's output is env2 with the same scope
   updates that env's output applied to env, so the two outputs are again
   related by tyenv_extends. Mirrors core_statement_type_irrelevant_tyvar's
   induction structure. *)
lemma core_statement_type_tyenv_extends:
  "core_statement_type env ghost stmt = Some envOut \<Longrightarrow>
   tyenv_extends env env2 \<Longrightarrow> tyenv_ctors_consistent env \<Longrightarrow>
   \<exists>envOut2. core_statement_type env2 ghost stmt = Some envOut2
             \<and> tyenv_extends envOut envOut2"
and core_statement_list_type_tyenv_extends:
  "core_statement_list_type env ghost stmts = Some envOut \<Longrightarrow>
   tyenv_extends env env2 \<Longrightarrow> tyenv_ctors_consistent env \<Longrightarrow>
   \<exists>envOut2. core_statement_list_type env2 ghost stmts = Some envOut2
             \<and> tyenv_extends envOut envOut2"
proof (induction env ghost stmt and env ghost stmts
       arbitrary: envOut env2 and envOut env2
       rule: core_statement_type_core_statement_list_type.induct)
  \<comment> \<open>VarDecl (Var): adds a local; env2 gets the same-valued updates.\<close>
  case (1 env ghost declGhost varName varTy initTm)
  note ext = "1.prems"(2) and cons = "1.prems"(3)
  from "1.prems"(1) have
    gh: "ghost = Ghost \<longrightarrow> declGhost = Ghost" and
    wk: "is_well_kinded env varTy" and
    rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy" and
    init: "core_term_type env declGhost initTm = Some varTy" and
    out_eq: "envOut = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                  TE_GhostLocals := (if declGhost = Ghost
                                   then finsert varName (TE_GhostLocals env)
                                   else fminus (TE_GhostLocals env) {|varName|}),
                  TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
    by (auto split: if_splits)
  have wk2: "is_well_kinded env2 varTy"
    using is_well_kinded_tyenv_extends[OF ext wk] .
  have rt2: "declGhost = NotGhost \<longrightarrow> is_runtime_type env2 varTy"
    using rt is_runtime_type_tyenv_extends[OF ext wk] by blast
  have init2: "core_term_type env2 declGhost initTm = Some varTy"
    using core_term_type_tyenv_extends[OF ext cons init] .
  let ?out2 = "env2 \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env2),
                  TE_GhostLocals := (if declGhost = Ghost
                                   then finsert varName (TE_GhostLocals env2)
                                   else fminus (TE_GhostLocals env2) {|varName|}),
                  TE_ConstLocals := fminus (TE_ConstLocals env2) {|varName|} \<rparr>"
  have res: "core_statement_type env2 ghost (CoreStmt_VarDecl declGhost varName Var varTy initTm)
               = Some ?out2"
    using gh wk2 rt2 init2 by simp
  have ext_out: "tyenv_extends envOut ?out2"
    using ext unfolding out_eq tyenv_extends_def by simp
  from res ext_out show ?case by blast
next
  \<comment> \<open>VarDeclCall: adds a local of the (optionally cast) call return type.\<close>
  case (2 env ghost declGhost varName varTy castOpt fnName tyArgs argTms)
  note ext = "2.prems"(2) and cons = "2.prems"(3)
  from "2.prems"(1) obtain retTy where
    gh: "ghost = Ghost \<longrightarrow> declGhost = Ghost" and
    wk: "is_well_kinded env varTy" and
    rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy" and
    ct: "core_impure_call_type env declGhost fnName tyArgs argTms = Some retTy" and
    cast: "cast_result_type env declGhost retTy castOpt = Some varTy" and
    out_eq:
      "envOut = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                    TE_GhostLocals := (if declGhost = Ghost
                                     then finsert varName (TE_GhostLocals env)
                                     else fminus (TE_GhostLocals env) {|varName|}),
                    TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
    by (auto split: if_splits option.splits)
  have wk2: "is_well_kinded env2 varTy"
    using is_well_kinded_tyenv_extends[OF ext wk] .
  have rt2: "declGhost = NotGhost \<longrightarrow> is_runtime_type env2 varTy"
    using rt is_runtime_type_tyenv_extends[OF ext wk] by blast
  have ct2: "core_impure_call_type env2 declGhost fnName tyArgs argTms = Some retTy"
    using core_impure_call_type_tyenv_extends[OF ext cons ct] .
  have cast2: "cast_result_type env2 declGhost retTy castOpt = Some varTy"
    using cast_result_type_tyenv_extends[OF ext cast] .
  let ?out2 = "env2 \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env2),
                    TE_GhostLocals := (if declGhost = Ghost
                                     then finsert varName (TE_GhostLocals env2)
                                     else fminus (TE_GhostLocals env2) {|varName|}),
                    TE_ConstLocals := fminus (TE_ConstLocals env2) {|varName|} \<rparr>"
  have res: "core_statement_type env2 ghost
               (CoreStmt_VarDeclCall declGhost varName varTy castOpt fnName tyArgs argTms)
               = Some ?out2"
    using gh wk2 rt2 ct2 cast2 by simp
  have ext_out: "tyenv_extends envOut ?out2"
    using ext unfolding out_eq tyenv_extends_def by simp
  from res ext_out show ?case by blast
next
  \<comment> \<open>VarDecl (Ref): the writability of the initializer (which decides the new
      ref's const-ness) is unchanged under extension.\<close>
  case (3 env ghost declGhost varName varTy initTm)
  note ext = "3.prems"(2) and cons = "3.prems"(3)
  from "3.prems"(1) have
    gh: "ghost = Ghost \<longrightarrow> declGhost = Ghost" and
    wk: "is_well_kinded env varTy" and
    rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy" and
    lv: "is_lvalue initTm" and
    glv: "ghost_lvalue_ok env declGhost initTm" and
    init: "core_term_type env declGhost initTm = Some varTy" and
    out_eq:
      "envOut = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                    TE_GhostLocals := (if declGhost = Ghost
                                     then finsert varName (TE_GhostLocals env)
                                     else fminus (TE_GhostLocals env) {|varName|}),
                    TE_ConstLocals := (if is_writable_lvalue env initTm
                                      then fminus (TE_ConstLocals env) {|varName|}
                                      else finsert varName (TE_ConstLocals env)) \<rparr>"
    by (auto split: if_splits)
  have wk2: "is_well_kinded env2 varTy"
    using is_well_kinded_tyenv_extends[OF ext wk] .
  have rt2: "declGhost = NotGhost \<longrightarrow> is_runtime_type env2 varTy"
    using rt is_runtime_type_tyenv_extends[OF ext wk] by blast
  have glv2: "ghost_lvalue_ok env2 declGhost initTm"
    using ghost_lvalue_ok_tyenv_extends[OF ext init glv] .
  have init2: "core_term_type env2 declGhost initTm = Some varTy"
    using core_term_type_tyenv_extends[OF ext cons init] .
  have wl_eq: "is_writable_lvalue env2 initTm = is_writable_lvalue env initTm"
    using is_writable_lvalue_tyenv_extends[OF ext] .
  let ?out2 = "env2 \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env2),
                    TE_GhostLocals := (if declGhost = Ghost
                                     then finsert varName (TE_GhostLocals env2)
                                     else fminus (TE_GhostLocals env2) {|varName|}),
                    TE_ConstLocals := (if is_writable_lvalue env2 initTm
                                      then fminus (TE_ConstLocals env2) {|varName|}
                                      else finsert varName (TE_ConstLocals env2)) \<rparr>"
  have res: "core_statement_type env2 ghost (CoreStmt_VarDecl declGhost varName Ref varTy initTm)
               = Some ?out2"
    using gh wk2 rt2 lv glv2 init2 by simp
  have ext_out: "tyenv_extends envOut ?out2"
    using ext unfolding out_eq tyenv_extends_def by (simp add: wl_eq)
  from res ext_out show ?case by blast
next
  \<comment> \<open>Assign: env unchanged.\<close>
  case (4 env ghost assignGhost lhsTm rhsTm)
  note ext = "4.prems"(2) and cons = "4.prems"(3)
  from "4.prems"(1) obtain lhsTy where
    gh: "ghost = Ghost \<longrightarrow> assignGhost = Ghost" and
    wl: "is_writable_lvalue env lhsTm" and
    glv: "ghost_lvalue_ok env assignGhost lhsTm" and
    lhs: "core_term_type env assignGhost lhsTm = Some lhsTy" and
    rhs: "core_term_type env assignGhost rhsTm = Some lhsTy" and
    out_eq: "envOut = env"
    by (auto split: if_splits option.splits)
  have wl2: "is_writable_lvalue env2 lhsTm"
    using wl is_writable_lvalue_tyenv_extends[OF ext] by simp
  have glv2: "ghost_lvalue_ok env2 assignGhost lhsTm"
    using ghost_lvalue_ok_tyenv_extends[OF ext lhs glv] .
  have lhs2: "core_term_type env2 assignGhost lhsTm = Some lhsTy"
    using core_term_type_tyenv_extends[OF ext cons lhs] .
  have rhs2: "core_term_type env2 assignGhost rhsTm = Some lhsTy"
    using core_term_type_tyenv_extends[OF ext cons rhs] .
  have res: "core_statement_type env2 ghost (CoreStmt_Assign assignGhost lhsTm rhsTm) = Some env2"
    using gh wl2 glv2 lhs2 rhs2 by simp
  from res ext show ?case using out_eq by blast
next
  \<comment> \<open>AssignCall: env unchanged.\<close>
  case (5 env ghost assignGhost lhsTm castOpt fnName tyArgs argTms)
  note ext = "5.prems"(2) and cons = "5.prems"(3)
  from "5.prems"(1) have
    pre: "(ghost = Ghost \<longrightarrow> assignGhost = Ghost) \<and> is_writable_lvalue env lhsTm
            \<and> ghost_lvalue_ok env assignGhost lhsTm"
    by (simp split: if_splits)
  hence gh: "ghost = Ghost \<longrightarrow> assignGhost = Ghost" and wl: "is_writable_lvalue env lhsTm"
    and glv: "ghost_lvalue_ok env assignGhost lhsTm"
    by simp_all
  from "5.prems"(1) pre obtain lhsTy where
    lhs: "core_term_type env assignGhost lhsTm = Some lhsTy"
    by (simp split: option.splits)
  from "5.prems"(1) pre lhs obtain retTy where
    ct: "core_impure_call_type env assignGhost fnName tyArgs argTms = Some retTy"
    by (simp split: option.splits)
  from "5.prems"(1) pre lhs ct have
    cast: "cast_result_type env assignGhost retTy castOpt = Some lhsTy" and
    out_eq: "envOut = env"
    by (simp split: if_splits)+
  have wl2: "is_writable_lvalue env2 lhsTm"
    using wl is_writable_lvalue_tyenv_extends[OF ext] by simp
  have glv2: "ghost_lvalue_ok env2 assignGhost lhsTm"
    using ghost_lvalue_ok_tyenv_extends[OF ext lhs glv] .
  have lhs2: "core_term_type env2 assignGhost lhsTm = Some lhsTy"
    using core_term_type_tyenv_extends[OF ext cons lhs] .
  have ct2: "core_impure_call_type env2 assignGhost fnName tyArgs argTms = Some retTy"
    using core_impure_call_type_tyenv_extends[OF ext cons ct] .
  have cast2: "cast_result_type env2 assignGhost retTy castOpt = Some lhsTy"
    using cast_result_type_tyenv_extends[OF ext cast] .
  have res: "core_statement_type env2 ghost
               (CoreStmt_AssignCall assignGhost lhsTm castOpt fnName tyArgs argTms) = Some env2"
    using gh wl2 glv2 lhs2 ct2 cast2 by simp
  from res ext show ?case using out_eq by blast
next
  \<comment> \<open>Return: TE_ReturnType and TE_FunctionGhost are pinned equal.\<close>
  case (6 env ghost tm)
  note ext = "6.prems"(2) and cons = "6.prems"(3)
  from "6.prems"(1) have
    gh: "ghost = TE_FunctionGhost env" and
    tm: "core_term_type env ghost tm = Some (TE_ReturnType env)" and
    out_eq: "envOut = env"
    by (auto split: if_splits)
  have fg_eq: "TE_FunctionGhost env2 = TE_FunctionGhost env"
    and ret_eq: "TE_ReturnType env2 = TE_ReturnType env"
    using ext unfolding tyenv_extends_def by blast+
  have tm2: "core_term_type env2 ghost tm = Some (TE_ReturnType env)"
    using core_term_type_tyenv_extends[OF ext cons tm] .
  have res: "core_statement_type env2 ghost (CoreStmt_Return tm) = Some env2"
    using gh tm2 by (simp add: fg_eq ret_eq)
  from res ext show ?case using out_eq by blast
next
  \<comment> \<open>Swap: env unchanged.\<close>
  case (7 env ghost swapGhost lhsTm rhsTm)
  note ext = "7.prems"(2) and cons = "7.prems"(3)
  from "7.prems"(1) obtain lhsTy where
    gh: "ghost = Ghost \<longrightarrow> swapGhost = Ghost" and
    wl: "is_writable_lvalue env lhsTm" and
    wr: "is_writable_lvalue env rhsTm" and
    glvL: "ghost_lvalue_ok env swapGhost lhsTm" and
    glvR: "ghost_lvalue_ok env swapGhost rhsTm" and
    lhs: "core_term_type env swapGhost lhsTm = Some lhsTy" and
    rhs: "core_term_type env swapGhost rhsTm = Some lhsTy" and
    out_eq: "envOut = env"
    by (auto split: if_splits option.splits)
  have wl2: "is_writable_lvalue env2 lhsTm"
    using wl is_writable_lvalue_tyenv_extends[OF ext] by simp
  have wr2: "is_writable_lvalue env2 rhsTm"
    using wr is_writable_lvalue_tyenv_extends[OF ext] by simp
  have glvL2: "ghost_lvalue_ok env2 swapGhost lhsTm"
    using ghost_lvalue_ok_tyenv_extends[OF ext lhs glvL] .
  have glvR2: "ghost_lvalue_ok env2 swapGhost rhsTm"
    using ghost_lvalue_ok_tyenv_extends[OF ext rhs glvR] .
  have lhs2: "core_term_type env2 swapGhost lhsTm = Some lhsTy"
    using core_term_type_tyenv_extends[OF ext cons lhs] .
  have rhs2: "core_term_type env2 swapGhost rhsTm = Some lhsTy"
    using core_term_type_tyenv_extends[OF ext cons rhs] .
  have res: "core_statement_type env2 ghost (CoreStmt_Swap swapGhost lhsTm rhsTm) = Some env2"
    using gh wl2 wr2 glvL2 glvR2 lhs2 rhs2 by simp
  from res ext show ?case using out_eq by blast
next
  \<comment> \<open>Assert: the goal env applies the same update on both sides (TE_ProofGoal
      is pinned equal, so the "assert *" branch reads the same goal).\<close>
  case (8 env ghost condOpt proofBody)
  note ext = "8.prems"(2) and cons = "8.prems"(3)
  let ?goalEnv = "\<lambda>e :: CoreTyEnv.
                    e \<lparr> TE_ProofGoal := (case condOpt of Some condTm \<Rightarrow> Some condTm
                                                        | None \<Rightarrow> TE_ProofGoal e),
                        TE_ProofTopLevel := True \<rparr>"
  let ?condOk = "case condOpt of
                   Some condTm \<Rightarrow> core_term_type env Ghost condTm = Some CoreTy_Bool
                 | None \<Rightarrow> TE_ProofGoal env \<noteq> None"
  from "8.prems"(1) obtain bodyEnv where
    condOk: "?condOk" and
    body: "core_statement_list_type (?goalEnv env) Ghost proofBody = Some bodyEnv" and
    out_eq: "envOut = env"
    by (auto simp: Let_def split: if_splits option.splits)
  have pg_eq: "TE_ProofGoal env2 = TE_ProofGoal env"
    using ext unfolding tyenv_extends_def by blast
  have ext_goal: "tyenv_extends (?goalEnv env) (?goalEnv env2)"
    using ext unfolding tyenv_extends_def by (cases condOpt) auto
  have cons_goal: "tyenv_ctors_consistent (?goalEnv env)"
    using cons unfolding tyenv_ctors_consistent_def by simp
  from "8.IH"[OF refl refl refl condOk body ext_goal cons_goal] obtain bodyEnv2 where
    body2: "core_statement_list_type (?goalEnv env2) Ghost proofBody = Some bodyEnv2"
    by blast
  have condOk2: "case condOpt of
                   Some condTm \<Rightarrow> core_term_type env2 Ghost condTm = Some CoreTy_Bool
                 | None \<Rightarrow> TE_ProofGoal env2 \<noteq> None"
    using condOk core_term_type_tyenv_extends[OF ext cons] pg_eq by (cases condOpt) auto
  have res: "core_statement_type env2 ghost (CoreStmt_Assert condOpt proofBody) = Some env2"
    using condOk2 body2 by (simp add: Let_def)
  from res ext show ?case using out_eq by blast
next
  \<comment> \<open>Assume: env unchanged.\<close>
  case (9 env ghost tm)
  note ext = "9.prems"(2) and cons = "9.prems"(3)
  from "9.prems"(1) have
    tm: "core_term_type env Ghost tm = Some CoreTy_Bool" and out_eq: "envOut = env"
    by (auto split: if_splits)
  have tm2: "core_term_type env2 Ghost tm = Some CoreTy_Bool"
    using core_term_type_tyenv_extends[OF ext cons tm] .
  have res: "core_statement_type env2 ghost (CoreStmt_Assume tm) = Some env2"
    using tm2 by simp
  from res ext show ?case using out_eq by blast
next
  \<comment> \<open>ShowHide: no checks.\<close>
  case (10 env ghost sh name)
  from "10.prems"(1) have "envOut = env" by simp
  then show ?case using "10.prems"(2) by auto
next
  \<comment> \<open>Match: env unchanged; arm bodies checked under TE_ProofTopLevel := False.\<close>
  case (11 env ghost matchGhost scrut arms)
  note ext = "11.prems"(2) and cons = "11.prems"(3)
  from "11.prems"(1) obtain scrutTy where
    gh: "ghost = Ghost \<longrightarrow> matchGhost = Ghost" and
    scrut: "core_term_type env matchGhost scrut = Some scrutTy" and
    pats: "list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst arms)" and
    bodies: "list_all (\<lambda>body. core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>)
                                  matchGhost body \<noteq> None) (map snd arms)" and
    out_eq: "envOut = env"
    by (auto simp: Let_def split: if_splits option.splits)
  have scrut2: "core_term_type env2 matchGhost scrut = Some scrutTy"
    using core_term_type_tyenv_extends[OF ext cons scrut] .
  have pats2: "list_all (\<lambda>p. pattern_compatible env2 p scrutTy) (map fst arms)"
    using pats pattern_compatible_tyenv_extends[OF ext] by (auto simp: list_all_iff)
  have pats_nn: "\<not> \<not> list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst arms)"
    using pats by simp
  have ext_f: "tyenv_extends (env \<lparr> TE_ProofTopLevel := False \<rparr>)
                             (env2 \<lparr> TE_ProofTopLevel := False \<rparr>)"
    using ext unfolding tyenv_extends_def by simp
  have cons_f: "tyenv_ctors_consistent (env \<lparr> TE_ProofTopLevel := False \<rparr>)"
    using cons unfolding tyenv_ctors_consistent_def by simp
  have bodies2: "list_all (\<lambda>body. core_statement_list_type (env2 \<lparr> TE_ProofTopLevel := False \<rparr>)
                                     matchGhost body \<noteq> None) (map snd arms)"
    unfolding list_all_iff
  proof (rule ballI)
    fix body assume body_in: "body \<in> set (map snd arms)"
    from bodies[unfolded list_all_iff] body_in
    have "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) matchGhost body \<noteq> None"
      by blast
    then obtain bEnv where
      bsome: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) matchGhost body
                = Some bEnv"
      by blast
    from "11.IH"[OF gh scrut refl refl pats_nn body_in bsome ext_f cons_f] obtain bEnv2 where
      "core_statement_list_type (env2 \<lparr> TE_ProofTopLevel := False \<rparr>) matchGhost body = Some bEnv2"
      by blast
    then show "core_statement_list_type (env2 \<lparr> TE_ProofTopLevel := False \<rparr>) matchGhost body
                 \<noteq> None"
      by simp
  qed
  have res: "core_statement_type env2 ghost (CoreStmt_Match matchGhost scrut arms) = Some env2"
    using gh scrut2 pats2 bodies2 by (simp add: Let_def)
  from res ext show ?case using out_eq by blast
next
  \<comment> \<open>While: env unchanged; body checked under TE_ProofTopLevel := False.\<close>
  case (12 env ghost whileGhost condTm invars decrTm body)
  note ext = "12.prems"(2) and cons = "12.prems"(3)
  from "12.prems"(1) obtain decrTy bodyEnv where
    gh: "ghost = Ghost \<longrightarrow> whileGhost = Ghost" and
    cond: "core_term_type env whileGhost condTm = Some CoreTy_Bool" and
    invs: "list_all (\<lambda>inv. core_term_type env Ghost inv = Some CoreTy_Bool) invars" and
    decr: "core_term_type env Ghost decrTm = Some decrTy" and
    decr_valid: "is_valid_decreases_type decrTy" and
    body: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) whileGhost body
             = Some bodyEnv" and
    out_eq: "envOut = env"
    by (auto split: if_splits option.splits CoreType.splits)
  have cond2: "core_term_type env2 whileGhost condTm = Some CoreTy_Bool"
    using core_term_type_tyenv_extends[OF ext cons cond] .
  have invs2: "list_all (\<lambda>inv. core_term_type env2 Ghost inv = Some CoreTy_Bool) invars"
    using invs core_term_type_tyenv_extends[OF ext cons] by (fastforce simp: list_all_iff)
  have decr2: "core_term_type env2 Ghost decrTm = Some decrTy"
    using core_term_type_tyenv_extends[OF ext cons decr] .
  have ext_f: "tyenv_extends (env \<lparr> TE_ProofTopLevel := False \<rparr>)
                             (env2 \<lparr> TE_ProofTopLevel := False \<rparr>)"
    using ext unfolding tyenv_extends_def by simp
  have cons_f: "tyenv_ctors_consistent (env \<lparr> TE_ProofTopLevel := False \<rparr>)"
    using cons unfolding tyenv_ctors_consistent_def by simp
  from "12.IH"[OF gh cond refl invs decr decr_valid body ext_f cons_f] obtain bodyEnv2 where
    body2: "core_statement_list_type (env2 \<lparr> TE_ProofTopLevel := False \<rparr>) whileGhost body
              = Some bodyEnv2"
    by blast
  have res: "core_statement_type env2 ghost (CoreStmt_While whileGhost condTm invars decrTm body)
               = Some env2"
    using gh cond2 invs2 decr2 decr_valid body2 by simp
  from res ext show ?case using out_eq by blast
next
  \<comment> \<open>Obtain: adds a ghost local; the condition is a term checked in the
      extended-by-x env, so the term-level lemma applies there.\<close>
  case (13 env ghost varName varTy condTm)
  note ext = "13.prems"(2) and cons = "13.prems"(3)
  let ?envX = "\<lambda>e :: CoreTyEnv.
                 e \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars e),
                     TE_GhostLocals := finsert varName (TE_GhostLocals e),
                     TE_ConstLocals := fminus (TE_ConstLocals e) {|varName|} \<rparr>"
  from "13.prems"(1) have
    wk: "is_well_kinded env varTy" and
    cond: "core_term_type (?envX env) Ghost condTm = Some CoreTy_Bool" and
    out_eq: "envOut = ?envX env"
    by (auto simp: Let_def split: if_splits)
  have wk2: "is_well_kinded env2 varTy"
    using is_well_kinded_tyenv_extends[OF ext wk] .
  have ext_X: "tyenv_extends (?envX env) (?envX env2)"
    using ext unfolding tyenv_extends_def by simp
  have cons_X: "tyenv_ctors_consistent (?envX env)"
    using cons unfolding tyenv_ctors_consistent_def by simp
  have cond2: "core_term_type (?envX env2) Ghost condTm = Some CoreTy_Bool"
    using core_term_type_tyenv_extends[OF ext_X cons_X cond] .
  have res: "core_statement_type env2 ghost (CoreStmt_Obtain varName varTy condTm)
               = Some (?envX env2)"
    using wk2 cond2 by (simp add: Let_def)
  from res ext_X show ?case using out_eq by blast
next
  \<comment> \<open>Fix: needs a Quant_Forall goal; TE_ProofGoal / TE_ProofTopLevel are pinned equal.\<close>
  case (14 env ghost varName varTy)
  note ext = "14.prems"(2) and cons = "14.prems"(3)
  from "14.prems"(1) obtain qName bodyTm where
    goal: "TE_ProofGoal env = Some (CoreTm_Quantifier Quant_Forall qName varTy bodyTm)" and
    gh: "ghost = Ghost" and wk: "is_well_kinded env varTy" and
    topLevel: "TE_ProofTopLevel env" and
    out_eq: "envOut = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                            TE_GhostLocals := finsert varName (TE_GhostLocals env),
                            TE_ConstLocals := finsert varName (TE_ConstLocals env),
                            TE_ProofGoal := Some bodyTm \<rparr>"
    by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
  have pg_eq: "TE_ProofGoal env2 = TE_ProofGoal env"
    and tl_eq: "TE_ProofTopLevel env2 = TE_ProofTopLevel env"
    using ext unfolding tyenv_extends_def by blast+
  have goal2: "TE_ProofGoal env2 = Some (CoreTm_Quantifier Quant_Forall qName varTy bodyTm)"
    using goal pg_eq by simp
  have wk2: "is_well_kinded env2 varTy"
    using is_well_kinded_tyenv_extends[OF ext wk] .
  let ?out2 = "env2 \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env2),
                      TE_GhostLocals := finsert varName (TE_GhostLocals env2),
                      TE_ConstLocals := finsert varName (TE_ConstLocals env2),
                      TE_ProofGoal := Some bodyTm \<rparr>"
  have res: "core_statement_type env2 ghost (CoreStmt_Fix varName varTy) = Some ?out2"
    using goal2 gh wk2 topLevel tl_eq by simp
  have ext_out: "tyenv_extends envOut ?out2"
    using ext unfolding out_eq tyenv_extends_def by simp
  from res ext_out show ?case by blast
next
  \<comment> \<open>Use: needs a Quant_Exists goal; updates the goal only.\<close>
  case (15 env ghost witnessTm)
  note ext = "15.prems"(2) and cons = "15.prems"(3)
  from "15.prems"(1) obtain qName qVarTy bodyTm where
    goal: "TE_ProofGoal env = Some (CoreTm_Quantifier Quant_Exists qName qVarTy bodyTm)" and
    gh: "ghost = Ghost" and
    wit: "core_term_type env ghost witnessTm = Some qVarTy" and
    topLevel: "TE_ProofTopLevel env" and
    out_eq: "envOut = env \<lparr> TE_ProofGoal := Some bodyTm \<rparr>"
    by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
  have pg_eq: "TE_ProofGoal env2 = TE_ProofGoal env"
    and tl_eq: "TE_ProofTopLevel env2 = TE_ProofTopLevel env"
    using ext unfolding tyenv_extends_def by blast+
  have goal2: "TE_ProofGoal env2 = Some (CoreTm_Quantifier Quant_Exists qName qVarTy bodyTm)"
    using goal pg_eq by simp
  have wit2: "core_term_type env2 ghost witnessTm = Some qVarTy"
    using core_term_type_tyenv_extends[OF ext cons wit] .
  let ?out2 = "env2 \<lparr> TE_ProofGoal := Some bodyTm \<rparr>"
  have res: "core_statement_type env2 ghost (CoreStmt_Use witnessTm) = Some ?out2"
    using goal2 gh wit2 topLevel tl_eq by simp
  have ext_out: "tyenv_extends envOut ?out2"
    using ext unfolding out_eq tyenv_extends_def by simp
  from res ext_out show ?case by blast
next
  \<comment> \<open>Block: env unchanged; body checked under TE_ProofTopLevel := False.\<close>
  case (16 env ghost body)
  note ext = "16.prems"(2) and cons = "16.prems"(3)
  from "16.prems"(1) obtain bodyEnv where
    body: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) ghost body
             = Some bodyEnv" and
    out_eq: "envOut = env"
    by (auto split: option.splits)
  have ext_f: "tyenv_extends (env \<lparr> TE_ProofTopLevel := False \<rparr>)
                             (env2 \<lparr> TE_ProofTopLevel := False \<rparr>)"
    using ext unfolding tyenv_extends_def by simp
  have cons_f: "tyenv_ctors_consistent (env \<lparr> TE_ProofTopLevel := False \<rparr>)"
    using cons unfolding tyenv_ctors_consistent_def by simp
  from "16.IH"[OF body ext_f cons_f] obtain bodyEnv2 where
    body2: "core_statement_list_type (env2 \<lparr> TE_ProofTopLevel := False \<rparr>) ghost body
              = Some bodyEnv2"
    by blast
  have res: "core_statement_type env2 ghost (CoreStmt_Block body) = Some env2"
    using body2 by simp
  from res ext show ?case using out_eq by blast
next
  \<comment> \<open>Empty statement list.\<close>
  case (17 env ghost)
  from "17.prems"(1) have "envOut = env" by simp
  then show ?case using "17.prems"(2) by auto
next
  \<comment> \<open>Cons: thread the extension through head then tail; consistency propagates
      because the head statement leaves the fixed fields unchanged.\<close>
  case (18 env ghost stmt stmts)
  note ext = "18.prems"(2) and cons = "18.prems"(3)
  from "18.prems"(1) obtain envMid where
    head: "core_statement_type env ghost stmt = Some envMid" and
    tail: "core_statement_list_type envMid ghost stmts = Some envOut"
    by (auto split: option.splits)
  from "18.IH"(1)[OF head ext cons] obtain envMid2 where
    head2: "core_statement_type env2 ghost stmt = Some envMid2" and
    ext_mid: "tyenv_extends envMid envMid2"
    by blast
  have cons_mid: "tyenv_ctors_consistent envMid"
    using tyenv_ctors_consistent_fixed_eq[OF core_statement_type_fixed_eq[OF head] cons] .
  from "18.IH"(2)[OF head tail ext_mid cons_mid] obtain envOut2 where
    tail2: "core_statement_list_type envMid2 ghost stmts = Some envOut2" and
    ext_out: "tyenv_extends envOut envOut2"
    by blast
  have res: "core_statement_list_type env2 ghost (stmt # stmts) = Some envOut2"
    using head2 tail2 by simp
  from res ext_out show ?case by blast
qed

end
