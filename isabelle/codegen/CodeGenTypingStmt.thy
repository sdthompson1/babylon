theory CodeGenTypingStmt
  imports CodeGenTypingTerm
begin

declare int_fits.simps [simp del]
declare term_types.simps [simp del]

(* ========================================================================== *)
(* The typing theorem: statements                                             *)
(* ========================================================================== *)

section \<open>Size facts of statements\<close>

(* Every type the lowering of a statement (list) computes a size of fits:
   the types of stmt_types / stmts_types (SizeBound.thy). *)
definition stmt_fits :: "CoreTyEnv \<Rightarrow> CoreStatement \<Rightarrow> bool" where
  "stmt_fits env s = (\<exists>tys. stmt_types env s = Some tys \<and> (\<forall>ty \<in> set tys. fits env ty))"

definition stmts_fits :: "CoreTyEnv \<Rightarrow> CoreStatement list \<Rightarrow> bool" where
  "stmts_fits env ss = (\<exists>tys. stmts_types env ss = Some tys \<and> (\<forall>ty \<in> set tys. fits env ty))"

lemma stmts_fits_Nil [simp]: "stmts_fits env []"
  by (simp add: stmts_fits_def)

(* fits does not look at the local variables. *)
lemma fits_locals_irrelevant:
  assumes "TE_DataCtors env' = TE_DataCtors env" and "TE_DataCtorsByType env' = TE_DataCtorsByType env"
  shows "fits env' ty = fits env ty"
  unfolding fits_def by (rule size_fits_cong_env[OF assms])

lemma fits_nested [simp]: "fits (env \<lparr> TE_ProofTopLevel := b \<rparr>) ty = fits env ty"
  by (rule fits_locals_irrelevant) simp_all

lemma fits_stmt_env:
  assumes "core_statement_type env g s = Some env'"
  shows "fits env' ty = fits env ty"
  using core_statement_type_fixed_eq[OF assms] by (intro fits_locals_irrelevant) (simp_all add: tyenv_fixed_eq_def)

lemma stmts_fits_Cons:
  assumes "stmts_fits env (s # ss)"
  shows "stmt_fits env s"
    and "\<And>env'. core_statement_type env NotGhost s = Some env' \<Longrightarrow> stmts_fits env' ss"
proof -
  from assms obtain l env1 l2 where st: "stmt_types env s = Some l" and ct: "core_statement_type env NotGhost s = Some env1"
    and ss: "stmts_types env1 ss = Some l2" and f: "\<forall>ty \<in> set (l @ l2). fits env ty"
    unfolding stmts_fits_def by (auto split: option.splits)
  show "stmt_fits env s" using st f unfolding stmt_fits_def by auto
  fix env' assume "core_statement_type env NotGhost s = Some env'"
  then have "env' = env1" using ct by simp
  then show "stmts_fits env' ss" using ss f fits_stmt_env[OF ct] unfolding stmts_fits_def by auto
qed

lemma stmt_fits_VarDecl:
  assumes "stmt_fits env (CoreStmt_VarDecl g x vor ty tm)"
  shows "fits env ty" and "term_fits env tm"
  using assms unfolding stmt_fits_def term_fits_def by auto

lemma stmt_fits_VarDeclCall:
  assumes "stmt_fits env (CoreStmt_VarDeclCall g x ty castOpt f tys args)"
  obtains retTy where "core_impure_call_type env NotGhost f tys args = Some retTy"
    and "fits env ty" and "fits env retTy" and "\<And>t. castOpt = Some t \<Longrightarrow> fits env t"
    and "\<forall>ty \<in> set tys. fits env ty" and "\<forall>a \<in> set args. term_fits env a"
proof -
  from assms obtain retTy ls where ct: "core_impure_call_type env NotGhost f tys args = Some retTy"
    and th: "those (map (term_types env) args) = Some ls"
    and f: "\<forall>ty' \<in> set (ty # retTy # (case castOpt of None \<Rightarrow> [] | Some t \<Rightarrow> [t]) @ tys @ concat ls). fits env ty'"
    unfolding stmt_fits_def by (auto split: option.splits)
  show thesis
  proof (rule that[OF ct])
    show "\<forall>a \<in> set args. term_fits env a" using term_fits_of_those[OF th] f by auto
  qed (use f in \<open>auto split: option.splits\<close>)
qed

lemma stmt_fits_Assign:
  assumes "stmt_fits env (CoreStmt_Assign g ty lhs rhs)"
  shows "fits env ty" and "term_fits env lhs" and "term_fits env rhs"
  using assms unfolding stmt_fits_def term_fits_def by (auto split: option.splits)

lemma stmt_fits_AssignCall:
  assumes "stmt_fits env (CoreStmt_AssignCall g lhs castOpt f tys args)"
  obtains retTy where "core_impure_call_type env NotGhost f tys args = Some retTy"
    and "fits env retTy" and "\<And>t. castOpt = Some t \<Longrightarrow> fits env t"
    and "\<forall>ty \<in> set tys. fits env ty" and "term_fits env lhs" and "\<forall>a \<in> set args. term_fits env a"
proof -
  from assms obtain retTy l ls where ct: "core_impure_call_type env NotGhost f tys args = Some retTy"
    and tl: "term_types env lhs = Some l"
    and th: "those (map (term_types env) args) = Some ls"
    and f: "\<forall>ty' \<in> set (retTy # (case castOpt of None \<Rightarrow> [] | Some t \<Rightarrow> [t]) @ tys @ l @ concat ls). fits env ty'"
    unfolding stmt_fits_def by (auto split: option.splits)
  show thesis
  proof (rule that[OF ct])
    show "\<forall>a \<in> set args. term_fits env a" using term_fits_of_those[OF th] f by auto
    show "term_fits env lhs" using tl f unfolding term_fits_def by auto
  qed (use f in \<open>auto split: option.splits\<close>)
qed

lemma stmt_fits_Swap:
  assumes "stmt_fits env (CoreStmt_Swap g lhs rhs)"
  shows "term_fits env lhs" and "term_fits env rhs"
  using assms unfolding stmt_fits_def term_fits_def by (auto split: option.splits)

lemma stmt_fits_Return:
  assumes "stmt_fits env (CoreStmt_Return tm)"
  shows "term_fits env tm"
  using assms unfolding stmt_fits_def term_fits_def by auto

lemma stmt_fits_While:
  assumes "stmt_fits env (CoreStmt_While g c invs decr body)"
  shows "term_fits env c" and "stmts_fits (env \<lparr> TE_ProofTopLevel := False \<rparr>) body"
proof -
  from assms obtain l1 l2 where tc: "term_types env c = Some l1"
    and tb: "stmts_types (env \<lparr> TE_ProofTopLevel := False \<rparr>) body = Some l2"
    and f: "\<forall>ty \<in> set (l1 @ l2). fits env ty"
    unfolding stmt_fits_def by (auto simp del: term_types.simps split: option.splits)
  show "term_fits env c" using tc f unfolding term_fits_def by auto
  show "stmts_fits (env \<lparr> TE_ProofTopLevel := False \<rparr>) body" using tb f unfolding stmts_fits_def by auto
qed

lemma stmt_fits_Match:
  assumes "stmt_fits env (CoreStmt_Match g s arms)"
  shows "term_fits env s" and "\<And>p body. (p, body) \<in> set arms \<Longrightarrow> stmts_fits (env \<lparr> TE_ProofTopLevel := False \<rparr>) body"
proof -
  from assms obtain l ls where ts: "term_types env s = Some l"
    and th: "those (map (stmts_types (env \<lparr> TE_ProofTopLevel := False \<rparr>) \<circ> snd) arms) = Some ls"
    and f: "\<forall>ty \<in> set (l @ concat ls). fits env ty"
    unfolding stmt_fits_def by (auto simp del: term_types.simps split: option.splits)
  show "term_fits env s" using ts f unfolding term_fits_def by auto
  fix p body assume "(p, body) \<in> set arms"
  then have "stmts_types (env \<lparr> TE_ProofTopLevel := False \<rparr>) body \<in> set (map (stmts_types (env \<lparr> TE_ProofTopLevel := False \<rparr>) \<circ> snd) arms)"
    by force
  then obtain l' where "stmts_types (env \<lparr> TE_ProofTopLevel := False \<rparr>) body = Some l'" and "l' \<in> set ls"
    using those_Some_elem[OF th] by auto
  then show "stmts_fits (env \<lparr> TE_ProofTopLevel := False \<rparr>) body" using f unfolding stmts_fits_def by auto
qed

lemma stmt_fits_Block:
  assumes "stmt_fits env (CoreStmt_Block body)"
  shows "stmts_fits env body"
  using assms unfolding stmt_fits_def stmts_fits_def by auto


section \<open>The proof-top-level flag\<close>

(* The typechecker clears TE_ProofTopLevel in nested statement scopes, but
   stmt_types (SizeBound.thy) keeps the environment for a Block's body.
   Neither the types nor the typing of ghost-free statements depend on the
   flag. *)

lemma is_well_kinded_ptl [simp]: "is_well_kinded (env \<lparr> TE_ProofTopLevel := b \<rparr>) ty = is_well_kinded env ty"
  by (rule is_well_kinded_cong_env) simp_all

lemma is_runtime_type_ptl [simp]: "is_runtime_type (env \<lparr> TE_ProofTopLevel := b \<rparr>) ty = is_runtime_type env ty"
  by (rule is_runtime_type_cong_fields) simp_all

lemma is_well_kinded_ptl_fun [simp]: "is_well_kinded (env \<lparr> TE_ProofTopLevel := b \<rparr>) = is_well_kinded env"
  by (rule ext) simp

lemma is_runtime_type_ptl_fun [simp]: "is_runtime_type (env \<lparr> TE_ProofTopLevel := b \<rparr>) = is_runtime_type env"
  by (rule ext) simp

lemma core_term_type_ptl [simp]: "core_term_type (env \<lparr> TE_ProofTopLevel := b \<rparr>) g tm = core_term_type env g tm"
  by (rule core_term_type_TE_ProofTopLevel_irrelevant)

lemma cast_ok_ptl [simp]: "cast_ok (env \<lparr> TE_ProofTopLevel := b \<rparr>) a c = cast_ok env a c"
  by (rule cast_ok_cong_env) simp_all

lemma pattern_compatible_ptl [simp]: "pattern_compatible (env \<lparr> TE_ProofTopLevel := b \<rparr>) p ty = pattern_compatible env p ty"
  by (rule pattern_compatible_cong_env) simp

lemma ghost_lvalue_ok_ptl [simp]: "ghost_lvalue_ok (env \<lparr> TE_ProofTopLevel := b \<rparr>) g tm = ghost_lvalue_ok env g tm"
  by (rule ghost_lvalue_ok_cong_env) simp_all

lemma is_writable_lvalue_ptl [simp]: "is_writable_lvalue (env \<lparr> TE_ProofTopLevel := b \<rparr>) tm = is_writable_lvalue env tm"
  by (induction tm rule: is_writable_lvalue.induct) (auto simp: tyenv_var_writable_def)

lemma cast_result_type_ptl [simp]:
  "cast_result_type (env \<lparr> TE_ProofTopLevel := b \<rparr>) g retTy castOpt = cast_result_type env g retTy castOpt"
  by (simp add: cast_result_type_def cong: option.case_cong)

lemma core_impure_call_type_ptl [simp]:
  "core_impure_call_type (env \<lparr> TE_ProofTopLevel := b \<rparr>) g f tys args = core_impure_call_type env g f tys args"
proof -
  have A: "(\<lambda>(tm, vor) (expectedTy, mode). case vor of
             Var \<Rightarrow> core_term_type (env \<lparr> TE_ProofTopLevel := b \<rparr>) mode tm = Some expectedTy
           | Ref \<Rightarrow> is_writable_lvalue (env \<lparr> TE_ProofTopLevel := b \<rparr>) tm
                    \<and> ghost_lvalue_ok (env \<lparr> TE_ProofTopLevel := b \<rparr>) mode tm
                    \<and> core_term_type (env \<lparr> TE_ProofTopLevel := b \<rparr>) mode tm = Some expectedTy)
         = (\<lambda>(tm, vor) (expectedTy, mode). case vor of
             Var \<Rightarrow> core_term_type env mode tm = Some expectedTy
           | Ref \<Rightarrow> is_writable_lvalue env tm \<and> ghost_lvalue_ok env mode tm
                    \<and> core_term_type env mode tm = Some expectedTy)"
    by (intro ext) (auto split: prod.splits VarOrRef.splits)
  show ?thesis unfolding core_impure_call_type_def A
    by (cases "fmlookup (TE_Functions env) f"; cases g) (simp_all add: Let_def)
qed

lemma has_valid_decreases_type_ptl [simp]:
  "has_valid_decreases_type (env \<lparr> TE_ProofTopLevel := b \<rparr>) decr = has_valid_decreases_type env decr"
  by (cases decr) simp_all

lemma let_env_ptl [simp]: "let_env (env \<lparr> TE_ProofTopLevel := b \<rparr>) x ty = (let_env env x ty) \<lparr> TE_ProofTopLevel := b \<rparr>"
  by (simp add: let_env_def)

lemma term_types_ptl: "term_types (env \<lparr> TE_ProofTopLevel := b \<rparr>) t = term_types env t"
proof (induction t arbitrary: env)
  case (CoreTm_LitArray ty tms)
  then show ?case by (simp add: term_types.simps[of _ "CoreTm_LitArray ty tms"] del: core_term_type.simps split: option.splits cong: map_cong)
next
  case (CoreTm_Cast ty t)
  then show ?case by (simp add: term_types.simps[of _ "CoreTm_Cast ty t"] del: core_term_type.simps split: option.splits)
next
  case (CoreTm_Unop op t)
  then show ?case by (simp add: term_types.simps[of _ "CoreTm_Unop op t"] del: core_term_type.simps split: option.splits)
next
  case (CoreTm_Binop op t1 t2)
  then show ?case by (simp add: term_types.simps[of _ "CoreTm_Binop op t1 t2"] del: core_term_type.simps split: option.splits)
next
  case (CoreTm_Let x t1 t2)
  show ?case using CoreTm_Let.IH by (simp add: term_types.simps[of _ "CoreTm_Let x t1 t2"] del: core_term_type.simps split: option.splits)
next
  case (CoreTm_FunctionCall f tys args)
  then show ?case by (simp add: term_types.simps[of _ "CoreTm_FunctionCall f tys args"] del: core_term_type.simps split: option.splits cong: map_cong)
next
  case (CoreTm_VariantCtor c tys t)
  then show ?case by (simp add: term_types.simps[of _ "CoreTm_VariantCtor c tys t"] del: core_term_type.simps split: option.splits)
next
  case (CoreTm_Record flds)
  have IH': "\<And>x env. x \<in> set flds \<Longrightarrow> term_types (env \<lparr> TE_ProofTopLevel := b \<rparr>) (snd x) = term_types env (snd x)"
    using CoreTm_Record.IH by (auto simp: snds_def sndsp.simps)
  show ?case by (simp add: term_types.simps[of _ "CoreTm_Record flds"] IH' del: core_term_type.simps split: option.splits cong: map_cong)
next
  case (CoreTm_RecordProj t f)
  then show ?case by (simp add: term_types.simps[of _ "CoreTm_RecordProj t f"] del: core_term_type.simps split: option.splits)
next
  case (CoreTm_VariantProj t c)
  then show ?case by (simp add: term_types.simps[of _ "CoreTm_VariantProj t c"] del: core_term_type.simps split: option.splits)
next
  case (CoreTm_ArrayProj t idxs)
  then show ?case by (simp add: term_types.simps[of _ "CoreTm_ArrayProj t idxs"] del: core_term_type.simps split: option.splits cong: map_cong)
next
  case (CoreTm_Match s arms)
  have IH': "\<And>x env. x \<in> set arms \<Longrightarrow> term_types (env \<lparr> TE_ProofTopLevel := b \<rparr>) (snd x) = term_types env (snd x)"
    using CoreTm_Match.IH(2) by (auto simp: snds_def sndsp.simps)
  show ?case using CoreTm_Match.IH(1)
    by (simp add: term_types.simps[of _ "CoreTm_Match s arms"] IH' del: core_term_type.simps split: option.splits cong: map_cong)
next
  case (CoreTm_Sizeof t)
  then show ?case by (simp add: term_types.simps[of _ "CoreTm_Sizeof t"] del: core_term_type.simps split: option.splits)
qed (simp_all add: term_types.simps del: core_term_type.simps split: option.splits)

lemma term_types_ptl_fun [simp]: "term_types (env \<lparr> TE_ProofTopLevel := b \<rparr>) = term_types env"
  by (rule ext) (rule term_types_ptl)

(* The typing of a statement that has types (a ghost-free form) commutes with
   the flag. *)
lemma core_statement_type_ptl:
  assumes "stmt_types env s = Some l"
  shows "core_statement_type (env \<lparr> TE_ProofTopLevel := b \<rparr>) NotGhost s
         = map_option (\<lambda>e. e \<lparr> TE_ProofTopLevel := b \<rparr>) (core_statement_type env NotGhost s)"
proof (cases s)
  case (CoreStmt_VarDecl g x vor ty tm)
  then show ?thesis by (cases vor) (auto simp: Let_def split: if_splits)
qed (use assms in \<open>auto simp: Let_def split: option.splits if_splits CoreType.splits\<close>)

lemma stmt_types_ptl:
  "stmt_types (env \<lparr> TE_ProofTopLevel := b \<rparr>) s = stmt_types env s"
  "stmts_types (env \<lparr> TE_ProofTopLevel := b \<rparr>) ss = stmts_types env ss"
proof (induction env s and env ss rule: stmt_types_stmts_types.induct)
  case (12 env s ss)
  show ?case
  proof (cases "stmt_types env s")
    case None
    then show ?thesis using 12(1) by simp
  next
    case (Some l)
    show ?thesis
    proof (cases "core_statement_type env NotGhost s")
      case None
      then show ?thesis using 12(1) Some core_statement_type_ptl[OF Some] by simp
    next
      case (Some env')
      then show ?thesis using 12(1) 12(2)[OF \<open>stmt_types env s = Some l\<close> Some] \<open>stmt_types env s = Some l\<close>
        core_statement_type_ptl[OF \<open>stmt_types env s = Some l\<close>] by simp
    qed
  qed
qed (simp_all add: term_types_ptl split: option.splits)

lemma stmts_fits_ptl [simp]: "stmts_fits (env \<lparr> TE_ProofTopLevel := b \<rparr>) ss = stmts_fits env ss"
  by (simp add: stmts_fits_def stmt_types_ptl)


section \<open>Eliminating the typing lookups of the generator\<close>

lemma env_after_InrE:
  assumes "cg_bind (env_after cg s) k st = Inr r" and "core_statement_type (CG_TyEnv cg) NotGhost s = Some env'"
  shows "k env' st = Inr r"
  using assms(1) unfolding cg_bind_def env_after_def assms(2) cg_lift_def by (simp add: cg_return_def)

lemma ty_of_bind_InrE:
  assumes "cg_bind (ty_of cg t) k st = Inr r" and "core_term_type (CG_TyEnv cg) NotGhost t = Some ty"
  shows "k ty st = Inr r"
  using assms(1) unfolding cg_bind_def ty_of_def assms(2) cg_lift_def by (simp add: cg_return_def)

lemma impure_ret_type_bind_InrE:
  assumes "cg_bind (impure_ret_type cg f tys args) k st = Inr r"
    and "core_impure_call_type (CG_TyEnv cg) NotGhost f tys args = Some retTy"
  shows "k retTy st = Inr r"
  using assms(1) unfolding cg_bind_def impure_ret_type_def assms(2) cg_lift_def by (simp add: cg_return_def)

section \<open>Declaring a variable\<close>

(* The invariant after a VarDecl: the new context binds x to ty (a well-kinded
   runtime type) with a representation typed in the extended environment. *)
lemma cg_ok_decl:
  assumes ok: "cg_ok prog E cg" and wk: "is_well_kinded (CG_TyEnv cg) ty" and rtt: "is_runtime_type (CG_TyEnv cg) ty"
    and le: "env_le E E'"
    and rep: "rep_ok E' (CG_TyEnv cg) ty rep"
  shows "cg_ok prog E' (cg_bind_var cg ((CG_TyEnv cg) \<lparr> TE_LocalVars := fmupd x ty (TE_LocalVars (CG_TyEnv cg)),
                                                       TE_GhostLocals := fminus (TE_GhostLocals (CG_TyEnv cg)) {|x|},
                                                       TE_ConstLocals := c \<rparr>) x rep)"
proof (rule cg_okI)
  let ?env' = "(CG_TyEnv cg) \<lparr> TE_LocalVars := fmupd x ty (TE_LocalVars (CG_TyEnv cg)),
                             TE_GhostLocals := fminus (TE_GhostLocals (CG_TyEnv cg)) {|x|},
                             TE_ConstLocals := c \<rparr>"
  let ?cg' = "cg_bind_var cg ?env' x rep"
  have A: "CG_TyEnv ?cg' = ?env'" by (simp add: cg_bind_var_def)
  show "tyenv_well_formed (CG_TyEnv ?cg')"
    using tyenv_well_formed_declare_var[OF cg_ok_wf[OF ok] wk, where g = NotGhost and var = x and c = c] rtt
    unfolding A by simp
  show "sizes_in E' (fset (TE_TypeVars (CG_TyEnv ?cg')))"
    using sizes_in_mono[OF le cg_ok_sizes_in[OF ok]] unfolding A by simp
  show "\<And>y r. fmlookup (CG_Vars ?cg') y = Some r \<Longrightarrow>
          \<exists>ty. tyenv_lookup_var (CG_TyEnv ?cg') y = Some ty \<and> rep_ok E' (CG_TyEnv ?cg') ty r"
  proof -
    fix y r assume lk: "fmlookup (CG_Vars ?cg') y = Some r"
    have cong: "\<And>ty r. rep_ok E' ?env' ty r = rep_ok E' (CG_TyEnv cg) ty r"
      by (rule rep_ok_cong_env(1)) simp_all
    have lk': "\<And>y. tyenv_lookup_var ?env' y = (if y = x then Some ty else tyenv_lookup_var (CG_TyEnv cg) y)"
      by (simp add: tyenv_lookup_var_def split: option.splits)
    show "\<exists>ty. tyenv_lookup_var (CG_TyEnv ?cg') y = Some ty \<and> rep_ok E' (CG_TyEnv ?cg') ty r"
    proof (cases "y = x")
      case True
      then have "r = rep" using lk by (simp add: cg_bind_var_def)
      then show ?thesis using True rep unfolding A cong lk' by simp
    next
      case False
      then have "fmlookup (CG_Vars cg) y = Some r" using lk by (simp add: cg_bind_var_def)
      then obtain ty where "tyenv_lookup_var (CG_TyEnv cg) y = Some ty" "rep_ok E (CG_TyEnv cg) ty r"
        using cg_ok_var[OF ok] by blast
      then show ?thesis using False rep_ok_mono[OF le] unfolding A cong lk' by auto
    qed
  qed
  show "CG_Ret ?cg' = ret_kind (TE_ReturnType (CG_TyEnv ?cg'))"
    using cg_ok_ret[OF ok] unfolding A by (simp add: cg_bind_var_def)
  show "CG_Ret ?cg' = RK_Buf \<Longrightarrow> fmlookup E' ret_param = Some (VT_Scalar CTy_CharPtr)"
    using cg_ok_ret_param[OF ok] env_le_lookup[OF le] by (simp add: cg_bind_var_def)
  show "size_fits (CG_TyEnv ?cg') 0 (\<lambda>_. 0) (TE_ReturnType (CG_TyEnv ?cg'))"
    using cg_ok_ret_fits[OF ok] size_fits_cong_env[of ?env' "CG_TyEnv cg"] unfolding A by simp
  show "\<And>d. dt_tags_fit (CG_TyEnv ?cg') d"
    using cg_ok_tags[OF ok] unfolding A by (simp add: dt_tags_fit_def dt_ctors_def)
  show "prog_ok prog (CG_TyEnv ?cg')"
    using cg_ok_prog[OF ok] unfolding A by (simp add: prog_ok_def)
qed

lemma cg_mapM_length: "cg_mapM f xs st = Inr (ys, st') \<Longrightarrow> length ys = length xs"
proof (induction xs arbitrary: st ys)
  case Nil
  then show ?case by (simp add: cg_mapM.simps)
next
  case (Cons x xs)
  from Cons.prems obtain y st1 ys' where "cg_mapM f xs st1 = Inr (ys', st')" and "ys = y # ys'"
    by (auto simp: cg_mapM.simps elim!: cg_bind_InrE)
  then show ?case using Cons.IH by simp
qed


section \<open>Frozen lvalues\<close>

(* The index variables of a frozen array projection: each index value in a
   fresh uint64_t variable. *)
lemma freeze_indices_ok:
  assumes "cg_mapM (\<lambda>e. cg_bind (fresh_name (CG_Fun cg) ''idx'')
                       (\<lambda>v. cg_return (v, [MS_DeclScalar v CTy_U64, MS_Assign v e]))) es st = Inr (vs, st')"
    and "scope_ok prog (E, ds) st" and "\<forall>e \<in> set es. u64_ok E e"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st (concat (map snd vs)) st' (E', ds')
           \<and> (\<forall>v \<in> set (map fst vs). fmlookup E' v = Some (VT_Scalar CTy_U64))"
proof -
  have "\<exists>E' ds'. lowered_ok prog rt (E, ds) st (concat (map snd vs)) st' (E', ds')
           \<and> (\<forall>y \<in> set vs. fmlookup E' (fst y) = Some (VT_Scalar CTy_U64))"
  proof (rule cg_mapM_chain[OF assms(1,2)])
    fix e sta y stb Ea dsa
    assume e: "e \<in> set es"
      and fy: "cg_bind (fresh_name (CG_Fun cg) ''idx'') (\<lambda>v. cg_return (v, [MS_DeclScalar v CTy_U64, MS_Assign v e])) sta = Inr (y, stb)"
      and sca: "scope_ok prog (Ea, dsa) sta" and le: "env_le E Ea"
    from fy obtain v where fr: "fresh_name (CG_Fun cg) ''idx'' sta = Inr (v, stb)"
      and y: "y = (v, [MS_DeclScalar v CTy_U64, MS_Assign v e])"
      by (auto simp: cg_return_def elim!: cg_bind_InrE)
    let ?E2 = "fmupd v (VT_Scalar CTy_U64) Ea"
    have d: "lowered_ok prog rt (Ea, dsa) sta [MS_DeclScalar v CTy_U64] stb (?E2, v # dsa)"
      by (rule fresh_scalar_ok[OF sca fr])
    have le2: "env_le E ?E2" by (rule env_le_trans[OF le lowered_ok_env_le'[OF d]])
    have ue: "u64_ok ?E2 e" using assms(3) e expr_type_mono[OF le2] by (auto simp: u64_ok_def)
    have a: "lowered_ok prog rt (?E2, v # dsa) stb [MS_Assign v e] stb (?E2, v # dsa)"
      using lowered_ok_scope[OF d] ue by (intro assign_ok[where cty' = CTy_U64]) (auto simp: ty_compat_def)
    show "\<exists>E2 ds2. lowered_ok prog rt (Ea, dsa) sta (snd y) stb (E2, ds2) \<and> fmlookup E2 (fst y) = Some (VT_Scalar CTy_U64)"
      unfolding y using lowered_ok_append[OF d a] by auto
  next
    fix E1 E2 y assume "env_le E1 E2" "fmlookup E1 (fst y) = Some (VT_Scalar CTy_U64)"
    then show "fmlookup E2 (fst y) = Some (VT_Scalar CTy_U64)" by (rule env_le_lookup)
  qed
  then show ?thesis by auto
qed

lemma freeze_lvalue_ok:
  "freeze_lvalue cg lv st = Inr ((S, ll), st') \<Longrightarrow> cg_ok prog E cg \<Longrightarrow> scope_ok prog (E, ds) st
   \<Longrightarrow> term_fits (CG_TyEnv cg) lv \<Longrightarrow> core_term_type (CG_TyEnv cg) NotGhost lv = Some ty
   \<Longrightarrow> \<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> ll_type ll = ty \<and> ll_ok E' (CG_TyEnv cg) ll"
proof (induction cg lv arbitrary: st S ll st' E ds ty rule: freeze_lvalue.induct)
  case (1 cg x)
  from 1(1) obtain rep where rep: "fmlookup (CG_Vars cg) x = Some rep"
    and r: "(case rep of VR_Lazy ll \<Rightarrow> cg_return ([], ll) | _ \<Rightarrow> cg_return ([], LL_Base rep ty)) st = Inr ((S, ll), st')"
    using 1(5) by (auto simp: freeze_lvalue.simps ty_of_Inr lookup_var_Inr elim!: cg_bind_InrE)
  obtain ty' where "tyenv_lookup_var (CG_TyEnv cg) x = Some ty'" "rep_ok E (CG_TyEnv cg) ty' rep"
    using cg_ok_var[OF 1(2) rep] by blast
  then have ro: "rep_ok E (CG_TyEnv cg) ty rep" using var_typed[OF 1(5)] by simp
  have wk: "is_well_kinded (CG_TyEnv cg) ty" using term_type_wk(1)[OF 1(2,5)] .
  have f: "fits (CG_TyEnv cg) ty" using term_fits_ty[OF 1(4,5)] .
  show ?case
  proof (cases rep)
    case (VR_Lazy ll')
    then have "S = []" "ll = ll'" "st' = st" using r by (auto simp: cg_return_def)
    then show ?thesis using ro VR_Lazy lowered_ok_nil[OF 1(3)] by auto
  next
    case (VR_Scalar n cty)
    then have "S = []" "ll = LL_Base rep ty" "st' = st" using r by (auto simp: cg_return_def)
    then show ?thesis using ro wk f VR_Scalar lowered_ok_nil[OF 1(3)] by (auto simp: fits_def)
  next
    case (VR_Buf n)
    then have "S = []" "ll = LL_Base rep ty" "st' = st" using r by (auto simp: cg_return_def)
    then show ?thesis using ro wk f VR_Buf lowered_ok_nil[OF 1(3)] by (auto simp: fits_def)
  next
    case (VR_Ptr n)
    then have "S = []" "ll = LL_Base rep ty" "st' = st" using r by (auto simp: cg_return_def)
    then show ?thesis using ro wk f VR_Ptr lowered_ok_nil[OF 1(3)] by (auto simp: fits_def)
  qed
next
  case (2 cg t f)
  obtain fldTys where tt: "core_term_type (CG_TyEnv cg) NotGhost t = Some (CoreTy_Record fldTys)" and mo: "map_of fldTys f = Some ty"
    using record_proj_typed[OF 2(6)] by blast
  from 2(2) obtain S1 ll1 where fr: "freeze_lvalue cg t st = Inr ((S1, ll1), st')" and S: "S = S1" and ll: "ll = LL_Field ll1 f ty"
    using 2(6) by (auto simp: freeze_lvalue.simps ty_of_Inr cg_return_def elim!: cg_bind_InrE)
  obtain E1 ds1 where lo: "lowered_ok prog rt (E, ds) st S1 st' (E1, ds1)" and lt: "ll_type ll1 = CoreTy_Record fldTys"
    and lok: "ll_ok E1 (CG_TyEnv cg) ll1"
    using 2(1)[OF ty_of_Some[OF 2(6)] fr 2(3,4) term_fits_RecordProj[OF 2(5)] tt] by blast
  have wk: "is_well_kinded (CG_TyEnv cg) ty" using term_type_wk(1)[OF 2(3,6)] .
  have f: "fits (CG_TyEnv cg) ty" using term_fits_ty[OF 2(5,6)] .
  show ?case unfolding S ll using lo lt lok mo wk f by (auto simp: fits_def)
next
  case (3 cg t c)
  obtain dtName args tyvars payloadTy where tt: "core_term_type (CG_TyEnv cg) NotGhost t = Some (CoreTy_Datatype dtName args)"
    using variant_proj_typed[OF 3(6)] by blast
  from 3(2) obtain S1 ll1 where fr: "freeze_lvalue cg t st = Inr ((S1, ll1), st')" and S: "S = S1" and ll: "ll = LL_Payload ll1 c ty"
    using 3(6) by (auto simp: freeze_lvalue.simps ty_of_Inr cg_return_def elim!: cg_bind_InrE)
  obtain E1 ds1 where lo: "lowered_ok prog rt (E, ds) st S1 st' (E1, ds1)" and lt: "ll_type ll1 = CoreTy_Datatype dtName args"
    and lok: "ll_ok E1 (CG_TyEnv cg) ll1"
    using 3(1)[OF ty_of_Some[OF 3(6)] fr 3(3,4) term_fits_VariantProj[OF 3(5)] tt] by blast
  have wk: "is_well_kinded (CG_TyEnv cg) ty" using term_type_wk(1)[OF 3(3,6)] .
  have f: "fits (CG_TyEnv cg) ty" using term_fits_ty[OF 3(5,6)] .
  show ?case unfolding S ll using lo lt lok wk f by (auto simp: fits_def)
next
  case (4 cg t idxs)
  obtain dims where tt: "core_term_type (CG_TyEnv cg) NotGhost t = Some (CoreTy_Array ty dims)"
    and lens: "length idxs = length dims"
    and idxty: "\<forall>i \<in> set idxs. core_term_type (CG_TyEnv cg) NotGhost i = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
    using array_proj_typed[OF 4(6)] by blast
  let ?vf = "\<lambda>e. cg_bind (fresh_name (CG_Fun cg) ''idx'') (\<lambda>v. cg_return (v, [MS_DeclScalar v CTy_U64, MS_Assign v e]))"
  have unf: "freeze_lvalue cg (CoreTm_ArrayProj t idxs) st =
      cg_bind (freeze_lvalue cg t) (\<lambda>(S, ll).
      cg_bind (cg_mapM (lower_term cg) idxs) (\<lambda>rs.
      cg_bind (cg_mapM ?vf (map snd rs)) (\<lambda>vs.
      cg_return (S @ concat (map fst rs) @ concat (map snd vs), LL_Index ll (map fst vs) ty)))) st"
    unfolding freeze_lvalue.simps by (simp add: cg_bind_def ty_of_Some[OF 4(6)])
  from 4(2)[unfolded unf] obtain r1 st1 where fr': "freeze_lvalue cg t st = Inr (r1, st1)"
    and k1: "(\<lambda>(S, ll). cg_bind (cg_mapM (lower_term cg) idxs) (\<lambda>rs.
      cg_bind (cg_mapM ?vf (map snd rs)) (\<lambda>vs.
      cg_return (S @ concat (map fst rs) @ concat (map snd vs), LL_Index ll (map fst vs) ty)))) r1 st1 = Inr ((S, ll), st')"
    by (rule cg_bind_InrE)
  obtain S1 ll1 where r1: "r1 = (S1, ll1)" by (cases r1)
  have fr: "freeze_lvalue cg t st = Inr ((S1, ll1), st1)" using fr' r1 by simp
  from k1[unfolded r1 case_prod_conv] obtain rs st2 where lm: "cg_mapM (lower_term cg) idxs st1 = Inr (rs, st2)"
    and k2: "cg_bind (cg_mapM ?vf (map snd rs)) (\<lambda>vs.
      cg_return (S1 @ concat (map fst rs) @ concat (map snd vs), LL_Index ll1 (map fst vs) ty)) st2 = Inr ((S, ll), st')"
    by (rule cg_bind_InrE)
  from k2 obtain vs st3 where lv: "cg_mapM ?vf (map snd rs) st2 = Inr (vs, st3)"
    and k3: "cg_return (S1 @ concat (map fst rs) @ concat (map snd vs), LL_Index ll1 (map fst vs) ty) st3 = Inr ((S, ll), st')"
    by (rule cg_bind_InrE)
  from k3 have S: "S = S1 @ concat (map fst rs) @ concat (map snd vs)" and ll: "ll = LL_Index ll1 (map fst vs) ty" and st': "st' = st3"
    by (auto simp: cg_return_def)
  note tfs = term_fits_ArrayProj[OF 4(5)]
  obtain E1 ds1 where lo1: "lowered_ok prog rt (E, ds) st S1 st1 (E1, ds1)" and lt: "ll_type ll1 = CoreTy_Array ty dims"
    and lok: "ll_ok E1 (CG_TyEnv cg) ll1"
    using 4(1)[OF ty_of_Some[OF 4(6)] fr 4(3,4) tfs[THEN conjunct1] tt] by blast
  have ok1: "cg_ok prog E1 cg" using cg_ok_mono[OF lowered_ok_env_le'[OF lo1] 4(3)] .
  obtain E2 ds2 where lo2: "lowered_ok prog rt (E1, ds1) st1 (concat (map fst rs)) st2 (E2, ds2)"
    and idx: "\<forall>r \<in> set rs. u64_ok E2 (snd r)"
    using lower_indices_ok[OF lm _ ok1 lowered_ok_scope[OF lo1]] lower_ok(1) tfs idxty by blast
  have idx': "\<forall>e \<in> set (map snd rs). u64_ok E2 e" using idx by auto
  obtain E3 ds3 where lo3: "lowered_ok prog rt (E2, ds2) st2 (concat (map snd vs)) st' (E3, ds3)"
    and vsok: "\<forall>v \<in> set (map fst vs). fmlookup E3 v = Some (VT_Scalar CTy_U64)"
    using freeze_indices_ok[OF lv[folded st'] lowered_ok_scope[OF lo2] idx', where rt = rt] by blast
  have lenvs: "length vs = length dims"
    using cg_mapM_length[OF lv] cg_mapM_length[OF lm] lens by simp
  have lok3: "ll_ok E3 (CG_TyEnv cg) ll1"
    using ll_ok_mono[OF env_le_trans[OF lowered_ok_env_le'[OF lo2] lowered_ok_env_le'[OF lo3]] lok] .
  have wk: "is_well_kinded (CG_TyEnv cg) ty" using term_type_wk(1)[OF 4(3,6)] .
  have f: "fits (CG_TyEnv cg) ty" using term_fits_ty[OF 4(5,6)] .
  have lo: "lowered_ok prog rt (E, ds) st S st' (E3, ds3)"
    unfolding S using lowered_ok_append[OF lowered_ok_append[OF lo1 lo2] lo3] by simp
  show ?case unfolding ll using lo lok3 lt lenvs vsok wk f by (auto simp: fits_def)
next
  case (5 cg ty' t)
  from cast_typed[OF 5(6)] obtain fromTy where ty': "ty = ty'" and ft: "core_term_type (CG_TyEnv cg) NotGhost t = Some fromTy"
    and co: "cast_ok (CG_TyEnv cg) fromTy ty'" by blast
  have arr: "is_array_type ty'" using 5(2) by (auto simp: freeze_lvalue.simps internal_def cg_fail_def split: if_splits)
  from 5(2) obtain S1 ll1 where fr: "freeze_lvalue cg t st = Inr ((S1, ll1), st')" and S: "S = S1" and ll: "ll = LL_Cast ll1 ty'"
    using arr by (auto simp: freeze_lvalue.simps cg_return_def elim!: cg_bind_InrE)
  obtain E1 ds1 where lo: "lowered_ok prog rt (E, ds) st S1 st' (E1, ds1)" and lt: "ll_type ll1 = fromTy"
    and lok: "ll_ok E1 (CG_TyEnv cg) ll1"
    using 5(1)[OF arr fr 5(3,4) term_fits_Cast[OF 5(5)] ft] by blast
  have aco: "array_cast_ok fromTy ty'" using co arr by (cases ty') (auto simp: cast_ok_def)
  have wk: "is_well_kinded (CG_TyEnv cg) ty'" using term_type_wk(1)[OF 5(3,6)] ty' by simp
  have f: "fits (CG_TyEnv cg) ty'" using term_fits_ty[OF 5(5,6)] ty' by simp
  show ?case unfolding S ll ty' using lo lt lok aco wk f by (auto simp: fits_def)
qed (auto simp: freeze_lvalue.simps internal_def cg_fail_def)


section \<open>Stores\<close>

lemma lower_store_ok:
  assumes "lower_store cg lv ty e st = Inr (S, st')" and "cg_ok prog E cg" and "scope_ok prog (E, ds) st"
    and "term_fits (CG_TyEnv cg) lv" and "core_term_type (CG_TyEnv cg) NotGhost lv = Some ty"
    and "expr_ok E e (res_cty ty)" and "fits (CG_TyEnv cg) ty"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds')"
proof -
  have "(\<exists>x n cty. lv = CoreTm_Var x \<and> fmlookup (CG_Vars cg) x = Some (VR_Scalar n cty) \<and> S = [MS_Assign n e] \<and> st' = st)
      \<or> cg_bind (lower_addr cg lv) (\<lambda>(S, a). cg_return (S @ [store_at cg ty a e])) st = Inr (S, st')"
    using assms(1) unfolding lower_store_def
    by (cases lv) (auto simp: cg_return_def split: option.splits VarRep.splits simp del: lower_addr.simps)
  then have "(\<exists>x n cty. lv = CoreTm_Var x \<and> fmlookup (CG_Vars cg) x = Some (VR_Scalar n cty) \<and> S = [MS_Assign n e] \<and> st' = st)
      \<or> (\<exists>S1 a. lower_addr cg lv st = Inr ((S1, a), st') \<and> S = S1 @ [store_at cg ty a e])"
    by (auto simp: cg_return_def split: prod.splits elim!: cg_bind_InrE simp del: lower_addr.simps)
  then show ?thesis
  proof (elim disjE exE conjE)
    fix x n cty assume lv: "lv = CoreTm_Var x" and rep: "fmlookup (CG_Vars cg) x = Some (VR_Scalar n cty)"
      and S: "S = [MS_Assign n e]" and st': "st' = st"
    obtain ty' where "tyenv_lookup_var (CG_TyEnv cg) x = Some ty'" "rep_ok E (CG_TyEnv cg) ty' (VR_Scalar n cty)"
      using cg_ok_var[OF assms(2) rep] by blast
    then have ro: "rep_ok E (CG_TyEnv cg) ty (VR_Scalar n cty)" using var_typed[OF assms(5)[unfolded lv]] by simp
    then have "scalar_ty ty = Some cty" "fmlookup E n = Some (VT_Scalar cty)" by simp_all
    then show ?thesis unfolding S st' using assms(3,6) by (auto intro!: exI assign_ok[where cty' = cty] simp: ty_compat_def)
  next
    fix S1 a assume la: "lower_addr cg lv st = Inr ((S1, a), st')" and S: "S = S1 @ [store_at cg ty a e]"
    obtain E1 ds1 where lo1: "lowered_ok prog rt (E, ds) st S1 st' (E1, ds1)" and a: "expr_ok E1 a CTy_CharPtr"
      by (rule lower_addr_ok[OF la assms(2,3,4)])
    have le: "env_le E E1" by (rule lowered_ok_env_le'[OF lo1])
    have sz: "u64_ok E1 (cg_size cg ty)" using cg_size_ok[OF cg_ok_mono[OF le assms(2)] term_type_wk(1)[OF assms(2,5)] assms(7)] .
    have "lowered_ok prog rt (E1, ds1) st' [store_at cg ty a e] st' (E1, ds1)"
      by (rule store_at_ok[OF lowered_ok_scope[OF lo1] a expr_ok_mono[OF le assms(6)] sz])
    then show ?thesis unfolding S using lowered_ok_append[OF lo1] by blast
  qed
qed


section \<open>Call results\<close>

(* The result of a call at its (instantiated, possibly cast) result type. *)
fun cres_ok :: "MTyEnv \<Rightarrow> CoreType \<Rightarrow> CallRes \<Rightarrow> bool" where
  "cres_ok E ty (CR_Scalar e) = expr_ok E e (res_cty ty)"
| "cres_ok E ty (CR_Place p) = expr_ok E p CTy_CharPtr"
| "cres_ok E ty CR_Unit = True"

lemma cres_ok_mono: "env_le E E' \<Longrightarrow> cres_ok E ty res \<Longrightarrow> cres_ok E' ty res"
  by (cases res) (auto intro: expr_ok_mono)

lemma cres_ok_of_res_ok:
  assumes "res_ok E info res"
  shows "cres_ok E (apply_subst s (FI_ReturnType info)) res"
proof (cases res)
  case (CR_Scalar e)
  then obtain cty where "ret_kind (FI_ReturnType info) = RK_Scalar cty" "expr_ok E e cty" using assms by auto
  then have "scalar_ty (FI_ReturnType info) = Some cty" by (auto simp: ret_kind_def split: option.splits if_splits)
  then show ?thesis using \<open>expr_ok E e cty\<close> CR_Scalar by (simp add: res_cty_apply_subst_scalar)
qed (use assms in auto)

lemma call_result_expr_cres:
  assumes "cres_ok E ty res" and "call_result_expr ty res = Some e"
  shows "expr_ok E e (res_cty ty)"
  using assms by (cases res) (auto simp: call_result_expr_def intro: expr_ok_load_at)

lemma cast_ok_wk: "cast_ok env a b \<Longrightarrow> is_runtime_type env b \<Longrightarrow> is_well_kinded env b"
  unfolding cast_ok_def by (cases b) auto

lemma cast_call_res_ok:
  assumes "cast_call_res cg retTy castOpt res st = Inr ((S, res'), st')" and "cg_ok prog E cg" and "scope_ok prog (E, ds) st"
    and "cres_ok E retTy res" and "cast_result_type (CG_TyEnv cg) NotGhost retTy castOpt = Some ty"
    and "is_well_kinded (CG_TyEnv cg) retTy" and "is_runtime_type (CG_TyEnv cg) retTy" and "fits (CG_TyEnv cg) ty"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds') \<and> cres_ok E' ty res'"
proof (cases castOpt)
  case None
  then have "S = []" "res' = res" "st' = st" "ty = retTy" using assms(1,5) by (auto simp: cast_call_res_def cast_result_type_def cg_return_def)
  then show ?thesis using lowered_ok_nil[OF assms(3)] assms(4) by auto
next
  case (Some toTy)
  have ty: "ty = toTy" and co: "cast_ok (CG_TyEnv cg) retTy toTy" and rtt: "is_runtime_type (CG_TyEnv cg) toTy"
    using assms(5) Some by (auto simp: cast_result_type_def split: if_splits)
  from assms(1) obtain e S1 e1 where cr: "call_result_expr retTy res = Some e"
    and cres: "cast_result cg retTy toTy e st = Inr ((S1, e1), st')"
    and S: "S = S1" and res': "res' = (if is_scalar toTy then CR_Scalar e1 else CR_Place e1)"
    unfolding cast_call_res_def Some by (auto simp: cg_return_def internal_def cg_fail_def split: option.splits elim!: cg_bind_InrE)
  have e: "expr_ok E e (res_cty retTy)" by (rule call_result_expr_cres[OF assms(4) cr])
  obtain E1 ds1 where lo: "lowered_ok prog rt (E, ds) st S1 st' (E1, ds1)" and e1: "expr_ok E1 e1 (res_cty toTy)"
    using cast_result_ok[OF cres assms(2,3) e co assms(7) rtt assms(6) cast_ok_wk[OF co rtt] assms(8)[unfolded ty]] by blast
  show ?thesis unfolding S ty res' using lo e1 by (cases "scalar_ty toTy") (auto simp: res_cty_def)
qed

lemma call_store_ok:
  assumes "call_store cg store ty res st = Inr (S, st')" and "cres_ok E ty res" and "scope_ok prog (E, ds) st"
    and "\<And>e S st'. store e st = Inr (S, st') \<Longrightarrow> expr_ok E e (res_cty ty) \<Longrightarrow> \<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds')"
  shows "\<exists>E' ds'. lowered_ok prog rt (E, ds) st S st' (E', ds')"
proof (cases "call_result_expr ty res")
  case None
  then have "S = []" "st' = st" using assms(1) by (auto simp: call_store_def cg_return_def)
  then show ?thesis using lowered_ok_nil[OF assms(3)] by auto
next
  case (Some e)
  then have "store e st = Inr (S, st')" using assms(1) by (simp add: call_store_def)
  then show ?thesis using assms(4) call_result_expr_cres[OF assms(2) Some] by blast
qed


section \<open>Locals\<close>

lemma decl_local_ok:
  assumes "decl_local cg x ty st = Inr ((decl, rep), st')" and "cg_ok prog E cg" and "scope_ok prog (E, ds) st"
    and "is_well_kinded (CG_TyEnv cg) ty" and "fits (CG_TyEnv cg) ty"
  obtains n where "lowered_ok prog rt (E, ds) st [decl] st' (fmupd n (case scalar_ty ty of Some cty \<Rightarrow> VT_Scalar cty | None \<Rightarrow> VT_Buf) E, n # ds)"
    and "rep_ok (fmupd n (case scalar_ty ty of Some cty \<Rightarrow> VT_Scalar cty | None \<Rightarrow> VT_Buf) E) (CG_TyEnv cg) ty rep"
    and "n |\<notin>| fmdom E"
    and "rep = (case scalar_ty ty of Some cty \<Rightarrow> VR_Scalar n cty | None \<Rightarrow> VR_Buf n)"
proof -
  from assms(1) obtain n where ln: "local_name (CG_Fun cg) x st = Inr (n, st')"
    and decl: "decl = (case scalar_ty ty of Some cty \<Rightarrow> MS_DeclScalar n cty | None \<Rightarrow> MS_DeclBuf n (buf_size (cg_size cg ty)))"
    and rep: "rep = (case scalar_ty ty of Some cty \<Rightarrow> VR_Scalar n cty | None \<Rightarrow> VR_Buf n)"
    by (auto simp: decl_local_def cg_return_def split: option.splits elim!: cg_bind_InrE)
  have nd: "n |\<notin>| fmdom E" using local_decl_facts[OF assms(3) ln] by blast
  show thesis
  proof (cases "scalar_ty ty")
    case (Some cty)
    show thesis
      by (rule that[of n]) (use Some decl rep local_scalar_ok[OF assms(3) ln, where cty = cty] nd in auto)
  next
    case None
    have sz: "u64_ok E (buf_size (cg_size cg ty))" using cg_buf_size_ok[OF assms(2,4,5)] .
    show thesis
      by (rule that[of n]) (use None decl rep local_buf_ok[OF assms(3) ln sz] nd in auto)
  qed
qed

lemma init_local_ok:
  assumes "init_local cg rep ty e st = Inr (S, st')" and "scope_ok prog (E, ds) st" and "rep_ok E (CG_TyEnv cg) ty rep"
    and "rep = (case scalar_ty ty of Some cty \<Rightarrow> VR_Scalar n cty | None \<Rightarrow> VR_Buf n)"
    and "expr_ok E e (res_cty ty)" and "u64_ok E (cg_size cg ty)"
  shows "lowered_ok prog rt (E, ds) st S st (E, ds) \<and> st' = st"
proof (cases "scalar_ty ty")
  case (Some cty)
  then have rep: "rep = VR_Scalar n cty" using assms(4) by simp
  have "S = [MS_Assign n e]" "st' = st" using assms(1) unfolding rep by (auto simp: init_local_def cg_return_def)
  then show ?thesis using assms(2,3,5) Some unfolding rep by (auto intro!: assign_ok[where cty' = cty] simp: ty_compat_def)
next
  case None
  then have rep: "rep = VR_Buf n" using assms(4) by simp
  have "S = [MS_Copy (ME_AddrOf n) e (cg_size cg ty)]" "st' = st" using assms(1) unfolding rep by (auto simp: init_local_def cg_return_def)
  then show ?thesis using assms(2,3,5,6) None unfolding rep
    by (auto intro!: copy_ok[where dty = CTy_CharPtr and sty = CTy_CharPtr] simp: expr_ok_def res_cty_def)
qed


section \<open>The statements\<close>

(* The statement of the statement theorem: the lowering of a statement
   (list) that typechecks and whose types fit yields statements accepted by
   the MiniC typechecker at the context's return type, and a context that
   satisfies the invariant for the typechecker's resulting environment. *)
definition ls_ok :: "MProgram \<Rightarrow> CGEnv \<Rightarrow> CoreStatement \<Rightarrow> bool" where
  "ls_ok prog cg s =
    (\<forall>E ds st S cg' st' env'. lower_stmt cg s st = Inr ((S, cg'), st') \<longrightarrow> cg_ok prog E cg
       \<longrightarrow> scope_ok prog (E, ds) st \<longrightarrow> stmt_fits (CG_TyEnv cg) s
       \<longrightarrow> core_statement_type (CG_TyEnv cg) NotGhost s = Some env'
       \<longrightarrow> (\<exists>E' ds'. lowered_ok prog (rk_cty (CG_Ret cg)) (E, ds) st S st' (E', ds') \<and> cg_ok prog E' cg'
              \<and> CG_TyEnv cg' = env' \<and> CG_Ret cg' = CG_Ret cg))"

definition lss_ok :: "MProgram \<Rightarrow> CGEnv \<Rightarrow> CoreStatement list \<Rightarrow> bool" where
  "lss_ok prog cg ss =
    (\<forall>E ds st S cg' st' env'. lower_stmts cg ss st = Inr ((S, cg'), st') \<longrightarrow> cg_ok prog E cg
       \<longrightarrow> scope_ok prog (E, ds) st \<longrightarrow> stmts_fits (CG_TyEnv cg) ss
       \<longrightarrow> core_statement_list_type (CG_TyEnv cg) NotGhost ss = Some env'
       \<longrightarrow> (\<exists>E' ds'. lowered_ok prog (rk_cty (CG_Ret cg)) (E, ds) st S st' (E', ds') \<and> cg_ok prog E' cg'
              \<and> CG_TyEnv cg' = env' \<and> CG_Ret cg' = CG_Ret cg))"

lemma ls_okD:
  assumes "ls_ok prog cg s" and "lower_stmt cg s st = Inr ((S, cg'), st')" and "cg_ok prog E cg"
    and "scope_ok prog (E, ds) st" and "stmt_fits (CG_TyEnv cg) s"
    and "core_statement_type (CG_TyEnv cg) NotGhost s = Some env'"
  obtains E' ds' where "lowered_ok prog (rk_cty (CG_Ret cg)) (E, ds) st S st' (E', ds')" and "cg_ok prog E' cg'"
    and "CG_TyEnv cg' = env'" and "CG_Ret cg' = CG_Ret cg"
  using assms unfolding ls_ok_def by blast

lemma lss_okD:
  assumes "lss_ok prog cg ss" and "lower_stmts cg ss st = Inr ((S, cg'), st')" and "cg_ok prog E cg"
    and "scope_ok prog (E, ds) st" and "stmts_fits (CG_TyEnv cg) ss"
    and "core_statement_list_type (CG_TyEnv cg) NotGhost ss = Some env'"
  obtains E' ds' where "lowered_ok prog (rk_cty (CG_Ret cg)) (E, ds) st S st' (E', ds')" and "cg_ok prog E' cg'"
    and "CG_TyEnv cg' = env'" and "CG_Ret cg' = CG_Ret cg"
  using assms unfolding lss_ok_def by blast

(* The ghost statements and the ghost-flagged forms are rejected. *)
lemma ls_fail:
  "ls_ok prog cg (CoreStmt_VarDecl Ghost a b c d)" "ls_ok prog cg (CoreStmt_VarDeclCall Ghost a1 b1 c1 d1 e1 f1)"
  "ls_ok prog cg (CoreStmt_Assign Ghost a2 b2 c2)" "ls_ok prog cg (CoreStmt_AssignCall Ghost a3 b3 c3 d3 e3)"
  "ls_ok prog cg (CoreStmt_Swap Ghost a4 b4)" "ls_ok prog cg (CoreStmt_While Ghost a5 b5 c5 d5)"
  "ls_ok prog cg (CoreStmt_Match Ghost a6 b6)" "ls_ok prog cg (CoreStmt_Fix a7 b7)" "ls_ok prog cg (CoreStmt_Obtain a8 b8 c8)"
  "ls_ok prog cg (CoreStmt_Use a9)" "ls_ok prog cg (CoreStmt_Assert a10 b10)" "ls_ok prog cg (CoreStmt_Assume a11)"
  "ls_ok prog cg (CoreStmt_ShowHide a12 b12)"
  by (simp_all add: ls_ok_def lower_stmt.simps cg_fail_def)

lemma ls_VarDecl_Var: "ls_ok prog cg (CoreStmt_VarDecl NotGhost x Var ty t)"
  unfolding ls_ok_def
proof (intro allI impI)
  fix E ds st S cg' st' env'
  assume l: "lower_stmt cg (CoreStmt_VarDecl NotGhost x Var ty t) st = Inr ((S, cg'), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and sf: "stmt_fits (CG_TyEnv cg) (CoreStmt_VarDecl NotGhost x Var ty t)"
    and ct: "core_statement_type (CG_TyEnv cg) NotGhost (CoreStmt_VarDecl NotGhost x Var ty t) = Some env'"
  let ?env = "CG_TyEnv cg"
  let ?rt = "rk_cty (CG_Ret cg)"
  from ct have wk: "is_well_kinded ?env ty" and rtt: "is_runtime_type ?env ty" and tt: "core_term_type ?env NotGhost t = Some ty"
    and env': "env' = ?env \<lparr> TE_LocalVars := fmupd x ty (TE_LocalVars ?env), TE_GhostLocals := fminus (TE_GhostLocals ?env) {|x|},
                            TE_ConstLocals := fminus (TE_ConstLocals ?env) {|x|} \<rparr>"
    by (auto split: if_splits)
  note sfs = stmt_fits_VarDecl[OF sf]
  have unf: "cg_bind (lower_term cg t) (\<lambda>(S, e).
      cg_bind (decl_local cg x ty) (\<lambda>(decl, rep).
      cg_bind (init_local cg rep ty e) (\<lambda>init.
      cg_return (S @ [decl] @ init, cg_bind_var cg env' x rep)))) st = Inr ((S, cg'), st')"
    by (rule env_after_InrE[OF l[unfolded lower_stmt.simps] ct])
  from unf obtain r1 st1 where lt': "lower_term cg t st = Inr (r1, st1)"
    and k1: "(\<lambda>(S, e). cg_bind (decl_local cg x ty) (\<lambda>(decl, rep). cg_bind (init_local cg rep ty e) (\<lambda>init.
      cg_return (S @ [decl] @ init, cg_bind_var cg env' x rep)))) r1 st1 = Inr ((S, cg'), st')"
    by (rule cg_bind_InrE)
  obtain S1 e where r1: "r1 = (S1, e)" by (cases r1)
  have lt: "lower_term cg t st = Inr ((S1, e), st1)" using lt' r1 by simp
  from k1[unfolded r1 case_prod_conv] obtain r2 st2 where dl': "decl_local cg x ty st1 = Inr (r2, st2)"
    and k2: "(\<lambda>(decl, rep). cg_bind (init_local cg rep ty e) (\<lambda>init. cg_return (S1 @ [decl] @ init, cg_bind_var cg env' x rep))) r2 st2
             = Inr ((S, cg'), st')"
    by (rule cg_bind_InrE)
  obtain decl rep where r2: "r2 = (decl, rep)" by (cases r2)
  have dl: "decl_local cg x ty st1 = Inr ((decl, rep), st2)" using dl' r2 by simp
  from k2[unfolded r2 case_prod_conv] obtain init st3 where il: "init_local cg rep ty e st2 = Inr (init, st3)"
    and k3: "cg_return (S1 @ [decl] @ init, cg_bind_var cg env' x rep) st3 = Inr ((S, cg'), st')"
    by (rule cg_bind_InrE)
  from k3 have S: "S = S1 @ [decl] @ init" and cg': "cg' = cg_bind_var cg env' x rep" and st': "st' = st3"
    by (auto simp: cg_return_def)
  obtain E1 ds1 ty1 where ty1: "core_term_type ?env NotGhost t = Some ty1"
    and lo1: "lowered_ok prog ?rt (E, ds) st S1 st1 (E1, ds1)" and e: "expr_ok E1 e (res_cty ty1)"
    by (rule lower_term_ok[OF lt ok sc sfs(2)])
  have ty1: "ty1 = ty" using ty1 tt by simp
  have ok1: "cg_ok prog E1 cg" using cg_ok_mono[OF lowered_ok_env_le'[OF lo1] ok] .
  obtain n where d: "lowered_ok prog ?rt (E1, ds1) st1 [decl] st2 (fmupd n (case scalar_ty ty of Some cty \<Rightarrow> VT_Scalar cty | None \<Rightarrow> VT_Buf) E1, n # ds1)"
    and ro: "rep_ok (fmupd n (case scalar_ty ty of Some cty \<Rightarrow> VT_Scalar cty | None \<Rightarrow> VT_Buf) E1) ?env ty rep"
    and rep: "rep = (case scalar_ty ty of Some cty \<Rightarrow> VR_Scalar n cty | None \<Rightarrow> VR_Buf n)"
    by (rule decl_local_ok[OF dl ok1 lowered_ok_scope[OF lo1] wk sfs(1)])
  let ?E2 = "fmupd n (case scalar_ty ty of Some cty \<Rightarrow> VT_Scalar cty | None \<Rightarrow> VT_Buf) E1"
  have le2: "env_le E1 ?E2" by (rule lowered_ok_env_le'[OF d])
  have ok2: "cg_ok prog ?E2 cg" using cg_ok_mono[OF le2 ok1] .
  have e2: "expr_ok ?E2 e (res_cty ty)" using expr_ok_mono[OF le2 e] ty1 by simp
  have sz: "u64_ok ?E2 (cg_size cg ty)" using cg_size_ok[OF ok2 wk sfs(1)] .
  have i: "lowered_ok prog ?rt (?E2, n # ds1) st2 init st2 (?E2, n # ds1)" and st3: "st3 = st2"
    using init_local_ok[OF il lowered_ok_scope[OF d] ro rep e2 sz] by simp_all
  have lo: "lowered_ok prog ?rt (E, ds) st S st' (?E2, n # ds1)"
    unfolding S st' st3 using lowered_ok_append[OF lowered_ok_append[OF lo1 d] i] by simp
  have okd: "cg_ok prog ?E2 cg'" unfolding cg' env' by (rule cg_ok_decl[OF ok1 wk rtt le2 ro])
  show "\<exists>E' ds'. lowered_ok prog ?rt (E, ds) st S st' (E', ds') \<and> cg_ok prog E' cg' \<and> CG_TyEnv cg' = env' \<and> CG_Ret cg' = CG_Ret cg"
    using lo okd unfolding cg' by (auto simp: cg_bind_var_def)
qed

lemma ls_VarDecl_Ref: "ls_ok prog cg (CoreStmt_VarDecl NotGhost x Ref ty lv)"
  unfolding ls_ok_def
proof (intro allI impI)
  fix E ds st S cg' st' env'
  assume l: "lower_stmt cg (CoreStmt_VarDecl NotGhost x Ref ty lv) st = Inr ((S, cg'), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and sf: "stmt_fits (CG_TyEnv cg) (CoreStmt_VarDecl NotGhost x Ref ty lv)"
    and ct: "core_statement_type (CG_TyEnv cg) NotGhost (CoreStmt_VarDecl NotGhost x Ref ty lv) = Some env'"
  let ?env = "CG_TyEnv cg"
  let ?rt = "rk_cty (CG_Ret cg)"
  from ct have wk: "is_well_kinded ?env ty" and rtt: "is_runtime_type ?env ty" and tt: "core_term_type ?env NotGhost lv = Some ty"
    and env': "env' = ?env \<lparr> TE_LocalVars := fmupd x ty (TE_LocalVars ?env), TE_GhostLocals := fminus (TE_GhostLocals ?env) {|x|},
                            TE_ConstLocals := (if is_writable_lvalue ?env lv then fminus (TE_ConstLocals ?env) {|x|}
                                               else finsert x (TE_ConstLocals ?env)) \<rparr>"
    by (auto split: if_splits)
  note sfs = stmt_fits_VarDecl[OF sf]
  have l0: "(if needs_lazy cg lv
             then cg_bind (freeze_lvalue cg lv) (\<lambda>(S, ll). cg_return (S, cg_bind_var cg env' x (VR_Lazy ll)))
             else cg_bind (lower_addr cg lv) (\<lambda>(S, a). cg_bind (local_name (CG_Fun cg) x) (\<lambda>n.
                    cg_return (S @ [MS_DeclScalar n CTy_CharPtr, MS_Assign n a], cg_bind_var cg env' x (VR_Ptr n))))) st
            = Inr ((S, cg'), st')"
    by (rule env_after_InrE[OF l[unfolded lower_stmt.simps] ct])
  show "\<exists>E' ds'. lowered_ok prog ?rt (E, ds) st S st' (E', ds') \<and> cg_ok prog E' cg' \<and> CG_TyEnv cg' = env' \<and> CG_Ret cg' = CG_Ret cg"
  proof (cases "needs_lazy cg lv")
    case True
    from l0[unfolded if_P[OF True]] obtain S1 ll where fr: "freeze_lvalue cg lv st = Inr ((S1, ll), st')" and S: "S = S1"
      and cg': "cg' = cg_bind_var cg env' x (VR_Lazy ll)"
      by (auto simp: cg_return_def split: prod.splits elim!: cg_bind_InrE)
    obtain E1 ds1 where lo: "lowered_ok prog ?rt (E, ds) st S1 st' (E1, ds1)" and lt: "ll_type ll = ty" and lok: "ll_ok E1 ?env ll"
      using freeze_lvalue_ok[OF fr ok sc sfs(2) tt] by blast
    have ro: "rep_ok E1 ?env ty (VR_Lazy ll)" using lt lok by simp
    have okd: "cg_ok prog E1 cg'" unfolding cg' env' by (rule cg_ok_decl[OF ok wk rtt lowered_ok_env_le'[OF lo] ro])
    show ?thesis unfolding S using lo okd unfolding cg' by (auto simp: cg_bind_var_def)
  next
    case False
    from l0[unfolded if_not_P[OF False]] obtain r1 st1 where la': "lower_addr cg lv st = Inr (r1, st1)"
      and k1: "(\<lambda>(S, a). cg_bind (local_name (CG_Fun cg) x) (\<lambda>n.
          cg_return (S @ [MS_DeclScalar n CTy_CharPtr, MS_Assign n a], cg_bind_var cg env' x (VR_Ptr n)))) r1 st1 = Inr ((S, cg'), st')"
      by (rule cg_bind_InrE)
    obtain S1 a where r1: "r1 = (S1, a)" by (cases r1)
    have la: "lower_addr cg lv st = Inr ((S1, a), st1)" using la' r1 by simp
    from k1[unfolded r1 case_prod_conv] obtain n st2 where ln: "local_name (CG_Fun cg) x st1 = Inr (n, st2)"
      and k2: "cg_return (S1 @ [MS_DeclScalar n CTy_CharPtr, MS_Assign n a], cg_bind_var cg env' x (VR_Ptr n)) st2 = Inr ((S, cg'), st')"
      by (rule cg_bind_InrE)
    from k2 have S: "S = S1 @ [MS_DeclScalar n CTy_CharPtr, MS_Assign n a]" and cg': "cg' = cg_bind_var cg env' x (VR_Ptr n)"
      and st': "st' = st2" by (auto simp: cg_return_def)
    obtain E1 ds1 where lo1: "lowered_ok prog ?rt (E, ds) st S1 st1 (E1, ds1)" and a: "expr_ok E1 a CTy_CharPtr"
      by (rule lower_addr_ok[OF la ok sc sfs(2)])
    let ?E2 = "fmupd n (VT_Scalar CTy_CharPtr) E1"
    have d: "lowered_ok prog ?rt (E1, ds1) st1 [MS_DeclScalar n CTy_CharPtr] st2 (?E2, n # ds1)"
      by (rule local_scalar_ok[OF lowered_ok_scope[OF lo1] ln])
    have as: "lowered_ok prog ?rt (?E2, n # ds1) st2 [MS_Assign n a] st2 (?E2, n # ds1)"
      using lowered_ok_scope[OF d] expr_ok_mono[OF lowered_ok_env_le'[OF d] a]
      by (intro assign_ok[where cty' = CTy_CharPtr]) (auto simp: ty_compat_def)
    have lo: "lowered_ok prog ?rt (E, ds) st S st' (?E2, n # ds1)"
      unfolding S st' using lowered_ok_append[OF lowered_ok_append[OF lo1 d] as] by simp
    have ro: "rep_ok ?E2 ?env ty (VR_Ptr n)" by simp
    have okd: "cg_ok prog ?E2 cg'" unfolding cg' env'
      by (rule cg_ok_decl[OF ok wk rtt env_le_trans[OF lowered_ok_env_le'[OF lo1] lowered_ok_env_le'[OF d]] ro])
    show ?thesis using lo okd unfolding cg' by (auto simp: cg_bind_var_def)
  qed
qed

lemma ls_VarDeclCall: "ls_ok prog cg (CoreStmt_VarDeclCall NotGhost x ty castOpt f tys args)"
  unfolding ls_ok_def
proof (intro allI impI)
  fix E ds st S cg' st' env'
  assume l: "lower_stmt cg (CoreStmt_VarDeclCall NotGhost x ty castOpt f tys args) st = Inr ((S, cg'), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and sf: "stmt_fits (CG_TyEnv cg) (CoreStmt_VarDeclCall NotGhost x ty castOpt f tys args)"
    and ct: "core_statement_type (CG_TyEnv cg) NotGhost (CoreStmt_VarDeclCall NotGhost x ty castOpt f tys args) = Some env'"
  let ?env = "CG_TyEnv cg"
  let ?rt = "rk_cty (CG_Ret cg)"
  from ct obtain retTy where wk: "is_well_kinded ?env ty" and rtt: "is_runtime_type ?env ty"
    and ict: "core_impure_call_type ?env NotGhost f tys args = Some retTy"
    and crt: "cast_result_type ?env NotGhost retTy castOpt = Some ty"
    and env': "env' = ?env \<lparr> TE_LocalVars := fmupd x ty (TE_LocalVars ?env), TE_GhostLocals := fminus (TE_GhostLocals ?env) {|x|},
                            TE_ConstLocals := fminus (TE_ConstLocals ?env) {|x|} \<rparr>"
    by (auto split: if_splits option.splits)
  obtain retTy' where fty: "fits ?env ty" and fret: "fits ?env retTy'" and ict': "core_impure_call_type ?env NotGhost f tys args = Some retTy'"
    and ftys: "\<forall>ty \<in> set tys. fits ?env ty" and tfa: "\<forall>a \<in> set args. term_fits ?env a"
    by (rule stmt_fits_VarDeclCall[OF sf])
  have fret: "fits ?env retTy" using fret ict ict' by simp
  obtain info where info: "fmlookup (TE_Functions ?env) f = Some info" using core_impure_call_type_fn_facts[OF ict] by blast
  have ngp: "no_ghost_params info" using cg_ok_prog[OF ok] info unfolding prog_ok_def by blast
  note cti = call_typed_impure[OF ict info ngp]
  have wkret: "is_well_kinded ?env retTy" and rtret: "is_runtime_type ?env retTy"
    using core_impure_call_type_well_kinded_and_runtime[OF ict cg_ok_wf[OF ok]] by simp_all
  have unf: "cg_bind (lower_call cg f tys args) (\<lambda>(Sc, res).
      cg_bind (cast_call_res cg retTy castOpt res) (\<lambda>(Scast, res').
      cg_bind (decl_local cg x ty) (\<lambda>(decl, rep).
      cg_bind (call_store cg (init_local cg rep ty) ty res') (\<lambda>init.
      cg_return (Sc @ Scast @ [decl] @ init, cg_bind_var cg env' x rep))))) st = Inr ((S, cg'), st')"
    by (rule impure_ret_type_bind_InrE[OF env_after_InrE[OF l[unfolded lower_stmt.simps] ct] ict])
  from unf obtain r1 st1 where lc': "lower_call cg f tys args st = Inr (r1, st1)"
    and k1: "(\<lambda>(Sc, res). cg_bind (cast_call_res cg retTy castOpt res) (\<lambda>(Scast, res').
      cg_bind (decl_local cg x ty) (\<lambda>(decl, rep).
      cg_bind (call_store cg (init_local cg rep ty) ty res') (\<lambda>init.
      cg_return (Sc @ Scast @ [decl] @ init, cg_bind_var cg env' x rep))))) r1 st1 = Inr ((S, cg'), st')"
    by (rule cg_bind_InrE)
  obtain Sc res where r1: "r1 = (Sc, res)" by (cases r1)
  have lc: "lower_call cg f tys args st = Inr ((Sc, res), st1)" using lc' r1 by simp
  from k1[unfolded r1 case_prod_conv] obtain r2 st2 where ccr': "cast_call_res cg retTy castOpt res st1 = Inr (r2, st2)"
    and k2: "(\<lambda>(Scast, res'). cg_bind (decl_local cg x ty) (\<lambda>(decl, rep).
      cg_bind (call_store cg (init_local cg rep ty) ty res') (\<lambda>init.
      cg_return (Sc @ Scast @ [decl] @ init, cg_bind_var cg env' x rep)))) r2 st2 = Inr ((S, cg'), st')"
    by (rule cg_bind_InrE)
  obtain Scast res' where r2: "r2 = (Scast, res')" by (cases r2)
  have ccr: "cast_call_res cg retTy castOpt res st1 = Inr ((Scast, res'), st2)" using ccr' r2 by simp
  from k2[unfolded r2 case_prod_conv] obtain r3 st3 where dl': "decl_local cg x ty st2 = Inr (r3, st3)"
    and k3: "(\<lambda>(decl, rep). cg_bind (call_store cg (init_local cg rep ty) ty res') (\<lambda>init.
      cg_return (Sc @ Scast @ [decl] @ init, cg_bind_var cg env' x rep))) r3 st3 = Inr ((S, cg'), st')"
    by (rule cg_bind_InrE)
  obtain decl rep where r3: "r3 = (decl, rep)" by (cases r3)
  have dl: "decl_local cg x ty st2 = Inr ((decl, rep), st3)" using dl' r3 by simp
  from k3[unfolded r3 case_prod_conv] obtain init st4 where cs: "call_store cg (init_local cg rep ty) ty res' st3 = Inr (init, st4)"
    and k4: "cg_return (Sc @ Scast @ [decl] @ init, cg_bind_var cg env' x rep) st4 = Inr ((S, cg'), st')"
    by (rule cg_bind_InrE)
  from k4 have S: "S = Sc @ Scast @ [decl] @ init" and cg': "cg' = cg_bind_var cg env' x rep" and st': "st' = st4"
    by (auto simp: cg_return_def)
  (* the call *)
  obtain E1 ds1 where lo1: "lowered_ok prog ?rt (E, ds) st Sc st1 (E1, ds1)" and ro: "res_ok E1 info res"
    by (rule lower_call_ok[OF lc ok sc info cti(1) tfa ftys wkret[unfolded cti(2)] fret[unfolded cti(2)]])
  have ok1: "cg_ok prog E1 cg" using cg_ok_mono[OF lowered_ok_env_le'[OF lo1] ok] .
  have cres1: "cres_ok E1 retTy res" using cres_ok_of_res_ok[OF ro] unfolding cti(2) .
  (* the cast *)
  obtain E2 ds2 where lo2: "lowered_ok prog ?rt (E1, ds1) st1 Scast st2 (E2, ds2)" and cres2: "cres_ok E2 ty res'"
    using cast_call_res_ok[OF ccr ok1 lowered_ok_scope[OF lo1] cres1 crt wkret rtret fty] by blast
  have ok2: "cg_ok prog E2 cg" using cg_ok_mono[OF lowered_ok_env_le'[OF lo2] ok1] .
  (* the declaration *)
  obtain n where d: "lowered_ok prog ?rt (E2, ds2) st2 [decl] st3 (fmupd n (case scalar_ty ty of Some cty \<Rightarrow> VT_Scalar cty | None \<Rightarrow> VT_Buf) E2, n # ds2)"
    and rok: "rep_ok (fmupd n (case scalar_ty ty of Some cty \<Rightarrow> VT_Scalar cty | None \<Rightarrow> VT_Buf) E2) ?env ty rep"
    and rep: "rep = (case scalar_ty ty of Some cty \<Rightarrow> VR_Scalar n cty | None \<Rightarrow> VR_Buf n)"
    by (rule decl_local_ok[OF dl ok2 lowered_ok_scope[OF lo2] wk fty])
  let ?E3 = "fmupd n (case scalar_ty ty of Some cty \<Rightarrow> VT_Scalar cty | None \<Rightarrow> VT_Buf) E2"
  have le3: "env_le E2 ?E3" by (rule lowered_ok_env_le'[OF d])
  have ok3: "cg_ok prog ?E3 cg" using cg_ok_mono[OF le3 ok2] .
  have sz: "u64_ok ?E3 (cg_size cg ty)" using cg_size_ok[OF ok3 wk fty] .
  (* the store *)
  have i: "\<exists>E' ds'. lowered_ok prog ?rt (?E3, n # ds2) st3 init st4 (E', ds')"
  proof (rule call_store_ok[OF cs cres_ok_mono[OF le3 cres2] lowered_ok_scope[OF d]])
    fix e S' st''
    assume "init_local cg rep ty e st3 = Inr (S', st'')" and "expr_ok ?E3 e (res_cty ty)"
    then show "\<exists>E' ds'. lowered_ok prog ?rt (?E3, n # ds2) st3 S' st'' (E', ds')"
      using init_local_ok[OF _ lowered_ok_scope[OF d] rok rep _ sz] by blast
  qed
  then obtain E4 ds4 where i': "lowered_ok prog ?rt (?E3, n # ds2) st3 init st4 (E4, ds4)" by blast
  have lo: "lowered_ok prog ?rt (E, ds) st S st' (E4, ds4)"
    unfolding S st' using lowered_ok_append[OF lowered_ok_append[OF lowered_ok_append[OF lo1 lo2] d] i'] by simp
  have okd: "cg_ok prog E4 cg'" unfolding cg' env'
    by (rule cg_ok_decl[OF ok2 wk rtt env_le_trans[OF le3 lowered_ok_env_le'[OF i']] rep_ok_mono[OF lowered_ok_env_le'[OF i'] rok]])
  show "\<exists>E' ds'. lowered_ok prog ?rt (E, ds) st S st' (E', ds') \<and> cg_ok prog E' cg' \<and> CG_TyEnv cg' = env' \<and> CG_Ret cg' = CG_Ret cg"
    using lo okd unfolding cg' by (auto simp: cg_bind_var_def)
qed

lemma ls_Assign: "ls_ok prog cg (CoreStmt_Assign NotGhost ty lv t)"
  unfolding ls_ok_def
proof (intro allI impI)
  fix E ds st S cg' st' env'
  assume l: "lower_stmt cg (CoreStmt_Assign NotGhost ty lv t) st = Inr ((S, cg'), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and sf: "stmt_fits (CG_TyEnv cg) (CoreStmt_Assign NotGhost ty lv t)"
    and ct: "core_statement_type (CG_TyEnv cg) NotGhost (CoreStmt_Assign NotGhost ty lv t) = Some env'"
  let ?env = "CG_TyEnv cg"
  let ?rt = "rk_cty (CG_Ret cg)"
  from ct have tl: "core_term_type ?env NotGhost lv = Some ty" and tt: "core_term_type ?env NotGhost t = Some ty" and env': "env' = ?env"
    by (auto split: if_splits)
  note sfs = stmt_fits_Assign[OF sf]
  from l obtain S1 e st1 Ss where lt: "lower_term cg t st = Inr ((S1, e), st1)" and ls: "lower_store cg lv ty e st1 = Inr (Ss, st')"
    and S: "S = S1 @ Ss" and cg': "cg' = cg"
    by (auto simp: lower_stmt.simps cg_return_def split: prod.splits elim!: cg_bind_InrE)
  obtain E1 ds1 ty1 where ty1: "core_term_type ?env NotGhost t = Some ty1"
    and lo1: "lowered_ok prog ?rt (E, ds) st S1 st1 (E1, ds1)" and e: "expr_ok E1 e (res_cty ty1)"
    by (rule lower_term_ok[OF lt ok sc sfs(3)])
  have ty1: "ty1 = ty" using ty1 tt by simp
  obtain E2 ds2 where lo2: "lowered_ok prog ?rt (E1, ds1) st1 Ss st' (E2, ds2)"
    using lower_store_ok[OF ls cg_ok_mono[OF lowered_ok_env_le'[OF lo1] ok] lowered_ok_scope[OF lo1] sfs(2) tl e[unfolded ty1] sfs(1)] by blast
  show "\<exists>E' ds'. lowered_ok prog ?rt (E, ds) st S st' (E', ds') \<and> cg_ok prog E' cg' \<and> CG_TyEnv cg' = env' \<and> CG_Ret cg' = CG_Ret cg"
    unfolding S cg' env' using lowered_ok_append[OF lo1 lo2] cg_ok_mono[OF lowered_ok_env_le'[OF lowered_ok_append[OF lo1 lo2]] ok] by blast
qed

lemma ls_AssignCall: "ls_ok prog cg (CoreStmt_AssignCall NotGhost lv castOpt f tys args)"
  unfolding ls_ok_def
proof (intro allI impI)
  fix E ds st S cg' st' env'
  assume l: "lower_stmt cg (CoreStmt_AssignCall NotGhost lv castOpt f tys args) st = Inr ((S, cg'), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and sf: "stmt_fits (CG_TyEnv cg) (CoreStmt_AssignCall NotGhost lv castOpt f tys args)"
    and ct: "core_statement_type (CG_TyEnv cg) NotGhost (CoreStmt_AssignCall NotGhost lv castOpt f tys args) = Some env'"
  let ?env = "CG_TyEnv cg"
  let ?rt = "rk_cty (CG_Ret cg)"
  have "\<exists>lhsTy retTy. core_term_type ?env NotGhost lv = Some lhsTy
          \<and> core_impure_call_type ?env NotGhost f tys args = Some retTy
          \<and> cast_result_type ?env NotGhost retTy castOpt = Some lhsTy \<and> env' = ?env"
    using ct by (simp split: if_splits option.splits)
  then obtain lhsTy retTy where tl: "core_term_type ?env NotGhost lv = Some lhsTy"
    and ict: "core_impure_call_type ?env NotGhost f tys args = Some retTy"
    and crt: "cast_result_type ?env NotGhost retTy castOpt = Some lhsTy" and env': "env' = ?env" by blast
  obtain retTy' where fret: "fits ?env retTy'" and ict': "core_impure_call_type ?env NotGhost f tys args = Some retTy'"
    and ftys: "\<forall>ty \<in> set tys. fits ?env ty" and tfl: "term_fits ?env lv" and tfa: "\<forall>a \<in> set args. term_fits ?env a"
    by (rule stmt_fits_AssignCall[OF sf])
  have fret: "fits ?env retTy" using fret ict ict' by simp
  have flhs: "fits ?env lhsTy" using term_fits_ty[OF tfl tl] .
  obtain info where info: "fmlookup (TE_Functions ?env) f = Some info" using core_impure_call_type_fn_facts[OF ict] by blast
  have ngp: "no_ghost_params info" using cg_ok_prog[OF ok] info unfolding prog_ok_def by blast
  note cti = call_typed_impure[OF ict info ngp]
  have wkret: "is_well_kinded ?env retTy" and rtret: "is_runtime_type ?env retTy"
    using core_impure_call_type_well_kinded_and_runtime[OF ict cg_ok_wf[OF ok]] by simp_all
  have unf: "lower_stmt cg (CoreStmt_AssignCall NotGhost lv castOpt f tys args) st =
      cg_bind (lower_call cg f tys args) (\<lambda>(Sc, res).
      cg_bind (cast_call_res cg retTy castOpt res) (\<lambda>(Scast, res').
      cg_bind (call_store cg (lower_store cg lv lhsTy) lhsTy res') (\<lambda>Ss.
      cg_return (Sc @ Scast @ Ss, cg)))) st"
    unfolding lower_stmt.simps impure_ret_type_def by (simp add: cg_bind_def cg_lift_def ty_of_Some[OF tl] ict cg_return_def)
  from l[unfolded unf] obtain r2 st2 where lc': "lower_call cg f tys args st = Inr (r2, st2)"
    and k2: "(\<lambda>(Sc, res). cg_bind (cast_call_res cg retTy castOpt res) (\<lambda>(Scast, res').
      cg_bind (call_store cg (lower_store cg lv lhsTy) lhsTy res') (\<lambda>Ss.
      cg_return (Sc @ Scast @ Ss, cg)))) r2 st2 = Inr ((S, cg'), st')"
    by (rule cg_bind_InrE)
  obtain Sc res where r2: "r2 = (Sc, res)" by (cases r2)
  have lc: "lower_call cg f tys args st = Inr ((Sc, res), st2)" using lc' r2 by simp
  from k2[unfolded r2 case_prod_conv] obtain r3 st3 where ccr': "cast_call_res cg retTy castOpt res st2 = Inr (r3, st3)"
    and k3: "(\<lambda>(Scast, res'). cg_bind (call_store cg (lower_store cg lv lhsTy) lhsTy res') (\<lambda>Ss.
      cg_return (Sc @ Scast @ Ss, cg))) r3 st3 = Inr ((S, cg'), st')"
    by (rule cg_bind_InrE)
  obtain Scast res' where r3: "r3 = (Scast, res')" by (cases r3)
  have ccr: "cast_call_res cg retTy castOpt res st2 = Inr ((Scast, res'), st3)" using ccr' r3 by simp
  from k3[unfolded r3 case_prod_conv] obtain Ss st4 where cs: "call_store cg (lower_store cg lv lhsTy) lhsTy res' st3 = Inr (Ss, st4)"
    and k4: "cg_return (Sc @ Scast @ Ss, cg) st4 = Inr ((S, cg'), st')"
    by (rule cg_bind_InrE)
  from k4 have S: "S = Sc @ Scast @ Ss" and cg': "cg' = cg" and st': "st' = st4" by (auto simp: cg_return_def)
  (* the call *)
  obtain E2 ds2 where lo2: "lowered_ok prog ?rt (E, ds) st Sc st2 (E2, ds2)" and ro: "res_ok E2 info res"
    by (rule lower_call_ok[OF lc ok sc info cti(1) tfa ftys wkret[unfolded cti(2)] fret[unfolded cti(2)]])
  have ok2: "cg_ok prog E2 cg" using cg_ok_mono[OF lowered_ok_env_le'[OF lo2] ok] .
  have cres2: "cres_ok E2 retTy res" using cres_ok_of_res_ok[OF ro] unfolding cti(2) .
  (* the cast *)
  obtain E3 ds3 where lo3: "lowered_ok prog ?rt (E2, ds2) st2 Scast st3 (E3, ds3)" and cres3: "cres_ok E3 lhsTy res'"
    using cast_call_res_ok[OF ccr ok2 lowered_ok_scope[OF lo2] cres2 crt wkret rtret flhs] by blast
  have ok3: "cg_ok prog E3 cg" using cg_ok_mono[OF lowered_ok_env_le'[OF lo3] ok2] .
  (* the store, through the lvalue computed after the call *)
  have "\<exists>E' ds'. lowered_ok prog ?rt (E3, ds3) st3 Ss st4 (E', ds')"
  proof (rule call_store_ok[OF cs cres3 lowered_ok_scope[OF lo3]])
    fix e S' st''
    assume "lower_store cg lv lhsTy e st3 = Inr (S', st'')" and "expr_ok E3 e (res_cty lhsTy)"
    then show "\<exists>E' ds'. lowered_ok prog ?rt (E3, ds3) st3 S' st'' (E', ds')"
      using lower_store_ok[OF _ ok3 lowered_ok_scope[OF lo3] tfl tl _ flhs] by blast
  qed
  then obtain E4 ds4 where lo4: "lowered_ok prog ?rt (E3, ds3) st3 Ss st4 (E4, ds4)" by blast
  have lo: "lowered_ok prog ?rt (E, ds) st S st' (E4, ds4)"
    unfolding S st' using lowered_ok_append[OF lowered_ok_append[OF lo2 lo3] lo4] by simp
  show "\<exists>E' ds'. lowered_ok prog ?rt (E, ds) st S st' (E', ds') \<and> cg_ok prog E' cg' \<and> CG_TyEnv cg' = env' \<and> CG_Ret cg' = CG_Ret cg"
    unfolding cg' env' using lo cg_ok_mono[OF lowered_ok_env_le'[OF lo] ok] by blast
qed

lemma ls_Swap: "ls_ok prog cg (CoreStmt_Swap NotGhost lv1 lv2)"
  unfolding ls_ok_def
proof (intro allI impI)
  fix E ds st S cg' st' env'
  assume l: "lower_stmt cg (CoreStmt_Swap NotGhost lv1 lv2) st = Inr ((S, cg'), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and sf: "stmt_fits (CG_TyEnv cg) (CoreStmt_Swap NotGhost lv1 lv2)"
    and ct: "core_statement_type (CG_TyEnv cg) NotGhost (CoreStmt_Swap NotGhost lv1 lv2) = Some env'"
  let ?env = "CG_TyEnv cg"
  let ?rt = "rk_cty (CG_Ret cg)"
  from ct obtain ty where t1: "core_term_type ?env NotGhost lv1 = Some ty" and t2: "core_term_type ?env NotGhost lv2 = Some ty"
    and env': "env' = ?env"
    by (auto split: if_splits option.splits)
  note sfs = stmt_fits_Swap[OF sf]
  have wk: "is_well_kinded ?env ty" using term_type_wk(1)[OF ok t1] .
  have fty: "fits ?env ty" using term_fits_ty[OF sfs(1) t1] .
  let ?body = "\<lambda>tmp a1 a2. (case scalar_ty ty of
                    Some cty \<Rightarrow> [MS_Assign tmp (ME_Load cty a1), MS_Store cty a1 (ME_Load cty a2), MS_Store cty a2 (ME_Var tmp)]
                  | None \<Rightarrow> [MS_Copy (ME_AddrOf tmp) a1 (cg_size cg ty), MS_Copy a1 a2 (cg_size cg ty), MS_Copy a2 (ME_AddrOf tmp) (cg_size cg ty)])"
  have unf: "lower_stmt cg (CoreStmt_Swap NotGhost lv1 lv2) st =
      cg_bind (lower_addr cg lv1) (\<lambda>(S1, a1).
      cg_bind (lower_addr cg lv2) (\<lambda>(S2, a2).
      cg_bind (temp_for cg ''swap'' ty) (\<lambda>(tmp, decl).
      cg_return (S1 @ S2 @ [decl] @ ?body tmp a1 a2, cg)))) st"
    unfolding lower_stmt.simps by (simp add: cg_bind_def ty_of_Some[OF t1] cg_return_def)
  from l[unfolded unf] obtain r1 st1 where la1': "lower_addr cg lv1 st = Inr (r1, st1)"
    and k1: "(\<lambda>(S1, a1). cg_bind (lower_addr cg lv2) (\<lambda>(S2, a2).
      cg_bind (temp_for cg ''swap'' ty) (\<lambda>(tmp, decl).
      cg_return (S1 @ S2 @ [decl] @ ?body tmp a1 a2, cg)))) r1 st1 = Inr ((S, cg'), st')"
    by (rule cg_bind_InrE)
  obtain S1 a1 where r1: "r1 = (S1, a1)" by (cases r1)
  have la1: "lower_addr cg lv1 st = Inr ((S1, a1), st1)" using la1' r1 by simp
  from k1[unfolded r1 case_prod_conv] obtain r2 st2 where la2': "lower_addr cg lv2 st1 = Inr (r2, st2)"
    and k2: "(\<lambda>(S2, a2). cg_bind (temp_for cg ''swap'' ty) (\<lambda>(tmp, decl).
      cg_return (S1 @ S2 @ [decl] @ ?body tmp a1 a2, cg))) r2 st2 = Inr ((S, cg'), st')"
    by (rule cg_bind_InrE)
  obtain S2 a2 where r2: "r2 = (S2, a2)" by (cases r2)
  have la2: "lower_addr cg lv2 st1 = Inr ((S2, a2), st2)" using la2' r2 by simp
  from k2[unfolded r2 case_prod_conv] obtain r3 st3 where tf': "temp_for cg ''swap'' ty st2 = Inr (r3, st3)"
    and k3: "(\<lambda>(tmp, decl). cg_return (S1 @ S2 @ [decl] @ ?body tmp a1 a2, cg)) r3 st3 = Inr ((S, cg'), st')"
    by (rule cg_bind_InrE)
  obtain tmp decl where r3: "r3 = (tmp, decl)" by (cases r3)
  have tfr: "temp_for cg ''swap'' ty st2 = Inr ((tmp, decl), st3)" using tf' r3 by simp
  from k3 have S: "S = S1 @ S2 @ [decl] @ ?body tmp a1 a2" and cg': "cg' = cg" and st': "st' = st3"
    unfolding r3 by (auto simp: cg_return_def)
  obtain E1 ds1 where lo1: "lowered_ok prog ?rt (E, ds) st S1 st1 (E1, ds1)" and a1: "expr_ok E1 a1 CTy_CharPtr"
    by (rule lower_addr_ok[OF la1 ok sc sfs(1)])
  have ok1: "cg_ok prog E1 cg" using cg_ok_mono[OF lowered_ok_env_le'[OF lo1] ok] .
  obtain E2 ds2 where lo2: "lowered_ok prog ?rt (E1, ds1) st1 S2 st2 (E2, ds2)" and a2: "expr_ok E2 a2 CTy_CharPtr"
    by (rule lower_addr_ok[OF la2 ok1 lowered_ok_scope[OF lo1] sfs(2)])
  have ok2: "cg_ok prog E2 cg" using cg_ok_mono[OF lowered_ok_env_le'[OF lo2] ok1] .
  from temp_for_ok[OF tfr ok2 lowered_ok_scope[OF lo2] wk fty] obtain E3 where
    d: "lowered_ok prog ?rt (E2, ds2) st2 [decl] st3 (E3, tmp # ds2)"
    and lk: "fmlookup E3 tmp = Some (case scalar_ty ty of Some cty \<Rightarrow> VT_Scalar cty | None \<Rightarrow> VT_Buf)"
    by blast
  have le3: "env_le E2 E3" by (rule lowered_ok_env_le'[OF d])
  have ok3: "cg_ok prog E3 cg" using cg_ok_mono[OF le3 ok2] .
  have a1: "expr_ok E3 a1 CTy_CharPtr" using expr_ok_mono[OF le3 expr_ok_mono[OF lowered_ok_env_le'[OF lo2] a1]] .
  have a2: "expr_ok E3 a2 CTy_CharPtr" using expr_ok_mono[OF le3 a2] .
  have sc3: "scope_ok prog (E3, tmp # ds2) st3" by (rule lowered_ok_scope[OF d])
  have body: "lowered_ok prog ?rt (E3, tmp # ds2) st3 (?body tmp a1 a2) st3 (E3, tmp # ds2)"
  proof (cases "scalar_ty ty")
    case (Some cty)
    have tmpv: "expr_ok E3 (ME_Var tmp) cty" using lk Some by (intro expr_ok_Var) simp
    have s1: "lowered_ok prog ?rt (E3, tmp # ds2) st3 [MS_Assign tmp (ME_Load cty a1)] st3 (E3, tmp # ds2)"
      using sc3 lk Some expr_ok_Load[OF a1] by (intro assign_ok[where cty' = cty]) (auto simp: ty_compat_def)
    have s2: "lowered_ok prog ?rt (E3, tmp # ds2) st3 [MS_Store cty a1 (ME_Load cty a2)] st3 (E3, tmp # ds2)"
      using sc3 a1 expr_ok_Load[OF a2] by (intro store_ok[where cty' = cty]) (auto simp: ty_compat_def)
    have s3: "lowered_ok prog ?rt (E3, tmp # ds2) st3 [MS_Store cty a2 (ME_Var tmp)] st3 (E3, tmp # ds2)"
      using sc3 a2 tmpv by (intro store_ok[where cty' = cty]) (auto simp: ty_compat_def)
    show ?thesis unfolding Some option.case using lowered_ok_append[OF lowered_ok_append[OF s1 s2] s3] by simp
  next
    case None
    have tmpa: "expr_ok E3 (ME_AddrOf tmp) CTy_CharPtr" using lk None by (intro expr_ok_AddrOf) simp
    have sz: "u64_ok E3 (cg_size cg ty)" using cg_size_ok[OF ok3 wk fty] .
    have s1: "lowered_ok prog ?rt (E3, tmp # ds2) st3 [MS_Copy (ME_AddrOf tmp) a1 (cg_size cg ty)] st3 (E3, tmp # ds2)"
      using sc3 tmpa a1 sz by (intro copy_ok[where dty = CTy_CharPtr and sty = CTy_CharPtr]) auto
    have s2: "lowered_ok prog ?rt (E3, tmp # ds2) st3 [MS_Copy a1 a2 (cg_size cg ty)] st3 (E3, tmp # ds2)"
      using sc3 a1 a2 sz by (intro copy_ok[where dty = CTy_CharPtr and sty = CTy_CharPtr]) auto
    have s3: "lowered_ok prog ?rt (E3, tmp # ds2) st3 [MS_Copy a2 (ME_AddrOf tmp) (cg_size cg ty)] st3 (E3, tmp # ds2)"
      using sc3 a2 tmpa sz by (intro copy_ok[where dty = CTy_CharPtr and sty = CTy_CharPtr]) auto
    show ?thesis unfolding None option.case using lowered_ok_append[OF lowered_ok_append[OF s1 s2] s3] by simp
  qed
  have lo: "lowered_ok prog ?rt (E, ds) st S st' (E3, tmp # ds2)"
    unfolding S st' using lowered_ok_append[OF lowered_ok_append[OF lowered_ok_append[OF lo1 lo2] d] body] by simp
  show "\<exists>E' ds'. lowered_ok prog ?rt (E, ds) st S st' (E', ds') \<and> cg_ok prog E' cg' \<and> CG_TyEnv cg' = env' \<and> CG_Ret cg' = CG_Ret cg"
    unfolding cg' env' using lo ok3 by blast
qed

lemma ls_Return: "ls_ok prog cg (CoreStmt_Return t)"
  unfolding ls_ok_def
proof (intro allI impI)
  fix E ds st S cg' st' env'
  assume l: "lower_stmt cg (CoreStmt_Return t) st = Inr ((S, cg'), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and sf: "stmt_fits (CG_TyEnv cg) (CoreStmt_Return t)"
    and ct: "core_statement_type (CG_TyEnv cg) NotGhost (CoreStmt_Return t) = Some env'"
  let ?env = "CG_TyEnv cg"
  let ?rt = "rk_cty (CG_Ret cg)"
  let ?R = "TE_ReturnType ?env"
  from ct have tt: "core_term_type ?env NotGhost t = Some ?R" and env': "env' = ?env" by (auto split: if_splits)
  note tf = stmt_fits_Return[OF sf]
  note rk = cg_ok_ret[OF ok]
  show "\<exists>E' ds'. lowered_ok prog ?rt (E, ds) st S st' (E', ds') \<and> cg_ok prog E' cg' \<and> CG_TyEnv cg' = env' \<and> CG_Ret cg' = CG_Ret cg"
  proof (cases "CG_Ret cg")
    case (RK_Scalar cty)
    have sty: "scalar_ty ?R = Some cty" using rk RK_Scalar by (auto simp: ret_kind_def split: option.splits if_splits)
    from l obtain S1 e where lt: "lower_term cg t st = Inr ((S1, e), st')" and S: "S = S1 @ [MS_Return (Some e)]" and cg': "cg' = cg"
      unfolding lower_stmt.simps RK_Scalar RetKind.case by (auto simp: cg_return_def split: prod.splits elim!: cg_bind_InrE)
    obtain E1 ds1 ty1 where ty1: "core_term_type ?env NotGhost t = Some ty1"
      and lo1: "lowered_ok prog ?rt (E, ds) st S1 st' (E1, ds1)" and e: "expr_ok E1 e (res_cty ty1)"
      by (rule lower_term_ok[OF lt ok sc tf])
    have e: "expr_ok E1 e cty" using e ty1 tt sty by simp
    have r: "lowered_ok prog ?rt (E1, ds1) st' [MS_Return (Some e)] st' (E1, ds1)"
      using lowered_ok_scope[OF lo1] e RK_Scalar by (intro return_ok[where cty' = cty]) (auto simp: ty_compat_def)
    show ?thesis unfolding S cg' env' using lowered_ok_append[OF lo1 r] cg_ok_mono[OF lowered_ok_env_le'[OF lo1] ok] by blast
  next
    case RK_Unit
    show ?thesis
    proof (cases "t = CoreTm_Record []")
      case True
      have S: "S = [MS_Return None]" "cg' = cg" "st' = st" using l unfolding lower_stmt.simps RK_Unit RetKind.case True
        by (auto simp: cg_return_def)
      show ?thesis unfolding S env' using return_none_ok[OF sc] RK_Unit ok by auto
    next
      case False
      from l obtain S1 e where lt: "lower_term cg t st = Inr ((S1, e), st')" and S: "S = S1 @ [MS_Return None]" and cg': "cg' = cg"
        unfolding lower_stmt.simps RK_Unit RetKind.case using False by (auto simp: cg_return_def split: prod.splits elim!: cg_bind_InrE)
      obtain E1 ds1 ty1 where lo1: "lowered_ok prog ?rt (E, ds) st S1 st' (E1, ds1)"
        by (rule lower_term_ok[OF lt ok sc tf])
      have r: "lowered_ok prog ?rt (E1, ds1) st' [MS_Return None] st' (E1, ds1)"
        using lowered_ok_scope[OF lo1] RK_Unit by (intro return_none_ok) auto
      show ?thesis unfolding S cg' env' using lowered_ok_append[OF lo1 r] cg_ok_mono[OF lowered_ok_env_le'[OF lo1] ok] by blast
    qed
  next
    case RK_Buf
    have sty: "scalar_ty ?R = None" using rk RK_Buf by (auto simp: ret_kind_def split: option.splits if_splits)
    have l1: "cg_bind (lower_term cg t) (\<lambda>(S, p).
                cg_return (S @ [MS_Copy (ME_Var ret_param) p (cg_size cg ?R), MS_Return None], cg)) st = Inr ((S, cg'), st')"
      using l unfolding lower_stmt.simps RK_Buf RetKind.case .
    from l1 obtain r1 st1 where lt': "lower_term cg t st = Inr (r1, st1)"
      and k1: "(\<lambda>(S, p). cg_return (S @ [MS_Copy (ME_Var ret_param) p (cg_size cg ?R), MS_Return None], cg)) r1 st1 = Inr ((S, cg'), st')"
      by (rule cg_bind_InrE)
    obtain S1 p where r1: "r1 = (S1, p)" by (cases r1)
    have lt: "lower_term cg t st = Inr ((S1, p), st1)" using lt' r1 by simp
    from k1 have S: "S = S1 @ [MS_Copy (ME_Var ret_param) p (cg_size cg ?R), MS_Return None]" and cg': "cg' = cg" and st': "st' = st1"
      unfolding r1 by (auto simp: cg_return_def)
    note lt = lt[folded st']
    obtain E1 ds1 ty1 where ty1: "core_term_type ?env NotGhost t = Some ty1"
      and lo1: "lowered_ok prog ?rt (E, ds) st S1 st' (E1, ds1)" and p: "expr_ok E1 p (res_cty ty1)"
      by (rule lower_term_ok[OF lt ok sc tf])
    have p: "expr_ok E1 p CTy_CharPtr" using p ty1 tt sty by simp
    have le1: "env_le E E1" by (rule lowered_ok_env_le'[OF lo1])
    have ok1: "cg_ok prog E1 cg" using cg_ok_mono[OF le1 ok] .
    have rp: "expr_ok E1 (ME_Var ret_param) CTy_CharPtr"
      using env_le_lookup[OF le1 cg_ok_ret_param[OF ok RK_Buf]] by (intro expr_ok_Var)
    have sz: "u64_ok E1 (cg_size cg ?R)"
      using cg_size_ok[OF ok1 term_type_wk(1)[OF ok tt]] cg_ok_ret_fits[OF ok] by (simp add: fits_def)
    have c: "lowered_ok prog ?rt (E1, ds1) st' [MS_Copy (ME_Var ret_param) p (cg_size cg ?R)] st' (E1, ds1)"
      using lowered_ok_scope[OF lo1] rp p sz by (intro copy_ok[where dty = CTy_CharPtr and sty = CTy_CharPtr]) auto
    have r: "lowered_ok prog ?rt (E1, ds1) st' [MS_Return None] st' (E1, ds1)"
      using lowered_ok_scope[OF lo1] RK_Buf by (intro return_none_ok) auto
    have "lowered_ok prog ?rt (E, ds) st S st' (E1, ds1)"
      unfolding S using lowered_ok_append[OF lo1 lowered_ok_append[OF c r]] by simp
    then show ?thesis unfolding cg' env' using ok1 by blast
  qed
qed

lemma ls_While:
  assumes IH: "\<And>x st st' xa y. lower_term cg c st = Inr (x, st') \<Longrightarrow> (xa, y) = x \<Longrightarrow> lss_ok prog (cg_nested cg) body"
  shows "ls_ok prog cg (CoreStmt_While NotGhost c invs decr body)"
  unfolding ls_ok_def
proof (intro allI impI)
  fix E ds st S cg' st' env'
  assume l: "lower_stmt cg (CoreStmt_While NotGhost c invs decr body) st = Inr ((S, cg'), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and sf: "stmt_fits (CG_TyEnv cg) (CoreStmt_While NotGhost c invs decr body)"
    and ct: "core_statement_type (CG_TyEnv cg) NotGhost (CoreStmt_While NotGhost c invs decr body) = Some env'"
  let ?env = "CG_TyEnv cg"
  let ?rt = "rk_cty (CG_Ret cg)"
  from ct obtain envb where tc: "core_term_type ?env NotGhost c = Some CoreTy_Bool"
    and tb: "core_statement_list_type (?env \<lparr> TE_ProofTopLevel := False \<rparr>) NotGhost body = Some envb" and env': "env' = ?env"
    by (auto split: if_splits option.splits CoreType.splits)
  note sfs = stmt_fits_While[OF sf]
  from l obtain Sc ec st1 Sb cgb where lt: "lower_term cg c st = Inr ((Sc, ec), st1)"
    and lb: "lower_stmts (cg_nested cg) body st1 = Inr ((Sb, cgb), st')"
    and S: "S = [MS_Loop (Sc @ [MS_If (ME_Unop CU_Not ec) [MS_Break] []] @ Sb)]" and cg': "cg' = cg"
    by (auto simp: lower_stmt.simps cg_return_def split: prod.splits elim!: cg_bind_InrE)
  obtain E1 ds1 ty1 where ty1: "core_term_type ?env NotGhost c = Some ty1"
    and lo1: "lowered_ok prog ?rt (E, []) st Sc st1 (E1, ds1)" and ec: "expr_ok E1 ec (res_cty ty1)"
    by (rule lower_term_ok[OF lt ok scope_ok_inner[OF sc] sfs(1)])
  have ec: "expr_ok E1 ec CTy_U8" using ec ty1 tc by simp
  have okn: "cg_ok prog E1 (cg_nested cg)" using cg_ok_nested[OF cg_ok_mono[OF lowered_ok_env_le'[OF lo1] ok]] .
  obtain E2 ds2 where lo2: "lowered_ok prog (rk_cty (CG_Ret (cg_nested cg))) (E1, ds1) st1 Sb st' (E2, ds2)"
    by (rule lss_okD[OF IH[OF lt refl] lb okn lowered_ok_scope[OF lo1]]) (use sfs(2) tb in \<open>simp_all add: cg_nested_def\<close>)
  have "lowered_ok prog ?rt (E, ds) st S st' (E, ds)"
    unfolding S using while_loop_ok[OF sc lo1 ec lo2[unfolded cg_nested_def, simplified]] by simp
  then show "\<exists>E' ds'. lowered_ok prog ?rt (E, ds) st S st' (E', ds') \<and> cg_ok prog E' cg' \<and> CG_TyEnv cg' = env' \<and> CG_Ret cg' = CG_Ret cg"
    unfolding cg' env' using ok by blast
qed

lemma ls_Match:
  assumes IH: "\<And>x st st' xa sta st'a xb y xaa stb st'b xab ya xac xad yb xae stc st'c.
        ty_of cg s st = Inr (x, st') \<Longrightarrow> lower_term cg s sta = Inr (xa, st'a) \<Longrightarrow> (xb, y) = xa \<Longrightarrow>
        match_tag cg x y stb = Inr (xaa, st'b) \<Longrightarrow> (xab, ya) = xaa \<Longrightarrow> xac \<in> set arms \<Longrightarrow> (xad, yb) = xac \<Longrightarrow>
        arm_cond cg x ya xad stc = Inr (xae, st'c) \<Longrightarrow> lss_ok prog (cg_nested cg) yb"
  shows "ls_ok prog cg (CoreStmt_Match NotGhost s arms)"
  unfolding ls_ok_def
proof (intro allI impI)
  fix E ds st S cg' st' env'
  assume l: "lower_stmt cg (CoreStmt_Match NotGhost s arms) st = Inr ((S, cg'), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and sf: "stmt_fits (CG_TyEnv cg) (CoreStmt_Match NotGhost s arms)"
    and ct: "core_statement_type (CG_TyEnv cg) NotGhost (CoreStmt_Match NotGhost s arms) = Some env'"
  let ?env = "CG_TyEnv cg"
  let ?envn = "?env \<lparr> TE_ProofTopLevel := False \<rparr>"
  let ?rt = "rk_cty (CG_Ret cg)"
  from ct obtain scrutTy where ts: "core_term_type ?env NotGhost s = Some scrutTy"
    and pats: "list_all (\<lambda>p. pattern_compatible ?env p scrutTy) (map fst arms)"
    and bodies: "list_all (\<lambda>body. core_statement_list_type ?envn NotGhost body \<noteq> None) (map snd arms)"
    and env': "env' = ?env"
    by (auto simp: Let_def split: if_splits option.splits)
  have arm_ty: "\<And>p body. (p, body) \<in> set arms \<Longrightarrow>
      pattern_compatible ?env p scrutTy \<and> (\<exists>envb. core_statement_list_type ?envn NotGhost body = Some envb)"
  proof -
    fix p body assume m: "(p, body) \<in> set arms"
    have "p \<in> set (map fst arms)" using m by force
    moreover have "body \<in> set (map snd arms)" using m by force
    ultimately show "pattern_compatible ?env p scrutTy \<and> (\<exists>envb. core_statement_list_type ?envn NotGhost body = Some envb)"
      using pats bodies unfolding list_all_iff by blast
  qed
  note sfs = stmt_fits_Match[OF sf]
  let ?arm = "\<lambda>tag. \<lambda>(pat, body). cg_bind (arm_cond cg scrutTy tag pat)
                 (\<lambda>c. cg_bind (lower_stmts (cg_nested cg) body) (\<lambda>(Sb, _). cg_return (c, Sb)))"
  have unf: "lower_stmt cg (CoreStmt_Match NotGhost s arms) st =
      cg_bind (lower_term cg s) (\<lambda>(Ss, es).
      cg_bind (match_tag cg scrutTy es) (\<lambda>(St, tag).
      cg_bind (cg_mapM (?arm tag) arms) (\<lambda>armsL.
      cg_return (Ss @ St @ if_chain armsL, cg)))) st"
    unfolding lower_stmt.simps by (simp add: cg_bind_def ty_of_Some[OF ts] cg_return_def)
  from l[unfolded unf] obtain r1 st1 where ls': "lower_term cg s st = Inr (r1, st1)"
    and k1: "(\<lambda>(Ss, es). cg_bind (match_tag cg scrutTy es) (\<lambda>(St, tag).
      cg_bind (cg_mapM (?arm tag) arms) (\<lambda>armsL.
      cg_return (Ss @ St @ if_chain armsL, cg)))) r1 st1 = Inr ((S, cg'), st')"
    by (rule cg_bind_InrE)
  obtain Ss es where r1: "r1 = (Ss, es)" by (cases r1)
  have ls: "lower_term cg s st = Inr ((Ss, es), st1)" using ls' r1 by simp
  from k1[unfolded r1 case_prod_conv] obtain r2 st2 where mt': "match_tag cg scrutTy es st1 = Inr (r2, st2)"
    and k2: "(\<lambda>(St, tag). cg_bind (cg_mapM (?arm tag) arms) (\<lambda>armsL.
      cg_return (Ss @ St @ if_chain armsL, cg))) r2 st2 = Inr ((S, cg'), st')"
    by (rule cg_bind_InrE)
  obtain St tag where r2: "r2 = (St, tag)" by (cases r2)
  have mt: "match_tag cg scrutTy es st1 = Inr ((St, tag), st2)" using mt' r2 by simp
  from k2[unfolded r2 case_prod_conv] obtain armsL st3 where lm: "cg_mapM (?arm tag) arms st2 = Inr (armsL, st3)"
    and k3: "cg_return (Ss @ St @ if_chain armsL, cg) st3 = Inr ((S, cg'), st')"
    by (rule cg_bind_InrE)
  from k3 have S: "S = Ss @ St @ if_chain armsL" and cg': "cg' = cg" and st': "st' = st3" by (auto simp: cg_return_def)
  note lm = lm[folded st']
  (* the scrutinee *)
  obtain E1 ds1 ty1 where ty1: "core_term_type ?env NotGhost s = Some ty1"
    and lo1: "lowered_ok prog ?rt (E, ds) st Ss st1 (E1, ds1)" and es: "expr_ok E1 es (res_cty ty1)"
    by (rule lower_term_ok[OF ls ok sc sfs(1)])
  have ty1: "ty1 = scrutTy" using ty1 ts by simp
  (* the tag *)
  obtain E2 ds2 where lo2: "lowered_ok prog ?rt (E1, ds1) st1 St st2 (E2, ds2)" and tag: "expr_ok E2 tag (tag_cty ?env scrutTy)"
    using match_tag_ok[OF mt lowered_ok_scope[OF lo1] es[unfolded ty1]] by blast
  have ok2: "cg_ok prog E2 cg" using cg_ok_mono[OF lowered_ok_env_le'[OF lo2] cg_ok_mono[OF lowered_ok_env_le'[OF lo1] ok]] .
  have sc2: "scope_ok prog (E2, ds2) st2" by (rule lowered_ok_scope[OF lo2])
  (* the arms *)
  have arms: "(\<forall>(c, Sb) \<in> set armsL. (\<forall>ce. c = Some ce \<longrightarrow> expr_ok E2 ce CTy_U8)
                \<and> stmts_ok (mk_ctx prog ?rt) (E2, []) Sb \<noteq> None \<and> (\<forall>l. stmts_wf prog l Sb)) \<and> used_le st2 st'"
  proof (rule cg_mapM_same_scope[OF lm sc2])
    fix x sta y stb
    assume x: "x \<in> set arms" and fx: "?arm tag x sta = Inr (y, stb)" and sca: "scope_ok prog (E2, ds2) sta"
    obtain pat body where xpb: "x = (pat, body)" by (cases x)
    obtain envb where pc: "pattern_compatible ?env pat scrutTy" and bt: "core_statement_list_type ?envn NotGhost body = Some envb"
      using arm_ty x unfolding xpb by blast
    have sfb: "stmts_fits ?envn body" using sfs(2) x unfolding xpb by blast
    have fx': "cg_bind (arm_cond cg scrutTy tag pat) (\<lambda>c. cg_bind (lower_stmts (cg_nested cg) body) (\<lambda>(Sb, _). cg_return (c, Sb))) sta
               = Inr (y, stb)"
      using fx unfolding xpb by simp
    from fx' obtain c sta1 where ac: "arm_cond cg scrutTy tag pat sta = Inr (c, sta1)"
      and k5: "cg_bind (lower_stmts (cg_nested cg) body) (\<lambda>(Sb, _). cg_return (c, Sb)) sta1 = Inr (y, stb)"
      by (rule cg_bind_InrE)
    have acok: "sta1 = sta \<and> (\<forall>ce. c = Some ce \<longrightarrow> expr_ok E2 ce CTy_U8)"
      by (rule arm_cond_ok[OF ac cg_ok_wf[OF ok] cg_ok_tags[OF ok] tag pc])
    from k5 obtain Sb cgb where lb': "lower_stmts (cg_nested cg) body sta1 = Inr ((Sb, cgb), stb)" and y: "y = (c, Sb)"
      by (auto simp: cg_return_def split: prod.splits elim!: cg_bind_InrE)
    have lb: "lower_stmts (cg_nested cg) body sta = Inr ((Sb, cgb), stb)" using lb' acok by simp
    have okn: "cg_ok prog E2 (cg_nested cg)" using cg_ok_nested[OF ok2] .
    obtain E4 ds4 where lo4: "lowered_ok prog (rk_cty (CG_Ret (cg_nested cg))) (E2, []) sta Sb stb (E4, ds4)"
      by (rule lss_okD[OF IH[OF ty_of_Some[OF ts] ls refl mt refl x xpb[symmetric] ac] lb okn scope_ok_inner[OF sca]])
         (use sfb bt in \<open>simp_all add: cg_nested_def\<close>)
    show "(case y of (c, Sb) \<Rightarrow> (\<forall>ce. c = Some ce \<longrightarrow> expr_ok E2 ce CTy_U8)
                \<and> stmts_ok (mk_ctx prog ?rt) (E2, []) Sb \<noteq> None \<and> (\<forall>l. stmts_wf prog l Sb)) \<and> used_le sta stb"
      using acok lo4[unfolded cg_nested_def, simplified] unfolding y lowered_ok_def by simp
  qed
  have ic: "lowered_ok prog ?rt (E2, ds2) st2 (if_chain armsL) st' (E2, ds2)"
    using if_chain_ok[OF sc2 arms[THEN conjunct2] arms[THEN conjunct1]] .
  have lo: "lowered_ok prog ?rt (E, ds) st S st' (E2, ds2)"
    unfolding S using lowered_ok_append[OF lowered_ok_append[OF lo1 lo2] ic] by simp
  show "\<exists>E' ds'. lowered_ok prog ?rt (E, ds) st S st' (E', ds') \<and> cg_ok prog E' cg' \<and> CG_TyEnv cg' = env' \<and> CG_Ret cg' = CG_Ret cg"
    unfolding cg' env' using lo ok2 by blast
qed

lemma ls_Block:
  assumes IH: "lss_ok prog (cg_nested cg) body"
  shows "ls_ok prog cg (CoreStmt_Block body)"
  unfolding ls_ok_def
proof (intro allI impI)
  fix E ds st S cg' st' env'
  assume l: "lower_stmt cg (CoreStmt_Block body) st = Inr ((S, cg'), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and sf: "stmt_fits (CG_TyEnv cg) (CoreStmt_Block body)"
    and ct: "core_statement_type (CG_TyEnv cg) NotGhost (CoreStmt_Block body) = Some env'"
  let ?env = "CG_TyEnv cg"
  let ?rt = "rk_cty (CG_Ret cg)"
  from ct obtain envb where tb: "core_statement_list_type (?env \<lparr> TE_ProofTopLevel := False \<rparr>) NotGhost body = Some envb"
    and env': "env' = ?env"
    by (auto split: option.splits)
  from l obtain S1 cgb where lb: "lower_stmts (cg_nested cg) body st = Inr ((S1, cgb), st')" and S: "S = [MS_Block S1]" and cg': "cg' = cg"
    by (auto simp: lower_stmt.simps cg_return_def split: prod.splits elim!: cg_bind_InrE)
  obtain E1 ds1 where lo1: "lowered_ok prog (rk_cty (CG_Ret (cg_nested cg))) (E, []) st S1 st' (E1, ds1)"
    by (rule lss_okD[OF IH lb cg_ok_nested[OF ok] scope_ok_inner[OF sc]])
       (use stmt_fits_Block[OF sf] tb in \<open>simp_all add: cg_nested_def stmts_fits_ptl\<close>)
  have "lowered_ok prog ?rt (E, ds) st S st' (E, ds)"
    unfolding S using block_ok[OF sc lo1[unfolded cg_nested_def, simplified]] .
  then show "\<exists>E' ds'. lowered_ok prog ?rt (E, ds) st S st' (E', ds') \<and> cg_ok prog E' cg' \<and> CG_TyEnv cg' = env' \<and> CG_Ret cg' = CG_Ret cg"
    unfolding cg' env' using ok by blast
qed

lemma lss_Nil: "lss_ok prog cg []"
  unfolding lss_ok_def
proof (intro allI impI)
  fix E ds st S cg' st' env'
  assume l: "lower_stmts cg [] st = Inr ((S, cg'), st')" and ok: "cg_ok prog E cg" and sc: "scope_ok prog (E, ds) st"
    and ct: "core_statement_list_type (CG_TyEnv cg) NotGhost [] = Some env'"
  have "S = []" "cg' = cg" "st' = st" using l by (auto simp: lower_stmts.simps cg_return_def)
  then show "\<exists>E' ds'. lowered_ok prog (rk_cty (CG_Ret cg)) (E, ds) st S st' (E', ds') \<and> cg_ok prog E' cg' \<and> CG_TyEnv cg' = env' \<and> CG_Ret cg' = CG_Ret cg"
    using lowered_ok_nil[OF sc] ok ct by auto
qed

lemma lss_Cons:
  assumes IH1: "ls_ok prog cg s"
    and IH2: "\<And>x st st' xa y. lower_stmt cg s st = Inr (x, st') \<Longrightarrow> (xa, y) = x \<Longrightarrow> lss_ok prog y ss"
  shows "lss_ok prog cg (s # ss)"
  unfolding lss_ok_def
proof (intro allI impI)
  fix E ds st S cg' st' env'
  assume l: "lower_stmts cg (s # ss) st = Inr ((S, cg'), st')" and ok: "cg_ok prog E cg"
    and sc: "scope_ok prog (E, ds) st" and sf: "stmts_fits (CG_TyEnv cg) (s # ss)"
    and ct: "core_statement_list_type (CG_TyEnv cg) NotGhost (s # ss) = Some env'"
  let ?rt = "rk_cty (CG_Ret cg)"
  from ct obtain env1 where ct1: "core_statement_type (CG_TyEnv cg) NotGhost s = Some env1"
    and ct2: "core_statement_list_type env1 NotGhost ss = Some env'"
    by (auto split: option.splits)
  note sfs = stmts_fits_Cons[OF sf]
  from l obtain S1 cg1 st1 S2 cg2 where ls: "lower_stmt cg s st = Inr ((S1, cg1), st1)"
    and lss: "lower_stmts cg1 ss st1 = Inr ((S2, cg2), st')" and S: "S = S1 @ S2" and cg': "cg' = cg2"
    by (auto simp: lower_stmts.simps cg_return_def split: prod.splits elim!: cg_bind_InrE)
  obtain E1 ds1 where lo1: "lowered_ok prog ?rt (E, ds) st S1 st1 (E1, ds1)" and ok1: "cg_ok prog E1 cg1"
    and env1: "CG_TyEnv cg1 = env1" and ret1: "CG_Ret cg1 = CG_Ret cg"
    by (rule ls_okD[OF IH1 ls ok sc sfs(1) ct1])
  obtain E2 ds2 where lo2: "lowered_ok prog (rk_cty (CG_Ret cg1)) (E1, ds1) st1 S2 st' (E2, ds2)" and ok2: "cg_ok prog E2 cg2"
    and env2: "CG_TyEnv cg2 = env'" and ret2: "CG_Ret cg2 = CG_Ret cg1"
    by (rule lss_okD[OF IH2[OF ls refl] lss ok1 lowered_ok_scope[OF lo1]]) (use sfs(2)[OF ct1] ct2 in \<open>simp_all add: env1\<close>)
  show "\<exists>E' ds'. lowered_ok prog ?rt (E, ds) st S st' (E', ds') \<and> cg_ok prog E' cg' \<and> CG_TyEnv cg' = env' \<and> CG_Ret cg' = CG_Ret cg"
    unfolding S cg' using lowered_ok_append[OF lo1 lo2[unfolded ret1]] ok2 env2 ret2 ret1 by auto
qed


section \<open>The statement theorem\<close>

theorem lower_stmt_ok_all:
  "ls_ok prog cg s" "lss_ok prog cg ss"
  by (induction rule: lower_stmt_lower_stmts.induct)
     ((rule ls_fail ls_VarDecl_Var ls_VarDecl_Ref ls_VarDeclCall ls_Assign ls_AssignCall ls_Swap ls_Return
            ls_While ls_Match ls_Block lss_Nil lss_Cons; assumption)+)

corollary lower_stmts_ok:
  assumes "lower_stmts cg ss st = Inr ((S, cg'), st')" and "cg_ok prog E cg" and "scope_ok prog (E, ds) st"
    and "stmts_fits (CG_TyEnv cg) ss" and "core_statement_list_type (CG_TyEnv cg) NotGhost ss = Some env'"
  obtains E' ds' where "lowered_ok prog (rk_cty (CG_Ret cg)) (E, ds) st S st' (E', ds')" and "cg_ok prog E' cg'"
    and "CG_TyEnv cg' = env'" and "CG_Ret cg' = CG_Ret cg"
  by (rule lss_okD[OF lower_stmt_ok_all(2) assms])

end
