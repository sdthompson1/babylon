theory EraseGhostTyping
  imports EraseGhost
begin

(* This file proves that well-kinded runtime types remain well-kinded and runtime
   after ghost erasure, and that the ghost erasure of a well-typed term (in
   NotGhost mode) is well-typed, with the same type. *)

(* Erased code is typed in a different environment from the original code:
    - a ghost declaration is deleted, so the erased environment does not have
      the ghost locals of the original one;
    - the ghost functions, the ghost datatypes and the type variables that are
      not runtime are removed from the environment;
    - the functions that stay lose their ghost parameters.

   tyenv_erased env envE relates the two environments. *)


(* ========================================================================== *)
(* The relation between the two environments *)
(* ========================================================================== *)

(* The declarations of envE are those of env that are not ghost, and each
   function has lost its ghost parameters. This part of
   the relation does not look at the local variables. It does not mention
   TE_AbstractTypes either: typing of terms and statements does not read that
   field, and inside a function body it is not simply the erasure of the
   original one (a type parameter may have the name of an abstract type). *)
definition tyenv_decls_erased :: "CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "tyenv_decls_erased env envE =
    (TE_GlobalVars envE = TE_GlobalVars env
     \<and> TE_TypeVars envE = TE_TypeVars env |\<inter>| TE_RuntimeTypeVars env
     \<and> TE_RuntimeTypeVars envE = TE_RuntimeTypeVars env
     \<and> TE_Functions envE
         = fmmap erase_ghost_funinfo (fmfilter (tyenv_nonghost_fun env) (TE_Functions env))
     \<and> TE_Datatypes envE
         = fmfilter (\<lambda>dtName. dtName |\<notin>| TE_GhostDatatypes env) (TE_Datatypes env)
     \<and> TE_DataCtors envE = fmfilter (tyenv_nonghost_ctor env) (TE_DataCtors env)
     \<and> TE_DataCtorsByType envE
         = fmfilter (\<lambda>dtName. dtName |\<notin>| TE_GhostDatatypes env) (TE_DataCtorsByType env)
     \<and> TE_GhostDatatypes envE = {||})"

(* tyenv_erased env envE:
    - the declarations of envE are those of env that are not ghost;
    - the two agree on the return type and on the ghost-ness of the function;
    - envE has no ghost local;
    - a name that is not a ghost local of env means the same in both: the same
      local (or no local), and const in one exactly when const in the other.
   Nothing is said about a name that is a ghost local of env. In envE it may
   be unbound, or bound to whatever the ghost declaration shadowed. *)
definition tyenv_erased :: "CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "tyenv_erased env envE =
    (tyenv_decls_erased env envE
     \<and> TE_ReturnType envE = TE_ReturnType env
     \<and> TE_FunctionGhost envE = TE_FunctionGhost env
     \<and> TE_FunctionImpure envE = TE_FunctionImpure env
     \<and> TE_GhostLocals envE = {||}
     \<and> (\<forall>name. \<not> tyenv_var_ghost env name \<longrightarrow>
           fmlookup (TE_LocalVars envE) name = fmlookup (TE_LocalVars env) name
           \<and> (name |\<in>| TE_ConstLocals envE \<longleftrightarrow> name |\<in>| TE_ConstLocals env)))"

(* tyenv_decls_erased reads only the declaration fields. *)
lemma tyenv_decls_erased_cong:
  assumes "TE_GlobalVars env1 = TE_GlobalVars env2"
    and "TE_TypeVars env1 = TE_TypeVars env2"
    and "TE_RuntimeTypeVars env1 = TE_RuntimeTypeVars env2"
    and "TE_Functions env1 = TE_Functions env2"
    and "TE_Datatypes env1 = TE_Datatypes env2"
    and "TE_DataCtors env1 = TE_DataCtors env2"
    and "TE_DataCtorsByType env1 = TE_DataCtorsByType env2"
    and "TE_GhostDatatypes env1 = TE_GhostDatatypes env2"
    and "TE_GlobalVars envE1 = TE_GlobalVars envE2"
    and "TE_TypeVars envE1 = TE_TypeVars envE2"
    and "TE_RuntimeTypeVars envE1 = TE_RuntimeTypeVars envE2"
    and "TE_Functions envE1 = TE_Functions envE2"
    and "TE_Datatypes envE1 = TE_Datatypes envE2"
    and "TE_DataCtors envE1 = TE_DataCtors envE2"
    and "TE_DataCtorsByType envE1 = TE_DataCtorsByType envE2"
    and "TE_GhostDatatypes envE1 = TE_GhostDatatypes envE2"
  shows "tyenv_decls_erased env1 envE1 = tyenv_decls_erased env2 envE2"
proof -
  have f: "tyenv_nonghost_fun env1 = tyenv_nonghost_fun env2"
    by (rule ext) (simp add: tyenv_nonghost_fun_def assms)
  have c: "tyenv_nonghost_ctor env1 = tyenv_nonghost_ctor env2"
    by (rule ext) (simp add: tyenv_nonghost_ctor_def assms split: option.splits prod.splits)
  show ?thesis
    unfolding tyenv_decls_erased_def f c assms by (rule refl)
qed

(* The erased environment is related to the original one, when the original
   has no ghost local. *)
lemma tyenv_erased_erase_ghost_tyenv:
  assumes "TE_GhostLocals env = {||}"
  shows "tyenv_erased env (erase_ghost_tyenv env)"
  using assms unfolding tyenv_erased_def tyenv_decls_erased_def by simp

(* What the relation gives. *)

lemma tyenv_erased_decls:
  "tyenv_erased env envE \<Longrightarrow> tyenv_decls_erased env envE"
  unfolding tyenv_erased_def by blast

lemma tyenv_erased_fun_lookup:
  assumes "tyenv_erased env envE"
    and "fmlookup (TE_Functions env) fnName = Some info"
    and "FI_Ghost info = NotGhost"
  shows "fmlookup (TE_Functions envE) fnName = Some (erase_ghost_funinfo info)"
  using assms
  unfolding tyenv_erased_def tyenv_decls_erased_def
  by (simp add: tyenv_nonghost_fun_def)

lemma tyenv_erased_ctor_lookup:
  assumes "tyenv_erased env envE"
    and "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload)"
    and "dtName |\<notin>| TE_GhostDatatypes env"
  shows "fmlookup (TE_DataCtors envE) ctorName = Some (dtName, tyVars, payload)"
  using assms
  unfolding tyenv_erased_def tyenv_decls_erased_def
  by (simp add: tyenv_nonghost_ctor_def)

lemma tyenv_erased_no_ghost_datatype:
  "tyenv_erased env envE \<Longrightarrow> dtName |\<notin>| TE_GhostDatatypes envE"
  unfolding tyenv_erased_def tyenv_decls_erased_def by simp

lemma tyenv_erased_not_ghost:
  "tyenv_erased env envE \<Longrightarrow> \<not> tyenv_var_ghost envE name"
  unfolding tyenv_erased_def tyenv_var_ghost_def by simp

lemma tyenv_erased_local_lookup:
  assumes "tyenv_erased env envE" and "\<not> tyenv_var_ghost env name"
  shows "fmlookup (TE_LocalVars envE) name = fmlookup (TE_LocalVars env) name"
  using assms unfolding tyenv_erased_def by blast

lemma tyenv_erased_const_local:
  assumes "tyenv_erased env envE" and "\<not> tyenv_var_ghost env name"
  shows "name |\<in>| TE_ConstLocals envE \<longleftrightarrow> name |\<in>| TE_ConstLocals env"
  using assms unfolding tyenv_erased_def by blast

lemma tyenv_erased_lookup_var:
  assumes rel: "tyenv_erased env envE" and ng: "\<not> tyenv_var_ghost env name"
  shows "tyenv_lookup_var envE name = tyenv_lookup_var env name"
proof -
  have g: "TE_GlobalVars envE = TE_GlobalVars env"
    using rel unfolding tyenv_erased_def tyenv_decls_erased_def by blast
  show ?thesis
    unfolding tyenv_lookup_var_def tyenv_erased_local_lookup[OF rel ng] g by (rule refl)
qed

(* Binding a new local that is not ghost, on both sides. The const-ness of the
   new name is the same on both sides: constE holds exactly when const does. *)
lemma tyenv_erased_add_var:
  assumes rel: "tyenv_erased env envE"
    and c: "varName |\<in>| cs \<longleftrightarrow> varName |\<in>| csE"
    and others: "\<And>name. name \<noteq> varName \<Longrightarrow>
                   (name |\<in>| cs \<longleftrightarrow> name |\<in>| TE_ConstLocals env)
                   \<and> (name |\<in>| csE \<longleftrightarrow> name |\<in>| TE_ConstLocals envE)"
  shows "tyenv_erased
           (env \<lparr> TE_LocalVars := fmupd varName ty (TE_LocalVars env),
                  TE_GhostLocals := TE_GhostLocals env |-| {|varName|},
                  TE_ConstLocals := cs \<rparr>)
           (envE \<lparr> TE_LocalVars := fmupd varName ty (TE_LocalVars envE),
                   TE_GhostLocals := TE_GhostLocals envE |-| {|varName|},
                   TE_ConstLocals := csE \<rparr>)"
    (is "tyenv_erased ?env' ?envE'")
proof -
  have d: "tyenv_decls_erased ?env' ?envE' = tyenv_decls_erased env envE"
    by (rule tyenv_decls_erased_cong) simp_all
  have decls: "tyenv_decls_erased ?env' ?envE'"
    unfolding d by (rule tyenv_erased_decls[OF rel])
  have ret: "TE_ReturnType ?envE' = TE_ReturnType ?env'"
    and fg: "TE_FunctionGhost ?envE' = TE_FunctionGhost ?env'"
    and fi: "TE_FunctionImpure ?envE' = TE_FunctionImpure ?env'"
    and gl: "TE_GhostLocals ?envE' = {||}"
    using rel unfolding tyenv_erased_def by simp_all
  have locals: "fmlookup (TE_LocalVars ?envE') name = fmlookup (TE_LocalVars ?env') name
                \<and> (name |\<in>| TE_ConstLocals ?envE' \<longleftrightarrow> name |\<in>| TE_ConstLocals ?env')"
    if ng: "\<not> tyenv_var_ghost ?env' name" for name
  proof (cases "name = varName")
    case True
    then show ?thesis using c by simp
  next
    case False
    have ng0: "\<not> tyenv_var_ghost env name"
      using ng False unfolding tyenv_var_ghost_def by simp
    show ?thesis
      using False others[OF False]
            tyenv_erased_local_lookup[OF rel ng0] tyenv_erased_const_local[OF rel ng0]
      by simp
  qed
  show ?thesis
    unfolding tyenv_erased_def using decls ret fg fi gl locals by blast
qed

(* The same, for a const local (the binding of a Let). *)
lemma tyenv_erased_add_const_var:
  assumes rel: "tyenv_erased env envE"
  shows "tyenv_erased
           (env \<lparr> TE_LocalVars := fmupd varName ty (TE_LocalVars env),
                  TE_GhostLocals := TE_GhostLocals env |-| {|varName|},
                  TE_ConstLocals := finsert varName (TE_ConstLocals env) \<rparr>)
           (envE \<lparr> TE_LocalVars := fmupd varName ty (TE_LocalVars envE),
                   TE_GhostLocals := TE_GhostLocals envE |-| {|varName|},
                   TE_ConstLocals := finsert varName (TE_ConstLocals envE) \<rparr>)"
  by (rule tyenv_erased_add_var[OF rel]) simp_all


(* ========================================================================== *)
(* Types: well-kinded runtime types remain well-kinded and runtime in
   the erased environment. *)
(* ========================================================================== *)

(* A runtime type of env mentions no ghost datatype and no type variable that
   is not runtime, so it is still well-kinded, and still a runtime type, in
   envE. *)
lemma tyenv_erased_runtime_type:
  assumes rel: "tyenv_erased env envE"
  shows "is_well_kinded env ty \<Longrightarrow> is_runtime_type env ty
           \<Longrightarrow> is_well_kinded envE ty \<and> is_runtime_type envE ty"
proof (induction ty)
  case (CoreTy_Datatype nm args)
  from CoreTy_Datatype.prems(1) obtain n where
      lk: "fmlookup (TE_Datatypes env) nm = Some n" and
      len: "length args = n" and
      wks: "list_all (is_well_kinded env) args"
    by (auto split: option.splits)
  from CoreTy_Datatype.prems(2) have
      ng: "nm |\<notin>| TE_GhostDatatypes env" and
      rts: "list_all (is_runtime_type env) args"
    by simp_all
  have lkE: "fmlookup (TE_Datatypes envE) nm = Some n"
    using rel lk ng unfolding tyenv_erased_def tyenv_decls_erased_def by simp
  have each: "is_well_kinded envE a \<and> is_runtime_type envE a" if a_in: "a \<in> set args" for a
  proof -
    have wk: "is_well_kinded env a" using wks a_in by (simp add: list_all_iff)
    have rt: "is_runtime_type env a" using rts a_in by (simp add: list_all_iff)
    show ?thesis by (rule CoreTy_Datatype.IH[OF a_in wk rt])
  qed
  show ?case
    using lkE len each tyenv_erased_no_ghost_datatype[OF rel]
    by (simp add: list_all_iff)
next
  case (CoreTy_Record flds)
  have each: "is_well_kinded envE fty \<and> is_runtime_type envE fty"
    if f_in: "(nm, fty) \<in> set flds" for nm fty
  proof -
    have sn: "fty \<in> Basic_BNFs.snds (nm, fty)" by simp
    have wk: "is_well_kinded env fty"
      using CoreTy_Record.prems(1) f_in by (force simp: list_all_iff)
    have rt: "is_runtime_type env fty"
      using CoreTy_Record.prems(2) f_in by (force simp: list_all_iff)
    show ?thesis by (rule CoreTy_Record.IH[OF f_in sn wk rt])
  qed
  show ?case
    using CoreTy_Record.prems(1) each by (auto simp: list_all_iff)
next
  case (CoreTy_Array elemTy dims)
  then show ?case by simp
next
  case (CoreTy_Var n)
  then show ?case
    using rel unfolding tyenv_erased_def tyenv_decls_erased_def by simp
qed simp_all

(* The same, for a list of types. *)
lemma tyenv_erased_runtime_type_list:
  assumes rel: "tyenv_erased env envE"
  shows "list_all (is_well_kinded env) tys \<Longrightarrow> list_all (is_runtime_type env) tys
           \<Longrightarrow> list_all (is_well_kinded envE) tys \<and> list_all (is_runtime_type envE) tys"
proof (induction tys)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  from Cons.prems have
      a: "is_well_kinded env t" and b: "is_runtime_type env t" and
      c: "list_all (is_well_kinded env) ts" and d: "list_all (is_runtime_type env) ts"
    by simp_all
  from tyenv_erased_runtime_type[OF rel a b] Cons.IH[OF c d] show ?case by simp
qed


(* ========================================================================== *)
(* Patterns *)
(* ========================================================================== *)

(* A pattern that is compatible with a runtime type names only constructors of
   datatypes that are not ghost, and those are in envE. *)
lemma pattern_compatible_erased:
  assumes rel: "tyenv_erased env envE" and wf: "tyenv_well_formed env"
  shows "pattern_compatible env p ty \<Longrightarrow> is_runtime_type env ty
           \<Longrightarrow> pattern_compatible envE p ty"
proof (induction p arbitrary: ty)
  case (CorePat_Variant ctorName payloadPat)
  from CorePat_Variant.prems(1) obtain dtName tyvars payloadTy tyArgs where
      lk: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payloadTy)" and
      ty: "ty = CoreTy_Datatype dtName tyArgs" and
      len: "length tyArgs = length tyvars" and
      pc: "pattern_compatible env payloadPat
             (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
    by (auto split: option.splits prod.splits CoreType.splits)
  from CorePat_Variant.prems(2) ty have
      ng: "dtName |\<notin>| TE_GhostDatatypes env" and
      rts: "list_all (is_runtime_type env) tyArgs"
    by simp_all
  have "tyenv_nonghost_payloads_runtime env"
    using wf unfolding tyenv_well_formed_def by blast
  hence payload_rt:
    "is_runtime_type
       (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyvars,
              TE_RuntimeTypeVars := (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                     |\<union>| fset_of_list tyvars \<rparr>) payloadTy"
    using lk ng unfolding tyenv_nonghost_payloads_runtime_def by blast
  have rt': "is_runtime_type env (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
    by (rule apply_subst_specializes_runtime[OF payload_rt rts len[symmetric]])
  have pcE: "pattern_compatible envE payloadPat
               (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
    by (rule CorePat_Variant.IH[OF pc rt'])
  have lkE: "fmlookup (TE_DataCtors envE) ctorName = Some (dtName, tyvars, payloadTy)"
    by (rule tyenv_erased_ctor_lookup[OF rel lk ng])
  show ?case using lkE ty len pcE by simp
next
  case (CorePat_Record pflds)
  let ?P = "\<lambda>e. (\<lambda>(pn, p) (fn, fty). pn = fn \<and> pattern_compatible e p fty)"
  from CorePat_Record.prems(1) obtain fldTys where
      ty: "ty = CoreTy_Record fldTys" and
      la: "list_all2 (?P env) pflds fldTys"
    by (auto split: CoreType.splits)
  from CorePat_Record.prems(2) ty have
      rts: "list_all (is_runtime_type env) (map snd fldTys)"
    by simp
  have len: "length pflds = length fldTys" using la by (rule list_all2_lengthD)
  have laE: "list_all2 (?P envE) pflds fldTys"
  proof (rule list_all2_all_nthI)
    show "length pflds = length fldTys" by (rule len)
  next
    fix i assume i: "i < length pflds"
    obtain pn p where pf: "pflds ! i = (pn, p)" by (cases "pflds ! i")
    obtain fn fty where ff: "fldTys ! i = (fn, fty)" by (cases "fldTys ! i")
    from la i have "?P env (pflds ! i) (fldTys ! i)" by (rule list_all2_nthD)
    hence nm: "pn = fn" and pc: "pattern_compatible env p fty"
      using pf ff by simp_all
    have in_p: "(pn, p) \<in> set pflds" using i pf by (metis nth_mem)
    have "fldTys ! i \<in> set fldTys" using i len by simp
    hence rt: "is_runtime_type env fty" using rts ff by (force simp: list_all_iff)
    have sn: "p \<in> Basic_BNFs.snds (pn, p)" by simp
    have "pattern_compatible envE p fty"
      by (rule CorePat_Record.IH[OF in_p sn pc rt])
    thus "?P envE (pflds ! i) (fldTys ! i)" using pf ff nm by simp
  qed
  show ?case using ty laE by simp
qed simp_all


(* ========================================================================== *)
(* Lvalues: erasure keeps the shape of an lvalue, so the lvalue checks give the
   same answer for a term and for its erasure. *)
(* ========================================================================== *)

lemma is_writable_lvalue_erase_ghost_term [simp]:
  "is_writable_lvalue env (erase_ghost_term funs tm) = is_writable_lvalue env tm"
  by (induction tm) simp_all

lemma ghost_lvalue_ok_erase_ghost_term [simp]:
  "ghost_lvalue_ok env ghost (erase_ghost_term funs tm) = ghost_lvalue_ok env ghost tm"
  by (simp add: ghost_lvalue_ok_def)


(* ========================================================================== *)
(* Terms: the ghost-erasure of a term typed in NotGhost mode is well-typed,
   with the same NotGhost type. *)
(* ========================================================================== *)

lemma those_Some_all_Some:
  "those xs = Some ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<exists>y. x = Some y"
  by (induction xs arbitrary: ys) (auto split: option.splits)

(* The per-argument check of a call, written as a relation between the actuals
   and the parameter list. *)
lemma args_typed_params_conv:
  "list_all2 (\<lambda>tm (expectedTy, mode). tc mode tm = Some expectedTy) tms
     (zip (map (\<lambda>(ty, _). f ty) params) (map (\<lambda>(_, _, gh). m gh) params))
     \<longleftrightarrow> list_all2 (\<lambda>tm (pty, vor, gh). tc (m gh) tm = Some (f pty)) tms params"
proof -
  have z: "zip (map (\<lambda>(ty, _). f ty) params) (map (\<lambda>(_, _, gh). m gh) params)
             = map (\<lambda>(pty, vor, gh). (f pty, m gh)) params"
    by (induction params) auto
  show ?thesis
    unfolding z list.rel_map
    by (simp add: case_prod_unfold)
qed

(* The actuals of an executable call, after erasure: the actuals of the ghost
   parameters are dropped, and the others are typed in NotGhost mode against
   the parameters that are not ghost. tc and tcE are the typing functions of
   the two environments, and e is the erasure of a term. *)
lemma args_typed_erased_aux:
  assumes typed: "list_all2 (\<lambda>tm (pty, vor, gh). tc (param_mode NotGhost gh) tm = Some (f pty))
                    tms params"
    and sub: "\<And>tm ty. tm \<in> set tms \<Longrightarrow> tc NotGhost tm = Some ty
                \<Longrightarrow> tcE NotGhost (e tm) = Some ty"
  shows "list_all2 (\<lambda>tm (pty, vor, gh). tcE (param_mode NotGhost gh) tm = Some (f pty))
           (drop_ghost (map (\<lambda>(_, _, gh). gh) params) (map e tms))
           (filter (\<lambda>(_, _, gh). gh = NotGhost) params)"
  using assms
proof (induction tms params rule: list_all2_induct)
  case Nil
  show ?case by simp
next
  case (Cons tm tms p params)
  obtain pty vor gh where p: "p = (pty, vor, gh)" by (cases p)
  have tl: "list_all2 (\<lambda>tm (pty, vor, gh). tcE (param_mode NotGhost gh) tm = Some (f pty))
              (drop_ghost (map (\<lambda>(_, _, gh). gh) params) (map e tms))
              (filter (\<lambda>(_, _, gh). gh = NotGhost) params)"
  proof (rule Cons.IH)
    fix tm' ty' assume "tm' \<in> set tms" and "tc NotGhost tm' = Some ty'"
    then show "tcE NotGhost (e tm') = Some ty'"
      by (intro Cons.prems) simp_all
  qed
  show ?case
  proof (cases gh)
    case NotGhost
    have "tc NotGhost tm = Some (f pty)"
      using Cons.hyps(1) p NotGhost by simp
    then have "tcE NotGhost (e tm) = Some (f pty)"
      by (intro Cons.prems) simp_all
    with tl show ?thesis by (simp add: p NotGhost)
  next
    case Ghost
    with tl show ?thesis by (simp add: p)
  qed
qed

(* A term typed in NotGhost mode in env: its ghost-erasure has the same type,
   in NotGhost mode, in envE. *)
theorem core_term_type_erased:
  "core_term_type env NotGhost tm = Some ty \<Longrightarrow> tyenv_well_formed env
     \<Longrightarrow> tyenv_erased env envE
     \<Longrightarrow> core_term_type envE NotGhost (erase_ghost_term (TE_Functions env) tm) = Some ty"
proof (induction tm arbitrary: env envE ty)
  case (CoreTm_LitBool b)
  then show ?case by simp
next
  case (CoreTm_LitInt i)
  then show ?case by simp
next
  case (CoreTm_LitArray elemTy tms)
  note wf = CoreTm_LitArray.prems(2) and rel = CoreTm_LitArray.prems(3)
  let ?E = "erase_ghost_term (TE_Functions env)"
  from CoreTm_LitArray.prems(1) have
      wk: "is_well_kinded env elemTy" and
      rt: "is_runtime_type env elemTy" and
      all: "list_all (\<lambda>tm. core_term_type env NotGhost tm = Some elemTy) tms" and
      len: "int_in_range (int_range Unsigned IntBits_64) (int (length tms))" and
      ty_eq: "ty = CoreTy_Array elemTy [CoreDim_Fixed (int (length tms))]"
    by (auto split: if_splits)
  note t = tyenv_erased_runtime_type[OF rel wk rt]
  have allE: "list_all (\<lambda>tm. core_term_type envE NotGhost tm = Some elemTy) (map ?E tms)"
    unfolding list_all_iff
  proof
    fix tmE assume "tmE \<in> set (map ?E tms)"
    then obtain tm where tin: "tm \<in> set tms" and tmE: "tmE = ?E tm" by auto
    have "core_term_type env NotGhost tm = Some elemTy"
      using all tin by (simp add: list_all_iff)
    hence "core_term_type envE NotGhost (?E tm) = Some elemTy"
      by (rule CoreTm_LitArray.IH[OF tin _ wf rel])
    thus "core_term_type envE NotGhost tmE = Some elemTy" unfolding tmE .
  qed
  have "core_term_type envE NotGhost (CoreTm_LitArray elemTy (map ?E tms)) = Some ty"
    using t allE len ty_eq by simp
  then show ?case by simp
next
  case (CoreTm_Var name)
  note rel = CoreTm_Var.prems(3)
  from CoreTm_Var.prems(1) have
      lk: "tyenv_lookup_var env name = Some ty" and
      ng: "\<not> tyenv_var_ghost env name"
    by (auto split: option.splits if_splits)
  show ?case
    using tyenv_erased_lookup_var[OF rel ng] tyenv_erased_not_ghost[OF rel, of name] lk
    by simp
next
  case (CoreTm_Cast targetTy operand)
  note wf = CoreTm_Cast.prems(2) and rel = CoreTm_Cast.prems(3)
  from CoreTm_Cast.prems(1) obtain operandTy where
      op: "core_term_type env NotGhost operand = Some operandTy" and
      co: "cast_ok env operandTy targetTy" and
      rt: "is_runtime_type env targetTy" and
      ty_eq: "ty = targetTy"
    by (auto split: option.splits if_splits)
  have wk: "is_well_kinded env targetTy" by (rule cast_ok_well_kinded[OF co])
  note t = tyenv_erased_runtime_type[OF rel wk rt]
  have coE: "cast_ok envE operandTy targetTy"
    using co t unfolding cast_ok_def by blast
  have opE: "core_term_type envE NotGhost (erase_ghost_term (TE_Functions env) operand)
               = Some operandTy"
    by (rule CoreTm_Cast.IH[OF op wf rel])
  show ?case using opE coE t ty_eq by simp
next
  case (CoreTm_Unop op operand)
  note wf = CoreTm_Unop.prems(2) and rel = CoreTm_Unop.prems(3)
  from CoreTm_Unop.prems(1) obtain operandTy where
      opd: "core_term_type env NotGhost operand = Some operandTy"
    by (auto split: option.splits)
  have opdE: "core_term_type envE NotGhost (erase_ghost_term (TE_Functions env) operand)
                = Some operandTy"
    by (rule CoreTm_Unop.IH[OF opd wf rel])
  show ?case using CoreTm_Unop.prems(1) opd opdE by simp
next
  case (CoreTm_Binop op lhs rhs)
  note wf = CoreTm_Binop.prems(2) and rel = CoreTm_Binop.prems(3)
  from CoreTm_Binop.prems(1) obtain lhsTy rhsTy where
      l: "core_term_type env NotGhost lhs = Some lhsTy" and
      r: "core_term_type env NotGhost rhs = Some rhsTy"
    by (auto split: option.splits prod.splits)
  have lE: "core_term_type envE NotGhost (erase_ghost_term (TE_Functions env) lhs)
              = Some lhsTy"
    by (rule CoreTm_Binop.IH(1)[OF l wf rel])
  have rE: "core_term_type envE NotGhost (erase_ghost_term (TE_Functions env) rhs)
              = Some rhsTy"
    by (rule CoreTm_Binop.IH(2)[OF r wf rel])
  show ?case using CoreTm_Binop.prems(1) l r lE rE by simp
next
  case (CoreTm_Let var rhs body)
  note wf = CoreTm_Let.prems(2) and rel = CoreTm_Let.prems(3)
  from CoreTm_Let.prems(1) obtain rhsTy where
      r: "core_term_type env NotGhost rhs = Some rhsTy" and
      b: "core_term_type
            (env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                   TE_GhostLocals := TE_GhostLocals env |-| {|var|},
                   TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>)
            NotGhost body = Some ty"
    by (auto simp: Let_def split: option.splits)
  have rk: "is_well_kinded env rhsTy" by (rule core_term_type_well_kinded[OF r wf])
  have rr: "is_runtime_type env rhsTy" by (rule core_term_type_notghost_runtime[OF r wf])
  have wf0: "tyenv_well_formed
               (env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                      TE_GhostLocals := TE_GhostLocals env |-| {|var|} \<rparr>)"
    by (rule tyenv_well_formed_add_var[OF wf rk rr])
  have wf': "tyenv_well_formed
               (env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                      TE_GhostLocals := TE_GhostLocals env |-| {|var|},
                      TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>)"
    using tyenv_well_formed_TE_ConstLocals_irrelevant[
            OF wf0, where c = "finsert var (TE_ConstLocals env)"]
    by simp
  have rE: "core_term_type envE NotGhost (erase_ghost_term (TE_Functions env) rhs)
              = Some rhsTy"
    by (rule CoreTm_Let.IH(1)[OF r wf rel])
  \<comment> \<open>The body is typed in an environment with one more local; its function
      table is the same.\<close>
  have bE: "core_term_type
              (envE \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars envE),
                      TE_GhostLocals := TE_GhostLocals envE |-| {|var|},
                      TE_ConstLocals := finsert var (TE_ConstLocals envE) \<rparr>)
              NotGhost (erase_ghost_term (TE_Functions env) body) = Some ty"
    using CoreTm_Let.IH(2)[OF b wf' tyenv_erased_add_const_var[OF rel]] by simp
  show ?case using rE bE by (simp add: Let_def)
next
  case (CoreTm_Quantifier quant var varTy body)
  then show ?case by simp
next
  case (CoreTm_FunctionCall fnName tyArgs tmArgs)
  note wf = CoreTm_FunctionCall.prems(2) and rel = CoreTm_FunctionCall.prems(3)
  from CoreTm_FunctionCall.prems(1) obtain funInfo where
      fn: "fmlookup (TE_Functions env) fnName = Some funInfo"
    by (auto split: option.splits)
  let ?E = "erase_ghost_term (TE_Functions env)"
  let ?sub = "fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)"
  let ?infoE = "erase_ghost_funinfo funInfo"
  let ?argsE = "drop_ghost (param_ghost_flags funInfo) (map ?E tmArgs)"
  from CoreTm_FunctionCall.prems(1) fn have
      len_ty: "length tyArgs = length (FI_TyArgs funInfo)" and
      wks: "list_all (is_well_kinded env) tyArgs" and
      cps: "list_all is_complete_type tyArgs" and
      rts: "list_all (is_runtime_type env) tyArgs" and
      ng: "FI_Ghost funInfo \<noteq> Ghost" and
      vars: "list_all (\<lambda>(_, vor, _). vor = Var) (FI_TmArgs funInfo)" and
      pure: "\<not> FI_Impure funInfo" and
      len_tm: "length tmArgs = length (FI_TmArgs funInfo)" and
      args: "list_all2 (\<lambda>tm (expectedTy, mode). core_term_type env mode tm = Some expectedTy) tmArgs
               (zip (map (\<lambda>(ty, _). apply_subst ?sub ty) (FI_TmArgs funInfo))
                    (map (\<lambda>(_, _, gh). param_mode NotGhost gh) (FI_TmArgs funInfo)))" and
      ty_eq: "ty = apply_subst ?sub (FI_ReturnType funInfo)"
    by (auto simp: Let_def split: if_splits)
  have ngN: "FI_Ghost funInfo = NotGhost"
    using ng by (cases "FI_Ghost funInfo") simp_all
  have fnE: "fmlookup (TE_Functions envE) fnName = Some ?infoE"
    by (rule tyenv_erased_fun_lookup[OF rel fn ngN])
  note tysE = tyenv_erased_runtime_type_list[OF rel wks rts]
  \<comment> \<open>The actuals, as a relation with the parameter list.\<close>
  have args0: "list_all2 (\<lambda>tm (pty, vor, gh).
                   core_term_type env (param_mode NotGhost gh) tm = Some (apply_subst ?sub pty))
                 tmArgs (FI_TmArgs funInfo)"
    using args
    unfolding args_typed_params_conv[where f = "apply_subst ?sub" and m = "param_mode NotGhost"] .
  \<comment> \<open>The actuals that are kept, against the parameters that are kept.\<close>
  have argsE0: "list_all2 (\<lambda>tm (pty, vor, gh).
                    core_term_type envE (param_mode NotGhost gh) tm = Some (apply_subst ?sub pty))
                  ?argsE (FI_TmArgs ?infoE)"
    unfolding param_ghost_flags_def erase_ghost_funinfo_simps
  proof (rule args_typed_erased_aux[where tcE = "core_term_type envE" and e = "?E", OF args0])
    fix tm ty0
    assume tin: "tm \<in> set tmArgs" and t: "core_term_type env NotGhost tm = Some ty0"
    show "core_term_type envE NotGhost (?E tm) = Some ty0"
      by (rule CoreTm_FunctionCall.IH[OF tin t wf rel])
  qed
  have argsE: "list_all2 (\<lambda>tm (expectedTy, mode).
                   core_term_type envE mode tm = Some expectedTy) ?argsE
                 (zip (map (\<lambda>(ty, _). apply_subst ?sub ty) (FI_TmArgs ?infoE))
                      (map (\<lambda>(_, _, gh). param_mode NotGhost gh) (FI_TmArgs ?infoE)))"
    using argsE0
    unfolding args_typed_params_conv[where f = "apply_subst ?sub" and m = "param_mode NotGhost"] .
  have lenE: "length ?argsE = length (FI_TmArgs ?infoE)"
    using argsE0 by (rule list_all2_lengthD)
  have varsE: "list_all (\<lambda>(_, vor, _). vor = Var) (FI_TmArgs ?infoE)"
    using vars by (auto simp: list_all_iff)
  have callE: "core_term_type envE NotGhost (CoreTm_FunctionCall fnName tyArgs ?argsE) = Some ty"
    using fnE len_ty tysE cps ngN varsE pure lenE argsE ty_eq
    by (simp add: Let_def)
  have eq: "?E (CoreTm_FunctionCall fnName tyArgs tmArgs)
              = CoreTm_FunctionCall fnName tyArgs ?argsE"
    by (simp add: erase_ghost_args_def fn)
  show ?case unfolding eq by (rule callE)
next
  case (CoreTm_VariantCtor ctorName tyArgs payload)
  note wf = CoreTm_VariantCtor.prems(2) and rel = CoreTm_VariantCtor.prems(3)
  from CoreTm_VariantCtor.prems(1) obtain dtName tyvars payloadTy where
      lk: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payloadTy)"
    by (auto split: option.splits prod.splits)
  from CoreTm_VariantCtor.prems(1) lk have
      len: "length tyArgs = length tyvars" and
      wks: "list_all (is_well_kinded env) tyArgs" and
      cps: "list_all is_complete_type tyArgs" and
      rts: "list_all (is_runtime_type env) tyArgs" and
      ng: "dtName |\<notin>| TE_GhostDatatypes env" and
      p: "core_term_type env NotGhost payload
            = Some (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)" and
      ty_eq: "ty = CoreTy_Datatype dtName tyArgs"
    by (auto simp: Let_def split: option.splits if_splits)
  have lkE: "fmlookup (TE_DataCtors envE) ctorName = Some (dtName, tyvars, payloadTy)"
    by (rule tyenv_erased_ctor_lookup[OF rel lk ng])
  note tysE = tyenv_erased_runtime_type_list[OF rel wks rts]
  have pE: "core_term_type envE NotGhost (erase_ghost_term (TE_Functions env) payload)
              = Some (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
    by (rule CoreTm_VariantCtor.IH[OF p wf rel])
  show ?case
    using lkE len tysE cps tyenv_erased_no_ghost_datatype[OF rel, of dtName] pE ty_eq
    by (simp add: Let_def)
next
  case (CoreTm_Record flds)
  note wf = CoreTm_Record.prems(2) and rel = CoreTm_Record.prems(3)
  from CoreTm_Record.prems(1) obtain tys where
      d: "distinct (map fst flds)" and
      th: "those (map (\<lambda>(name, tm). core_term_type env NotGhost tm) flds) = Some tys" and
      ty_eq: "ty = CoreTy_Record (zip (map fst flds) tys)"
    by (auto split: option.splits if_splits)
  let ?E = "erase_ghost_term (TE_Functions env)"
  let ?fldsE = "map (\<lambda>(name, tm). (name, ?E tm)) flds"
  have fstE: "map fst ?fldsE = map fst flds"
    by (induction flds) auto
  have compE: "map (\<lambda>(name, tm). core_term_type envE NotGhost tm) ?fldsE
                 = map (\<lambda>(name, tm). core_term_type envE NotGhost (?E tm)) flds"
    by (induction flds) auto
  have map_eq: "map (\<lambda>(name, tm). core_term_type envE NotGhost (?E tm)) flds
                  = map (\<lambda>(name, tm). core_term_type env NotGhost tm) flds"
  proof (rule map_cong[OF refl])
    fix x assume xin: "x \<in> set flds"
    obtain nm tm where x: "x = (nm, tm)" by (cases x)
    have "core_term_type env NotGhost tm
            \<in> set (map (\<lambda>(name, tm). core_term_type env NotGhost tm) flds)"
      using xin x by force
    then obtain t where t: "core_term_type env NotGhost tm = Some t"
      using those_Some_all_Some[OF th] by blast
    have fin: "(nm, tm) \<in> set flds" using xin x by simp
    have sn: "tm \<in> Basic_BNFs.snds (nm, tm)" by simp
    have "core_term_type envE NotGhost (?E tm) = Some t"
      by (rule CoreTm_Record.IH[OF fin sn t wf rel])
    thus "(case x of (name, tm) \<Rightarrow> core_term_type envE NotGhost (?E tm))
            = (case x of (name, tm) \<Rightarrow> core_term_type env NotGhost tm)"
      using t x by simp
  qed
  have dE: "distinct (map fst ?fldsE)" unfolding fstE by (rule d)
  have thE: "those (map (\<lambda>(name, tm). core_term_type envE NotGhost tm) ?fldsE) = Some tys"
    unfolding compE map_eq by (rule th)
  have recE: "core_term_type envE NotGhost (CoreTm_Record ?fldsE)
                = Some (CoreTy_Record (zip (map fst ?fldsE) tys))"
    using dE thE by simp
  have eq: "?E (CoreTm_Record flds) = CoreTm_Record ?fldsE" by simp
  show ?case unfolding eq ty_eq using recE unfolding fstE .
next
  case (CoreTm_RecordProj tm fldName)
  note wf = CoreTm_RecordProj.prems(2) and rel = CoreTm_RecordProj.prems(3)
  from CoreTm_RecordProj.prems(1) obtain fieldTypes where
      t: "core_term_type env NotGhost tm = Some (CoreTy_Record fieldTypes)" and
      f: "map_of fieldTypes fldName = Some ty"
    by (auto split: option.splits CoreType.splits)
  have tE: "core_term_type envE NotGhost (erase_ghost_term (TE_Functions env) tm)
              = Some (CoreTy_Record fieldTypes)"
    by (rule CoreTm_RecordProj.IH[OF t wf rel])
  show ?case using tE f by simp
next
  case (CoreTm_ArrayProj arr idxTms)
  note wf = CoreTm_ArrayProj.prems(2) and rel = CoreTm_ArrayProj.prems(3)
  from CoreTm_ArrayProj.prems(1) obtain elemTy dims where
      a: "core_term_type env NotGhost arr = Some (CoreTy_Array elemTy dims)"
    by (auto split: option.splits CoreType.splits)
  from CoreTm_ArrayProj.prems(1) a have
      len: "length idxTms = length dims" and
      all: "list_all (\<lambda>tm. core_term_type env NotGhost tm
                              = Some (CoreTy_FiniteInt Unsigned IntBits_64)) idxTms" and
      ty_eq: "ty = elemTy"
    by (auto split: if_splits)
  let ?E = "erase_ghost_term (TE_Functions env)"
  have aE: "core_term_type envE NotGhost (?E arr) = Some (CoreTy_Array elemTy dims)"
    by (rule CoreTm_ArrayProj.IH(1)[OF a wf rel])
  have allE: "list_all (\<lambda>tm. core_term_type envE NotGhost tm
                                = Some (CoreTy_FiniteInt Unsigned IntBits_64)) (map ?E idxTms)"
    unfolding list_all_iff
  proof
    fix tmE assume "tmE \<in> set (map ?E idxTms)"
    then obtain tm where tin: "tm \<in> set idxTms" and tmE: "tmE = ?E tm" by auto
    have "core_term_type env NotGhost tm = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
      using all tin by (simp add: list_all_iff)
    hence "core_term_type envE NotGhost (?E tm) = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
      by (rule CoreTm_ArrayProj.IH(2)[OF tin _ wf rel])
    thus "core_term_type envE NotGhost tmE = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
      unfolding tmE .
  qed
  have lenE: "length (map ?E idxTms) = length dims" using len by simp
  have projE: "core_term_type envE NotGhost (CoreTm_ArrayProj (?E arr) (map ?E idxTms))
                 = Some ty"
    using aE lenE allE ty_eq by simp
  have eq: "?E (CoreTm_ArrayProj arr idxTms) = CoreTm_ArrayProj (?E arr) (map ?E idxTms)"
    by simp
  show ?case unfolding eq by (rule projE)
next
  case (CoreTm_VariantProj tm ctorName)
  note wf = CoreTm_VariantProj.prems(2) and rel = CoreTm_VariantProj.prems(3)
  from CoreTm_VariantProj.prems(1) obtain dtName tyArgs where
      t: "core_term_type env NotGhost tm = Some (CoreTy_Datatype dtName tyArgs)"
    by (auto split: option.splits CoreType.splits)
  from CoreTm_VariantProj.prems(1) t obtain tyvars payloadTy where
      lk: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payloadTy)" and
      len: "length tyArgs = length tyvars" and
      ty_eq: "ty = apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy"
    by (auto split: option.splits prod.splits if_splits)
  have "is_runtime_type env (CoreTy_Datatype dtName tyArgs)"
    by (rule core_term_type_notghost_runtime[OF t wf])
  hence ng: "dtName |\<notin>| TE_GhostDatatypes env" by simp
  have lkE: "fmlookup (TE_DataCtors envE) ctorName = Some (dtName, tyvars, payloadTy)"
    by (rule tyenv_erased_ctor_lookup[OF rel lk ng])
  have tE: "core_term_type envE NotGhost (erase_ghost_term (TE_Functions env) tm)
              = Some (CoreTy_Datatype dtName tyArgs)"
    by (rule CoreTm_VariantProj.IH[OF t wf rel])
  show ?case using tE lkE len ty_eq by simp
next
  case (CoreTm_Match scrut arms)
  note wf = CoreTm_Match.prems(2) and rel = CoreTm_Match.prems(3)
  let ?E = "erase_ghost_term (TE_Functions env)"
  let ?armsE = "map (\<lambda>(pat, tm). (pat, ?E tm)) arms"
  from CoreTm_Match.prems(1) obtain scrutTy where
      s: "core_term_type env NotGhost scrut = Some scrutTy"
    by (auto split: option.splits)
  from CoreTm_Match.prems(1) s have
      ne: "arms \<noteq> []" and
      pats: "list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst arms)" and
      hdT: "core_term_type env NotGhost (snd (hd arms)) = Some ty" and
      tlT: "list_all (\<lambda>body. core_term_type env NotGhost body = Some ty)
                    (tl (map snd arms))"
    by (auto simp: Let_def split: option.splits if_splits)
  have sE: "core_term_type envE NotGhost (?E scrut) = Some scrutTy"
    by (rule CoreTm_Match.IH(1)[OF s wf rel])
  have srt: "is_runtime_type env scrutTy"
    by (rule core_term_type_notghost_runtime[OF s wf])
  have patsE: "list_all (\<lambda>p. pattern_compatible envE p scrutTy) (map fst arms)"
    unfolding list_all_iff
  proof
    fix p assume pin: "p \<in> set (map fst arms)"
    have pc: "pattern_compatible env p scrutTy"
      using pats pin by (auto simp: list_all_iff)
    show "pattern_compatible envE p scrutTy"
      by (rule pattern_compatible_erased[OF rel wf pc srt])
  qed
  have hin: "hd arms \<in> set arms" using ne by simp
  have hsn: "snd (hd arms) \<in> Basic_BNFs.snds (hd arms)"
    by (cases "hd arms") simp
  have hdE: "core_term_type envE NotGhost (?E (snd (hd arms))) = Some ty"
    by (rule CoreTm_Match.IH(2)[OF hin hsn hdT wf rel])
  have tlE: "list_all (\<lambda>body. core_term_type envE NotGhost (?E body) = Some ty)
                      (tl (map snd arms))"
    unfolding list_all_iff
  proof
    fix body assume bin: "body \<in> set (tl (map snd arms))"
    then obtain arm where ain: "arm \<in> set arms" and b: "body = snd arm"
      using ne by (cases arms) auto
    have sn: "body \<in> Basic_BNFs.snds arm" using b by (cases arm) simp
    have "core_term_type env NotGhost body = Some ty"
      using tlT bin by (auto simp: list_all_iff)
    thus "core_term_type envE NotGhost (?E body) = Some ty"
      by (rule CoreTm_Match.IH(2)[OF ain sn _ wf rel])
  qed
  \<comment> \<open>The same facts, about the erased arms.\<close>
  have fstE: "map fst ?armsE = map fst arms"
    by (induction arms) auto
  have sndE: "map snd ?armsE = map ?E (map snd arms)"
    by (induction arms) auto
  have neE: "?armsE \<noteq> []" using ne by simp
  have patsE': "list_all (\<lambda>p. pattern_compatible envE p scrutTy) (map fst ?armsE)"
    unfolding fstE by (rule patsE)
  have hdE': "core_term_type envE NotGhost (snd (hd ?armsE)) = Some ty"
    by (cases arms) (use hdE ne in \<open>auto simp: case_prod_unfold\<close>)
  have tlE': "list_all (\<lambda>body. core_term_type envE NotGhost body = Some ty)
                       (tl (map snd ?armsE))"
    unfolding sndE
    by (cases arms) (use tlE in \<open>auto simp: list_all_iff\<close>)
  have matchE: "core_term_type envE NotGhost (CoreTm_Match (?E scrut) ?armsE) = Some ty"
    using sE neE patsE' hdE' tlE' by (simp add: Let_def)
  have eq: "?E (CoreTm_Match scrut arms) = CoreTm_Match (?E scrut) ?armsE" by simp
  show ?case unfolding eq by (rule matchE)
next
  case (CoreTm_Sizeof tm)
  note wf = CoreTm_Sizeof.prems(2) and rel = CoreTm_Sizeof.prems(3)
  from CoreTm_Sizeof.prems(1) obtain elemTy dims where
      t: "core_term_type env NotGhost tm = Some (CoreTy_Array elemTy dims)"
    by (auto split: option.splits CoreType.splits)
  have tE: "core_term_type envE NotGhost (erase_ghost_term (TE_Functions env) tm)
              = Some (CoreTy_Array elemTy dims)"
    by (rule CoreTm_Sizeof.IH[OF t wf rel])
  show ?case using CoreTm_Sizeof.prems(1) t tE by simp
next
  case (CoreTm_Allocated ty tm)
  then show ?case by simp
next
  case (CoreTm_Old tm)
  then show ?case by simp
next
  case (CoreTm_Default dty)
  note rel = CoreTm_Default.prems(3)
  from CoreTm_Default.prems(1) have
      wk: "is_well_kinded env dty" and
      rt: "is_runtime_type env dty" and
      ty_eq: "ty = dty"
    by (auto split: if_splits)
  show ?case using tyenv_erased_runtime_type[OF rel wk rt] ty_eq by simp
qed

end
