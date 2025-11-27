theory ResolveTypedefs
  imports BabSyntax
begin

(* Resolve a typedef name to its underlying type *)
(* This recursively resolves all typedefs found inside e.g. tuples and arrays as well *)
(* Returns None if fuel runs out, Some ty otherwise *)
fun resolve_typedefs :: "nat \<Rightarrow> (string, DeclTypedef) fmap \<Rightarrow> BabType \<Rightarrow> BabType option" where
  "resolve_typedefs 0 _ _ = None"  (* Fuel exhausted *)
| "resolve_typedefs (Suc fuel) typedefs (BabTy_Name loc name tyargs) =
    (case those (map (resolve_typedefs fuel typedefs) tyargs) of
      None \<Rightarrow> None
    | Some resolved_tyargs \<Rightarrow>
        (case fmlookup typedefs name of
          Some typedef \<Rightarrow>
            (case DT_Definition typedef of
              Some body \<Rightarrow>
                let typarams = DT_TyArgs typedef;
                    subst = fmap_of_list (zip typarams resolved_tyargs)
                in resolve_typedefs fuel typedefs (substitute_bab_type subst body)
            | None \<Rightarrow>
                Some (BabTy_Name loc name resolved_tyargs))
        | None \<Rightarrow>
            Some (BabTy_Name loc name resolved_tyargs)))"
| "resolve_typedefs (Suc fuel) typedefs (BabTy_Tuple loc tys) =
    (case those (map (resolve_typedefs fuel typedefs) tys) of
      None \<Rightarrow> None
    | Some resolved_tys \<Rightarrow> Some (BabTy_Tuple loc resolved_tys))"
| "resolve_typedefs (Suc fuel) typedefs (BabTy_Record loc flds) =
    (case those (map (\<lambda>(name, ty). case resolve_typedefs fuel typedefs ty of
                                     None \<Rightarrow> None
                                   | Some rty \<Rightarrow> Some (name, rty)) flds) of
      None \<Rightarrow> None
    | Some resolved_flds \<Rightarrow> Some (BabTy_Record loc resolved_flds))"
| "resolve_typedefs (Suc fuel) typedefs (BabTy_Array loc ty dims) =
    (case resolve_typedefs fuel typedefs ty of
      None \<Rightarrow> None
    | Some resolved_ty \<Rightarrow> Some (BabTy_Array loc resolved_ty dims))"
| "resolve_typedefs (Suc fuel) _ ty = Some ty"  (* Base types *)


(* Helper lemma: if those succeeds on a list, every element is Some *)
lemma those_Some_implies_all_Some:
  assumes "those xs = Some ys"
  shows "\<forall>x \<in> set xs. x \<noteq> None"
  using assms
  by (induction xs arbitrary: ys) (auto split: option.splits)

(* Helper lemma: those preserves length *)
lemma those_length:
  assumes "those xs = Some ys"
  shows "length ys = length xs"
  using assms
  by (induction xs arbitrary: ys) (auto split: option.splits)

(* Helper lemma: those nth element *)
lemma those_nth:
  assumes "those xs = Some ys" and "i < length xs"
  shows "xs ! i = Some (ys ! i)"
  using assms
proof (induction xs arbitrary: ys i)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  from Cons.prems obtain y ys' where "x = Some y" and "those xs = Some ys'" and "ys = y # ys'"
    by (auto split: option.splits)
  show ?case
  proof (cases i)
    case 0
    with \<open>x = Some y\<close> \<open>ys = y # ys'\<close> show ?thesis by simp
  next
    case (Suc j)
    with Cons.prems have "j < length xs" by simp
    with Cons.IH \<open>those xs = Some ys'\<close> have "xs ! j = Some (ys' ! j)" by simp
    with Suc \<open>ys = y # ys'\<close> show ?thesis by simp
  qed
qed

(* Helper lemma: those iff all elements are Some *)
lemma those_iff_all_Some:
  "those xs = Some ys \<longleftrightarrow> (length ys = length xs \<and> (\<forall>i < length xs. xs ! i = Some (ys ! i)))"
proof
  assume "those xs = Some ys"
  then show "length ys = length xs \<and> (\<forall>i<length xs. xs ! i = Some (ys ! i))"
    using those_length those_nth by blast
next
  assume "length ys = length xs \<and> (\<forall>i<length xs. xs ! i = Some (ys ! i))"
  then show "those xs = Some ys"
  proof (induction xs arbitrary: ys)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs)
    then obtain y ys' where "ys = y # ys'" by (cases ys) auto
    with Cons have "x = Some y" by (metis length_Cons nth_Cons_0 zero_less_Suc)
    moreover from Cons \<open>ys = y # ys'\<close> have "length ys' = length xs" by simp
    moreover from Cons \<open>ys = y # ys'\<close> have "\<forall>i<length xs. xs ! i = Some (ys' ! i)"
      by (metis Suc_less_eq length_Cons nth_Cons_Suc)
    ultimately show ?case using Cons.IH \<open>ys = y # ys'\<close> by auto
  qed
qed

(* Helper lemma: map f xs = ys iff they have same length and agree pointwise *)
lemma map_nth_eq_conv:
  "map f xs = ys \<longleftrightarrow> (length ys = length xs \<and> (\<forall>i < length xs. f (xs ! i) = ys ! i))"
  by (auto simp: list_eq_iff_nth_eq)


(* resolve_typedefs is monotonic in fuel *)
lemma resolve_typedefs_monotonic:
  assumes "resolve_typedefs fuel typedefs ty = Some ty'"
    and "fuel' \<ge> fuel"
  shows "resolve_typedefs fuel' typedefs ty = Some ty'"
  using assms
proof (induction fuel typedefs ty arbitrary: fuel' ty' rule: resolve_typedefs.induct)
  case (1 typedefs ty)
  (* fuel = 0 case *)
  then show ?case by simp
next
  case (2 fuel typedefs loc name tyargs)
  (* BabTy_Name case *)
  show ?case
  proof (cases fuel')
    case 0
    with 2 show ?thesis by simp
  next
    case (Suc fuel'_pred)
    with 2 have fuel_le: "fuel'_pred \<ge> fuel" by simp

    (* Extract what we know from the assumption *)
    from 2 have "resolve_typedefs (Suc fuel) typedefs (BabTy_Name loc name tyargs) = Some ty'"
      by blast
    then obtain resolved_tyargs where
      tyargs_resolved: "those (map (resolve_typedefs fuel typedefs) tyargs) = Some resolved_tyargs"
      by (auto split: option.splits)

    (* Use IH to show tyargs resolve the same with more fuel *)
    have ih_tyargs: "\<forall>t \<in> set tyargs. \<forall>ty_t.
          resolve_typedefs fuel typedefs t = Some ty_t \<longrightarrow>
          resolve_typedefs fuel'_pred typedefs t = Some ty_t"
      using "2.IH" fuel_le by blast

    (* Show that map with fuel'_pred gives same result as map with fuel *)
    have all_some: "\<forall>t \<in> set (map (resolve_typedefs fuel typedefs) tyargs). t \<noteq> None"
      using tyargs_resolved those_Some_implies_all_Some by metis

    have tyargs_eq: "\<forall>t \<in> set tyargs. resolve_typedefs fuel'_pred typedefs t = resolve_typedefs fuel typedefs t"
    proof
      fix t
      assume t_in: "t \<in> set tyargs"
      then have "resolve_typedefs fuel typedefs t \<in> set (map (resolve_typedefs fuel typedefs) tyargs)"
        by auto
      with all_some have "resolve_typedefs fuel typedefs t \<noteq> None"
        by auto
      then obtain ty_t where res_fuel: "resolve_typedefs fuel typedefs t = Some ty_t"
        by auto
      with t_in ih_tyargs have "resolve_typedefs fuel'_pred typedefs t = Some ty_t"
        by blast
      with res_fuel show "resolve_typedefs fuel'_pred typedefs t = resolve_typedefs fuel typedefs t"
        by simp
    qed

    have tyargs_resolved': "those (map (resolve_typedefs fuel'_pred typedefs) tyargs) = Some resolved_tyargs"
      using tyargs_eq tyargs_resolved map_ext by metis

    (* Now handle the typedef lookup and body substitution *)
    show ?thesis
    proof (cases "fmlookup typedefs name")
      case None
      (* No typedef found - just return Name with resolved tyargs *)
      from 2 None tyargs_resolved have "ty' = BabTy_Name loc name resolved_tyargs"
        by auto
      with None tyargs_resolved' Suc show ?thesis by auto
    next
      case SomeTydef: (Some tydef)
      then show ?thesis
      proof (cases "DT_Definition tydef")
        case None
        (* Abstract/extern type - just return Name with resolved tyargs *)
        with SomeTydef tyargs_resolved tyargs_resolved' Suc show ?thesis
          using "2.prems"(1) by force 
      next
        case SomeBody: (Some body)
        (* Concrete typedef - need to substitute and recurse *)
        define typarams where "typarams = DT_TyArgs tydef"
        define subst where "subst = fmap_of_list (zip typarams resolved_tyargs)"
        define subst_body where "subst_body = substitute_bab_type subst body"

        from 2 SomeTydef SomeBody tyargs_resolved have
          "resolve_typedefs fuel typedefs subst_body = Some ty'"
          by (metis (no_types, lifting) option.simps(5) resolve_typedefs.simps(2) subst_body_def subst_def
              typarams_def)

        (* Use the IH for the substituted body *)
        with fuel_le "2.IH" have
          "resolve_typedefs fuel'_pred typedefs subst_body = Some ty'"
          using SomeBody SomeTydef subst_body_def subst_def tyargs_resolved typarams_def by blast
          
        with tyargs_resolved' SomeTydef SomeBody Suc show ?thesis
          by (auto simp: typarams_def subst_def subst_body_def)
      qed
    qed
  qed
next
  case (3 fuel typedefs loc tys)
  (* BabTy_Tuple case *)
  show ?case
  proof (cases fuel')
    case 0
    with 3 show ?thesis by simp
  next
    case (Suc fuel'_pred)
    with 3 have fuel_le: "fuel \<le> fuel'_pred" by simp
    from 3 obtain resolved_tys where
      those_result: "those (map (resolve_typedefs fuel typedefs) tys) = Some resolved_tys"
      and ty'_eq: "ty' = BabTy_Tuple loc resolved_tys"
      by (auto split: option.splits)

    (* Use IH for each element of tys *)
    have ih_all: "\<forall>t \<in> set tys. \<forall>ty_t.
          resolve_typedefs fuel typedefs t = Some ty_t \<longrightarrow>
          resolve_typedefs fuel'_pred typedefs t = Some ty_t"
      using "3.IH" fuel_le by blast

    (* Show that map with fuel'_pred gives same result as map with fuel *)
    have all_some: "\<forall>t \<in> set (map (resolve_typedefs fuel typedefs) tys). t \<noteq> None"
      using those_result those_Some_implies_all_Some
      by metis 

    have map_eq: "\<forall>t \<in> set tys. resolve_typedefs fuel'_pred typedefs t = resolve_typedefs fuel typedefs t"
    proof
      fix t
      assume t_in: "t \<in> set tys"
      then have "resolve_typedefs fuel typedefs t \<in> set (map (resolve_typedefs fuel typedefs) tys)"
        by auto
      with all_some have "resolve_typedefs fuel typedefs t \<noteq> None"
        by auto
      then obtain ty_t where res_fuel: "resolve_typedefs fuel typedefs t = Some ty_t"
        by auto
      with t_in ih_all have "resolve_typedefs fuel'_pred typedefs t = Some ty_t"
        by blast
      with res_fuel show "resolve_typedefs fuel'_pred typedefs t = resolve_typedefs fuel typedefs t"
        by simp
    qed

    have "those (map (resolve_typedefs fuel'_pred typedefs) tys) = those (map (resolve_typedefs fuel typedefs) tys)"
      using map_eq map_ext by metis
    with those_result have "those (map (resolve_typedefs fuel'_pred typedefs) tys) = Some resolved_tys"
      by simp

    with Suc ty'_eq show ?thesis by simp
  qed
next
  case (4 fuel typedefs loc flds)
  (* BabTy_Record case *)
  show ?case
  proof (cases fuel')
    case 0
    with 4 show ?thesis by simp
  next
    case (Suc fuel'_pred)
    with 4 have fuel_le: "fuel \<le> fuel'_pred" by simp
    from 4 obtain resolved_flds where
      those_result: "those (map (\<lambda>(name, ty). case resolve_typedefs fuel typedefs ty of
                                     None \<Rightarrow> None
                                   | Some rty \<Rightarrow> Some (name, rty)) flds) = Some resolved_flds"
      and ty'_eq: "ty' = BabTy_Record loc resolved_flds"
      by (auto split: option.splits)

    (* Use IH for each field type *)
    have ih_all: "\<forall>(name, ty) \<in> set flds. \<forall>ty_t.
          resolve_typedefs fuel typedefs ty = Some ty_t \<longrightarrow>
          resolve_typedefs fuel'_pred typedefs ty = Some ty_t"
      using "4.IH" fuel_le by blast

    (* Show that map with fuel'_pred gives same result as map with fuel *)
    have all_some: "\<forall>x \<in> set (map (\<lambda>(name, ty). case resolve_typedefs fuel typedefs ty of
                                     None \<Rightarrow> None
                                   | Some rty \<Rightarrow> Some (name, rty)) flds). x \<noteq> None"
      using those_result those_Some_implies_all_Some
      by metis

    have map_eq: "\<forall>x \<in> set flds.
          (case x of (name, ty) \<Rightarrow>
            (case resolve_typedefs fuel'_pred typedefs ty of None \<Rightarrow> None | Some rty \<Rightarrow> Some (name, rty))) =
          (case x of (name, ty) \<Rightarrow>
            (case resolve_typedefs fuel typedefs ty of None \<Rightarrow> None | Some rty \<Rightarrow> Some (name, rty)))"
    proof
      fix x
      assume x_in: "x \<in> set flds"
      obtain name ty where x_def: "x = (name, ty)" by (cases x)
      with x_in have name_ty_in: "(name, ty) \<in> set flds" by simp

      (* The mapped element must be Some because those succeeded *)
      have elem_form: "(case resolve_typedefs fuel typedefs ty of None \<Rightarrow> None | Some rty \<Rightarrow> Some (name, rty))
                 \<in> set (map (\<lambda>(name, ty). case resolve_typedefs fuel typedefs ty of
                                     None \<Rightarrow> None
                                   | Some rty \<Rightarrow> Some (name, rty)) flds)"
        using name_ty_in by auto
      with all_some have not_none: "(case resolve_typedefs fuel typedefs ty of None \<Rightarrow> None | Some rty \<Rightarrow> Some (name, rty)) \<noteq> None"
        by auto
      then obtain rty where res_fuel: "resolve_typedefs fuel typedefs ty = Some rty"
        by (auto split: option.splits)
      with name_ty_in ih_all have res_fuel': "resolve_typedefs fuel'_pred typedefs ty = Some rty"
        by blast
      with res_fuel x_def show
        "(case x of (name, ty) \<Rightarrow>
            (case resolve_typedefs fuel'_pred typedefs ty of None \<Rightarrow> None | Some rty \<Rightarrow> Some (name, rty))) =
         (case x of (name, ty) \<Rightarrow>
            (case resolve_typedefs fuel typedefs ty of None \<Rightarrow> None | Some rty \<Rightarrow> Some (name, rty)))"
        by simp
    qed

    have "those (map (\<lambda>(name, ty). case resolve_typedefs fuel'_pred typedefs ty of
                                     None \<Rightarrow> None
                                   | Some rty \<Rightarrow> Some (name, rty)) flds) =
          those (map (\<lambda>(name, ty). case resolve_typedefs fuel typedefs ty of
                                     None \<Rightarrow> None
                                   | Some rty \<Rightarrow> Some (name, rty)) flds)"
      using map_eq map_ext
      by (metis (no_types, lifting)) 
    with those_result have "those (map (\<lambda>(name, ty). case resolve_typedefs fuel'_pred typedefs ty of
                                     None \<Rightarrow> None
                                   | Some rty \<Rightarrow> Some (name, rty)) flds) = Some resolved_flds"
      by simp

    with Suc ty'_eq show ?thesis by simp
  qed
next
  case (5 fuel typedefs loc ty dims)
  (* BabTy_Array case *)
  show ?case
  proof (cases fuel')
    case 0
    with 5 show ?thesis by simp
  next
    case (Suc fuel'_pred)
    with 5 have fuel_le: "fuel \<le> fuel'_pred"
      by blast

    (* The assumption tells us resolve_typedefs (Suc fuel) succeeded *)
    (* which means resolve_typedefs fuel ty succeeded *)
    from 5 have "resolve_typedefs (Suc fuel) typedefs (BabTy_Array loc ty dims) = Some ty'"
      by blast
    then obtain resolved_ty where
      resolve_result: "resolve_typedefs fuel typedefs ty = Some resolved_ty"
      and ty'_eq: "ty' = BabTy_Array loc resolved_ty dims"
      by (auto split: option.splits)

    (* Use IH for the element type *)
    from resolve_result fuel_le "5.IH" have
      "resolve_typedefs fuel'_pred typedefs ty = Some resolved_ty"
      by blast

    with Suc ty'_eq show ?thesis by simp
  qed
next
  (* BabTy_Bool case *)
  case ("6_1" fuel typedefs loc)
  then show ?case by (cases fuel'; auto)
next
  (* BabTy_FiniteInt case *)
  case ("6_2" fuel typedefs loc sign bits)
  then show ?case by (cases fuel'; auto)
next
  (* BabTy_MathInt case *)
  case ("6_3" fuel typedefs loc)
  then show ?case by (cases fuel'; auto)
next
  (* BabTy_MathReal case *)
  case ("6_4" fuel typedefs loc)
  then show ?case by (cases fuel'; auto)
qed


(* resolve_typedefs is idempotent: resolving an already-resolved type gives the same result *)
lemma resolve_typedefs_idempotent:
  assumes "resolve_typedefs fuel typedefs ty = Some ty'"
  shows "resolve_typedefs fuel typedefs ty' = Some ty'"
  using assms
proof (induction fuel typedefs ty arbitrary: ty' rule: resolve_typedefs.induct)
  case (1 typedefs ty)
  then show ?case by simp
next
  case (2 fuel typedefs loc name tyargs)
  (* BabTy_Name case *)
  from 2 obtain resolved_tyargs where
    those_result: "those (map (resolve_typedefs fuel typedefs) tyargs) = Some resolved_tyargs"
    by (auto split: option.splits)
  show ?case
  proof (cases "fmlookup typedefs name")
    case None
    (* Name not in typedefs - result is BabTy_Name with resolved tyargs *)
    with 2 those_result have ty'_eq: "ty' = BabTy_Name loc name resolved_tyargs"
      by auto
    (* Each resolved_tyarg is idempotent by IH *)
    have ih_tyargs: "\<forall>t \<in> set tyargs. \<forall>t'. resolve_typedefs fuel typedefs t = Some t' \<longrightarrow>
                     resolve_typedefs fuel typedefs t' = Some t'"
      using "2.IH" None by blast
    (* Show that resolving resolved_tyargs gives resolved_tyargs *)
    have all_some: "\<forall>t \<in> set (map (resolve_typedefs fuel typedefs) tyargs). t \<noteq> None"
      using those_result those_Some_implies_all_Some by metis
    have resolved_idempotent: "those (map (resolve_typedefs fuel typedefs) resolved_tyargs) = Some resolved_tyargs"
    proof -
      have "length resolved_tyargs = length tyargs"
        using those_result by (metis length_map those_length)
      moreover have "\<forall>i < length tyargs. resolve_typedefs fuel typedefs (resolved_tyargs ! i) = Some (resolved_tyargs ! i)"
      proof (intro allI impI)
        fix i assume i_bound: "i < length tyargs"
        then have "tyargs ! i \<in> set tyargs" by simp
        from those_nth[OF those_result] i_bound have
          map_nth: "(map (resolve_typedefs fuel typedefs) tyargs) ! i = Some (resolved_tyargs ! i)"
          by (simp add: \<open>length resolved_tyargs = length tyargs\<close>)
        then have res: "resolve_typedefs fuel typedefs (tyargs ! i) = Some (resolved_tyargs ! i)"
          using i_bound by simp
        with ih_tyargs \<open>tyargs ! i \<in> set tyargs\<close> show "resolve_typedefs fuel typedefs (resolved_tyargs ! i) = Some (resolved_tyargs ! i)"
          by auto
      qed
      ultimately show ?thesis
        by (metis map_nth_eq_conv those_iff_all_Some)
    qed
    with ty'_eq None show ?thesis by simp
  next
    case (Some tydef)
    then show ?thesis
    proof (cases "DT_Definition tydef")
      case None
      (* Abstract type - result is BabTy_Name with resolved tyargs *)
      with Some 2 those_result have ty'_eq: "ty' = BabTy_Name loc name resolved_tyargs"
        by auto
      have ih_tyargs: "\<forall>t \<in> set tyargs. \<forall>t'. resolve_typedefs fuel typedefs t = Some t' \<longrightarrow>
                       resolve_typedefs fuel typedefs t' = Some t'"
        using "2.IH" Some None by blast
      have all_some: "\<forall>t \<in> set (map (resolve_typedefs fuel typedefs) tyargs). t \<noteq> None"
        using those_result those_Some_implies_all_Some by metis
      have resolved_idempotent: "those (map (resolve_typedefs fuel typedefs) resolved_tyargs) = Some resolved_tyargs"
      proof -
        have "length resolved_tyargs = length tyargs"
          using those_result by (metis length_map those_length)
        moreover have "\<forall>i < length tyargs. resolve_typedefs fuel typedefs (resolved_tyargs ! i) = Some (resolved_tyargs ! i)"
        proof (intro allI impI)
          fix i assume i_bound: "i < length tyargs"
          then have "tyargs ! i \<in> set tyargs" by simp
          from those_nth[OF those_result] i_bound have
            map_nth: "(map (resolve_typedefs fuel typedefs) tyargs) ! i = Some (resolved_tyargs ! i)"
            by (simp add: \<open>length resolved_tyargs = length tyargs\<close>)
          then have res: "resolve_typedefs fuel typedefs (tyargs ! i) = Some (resolved_tyargs ! i)"
            using i_bound by simp
          with ih_tyargs \<open>tyargs ! i \<in> set tyargs\<close> show "resolve_typedefs fuel typedefs (resolved_tyargs ! i) = Some (resolved_tyargs ! i)"
            by auto
        qed
        ultimately show ?thesis
          by (metis map_nth_eq_conv those_iff_all_Some)
      qed
      with ty'_eq Some None show ?thesis by simp
    next
      case (Some body)
      (* Concrete typedef - recursively resolved *)
      define typarams where "typarams = DT_TyArgs tydef"
      define subst where "subst = fmap_of_list (zip typarams resolved_tyargs)"
      define subst_body where "subst_body = substitute_bab_type subst body"
      from \<open>fmlookup typedefs name = Some tydef\<close> Some those_result 2 have
        res_subst: "resolve_typedefs fuel typedefs subst_body = Some ty'"
        by (simp add: typarams_def subst_def subst_body_def)
      (* Use the IH for the substituted body *)
      from "2.IH"(2)
      have "resolve_typedefs fuel typedefs ty' = Some ty'"
        using Some \<open>fmlookup typedefs name = Some tydef\<close> res_subst subst_body_def subst_def
          those_result typarams_def by blast
      then show ?thesis
        using resolve_typedefs_monotonic[of fuel typedefs ty' ty' "Suc fuel"] by simp
    qed
  qed
next
  case (3 fuel typedefs loc tys)
  (* BabTy_Tuple case *)
  from 3 obtain resolved_tys where
    those_result: "those (map (resolve_typedefs fuel typedefs) tys) = Some resolved_tys"
    and ty'_eq: "ty' = BabTy_Tuple loc resolved_tys"
    by (auto split: option.splits)
  have ih_tys: "\<forall>t \<in> set tys. \<forall>t'. resolve_typedefs fuel typedefs t = Some t' \<longrightarrow>
               resolve_typedefs fuel typedefs t' = Some t'"
    using "3.IH" by blast
  have all_some: "\<forall>t \<in> set (map (resolve_typedefs fuel typedefs) tys). t \<noteq> None"
    using those_result those_Some_implies_all_Some by metis
  have resolved_idempotent: "those (map (resolve_typedefs fuel typedefs) resolved_tys) = Some resolved_tys"
  proof -
    have "length resolved_tys = length tys"
      using those_result by (metis length_map those_length)
    moreover have "\<forall>i < length tys. resolve_typedefs fuel typedefs (resolved_tys ! i) = Some (resolved_tys ! i)"
    proof (intro allI impI)
      fix i assume i_bound: "i < length tys"
      then have "tys ! i \<in> set tys" by simp
      from those_nth[OF those_result] i_bound have
        map_nth: "(map (resolve_typedefs fuel typedefs) tys) ! i = Some (resolved_tys ! i)"
        by (simp add: \<open>length resolved_tys = length tys\<close>)
      then have res: "resolve_typedefs fuel typedefs (tys ! i) = Some (resolved_tys ! i)"
        using i_bound by simp
      with ih_tys \<open>tys ! i \<in> set tys\<close> show "resolve_typedefs fuel typedefs (resolved_tys ! i) = Some (resolved_tys ! i)"
        by auto
    qed
    ultimately show ?thesis
      by (metis map_nth_eq_conv those_iff_all_Some)
  qed
  with ty'_eq show ?case by simp
next
  case (4 fuel typedefs loc flds)
  (* BabTy_Record case *)
  let ?map_fld = "\<lambda>(name, ty). case resolve_typedefs fuel typedefs ty of None \<Rightarrow> None | Some rty \<Rightarrow> Some (name, rty)"
  from 4 obtain resolved_flds where
    those_result: "those (map ?map_fld flds) = Some resolved_flds"
    and ty'_eq: "ty' = BabTy_Record loc resolved_flds"
    by (auto split: option.splits)
  have ih_flds: "\<forall>(name, ty) \<in> set flds. \<forall>ty'. resolve_typedefs fuel typedefs ty = Some ty' \<longrightarrow>
               resolve_typedefs fuel typedefs ty' = Some ty'"
    using "4.IH" by blast
  have all_some: "\<forall>x \<in> set (map ?map_fld flds). x \<noteq> None"
    using those_result those_Some_implies_all_Some by metis
  (* Show that resolved_flds has same length as flds and each field type is idempotent *)
  have len_eq: "length resolved_flds = length flds"
    using those_result by (metis length_map those_length)
  have resolved_idempotent: "those (map ?map_fld resolved_flds) = Some resolved_flds"
  proof -
    have "\<forall>i < length flds. ?map_fld (resolved_flds ! i) = Some (resolved_flds ! i)"
    proof (intro allI impI)
      fix i assume i_bound: "i < length flds"
      (* Get the i-th field from flds *)
      obtain fname fty where fld_i: "flds ! i = (fname, fty)" by (cases "flds ! i")
      then have "(fname, fty) \<in> set flds" using i_bound
        by (metis nth_mem) 
      (* From those_result, the i-th mapped element is Some (resolved_flds ! i) *)
      from those_nth[OF those_result] i_bound have
        map_nth: "(map ?map_fld flds) ! i = Some (resolved_flds ! i)"
        by (simp add: len_eq)
      then have "?map_fld (flds ! i) = Some (resolved_flds ! i)"
        using i_bound by simp
      with fld_i obtain rty where
        res_fty: "resolve_typedefs fuel typedefs fty = Some rty"
        and resolved_i: "resolved_flds ! i = (fname, rty)"
        by (auto split: option.splits)
      (* By IH, resolving rty again gives rty *)
      from ih_flds \<open>(fname, fty) \<in> set flds\<close> res_fty have
        "resolve_typedefs fuel typedefs rty = Some rty" by auto
      with resolved_i show "?map_fld (resolved_flds ! i) = Some (resolved_flds ! i)"
        by simp
    qed
    with len_eq show ?thesis
      by (simp add: those_iff_all_Some)
  qed
  with ty'_eq show ?case by simp
next
  case (5 fuel typedefs loc ty dims)
  (* BabTy_Array case *)
  from 5 obtain resolved_ty where
    resolve_result: "resolve_typedefs fuel typedefs ty = Some resolved_ty"
    and ty'_eq: "ty' = BabTy_Array loc resolved_ty dims"
    by (auto split: option.splits)
  from "5.IH"[OF resolve_result] have ih: "resolve_typedefs fuel typedefs resolved_ty = Some resolved_ty"
    by simp
  with ty'_eq show ?case by simp
next
  (* Base types - BabTy_Bool *)
  case ("6_1" fuel typedefs loc)
  then show ?case by auto
next
  (* Base types - BabTy_FiniteInt *)
  case ("6_2" fuel typedefs loc sign bits)
  then show ?case by auto
next
  (* Base types - BabTy_MathInt *)
  case ("6_3" fuel typedefs loc)
  then show ?case by auto
next
  (* Base types - BabTy_MathReal *)
  case ("6_4" fuel typedefs loc)
  then show ?case by auto
qed

end
