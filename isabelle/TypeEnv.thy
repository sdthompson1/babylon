theory TypeEnv
  imports BabSyntax
begin

record BabTyEnv =
  (* Term-level bindings: variables and constants *)
  (* Types are kind-correct and all typedefs are resolved *)
  TE_TermVars :: "(string, BabType) fmap"

  (* Ghost variables - subset of TE_TermVars keys *)
  TE_GhostVars :: "string fset"

  (* Type variable bindings: for polymorphic contexts *)
  TE_TypeVars :: "string fset"

  (* Function signatures *)
  (* DeclFuns are valid and have all typedefs resolved *)
  TE_Functions :: "(string, DeclFun) fmap"

  (* Datatype definitions *)
  (* DeclDatatypes are valid and have all typedefs resolved *)
  TE_Datatypes :: "(string, DeclDatatype) fmap"


(* Helper functions for BabTyEnv *)

(* Add a variable to the environment *)
(*
fun add_var :: "string \<Rightarrow> BabType \<Rightarrow> GhostOrNot \<Rightarrow> BabTyEnv \<Rightarrow> BabTyEnv" where
  "add_var name ty Ghost env =
    env \<lparr> TE_TermVars := fmupd name ty (TE_TermVars env),
          TE_GhostVars := finsert name (TE_GhostVars env) \<rparr>"
| "add_var name ty NotGhost env =
    env \<lparr> TE_TermVars := fmupd name ty (TE_TermVars env) \<rparr>"
*)

(* Add a type variable to the environment *)
(*
fun add_type_var :: "string \<Rightarrow> BabTyEnv \<Rightarrow> BabTyEnv" where
  "add_type_var name env = env \<lparr> TE_TypeVars := finsert name (TE_TypeVars env) \<rparr>"
*)

(* Clear local variables (for entering a new function scope) *)
(*
fun clear_locals :: "BabTyEnv \<Rightarrow> BabTyEnv" where
  "clear_locals env = env \<lparr> TE_TermVars := fmempty, TE_GhostVars := {||}, TE_TypeVars := {||} \<rparr>"
*)

(* Check if a type is an integer type *)
fun is_integer_type :: "BabType \<Rightarrow> bool" where
  "is_integer_type (BabTy_FiniteInt _ _ _) = True"
| "is_integer_type (BabTy_MathInt _) = True"
| "is_integer_type _ = False"

(* Check if a type is a signed integer type (signed finite int or MathInt) *)
fun is_signed_integer_type :: "BabType \<Rightarrow> bool" where
  "is_signed_integer_type (BabTy_FiniteInt _ Signed _) = True"
| "is_signed_integer_type (BabTy_MathInt _) = True"
| "is_signed_integer_type _ = False"

(* Check if a type is a finite integer type *)
fun is_finite_integer_type :: "BabType \<Rightarrow> bool" where
  "is_finite_integer_type (BabTy_FiniteInt _ _ _) = True"
| "is_finite_integer_type _ = False"

(* Check if an array dimension is resolved (not BabDim_Fixed) *)
fun is_resolved_dimension :: "BabDimension \<Rightarrow> bool" where
  "is_resolved_dimension (BabDim_Fixed _) = False"
| "is_resolved_dimension _ = True"

(* Check if a type is a runtime-compatible type (no MathInt/MathReal/Meta) *)
fun is_runtime_type :: "BabType \<Rightarrow> bool" where
  "is_runtime_type (BabTy_MathInt _) = False"
| "is_runtime_type (BabTy_MathReal _) = False"
| "is_runtime_type (BabTy_Meta _) = False"  (* metavariables must be resolved *)
| "is_runtime_type (BabTy_Tuple _ tys) = list_all is_runtime_type tys"
| "is_runtime_type (BabTy_Record _ flds) = list_all (is_runtime_type \<circ> snd) flds"
| "is_runtime_type (BabTy_Array _ ty _) = is_runtime_type ty"
| "is_runtime_type _ = True"


(* Check structural equality of types *)
(* This only works on fully resolved types, i.e. typedefs are not followed. *)
(* Also, types inside BabDimension terms are not followed - so this should be used only
   on types where BabDim_Fixed has been elaborated to BabDim_FixedInt. *)
function types_equal :: "BabType \<Rightarrow> BabType \<Rightarrow> bool" where
  "types_equal ty1 ty2 =
    (case (ty1, ty2) of
      (BabTy_Bool _, BabTy_Bool _) \<Rightarrow> True
    | (BabTy_FiniteInt _ s1 b1, BabTy_FiniteInt _ s2 b2) \<Rightarrow> (s1 = s2 \<and> b1 = b2)
    | (BabTy_MathInt _, BabTy_MathInt _) \<Rightarrow> True
    | (BabTy_MathReal _, BabTy_MathReal _) \<Rightarrow> True
    | (BabTy_Meta n1, BabTy_Meta n2) \<Rightarrow> (n1 = n2)
    | (BabTy_Tuple _ tys1, BabTy_Tuple _ tys2) \<Rightarrow>
        (length tys1 = length tys2 \<and>
         list_all (\<lambda>(t1, t2). types_equal t1 t2) (zip tys1 tys2))
    | (BabTy_Record _ flds1, BabTy_Record _ flds2) \<Rightarrow>
        (length flds1 = length flds2 \<and>
         list_all (\<lambda>(fld1, fld2). fst fld1 = fst fld2 \<and> types_equal (snd fld1) (snd fld2))
                 (zip flds1 flds2))
    | (BabTy_Array _ elem1 dims1, BabTy_Array _ elem2 dims2) \<Rightarrow>
        (dims1 = dims2 \<and> types_equal elem1 elem2)
    | (BabTy_Name _ n1 tyargs1, BabTy_Name _ n2 tyargs2) \<Rightarrow>
        (n1 = n2 \<and>
         length tyargs1 = length tyargs2 \<and>
         list_all (\<lambda>(ta1, ta2). types_equal ta1 ta2) (zip tyargs1 tyargs2))
    | _ \<Rightarrow> False)"
  by pat_completeness auto

termination types_equal
proof (relation "measure (\<lambda>(t1, t2). bab_type_size t1 + bab_type_size t2)")
  show "wf (measure (\<lambda>(t1, t2). bab_type_size t1 + bab_type_size t2))"
    by auto
next
  (* BabTy_Name case: type arguments in zip are smaller *)
  fix ty1 ty2 x y x11 x12 x13 x11a x12a x13a z xa ya
  assume xy: "(x, y) = (ty1, ty2)"
     and x: "x = BabTy_Name x11 x12 x13"
     and y: "y = BabTy_Name x11a x12a x13a"
     and z: "z \<in> set (zip x13 x13a)"
     and xaya: "(xa, ya) = z"
  have "bab_type_size xa < Suc (sum_list (map bab_type_size x13))"
    by (metis bab_type_smaller_than_list in_set_zipE xaya z)
  hence "bab_type_size xa < bab_type_size ty1"
    using x xy by fastforce
  moreover have "bab_type_size ya < Suc (sum_list (map bab_type_size x13a))"
    by (metis bab_type_smaller_than_list set_zip_rightD xaya z)
  hence "bab_type_size ya < bab_type_size ty2"
    by (metis bab_type_size.simps(1) plus_1_eq_Suc prod.inject xy y)
  ultimately show "((xa, ya), ty1, ty2) \<in> measure (\<lambda>(t1, t2). bab_type_size t1 + bab_type_size t2)"
    by simp
next
  (* Tuple case: elements in zip are smaller *)
  fix ty1 ty2 x y x61 x62 x61a x62a z xa ya
  assume xy: "(x, y) = (ty1, ty2)"
     and x: "x = BabTy_Tuple x61 x62"
     and y: "y = BabTy_Tuple x61a x62a"
     and z: "z \<in> set (zip x62 x62a)"
     and xaya: "(xa, ya) = z"
  have "bab_type_size xa < Suc (sum_list (map bab_type_size x62))"
    by (metis bab_type_smaller_than_list in_set_zipE xaya z)
  hence "bab_type_size xa < bab_type_size ty1"
    using x xy by fastforce
  moreover have "bab_type_size ya < Suc (sum_list (map bab_type_size x62a))"
    by (metis bab_type_smaller_than_list set_zip_rightD xaya z)
  hence "bab_type_size ya < bab_type_size ty2"
    by (metis bab_type_size.simps(6) plus_1_eq_Suc prod.inject xy y)
  ultimately show "((xa, ya), ty1, ty2) \<in> measure (\<lambda>(t1, t2). bab_type_size t1 + bab_type_size t2)"
    by simp
next
  (* Record case: field types in zip are smaller *)
  fix ty1 ty2 x y x71 x72 x71a x72a z fld1 fld2
  assume xy: "(x, y) = (ty1, ty2)"
     and x: "x = BabTy_Record x71 x72"
     and y: "y = BabTy_Record x71a x72a"
     and z: "z \<in> set (zip x72 x72a)"
     and fld12: "(fld1, fld2) = z"
  have "fld1 \<in> set x72"
    by (metis fld12 in_set_zipE z)
  hence "snd fld1 \<in> snd ` set x72"
    by force
  hence "bab_type_size (snd fld1) < Suc (sum_list (map (bab_type_size \<circ> snd) x72))"
    using bab_type_smaller_than_fieldlist by fastforce
  hence "bab_type_size (snd fld1) < bab_type_size ty1"
    using x xy by fastforce
  moreover have "fld2 \<in> set x72a"
    by (metis fld12 set_zip_rightD z)
  hence "snd fld2 \<in> snd ` set x72a"
    by force
  hence "bab_type_size (snd fld2) < Suc (sum_list (map (bab_type_size \<circ> snd) x72a))"
    using bab_type_smaller_than_fieldlist by fastforce
  hence "bab_type_size (snd fld2) < bab_type_size ty2"
    by (metis bab_type_size.simps(7) plus_1_eq_Suc prod.inject xy y)
  ultimately show "((snd fld1, snd fld2), ty1, ty2) \<in> measure (\<lambda>(t1, t2). bab_type_size t1 + bab_type_size t2)"
    by simp
next
  (* Array case: element types are smaller *)
  fix ty1 ty2 x y x81 x82 x83 x81a x82a x83a
  assume xy: "(x, y) = (ty1, ty2)"
     and x: "x = BabTy_Array x81 x82 x83"
     and y: "y = BabTy_Array x81a x82a x83a"
  have "bab_type_size x82 < bab_type_size ty1"
    using x xy by fastforce
  moreover have "bab_type_size x82a < bab_type_size ty2"
    using y xy by fastforce
  ultimately show "((x82, x82a), ty1, ty2) \<in> measure (\<lambda>(ty1, ty2). bab_type_size ty1 + bab_type_size ty2)"
    by simp
qed


(* Simplification lemmas for types_equal *)
lemma types_equal_Tuple:
  "types_equal (BabTy_Tuple loc1 tys1) (BabTy_Tuple loc2 tys2) =
   (length tys1 = length tys2 \<and> list_all (\<lambda>(t1, t2). types_equal t1 t2) (zip tys1 tys2))"
  by (smt (verit, best) BabType.simps(87) old.prod.case types_equal.simps)
  
lemma types_equal_Name:
  "types_equal (BabTy_Name loc1 n1 tyargs1) (BabTy_Name loc2 n2 tyargs2) =
   (n1 = n2 \<and> length tyargs1 = length tyargs2 \<and>
    list_all (\<lambda>(ta1, ta2). types_equal ta1 ta2) (zip tyargs1 tyargs2))"
  by (smt (verit, best) BabType.simps(82) old.prod.case types_equal.simps)

lemma types_equal_Record:
  "types_equal (BabTy_Record loc1 flds1) (BabTy_Record loc2 flds2) =
   (length flds1 = length flds2 \<and>
    list_all (\<lambda>(f1, f2). fst f1 = fst f2 \<and> types_equal (snd f1) (snd f2)) (zip flds1 flds2))"
  by (smt (verit, best) BabType.simps(88) old.prod.case types_equal.simps)


(* Proving that types_equal is an equivalence relation: *)

(* Helper: zip of a list with itself gives paired elements *)
lemma zip_same_list_all:
  "list_all (\<lambda>(x, y). P x y) (zip xs xs) \<longleftrightarrow> list_all (\<lambda>x. P x x) xs"
  by (induction xs) auto

(* types_equal is reflexive *)
lemma types_equal_reflexive:
  "types_equal ty ty"
proof (induction ty rule: measure_induct_rule[where f=bab_type_size])
  case (less ty)
  then show ?case
  proof (cases ty)
    case (BabTy_Bool loc)
    then show ?thesis by simp
  next
    case (BabTy_FiniteInt loc s b)
    then show ?thesis by simp
  next
    case (BabTy_MathInt loc)
    then show ?thesis by simp
  next
    case (BabTy_MathReal loc)
    then show ?thesis by simp
  next
    case (BabTy_Tuple loc tys)
    have "\<And>t. t \<in> set tys \<Longrightarrow> types_equal t t"
      using less BabTy_Tuple bab_type_smaller_than_list by fastforce
    then have "list_all (\<lambda>t. types_equal t t) tys"
      by (simp add: list_all_iff)
    then show ?thesis
      using BabTy_Tuple zip_same_list_all types_equal_Tuple by fastforce
  next
    case (BabTy_Record loc flds)
    have "\<And>fld. fld \<in> set flds \<Longrightarrow> types_equal (snd fld) (snd fld)"
      using less BabTy_Record bab_type_smaller_than_fieldlist by fastforce
    then have "list_all (\<lambda>fld. types_equal (snd fld) (snd fld)) flds"
      by (simp add: list_all_iff)
    then have "list_all (\<lambda>(fld1, fld2). fst fld1 = fst fld2 \<and> types_equal (snd fld1) (snd fld2)) (zip flds flds)"
      by (simp add: zip_same_list_all)
    then show ?thesis
      using BabTy_Record by simp
  next
    case (BabTy_Array loc elem dims)
    then show ?thesis using less by simp
  next
    case (BabTy_Name loc n tyargs)
    have "\<And>t. t \<in> set tyargs \<Longrightarrow> types_equal t t"
      using less BabTy_Name bab_type_smaller_than_list by fastforce
    then have "list_all (\<lambda>t. types_equal t t) tyargs"
      by (simp add: list_all_iff)
    then show ?thesis
      using BabTy_Name zip_same_list_all types_equal_Name by fastforce
  next
    case (BabTy_Meta n)
    then show ?thesis by simp
  qed
qed

(* Helper: if a symmetric property holds for all pairs in two equal-length lists,
   then list_all holds symmetrically *)
lemma list_all_zip_symmetric:
  assumes "\<forall>x y. (x, y) \<in> set (zip xs ys) \<longrightarrow> P x y = P y x"
    and "length xs = length ys"
  shows "list_all (\<lambda>(x, y). P x y) (zip xs ys) = list_all (\<lambda>(x, y). P x y) (zip ys xs)"
  using assms
  by (auto simp: list_all_length set_zip)

(* types_equal is symmetric *)
lemma types_equal_symmetric:
  "types_equal ty1 ty2 = types_equal ty2 ty1"
proof (induction ty1 ty2 rule: types_equal.induct)
  case (1 ty1 ty2)
  show ?case
  proof (cases ty1)
    case (BabTy_Bool loc1)
    then show ?thesis by (cases ty2; simp)
  next
    case (BabTy_FiniteInt loc1 s1 b1)
    then show ?thesis by (cases ty2; auto)
  next
    case (BabTy_MathInt loc1)
    then show ?thesis by (cases ty2; simp)
  next
    case (BabTy_MathReal loc1)
    then show ?thesis by (cases ty2; simp)
  next
    case tuple1: (BabTy_Tuple loc1 tys1)
    then show ?thesis
    proof (cases ty2)
      case tuple2: (BabTy_Tuple loc2 tys2)
      show ?thesis
        using tuple1 tuple2 types_equal_Tuple list_all_zip_symmetric
        by (metis (mono_tags, lifting) "1.IH"(2)) 
    qed auto
  next
    case record1: (BabTy_Record loc1 flds1)
    then show ?thesis
    proof (cases ty2)
      case record2: (BabTy_Record loc2 flds2)
      show ?thesis
        using record1 record2 list_all_zip_symmetric
      proof -
        obtain pp :: "(char list \<times> BabType \<Rightarrow> char list \<times> BabType \<Rightarrow> bool) \<Rightarrow> (char list \<times> BabType) list \<Rightarrow> (char list \<times> BabType) list \<Rightarrow> char list \<times> BabType" and ppa :: "(char list \<times> BabType \<Rightarrow> char list \<times> BabType \<Rightarrow> bool) \<Rightarrow> (char list \<times> BabType) list \<Rightarrow> (char list \<times> BabType) list \<Rightarrow> char list \<times> BabType" where
          f1: "\<forall>x0 x1 x2. (\<exists>v3 v4. (v3, v4) \<in> set (zip x2 x1) \<and> x0 v3 v4 \<noteq> x0 v4 v3) = ((pp x0 x1 x2, ppa x0 x1 x2) \<in> set (zip x2 x1) \<and> x0 (pp x0 x1 x2) (ppa x0 x1 x2) \<noteq> x0 (ppa x0 x1 x2) (pp x0 x1 x2))"
          by moura
        have "\<forall>ps psa p. ((\<exists>pa pb. (pa::char list \<times> BabType, pb) \<in> set (zip ps psa) \<and> p pa pb \<noteq> p pb pa) \<or> length ps \<noteq> length psa) \<or> list_all (\<lambda>(x, y). p x y) (zip ps psa) = list_all (\<lambda>(x, y). p x y) (zip psa ps)"
          by (metis (no_types) list_all_zip_symmetric)
        then have f2: "\<forall>ps psa p. (pp p psa ps, ppa p psa ps) \<in> set (zip ps psa) \<and> p (pp p psa ps) (ppa p psa ps) \<noteq> p (ppa p psa ps) (pp p psa ps) \<or> length ps \<noteq> length psa \<or> list_all (\<lambda>(x, y). p x y) (zip ps psa) = list_all (\<lambda>(x, y). p x y) (zip psa ps)"
          using f1 by simp
        have "(pp (\<lambda>p pa. fst p = fst pa \<and> types_equal (snd p) (snd pa)) flds2 flds1, ppa (\<lambda>p pa. fst p = fst pa \<and> types_equal (snd p) (snd pa)) flds2 flds1) \<in> set (zip flds1 flds2) \<and> (fst (pp (\<lambda>p pa. fst p = fst pa \<and> types_equal (snd p) (snd pa)) flds2 flds1) = fst (ppa (\<lambda>p pa. fst p = fst pa \<and> types_equal (snd p) (snd pa)) flds2 flds1) \<and> types_equal (snd (pp (\<lambda>p pa. fst p = fst pa \<and> types_equal (snd p) (snd pa)) flds2 flds1)) (snd (ppa (\<lambda>p pa. fst p = fst pa \<and> types_equal (snd p) (snd pa)) flds2 flds1))) \<noteq> (fst (ppa (\<lambda>p pa. fst p = fst pa \<and> types_equal (snd p) (snd pa)) flds2 flds1) = fst (pp (\<lambda>p pa. fst p = fst pa \<and> types_equal (snd p) (snd pa)) flds2 flds1) \<and> types_equal (snd (ppa (\<lambda>p pa. fst p = fst pa \<and> types_equal (snd p) (snd pa)) flds2 flds1)) (snd (pp (\<lambda>p pa. fst p = fst pa \<and> types_equal (snd p) (snd pa)) flds2 flds1))) \<longrightarrow> (BabTy_Record loc1 flds1, BabTy_Record loc2 flds2) \<noteq> (ty1, ty2) \<or> types_equal (snd (pp (\<lambda>p pa. fst p = fst pa \<and> types_equal (snd p) (snd pa)) flds2 flds1)) (snd (ppa (\<lambda>p pa. fst p = fst pa \<and> types_equal (snd p) (snd pa)) flds2 flds1)) = types_equal (snd (ppa (\<lambda>p pa. fst p = fst pa \<and> types_equal (snd p) (snd pa)) flds2 flds1)) (snd (pp (\<lambda>p pa. fst p = fst pa \<and> types_equal (snd p) (snd pa)) flds2 flds1))"
          using "1.IH"(3) by blast
        then show ?thesis
          using f2 by (smt (z3) BabType.simps(88) case_prodD case_prodI record1 record2 types_equal.simps)
      qed
        
    qed auto
  next
    case array1: (BabTy_Array loc1 elem1 dims1)
    then show ?thesis
    proof (cases ty2)
      case array2: (BabTy_Array loc2 elem2 dims2)
      show ?thesis
        using array1 array2 "1.IH"(4) by auto
    qed auto
  next
    case name1: (BabTy_Name loc1 n1 tyargs1)
    then show ?thesis
    proof (cases ty2)
      case name2: (BabTy_Name loc2 n2 tyargs2)
      show ?thesis
        using name1 name2 types_equal_Name list_all_zip_symmetric
        by (metis (full_types) "1.IH"(1))
    qed auto
  next
    case (BabTy_Meta n1)
    then show ?thesis by (cases ty2; auto)
  qed
qed

(* Helper for transitivity: zip three lists *)
lemma list_all_zip3_trans:
  assumes "length xs = length ys" "length ys = length zs"
    and "list_all (\<lambda>(x, y). P x y) (zip xs ys)"
    and "list_all (\<lambda>(y, z). P y z) (zip ys zs)"
    and "\<And>x y z. (x, y) \<in> set (zip xs ys) \<Longrightarrow> P x y \<Longrightarrow> P y z \<Longrightarrow> P x z"
  shows "list_all (\<lambda>(x, z). P x z) (zip xs zs)"
  using assms
  by (induction xs ys zs rule: list_induct3) auto

(* types_equal is transitive *)
lemma types_equal_transitive [trans]:
  "types_equal ty1 ty2 \<Longrightarrow> types_equal ty2 ty3 \<Longrightarrow> types_equal ty1 ty3"
proof (induction ty1 ty2 arbitrary: ty3 rule: types_equal.induct)
  case (1 ty1 ty2)
  show ?case
  proof (cases ty1)
    case (BabTy_Bool loc1)
    then show ?thesis using "1.prems" by (cases ty2; cases ty3; simp)
  next
    case (BabTy_FiniteInt loc1 s1 b1)
    then show ?thesis using "1.prems" by (cases ty2; cases ty3; auto)
  next
    case (BabTy_MathInt loc1)
    then show ?thesis using "1.prems" by (cases ty2; cases ty3; simp)
  next
    case (BabTy_MathReal loc1)
    then show ?thesis using "1.prems" by (cases ty2; cases ty3; simp)
  next
    case tuple1: (BabTy_Tuple loc1 tys1)
    then show ?thesis using "1.prems"
    proof (cases ty2)
      case tuple2: (BabTy_Tuple loc2 tys2)
      then show ?thesis using "1.prems" tuple1
      proof (cases ty3)
        case tuple3: (BabTy_Tuple loc3 tys3)
        from "1.prems" tuple1 tuple2 have eq12: "types_equal ty1 ty2" by simp
        from "1.prems" tuple2 tuple3 have eq23: "types_equal ty2 ty3" by simp
        from eq12 tuple1 tuple2 have len12: "length tys1 = length tys2"
          and all12: "list_all (\<lambda>(t1, t2). types_equal t1 t2) (zip tys1 tys2)"
          using types_equal_Tuple by auto
        from eq23 tuple2 tuple3 have len23: "length tys2 = length tys3"
          and all23: "list_all (\<lambda>(t2, t3). types_equal t2 t3) (zip tys2 tys3)"
          using types_equal_Tuple by auto
        have "list_all (\<lambda>(t1, t3). types_equal t1 t3) (zip tys1 tys3)"
          using list_all_zip3_trans[OF len12 len23 all12 all23] "1.IH"(2) tuple1 tuple2
          by fastforce
        then show ?thesis
          using tuple1 tuple3 len12 len23 types_equal_Tuple by auto
      next
        case (BabTy_Name x11 x12 x13)
        then show ?thesis using "1.prems" tuple2 by simp
      next
        case (BabTy_Bool x2)
        then show ?thesis using "1.prems" tuple2 by simp
      next
        case (BabTy_FiniteInt x31 x32 x33)
        then show ?thesis using "1.prems" tuple2 by simp
      next
        case (BabTy_MathInt x4)
        then show ?thesis using "1.prems" tuple2 by simp
      next
        case (BabTy_MathReal x5)
        then show ?thesis using "1.prems" tuple2 by simp
      next
        case (BabTy_Record x71 x72)
        then show ?thesis using "1.prems" tuple2 by simp
      next
        case (BabTy_Array x81 x82 x83)
        then show ?thesis using "1.prems" tuple2 by simp
      next
        case (BabTy_Meta x)
        thus ?thesis using "1.prems" tuple2 by simp
      qed
    next
      case (BabTy_Name x11 x12 x13)
      then show ?thesis using "1.prems" tuple1 by simp
    next
      case (BabTy_Bool x2)
      then show ?thesis using "1.prems" tuple1 by simp
    next
      case (BabTy_FiniteInt x31 x32 x33)
      then show ?thesis using "1.prems" tuple1 by simp
    next
      case (BabTy_MathInt x4)
      then show ?thesis using "1.prems" tuple1 by simp
    next
      case (BabTy_MathReal x5)
      then show ?thesis using "1.prems" tuple1 by simp
    next
      case (BabTy_Record x71 x72)
      then show ?thesis using "1.prems" tuple1 by simp
    next
      case (BabTy_Array x81 x82 x83)
      then show ?thesis using "1.prems" tuple1 by simp
    next
      case (BabTy_Meta x)
      then show ?thesis using "1.prems" tuple1 by simp
    qed
  next
    case record1: (BabTy_Record loc1 flds1)
    then show ?thesis using "1.prems"
    proof (cases ty2)
      case record2: (BabTy_Record loc2 flds2)
      then show ?thesis using "1.prems" record1
      proof (cases ty3)
        case (BabTy_Record loc3 flds3)
        from "1.prems" record1 record2 have eq12: "types_equal ty1 ty2" by simp
        from "1.prems" record2 BabTy_Record have eq23: "types_equal ty2 ty3" by simp
        from eq12 record1 record2 have len12: "length flds1 = length flds2"
          and all12: "list_all (\<lambda>(f1, f2). fst f1 = fst f2 \<and> types_equal (snd f1) (snd f2)) (zip flds1 flds2)"
          by auto
        from eq23 record2 BabTy_Record have len23: "length flds2 = length flds3"
          and all23: "list_all (\<lambda>(f2, f3). fst f2 = fst f3 \<and> types_equal (snd f2) (snd f3)) (zip flds2 flds3)"
          by auto
        have "list_all (\<lambda>(f1, f3). fst f1 = fst f3 \<and> types_equal (snd f1) (snd f3)) (zip flds1 flds3)"
          using list_all_zip3_trans[OF len12 len23,
                  of "\<lambda>f1 f2. fst f1 = fst f2 \<and> types_equal (snd f1) (snd f2)"]
                all12 all23 "1.IH"(3) record1 record2
          by presburger
        then show ?thesis
          using record1 BabTy_Record len12 len23 by auto
      next
        case (BabTy_Name x11 x12 x13)
        then show ?thesis using "1.prems" record2 by simp
      next
        case (BabTy_Bool x2)
        then show ?thesis using "1.prems" record2 by simp
      next
        case (BabTy_FiniteInt x31 x32 x33)
        then show ?thesis using "1.prems" record2 by simp
      next
        case (BabTy_MathInt x4)
        then show ?thesis using "1.prems" record2 by simp
      next
        case (BabTy_MathReal x5)
        then show ?thesis using "1.prems" record2 by simp
      next
        case (BabTy_Tuple x61 x62)
        then show ?thesis using "1.prems" record2 by simp
      next
        case (BabTy_Array x81 x82 x83)
        then show ?thesis using "1.prems" record2 by simp
      next
        case (BabTy_Meta x)
        then show ?thesis using "1.prems" record2 by simp
      qed
    next
      case (BabTy_Name x11 x12 x13)
      then show ?thesis using "1.prems" record1 by simp
    next
      case (BabTy_Bool x2)
      then show ?thesis using "1.prems" record1 by simp
    next
      case (BabTy_FiniteInt x31 x32 x33)
      then show ?thesis using "1.prems" record1 by simp
    next
      case (BabTy_MathInt x4)
      then show ?thesis using "1.prems" record1 by simp
    next
      case (BabTy_MathReal x5)
      then show ?thesis using "1.prems" record1 by simp
    next
      case (BabTy_Tuple x61 x62)
      then show ?thesis using "1.prems" record1 by simp
    next
      case (BabTy_Array x81 x82 x83)
      then show ?thesis using "1.prems" record1 by simp
    next
      case (BabTy_Meta x)
      then show ?thesis using "1.prems" record1 by simp
    qed
  next
    case array1: (BabTy_Array loc1 elem1 dims1)
    then show ?thesis using "1.prems"
    proof (cases ty2)
      case array2: (BabTy_Array loc2 elem2 dims2)
      then show ?thesis using "1.prems" array1
      proof (cases ty3)
        case array3: (BabTy_Array loc3 elem3 dims3)
        then show ?thesis
          using "1.prems" "1.IH"(4) array1 array2 by auto
      next
        case (BabTy_Name x11 x12 x13)
        then show ?thesis using "1.prems" array2 by simp
      next
        case (BabTy_Bool x2)
        then show ?thesis using "1.prems" array2 by simp
      next
        case (BabTy_FiniteInt x31 x32 x33)
        then show ?thesis using "1.prems" array2 by simp
      next
        case (BabTy_MathInt x4)
        then show ?thesis using "1.prems" array2 by simp
      next
        case (BabTy_MathReal x5)
        then show ?thesis using "1.prems" array2 by simp
      next
        case (BabTy_Tuple x61 x62)
        then show ?thesis using "1.prems" array2 by simp
      next
        case (BabTy_Record x71 x72)
        then show ?thesis using "1.prems" array2 by simp
      next
        case (BabTy_Meta x)
        then show ?thesis using "1.prems" array2 by simp
      qed
    next
      case (BabTy_Name x11 x12 x13)
      then show ?thesis using "1.prems" array1 by simp
    next
      case (BabTy_Bool x2)
      then show ?thesis using "1.prems" array1 by simp
    next
      case (BabTy_FiniteInt x31 x32 x33)
      then show ?thesis using "1.prems" array1 by simp
    next
      case (BabTy_MathInt x4)
      then show ?thesis using "1.prems" array1 by simp
    next
      case (BabTy_MathReal x5)
      then show ?thesis using "1.prems" array1 by simp
    next
      case (BabTy_Tuple x61 x62)
      then show ?thesis using "1.prems" array1 by simp
    next
      case (BabTy_Record x71 x72)
      then show ?thesis using "1.prems" array1 by simp
    next
      case (BabTy_Meta x)
      then show ?thesis using "1.prems" array1 by simp
    qed
  next
    case name1: (BabTy_Name loc1 n1 tyargs1)
    then show ?thesis using "1.prems"
    proof (cases ty2)
      case name2: (BabTy_Name loc2 n2 tyargs2)
      then show ?thesis using "1.prems" name1
      proof (cases ty3)
        case name3: (BabTy_Name loc3 n3 tyargs3)
        from "1.prems" name1 name2 have eq12: "types_equal ty1 ty2" by simp
        from "1.prems" name2 name3 have eq23: "types_equal ty2 ty3" by simp
        from eq12 name1 name2 have n_eq1: "n1 = n2"
          and len12: "length tyargs1 = length tyargs2"
          and all12: "list_all (\<lambda>(t1, t2). types_equal t1 t2) (zip tyargs1 tyargs2)"
          using types_equal_Name by auto
        from eq23 name2 name3 have n_eq2: "n2 = n3"
          and len23: "length tyargs2 = length tyargs3"
          and all23: "list_all (\<lambda>(t2, t3). types_equal t2 t3) (zip tyargs2 tyargs3)"
          using types_equal_Name by auto
        have "list_all (\<lambda>(t1, t3). types_equal t1 t3) (zip tyargs1 tyargs3)"
          using list_all_zip3_trans[OF len12 len23 all12 all23] "1.IH"(1) name1 name2
          by fastforce
        then show ?thesis
          using name1 name3 n_eq1 n_eq2 len12 len23 types_equal_Name by auto
      next
        case (BabTy_Bool x2)
        then show ?thesis using "1.prems" name2 by simp
      next
        case (BabTy_FiniteInt x31 x32 x33)
        then show ?thesis using "1.prems" name2 by simp
      next
        case (BabTy_MathInt x4)
        then show ?thesis using "1.prems" name2 by simp
      next
        case (BabTy_MathReal x5)
        then show ?thesis using "1.prems" name2 by simp
      next
        case (BabTy_Tuple x61 x62)
        then show ?thesis using "1.prems" name2 by simp
      next
        case (BabTy_Record x71 x72)
        then show ?thesis using "1.prems" name2 by simp
      next
        case (BabTy_Array x81 x82 x83)
        then show ?thesis using "1.prems" name2 by simp
      next
        case (BabTy_Meta x)
        then show ?thesis using "1.prems" name2 by simp
      qed
    next
      case (BabTy_Bool x2)
      then show ?thesis using "1.prems" name1 by simp
    next
      case (BabTy_FiniteInt x31 x32 x33)
      then show ?thesis using "1.prems" name1 by simp
    next
      case (BabTy_MathInt x4)
      then show ?thesis using "1.prems" name1 by simp
    next
      case (BabTy_MathReal x5)
      then show ?thesis using "1.prems" name1 by simp
    next
      case (BabTy_Tuple x61 x62)
      then show ?thesis using "1.prems" name1 by simp
    next
      case (BabTy_Record x71 x72)
      then show ?thesis using "1.prems" name1 by simp
    next
      case (BabTy_Array x81 x82 x83)
      then show ?thesis using "1.prems" name1 by simp
    next
      case (BabTy_Meta x)
      then show ?thesis using "1.prems" name1 by simp
    qed
  next
    case (BabTy_Meta n1)
    then show ?thesis using "1.prems" by (cases ty2; cases ty3; auto)
  qed
qed


(* types_equal implies equal sizes *)
lemma types_equal_same_size:
  "types_equal ty1 ty2 \<Longrightarrow> bab_type_size ty1 = bab_type_size ty2"
proof (induction ty1 ty2 rule: types_equal.induct)
  case (1 ty1 ty2)
  then show ?case
  proof (cases ty1)
    case (BabTy_Bool loc1)
    then show ?thesis using "1.prems" by (cases ty2; simp)
  next
    case (BabTy_FiniteInt loc1 s1 b1)
    then show ?thesis using "1.prems" by (cases ty2; simp)
  next
    case (BabTy_MathInt loc1)
    then show ?thesis using "1.prems" by (cases ty2; simp)
  next
    case (BabTy_MathReal loc1)
    then show ?thesis using "1.prems" by (cases ty2; simp)
  next
    case (BabTy_Meta n1)
    then show ?thesis using "1.prems" by (cases ty2; simp)
  next
    case (BabTy_Tuple loc1 tys1)
    then show ?thesis using "1.prems"
    proof (cases ty2)
      case (BabTy_Tuple loc2 tys2)
      from "1.prems" \<open>ty1 = BabTy_Tuple loc1 tys1\<close> BabTy_Tuple
      have len_eq: "length tys1 = length tys2"
        and all_eq: "list_all (\<lambda>(t1, t2). types_equal t1 t2) (zip tys1 tys2)"
        by (simp_all add: types_equal_Tuple del: types_equal.simps)
      have "sum_list (map bab_type_size tys1) = sum_list (map bab_type_size tys2)"
      proof -
        have "\<forall>i < length tys1. bab_type_size (tys1 ! i) = bab_type_size (tys2 ! i)"
        proof (intro allI impI)
          fix i assume "i < length tys1"
          hence "(tys1 ! i, tys2 ! i) \<in> set (zip tys1 tys2)"
            using len_eq in_set_zip by fastforce
          hence "types_equal (tys1 ! i) (tys2 ! i)"
            using all_eq by (meson Ball_set_list_all case_prodD)
          thus "bab_type_size (tys1 ! i) = bab_type_size (tys2 ! i)"
            using "1.IH"(2) \<open>ty1 = BabTy_Tuple loc1 tys1\<close> BabTy_Tuple
                  \<open>(tys1 ! i, tys2 ! i) \<in> set (zip tys1 tys2)\<close> by blast
        qed
        thus ?thesis using len_eq
          by (metis map_equality_iff)
      qed
      then show ?thesis using \<open>ty1 = BabTy_Tuple loc1 tys1\<close> BabTy_Tuple by simp
    qed (use "1.prems" BabTy_Tuple in simp_all)
  next
    case (BabTy_Record loc1 flds1)
    then show ?thesis using "1.prems"
    proof (cases ty2)
      case (BabTy_Record loc2 flds2)
      from "1.prems" \<open>ty1 = BabTy_Record loc1 flds1\<close> BabTy_Record
      have len_eq: "length flds1 = length flds2"
        and all_eq: "list_all (\<lambda>(f1, f2). fst f1 = fst f2 \<and> types_equal (snd f1) (snd f2)) (zip flds1 flds2)"
        by (simp_all add: types_equal_Record del: types_equal.simps)
      have "sum_list (map (bab_type_size \<circ> snd) flds1) = sum_list (map (bab_type_size \<circ> snd) flds2)"
      proof -
        have "\<forall>i < length flds1. bab_type_size (snd (flds1 ! i)) = bab_type_size (snd (flds2 ! i))"
        proof (intro allI impI)
          fix i assume "i < length flds1"
          hence "(flds1 ! i, flds2 ! i) \<in> set (zip flds1 flds2)"
            using len_eq
            using in_set_zip by fastforce 
          hence "types_equal (snd (flds1 ! i)) (snd (flds2 ! i))"
            using all_eq
            by (metis (mono_tags, lifting) case_prodD list.pred_set)
          thus "bab_type_size (snd (flds1 ! i)) = bab_type_size (snd (flds2 ! i))"
            using "1.IH"(3) \<open>ty1 = BabTy_Record loc1 flds1\<close> BabTy_Record
                  \<open>(flds1 ! i, flds2 ! i) \<in> set (zip flds1 flds2)\<close> by blast
        qed
        thus ?thesis using len_eq
          by (smt (verit, ccfv_threshold) comp_apply map_equality_iff)
      qed
      then show ?thesis using \<open>ty1 = BabTy_Record loc1 flds1\<close> BabTy_Record by simp
    qed (use "1.prems" BabTy_Record in simp_all)
  next
    case (BabTy_Array loc1 elem1 dims1)
    then show ?thesis using "1.prems"
    proof (cases ty2)
      case (BabTy_Array loc2 elem2 dims2)
      from "1.prems" \<open>ty1 = BabTy_Array loc1 elem1 dims1\<close> BabTy_Array
      have dims_eq: "dims1 = dims2" and elem_eq: "types_equal elem1 elem2"
        by simp_all
      from "1.IH"(4) \<open>ty1 = BabTy_Array loc1 elem1 dims1\<close> BabTy_Array elem_eq
      have "bab_type_size elem1 = bab_type_size elem2" by blast
      then show ?thesis using \<open>ty1 = BabTy_Array loc1 elem1 dims1\<close> BabTy_Array dims_eq by simp
    qed (use "1.prems" BabTy_Array in simp_all)
  next
    case (BabTy_Name loc1 name1 args1)
    then show ?thesis using "1.prems"
    proof (cases ty2)
      case (BabTy_Name loc2 name2 args2)
      from "1.prems" \<open>ty1 = BabTy_Name loc1 name1 args1\<close> BabTy_Name
      have name_eq: "name1 = name2" and len_eq: "length args1 = length args2"
        and all_eq: "list_all (\<lambda>(t1, t2). types_equal t1 t2) (zip args1 args2)"
        by (simp_all add: types_equal_Name del: types_equal.simps)
      have "sum_list (map bab_type_size args1) = sum_list (map bab_type_size args2)"
      proof -
        have "\<forall>i < length args1. bab_type_size (args1 ! i) = bab_type_size (args2 ! i)"
        proof (intro allI impI)
          fix i assume "i < length args1"
          hence "(args1 ! i, args2 ! i) \<in> set (zip args1 args2)"
            using len_eq
            by (metis length_zip min_less_iff_conj nth_mem nth_zip)
          hence "types_equal (args1 ! i) (args2 ! i)"
            using all_eq
            by (meson Ball_set_list_all case_prodD)
          thus "bab_type_size (args1 ! i) = bab_type_size (args2 ! i)"
            using "1.IH"(1) \<open>ty1 = BabTy_Name loc1 name1 args1\<close> BabTy_Name
                  \<open>(args1 ! i, args2 ! i) \<in> set (zip args1 args2)\<close> by blast
        qed
        thus ?thesis using len_eq
          by (metis map_equality_iff)
      qed
      then show ?thesis using \<open>ty1 = BabTy_Name loc1 name1 args1\<close> BabTy_Name by simp
    qed (use "1.prems" BabTy_Name in simp_all)
  qed
qed


end
