theory TypeProps
  imports "../base/BabSyntax"
begin

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

(* Finite integer types are ground *)
lemma finite_integer_type_is_ground:
  "is_finite_integer_type ty \<Longrightarrow> is_ground ty"
  by (cases ty) auto

(* Check if an array dimension is resolved (not BabDim_Fixed) *)
fun is_resolved_dimension :: "BabDimension \<Rightarrow> bool" where
  "is_resolved_dimension (BabDim_Fixed _) = False"
| "is_resolved_dimension _ = True"

(* Check if a type is a runtime-compatible type (no MathInt/MathReal) *)
(* Note: Metavariables are considered runtime types, but metavariables should theoretically
   be removed anyway, post type inference. *)
fun is_runtime_type :: "BabType \<Rightarrow> bool" where
  "is_runtime_type (BabTy_MathInt _) = False"
| "is_runtime_type (BabTy_MathReal _) = False"
| "is_runtime_type (BabTy_Name _ _ tyArgs) = list_all is_runtime_type tyArgs"
| "is_runtime_type (BabTy_Tuple _ tys) = list_all is_runtime_type tys"
| "is_runtime_type (BabTy_Record _ flds) = list_all (is_runtime_type \<circ> snd) flds"
| "is_runtime_type (BabTy_Array _ ty _) = is_runtime_type ty"
| "is_runtime_type _ = True"

(* Signed integer types are integer types *)
lemma signed_integer_type_is_integer_type:
  "is_signed_integer_type ty \<Longrightarrow> is_integer_type ty"
  by (cases ty) auto

(* Finite integer types are integer types *)
lemma finite_integer_type_is_integer_type:
  "is_finite_integer_type ty \<Longrightarrow> is_integer_type ty"
  by (cases ty) auto

(* Integer types are either FiniteInt or MathInt *)
lemma is_integer_type_cases:
  assumes "is_integer_type ty"
  obtains (FiniteInt) loc sign bits where "ty = BabTy_FiniteInt loc sign bits"
        | (MathInt) loc where "ty = BabTy_MathInt loc"
  using assms by (cases ty) auto

(* Substituting runtime types preserves runtime-ness *)
lemma is_runtime_type_substitute_bab_type:
  assumes "is_runtime_type ty"
      and "\<forall>ty' \<in> fmran' subst. is_runtime_type ty'"
  shows "is_runtime_type (substitute_bab_type subst ty)"
using assms proof (induction ty rule: is_runtime_type.induct)
  (* BabTy_Name case - need to handle both variable substitution and recursive args *)
  case (3 loc name tyArgs)
  show ?case
  proof (cases tyArgs)
    case Nil
    (* tyArgs = [], so this might be a type variable that gets substituted *)
    then show ?thesis
    proof (cases "fmlookup subst name")
      case None
      with Nil show ?thesis by simp
    next
      case (Some substTy)
      with "3.prems"(2) have "is_runtime_type substTy"
        by (simp add: fmran'I)
      with Some Nil show ?thesis by simp
    qed
  next
    case (Cons a list)
    (* tyArgs is non-empty, so not substituted (just recurse on args) *)
    from "3.prems"(1) Cons have args_rt: "list_all is_runtime_type (a # list)"
      by simp
    have "\<forall>t \<in> set (a # list). is_runtime_type (substitute_bab_type subst t)"
    proof
      fix t assume "t \<in> set (a # list)"
      with args_rt have "is_runtime_type t"
        using split_list by fastforce
      with "3.IH" "3.prems"(2) Cons \<open>t \<in> set (a # list)\<close> show "is_runtime_type (substitute_bab_type subst t)"
        by auto
    qed
    hence "list_all is_runtime_type (map (substitute_bab_type subst) (a # list))"
      by (simp add: list_all_iff)
    with Cons show ?thesis by simp
  qed
next
  (* Tuple case *)
  case (4 loc tys)
  from "4.prems"(1) have "list_all is_runtime_type tys" by simp
  hence "list_all is_runtime_type (map (substitute_bab_type subst) tys)"
    using "4.IH" "4.prems"(2) by (auto simp: list_all_iff)
  then show ?case by simp
next
  (* Record case *)
  case (5 loc flds)
  from "5.prems"(1) have "list_all (is_runtime_type \<circ> snd) flds" by simp
  hence "list_all (is_runtime_type \<circ> snd) (map (\<lambda>(name, ty). (name, substitute_bab_type subst ty)) flds)"
    using "5.IH" "5.prems"(2) by (auto simp: list_all_iff)
  then show ?case by simp
next
  (* Array case *)
  case (6 loc ty dims)
  from "6.prems"(1) have "is_runtime_type ty" by simp
  with "6.IH" "6.prems"(2) have "is_runtime_type (substitute_bab_type subst ty)" by simp
  then show ?case by simp
qed simp_all

end
