theory ConstFold
  imports TypeError "../core/CoreFreeVars"
      "HOL-Library.Char_ord" "HOL-Library.List_Lexorder"
begin

(* Compile-time evaluation of global constants.

   The elaborator evaluates each (non-ghost) global-constant initializer to a CoreValue
   at compile time. This is similar to how C handles global constants (in C, global
   initializers are evaluated to data bytes at compile time -- unlike C++, where global
   constructors are run before "main" at program startup).

   Instead of directly calling interp_term (the actual Core interpreter), the
   elaborator defines its own eval_const and fold_const functions, which are then
   proved equivalent to interp_term (see theorem fold_const_is_core_evaluation in
   ConstFoldCorrect.thy). The advantages of doing it this way are that no fuel
   is needed, and the full InterpState is not needed (we just need a map from
   global variable names to values).
*)


(* ========================================================================== *)
(* Compile-time constant terms *)
(* ========================================================================== *)

(* A "compile-time constant term" is one that doesn't include function calls, quantifiers
   or CoreTm_Default.

   The rule against function calls is there to simplify the elaborator, which doesn't want
   to have to worry about calling functions at compile time. The other two - quantifiers
   and default - can't occur in legal non-ghost consts anyway, so these are not "real"
   restrictions.

   Terms that satisfy is_constant_term are exactly the ones for which eval_const
   and interp_term agree. *)

fun is_constant_term :: "CoreTerm \<Rightarrow> bool" where
  "is_constant_term (CoreTm_LitBool _) = True"
| "is_constant_term (CoreTm_LitInt _) = True"
| "is_constant_term (CoreTm_LitArray _ tms) = list_all is_constant_term tms"
| "is_constant_term (CoreTm_Var _) = True"
| "is_constant_term (CoreTm_Cast _ tm) = is_constant_term tm"
| "is_constant_term (CoreTm_Unop _ tm) = is_constant_term tm"
| "is_constant_term (CoreTm_Binop _ lhs rhs) =
    (is_constant_term lhs \<and> is_constant_term rhs)"
| "is_constant_term (CoreTm_Let _ rhs body) =
    (is_constant_term rhs \<and> is_constant_term body)"
| "is_constant_term (CoreTm_Quantifier _ _ _ _) = False"
| "is_constant_term (CoreTm_FunctionCall _ _ _) = False"
| "is_constant_term (CoreTm_VariantCtor _ _ payload) = is_constant_term payload"
| "is_constant_term (CoreTm_Record flds) =
    list_all (is_constant_term \<circ> snd) flds"
| "is_constant_term (CoreTm_RecordProj tm _) = is_constant_term tm"
| "is_constant_term (CoreTm_VariantProj tm _) = is_constant_term tm"
| "is_constant_term (CoreTm_ArrayProj arr idxs) =
    (is_constant_term arr \<and> list_all is_constant_term idxs)"
| "is_constant_term (CoreTm_Match scrut arms) =
    (is_constant_term scrut \<and> list_all (is_constant_term \<circ> snd) arms)"
| "is_constant_term (CoreTm_Sizeof tm) = is_constant_term tm"
| "is_constant_term (CoreTm_Allocated tm) = is_constant_term tm"
| "is_constant_term (CoreTm_Old tm) = is_constant_term tm"
| "is_constant_term (CoreTm_Default _) = False"


(* ========================================================================== *)
(* Ground embedded types *)
(* ========================================================================== *)

(* In addition to the is_constant_term restrictions, the elaborator also can't evaluate
   constants that mention an unresolved abstract type explicitly anywhere inside the term.
  
   This is not because eval_const or interp_term would fail on such terms (they would
   succeed), it is because value_has_type would not be able to type such terms (e.g.,
   the typing rule for CV_Variant rejects free type variables in the type arguments -- see
   also value_has_type_ground).

   This rule is slightly annoying, but because of the way we have defined value_has_type,
   it seems unavoidable. But in practice, it has limited impact - it mainly just excludes
   constants like "[]" or "Nothing" (empty array or empty data-constructor of some abstract
   type). (A constant like "Just(c)", where c has an abstract type, couldn't be constructed -- 
   you wouldn't have a value "c" available.) So maybe it's not too bad. In any case, a
   workaround is to make a function returning the value you want, instead of declaring it as
   a const.
*)

fun term_types_ground :: "CoreTerm \<Rightarrow> bool" where
  "term_types_ground (CoreTm_LitBool _) = True"
| "term_types_ground (CoreTm_LitInt _) = True"
| "term_types_ground (CoreTm_LitArray elemTy tms) =
    (type_tyvars elemTy = {} \<and> list_all term_types_ground tms)"
| "term_types_ground (CoreTm_Var _) = True"
| "term_types_ground (CoreTm_Cast ty tm) =
    (type_tyvars ty = {} \<and> term_types_ground tm)"
| "term_types_ground (CoreTm_Unop _ tm) = term_types_ground tm"
| "term_types_ground (CoreTm_Binop _ lhs rhs) =
    (term_types_ground lhs \<and> term_types_ground rhs)"
| "term_types_ground (CoreTm_Let _ rhs body) =
    (term_types_ground rhs \<and> term_types_ground body)"
| "term_types_ground (CoreTm_Quantifier _ _ varTy body) =
    (type_tyvars varTy = {} \<and> term_types_ground body)"
| "term_types_ground (CoreTm_FunctionCall _ tyArgs tmArgs) =
    (list_all (\<lambda>t. type_tyvars t = {}) tyArgs \<and> list_all term_types_ground tmArgs)"
| "term_types_ground (CoreTm_VariantCtor _ tyArgs payload) =
    (list_all (\<lambda>t. type_tyvars t = {}) tyArgs \<and> term_types_ground payload)"
| "term_types_ground (CoreTm_Record flds) = list_all (term_types_ground \<circ> snd) flds"
| "term_types_ground (CoreTm_RecordProj tm _) = term_types_ground tm"
| "term_types_ground (CoreTm_VariantProj tm _) = term_types_ground tm"
| "term_types_ground (CoreTm_ArrayProj arr idxs) =
    (term_types_ground arr \<and> list_all term_types_ground idxs)"
| "term_types_ground (CoreTm_Match scrut arms) =
    (term_types_ground scrut \<and> list_all (term_types_ground \<circ> snd) arms)"
| "term_types_ground (CoreTm_Sizeof tm) = term_types_ground tm"
| "term_types_ground (CoreTm_Allocated tm) = term_types_ground tm"
| "term_types_ground (CoreTm_Old tm) = term_types_ground tm"
| "term_types_ground (CoreTm_Default ty) = (type_tyvars ty = {})"


(* ========================================================================== *)
(* Size helpers for the termination proof *)
(* ========================================================================== *)

(* An arm body is bounded by the size of the arm list. *)
lemma size_snd_in_arms_le:
  assumes "rhs \<in> snd ` set (arms :: (CorePattern \<times> CoreTerm) list)"
  shows "size rhs \<le> size_list (size_prod (\<lambda>_. 0) size) arms"
proof -
  from assms obtain p where p_in: "(p, rhs) \<in> set arms" by auto
  have "size_prod (\<lambda>_. 0) size (p, rhs) \<le> size_list (size_prod (\<lambda>_. 0) size) arms"
    using p_in by (simp add: size_list_estimation')
  thus ?thesis by simp
qed

(* The record-field terms are bounded by the size of the field list. *)
lemma size_list_map_snd_le:
  "size_list (size \<circ> snd) (flds :: (string \<times> CoreTerm) list)
     \<le> size_list (size_prod (\<lambda>_. 0) size) flds"
  by (induction flds) auto


(* ========================================================================== *)
(* eval_const *)
(* ========================================================================== *)

(* Evaluate a compile-time constant term (or list of terms) to a CoreValue.

   Parameters are a variable environment (mapping from variable names to CoreValues) and
   the term(s) to be evaluated. Result is either an InterpError or the evaluated CoreValue.
   (No fuel is required; compile-time evaluation always terminates.)

   On terms that can't be evaluated at compile-time, this returns Inl TypeError.

   The implementation doesn't call interp_term directly, but it does re-use helpers from
   the interpreter, such as eval_binop.

   eval_const is (roughly speaking) equivalent to interp_term for compile-time constant
   terms; the precise statement is `eval_const_interp_agree` in ConstFoldCorrect.thy.
*)

function eval_const :: "(string, CoreValue) fmap \<Rightarrow> CoreTerm \<Rightarrow> InterpError + CoreValue"
  and eval_const_list :: "(string, CoreValue) fmap \<Rightarrow> CoreTerm list \<Rightarrow> InterpError + CoreValue list"
where
  (* Literals *)
  "eval_const vals (CoreTm_LitBool b) = Inr (CV_Bool b)"
| "eval_const vals (CoreTm_LitInt i) =
    (case get_type_for_int i of
      Some (sign, bits) \<Rightarrow> Inr (CV_FiniteInt sign bits i)
    | None \<Rightarrow> Inl TypeError)"
| "eval_const vals (CoreTm_LitArray _ tms) =
    (case eval_const_list vals tms of
      Inl err \<Rightarrow> Inl err
    | Inr vs \<Rightarrow> Inr (make_1d_array vs))"

  (* Variable lookup *)
| "eval_const vals (CoreTm_Var varName) =
    (case fmlookup vals varName of
      Some v \<Rightarrow> Inr v
    | None \<Rightarrow> Inl TypeError)"  \<comment> \<open>name not in scope\<close>

  (* Cast *)
| "eval_const vals (CoreTm_Cast targetTy tm) =
    (case eval_const vals tm of
      Inr (CV_FiniteInt _ _ i) \<Rightarrow>
        (case targetTy of
          CoreTy_FiniteInt sign bits \<Rightarrow>
            if int_fits sign bits i
            then Inr (CV_FiniteInt sign bits i)
            else Inl RuntimeError  \<comment> \<open>overflow\<close>
        | _ \<Rightarrow> Inl TypeError)  \<comment> \<open>cast to non-finite-integer type\<close>
    | Inr _ \<Rightarrow> Inl TypeError   \<comment> \<open>cast from non-finite-integer type\<close>
    | Inl err \<Rightarrow> Inl err)"

  (* Unary operator *)
| "eval_const vals (CoreTm_Unop op tm) =
    (case eval_const vals tm of
      Inl err \<Rightarrow> Inl err
    | Inr val \<Rightarrow> eval_unop op val)"

  (* Binary operator *)
| "eval_const vals (CoreTm_Binop op lhsTm rhsTm) =
    (case eval_const vals lhsTm of
      Inl err \<Rightarrow> Inl err
    | Inr lhsVal \<Rightarrow>
        (case eval_const vals rhsTm of
          Inl err \<Rightarrow> Inl err
        | Inr rhsVal \<Rightarrow> eval_binop op lhsVal rhsVal))"

  (* Let *)
| "eval_const vals (CoreTm_Let varName rhsTm bodyTm) =
    (case eval_const vals rhsTm of
      Inl err \<Rightarrow> Inl err
    | Inr rhsVal \<Rightarrow> eval_const (fmupd varName rhsVal vals) bodyTm)"

  (* Function call - excluded from constant terms *)
| "eval_const vals (CoreTm_FunctionCall _ _ _) = Inl TypeError"

  (* Variant construction *)
| "eval_const vals (CoreTm_VariantCtor ctorName _ payloadTm) =
    (case eval_const vals payloadTm of
      Inl err \<Rightarrow> Inl err
    | Inr payloadValue \<Rightarrow> Inr (CV_Variant ctorName payloadValue))"

  (* Record construction *)
| "eval_const vals (CoreTm_Record nameTermPairs) =
    (case eval_const_list vals (map snd nameTermPairs) of
      Inl err \<Rightarrow> Inl err
    | Inr vs \<Rightarrow> Inr (CV_Record (zip (map fst nameTermPairs) vs)))"

  (* Record projection *)
| "eval_const vals (CoreTm_RecordProj tm fldName) =
    (case eval_const vals tm of
      Inr (CV_Record nameValPairs) \<Rightarrow>
        (case map_of nameValPairs fldName of
          Some v \<Rightarrow> Inr v
        | None \<Rightarrow> Inl TypeError)
    | Inr _ \<Rightarrow> Inl TypeError
    | Inl err \<Rightarrow> Inl err)"

  (* Variant projection (get payload; ctor name must match) *)
| "eval_const vals (CoreTm_VariantProj tm expectedCtorName) =
    (case eval_const vals tm of
      Inr (CV_Variant actualCtorName payload) \<Rightarrow>
        (if actualCtorName = expectedCtorName then Inr payload
        else Inl RuntimeError)  \<comment> \<open>constructor name mismatch\<close>
    | Inr _ \<Rightarrow> Inl TypeError  \<comment> \<open>not a variant value\<close>
    | Inl err \<Rightarrow> Inl err)"

  (* Array projection (indexing) *)
| "eval_const vals (CoreTm_ArrayProj arrayTm idxTms) =
    (case eval_const vals arrayTm of
      Inr (CV_Array _ elementMap) \<Rightarrow>
        (case eval_const_list vals idxTms of
          Inr indexVals \<Rightarrow>
            (case interpret_index_vals indexVals of
              Inr indices \<Rightarrow>
                (case fmlookup elementMap indices of
                  Some result \<Rightarrow> Inr result
                | None \<Rightarrow> Inl RuntimeError)  \<comment> \<open>array index out of bounds\<close>
            | Inl err \<Rightarrow> Inl err)  \<comment> \<open>index terms not of type u64\<close>
        | Inl err \<Rightarrow> Inl err)  \<comment> \<open>error evaluating index terms\<close>
    | Inr _ \<Rightarrow> Inl TypeError  \<comment> \<open>not an array value\<close>
    | Inl err \<Rightarrow> Inl err)"  \<comment> \<open>error evaluating array term\<close>

  (* Pattern match *)
| "eval_const vals (CoreTm_Match scrutTm arms) =
    (case eval_const vals scrutTm of
      Inr scrutVal \<Rightarrow>
        (case find_matching_arm scrutVal arms of
          Inr armTm \<Rightarrow> eval_const vals armTm
        | Inl err \<Rightarrow> Inl err)
    | Inl err \<Rightarrow> Inl err)"

  (* Sizeof *)
| "eval_const vals (CoreTm_Sizeof tm) =
    (case eval_const vals tm of
      Inr (CV_Array sizes _) \<Rightarrow> Inr (array_size_to_value sizes)
    | Inr _ \<Rightarrow> Inl TypeError
    | Inl err \<Rightarrow> Inl err)"

  (* Quantifier, Allocated, Old, Default - not constant terms (and interp_term
     also rejects Quantifier/Allocated/Old with TypeError) *)
| "eval_const vals (CoreTm_Quantifier _ _ _ _) = Inl TypeError"
| "eval_const vals (CoreTm_Allocated _) = Inl TypeError"
| "eval_const vals (CoreTm_Old _) = Inl TypeError"
| "eval_const vals (CoreTm_Default _) = Inl TypeError"

  (* Evaluate a list of terms *)
| "eval_const_list vals [] = Inr []"
| "eval_const_list vals (tm # tms) =
    (case eval_const vals tm of
      Inl err \<Rightarrow> Inl err
    | Inr v \<Rightarrow>
        (case eval_const_list vals tms of
          Inl err \<Rightarrow> Inl err
        | Inr vs \<Rightarrow> Inr (v # vs)))"

  by pat_completeness auto

termination eval_const
  by (relation "measure (case_sum (\<lambda>(vals, tm). size tm)
                                  (\<lambda>(vals, tms). size_list size tms))")
     (auto simp add: less_Suc_eq_le size_list_map_snd_le
           dest!: find_matching_arm_in_arms find_matching_arm_in_arms[OF sym]
           intro: order_trans[OF size_snd_in_arms_le])


(* ========================================================================== *)
(* fold_const *)
(* ========================================================================== *)

(* Fold a constant initializer term to its value. This is the wrapper around eval_const
   used by the elaborator.

   First, it does some error checks:

    - If the term refers to some constant `c` whose value is not visible (because
      it was exported abstractly by another module), it reports TyErr_ConstValueNotVisible.

    - If the term fails the term_types_ground check, it reports TyErr_ConstAbstractType.

   Then, if the checks succeed, it calls eval_const. (This may itself return errors, e.g.
   if there was an overflow or division by zero etc. while evaluating the constant.)
*)
definition fold_const ::
  "(string, CoreValue) fmap \<Rightarrow> Location \<Rightarrow> CoreTerm \<Rightarrow> TypeError list + CoreValue" where
  "fold_const globalVals loc tm =
    (let missing = core_term_free_vars tm |-| fmdom globalVals
     in if missing \<noteq> {||}
        then Inl (map (TyErr_ConstValueNotVisible loc) (sorted_list_of_fset missing))
        else if \<not> term_types_ground tm
        then Inl [TyErr_ConstAbstractType loc]
        else case eval_const globalVals tm of
               Inl err \<Rightarrow> Inl [TyErr_ConstEvalError loc err]
             | Inr v \<Rightarrow> Inr v)"

end
