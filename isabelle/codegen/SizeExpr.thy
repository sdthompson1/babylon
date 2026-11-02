theory SizeExpr
  imports DatatypeAcyclic Babylon.MiniCSemantics
begin

(* ========================================================================== *)
(* MiniC size and offset expressions (minic/DESIGN.md, section 3.2)           *)
(* ========================================================================== *)

(* size_expr builds, from a Core type, the uint64_t MiniC expression for its
   size: the expression of section 3.2 of the design, with ME_PtrSize for the
   pointer size and a caller-supplied map tv from type-variable names to
   MiniC expressions (the generator decides how its size parameters are
   named). Sums, products and maxima of two literals are folded, so a ground
   type without pointers becomes one literal; ME_PtrSize stays symbolic.

   The evaluation lemma, size_expr_eval: if every type-variable expression
   evaluates to the uint64_t value of the assignment sz, and the type "fits"
   (size_fits: the size of the type and of every component the expression
   computes is below 2^64), then size_expr evaluates, with no undefined
   behaviour, to exactly type_size. size_fits is slightly stronger than
   type_size < 2^64: a fixed array with zero elements has size 0 whatever its
   element type, but the generated expression still multiplies the element
   size by 0, so the element size must fit too. For records and datatypes the
   components are bounded by the whole and nothing extra is required.
   size_fits is what the static checker (SizeBound.thy) checks. *)


section \<open>uint64_t arithmetic\<close>

(* 2^64, kept opaque so that the simplifier does not turn it into a numeral
   (which would stop lemmas about it from matching). *)
definition u64_max :: nat where
  "u64_max = 2 ^ 64"

lemma u64_max_pos [simp]: "0 < u64_max"
  by (simp add: u64_max_def)

lemma u64_max_gt_8: "8 < u64_max"
  by (simp add: u64_max_def)

lemma int_fits_u64: "int_fits Unsigned IntBits_64 i \<longleftrightarrow> 0 \<le> i \<and> i < int u64_max"
  unfolding int_fits_unsigned u64_max_def by simp

(* Simp unfolds int_fits to int_in_range (with 2^64 - 1 as a numeral), which
   hides the structure; the lemmas below block that. *)
lemmas int_fits_simps = int_fits.simps

abbreviation u64_lit :: "nat \<Rightarrow> MExpr" where
  "u64_lit n \<equiv> ME_Int Unsigned IntBits_64 (int n)"

(* The value of a uint64_t literal expression, if it is one. *)
fun u64_lit_of :: "MExpr \<Rightarrow> nat option" where
  "u64_lit_of (ME_Int Unsigned IntBits_64 i) = (if 0 \<le> i then Some (nat i) else None)"
| "u64_lit_of _ = None"

lemma u64_lit_of_Some: "u64_lit_of e = Some n \<Longrightarrow> e = u64_lit n"
  by (cases e rule: u64_lit_of.cases) (auto split: if_splits)

(* A binary operator on uint64_t expressions, folded when both operands are
   literals. f is the mathematical operation op computes. *)
definition e_fold2 :: "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> CBinop \<Rightarrow> MExpr \<Rightarrow> MExpr \<Rightarrow> MExpr" where
  "e_fold2 f op a b =
    (case (u64_lit_of a, u64_lit_of b) of
       (Some x, Some y) \<Rightarrow> u64_lit (f x y)
     | _ \<Rightarrow> ME_Binop op a b)"

abbreviation e_add :: "MExpr \<Rightarrow> MExpr \<Rightarrow> MExpr" where "e_add \<equiv> e_fold2 (+) CB_Add"
abbreviation e_mul :: "MExpr \<Rightarrow> MExpr \<Rightarrow> MExpr" where "e_mul \<equiv> e_fold2 (*) CB_Mul"
abbreviation e_max :: "MExpr \<Rightarrow> MExpr \<Rightarrow> MExpr" where "e_max \<equiv> e_fold2 max CB_Max"

lemma eval_u64_lit:
  "eval_expr enc st (u64_lit n) = (if n < u64_max then Some (MV_U64 (int n)) else None)"
  unfolding eval_expr.simps(1) int_fits_u64 by simp

lemma eval_u64_lit_Some [simp]:
  "n < u64_max \<Longrightarrow> eval_expr enc st (u64_lit n) = Some (MV_U64 (int n))"
  unfolding eval_u64_lit by simp

lemma eval_binop_u64_add:
  "eval_binop CB_Add (MV_U64 x) (MV_U64 y)
   = (if 0 \<le> x + y \<and> x + y < int u64_max then Some (MV_U64 (x + y)) else None)"
  by (simp add: eval_binop_def eval_cmp_binop_def eval_int_binop_def int_fits_u64 del: int_fits_simps)

lemma eval_binop_u64_mul:
  "eval_binop CB_Mul (MV_U64 x) (MV_U64 y)
   = (if 0 \<le> x * y \<and> x * y < int u64_max then Some (MV_U64 (x * y)) else None)"
  by (simp add: eval_binop_def eval_cmp_binop_def eval_int_binop_def int_fits_u64 del: int_fits_simps)

lemma eval_binop_u64_max:
  "eval_binop CB_Max (MV_U64 x) (MV_U64 y)
   = (if 0 \<le> max x y \<and> max x y < int u64_max then Some (MV_U64 (max x y)) else None)"
  by (simp add: eval_binop_def eval_cmp_binop_def eval_int_binop_def int_fits_u64 del: int_fits_simps)

(* The generic evaluation lemma for a folded operator. *)
lemma eval_e_fold2:
  assumes a: "eval_expr enc st a = Some (MV_U64 x)"
    and b: "eval_expr enc st b = Some (MV_U64 y)"
    and op: "eval_binop op (MV_U64 x) (MV_U64 y) = Some (MV_U64 r)"
    and fits: "0 \<le> r" "r < int u64_max"
    and fr: "int (f (nat x) (nat y)) = r"
  shows "eval_expr enc st (e_fold2 f op a b) = Some (MV_U64 r)"
proof (cases "u64_lit_of a")
  case None
  then show ?thesis using a b op by (simp add: e_fold2_def)
next
  case (Some x')
  hence a': "a = u64_lit x'" by (rule u64_lit_of_Some)
  with a have xx: "int x' = x" by (simp add: eval_u64_lit split: if_splits)
  show ?thesis
  proof (cases "u64_lit_of b")
    case None
    then show ?thesis using a b op Some by (simp add: e_fold2_def)
  next
    case (Some y')
    hence "b = u64_lit y'" by (rule u64_lit_of_Some)
    with b have yy: "int y' = y" by (simp add: eval_u64_lit split: if_splits)
    have "e_fold2 f op a b = u64_lit (f x' y')"
      using \<open>u64_lit_of a = Some x'\<close> Some by (simp add: e_fold2_def)
    moreover have "int (f x' y') = r" using fr xx[symmetric] yy[symmetric] by simp
    ultimately show ?thesis using fits
      unfolding \<open>e_fold2 f op a b = u64_lit (f x' y')\<close> eval_expr.simps(1) int_fits_u64 by simp
  qed
qed

lemma eval_e_add_int:
  assumes "eval_expr enc st a = Some (MV_U64 x)" and "eval_expr enc st b = Some (MV_U64 y)"
    and "0 \<le> x" and "0 \<le> y" and "x + y < int u64_max"
  shows "eval_expr enc st (e_add a b) = Some (MV_U64 (x + y))"
proof (rule eval_e_fold2[OF assms(1,2)])
  have "0 \<le> x + y" using assms(3,4) by linarith
  thus "eval_binop CB_Add (MV_U64 x) (MV_U64 y) = Some (MV_U64 (x + y))"
    and "0 \<le> x + y" using assms(5) by (simp_all add: eval_binop_u64_add)
  show "x + y < int u64_max" by (rule assms(5))
  show "int (nat x + nat y) = x + y" using assms(3,4) by simp
qed

lemma eval_e_mul_int:
  assumes "eval_expr enc st a = Some (MV_U64 x)" and "eval_expr enc st b = Some (MV_U64 y)"
    and "0 \<le> x" and "0 \<le> y" and "x * y < int u64_max"
  shows "eval_expr enc st (e_mul a b) = Some (MV_U64 (x * y))"
proof (rule eval_e_fold2[OF assms(1,2)])
  have nn: "0 \<le> x * y" using assms(3,4) by (rule mult_nonneg_nonneg)
  thus "eval_binop CB_Mul (MV_U64 x) (MV_U64 y) = Some (MV_U64 (x * y))"
    and "0 \<le> x * y" using assms(5) by (simp_all add: eval_binop_u64_mul)
  show "x * y < int u64_max" by (rule assms(5))
  show "int (nat x * nat y) = x * y" using assms(3) nn by (simp add: nat_mult_distrib[symmetric])
qed

lemma eval_e_max_int:
  assumes "eval_expr enc st a = Some (MV_U64 x)" and "eval_expr enc st b = Some (MV_U64 y)"
    and "0 \<le> x" and "0 \<le> y" and "x < int u64_max" and "y < int u64_max"
  shows "eval_expr enc st (e_max a b) = Some (MV_U64 (max x y))"
proof (rule eval_e_fold2[OF assms(1,2)])
  show "eval_binop CB_Max (MV_U64 x) (MV_U64 y) = Some (MV_U64 (max x y))"
    and "0 \<le> max x y" and "max x y < int u64_max"
    using assms(3-6) by (simp_all add: eval_binop_u64_max)
  show "int (max (nat x) (nat y)) = max x y" using assms(3,4) by (simp add: of_nat_max)
qed

lemma eval_e_add:
  assumes "eval_expr enc st a = Some (MV_U64 (int x))" and "eval_expr enc st b = Some (MV_U64 (int y))"
    and "x + y < u64_max"
  shows "eval_expr enc st (e_add a b) = Some (MV_U64 (int (x + y)))"
proof -
  have "int x + int y < int u64_max" using assms(3) by (simp flip: of_nat_add)
  from eval_e_add_int[OF assms(1,2) _ _ this] show ?thesis by simp
qed

lemma eval_e_mul:
  assumes "eval_expr enc st a = Some (MV_U64 (int x))" and "eval_expr enc st b = Some (MV_U64 (int y))"
    and "x * y < u64_max"
  shows "eval_expr enc st (e_mul a b) = Some (MV_U64 (int (x * y)))"
proof -
  have "int x * int y < int u64_max" using assms(3) by (simp flip: of_nat_mult)
  from eval_e_mul_int[OF assms(1,2) _ _ this] show ?thesis by simp
qed

lemma eval_e_max:
  assumes "eval_expr enc st a = Some (MV_U64 (int x))" and "eval_expr enc st b = Some (MV_U64 (int y))"
    and "x < u64_max" and "y < u64_max"
  shows "eval_expr enc st (e_max a b) = Some (MV_U64 (int (max x y)))"
proof -
  have "int x < int u64_max" and "int y < int u64_max" using assms(3,4) by simp_all
  from eval_e_max_int[OF assms(1,2) _ _ this] show ?thesis by (simp add: of_nat_max)
qed

(* Sums and maxima of lists of expressions. *)
lemma eval_foldr_add:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> eval_expr enc st (g x) = Some (MV_U64 (int (f x)))"
    and "sum_list (map f xs) < u64_max"
  shows "eval_expr enc st (foldr e_add (map g xs) (u64_lit 0)) = Some (MV_U64 (int (sum_list (map f xs))))"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have ih: "eval_expr enc st (foldr e_add (map g xs) (u64_lit 0)) = Some (MV_U64 (int (sum_list (map f xs))))"
    using Cons.prems by (intro Cons.IH) auto
  have "eval_expr enc st (e_add (g x) (foldr e_add (map g xs) (u64_lit 0)))
        = Some (MV_U64 (int (f x + sum_list (map f xs))))"
    using Cons.prems ih by (intro eval_e_add) simp_all
  thus ?case by simp
qed

lemma eval_foldr_max:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> eval_expr enc st (g x) = Some (MV_U64 (int (f x)))"
    and "max_list (map f xs) < u64_max"
  shows "eval_expr enc st (foldr e_max (map g xs) (u64_lit 0)) = Some (MV_U64 (int (max_list (map f xs))))"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have ih: "eval_expr enc st (foldr e_max (map g xs) (u64_lit 0)) = Some (MV_U64 (int (max_list (map f xs))))"
    using Cons.prems by (intro Cons.IH) auto
  have "eval_expr enc st (e_max (g x) (foldr e_max (map g xs) (u64_lit 0)))
        = Some (MV_U64 (int (max (f x) (max_list (map f xs)))))"
    using Cons.prems ih by (intro eval_e_max) simp_all
  thus ?case by simp
qed


section \<open>Size expressions\<close>

(* The expression for each type variable of a list, given the expressions of
   the corresponding type arguments (0 for a variable not in the list; cf.
   tyvar_sizes). *)
definition tyvar_exprs :: "string list \<Rightarrow> MExpr list \<Rightarrow> string \<Rightarrow> MExpr" where
  "tyvar_exprs tyvars es v = (case map_of (zip tyvars es) v of Some e \<Rightarrow> e | None \<Rightarrow> u64_lit 0)"

(* The fuelled size expression, mirroring tsz clause by clause. *)
fun tsz_expr :: "nat \<Rightarrow> CoreTyEnv \<Rightarrow> (string \<Rightarrow> MExpr) \<Rightarrow> CoreType \<Rightarrow> MExpr" where
  "tsz_expr fuel env tv (CoreTy_Datatype dtName args) =
    (if fuel = 0 then u64_lit 0
     else e_add (u64_lit (tag_size env dtName))
            (foldr e_max
               (map (\<lambda>ctor.
                  case fmlookup (TE_DataCtors env) ctor of
                    Some (_, tyvars, payloadTy) \<Rightarrow>
                      tsz_expr (fuel - 1) env
                          (tyvar_exprs tyvars (map (tsz_expr fuel env tv) args))
                          payloadTy
                  | None \<Rightarrow> u64_lit 0)
                (dt_ctors env dtName))
               (u64_lit 0)))"
| "tsz_expr fuel env tv CoreTy_Bool = u64_lit 1"
| "tsz_expr fuel env tv (CoreTy_FiniteInt s b) = u64_lit (byte_width b)"
| "tsz_expr fuel env tv CoreTy_MathInt = u64_lit 0"
| "tsz_expr fuel env tv CoreTy_MathReal = u64_lit 0"
| "tsz_expr fuel env tv (CoreTy_Record flds) =
    foldr e_add (map (\<lambda>fld. tsz_expr fuel env tv (snd fld)) flds) (u64_lit 0)"
| "tsz_expr fuel env tv (CoreTy_Array elemTy dims) =
    (if dims_all_fixed dims then e_mul (tsz_expr fuel env tv elemTy) (u64_lit (dims_count dims))
     else e_add ME_PtrSize (u64_lit (8 * length dims)))"
| "tsz_expr fuel env tv (CoreTy_Var v) = tv v"
| "tsz_expr fuel env tv (CoreTy_Extern _ _) = ME_PtrSize"

(* The payload expression of a constructor, given the expressions of its
   datatype's type arguments (cf. ctor_tsz). *)
definition ctor_tsz_expr :: "nat \<Rightarrow> CoreTyEnv \<Rightarrow> MExpr list \<Rightarrow> string \<Rightarrow> MExpr" where
  "ctor_tsz_expr fuel env argExprs ctor =
    (case fmlookup (TE_DataCtors env) ctor of
       Some (_, tyvars, payloadTy) \<Rightarrow> tsz_expr fuel env (tyvar_exprs tyvars argExprs) payloadTy
     | None \<Rightarrow> u64_lit 0)"

lemma tsz_expr_Suc_Datatype:
  "tsz_expr (Suc fuel) env tv (CoreTy_Datatype dtName args)
   = e_add (u64_lit (tag_size env dtName))
       (foldr e_max (map (ctor_tsz_expr fuel env (map (tsz_expr (Suc fuel) env tv) args)) (dt_ctors env dtName))
              (u64_lit 0))"
  by (simp add: ctor_tsz_expr_def[abs_def] cong: option.case_cong)

declare tsz_expr.simps(1) [simp del]

lemma tsz_expr_0_Datatype [simp]: "tsz_expr 0 env tv (CoreTy_Datatype dtName args) = u64_lit 0"
  by (simp add: tsz_expr.simps(1))

(* The size expression of a type. *)
definition size_expr :: "CoreTyEnv \<Rightarrow> (string \<Rightarrow> MExpr) \<Rightarrow> CoreType \<Rightarrow> MExpr" where
  "size_expr env tv ty = tsz_expr (dt_fuel env) env tv ty"


section \<open>Sizes that fit\<close>

(* Every size the expression for a type computes is below 2^64. *)
fun tsz_fits :: "nat \<Rightarrow> CoreTyEnv \<Rightarrow> nat \<Rightarrow> (string \<Rightarrow> nat) \<Rightarrow> CoreType \<Rightarrow> bool" where
  "tsz_fits fuel env P sz (CoreTy_Datatype dtName args) =
    (tsz fuel env P sz (CoreTy_Datatype dtName args) < u64_max
     \<and> list_all (tsz_fits fuel env P sz) args
     \<and> (if fuel = 0 then True
        else list_all (\<lambda>ctor.
               case fmlookup (TE_DataCtors env) ctor of
                 Some (_, tyvars, payloadTy) \<Rightarrow>
                   tsz_fits (fuel - 1) env P (tyvar_sizes tyvars (map (tsz fuel env P sz) args)) payloadTy
               | None \<Rightarrow> True)
             (dt_ctors env dtName)))"
| "tsz_fits fuel env P sz CoreTy_Bool = True"
| "tsz_fits fuel env P sz (CoreTy_FiniteInt s b) = True"
| "tsz_fits fuel env P sz CoreTy_MathInt = True"
| "tsz_fits fuel env P sz CoreTy_MathReal = True"
| "tsz_fits fuel env P sz (CoreTy_Record flds) =
    (tsz fuel env P sz (CoreTy_Record flds) < u64_max
     \<and> list_all (\<lambda>fld. tsz_fits fuel env P sz (snd fld)) flds)"
| "tsz_fits fuel env P sz (CoreTy_Array elemTy dims) =
    (if dims_all_fixed dims
     then dims_count dims < u64_max \<and> tsz fuel env P sz elemTy * dims_count dims < u64_max
          \<and> tsz_fits fuel env P sz elemTy
     else desc_size P (length dims) < u64_max)"
| "tsz_fits fuel env P sz (CoreTy_Var v) = (sz v < u64_max)"
| "tsz_fits fuel env P sz (CoreTy_Extern n l) = (P < u64_max)"

definition ctor_tsz_fits :: "nat \<Rightarrow> CoreTyEnv \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> string \<Rightarrow> bool" where
  "ctor_tsz_fits fuel env P argSizes ctor =
    (case fmlookup (TE_DataCtors env) ctor of
       Some (_, tyvars, payloadTy) \<Rightarrow> tsz_fits fuel env P (tyvar_sizes tyvars argSizes) payloadTy
     | None \<Rightarrow> True)"

lemma tsz_fits_Suc_Datatype:
  "tsz_fits (Suc fuel) env P sz (CoreTy_Datatype dtName args)
   = (tsz (Suc fuel) env P sz (CoreTy_Datatype dtName args) < u64_max
      \<and> list_all (tsz_fits (Suc fuel) env P sz) args
      \<and> list_all (ctor_tsz_fits fuel env P (map (tsz (Suc fuel) env P sz) args)) (dt_ctors env dtName))"
  by (simp add: ctor_tsz_fits_def[abs_def] cong: option.case_cong)

lemma tsz_fits_0_Datatype:
  "tsz_fits 0 env P sz (CoreTy_Datatype dtName args) = list_all (tsz_fits 0 env P sz) args"
  by simp

declare tsz_fits.simps(1) [simp del]

definition size_fits :: "CoreTyEnv \<Rightarrow> nat \<Rightarrow> (string \<Rightarrow> nat) \<Rightarrow> CoreType \<Rightarrow> bool" where
  "size_fits env P sz ty = tsz_fits (dt_fuel env) env P sz ty"

(* A type that fits has size below 2^64. *)
lemma tsz_fits_lt:
  assumes "tsz_fits fuel env P sz ty"
  shows "tsz fuel env P sz ty < u64_max"
proof (cases ty)
  case (CoreTy_Datatype dtName args)
  then show ?thesis using assms by (cases fuel) (simp_all add: tsz_fits_Suc_Datatype)
next
  case CoreTy_Bool
  then show ?thesis by (simp add: u64_max_def)
next
  case (CoreTy_FiniteInt s b)
  then show ?thesis by (cases b) (simp_all add: u64_max_def)
next
  case (CoreTy_Array elemTy dims)
  then show ?thesis using assms by (simp split: if_splits)
qed (use assms in simp_all)

lemma size_fits_lt: "size_fits env P sz ty \<Longrightarrow> type_size env P sz ty < u64_max"
  unfolding size_fits_def type_size_def by (rule tsz_fits_lt)

(* Fitting is preserved by decreasing the assignment and the pointer size. *)
lemma tsz_fits_anti_mono:
  assumes "P \<le> P'"
  shows "(\<And>v. sz v \<le> sz' v) \<Longrightarrow> tsz_fits fuel env P' sz' ty \<Longrightarrow> tsz_fits fuel env P sz ty"
proof (induction fuel arbitrary: ty sz sz')
  case 0
  then show ?case
  proof (induction ty)
    case (CoreTy_Datatype dtName args)
    then show ?case by (simp add: tsz_fits_0_Datatype list_all_iff)
  next
    case (CoreTy_Record flds)
    have le: "tsz 0 env P sz (CoreTy_Record flds) \<le> tsz 0 env P' sz' (CoreTy_Record flds)"
      using CoreTy_Record.prems(1) assms by (intro tsz_mono)
    have IH': "\<And>fld. fld \<in> set flds \<Longrightarrow> tsz_fits 0 env P' sz' (snd fld) \<Longrightarrow> tsz_fits 0 env P sz (snd fld)"
      by (rule CoreTy_Record.IH[OF _ snds.intros CoreTy_Record.prems(1)])
    with CoreTy_Record.prems(2) le show ?case by (auto simp: list_all_iff)
  next
    case (CoreTy_Array elemTy dims)
    have le: "tsz 0 env P sz elemTy \<le> tsz 0 env P' sz' elemTy"
      using CoreTy_Array.prems(1) assms by (intro tsz_mono)
    show ?case
    proof (cases "dims_all_fixed dims")
      case True
      with CoreTy_Array.prems(2) have f0: "dims_count dims < u64_max"
        and f1: "tsz 0 env P' sz' elemTy * dims_count dims < u64_max"
        and f2: "tsz_fits 0 env P' sz' elemTy" by simp_all
      have "tsz 0 env P sz elemTy * dims_count dims < u64_max"
        using mult_le_mono1[OF le, of "dims_count dims"] f1 by (rule le_less_trans)
      with True f0 CoreTy_Array.IH[OF CoreTy_Array.prems(1) f2] show ?thesis by simp
    next
      case False
      with CoreTy_Array.prems(2) have "desc_size P' (length dims) < u64_max" by simp
      hence "P + 8 * length dims < u64_max" using assms unfolding desc_size_def by linarith
      thus ?thesis using False by (simp add: desc_size_def)
    qed
  next
    case (CoreTy_Var v)
    show ?case unfolding tsz_fits.simps(8)
      by (rule le_less_trans[OF CoreTy_Var.prems(1)]) (use CoreTy_Var.prems(2) in simp)
  next
    case (CoreTy_Extern n l)
    show ?case unfolding tsz_fits.simps(9)
      by (rule le_less_trans[OF assms]) (use CoreTy_Extern.prems(2) in simp)
  qed simp_all
next
  case (Suc fuel)
  from Suc.prems show ?case
  proof (induction ty)
    case (CoreTy_Datatype dtName args)
    have le: "tsz (Suc fuel) env P sz (CoreTy_Datatype dtName args) \<le> tsz (Suc fuel) env P' sz' (CoreTy_Datatype dtName args)"
      using CoreTy_Datatype.prems(1) assms by (intro tsz_mono)
    have args_le: "list_all2 (\<le>) (map (tsz (Suc fuel) env P sz) args) (map (tsz (Suc fuel) env P' sz') args)"
      using assms CoreTy_Datatype.prems(1) by (auto simp: list_all2_conv_all_nth intro!: tsz_mono)
    have args_fit: "list_all (tsz_fits (Suc fuel) env P sz) args"
      using CoreTy_Datatype.IH CoreTy_Datatype.prems unfolding tsz_fits_Suc_Datatype list_all_iff by blast
    have ctors_fit: "\<And>ctor. ctor_tsz_fits fuel env P' (map (tsz (Suc fuel) env P' sz') args) ctor
          \<Longrightarrow> ctor_tsz_fits fuel env P (map (tsz (Suc fuel) env P sz) args) ctor"
    proof -
      fix ctor assume c: "ctor_tsz_fits fuel env P' (map (tsz (Suc fuel) env P' sz') args) ctor"
      show "ctor_tsz_fits fuel env P (map (tsz (Suc fuel) env P sz) args) ctor"
      proof (cases "fmlookup (TE_DataCtors env) ctor")
        case None
        then show ?thesis by (simp add: ctor_tsz_fits_def)
      next
        case (Some x)
        then obtain dt tyvars payloadTy where lk: "fmlookup (TE_DataCtors env) ctor = Some (dt, tyvars, payloadTy)"
          by (cases x) auto
        with c have "tsz_fits fuel env P' (tyvar_sizes tyvars (map (tsz (Suc fuel) env P' sz') args)) payloadTy"
          by (simp add: ctor_tsz_fits_def)
        from Suc.IH[OF tyvar_sizes_mono[OF args_le] this] show ?thesis
          using lk by (simp add: ctor_tsz_fits_def)
      qed
    qed
    with CoreTy_Datatype.prems(2) le args_fit show ?case
      unfolding tsz_fits_Suc_Datatype by (auto simp: list_all_iff)
  next
    case (CoreTy_Record flds)
    have le: "tsz (Suc fuel) env P sz (CoreTy_Record flds) \<le> tsz (Suc fuel) env P' sz' (CoreTy_Record flds)"
      using CoreTy_Record.prems(1) assms by (intro tsz_mono)
    have IH': "\<And>fld. fld \<in> set flds \<Longrightarrow> tsz_fits (Suc fuel) env P' sz' (snd fld) \<Longrightarrow> tsz_fits (Suc fuel) env P sz (snd fld)"
      by (rule CoreTy_Record.IH[OF _ snds.intros CoreTy_Record.prems(1)])
    with CoreTy_Record.prems(2) le show ?case by (auto simp: list_all_iff)
  next
    case (CoreTy_Array elemTy dims)
    have le: "tsz (Suc fuel) env P sz elemTy \<le> tsz (Suc fuel) env P' sz' elemTy"
      using CoreTy_Array.prems(1) assms by (intro tsz_mono)
    show ?case
    proof (cases "dims_all_fixed dims")
      case True
      with CoreTy_Array.prems(2) have f0: "dims_count dims < u64_max"
        and f1: "tsz (Suc fuel) env P' sz' elemTy * dims_count dims < u64_max"
        and f2: "tsz_fits (Suc fuel) env P' sz' elemTy" by simp_all
      have "tsz (Suc fuel) env P sz elemTy * dims_count dims < u64_max"
        using mult_le_mono1[OF le, of "dims_count dims"] f1 by (rule le_less_trans)
      with True f0 CoreTy_Array.IH[OF CoreTy_Array.prems(1) f2] show ?thesis by simp
    next
      case False
      with CoreTy_Array.prems(2) have "desc_size P' (length dims) < u64_max" by simp
      hence "P + 8 * length dims < u64_max" using assms unfolding desc_size_def by linarith
      thus ?thesis using False by (simp add: desc_size_def)
    qed
  next
    case (CoreTy_Var v)
    show ?case unfolding tsz_fits.simps(8)
      by (rule le_less_trans[OF CoreTy_Var.prems(1)]) (use CoreTy_Var.prems(2) in simp)
  next
    case (CoreTy_Extern n l)
    show ?case unfolding tsz_fits.simps(9)
      by (rule le_less_trans[OF assms]) (use CoreTy_Extern.prems(2) in simp)
  qed simp_all
qed

lemma size_fits_anti_mono:
  assumes "\<And>v. sz v \<le> sz' v" and "P \<le> P'" and "size_fits env P' sz' ty"
  shows "size_fits env P sz ty"
  unfolding size_fits_def by (rule tsz_fits_anti_mono[OF assms(2) assms(1) assms(3)[unfolded size_fits_def]])

(* Fitting depends on the assignment only at the type variables of the type. *)
lemma tsz_fits_cong_sz:
  "(\<And>v. v \<in> type_tyvars ty \<Longrightarrow> sz v = sz' v) \<Longrightarrow> tsz_fits fuel env P sz ty = tsz_fits fuel env P sz' ty"
proof (induction ty)
  case (CoreTy_Datatype dtName args)
  have args_eq: "map (tsz fuel env P sz) args = map (tsz fuel env P sz') args"
    using CoreTy_Datatype.prems by (intro map_cong refl tsz_cong_sz) auto
  have ty_eq: "tsz fuel env P sz (CoreTy_Datatype dtName args) = tsz fuel env P sz' (CoreTy_Datatype dtName args)"
    using CoreTy_Datatype.prems by (intro tsz_cong_sz)
  have fits_eq: "list_all (tsz_fits fuel env P sz) args = list_all (tsz_fits fuel env P sz') args"
    using CoreTy_Datatype.IH CoreTy_Datatype.prems unfolding list_all_iff by auto
  show ?case unfolding tsz_fits.simps(1) args_eq ty_eq fits_eq ..
next
  case (CoreTy_Record flds)
  have ty_eq: "tsz fuel env P sz (CoreTy_Record flds) = tsz fuel env P sz' (CoreTy_Record flds)"
    using CoreTy_Record.prems by (intro tsz_cong_sz)
  have "\<And>fld. fld \<in> set flds \<Longrightarrow> tsz_fits fuel env P sz (snd fld) = tsz_fits fuel env P sz' (snd fld)"
  proof -
    fix fld assume f: "fld \<in> set flds"
    show "tsz_fits fuel env P sz (snd fld) = tsz_fits fuel env P sz' (snd fld)"
      by (rule CoreTy_Record.IH[OF f snds.intros]) (use CoreTy_Record.prems f in \<open>auto simp: case_prod_beta\<close>)
  qed
  then show ?case using ty_eq by (simp add: list_all_iff)
next
  case (CoreTy_Array elemTy dims)
  have "tsz fuel env P sz elemTy = tsz fuel env P sz' elemTy"
    using CoreTy_Array.prems by (intro tsz_cong_sz) simp
  with CoreTy_Array show ?case by simp
qed simp_all

lemma size_fits_cong_sz:
  "(\<And>v. v \<in> type_tyvars ty \<Longrightarrow> sz v = sz' v) \<Longrightarrow> size_fits env P sz ty = size_fits env P sz' ty"
  unfolding size_fits_def by (rule tsz_fits_cong_sz)

(* Components of a type that fits also fit. *)
lemma tsz_fits_Record_fld:
  "tsz_fits fuel env P sz (CoreTy_Record flds) \<Longrightarrow> fld \<in> set flds \<Longrightarrow> tsz_fits fuel env P sz (snd fld)"
  by (simp add: list_all_iff)

lemma tsz_fits_Array_elem:
  "tsz_fits fuel env P sz (CoreTy_Array elemTy dims) \<Longrightarrow> dims_all_fixed dims \<Longrightarrow> tsz_fits fuel env P sz elemTy"
  by simp

lemma tsz_fits_Datatype_arg:
  "tsz_fits fuel env P sz (CoreTy_Datatype dtName args) \<Longrightarrow> arg \<in> set args \<Longrightarrow> tsz_fits fuel env P sz arg"
  by (cases fuel) (simp_all add: tsz_fits_0_Datatype tsz_fits_Suc_Datatype list_all_iff)

lemma tsz_fits_Datatype_payload:
  assumes "tsz_fits (Suc fuel) env P sz (CoreTy_Datatype dtName args)"
    and "ctor \<in> set (dt_ctors env dtName)"
    and "fmlookup (TE_DataCtors env) ctor = Some (dt, tyvars, payloadTy)"
  shows "tsz_fits fuel env P (tyvar_sizes tyvars (map (tsz (Suc fuel) env P sz) args)) payloadTy"
proof -
  have "ctor_tsz_fits fuel env P (map (tsz (Suc fuel) env P sz) args) ctor"
    using assms(1,2) unfolding tsz_fits_Suc_Datatype list_all_iff by blast
  thus ?thesis using assms(3) by (simp add: ctor_tsz_fits_def)
qed


section \<open>Evaluation\<close>

(* The type-variable expressions evaluate to the assignment, on the type
   variables of a type. *)
definition tv_eval :: "MEncoding \<Rightarrow> 'w MState \<Rightarrow> (string \<Rightarrow> MExpr) \<Rightarrow> (string \<Rightarrow> nat) \<Rightarrow> CoreType \<Rightarrow> bool" where
  "tv_eval enc st tv sz ty = (\<forall>v \<in> type_tyvars ty. eval_expr enc st (tv v) = Some (MV_U64 (int (sz v))))"

lemma tv_eval_subset: "tv_eval enc st tv sz ty \<Longrightarrow> type_tyvars ty' \<subseteq> type_tyvars ty \<Longrightarrow> tv_eval enc st tv sz ty'"
  unfolding tv_eval_def by blast

lemma tv_eval_Record_fld:
  "tv_eval enc st tv sz (CoreTy_Record flds) \<Longrightarrow> fld \<in> set flds \<Longrightarrow> tv_eval enc st tv sz (snd fld)"
  by (rule tv_eval_subset) (auto simp: case_prod_beta intro!: bexI[where x = fld])

lemma tv_eval_Datatype_arg:
  "tv_eval enc st tv sz (CoreTy_Datatype dtName args) \<Longrightarrow> arg \<in> set args \<Longrightarrow> tv_eval enc st tv sz arg"
  by (rule tv_eval_subset) auto

lemma tv_eval_Array_elem:
  "tv_eval enc st tv sz (CoreTy_Array elemTy dims) \<Longrightarrow> tv_eval enc st tv sz elemTy"
  by (rule tv_eval_subset) auto

(* The type-variable expressions of a constructor's payload: the argument
   expressions, which evaluate to the argument sizes. *)
lemma tv_eval_tyvar_exprs:
  assumes "\<And>arg. arg \<in> set args \<Longrightarrow> eval_expr enc st (g arg) = Some (MV_U64 (int (f arg)))"
  shows "tv_eval enc st (tyvar_exprs tyvars (map g args)) (tyvar_sizes tyvars (map f args)) ty"
  unfolding tv_eval_def
proof
  fix v assume "v \<in> type_tyvars ty"
  show "eval_expr enc st (tyvar_exprs tyvars (map g args) v) = Some (MV_U64 (int (tyvar_sizes tyvars (map f args) v)))"
  proof (cases "map_of (zip tyvars args) v")
    case None
    hence "map_of (zip tyvars (map g args)) v = None" and "map_of (zip tyvars (map f args)) v = None"
      by (simp_all add: zip_map2 map_of_map)
    then show ?thesis by (simp add: tyvar_exprs_def tyvar_sizes_def)
  next
    case (Some arg)
    hence "map_of (zip tyvars (map g args)) v = Some (g arg)" and "map_of (zip tyvars (map f args)) v = Some (f arg)"
      by (simp_all add: zip_map2 map_of_map)
    moreover have "arg \<in> set args" using Some by (auto dest: map_of_SomeD set_zip_rightD)
    ultimately show ?thesis using assms by (simp add: tyvar_exprs_def tyvar_sizes_def)
  qed
qed

(* The main lemma: a size expression evaluates to the size. *)
lemma tsz_expr_eval:
  assumes "valid_encoding enc"
  shows "tsz_fits fuel env (enc_ptr_size enc) sz ty \<Longrightarrow> tv_eval enc st tv sz ty
         \<Longrightarrow> eval_expr enc st (tsz_expr fuel env tv ty) = Some (MV_U64 (int (tsz fuel env (enc_ptr_size enc) sz ty)))"
proof (induction fuel arbitrary: ty sz tv)
  case 0
  then show ?case
  proof (induction ty)
    case (CoreTy_Record flds)
    have fld: "\<And>fld. fld \<in> set flds \<Longrightarrow>
            eval_expr enc st (tsz_expr 0 env tv (snd fld)) = Some (MV_U64 (int (tsz 0 env (enc_ptr_size enc) sz (snd fld))))"
    proof -
      fix fld assume f: "fld \<in> set flds"
      show "eval_expr enc st (tsz_expr 0 env tv (snd fld)) = Some (MV_U64 (int (tsz 0 env (enc_ptr_size enc) sz (snd fld))))"
        by (rule CoreTy_Record.IH[OF f snds.intros tsz_fits_Record_fld[OF CoreTy_Record.prems(1) f]
                                     tv_eval_Record_fld[OF CoreTy_Record.prems(2) f]])
    qed
    have "tsz 0 env (enc_ptr_size enc) sz (CoreTy_Record flds) < u64_max"
      by (rule tsz_fits_lt[OF CoreTy_Record.prems(1)])
    with fld show ?case unfolding tsz_expr.simps(6) tsz.simps(6) by (rule eval_foldr_add)
  next
    case (CoreTy_Array elemTy dims)
    show ?case
    proof (cases "dims_all_fixed dims")
      case True
      have ih: "eval_expr enc st (tsz_expr 0 env tv elemTy) = Some (MV_U64 (int (tsz 0 env (enc_ptr_size enc) sz elemTy)))"
        by (rule CoreTy_Array.IH[OF tsz_fits_Array_elem[OF CoreTy_Array.prems(1) True]
                                    tv_eval_Array_elem[OF CoreTy_Array.prems(2)]])
      from CoreTy_Array.prems(1) True have cnt: "dims_count dims < u64_max"
        and fits: "tsz 0 env (enc_ptr_size enc) sz elemTy * dims_count dims < u64_max" by simp_all
      show ?thesis using True
        by (simp only: tsz_expr.simps(7) tsz.simps(7) if_True) (rule eval_e_mul[OF ih eval_u64_lit_Some[OF cnt] fits])
    next
      case False
      have plt: "enc_ptr_size enc + 8 * length dims < u64_max"
        using CoreTy_Array.prems(1) False by (simp add: desc_size_def)
      hence lit: "8 * length dims < u64_max" by linarith
      show ?thesis using False
        by (simp only: tsz_expr.simps(7) tsz.simps(7) if_False desc_size_def)
           (rule eval_e_add[OF eval_expr.simps(2) eval_u64_lit_Some[OF lit] plt])
    qed
  next
    case (CoreTy_Var v)
    then show ?case by (simp add: tv_eval_def)
  next
    case (CoreTy_Extern n l)
    then show ?case by simp
  next
    case CoreTy_Bool
    then show ?case by (simp add: u64_max_def)
  next
    case (CoreTy_FiniteInt s b)
    then show ?case by (cases b) (simp_all add: u64_max_def)
  qed (simp_all add: tsz_fits_0_Datatype)
next
  case (Suc fuel)
  note IH_fuel = Suc.IH
  from Suc.prems show ?case
  proof (induction ty)
    case (CoreTy_Datatype dtName args)
    let ?P = "enc_ptr_size enc"
    let ?argExprs = "map (tsz_expr (Suc fuel) env tv) args"
    let ?argSizes = "map (tsz (Suc fuel) env ?P sz) args"
    have args: "\<And>arg. arg \<in> set args \<Longrightarrow>
            eval_expr enc st (tsz_expr (Suc fuel) env tv arg) = Some (MV_U64 (int (tsz (Suc fuel) env ?P sz arg)))"
      using CoreTy_Datatype.IH tsz_fits_Datatype_arg[OF CoreTy_Datatype.prems(1)]
            tv_eval_Datatype_arg[OF CoreTy_Datatype.prems(2)] by blast
    have ctors: "\<And>ctor. ctor \<in> set (dt_ctors env dtName) \<Longrightarrow>
            eval_expr enc st (ctor_tsz_expr fuel env ?argExprs ctor) = Some (MV_U64 (int (ctor_tsz fuel env ?P ?argSizes ctor)))"
    proof -
      fix ctor assume c: "ctor \<in> set (dt_ctors env dtName)"
      show "eval_expr enc st (ctor_tsz_expr fuel env ?argExprs ctor) = Some (MV_U64 (int (ctor_tsz fuel env ?P ?argSizes ctor)))"
      proof (cases "fmlookup (TE_DataCtors env) ctor")
        case None
        then show ?thesis by (simp add: ctor_tsz_expr_def ctor_tsz_def)
      next
        case (Some x)
        then obtain dt tyvars payloadTy where lk: "fmlookup (TE_DataCtors env) ctor = Some (dt, tyvars, payloadTy)"
          by (cases x) auto
        have "eval_expr enc st (tsz_expr fuel env (tyvar_exprs tyvars ?argExprs) payloadTy)
              = Some (MV_U64 (int (tsz fuel env ?P (tyvar_sizes tyvars ?argSizes) payloadTy)))"
          by (rule IH_fuel[OF tsz_fits_Datatype_payload[OF CoreTy_Datatype.prems(1) c lk] tv_eval_tyvar_exprs[OF args]])
        thus ?thesis using lk by (simp add: ctor_tsz_expr_def ctor_tsz_def)
      qed
    qed
    have fits: "tag_size env dtName + max_list (map (ctor_tsz fuel env ?P ?argSizes) (dt_ctors env dtName)) < u64_max"
      using tsz_fits_lt[OF CoreTy_Datatype.prems(1)] unfolding tsz_Suc_Datatype .
    have tag_lt: "tag_size env dtName < u64_max" using fits by linarith
    have max_lt: "max_list (map (ctor_tsz fuel env ?P ?argSizes) (dt_ctors env dtName)) < u64_max"
      using fits by linarith
    have "eval_expr enc st (foldr e_max (map (ctor_tsz_expr fuel env ?argExprs) (dt_ctors env dtName)) (u64_lit 0))
          = Some (MV_U64 (int (max_list (map (ctor_tsz fuel env ?P ?argSizes) (dt_ctors env dtName)))))"
      by (rule eval_foldr_max[OF ctors max_lt])
    thus ?case
      unfolding tsz_expr_Suc_Datatype tsz_Suc_Datatype
      by (rule eval_e_add[OF eval_u64_lit_Some[OF tag_lt] _ fits])
  next
    case (CoreTy_Record flds)
    have fld: "\<And>fld. fld \<in> set flds \<Longrightarrow>
            eval_expr enc st (tsz_expr (Suc fuel) env tv (snd fld)) = Some (MV_U64 (int (tsz (Suc fuel) env (enc_ptr_size enc) sz (snd fld))))"
    proof -
      fix fld assume f: "fld \<in> set flds"
      show "eval_expr enc st (tsz_expr (Suc fuel) env tv (snd fld)) = Some (MV_U64 (int (tsz (Suc fuel) env (enc_ptr_size enc) sz (snd fld))))"
        by (rule CoreTy_Record.IH[OF f snds.intros tsz_fits_Record_fld[OF CoreTy_Record.prems(1) f]
                                     tv_eval_Record_fld[OF CoreTy_Record.prems(2) f]])
    qed
    have "tsz (Suc fuel) env (enc_ptr_size enc) sz (CoreTy_Record flds) < u64_max"
      by (rule tsz_fits_lt[OF CoreTy_Record.prems(1)])
    with fld show ?case unfolding tsz_expr.simps(6) tsz.simps(6) by (rule eval_foldr_add)
  next
    case (CoreTy_Array elemTy dims)
    show ?case
    proof (cases "dims_all_fixed dims")
      case True
      have ih: "eval_expr enc st (tsz_expr (Suc fuel) env tv elemTy) = Some (MV_U64 (int (tsz (Suc fuel) env (enc_ptr_size enc) sz elemTy)))"
        by (rule CoreTy_Array.IH[OF tsz_fits_Array_elem[OF CoreTy_Array.prems(1) True]
                                    tv_eval_Array_elem[OF CoreTy_Array.prems(2)]])
      from CoreTy_Array.prems(1) True have cnt: "dims_count dims < u64_max"
        and fits: "tsz (Suc fuel) env (enc_ptr_size enc) sz elemTy * dims_count dims < u64_max" by simp_all
      show ?thesis using True
        by (simp only: tsz_expr.simps(7) tsz.simps(7) if_True) (rule eval_e_mul[OF ih eval_u64_lit_Some[OF cnt] fits])
    next
      case False
      have plt: "enc_ptr_size enc + 8 * length dims < u64_max"
        using CoreTy_Array.prems(1) False by (simp add: desc_size_def)
      hence lit: "8 * length dims < u64_max" by linarith
      show ?thesis using False
        by (simp only: tsz_expr.simps(7) tsz.simps(7) if_False desc_size_def)
           (rule eval_e_add[OF eval_expr.simps(2) eval_u64_lit_Some[OF lit] plt])
    qed
  next
    case (CoreTy_Var v)
    then show ?case by (simp add: tv_eval_def)
  next
    case (CoreTy_Extern n l)
    then show ?case by simp
  next
    case CoreTy_Bool
    then show ?case by (simp add: u64_max_def)
  next
    case (CoreTy_FiniteInt s b)
    then show ?case by (cases b) (simp_all add: u64_max_def)
  qed simp_all
qed

theorem size_expr_eval:
  assumes "valid_encoding enc"
    and "size_fits env (enc_ptr_size enc) sz ty"
    and "tv_eval enc st tv sz ty"
  shows "eval_expr enc st (size_expr env tv ty) = Some (MV_U64 (int (type_size env (enc_ptr_size enc) sz ty)))"
  using assms unfolding size_expr_def size_fits_def type_size_def by (rule tsz_expr_eval)

(* A ground type needs no type-variable expressions. *)
lemma tv_eval_ground: "type_tyvars ty = {} \<Longrightarrow> tv_eval enc st tv sz ty"
  by (simp add: tv_eval_def)


section \<open>Field offsets\<close>

(* The byte offset of a field: the sum of the sizes of the fields before the
   first field of that name. *)
definition field_offset :: "CoreTyEnv \<Rightarrow> nat \<Rightarrow> (string \<Rightarrow> nat) \<Rightarrow> (string \<times> CoreType) list \<Rightarrow> string \<Rightarrow> nat" where
  "field_offset env P sz flds f =
    sum_list (map (\<lambda>fld. type_size env P sz (snd fld)) (takeWhile (\<lambda>fld. fst fld \<noteq> f) flds))"

definition field_offset_expr :: "CoreTyEnv \<Rightarrow> (string \<Rightarrow> MExpr) \<Rightarrow> (string \<times> CoreType) list \<Rightarrow> string \<Rightarrow> MExpr" where
  "field_offset_expr env tv flds f =
    foldr e_add (map (\<lambda>fld. size_expr env tv (snd fld)) (takeWhile (\<lambda>fld. fst fld \<noteq> f) flds)) (u64_lit 0)"

(* A field splits the record into the fields before it, itself, and the rest. *)
lemma field_split:
  assumes "map_of flds f = Some fty"
  shows "\<exists>pre post. flds = pre @ (f, fty) # post \<and> f \<notin> fst ` set pre"
  using assms
proof (induction flds)
  case Nil
  then show ?case by simp
next
  case (Cons fld flds)
  show ?case
  proof (cases "fst fld = f")
    case True
    with Cons.prems have "fld = (f, fty)" by (cases fld) auto
    thus ?thesis by (intro exI[where x = "[]"] exI[where x = flds]) simp
  next
    case False
    with Cons.prems have "map_of flds f = Some fty" by (cases fld) auto
    from Cons.IH[OF this] obtain pre post where
      "flds = pre @ (f, fty) # post" "f \<notin> fst ` set pre" by blast
    thus ?thesis using False by (intro exI[where x = "fld # pre"] exI[where x = post]) simp
  qed
qed

lemma takeWhile_field:
  assumes "flds = pre @ (f, fty) # post" and "f \<notin> fst ` set pre"
  shows "takeWhile (\<lambda>fld. fst fld \<noteq> f) flds = pre"
  unfolding assms(1) using assms(2) by (subst takeWhile_append2) (auto simp: image_iff)

lemma field_offset_split:
  assumes "flds = pre @ (f, fty) # post" and "f \<notin> fst ` set pre"
  shows "field_offset env P sz flds f = sum_list (map (\<lambda>fld. type_size env P sz (snd fld)) pre)"
  unfolding field_offset_def takeWhile_field[OF assms] ..

(* The bytes of a field lie inside the bytes of the record. *)
lemma field_offset_bound:
  assumes "map_of flds f = Some fty"
  shows "field_offset env P sz flds f + type_size env P sz fty \<le> type_size env P sz (CoreTy_Record flds)"
proof -
  from field_split[OF assms] obtain pre post where
    split: "flds = pre @ (f, fty) # post" and notin: "f \<notin> fst ` set pre" by blast
  show ?thesis
    unfolding field_offset_split[OF split notin]
    unfolding split by simp
qed

lemma field_offset_expr_eval:
  assumes "valid_encoding enc"
    and "size_fits env (enc_ptr_size enc) sz (CoreTy_Record flds)"
    and "tv_eval enc st tv sz (CoreTy_Record flds)"
  shows "eval_expr enc st (field_offset_expr env tv flds f)
         = Some (MV_U64 (int (field_offset env (enc_ptr_size enc) sz flds f)))"
proof -
  let ?pre = "takeWhile (\<lambda>fld. fst fld \<noteq> f) flds"
  let ?g = "\<lambda>fld. type_size env (enc_ptr_size enc) sz (snd fld)"
  have fld: "\<And>fld. fld \<in> set ?pre \<Longrightarrow>
          eval_expr enc st (size_expr env tv (snd fld)) = Some (MV_U64 (int (?g fld)))"
  proof -
    fix fld assume "fld \<in> set ?pre"
    hence f: "fld \<in> set flds" by (auto dest: set_takeWhileD)
    show "eval_expr enc st (size_expr env tv (snd fld)) = Some (MV_U64 (int (?g fld)))"
      by (rule size_expr_eval[OF assms(1) tsz_fits_Record_fld[OF assms(2)[unfolded size_fits_def] f, folded size_fits_def]
                                 tv_eval_Record_fld[OF assms(3) f]])
  qed
  have "sum_list (map ?g ?pre) \<le> sum_list (map ?g (?pre @ dropWhile (\<lambda>fld. fst fld \<noteq> f) flds))"
    by (simp only: map_append sum_list_append le_add1)
  also have "sum_list (map ?g (?pre @ dropWhile (\<lambda>fld. fst fld \<noteq> f) flds)) = sum_list (map ?g flds)"
    by (simp only: takeWhile_dropWhile_id)
  finally have "sum_list (map ?g ?pre) < u64_max"
    using size_fits_lt[OF assms(2)] by simp
  with fld show ?thesis unfolding field_offset_expr_def field_offset_def by (rule eval_foldr_add)
qed


section \<open>Element offsets\<close>

(* The flat (Fortran-order) index as a MiniC expression over the size and
   index expressions: i1 + n1 * (i2 + n2 * (...)). *)
fun flat_index_expr :: "MExpr list \<Rightarrow> MExpr list \<Rightarrow> MExpr" where
  "flat_index_expr (n # ns) (i # is) = e_add i (e_mul n (flat_index_expr ns is))"
| "flat_index_expr _ _ = u64_lit 0"

definition elem_offset_expr :: "MExpr \<Rightarrow> MExpr list \<Rightarrow> MExpr list \<Rightarrow> MExpr" where
  "elem_offset_expr esz ns is = e_mul esz (flat_index_expr ns is)"

(* An in-bounds index has every size at least 1, so the element count is
   positive and the count of the remaining dimensions is at most the count. *)
lemma index_in_bounds_count_pos:
  "index_in_bounds sizes idx \<Longrightarrow> 0 < sizes_count sizes"
proof (induction sizes arbitrary: idx)
  case Nil
  then show ?case by (simp add: sizes_count_def)
next
  case (Cons n ns)
  then show ?case by (auto simp: index_in_bounds_Cons sizes_count_def)
qed

lemma flat_index_expr_eval:
  assumes "list_all2 (\<lambda>e n. eval_expr enc st e = Some (MV_U64 n)) ns sizes"
    and "list_all2 (\<lambda>e i. eval_expr enc st e = Some (MV_U64 i)) is idx"
    and "index_in_bounds sizes idx"
    and "sizes_count sizes < u64_max"
  shows "eval_expr enc st (flat_index_expr ns is) = Some (MV_U64 (flat_index sizes idx))"
  using assms
proof (induction ns sizes arbitrary: "is" idx rule: list_all2_induct)
  case Nil
  then show ?case by simp
next
  case (Cons n' ns' n ns)
  from Cons.prems(2) obtain i "is'" where idx: "idx = i # is'" and bnds: "0 \<le> i" "i < n"
    and rest_ok: "index_in_bounds ns is'" by (auto simp: index_in_bounds_Cons)
  from Cons.prems(1) idx obtain i' is'' where "is": "is = i' # is''"
    and ei: "eval_expr enc st i' = Some (MV_U64 i)"
    and rest_e: "list_all2 (\<lambda>e i. eval_expr enc st e = Some (MV_U64 i)) is'' is'"
    by (auto simp: list_all2_Cons2)
  have count: "sizes_count (n # ns) = nat n * sizes_count ns" by (simp add: sizes_count_def)
  have "1 \<le> nat n" using bnds by simp
  hence "1 * sizes_count ns \<le> nat n * sizes_count ns" by (rule mult_le_mono1)
  hence rest_le: "sizes_count ns \<le> sizes_count (n # ns)" unfolding count by simp
  have rest_lt: "sizes_count ns < u64_max" using rest_le Cons.prems(3) by (rule le_less_trans)
  have ih: "eval_expr enc st (flat_index_expr ns' is'') = Some (MV_U64 (flat_index ns is'))"
    by (rule Cons.IH[OF rest_e rest_ok rest_lt])
  from flat_index_bounds[OF rest_ok] have fb: "0 \<le> flat_index ns is'" "flat_index ns is' < int (sizes_count ns)" by auto
  have lt: "i + n * flat_index ns is' < int (sizes_count (n # ns))"
  proof -
    have "flat_index ns is' + 1 \<le> int (sizes_count ns)" using fb by simp
    hence "n * (flat_index ns is' + 1) \<le> n * int (sizes_count ns)" using bnds by (intro mult_left_mono) auto
    thus ?thesis using bnds count by (simp add: algebra_simps)
  qed
  have lt_max: "int (sizes_count (n # ns)) \<le> int u64_max" using Cons.prems(3) by simp
  have n_nonneg: "0 \<le> n" using bnds by linarith
  have nn: "0 \<le> n * flat_index ns is'" using n_nonneg fb(1) by (rule mult_nonneg_nonneg)
  have mul_lt: "n * flat_index ns is' < int u64_max" using lt lt_max bnds(1) by linarith
  have mul: "eval_expr enc st (e_mul n' (flat_index_expr ns' is'')) = Some (MV_U64 (n * flat_index ns is'))"
    by (rule eval_e_mul_int[OF Cons.hyps(1) ih n_nonneg fb(1) mul_lt])
  have sum_lt: "i + n * flat_index ns is' < int u64_max" using lt lt_max by linarith
  show ?case
    unfolding "is" idx flat_index_expr.simps flat_index.simps
    by (rule eval_e_add_int[OF ei mul bnds(1) nn sum_lt])
qed

lemma elem_offset_expr_eval:
  assumes "eval_expr enc st se = Some (MV_U64 (int esz))"
    and "list_all2 (\<lambda>e n. eval_expr enc st e = Some (MV_U64 n)) ns sizes"
    and "list_all2 (\<lambda>e i. eval_expr enc st e = Some (MV_U64 i)) is idx"
    and "index_in_bounds sizes idx"
    and "sizes_count sizes < u64_max"
    and "esz * sizes_count sizes < u64_max"
  shows "eval_expr enc st (elem_offset_expr se ns is) = Some (MV_U64 (int (elem_offset esz sizes idx)))"
proof -
  have fi: "eval_expr enc st (flat_index_expr ns is) = Some (MV_U64 (flat_index sizes idx))"
    by (rule flat_index_expr_eval[OF assms(2-5)])
  from flat_index_bounds[OF assms(4)] have fb: "0 \<le> flat_index sizes idx" "flat_index sizes idx < int (sizes_count sizes)" by auto
  have lt: "nat (flat_index sizes idx) < sizes_count sizes" using fb by (simp add: nat_less_iff)
  from mult_le_mono2[OF less_imp_le[OF lt], of esz] assms(6)
  have fits: "esz * nat (flat_index sizes idx) < u64_max" by (rule le_less_trans)
  have eq: "int (elem_offset esz sizes idx) = int esz * flat_index sizes idx"
    using fb unfolding elem_offset_def by simp
  have "int (esz * nat (flat_index sizes idx)) < int u64_max"
    using fits by (rule of_nat_less_iff[THEN iffD2])
  hence lt': "int esz * flat_index sizes idx < int u64_max" using fb(1) by simp
  show ?thesis
    unfolding elem_offset_expr_def eq by (rule eval_e_mul_int[OF assms(1) fi _ fb(1) lt']) simp
qed

end
