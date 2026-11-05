theory CoreInterpLvalueRel
  imports CoreInterpFuelMono
begin

(* Lemmas concerning the behaviour of interp_lvalue across a transformation of the
   state and the term. This is the shared core of the argument aliasing case
   of the ghost erasure and match compilation simulations. *)


(* ========================================================================== *)
(* The lvalue of an argument across a transformation of state and term         *)
(* ========================================================================== *)

(* The aliasing check of a call resolves every argument with interp_lvalue
   in its non-writable mode. The ghost erasure and match compilation
   simulations need the resolutions of the transformed arguments in the
   transformed state, from those of the original arguments in the original
   state. Both transformations keep the shape of lvalues (tr_simps), turn a
   non-lvalue into a non-lvalue (tr_other), and relate the addresses of the
   local variables (R). The argument evaluates as an rvalue in both states
   (so every index list of the lvalue skeleton does, at the respective fuel),
   and index lists that evaluate in both states evaluate to the same values
   (idx, at the fuels F and F'). Then, resolving at any fuels G and G' between
   those of the evaluations and F and F', either both resolutions are
   TypeError (no lvalue), or both are lvalues with the same path and related
   addresses. *)

lemma interp_term_Inr_le_Suc:
  "interp_term d fuel s tm = Inr v \<Longrightarrow> fuel \<le> G \<Longrightarrow> \<exists>G0. G = Suc G0"
  by (cases fuel; cases G) simp_all

(* A term that is not an lvalue resolves to TypeError in both states (the
   fuels are positive, as the terms evaluated). *)
lemma interp_lvalue_rel_other:
  assumes "\<not> lvalue_shape tm" and "\<not> lvalue_shape tm'"
    and "interp_term d fuel s tm = Inr v" and "fuel \<le> G"
    and "interp_term d fuel' s' tm' = Inr v'" and "fuel' \<le> G'"
  shows "(interp_lvalue d G wr s tm = Inl TypeError \<and> interp_lvalue d G' wr' s' tm' = Inl TypeError) \<or> P"
proof -
  obtain G0 where G: "G = Suc G0" using interp_term_Inr_le_Suc[OF assms(3,4)] by blast
  obtain G0' where G': "G' = Suc G0'" using interp_term_Inr_le_Suc[OF assms(5,6)] by blast
  have "interp_lvalue d G wr s tm = Inl TypeError"
    unfolding G by (rule interp_lvalue_not_shape[OF assms(1)])
  moreover have "interp_lvalue d G' wr' s' tm' = Inl TypeError"
    unfolding G' by (rule interp_lvalue_not_shape[OF assms(2)])
  ultimately show ?thesis by simp
qed

lemma interp_lvalue_rel:
  fixes tr :: "CoreTerm \<Rightarrow> CoreTerm" and R :: "nat \<Rightarrow> nat \<Rightarrow> bool" and Q :: "CoreTerm \<Rightarrow> bool"
    and s s' :: "'w InterpState"
  assumes Q_sub: "\<And>t f. Q (CoreTm_RecordProj t f) \<Longrightarrow> Q t"
                 "\<And>t c. Q (CoreTm_VariantProj t c) \<Longrightarrow> Q t"
                 "\<And>t idx. Q (CoreTm_ArrayProj t idx) \<Longrightarrow> Q t \<and> list_all Q idx"
                 "\<And>ty t. Q (CoreTm_Cast ty t) \<Longrightarrow> Q t"
    and locals: "\<And>x. Q (CoreTm_Var x) \<Longrightarrow> rel_option R (fmlookup (IS_Locals s) x) (fmlookup (IS_Locals s') x)"
    and refs: "\<And>x. Q (CoreTm_Var x) \<Longrightarrow> rel_option (\<lambda>(a, p) (a', p'). R a a' \<and> p = p')
                                         (fmlookup (IS_Refs s) x) (fmlookup (IS_Refs s') x)"
    and tr_simps: "\<And>x. tr (CoreTm_Var x) = CoreTm_Var x"
                  "\<And>t f. tr (CoreTm_RecordProj t f) = CoreTm_RecordProj (tr t) f"
                  "\<And>t c. tr (CoreTm_VariantProj t c) = CoreTm_VariantProj (tr t) c"
                  "\<And>t idx. tr (CoreTm_ArrayProj t idx) = CoreTm_ArrayProj (tr t) (map tr idx)"
                  "\<And>ty t. tr (CoreTm_Cast ty t) = CoreTm_Cast ty (tr t)"
    and tr_other: "\<And>t. \<not> lvalue_shape t \<Longrightarrow> \<not> lvalue_shape (tr t)"
    and idx: "\<And>tms vs vs'. list_all Q tms \<Longrightarrow> interp_term_list d F s tms = Inr vs
                \<Longrightarrow> interp_term_list d F' s' (map tr tms) = Inr vs' \<Longrightarrow> vs = vs'"
    and ev: "interp_term d fuel s tm = Inr v" and F: "fuel \<le> G" and GF: "G \<le> F"
    and ev': "interp_term d fuel' s' (tr tm) = Inr v'" and F': "fuel' \<le> G'" and GF': "G' \<le> F'"
    and Q: "Q tm"
  shows "(interp_lvalue d G False s tm = Inl TypeError
          \<and> interp_lvalue d G' False s' (tr tm) = Inl TypeError)
         \<or> (\<exists>a p a'. interp_lvalue d G False s tm = Inr (a, p)
                  \<and> interp_lvalue d G' False s' (tr tm) = Inr (a', p) \<and> R a a')"
  using ev F GF ev' F' GF' Q
proof (induction tm arbitrary: fuel fuel' v v' G G')
  case (CoreTm_Var x)
  note Qx = CoreTm_Var.prems(7)
  obtain G0 where G: "G = Suc G0" using interp_term_Inr_le_Suc[OF CoreTm_Var.prems(1,2)] by blast
  obtain G0' where G': "G' = Suc G0'" using interp_term_Inr_le_Suc[OF CoreTm_Var.prems(4,5)] by blast
  show ?case
    using locals[OF Qx] refs[OF Qx] unfolding G G'
    by (cases "fmlookup (IS_Locals s) x"; cases "fmlookup (IS_Locals s') x";
        cases "fmlookup (IS_Refs s) x"; cases "fmlookup (IS_Refs s') x")
       (auto simp: tr_simps(1))
next
  case (CoreTm_RecordProj t f)
  from CoreTm_RecordProj.prems(1) obtain f0 w where fuel: "fuel = Suc f0"
    and evt: "interp_term d f0 s t = Inr w"
    by (cases fuel) (auto split: sum.splits CoreValue.splits)
  from CoreTm_RecordProj.prems(4) obtain f0' w' where fuel': "fuel' = Suc f0'"
    and evt': "interp_term d f0' s' (tr t) = Inr w'"
    unfolding tr_simps(2) by (cases fuel') (auto split: sum.splits CoreValue.splits)
  obtain G0 where G: "G = Suc G0" using Suc_le_D[OF CoreTm_RecordProj.prems(2)[unfolded fuel]] by blast
  obtain G0' where G': "G' = Suc G0'" using Suc_le_D[OF CoreTm_RecordProj.prems(5)[unfolded fuel']] by blast
  have Qt: "Q t" using Q_sub(1) CoreTm_RecordProj.prems(7) by blast
  have le: "f0 \<le> G0" "G0 \<le> F" "f0' \<le> G0'" "G0' \<le> F'"
    using fuel fuel' G G' CoreTm_RecordProj.prems(2,3,5,6) by simp_all
  from CoreTm_RecordProj.IH[OF evt le(1,2) evt' le(3,4) Qt]
  show ?case unfolding tr_simps(2) G G' by auto
next
  case (CoreTm_VariantProj t c)
  from CoreTm_VariantProj.prems(1) obtain f0 w where fuel: "fuel = Suc f0"
    and evt: "interp_term d f0 s t = Inr w"
    by (cases fuel) (auto split: sum.splits CoreValue.splits if_splits)
  from CoreTm_VariantProj.prems(4) obtain f0' w' where fuel': "fuel' = Suc f0'"
    and evt': "interp_term d f0' s' (tr t) = Inr w'"
    unfolding tr_simps(3) by (cases fuel') (auto split: sum.splits CoreValue.splits if_splits)
  obtain G0 where G: "G = Suc G0" using Suc_le_D[OF CoreTm_VariantProj.prems(2)[unfolded fuel]] by blast
  obtain G0' where G': "G' = Suc G0'" using Suc_le_D[OF CoreTm_VariantProj.prems(5)[unfolded fuel']] by blast
  have Qt: "Q t" using Q_sub(2) CoreTm_VariantProj.prems(7) by blast
  have le: "f0 \<le> G0" "G0 \<le> F" "f0' \<le> G0'" "G0' \<le> F'"
    using fuel fuel' G G' CoreTm_VariantProj.prems(2,3,5,6) by simp_all
  from CoreTm_VariantProj.IH[OF evt le(1,2) evt' le(3,4) Qt]
  show ?case unfolding tr_simps(3) G G' by auto
next
  case (CoreTm_ArrayProj t idx)
  from CoreTm_ArrayProj.prems(1) obtain f0 w ivs indices where fuel: "fuel = Suc f0"
    and evt: "interp_term d f0 s t = Inr w" and evi: "interp_term_list d f0 s idx = Inr ivs"
    and ii: "interpret_index_vals ivs = Inr indices"
    by (cases fuel) (auto split: sum.splits CoreValue.splits option.splits)
  from CoreTm_ArrayProj.prems(4) obtain f0' w' ivs' where fuel': "fuel' = Suc f0'"
    and evt': "interp_term d f0' s' (tr t) = Inr w'"
    and evi': "interp_term_list d f0' s' (map tr idx) = Inr ivs'"
    unfolding tr_simps(4) by (cases fuel') (auto split: sum.splits CoreValue.splits option.splits)
  obtain G0 where G: "G = Suc G0" using Suc_le_D[OF CoreTm_ArrayProj.prems(2)[unfolded fuel]] by blast
  obtain G0' where G': "G' = Suc G0'" using Suc_le_D[OF CoreTm_ArrayProj.prems(5)[unfolded fuel']] by blast
  have Qt: "Q t" and Qi: "list_all Q idx" using Q_sub(3) CoreTm_ArrayProj.prems(7) by blast+
  have le: "f0 \<le> G0" "G0 \<le> F" "f0' \<le> G0'" "G0' \<le> F'"
    using fuel fuel' G G' CoreTm_ArrayProj.prems(2,3,5,6) by simp_all
  have eviG: "interp_term_list d G0 s idx = Inr ivs"
    by (rule interp_term_list_more_fuel[OF evi _ le(1)]) simp
  have eviG': "interp_term_list d G0' s' (map tr idx) = Inr ivs'"
    by (rule interp_term_list_more_fuel[OF evi' _ le(3)]) simp
  have eviF: "interp_term_list d F s idx = Inr ivs"
    by (rule interp_term_list_more_fuel[OF evi _ order_trans[OF le(1,2)]]) simp
  have eviF': "interp_term_list d F' s' (map tr idx) = Inr ivs'"
    by (rule interp_term_list_more_fuel[OF evi' _ order_trans[OF le(3,4)]]) simp
  have "ivs = ivs'" by (rule idx[OF Qi eviF eviF'])
  with CoreTm_ArrayProj.IH(1)[OF evt le(1,2) evt' le(3,4) Qt] eviG eviG' ii
  show ?case unfolding tr_simps(4) G G' by (auto split: sum.splits)
next
  case (CoreTm_Cast ty t)
  obtain G0 where G: "G = Suc G0" using interp_term_Inr_le_Suc[OF CoreTm_Cast.prems(1,2)] by blast
  obtain G0' where G': "G' = Suc G0'" using interp_term_Inr_le_Suc[OF CoreTm_Cast.prems(4,5)] by blast
  show ?case
  proof (cases ty)
    case (CoreTy_Array e dims)
    from CoreTm_Cast.prems(1) obtain f0 w where fuel: "fuel = Suc f0"
      and evt: "interp_term d f0 s t = Inr w"
      by (cases fuel) (auto split: sum.splits)
    from CoreTm_Cast.prems(4) obtain f0' w' where fuel': "fuel' = Suc f0'"
      and evt': "interp_term d f0' s' (tr t) = Inr w'"
      unfolding tr_simps(5) by (cases fuel') (auto split: sum.splits)
    have Qt: "Q t" using Q_sub(4) CoreTm_Cast.prems(7) by blast
    have le: "f0 \<le> G0" "G0 \<le> F" "f0' \<le> G0'" "G0' \<le> F'"
      using fuel fuel' G G' CoreTm_Cast.prems(2,3,5,6) by simp_all
    from CoreTm_Cast.IH[OF evt le(1,2) evt' le(3,4) Qt]
    show ?thesis unfolding tr_simps(5) CoreTy_Array G G' by auto
  qed (simp_all add: tr_simps(5) G G')
qed ((rule interp_lvalue_rel_other[OF _ tr_other]; (assumption | simp))+)


end
