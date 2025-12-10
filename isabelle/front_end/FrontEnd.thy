(* FrontEnd implements the unverified stages of the compiler, including: 
   lexer, parser, import resolution ("loader"), and renamer.
  
   The input to the FrontEnd is a list of RawPackages (essentially unparsed Babylon
   code strings), and the output is a list of parsed and renamed BabModules, ready to
   be interpreted by BabInterpreter (TODO) or compiled into C code (TODO).
*)

theory FrontEnd
  imports Main "../bab_loader/BabLoader" "../bab_renamer/BabRenamer"
begin

(* Combined error type for the front end *)
datatype FrontEndError =
  FrontEndError_Loader LoaderError
  | FrontEndError_Renamer RenameError

(* Helper function to sequence a list of sum types where errors are lists *)
(* If all are Inr, return Inr with list of successes *)
(* If any are Inl, return Inl with concatenated list of all errors *)
fun sequence_sum :: "('a list, 'b) sum list \<Rightarrow> ('a list, 'b list) sum"
  where
"sequence_sum [] = Inr []"
| "sequence_sum (x # xs) =
    (case sequence_sum xs of
      Inl errs \<Rightarrow>
        (case x of
          Inl err \<Rightarrow> Inl (err @ errs)
          | Inr _ \<Rightarrow> Inl errs)
      | Inr results \<Rightarrow>
        (case x of
          Inl err \<Rightarrow> Inl err
          | Inr result \<Rightarrow> Inr (result # results)))"

(* Correctness property: if all inputs are successes, sequence_sum returns all the values *)
lemma sequence_sum_all_success:
  assumes "\<forall>x \<in> set xs. \<exists>v. x = Inr v"
  shows "\<exists>vs. sequence_sum xs = Inr vs \<and> map Inr vs = xs"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then obtain v where x_def: "x = Inr v"
    by auto
  from Cons.prems have "\<forall>x \<in> set xs. \<exists>v. x = Inr v"
    by simp
  then obtain vs where ih: "sequence_sum xs = Inr vs" "map Inr vs = xs"
    using Cons.IH by blast
  from x_def ih have "sequence_sum (x # xs) = Inr (v # vs)"
    by simp
  moreover have "map Inr (v # vs) = x # xs"
    using x_def ih(2) by simp
  ultimately show ?case
    by simp
qed

(* Correctness property: if any input is an error, the output is an error *)
lemma sequence_sum_preserves_errors:
  assumes "\<exists>x \<in> set xs. (\<exists>errs. x = Inl errs)"
  shows "\<exists>errs. sequence_sum xs = Inl errs"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "\<exists>errs. x = Inl errs")
    case True
    then obtain errs where x_def: "x = Inl errs"
      by blast
    show ?thesis
    proof (cases "sequence_sum xs")
      case (Inl errs')
      then show ?thesis
        using x_def by simp
    next
      case (Inr vs)
      then show ?thesis
        using x_def by simp
    qed
  next
    case False
    then have "\<exists>x \<in> set xs. (\<exists>errs. x = Inl errs)"
      using Cons.prems by auto
    then obtain errs where "sequence_sum xs = Inl errs"
      using Cons.IH by blast
    then show ?thesis
      by (cases x; simp)
  qed
qed

(* Main front-end function *)
fun compiler_front_end :: "RawPackage list \<Rightarrow> string \<Rightarrow> string \<Rightarrow>
                           (FrontEndError list, BabModule list) sum"
  where
"compiler_front_end rawPkgs rootPkgName rootModName =
  (case load_packages rawPkgs rootPkgName rootModName of
    Inl loaderErrs \<Rightarrow> Inl (map FrontEndError_Loader loaderErrs)
    | Inr loadedModules \<Rightarrow>
      (let renameResults = map (\<lambda>module. rename_module module loadedModules) loadedModules
       in case sequence_sum renameResults of
            Inl renameErrs \<Rightarrow> Inl (map FrontEndError_Renamer renameErrs)
            | Inr renamedModules \<Rightarrow> Inr renamedModules))"

end
