theory Quantifier
  imports Main
begin

(* This file defines some miscellaneous types that are shared between the Core and Bab
   syntaxes. It's called "Quantifier" for historical reasons (it actually contains more than
   just quantifiers). *)

datatype Quantifier = Quant_Forall | Quant_Exists

datatype GhostOrNot = Ghost | NotGhost

datatype VarOrRef = Var | Ref

datatype ShowOrHide = Show | Hide

end
