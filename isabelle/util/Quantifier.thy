theory Quantifier
  imports Main
begin

datatype Quantifier = Quant_Forall | Quant_Exists

datatype GhostOrNot = Ghost | NotGhost

datatype VarOrRef = Var | Ref

datatype ShowOrHide = Show | Hide

end
