theory LinkError
  imports Main
begin

(* ========================================================================== *)
(* Link errors                                                                *)
(* ========================================================================== *)

datatype LinkError =
    LinkConflict "string list"   (* Multiple definition (the same name is defined in more
                                    than one module);
                                    payload = the names defined more than once *)
  | LinkCycle "string list"      (* The abstract-type dependency relation is cyclic;
                                    payload = the type names involved in cycles *)
  | LinkCapture "string list"    (* An abstract type resolved by some module in the link
                                    has the same name as a bound type parameter (an
                                    FI_TyArgs entry or a data constructor's type-variable
                                    list) of some module in the link. The renamer's
                                    dotted/undotted naming discipline means this never
                                    happens in practice; the link-time check turns a
                                    would-be soundness hole into a reported error.
                                    payload = the colliding names. *)

end
