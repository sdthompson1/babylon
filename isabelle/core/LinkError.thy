theory LinkError
  imports Main
begin

(* ========================================================================== *)
(* Link errors                                                                *)
(* ========================================================================== *)

datatype LinkError =
    LinkConflict            (* two substitutions disagree on a shared abstract type *)
  | LinkCycle               (* the abstract-type dependency relation is cyclic *)
  | LinkDefinitionMismatch  (* a declaration/definition name resolves to
                               non-identical entries in two modules *)

end
