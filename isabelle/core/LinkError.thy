theory LinkError
  imports Main
begin

(* ========================================================================== *)
(* Link errors                                                                *)
(* ========================================================================== *)

datatype LinkError =
    LinkConflict   (* multiple definition (the same name is defined in more than one module) *)
  | LinkCycle      (* the abstract-type dependency relation is cyclic *)

end
