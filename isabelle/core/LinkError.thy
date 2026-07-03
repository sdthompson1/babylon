theory LinkError
  imports Main
begin

(* ========================================================================== *)
(* Link errors                                                                *)
(* ========================================================================== *)

datatype LinkError =

  (* Multiple definition: the same name is defined in more than one module.
     Payload = the names defined more than once. *)
    LinkConflict "string list"

  (* Cyclic type definitions: the abstract-type dependency relation is cyclic.
     Payload = the type names involved in cycles. *)
  | LinkCycle "string list"

  (* Variable capture: an abstract type has the same name as one of the type parameters
     of a generic function or datatype.
     This should never happen for modules created by the renamer (because of the
     dotted/undotted naming discipline) but might happen for modules created by
     other means.
     Payload = the colliding names. *) 
  | LinkCapture "string list"

  (* Ghost resolution error: one module declares a non-ghost (runtime) abstract type, and
     another module resolves it to a ghost type.
     Payload = the offending abstract-type names. *)
  | LinkGhostResolution "string list"

end
