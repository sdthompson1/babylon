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

end
