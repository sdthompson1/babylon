module Datatype
interface {
  datatype T1 = T1;           // Allowed, T1 term name doesn't clash with T1 type name
  
  datatype T2 = T2 | T2;      // Not allowed, T2 term name duplicated

  datatype T3<a,a> = T3;      // Not allowed, 'a' duplicated

  datatype T4<a> = T41 { x: i32, y: a } | T42 { field1: a, field2: bool };  // Correct example

  datatype T5<a> = T51 { x: b };   // Not in scope 'b'
}
