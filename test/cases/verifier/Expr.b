module Expr
interface {}
  // If-then-else
  // Error reported in ite3 because the "bad" branch is executed, but not
  // in ite1 and ite2 because the "bad" branch is unreachable in those cases.
  const ite1: i32 = if 1 < 2 then 100 else 1/0;
  const ite2: i32 = if 1 > 2 then 1/0 else 100;
  const ite3: i32 = if 1 < 2 then 1/0 else 100;
  const ite4: i32 = if 1/0 < 0 then 1 else 0;

  // Similar results for &&, ||, ==>, <==.
  const and_error: bool = true  &&  1/0 == 0;
  const and_ok:    bool = false &&  1/0 == 0;
  const or_error:  bool = false ||  1/0 == 0;
  const or_ok:     bool = true  ||  1/0 == 0;
  const imp_error: bool = true  ==> 1/0 == 0;
  const imp_ok:    bool = false ==> 1/0 == 0;
  const imp_by_error: bool = 1/0 == 0 <== true;
  const imp_by_ok:    bool = 1/0 == 0 <== false;

  // Handling of verify failures under certain operators etc.
  const unop_fail: i32 = - (1/0);
  const let_rhs_fail: i32 = let x = 1/0 in x+1;
