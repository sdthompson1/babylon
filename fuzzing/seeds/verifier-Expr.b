module Main
interface {}

function f()
{
  // If-then-else
  // Error reported in ite3 because the "bad" branch is executed, but not
  // in ite1 and ite2 because the "bad" branch is unreachable in those cases.
  var ite1: i32 = if 1 < 2 then 100 else 1/0;
  var ite2: i32 = if 1 > 2 then 1/0 else 100;
  var ite3: i32 = if 1 < 2 then 1/0 else 100;
  var ite4: i32 = if 1/0 < 0 then 1 else 0;

  // Similar results for &&, ||, ==>, <==.
  var and_error: bool = true  &&  1/0 == 0;
  var and_ok:    bool = false &&  1/0 == 0;
  var or_error:  bool = false ||  1/0 == 0;
  var or_ok:     bool = true  ||  1/0 == 0;
  var imp_error: bool = true  ==> 1/0 == 0;
  var imp_ok:    bool = false ==> 1/0 == 0;
  var imp_by_error: bool = 1/0 == 0 <== true;
  var imp_by_ok:    bool = 1/0 == 0 <== false;

  // Handling of verify failures under certain operators etc.
  var unop_fail: i32 = - (1/0);
  var let_rhs_fail: i32 = let x = 1/0 in x+1;
}
