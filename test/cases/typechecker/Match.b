module Match
interface {}

datatype ABC = A {fld1: i32, fld2: bool} |
               B {i8, i64} |
               C;

datatype DE = D {abc: ABC, b: bool } |
              E {e: bool};

const abc: ABC = B{ i8(100), i64(2000) };
const de: DE = D{abc=abc, b=false};

const test1: i32 =
  match (abc) {
    case A {fld1=x} => x
    case B {_, y} => if y==0 then 1 else 2
    case _ => 1000
  };

const test2: bool =
  match (D{ abc=A{ fld1=1, fld2=true}, b=false}) {
    case D{ abc=A{ fld1=x, fld2=y} } => y
    case D{ abc=_, b=x } => x
    case E{ e = y } => y
  };

// Type error, expecting bool, got i32
const test3: bool =
  match (abc) {
    case A {fld1=x} => x
  };

// Type error, mismatching arms
const test4 =
  match (de) {
    case D{abc=x, b=y} => x
    case E{e=x} => x
  };

// Error, no arms
const test5 = match (1) {};

// Integer and boolean examples
const test6: bool =
  match (1) {
    case 1 => true
    case _ => false
  };

const test7: bool =
  match (1) {
    case E{} => false  // Type mismatch
  };

const test8: bool =
  match (de) {
    case E{} => false  // Ok
  };

const test9: i32 =
  match (false) {
    case true => 1
    case false => 0
  };


const test10: i32 =
  match (abc) {
    case false => 0    // error, wrong pattern type
    case 123 => 0      // ditto
    case {a,b,c} => 0  // ditto
    case D{} => 0      // 'D' is not a valid constructor for ABC
  };

// tuple pattern
const test_tuple: i32 =
  match ({1,true}) {
    case {2,false} => 0
    case {x,y} => x
  };

const test_tuple_mismatch: i32 =
  match ({1,true,de}) {
    case {false,x,y} => 100    // error, 'false' does not match '1'
  };


// Polymorphic example
datatype Poly<a> = P1 {a} | P2{a, i32};

const test_poly: i32 =
  match (P1<i32>{100}) {
    case P1<i32>{_} => 0
    case P2<i32>{y, _} => y
  };
