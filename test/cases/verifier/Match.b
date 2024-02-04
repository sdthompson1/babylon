module Match
import Test;
interface {}
  datatype Color = Red | Green | Blue;
  datatype D<a> = D { a };

  function f1(d: D<Color>): i32
  {
    return match (d) {   // Error: non-exhaustive
      case D<Color>{Red} => 1
      case D<Color>{Green} => 2
    };
  }

  function f2(d: D<Color>): i32
  {
    return match (d) {   // OK: All cases covered
      case D<Color>{Red} => 1
      case D<Color>{Green} => 2
      case D<Color>{Blue} => 3
    };
  }

  // This is OK, even though only one case provided, because the
  // verifier can see that the scrutinee matches the given pattern
  function f3() { var v = 
    match (D<Color>{Green}) {
      case D<Color>{Green} => 1
    }; }


  // Integer case, non-exhaustive
  function f4(i: i32): bool
  {
    return match (i) {
      case 1 => true
      case 2 => false
      case 3 => false
    };
  }

  // Integer case, exhaustive
  function f5(i: i32): bool
    requires 1 <= i <= 3;
  {
    return match i {
      case 1 => true
      case 2 => false
      case 3 => false
    };
  }


  // Checking that the verifier understands the results of
  // pattern matching
  function f6(d: D<i32>)
  {
    var i: i32 =
      match (d) {
        case D{1} => 2
        case D{_} => 1
      };
    assert (i == 1 || i == 2);   // Correct
    assert (d != D<i32>{i});     // Correct
    assert (i == 3);             // Fails
  }


  // Regression tests (i.e. previous bugs that were fixed)
  datatype N = Z | S{i32};
  datatype E = A{N,N} | M{N,N};
  function regression_test_1() { var v =
    match (A{Z,Z}) {
      case A{Z,Z} => 1
      case A{Z,Z} => 2
    }; }

  function regression_test_2() { var v =
    match ({1,true}) {
      case {2,true} => 0
    }; }



  // Match Statements
  function s1()
  {
    var x: i32 = 0;
    var y: i32 = 1;
    match (D<i32>{100}) {
      case D{z} =>
        x = x + z;
        y = y + z;
    }
    assert (x == 100);
    assert (y == 101);
    assert (y == 102);   // Fails
  }

  function s2()
  {
    var x: i32 = 25;
    match (true) {
      case true => x = x + 1;
    }
    assert (x == 26);
    assert (x == 27);  // Fails
  }

  function s3()
  {
    var x: i32 = 100;
    match (1) {
      case 1 => x = 10;
      case 2 => x = 20;
    }
    assert (x == 10);
  }

  function s4()
  {
    var x: i32 = 24;
    match (Red) {          // Error: non-exhaustive match
      case Green => x = 10;
    }
    assert (x == 24);
  }

  function s5()
  {
    match (1/0) {     // Error: scrutinee fails to verify
      case 1 =>
        var x = 1/0;    // No error, arms are not checked if scrutinee fails.
    }
  }


  // Match in requires and ensures
  function attrs(x: i32): i32
    requires (match (x) { case y => y < 1000 });
    ensures (match (return) { case y => y == x + 1 });
  {
    return x + 1;
  }


  // "Ref" pattern
  datatype Foo = Foo(i32) | Bar(i32);

  function ref_pat_1()
  {
    var x = Bar(20);
    match (x) {
      case Foo(ref r) => r = 10;
      case Bar(_) =>
    }
    assert (match (x) { case Foo(y) => y } == 10);    // Error, non exhaustive match
  }

  function ref_pat_2()
  {
    var x = Foo(20);
    match (x) {
      case Foo(ref r) => r = 10;
      case Bar(_) =>
    }
    assert (match (x) { case Foo(y) => y } == 10);    // Success
  }

  function ref_pat_3(ref a: i32[])
      requires sizeof(a) == u64(10);
      requires forall (i:u32) i < 10 ==> a[i] == 0;
  {
    // Modifying an array element through a ref-pattern-match
    match (a[3]) {
        case ref r => r = 25;
    }

    assert (a[3] == 25);      // OK
    assert (forall (i:u32) i < 10 && i != 3 ==> a[i] == 0);    // OK
  }

  function ref_pat_4(): i32
  {
    var x = Foo(20);
    match x {
    case Foo(ref r) =>
      r = 55;    // OK
      x = Foo(56);
      r = 57;    // OK, x is still Foo
      x = Bar(10);
      return r;  // Error, x is no longer Foo so r is invalid
    }
  }
