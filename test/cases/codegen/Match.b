module Match

// Test code generation for pattern matching

interface { function main(); }

import Test;

// The following is a simplified version of the example in "How to compile
// pattern matching" by Jacobs, 2021.

datatype N = Z | S{i32};
datatype E = A{N,N} | M{N,N};

function test(e: E): i32
{
    return match (e) {
        case A{Z,Z} => 1
        case M{Z,x} => 2
        case A{S{x},y} => 3
        case M{x,Z} => 4
        case M{S{x},y} => x
        case x => 6
    };
}

function run_test()
{
    var test1 = test(A{Z,Z});
    Test.print_i32(test1);
    
    var test2 = test(M{Z,S{100}});
    Test.print_i32(test2);
    
    var test3 = test(A{S{100},S{200}});
    Test.print_i32(test3);
    
    var test4 = test(M{S{100},Z});
    Test.print_i32(test4);

    var test5 = test(M{S{100},S{200}});
    Test.print_i32(test5);
    
    var test6 = test(A{Z,S{100}});
    Test.print_i32(test6);
}


// Tests involving tuples.

function test_tuples()
{
    var test_tup =
        match ({{1,2},{3,4}}) {
            case {{10,_},_} => 1
            case {_,{20,_}} => 2
            case _ => 3
        };

    var test_tup2 =
        match ({{S{1},S{2}},{S{3},S{4}}}) {
            case {{S{10},_},_} => 1;  // (new) optional semicolon syntax in match terms
            case {_,{S{x},_}} => x
            case _ => 4
        };

    Test.print_i32(test_tup);
    Test.print_i32(test_tup2);
}


// Match statements

function stmt_test(v: E): i32
{
    match (v) {
    case A{x,y} =>
        match (x) {
        case Z =>
            match ({1,2,3}) {
            case {a,b,c} =>
                return a + b + c;
            }
        case S{n} =>
            return n;
        }
    case M{_,_} =>
        return 99;
    }
}

function stmt_test_2(): i32
{
    match (Z) {
    case _ =>
        match (Z) {
        case S{} => return 333;
        case _   => return 999;
        }
    }
}

function test_statements()
{
    var s1: i32 = stmt_test(A{Z,Z});
    var s2: i32 = stmt_test(A{S{123},Z});
    var s3: i32 = stmt_test(M{S{123},S{456}});
    var s4: i32 = stmt_test_2();
    Test.print_i32(s1);
    Test.print_i32(s2);
    Test.print_i32(s3);
    Test.print_i32(s4);
}

function scope_test(v: E)
{
    // Regression test: This was previously crashing the compiler,
    // due to a scope not being closed properly
    match v {
    case A(_) =>
        var a = 1;
    case M(_) =>
        var b = 2;
    }

    match v {
    case A(_) =>
        var a = 1;
    case _ =>
        var a = 2;
    }
}

function empty_case()
{
    // regression test - the NULL stmt after the => was causing a crash
    match ({1,2,3}) {
    case {_,_,_} =>
    }
}

function main()
{
    run_test();
    test_tuples();
    test_statements();
    scope_test(A{Z,Z});
    empty_case();
}
