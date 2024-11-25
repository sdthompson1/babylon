// Example 9 -- Tuples and Records.

module Example09

interface {
    function main();
}

import Console;


// The language supports tuple types.
// A tuple is just an ordered collection of values, each value having its
// own type. For example, {bool, i32, i32} is a boolean value and two i32
// values, packaged together.

// This function takes a tuple named "t" of the above type.

function fun1(t: {bool, i32, i32})
{
    // The elements of the tuple can be accessed by using ".0" to access
    // the first element, ".1" to access the second, and so on.

    var i: i32;
    if t.0 {
        i = t.1;
    } else {
        i = t.2;
    }

    // We can create new variables of tuple type, and modify the elements
    // individually.

    var t2: {i32, i32} = {1, 2};
    t2.0 = t2.0 + 1;
    t2.1 = 5;

    assert t2.0 == 2;

    print("The value of t2.1 is ");
    print_i32(t2.1);   // prints 5
    println("");

    // We can also use the "match" statement to match on tuples.
    // Each field can be individually matched against either a specific number,
    // a variable, or the special "_" pattern.

    match t {
    case {false, 1, 3} =>
        // This code runs if t is exactly {false, 1, 3}.
        println("Case A");

    case {b, x, 7} =>
        // This code runs if the last component of t is equal to 7.
        // Within this case, "b" will be equal to t.0 and "x" will be equal
        // to t.1.
        println("Case B");
        print("x = ");
        print_i32(x);
        println("");

    case {_, 5, y} =>
        // This code runs if t.1 is equal to 5. The value of t.0 is ignored,
        // and t.2 is bound to the variable y.
        print("Case C, y = ");
        print_i32(y);
        println("");

    case {b, _, _} =>
        // This code runs in all other cases. t.0 is bound to "b" and the other
        // tuple elements are ignored.
        println("Case D");
    }


    // It is possible to have nested tuples. For example:
    var nested: {i32, i32, {bool, i32, i32}} = {1, 2, t};


    // More pattern matching:
    
    match nested {
    case {x, y, {true, _, _}} =>
        print_i32(x + y);   // prints 3
        println("");

    case {a, b, _} =>
        print_i32(b - a);   // prints 1
        println("");
    }

    // As usual, pattern matches must be exhaustive, so the following would
    // not work (because there is no match if t.0 is true).
    // match t {
    // case {false, _, _} => println("hello");
    // }


    // In a match, it is usually not allowed to modify one of the pattern match
    // variables. For example the following is illegal:
    // match nested {
    // case {_, x, _} =>
    //     x = x + 1;     // Error, can't modify x
    // }

    // However, if the "ref" keyword is used in the match, then the variable
    // *can* be modified, and the change is propagated back to the original
    // tuple. (This is yet another use of "ref"!)

    // For example:

    var t3: {i32, i32, i32} = {1, 2, 3};
    assert t3.0 == 1;
    assert t3.1 == 2;
    assert t3.2 == 3;

    match t3 {
    case { ref x, ref y, _ } =>
        assert x == 1;
        assert y == 2;
        x = 10;   // sets t3.0 to 10
        y = 20;   // sets t3.1 to 20
        
        assert x == 10;
        assert t3.0 == 10;
    }

    print("t3.0 is ");
    print_i32(t3.0);  // prints 10
    println("");
}


// We can also create records.

// A record is like a tuple, but the fields are named.

// For example: {field1: i32, field2: i32} is a record with two fields named
// "field1" and "field2".

function fun2()
{
    // Create a record
    var my_record = {field1 = 100, field2 = 200};

    // We can no longer refer to the fields by ".0" and ".1" etc; instead we
    // use the field names.
    // print_i32(my_record.0);   // doesn't work
    print_i32(my_record.field1);  // works, prints 100
    println("");

    my_record.field2 = 99;

    // We can "match" records by giving the field names.
    // We do not have to match all of the fields, for example the following
    // works:

    match my_record {
    case {field1 = 100} =>
        // This matches when field1=100, and field2 has any value
        println("Case I");

    case {field1 = 99, field2 = 888} =>
        // This matches exactly when field1=99 and field2=888
        println("Case II");

    case _ =>
        // This matches in any other case
        println("Case III");
    }


    // The order of fields is important. So for example,
    // {a:i32, b:i32} and {b:i32, a:i32} are different types.

    // However, within "case" patterns, we can list the fields in any order,
    // so for example the following *does* work even though the pattern lists
    // field1 and field2 in the wrong order.

    match my_record {
    case {field2=x, field1=y} =>
        print("my_record.field1 = ");
        print_i32(y);
        print("\nmy_record.field2 = ");
        print_i32(x);
        println("");
    }


    // Finally, note that records can be compared using ==, but only in
    // verification contexts. Currently the compiler cannot generate runtime
    // code that compares tuples and records for equality. So:

    // This works:
    assert my_record == {field1 = 100, field2 = 99};

    // This is not currently supported:
    // if (my_record == {field1 = 100, field2 = 99}) { ... }

    // Instead we have to do this:
    if my_record.field1 == 100 && my_record.field2 == 99 {
        println("Hello");
    }


    // Another thing you can do is use "record update" syntax.
    // This allows you to create a new record based on an old one.

    // For example:

    // Create a record with six fields.
    var r = {a=1, b=2, c=3, d=4, e=5, f=6};

    // Create a new record based on r. We will change fields a, c and f, and leave
    // the other three fields the same.
    var r2 = {r with a=10, c=30, f=60};

    // r2 is now equal to the following:
    assert r2 == {a=10, b=2, c=30, d=4, e=5, f=60};
}

function fun3()
{
    // As a final point, it is allowed to have a tuple with no elements.
    var v: {} = {};

    // This is a bit of a curiosity perhaps, but sometimes one finds that one 
    // needs a "dummy value", and {} can be a good choice in those situations.
}


// Main program.
function main()
{
    fun1({true, 56, 78});
    fun2();
}
