
// This is the third demonstration program for the Babylon language.

// In this file we will explain some of the statements that can be used in
// the language. Perhaps the most interesting is the "while" statement, in
// which we introduce the concept of loop invariants.


module Demo_03_Statements

interface {
    function main();
}

import ExampleLib;


function fun1(): i32
{
    // We have seen the return statement already:
    return 100;
}

function fun2()
{
    // This creates a variable "x", of type i32, and sets it to 42.
    var x: i32 = 42;

    // Note that the available (scalar) types are:
    // i8, i16, i32, i64 -- signed integers of 8, 16, 32 or 64 bits
    // u8, u16, u32, u64 -- unsigned integers
    // bool -- booleans (true or false).
    // There are also aggregate types (records, tuples and so on) -- we will
    // see those later.


    // Example of a boolean variable:
    var b: bool = true;

    // Some boolean operations:
    var b1 = b || true;     // sets b1 to true; || means OR
    var b2 = b && false;    // sets b2 to false; && means AND
    var b3 = !b;            // sets b3 to false; ! means NOT


    // Here no type is given, so the type is inferred from the given
    // initial value. Numeric values are assigned type "i32" by
    // default, so y receives the type "i32" here.
    var y = 42;

    // Variables can also be given a default value. (For integers the default
    // is zero, and for booleans the default is false.)
    var z: i32;

    // The following, however, is illegal, because there is no way to know
    // what type "w" should have.
    // var w;

    // Once a variable is created it can be assigned a new value:
    x = x + 1;    // sets x to 43

    // There is also a "swap" statement, allowing two variables to
    // be exchanged, provided they have the same type:
    swap x, y;    // sets x to 42 and y to 43

    // We've seen function calls already:
    print_i32(x);
    print_string("\n");
    print_i32(y);
    print_string("\n");
    print_i32(z);
    print_string("\n");

    // Note that if a function returns a value, it is an error to ignore
    // the return value. So for example:
    x = fun1();       // OK, return value of fun1() is being used
    y = x + fun1();   // Also OK
    // fun1();        // Illegal, return value of fun1() is being ignored    
}

function fun3(x: i32)
    requires 0 < x < 100;
{
    // The language has an "assert" statement. An assert statement means the
    // programmer is claiming that a certain condition is true at a certain
    // point in the program. Asserts will be proved by the verifier.

    // For example, the following will succeed:
    assert 1 + 2 == 3;
    // (The automatic provers will be asked to prove that 1 + 2 == 3, which
    // they will succeed in doing.)

    // But the following will produce a verification error:
    // assert 1 + 2 == 5;

    // The verifier can make use of the "requires" conditions in its proofs.
    // So for example, the following assert will succeed, because the verifier
    // knows that 0 < x < 100 in this function (and it passes this information
    // on to the automatic provers).
    assert 1 < x*x + 2*x + 1 < 10201;

    // Note: unlike in languages such as C, the Babylon assert statement does
    // not cause any check to be made at run-time. Asserts are only used by
    // the verifier.
}

function fun4(x: i32)
{
    // The language has "if" statements.
    // Note that unlike C (but like Rust), there is no need to put brackets
    // around the condition. For example:
    if x > 100 {
        print_string("x is greater than 100\n");
    } else {
        print_string("x is less than or equal to 100\n");
    }

    // If proofs are required, then the "if" condition is assumed to be true
    // during the "then" branch of the if, and false during the "else" branch.
    // For example:
    if 0 < x < 100 {

        // This can be proved, because we know that if we get into this branch
        // of the "if", then x must be less than 100.
        assert 2*x < 200;
    
        // This works -- the precondition of "fun3" can be proved, because it
        // is guaranteed by the "if" statement.
        fun3(x);

    } else {
        // This can be proved, because we know that the "if" condition was
        // false, if we reach this part of the code.
        assert x <= 0 || x >= 100;
    }
}

function fun5()
{
    // Now let's consider "while" loops.
    
    // In Babylon, every while loop must include a "decreases" clause. This is
    // used to prove that the loop terminates. For example:

    var i: i32 = 10;
    while i > 0
        decreases i;
    {
        print_i32(i);
        print_string("\n");
        i = i - 1;

        // At this point, the verifier will prove that the decreases-value
        // ("i" in this case) is lower than it was at the start of the loop.
        // (If the proof fails the program will be rejected.)

        // Since the i32 type (like all the integer types) has a lowest
        // possible value, this guarantees that the loop will terminate -- "i"
        // cannot go on decreasing forever.
    }


    // For loops that count "upwards" a common trick is to use the ~ operator
    // (bitwise complement). (Whenever i increases, ~i decreases, and vice
    // versa.)
    i = 0;
    while i < 10
        decreases ~i;
    {
        print_i32(i);
        print_string("\n");
        i = i + 1;
    }


    // We can also state "invariants". An invariant is a condition that is
    // true both on entry to, and exit from, the loop.

    // The verifier will prove that the invariant is true before the loop
    // is entered.

    // During the loop itself, the verifier will assume that the invariants are
    // true at the start of the loop, and then it will prove that the
    // invariants are still true at the end of the loop.

    // Here is an example:

    i = 0;
    var x: i32 = 10;
    var c: i32 = 20;
    var z: i32 = 100;

    while i < 10
        // We will increase i (therefore decrease ~i) on every loop iteration
        decreases ~i;

        // The following says that i will always be between 0 and 10.
        // The invariant must hold both during the loop, and immediately
        // after the loop exits (that is why we must say "<= 10" rather
        // than "< 10").
        invariant 0 <= i <= 10;

        // The following says that we will keep x equal to 10-i during
        // the loop.
        invariant x == 10 - i;

        // The following says that z will always remain >= 0 during
        // the loop.
        invariant z >= 0;

        // Note: The verifier will prove all these invariants are true
        // before the loop begins. For example if you change the initial
        // value of z (above) to -100 instead of 100, then the verification
        // will fail.

    {
        // At this point the verifier knows that the invariants are all true,
        // and also that the "while-condition" (i < 10) is true (because we
        // would not have entered the loop otherwise). It is therefore
        // possible to prove the following:
        
        assert 0 <= i < 10;

        // (This follows directly from the invariant 0 <= i <= 10 and the
        // condition i < 10.)


        // The verifier is aware of which variables are modified during the
        // loop and which are not. For example, the following assert succeeds,
        // for the following reasons:
        // (1) c is equal to 20 before the loop begins.
        // (2) c is not modified during the loop (as we can see by inspecting
        //     the code below), therefore the verifier deduces that c is always
        //     equal to its starting value (20) on every loop iteration.
        assert c == 20;
        

        // However, the following assert will fail, for the following reasons:
        // (1) z is modified during the loop, therefore the verifier is not
        //     allowed to assume anything about z's value, other than what may
        //     be deduced from the invariants.
        // (2) The only thing the invariants tell us about z is that z >= 0.
        //     This is not sufficient to prove that z == x.
        // assert z == x;

        // The irony is that z *is* actually equal to x at this point
        // (as can be seen by inspecting the code below; the loop always
        // sets z equal to x). However, the verifier is not able to prove
        // this, for the reasons stated above. If we needed to prove that
        // z == x at this point, then we would have to add "invariant z == x"
        // to the list of invariants above.

        // (Coming up with suitable invariants is a major element of loop
        // design. If the invariants are too strong, they will not be
        // provable, but if they are too weak, they will not be sufficient to
        // prove what we need to prove within the loop itself.)


        // Now (at last!) we write the code for what the loop actually does:
        i = i + 1;
        x = x - 1;
        z = x;


        // At this point the verifier will prove that the invariants are
        // still true (and, of course, that the "decreases" value has
        // actually decreased).
    }


    // Final note: The "while" loop is the only available looping construct
    // at the moment. At some point I plan to add "for" loops as well, but for
    // now, the effect of a "for" loop can be obtained by using a "while" loop
    // instead.
}


function sum_of_numbers_upto(n: i32): i32
    requires n >= 0;
    requires n <= 46340;
{
    // Here we will demonstrate one application of loop invariants.
    // We will prove that the sum of the numbers from 1 to n is equal to
    // n * (n+1) / 2.

    // (Note: It turns out that n=46340 is the highest value of n at which
    // this formula can be evaluated, without overflowing the range of an i32.
    // That is why "requires n <= 46340" was used above.)


    // We will count "i" from 1 upto n, and maintain the sum in "sum".

    // Initially i is zero, and sum is zero (because the sum of the first zero
    // numbers is zero).

    var i: i32 = 0;
    var sum: i32 = 0;

    while i < n
        invariant 0 <= i <= n;
        invariant sum == i * (i+1) / 2;
        decreases ~i;
    {
        // Here we know that sum == i * (i+1) / 2 (this is the loop invariant).

        // We now increase i by one, and add the next value of "i" into the
        // sum.

        i = i + 1;
        sum = sum + i;

        // For the purposes of the demo, we print out the values of i and
        // sum at every iteration.

        print_string("The sum from 1 to ");
        print_i32(i);
        print_string(" is ");
        print_i32(sum);
        print_string("\n");

        // The verifier now asks the SMT solvers to prove that the invariant
        // is still true at this point in the code.

        // For those interested in the details, the SMT problem that is
        // formulated is roughly the following:

        // (1) Let i_old, sum_old, i_new, sum_new, n be integers.
        // (2) Assume n >= 0 and n <= 46340 (these are the "requires"
        //     conditions; because n is not modified during the loop, the
        //     verifier knows that it is safe to bring these conditions into
        //     the loop, even though they are not explicitly stated as
        //     invariants).
        // (3) Assume that 0 <= i_old <= n and
        //     sum_old == i_old * (i_old + 1) / 2
        //     (these are the stated loop invariants).
        // (4) Assume that i_old < n (this is the "while-condition").
        // (5) Assume that i_new = i_old + 1, and sum_new = sum_old + i_new
        //     (this describes the effect of the assignment statements above).
        // (6) Prove that 0 <= i_new <= n.
        // (7) Also prove that sum_new == i_new * (i_new + 1) / 2.

        // Proving condition (7) is a matter of doing some algebra, which
        // the SMT solvers are more than capable of, so they return a result
        // indicating that the proof has been successful.
    }


    // Note that after a loop, the verifier knows that the loop invariants
    // are true, but the while-condition is false. Therefore the following
    // asserts are provable:
    assert i == n;
    assert sum == n * (n+1) / 2;


    return sum;
}


function fun6(i: i32)
{
    // The next statement we want to describe is "match".

    // The match statement will jump to a different "case" depending on the
    // value of a given expression. For example:

    match i {
    
    case 1 =>
        print_string("i is 1\n");
        
    case 2 =>
        print_string("i is 2\n");
        
    case 3 =>
        print_string("i is 3\n");

    // If multiple cases match, only the first is executed. Therefore the
    // following code will never be reached.
    case 3 =>
        print_string("This will never execute\n");

    // We can use "case _" as a "wildcard" -- this will match if none of
    // the previous cases matched.
    case _ =>
        print_string("i is neither 1, 2 nor 3\n");
    }


    // The verifier will check that at least one of the cases matches, and
    // raise an error if not. (Therefore when matching an integer, it is
    // almost always necessary to include a "case _".)


    // It's also possible to match on a boolean expression, but this is
    // pretty much equivalent to an "if" statement:

    match i > 10 {
    case true =>
        print_string("i is greater than 10\n");
    case false =>
        print_string("i is less than or equal to 10\n");
    }


    // The verifier can use the results of a match in its proofs; so for
    // example, the following asserts will succeed.
    match i {
    case 1 => assert i == 1;
    case _ => assert i != 1;
    }


    // When we come to look at datatypes and records (in a future demo),
    // we will see some more interesting uses of the "match" statement.
}


function main()
{
    fun2();
    fun3(99);
    fun4(10);
    fun5();

    var i = sum_of_numbers_upto(25);

    // Note that the following assert would fail, because the verifier (in this
    // case) is unable to "look inside" the definition of "sum_of_numbers_upto"
    // to see what it returns:
    // assert i == 25 * 24 / 2;

    // (In general, if a function is being used in an assert, or any other
    // proof, the verifier will try to pass along the definition of the
    // function to the SMT solvers. For example if f(x) is defined to
    // return x + 1, then the verifier would pass along "f(x) == x + 1" as
    // an axiom to the solvers; the solvers would then be able to use that fact
    // in their proofs. However, this is not always possible. If the function
    // is too complex, or if it contains a while loop, then the verifier will
    // not pass the full definition to the solver. In that case, all the solver
    // would know is that f is "some" function from integers to integers, and
    // that any "ensures" conditions are met, but nothing else about what the
    // function does.)

    // (In this case, one option would be to add "ensures 
    // return == n * (n+1) / 2" to the definition of "sum_of_numbers_upto";
    // this condition would then be passed to the SMT solvers, and the
    // above assert would become provable.)


    fun6(2);
}


// To verify this example:
//   babylon -V Demo_03_Statements.b

// To run this example:
//   babylon -c Demo_03_Statements.b
//   gcc Demo_03_Statements.c ExampleLib.c example_lib.c
//   ./a.out
