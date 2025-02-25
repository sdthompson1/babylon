// Example 13 -- Misc Topics.

module Example13

interface {
    function main();
}

import Console;


// -------------------------------------------------------------------

// Match and If Expressions:

function fun1(x: i32)
{
    // We explained before how if statements and match statements work.

    // What we didn't mention is that match and if can also be used as
    // expressions.

    // We will just give some examples without giving a full explanation:

    var v1 = (if x < 10 then x + 100 else x - 100);

    var v2 =
      (match v1 {
         case 100 => 25
         case 200 => 50
         case 300 => 75
         case _   => 0 });

    print_i32(v1);
    println("");
    print_i32(v2);
    println("");
}



// -------------------------------------------------------------------

// Let:

// Sometimes the "let" expression can be useful.

// "let x = EXPR1 in EXPR2" means to temporarily assign EXPR1 to a variable
// x, and then evaluate EXPR2 given that value of x.

// Here is a silly example:

function let_test(x: i32)
    requires 0 < x < 40000;   // this prevents x*x overflowing
    requires (let xsq = x*x in xsq == 49 || xsq == 81 || xsq == 100);
{
    // The precondition implies x must be 7, 9 or 10!
    assert x == 7 || x == 9 || x == 10;
}



// -------------------------------------------------------------------

// Use:

// To prove an existential statement, sometimes it is necessary to tell
// the prover which value to use.

// For example:

// Using our old friend "is_prime":
ghost function is_prime(n: u32): bool
{
    return n >= 2 &&
        (forall (f: u32) 1 < f < n ==> n % f != 0);
}

// Supposing we wanted to prove there exists a prime greater than 1000.
function exist_test()
{
    // The solvers are unable to prove the following statement, which is
    // perhaps surprising, since they are able to prove is_prime(1009).
    // assert exists (x: u32) x > 1000 && is_prime(x);

    // The solution is to tell the verifier that it can use x=1009 as
    // a possible solution.
    assert exists (x: u32) x > 1000 && is_prime(x)
    {
        use 1009;
    }
}



// -------------------------------------------------------------------

// Strings:

// The language doesn't really have any proper support for strings,
// however, a u8 array can be considered to be a string (if it is interpreted
// as a sequence of ASCII or UTF-8 values).

// The language does therefore allow a string literal to be interpreted
// as a (constant) array of u8 values. A string literal cannot be copied,
// but you can "ref" it.

// For example:

function fun2()
{
    // This is not allowed.
    // var s = "Hello, world!\n";

    // This is allowed. s is effectively a pointer to some read-only
    // piece of memory containing the given string.
    ref s = "Hello, world!\n";  

    // We can take the sizeof a string, just like any other array.
    // sizeof(s) is 15 (13 text characters, the newline, and an implicit null byte
    // at the end of the string).
    assert sizeof(s) == u64(15);

    // We can also print it, via the reference.
    print(s);

    // We could also pass 's' to a function that takes a u8[] argument
    // (but not a "ref u8[]" argument, because that would imply that the
    // function was able to change the string, but 's' is read-only).
}



// -------------------------------------------------------------------

// Assume:

// "assume" instructs the verifier to assume that something is true,
// without proof.

// There are two cases where this is useful. The first is where we are
// trying to do a proof, and we want to skip some step in the proof
// for now, and come back to fill it in later.

// In this case an assume statement is like a "TODO".

// For example, in Example 7 we had "modulo_lemma", which concluded that
// a % c == 0 under certain assumptions. If we wanted to, we could have
// written modulo_lemma like this:

ghost function modulo_lemma(a: u32, b: u32, c: u32)
    requires b != 0 && c != 0;
    requires a % b == 0;
    requires b % c == 0;
    ensures a % c == 0;
{
    // TODO: add proof here
    // For now just assume the result
    assume a % c == 0;
}

// We could then go and finish off our main proof, using "modulo_lemma" as
// needed. If that was successful, then we could come back and replace the
// "assume" in modulo_lemma with a proper proof.

// In general this is often a good strategy -- if we think we need some lemma,
// then we just "assume" the lemma to begin with, then confirm that we can
// actually solve the main problem using this lemma, before going back to
// complete the proof of the lemma. (There is nothing worse than spending
// hours proving some lemma, only to discover that it isn't actually useful
// in solving the main problem!)


// Of course, one does have to be very careful not to assume something that is
// untrue. If this is done, the verifier will be able to use the untrue
// statement to prove anything. For example, the following program contains
// a division by zero, but the verifier doesn't flag up this error, because
// of the incorrect assume statement.

function divide_by_zero()
{
    assume 1 + 1 == 3;   // This is not true, obviously

    // The verifier will try to prove that the following statement does NOT
    // divide by zero (like it does for any division expression).
    // The proof will (unexpectedly) succeed, because the verifier is able
    // to use the false assumption (above) to do a fake "proof by contradiction".
    var v = 1/0;

    // To fix this, we can uncomment the above "assume" statement and
    // then see that the error is now reported as expected.

    // For this reason it is recommended NOT to use "assume" in production
    // code, if at all possible.
}


// A second use of "assume" is to assume something that we know to be true,
// but which we cannot prove inside the system.

// For example, the following program looks like it can divide by zero, but
// actually, by Fermat's last theorem, it never actually will divide by zero.

function assume_test(x: i32, y: i32, z: i32)
    requires 0 < x < 1000;
    requires 0 < y < 1000;
    requires 0 < z < 1000;
{
    // The following assert will fail, because (not surprisingly!) the
    // SMT solvers are not clever enough to be able to prove Fermat's last
    // theorem (or even this special case of it) on their own.

    // assert x*x*x + y*y*y != z*z*z;

    // However, below we have some code that divides by zero in the case where
    // x*x*x + y*y*y == z*z*z. To verify the code, therefore, the verifier
    // must prove that x*x*x + y*y*y != z*z*z, which it is not able to do.

    // To work around this, we can assume the result instead.

    assume x*x*x + y*y*y != z*z*z;

    var v: i32;
    if x*x*x + y*y*y == z*z*z {
        v = 0;
    } else {
        v = 1;
    }
    v = x / v;    // (Division by zero if x*x*x + y*y*y == z*z*z)


    // Of course, it is important not to over-use "assume" because of the
    // risk of accidentally assuming something that is not true (as in the
    // divide_by_zero example above). Therefore, any uses of "assume" should
    // be kept to a minimum, if at all possible.


    // Note that if one did want to avoid "assume", then an alternative might
    // be to generate runtime errors instead. For example instead of

    // assume P;
    // do something that relies on P being true;

    // one might write

    // if P {
    //     do something;
    // } else {
    //     display an error message to the user;
    // }

    // This way, if our assumption P does turn out to be false, then the user
    // gets an error message, but at least the integrity of the verification
    // is not compromised.
}


function main()
{
    fun1(200);
    fun2();
}
