
// This is an example program which will compute the greatest common
// divisor (GCD) of two numbers using Euclid's algorithm. We also
// include proofs that the algorithm is correct.


module Demo_14_GCD

interface {
    function main();
}

import ExampleLib;
import Int;


// We will say that "a divides b" (or "a | b" or "divides(a,b)")
// whenever b % a == 0.

// Make a ghost function that encapsulates this definition.
// (We consider only the cases a != 0 and b != I32_MIN.)

ghost function divides(a: i32, b: i32): bool
    requires a != 0;
    requires b != I32_MIN;
{
    // Return true if a divides b, or b % a == 0.
    return b % a == 0;
}


// Alternatively, we could say that a divides b if and only if
// there exists a value "k" such that b == k * a.

// We would like to prove that this definition is equivalent to
// the previous one.

// The following ghost function does one direction of the proof
// (namely that if a divides b, then b == k * a for some k).

ghost function divides_necessary(a: i32, b: i32)
    requires a != 0 && b != I32_MIN;
    requires divides(a, b);
    ensures exists (k:i32) can_mul_i32(k, a) && b == k * a;
{
    // Unfortunately the SMT solver can't do the proof on its own, but
    // if we tell it to use "b/a" as the value of k, then it works!
    assert exists (k:i32) can_mul_i32(k, a) && b == k * a
    {
        use b/a;
    }
}

// Now we do the opposite direction -- that if b == k * a for some k,
// then a divides b.

ghost function divides_sufficient(a: i32, b: i32)
    requires a != 0 && b != I32_MIN;
    requires exists (k:i32) can_mul_i32(k, a) && b == k * a;
    ensures divides(a, b);
{
    // This time, the SMT solver can prove the result by itself -- no
    // explicit proof is required.
}


// Moving on, we now want to prove the following lemma about
// divisibility:

// If a|b, and a|c, then a|(b*x + c*y) (for any x and y).

// This can be stated as follows:

ghost function divides_linear(a: i32, b: i32, c: i32, x: i32, y: i32)
    requires a != 0;
    requires b != I32_MIN;
    requires c != I32_MIN;

    // We need to restrict the values of b, c, x, y, to prevent
    // integer overflows.
    requires can_mul_i32(b, x);
    requires can_mul_i32(c, y);
    requires can_add_i32(b*x, c*y);
    requires b * x + c * y != I32_MIN;

    // The hypotheses of the theorem.
    requires divides(a, b);
    requires divides(a, c);

    // The conclusion of the theorem.
    ensures divides(a, b*x + c*y);
{
    // Again the solver cannot prove this on its own, so we need to give
    // it some help.

    // The first thing is to separate out the case a == -1 and do that
    // separately.

    if (a == -1) {
        // When a == -1 the theorem is trivial (-1 divides anything), so
        // nothing further is needed here.

    } else {

        // The proof now goes as follows:

        // Because a | b, we know (by theorem divides_necessary) that
        // there exists kb such that b == kb * a.

        // This can be established by calling the divides_necessary
        // function (which lets the verifier know that we want to
        // use the postconditions of that function later in the proof):

        divides_necessary(a, b);

        // Now that we have convinced the verifier that there exists a kb
        // such that b == kb * a, we can use "obtain" to actually find
        // such a value.

        obtain (kb:i32) can_mul_i32(kb, a) && b == kb * a;


        // We can use exactly the same procedure to obtain a value
        // "kc" such that c == kc * a.

        divides_necessary(a, c);
        obtain (kc:i32) can_mul_i32(kc, a) && c == kc * a;


        // It is now pretty easy to see that there exists a "k"
        // such that b*x + c*y == k*a. This can be proved by
        // setting k == kb*x + kc*y.

        assert (exists (k:i32) can_mul_i32(k, a) && b * x + c * y == k * a) {
            use kb * x + kc * y;
        }


        // (Side note: If a == -1, the above expression would be
        // problematic because kb * x might overflow. An example is
        // a = -1, b = I32_MIN/2, c = 1, x = 2, y = 1.
        // These values satisfy all of the "requires" conditions
        // above, but we would have kb = -I32_MIN/2, and kb * x
        // would be -I32_MIN which is I32_MAX + 1, i.e. an
        // overflow. That is the reason why a==-1 has to be
        // treated as a special case.)


        // Anyway... having established that the required "k" exists,
        // we can now invoke "divides_sufficient" to show that
        // divides(a, b*x + c*y) must be true.

        divides_sufficient(a, b*x + c*y);
    }
}


// We now want to prove the following lemma:

// Given a > b > 0, we have that:
//   k|(a%b) && k|b if and only if k|a && k|b.

// This says that the set of divisors of a and b, is exactly the same as the
// set of divisors of a%b and b.

ghost function euclid_lemma(k: i32, a: i32, b: i32)
    requires k != 0;
    requires a > b > 0;
    ensures divides(k, a % b) && divides(k, b) <==> divides(k, a) && divides(k, b);
{
    // We can split the proof into "==>" and "<==" cases by using some
    // "if" statements.

    // For the "==>" direction:
    if (divides(k, a % b) && divides(k, b)) {
        assert (divides(k, a))
        {
            // This next assert follows from the definition of / and %
            assert (a == (a/b) * b + (a % b));

            // Apply our divides_linear lemma. We have that k|b and k|(a%b).
            // Therefore k|(b*x + (a%b)*y), where x=a/b and y=1.
            // But b*x + (a%b)*y is equal to a (by the previous assert) and
            // so k|a, as required.
            divides_linear(k, b, a%b, a/b, 1);
        }
    }

    // For the "<==" direction:
    if (divides(k, a) && divides(k, b)) {
        assert (divides(k, a % b))
        {
            // This next assert also follows from the definition of / and %
            // (it is like the previous one, but rearranged!)
            assert (a%b == a + (-a/b) * b);

            // We can now apply the divides_linear lemma again:
            divides_linear(k, a, b, 1, -a/b);
        }
    }
}


// euclid_lemma now suggests an implementation:

// If we wish to find gcd(a,b), it is permissible to replace a and b with
// b and a%b instead. This will leave the set of common divisors (and therefore the
// greatest common divisor) unchanged. We can keep doing this until b becomes
// zero, at which point gcd(a,0) is trivial to compute (it is just equal to a).

// The following function will implement this idea (which is known as Euclid's
// algorithm). Note that this is a real, executable function, not a ghost function.

function gcd(a_input: i32, b_input: i32): i32
    // It does not make sense to compute the gcd of 0 and 0.
    requires a_input != 0 || b_input != 0;

    // We also require that neither input is I32_MIN, as we will not be able
    // to negate this value.
    requires a_input != I32_MIN;
    requires b_input != I32_MIN;

    // We promise to return a nonzero value, that is a common divisor
    // of a and b.
    ensures return != 0;
    ensures divides(return, a_input);
    ensures divides(return, b_input);

    // We also prove that our return value is the *greatest* common divisor.
    // In other words, if any other value "k" divides both a_input and b_input,
    // then that "k" must be smaller than (or equal to) our return value.
    ensures forall (k:i32) k != 0 ==>
        divides(k, a_input) && divides(k, b_input) ==> k <= return;
{
    // Function parameters cannot be modified by the function itself.
    // Therefore, the first thing to do is copy the two input values
    // into variables "a" and "b".
    var a: i32 = a_input;
    var b: i32 = b_input;

    // Without loss of generality, we can flip the signs of a and b
    // (if necessary) to ensure a > 0 and b > 0.
    
    if (a < 0) {
        a = -a;
    }
    
    if (b < 0) {
        b = -b;
    }

    // If a == b then it is the case that gcd(a,b) == a, so we can return immediately
    // in this case.

    if (a == b) {
        return a;
    }

    // Without loss of generality, we can swap over a and b (if necessary)
    // to ensure a < b.
    
    if (a < b) {
        swap a, b;
    }


    // We now enter the main loop of Euclid's algorithm.
    // (We keep going until b reaches zero.)
    
    while (b != 0)

        // We keep a > b >= 0 at all times.
        
        invariant a > b >= 0;

        // We ensure that the set of common divisors of a and b
        // remains equal to the set of common divisors of a_input and b_input
        // at all times.
        // In other words, if k divides both a and b, then it divides both
        // a_input and b_input, and vice versa.
        
        invariant forall (k: i32) k != 0 ==>
             (divides(k, a) && divides(k, b) <==>
                divides(k, a_input) && divides(k, b_input));

        // b decreases after every iteration (and therefore, the loop must
        // eventually terminate).
        
        decreases b;
    {
        // We are going to change "a" during the loop body, so let's back up
        // its original value into a0.
        // (We only need a0 in the proofs, not at runtime, so we might as
        // well make it a ghost variable.)
        ghost var a0 = a;

        // Now perform one step of Euclid's algorithm. Preserve the original
        // value of b in b0.
        var b0 = b;
        b = a % b0;
        a = b0;

        // At this point, it is clear that we still have a > b >= 0, and
        // that b has decreased.

        // Proving the second invariant requires us to use our "euclid_lemma".

        assert (forall (k: i32) k != 0 ==> 
             (divides(k, a) && divides(k, b) <==> divides(k, a0) && divides(k, b0)))
        {
            fix k:i32;
            if (k != 0) {
                euclid_lemma(k, a0, b0);
            }
        }
    }

    return a;
}


// Let's make a small main function that prints out some GCDs.
function main()
{
    var max: i32 = 100;

    // Let "a" run from 1 to "max" inclusive.
    var a: i32 = 1;
    while (a <= max)
        decreases ~a;
        invariant 1 <= a <= max + 1;        
    {
        // Let "b" run from 1 to "max" inclusive.
        var b: i32 = 1;
        while (b <= max)
            decreases ~b;
            invariant 1 <= b <= max + 1;
        {
            // Print a little message including the calculation of gcd(a,b).
            print_string("The GCD of ");
            print_i32(a);
            print_string(" and ");
            print_i32(b);
            print_string(" is ");
            print_i32(gcd(a,b));
            print_string("\n");
            
            b = b + 1;
        }
        
        a = a + 1;
    }
}


// To verify this example:
//   babylon -V Demo_14_GCD.b

// To run this example:
//   babylon -c Demo_14_GCD.b
//   gcc Demo_14_GCD.s ExampleLib.s example_lib.c
//   ./a.out
