// Example 7 -- Primes.

// In this example we will illustrate how to prove some properties of prime
// numbers, and write a program to compute all primes up to and including
// 2^31 - 1.


// Note: This file has been tested with the following combinations of provers:
//   z3 4.13.3 + cvc5 1.2.0 + vampire 4.9: Verification succeeds
//   z3 4.13.3 + cvc5 1.2.0 + alt-ergo 2.6.0: Verification succeeds
//   z3 4.13.3 + cvc5 1.2.0: Verification fails (i.e. cvc5 and z3 alone are not enough!)


module Example07

interface {
    impure function main();
}

import Array;
import Console;
import Int;


// We first (once again) give a ghost function that defines whether or not
// a number is prime. (Here we use type u32, rather than i32.)

ghost function is_prime(n: u32): bool
{
    return n >= 2 &&
        (forall (f: u32) 1 < f < n ==> n % f != 0);
}


// An alternative definition is that a number is prime if it is >= 2 and
// not divisible by any *prime* number less than itself.

// Note: Arguably, this defintion should have "is_prime_alt" rather than
// "is_prime" on the right-hand-side (because it should be a self-contained
// definition, not reliant on our previous "is_prime" definition).
// However, the Babylon compiler doesn't support recursive definitions yet.
// The below definition (in terms of is_prime) will be good enough for our
// purposes here.

ghost function is_prime_alt(n: u32): bool
{
    return n >= 2 &&
        (forall (f: u32) f < n && is_prime(f) ==> n % f != 0);
}


// We would like to prove that is_prime_alt is equivalent to is_prime,
// i.e. both functions return the same value given the same input.


// First we will need to prove the following lemma:

// If a is a multiple of b, and b is a multiple of c, then a is a multiple
// of c.

// This seems obvious enough, but unfortunately, the SMT solvers need a
// little bit of help proving it. (This will be our first example of a
// case where such "help" is necessary!)

// Let's first state our lemma a bit more precisely:
//   "Let a, b, c be u32 values, with b != 0 and c != 0.
//    Suppose that a % b == 0 (a is a multiple of b),
//    and b % c == 0 (b is a multiple of c).
//    Then a % c == 0 (a is a multiple of c)."

// How can we encode this into a programming language construct?

// The answer is that we use a ghost function. The variables a, b, c become
// parameters of the function. The hypotheses of the lemma become "requires"
// conditions, and the conclusion becomes an "ensures" condition.

// If you think about it, if the system accepts this as a valid function
// definition, then that means the lemma must be true.

// So here goes:

ghost function modulo_lemma(a: u32, b: u32, c: u32)
    requires b != 0 && c != 0;
    requires a % b == 0;
    requires b % c == 0;
    ensures a % c == 0;
{
    // As mentioned above, if you just leave the function body empty, then the
    // automatic provers are not able to prove, on their own, that the
    // "ensures" condition is true. (The verifier times out with an error
    // that the postcondition might not be met.)

    // How can we fix this?

    // The answer is that we need to write a sequence of "assert" statements
    // that will lead the prover, step by step, to the solution.


    // First of all, let's show that a is "something" times b. We can use a/b
    // as the "something". (We have a = (a/b) * b, because a % b == 0.)
    var k1: u32 = a/b;
    assert a == k1 * b;


    // Similarly, we can show that b is "something" times c.
    var k2: u32 = b/c;
    assert b == k2 * c;


    // This means that a is "something" times c (where the "something" is the
    // product of the previous two "somethings"...).
    var k3: u32 = k1 * k2;
    assert a == k3 * c;


    // If we now point out to the solver that k3 is equal to a/c, that
    // seems to be enough. (The solver can then see that a == (a/c) * c,
    // which of course can only be true if a % c == 0.)
    assert a/c == k3;
}



// Here is another property that we can prove:

// If n >= 2 is NOT prime, then it has a prime factor.
// (I.e., there exists a prime p < n such that n % p == 0.)

// One way to demonstrate this, is to write a ghost function that actually
// returns a suitable p, given n. (Note that p will not be unique, in
// general.)

ghost function get_prime_factor(n: u32): u32

    // Preconditions: n is not prime, and n >= 2.
    requires !is_prime(n);
    requires n >= 2;

    // Postconditions: The returned value is a prime factor of n, and
    // it is strictly less than n.
    ensures is_prime(return);
    ensures n % return == 0;
    ensures return < n;

{
    // We're going to make a little while loop. We initially set "factor"
    // to n. Each time through the loop, we will find a new number
    // (different from 1 and factor) which is a factor of the current value
    // of "factor". This new number will also be a factor of n (this is
    // a consequence of modulo_lemma).
    // We repeat this until "factor" becomes prime (which must eventually
    // happen).
    var factor: u32 = n;

    // Loop while factor is not prime.
    while !is_prime(factor)
    
        // "factor" gets smaller on each iteration.
        decreases factor;

        // We always keep "factor" in the range 2 to n (it is n initially).
        invariant 2 <= factor <= n;

        // We always maintain that "factor" is a factor of n.
        invariant n % factor == 0;
    {
        // Because factor is not prime, there must exist a number k, not
        // equal to 1 or factor, such that k divides factor. (This is a
        // direct consequence of the definition of is_prime.)

        // We now introduce the "obtain" keyword. If something with a
        // certain property is known to exist, then we can use "obtain"
        // to obtain a concrete value that has that property. Here we obtain
        // a concrete value "k" satisfying the property mentioned above.

        obtain (k: u32) 1 < k < factor && factor % k == 0;

        // Note that "obtain" can only be used within ghost code. (If you
        // actually want to calculate such a k, in executable code, then you
        // need to write an algorithm to do it. But within a proof, it is
        // legitimate to simply state that such a k exists, and then start
        // working with it!)


        // Now, because n % factor == 0, and factor % k == 0, it follows
        // that n % k == 0.
        // (We need our previous "modulo_lemma" to prove this.)

        // To invoke a lemma, we can simply call it with the required
        // parameters. When a ghost function is called, the verifier inspects
        // any "ensures" conditions of the ghost function, and adds them to
        // the list of "known facts" that can be used in future proofs.
        // In this case, we are adding the fact that "n % k == 0" to our
        // known facts.

        modulo_lemma(n, factor, k);


        // Now, we can just use "k" as the new value of "factor".
        // This clearly satisfies the decreases-condition, and it
        // preserves all the loop invariants.
        factor = k;
    }

    // We now have:
    //  (1) is_prime(factor) (because the loop exited); and
    //  (2) factor < n (because factor <= n by the first loop invariant, 
    //         and factor != n because is_prime(factor) but !is_prime(n)); and
    //  (3) n % factor == 0 (by the second loop invariant).

    // Therefore returning 'factor' will satisfy all the "ensures" conditions
    // of this function.

    return factor;
}


// Now we are ready to prove that *if* is_prime_alt(n) *then* is_prime(n).

ghost function prime_alt_implies_prime(n: u32)
    requires is_prime_alt(n);
    ensures is_prime(n);
{
    // This is the definition of is_prime_alt(n):
    assert n > 1;
    assert forall (f: u32) 1 < f < n && is_prime(f) ==> n % f != 0;

    // This next assert is the thing that we need to prove.

    // We now introduce a new feature. If an "assert" cannot be proved by the
    // verifier directly (which is the case here) then we can write a "proof"
    // ourselves. We do this by *not* following the assert with a semicolon as
    // usual, but following it instead with a "{" character, then writing the
    // proof inside the curly brackets.

    assert forall (f: u32) 1 < f < n ==> n % f != 0
    {
        // The "proof" is just a series of normal Babylon statements --
        // although there are one or two "special" statements that can only
        // be used inside the proof of an assert.

        // One such statement is "fix". This is used for proving "forall"
        // statements. There are some limitations: "fix" can only be used
        // at the top level of a proof (i.e. not nested within an "if" or
        // some such) and it must correspond exactly with a "forall" condition
        // in the assert being proved.

        // Here we can state "fix f: u32" which brings an arbitrary value
        // "f" of type u32 into scope.
        fix f: u32;

        // We now have to prove that "1 < f < n  ==>  n % f != 0".
        // The implication is dealt with by using an "if" statement as follows:

        if 1 < f < n {

            // We now just have to prove that "n % f != 0".

            // If f happens to be prime, we are already done, so let's
            // consider the case !is_prime(f).

            // (A proof by cases is done by using an "if" statement.)

            if !is_prime(f) {

                // Because f is not prime, we can obtain a prime factor p of f
                // (using get_prime_factor, defined above).
                var p = get_prime_factor(f);

                // We now know the following:
                assert n % p != 0;   // because is_prime_alt(n)
                assert f % p == 0;   // because p is a prime factor of f

                // We are trying to prove: n % f != 0.

                // We can prove this by contradiction. If n % f *was* zero, we
                // would have n % f == 0 and f % p == 0, and so n % p == 0
                // (by modulo_lemma). But that contradicts n % p != 0 which
                // was asserted above.

                // To introduce the proof by contradiction, we use can use
                // another "if" statement:

                if n % f == 0 {
                
                    // We now just need to invoke modulo_lemma to bring the fact
                    // "n % p == 0" (the postcondition of modulo_lemma) into scope.
                    // The verifier will see that this contradicts "n % p != 0"
                    // and this will complete the proof.

                    modulo_lemma(n, f, p);
                }
            }
        }
    }
}


// We can go further, and say that is_prime(n) == is_prime_alt(n) at
// all values of n.

ghost function prime_alt_equals_prime(n: u32)
    ensures is_prime(n) == is_prime_alt(n);
{
    // If is_prime_alt(n) is true, then we can invoke "prime_alt_implies_prime"
    // to show that is_prime(n) is true.
    
    // If is_prime_alt(n) is false, then the result is obvious, and the solver
    // can see this without further help.
    
    if is_prime_alt(n) {
        prime_alt_implies_prime(n);
    }
}



// Here are a couple more lemmas, which will be needed below.

// If x % n == 0, then (x + n) % n == 0.
ghost function mod_plus(x: u32, n: u32)
    requires n != 0;
    requires x % n == 0;
    requires can_add_u32(x, n);
    ensures (x + n) % n == 0;
{}

// If x % n == 0, and k is in the range [x, x+n), and k % n == 0,
// then k must be equal to x.
ghost function mod_range(x: u32, n: u32)
    requires n != 0;
    requires x % n == 0;
    requires can_add_u32(x, n);
    ensures forall (k: u32) x <= k < x + n && k % n == 0 ==> k == x;
{}



// We will now implement the Sieve of Eratosthenes, which is a method for
// finding prime numbers.

// This function will print out all prime numbers up to and including n.

impure function sieve(n: u32)
    // Note: For the moment this only works upto U32_MAX/2.
    // We could make it go all the way to U32_MAX by adding some careful overflow
    // checking below (or else we could just make a 64 bit version...).
    requires 2 <= n <= U32_MAX/2;
{
    // The algorithm requires an array of boolean flags for each (positive)
    // integer upto and including n.
    // We will start off with each flag equal to false, and we will set
    // a flag to true when the corresponding number is found NOT to be prime.
    // (So at the end, all numbers >= 2 marked "false" will be primes.)

    var flag: bool[*];
    var ok = alloc_array(flag, n + u32(1));

    if !ok {
        println("Memory allocation failed!");
        return;
    }

    // Loop through all values of i from 2 to n (inclusive).
    var i: u32 = 2;
    while i <= n

        // "flag" is modified during the loop. Therefore we must state as an
        // invariant that the sizeof the flag array is not modified.
        invariant sizeof(flag) == n + 1;

        // The key property of the sieve is the following:
        // After number "i" has been processed, number "j" is marked (i.e.
        // flag[j] is true) exactly when there exists a prime p, less than
        // both i and j, such that p divides j.
        invariant forall (j: u32) 2 <= j <= n ==>
            (flag[j] <==>
                exists (p: u32) p < i && p < j && is_prime(p) && j % p == 0);

        invariant 2 <= i <= n + 1;
        decreases ~i;
    {
        // Skip any i that has already been marked.
        if !flag[i] {

            // If we look closely, we can see that the second invariant implies
            // that is_prime_alt(i) is true.
            // This means is_prime(i) is true as well (applying our
            // prime_alt_implies_prime result).
            // Note that to call a ghost function from executable code, we must
            // precede the call with the word "ghost" (this highlights that the
            // call doesn't actually do anything at runtime).
            ghost prime_alt_implies_prime(i);

            // Since i is a prime number, we print it out (the goal is to print
            // out all the primes, after all!).
            assert is_prime(i);
            print_i32(i);
            println("");

            // Now we need a second while loop to do the "marking".
            // We must mark all numbers starting from 2*i, up until n, in steps
            // of i. (Clearly these numbers are not primes, since they are
            // divisible by i. Therefore they should be marked, because we are
            // marking the non-primes.)
            var k: u32 = 2*i;
            while k <= n

                // Once again, we need to state that the size of the flag array
                // is unchanged.
                invariant sizeof(flag) == n + 1;

                // Here the invariant is slightly more complicated.
                // flag[j] is still true if there exists p, less than i and j,
                // such that p divides j.
                // However, flag[j] is now also true if j is a multiple of i,
                // greater than i, but less than k (k is the point that we have
                // reached in the "marking" loop).
                // If neither of these is true, flag[j] is false.
                invariant forall (j: u32) 2 <= j <= n ==>
                    (flag[j] <==>
                        (exists (p: u32) p < i && p < j && is_prime(p) && j % p == 0)
                        || i < j < k && j % i == 0);

                // k is always strictly greater than i, in this loop.
                invariant k > i;

                // k increases in steps of i, hence, k remains a multiple of i
                // at all times.
                invariant k % i == 0;

                // k increases during the loop (so ~k decreases).
                decreases ~k;
            {
                // Mark entry k in the array.
                flag[k] = true;

                // These calls are needed to prove that the second loop invariant
                // is maintained.
                ghost mod_plus(k, i);
                ghost mod_range(k, i);

                // Step k upwards by i.
                k = k + i;
            }
            
        } else {

            // If i was flagged, then the outer loop invariant implies that
            // there is some prime p < i that divides i. That means that i is
            // not prime. This assert confirms this.
            assert !is_prime(i);

            // Since this i is not prime, we don't print it.

        }

        // Move on to the next value of i.
        i = i + 1;

        // This helps for proving the invariant:
        assert forall (p: u32) is_prime(p) ==> p != 0;
        hide is_prime;
    }

    // Free the array afterwards.
    free_array(flag);
}
         

// This is just a list of primes less than 100.
// If n <= 100, this function returns the same as is_prime.
ghost function prime_less_than_100(n: u32): bool
{
    return (n == 2 || n == 3 || n == 5 || n == 7 || n == 11 || n == 13 ||
         n == 17 || n == 19 || n == 23 || n == 29 || n == 31 || n == 37 ||
         n == 41 || n == 43 || n == 47 || n == 53 || n == 59 || n == 61 ||
         n == 67 || n == 71 || n == 73 || n == 79 || n == 83 || n == 89 ||
         n == 97);
}


impure function main()
{
    // Some test cases to show that our is_prime function is doing the right
    // thing, at least on these examples...
    assert is_prime(3);
    assert !is_prime(4);
    assert is_prime(1997);

    // z3 can actually prove the following, interestingly enough!
    assert forall (n: u32) 2 <= n <= 100 ==> is_prime(n) == prime_less_than_100(n);


    // Now run the sieve function on I32_MAX (which is two to the power of 31,
    // minus one).
    // On my machine, this takes just over a minute (assuming output is redirected
    // to a file -- it is somewhat slower if output is printed on screen), and
    // it prints the first 105,097,565 prime numbers.
    sieve(I32_MAX);
}
