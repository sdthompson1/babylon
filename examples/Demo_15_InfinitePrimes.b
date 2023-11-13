
// This is in some ways a follow-on from Demo_07_Primes.

// In this file we will prove that there are infinitely many prime numbers
// (following Euclid's proof).

// In order to do this, we need to use the 'int' type which represents an
// unbounded (mathematical) integer. This can only be used in ghost code
// (as there is not currently any support for arbitrary-precision arithmetic
// at runtime).

module Demo_15_Infinite_Primes

interface {}

// Definition of a prime number.
ghost function is_prime(n: int): bool
{
    // Note that a literal constant like '1' or '2' gives an i32 by default.
    // If you want an 'int' constant then you have to say something like
    // int(1) or int(2), at least for now.
    return n >= int(2) &&
        forall (f: int) int(1) < f < n ==>
            n % f != int(0);
}


// We first need some arithmetic lemmas.

// If i divides n, then i also divides n*m, for any integer m.
ghost function mod_lemma_1(n: int, m: int, i: int)
    requires i != int(0);
    requires n % i == int(0);
    ensures (n * m) % i == int(0);
{
    obtain (k: int) n == i * k;
    assert (n * m) == i * (k * m);
}

// If a%b == 0, and b%c == 0, then a%c == 0.
ghost function mod_lemma_2(a: int, b: int, c: int)
    requires b != int(0) && c != int(0);
    requires a % b == int(0);
    requires b % c == int(0);
    ensures a % c == int(0);
{
    var k1 = a/b;
    assert a == k1 * b;

    var k2 = b/c;
    assert b == k2 * c;

    var k3 = k1*k2;
    assert a == k3 * c;

    assert a/c == k3;
}

// If a%b == 0, and b > 1, then a%b + 1 == 1.
ghost function mod_lemma_3(a: int, b: int)
    requires b > int(1);
    requires a % b == int(0);
    ensures (a + int(1)) % b == int(1);
{}

// This multiplies A by B and also asserts that the result is divisible by B.
ghost function multiply(a: int, b: int): int
    requires b != int(0);
    ensures return == a * b;
    ensures return % b == int(0);
{
    return a * b;
}


// Now we can define the factorial function.
// We also prove that i divides n! for any i between 1 and n, and that n! >= n.
ghost function factorial(n: int): int
    requires n >= int(0);
    ensures forall (i: int) int(1) <= i <= n ==>
        return % i == int(0);
    ensures return >= n;
{
    var result = int(1);
    var multiplier = int(1);
    
    while multiplier <= n
        invariant int(1) <= multiplier <= n + int(1);
        invariant forall (i: int) int(1) <= i < multiplier ==>
            result % i == int(0);
        invariant result >= multiplier - int(1);
        invariant result >= int(1);
        decreases n - multiplier;
    {
        ghost var old_result = result;

        // We have to use our 'multiply' function (with the postcondition) here,
        // otherwise the solver apparently cannot understand that result % multiplier == 0
        // (after the assignment).
        result = multiply(result, multiplier);

        // To prove that the second invariant is still true, we need
        // to use mod_lemma_1.
        assert forall (i: int) int(1) <= i < multiplier ==>
            result % i == int(0)
        {
            fix i: int;
            if int(1) <= i < multiplier {
                mod_lemma_1(old_result, multiplier, i);
            }
        }

        multiplier = multiplier + int(1);
    }

    return result;
}


// Here is a function which, when given a NON-prime number n,
// returns a prime factor of n.
// (This function is adapted from Demo_07_Primes.b.)
ghost function get_prime_factor(n: int): int
    requires !is_prime(n);
    requires n >= int(2);

    ensures is_prime(return);
    ensures n % return == int(0);
    ensures return < n;
{
    var factor: int = n;
    while !is_prime(factor)
        invariant int(2) <= factor <= n;
        invariant n % factor == int(0);
        decreases factor;
    {
        obtain (k: int) int(1) < k < factor && factor % k == int(0);
        mod_lemma_2(n, factor, k);
        factor = k;
    }
    return factor;
}


// We can't directly state that there are infinitely many primes (as our language
// doesn't really have any concept of "infinity"), but if we can define a function
// "make_higher_prime" which returns a prime greater than its argument, then this
// amounts to (more or less) the same thing.

ghost function make_higher_prime(n: int): int
    ensures is_prime(return);
    ensures return > n;
{
    // If n < 2 then we can just return 2 (the first prime).
    if n < int(2) {
        return int(2);
    }
    
    // Otherwise, calculate N = n! + 1.
    var N = factorial(n) + int(1);

    if is_prime(N) {
        // If N is prime, we are already done.
        return N;
        
    } else {
        // If N is not prime, then it has a prime factor...
        var p = get_prime_factor(N);

        // We can prove that p > n as follows.
        assert p > n
        {
            // p is prime so it must be at least 2.
            assert p >= int(2);

            // Suppose, for a contradiction, that p <= n.
            if p <= n {

                // Because p <= n, it must be that p divides n!, i.e. n! % p == 0.
                assert factorial(n) % p == int(0);

                // Therefore, (n! + 1) % p == 1 (by mod_lemma_3).
                // In other words, N % p == 1 (because N == n! + 1).
                mod_lemma_3(factorial(n), p);
                assert N % p == int(1);

                // But we also have that N % p == 0, because p is a (prime) factor of N.
                assert N % p == int(0);

                // We can't have both N%p == 0 and N%p == 1 at the same time...
                assert false;
            }

            // Since the assumption p <= n led to a contradiction, this proves that
            // p > n, as required!
        }

        return p;
    }
}


// It is not possible to "run" this example as it doesn't have any executable code,
// but we can verify that the proofs are valid with this command:
//   babylon -V Demo_15_Prime.b
