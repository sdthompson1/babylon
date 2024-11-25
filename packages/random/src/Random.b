/* This module contains two things:

(1) A function get_random_seed which calls the operating system to
return some non-deterministic 

(2) A re-implementation of the "Arbee" pseudo-random number generator
from PractRand (https://pracrand.sourceforge.net/).

See also https://pracrand.sourceforge.net/license.txt:
"I, Chris Doty-Humphrey, release all of my work on PractRand to the 
public domain."

NOTE: This file is NOT intended for cryptographic applications. It is
more like a fast and simple random number generator for applications
like games and simulations.

*/

module Random

interface {

    // This function will overwrite the current contents of 'bytes'
    // with a list of random (or at least, non-deterministic) bytes
    // obtained from the operating system. This could be from a source
    // such as getrandom(2) on Linux, or it could just be something like
    // a timer on systems that do not have anything like getrandom(2)
    // available.
    //
    extern impure function get_random_seed(ref bytes: u8[])
        requires sizeof(bytes) <= 1000000;   // Arbitrary limit
        ensures sizeof(bytes) == old(sizeof(bytes));


    // A simple pseudo-random number generator (PRNG).

    // This uses the "Arbee" algorithm from PractRand which is
    // described in https://pracrand.sourceforge.net/RNG_engines.txt.
    // See also below for more details about the implementation.

    type RNG;

    // Initialize an RNG using a seed obtained from get_random_seed.
    impure function new_rng(): RNG;

    // Initialize an RNG using a seed provided by the caller.
    // (The seed can be any desired size, but more bytes will be better,
    // at least up to a point.)
    function new_rng_with_seed(seed: u8[]): RNG;

    // Generate a random boolean (with equal probability of returning
    // true or false).
    function coin_flip(ref rng: RNG): bool;

    // Generate a random integer uniformly distributed in the
    // range [min_inclusive, max_inclusive].
    function random_range(ref rng: RNG,
                          min_inclusive: i32,
                          max_inclusive: i32): i32
        requires min_inclusive <= max_inclusive;
        ensures min_inclusive <= return <= max_inclusive;

}

import IntBitwise;
import IntWrap;

type RNG = {
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    i: u64
};

// Raw 64-bit random number generator
function raw64(ref rng: RNG): u64
{
    var e: u64 = u64_wrap_add(rng.a, u64_rol(rng.b, 45));
    rng.a = rng.b ^ u64_rol(rng.c, 13);
    rng.b = u64_wrap_add(rng.c, u64_rol(rng.d, 37));
    rng.c = u64_wrap_add(u64_wrap_add(e, rng.d), rng.i);
    rng.i = u64_wrap_add(rng.i, 1);
    rng.d = u64_wrap_add(e, rng.a);
    return rng.d;
}

// Seeding

function add_entropy_64(ref rng: RNG, value: u64)
{
    rng.d = rng.d ^ value;
    rng.b = u64_wrap_add(rng.b, value);
    var dummy = raw64(rng);
    dummy = raw64(rng);
    dummy = raw64(rng);
    dummy = raw64(rng);
    rng.b = u64_wrap_add(rng.b, value);
}

function add_entropy_16(ref rng: RNG, value: u16)
{
    rng.d = rng.d ^ value;
    rng.b = u64_wrap_add(rng.d, value);
    var dummy = raw64(rng);
    rng.b = u64_wrap_add(rng.b, value);
}

impure function new_rng(): RNG
{
    var seed: u8[64];
    get_random_seed(seed);
    return new_rng_with_seed(seed);
}

function new_rng_with_seed(seed_data: u8[]): RNG
{
    var rng: RNG;
    rng.a = 9873171087373218264;
    rng.b = 10599573592049074392;
    rng.c = 16865209178899817893;
    rng.d = 5013818595375203225;
    rng.i = 13;

    var size: u64 = sizeof(seed_data);
    var i: u64 = 0;

    if size >= 8 {
        while i <= size - 8
            decreases ~i;
        {
            var val: u64 = seed_data[i];
            val = val | (u64(seed_data[i + u64(1)]) << 8);
            val = val | (u64(seed_data[i + u64(2)]) << 16);
            val = val | (u64(seed_data[i + u64(3)]) << 24);
            val = val | (u64(seed_data[i + u64(4)]) << 32);
            val = val | (u64(seed_data[i + u64(5)]) << 40);
            val = val | (u64(seed_data[i + u64(6)]) << 48);
            val = val | (u64(seed_data[i + u64(7)]) << 56);
            add_entropy_64(rng, val);
            i = i + 8;
        }
    }

    if size >= 2 {
        while i <= size - 2
            decreases ~i;
        {
            var val: u16 = seed_data[i];
            val = val | (u16(seed_data[i + 1]) << 8);
            add_entropy_16(rng, val);
            i = i + 2;
        }
    }

    if size > 0 && i == size - 1 {
        add_entropy_16(rng, seed_data[size - 1]);
    }

    // Mix the initial state for good measure
    i = 0;
    while i < 12
        decreases ~i;
    {
        var dummy = raw64(rng);
        i = i + 1;
    }

    return rng;
}

// Random number generation interface

function coin_flip(ref rng: RNG): bool
{
    var n = raw64(rng);
    return (n & 1) != 0;
}

function random_range(ref rng: RNG,
                      min_inclusive: i32,
                      max_inclusive: i32): i32
    requires min_inclusive <= max_inclusive;
    ensures min_inclusive <= return <= max_inclusive;
{
    // range is how many different numbers are in the output range
    var range: u64 = i64(max_inclusive) - i64(min_inclusive) + 1;

    // Technically the following is biased, but even if range is the 
    // greatest possible, the bias will only be on the order of one
    // part in a billion, so we don't need to worry about it.
    // (Also, in typical cases, range will be much less than the
    // greatest possible, meaning the bias is even less.)

    var rand: u64 = raw64(rng);     // rand is a 64-bit random number
    rand = rand % range;            // rand is now in [0, range-1]

    // (in particular, rand must fit in an i64 at this point;
    // 0 <= rand <= max_inclusive - min_inclusive <= U32_MAX)

    var result: i64 = i64(min_inclusive) + i64(rand);
    return i32(result);
}
