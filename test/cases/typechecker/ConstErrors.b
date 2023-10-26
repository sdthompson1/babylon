module ConstErrors
interface{}

function f(): i32
{
    return 0;
}

function fb(): bool
{
    return false;
}

const INT64_MIN = -9223372036854775808;

// Error, not a compile time constant.
// (The compiler isn't smart enough to actually evaluate the function calls at
// compile time.)

const c1 = f();
const c2 = if fb() then 1 else 2;
const c3 = ~ f();
const c4 = INT64_MIN / -1;   // Overflows at compile time, this is ok, but verifier would catch it
const c5 = 1 / 0;            // Division by zero at compile time, ditto.
const c6 = f() + 1;
const c7 = 1 + f();
const c8 = { 1, f() };
const c9 = { a=f(), b=1 };
const c10 = {{ x=1, y=2 } with x=3, y=f() };
const c11 = let a = 10 in a+1;   // ok
const c12 = let a = f() in a+1;  // not ok

ghost const cg = f();   // ok, ghost constants are exempt from the "known at compile time" rule.
