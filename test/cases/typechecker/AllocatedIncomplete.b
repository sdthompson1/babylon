module AllocatedIncomplete

// The operand of 'allocated' must be a complete type: it must not be,
// or contain, an incomplete array type.

interface {}

datatype D = A(i32[]) | B;

datatype E = C(i32[*]) | F(i32[3]);

ghost function g0(a: i32[]): bool
{
    return allocated(a);    // Error
}

ghost function g1(p: {i32[], i32}): bool
{
    return allocated(p);    // Error
}

ghost function g2(d: D): bool
{
    return allocated(d);    // Error
}

function f10(p: {i32[], i32})
    ensures !allocated(p);  // Error
{
}

ghost function ok1(p: {i32[*], i32}, e: E, a: i32[], q: {i32[], i32}): bool
{
    // Complete operands are fine, including components of an
    // incomplete array or record.
    return allocated(p) && allocated(e) && allocated(a[0]) && allocated(q.1);
}
