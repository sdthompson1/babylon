module Allocated

interface{}

function f1(): bool
{
    ghost var b = allocated(0);  // This is ok
    return allocated(1);  // Error: allocated not allowed outside ghost code
}

ghost function f2(): bool
{
    return allocated(1 + true);   // Type error in allocated's argument.
}
