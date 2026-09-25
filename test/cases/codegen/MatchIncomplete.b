module MatchIncomplete

// 'if' and 'match' expressions may have an incomplete array type.
// This test checks that such expressions compile and run correctly.

interface {
    function main();
}

import Test;

function pick_size(c: bool, ref r: i32[], ref s: i32[]): u64
    ensures return == (if c then sizeof(r) else sizeof(s));
{
    return sizeof(match c { case true => r case false => s });
}

function pick_first(c: bool, ref r: i32[], ref s: i32[]): i32
    requires sizeof(r) > u64(0);
    requires sizeof(s) > u64(0);
    ensures return == (if c then old(r[0]) else old(s[0]));
{
    return (match c { case true => r case false => s })[0];
}

function pick_size_if(c: bool, ref r: i32[], ref s: i32[]): u64
    ensures return == (if c then sizeof(r) else sizeof(s));
{
    return sizeof(if c then r else s);
}

function pick_first_if(c: bool, ref r: i32[], ref s: i32[]): i32
    requires sizeof(r) > u64(0);
    requires sizeof(s) > u64(0);
    ensures return == (if c then old(r[0]) else old(s[0]));
{
    return (if c then r else s)[0];
}

function main()
{
    var a: i32[3];
    a[0] = 10;
    var b: i32[*];
    alloc_array<i32>(b, 5);
    b[0] = 20;

    var n1 = pick_size(true, a, b);
    print_u64(n1);
    var n2 = pick_size(false, a, b);
    print_u64(n2);
    var x1 = pick_first(true, a, b);
    print_i32(x1);
    var x2 = pick_first(false, a, b);
    print_i32(x2);

    var n3 = pick_size_if(true, a, b);
    print_u64(n3);
    var n4 = pick_size_if(false, a, b);
    print_u64(n4);
    var x3 = pick_first_if(true, a, b);
    print_i32(x3);
    var x4 = pick_first_if(false, a, b);
    print_i32(x4);

    free_array<i32>(b);
}
