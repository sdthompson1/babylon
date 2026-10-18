module ShowHide

interface {}

function test()
{
    var x: i32;
    show x;  // error, can't show/hide non-function value
    hide x;  // ditto
}

function test2()
{
    var y = 1 + false;   // error
    hide y;   // doesn't generate error because x's type is unknown/invalid
}

const c: i32 = 1;
ghost const gc: i32 = 2;
datatype D = Nullary | WithPayload(i32);
datatype G<a> = GCtor(a);

function test3()
{
    hide c;             // error, constant
    hide gc;            // error, ghost constant
    hide Nullary;       // error, data constructor
    hide WithPayload;   // error, data constructor (even though it takes a payload)
    hide GCtor;         // error, generic data constructor
}

function f(): i32
{
    return 1;
}

ghost function gf(): bool
{
    return true;
}

function poly<a>(x: a): a
{
    return x;
}

impure function imp()
{
}

extern function ext();

function test4()
{
    // All of these are ok
    hide f;
    show f;
    hide gf;
    show gf;
    hide poly;
    show poly;
    hide imp;
    show imp;
    hide ext;
    show ext;
}
