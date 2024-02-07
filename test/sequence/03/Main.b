module Main

// This time we introduce a new constant decl, which prevents the module from
// being cached. However each of the decls f, g, h, i will be skipped because
// they haven't changed since last time.

interface {}

const A_NEW_CONSTANT = 1;

function f(): i32
{
    return 1;
}

function g(): i32
{
    return 1 / f();
}

function h(): i32
{
    return 1 + g();
}

function i(): i32
{
    return 2;
}
