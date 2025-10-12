module Main

// The point of this test is that the parser succeeds (even with trailing
// commas present in various places) but then we get various errors from the renamer
// (see TrailingCommas.errors file).

interface {}

function trailing_comma_in_name_type_list() : {field_name: i32, }

function trailing_comma_in_name_pattern_list()
{
    match foo {
        case {field_name = 99, } => return;
    }
}

function trailing_comma_in_name_term_list()
{
    var x = {a with b = c, };
    var y = {b = c, };
}

function trailing_comma_in_term_list()
{
    some_function(1, 2, 3, );
}

function trailing_comma_in_tyvar_list<a, b, >()
{}

function trailing_comma_in_funargs(x: i32, y: i32, z: i32, ): bool
{
    return true;
}

