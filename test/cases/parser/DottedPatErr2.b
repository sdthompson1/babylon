// Dotted (lowercase) name in pattern - not allowed

module DottedPatErr2

interface {}

function f()
{
    match x {
    case a.b =>   // Error, this is neither a variant pattern nor a variable pattern.
    }
}
