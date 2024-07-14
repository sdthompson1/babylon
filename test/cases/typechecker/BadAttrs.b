module BadAttrs
interface {}

function f()
    invariant true;    // "Invariant" not allowed here
    decreases 99;      // "Decreases" not allowed here (for now)
{
}


function g()
{
    while (true)
        requires true;   // Requires not allowed here
        ensures true;    // Ensures not allowed here
    {
    }
}


function h()
{
    while (true)
        decreases 99;
        decreases true;  // Duplicate Decreases
    {
    }
}
