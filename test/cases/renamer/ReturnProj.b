module ReturnProj

interface {
    // Regression test - this was previously producing a "not in scope: 'return'" error
    function foo(): {x:i32, y:i32}
        ensures return.x == 1;
        ensures return.y == 2;
    {
        return {x=1, y=2};
    }

    function main() {}
}
