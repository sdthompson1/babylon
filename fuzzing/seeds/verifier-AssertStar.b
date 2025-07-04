module AssertStar

interface {}

function test1(x: i32, y: i32)
    requires x >= 0 ==> y > 10;
    requires x < 0 ==> y < -10;
{
    // This is a silly example of how "assert *" might be used
    assert y > 10 || y < -10 {
        if x >= 0 {
            assert *;
        } else {
            assert *;
        }
    }
}

function test2()
{
    assert forall (x: i32) exists (y: i32) y == x
    {
        fix x: i32;
        
        // assert * with a proof. This isn't all that useful (as you might as
        // well just write the proof out "inline") but it is still supported.
        assert * {
            use x;

            // nested assert *.
            assert *;
        }
    }
}

function test3()
{
    // Error case
    assert 1 == 0 {
        assert *;  // Fails
    }
}
