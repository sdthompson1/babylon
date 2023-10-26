module Use

interface{}
import Int;

function f1()
{
    assert (exists (x:i32) Int.can_mul_i32(x,x) && x*x == 10000) {
        use 100;  // Succeeds
    }
}

function f2()
{
    assert (exists (x:i32) Int.can_mul_i32(x,x) && x*x == 10000) {
        use 101;  // Fails, provided term doesn't meet the exists-condition
    }
}

function f3()
{
    assert (exists (x:i32) true) {
        use 1/0;  // Fails, provided term is not valid
    }
}
