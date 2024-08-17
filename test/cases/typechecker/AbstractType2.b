module AbstractType2

interface {
    type Foo;
    function fun1(x: Foo) {}
}

type Foo = i32;

function fun2(x: Foo)
{
    fun1(x);
}

function fun3(x: i32)
{
    fun1(x);
}

function fun4(x: bool)
{
    fun1(x);  // should fail
}
