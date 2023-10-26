module RefArg2
interface {}

    function f1(ref i: i32): i32
    {
        i = 1;
        return 99;
    }

    function test_f1()
    {
        var x = 0;
        var r = f1(x);
        assert (x == 1);
        assert (x == 0);   // Fails
    }


    function f2(ref i: i32)
    {
        i = 1;
    }

    function test_f2()
    {
        var x = 0;
        f2(x);
        assert (x == 1);
        assert (x == 0);   // Fails
    }


    function f3(ref i: i32)
    {
        i = 1;
        return;
    }

    function test_f3()
    {
        var x = 0;
        f3(x);
        assert (x == 1);
        assert (x == 0);   // Fails
    }


    ghost function f4(ref i: i32)
    {
        i = 0;
    }

    function test_f4()
    {
        ghost var x = 1;
        ghost f4(x);
        assert (x == 0);
        assert (x == 1);   // Fails
    }
