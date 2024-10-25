module ExternType

interface {
    function main();
}

import Test;


extern type Foo;

function foo(x: Foo)
{
}

function main()
{
    var v: Foo;
    foo(v);


    var m: MaybeAllocTest;
    assert m == MA_Nothing;

    allocate_alloc_test(m);
    assert match m {
      case MA_Nothing => false
      case MA_Just(_) => true
    };

    free_alloc_test(m);
    assert m == MA_Nothing;
}
