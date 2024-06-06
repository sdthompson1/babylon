module A.B.C

interface {
    function abc_func(): i32;
}

import A.X.Y;

function abc_func(): i32
{
    return axy_func();
}

