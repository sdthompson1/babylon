module ExternName

interface {
    function main();
}

import Test; // this is where "c_function_with_custom_name" is defined

extern function my_c_func() = "c_function_with_custom_name";

function main()
{
    my_c_func();
}
