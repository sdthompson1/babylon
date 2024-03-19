module ArrayLit

interface {
    function main();
}

import Test;

const const_array: i32[] = [1+1, 2+2, 3*3];
const const_value: i32 = [333, 444, 555][1];

function main()
{
    var a: i32[3] = [10, 20, 30];
    print_i32(a[0]);
    print_i32(a[1]);
    print_i32(a[2]);

    print_i32(const_array[0]);
    print_i32(const_array[1]);
    print_i32(const_array[2]);

    print_i32(const_value);
}
