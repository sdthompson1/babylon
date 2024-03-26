module ConstArray

interface {
    function main();
}

import Test;

const arr: i32[] = [1, 2, 3, 4, 5, 6];
const arr2: i32[3] = [99, 98, 97];

function main()
{
    print_u64(sizeof(arr));
    print_i32(arr[0]);
    print_i32(arr[1]);
    print_i32(arr[2]);
    print_i32(arr[3]);
    print_i32(arr[4]);
    print_i32(arr[5]);

    print_u64(sizeof(arr2));
    print_i32(arr2[0]);
    print_i32(arr2[1]);
    print_i32(arr2[2]);
}
