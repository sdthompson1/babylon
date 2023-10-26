module RefArg3
interface {}

function foo(dummy: bool, ref arr: i32[])
    requires sizeof(arr) == u64(10);
    ensures sizeof(arr) == old(sizeof(arr));
    ensures arr[5] == 1;
{
    arr[5] = 1;   // OK
    arr[15] = 0;  // Error
}
