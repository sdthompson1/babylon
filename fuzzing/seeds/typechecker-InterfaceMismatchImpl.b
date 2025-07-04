module InterfaceMismatchImpl
interface {
    const a: i64;
    const b: bool;

    function diff_num_args(x: i32);
    function diff_arg_type(x: i16);
    function diff_ret_type(): i32;
    function double_impl() {}

    const fun_confused_with_const: i32;

    function pure_int_impure_impl();   // Error
    impure function impure_int_pure_impl();   // Allowed

    ghost function ghost_int_real_impl();  // Error
    function real_int_ghost_impl();  // Error
}

const a: i32 = 0;
const b: i32 = 0;

function diff_num_args(x: i32, y: i32)
{
}

function diff_arg_type(x: i32)
{
}

function diff_ret_type(): i16
{
    return 0;
}

function double_impl()
{
}

function fun_confused_with_const(): i32
{
    return 10;
}

impure function pure_int_impure_impl() {}
function impure_int_pure_impl() {}

function ghost_int_real_impl() {}
ghost function real_int_ghost_impl() {}
