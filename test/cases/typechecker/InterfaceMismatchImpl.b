module InterfaceMismatchImpl
interface {
  const a: i64;
  const b: bool;

  function diff_num_args(x: i32);
  function diff_arg_type(x: i16);
  function diff_ret_type(): i32;
  function double_impl() {}

  const fun_confused_with_const: i32;
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
