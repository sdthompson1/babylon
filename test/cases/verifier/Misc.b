module Misc
interface { function main(); }

  // This covers a case in insert_lets, where no Item is found for 'x' 
  const c: i32 = 999;
  function return_const(): i32
  {
    return c;
  }


  function main()
  {
  }
  
