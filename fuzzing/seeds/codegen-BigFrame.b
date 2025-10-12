module Main
import Test;

interface {


  // Create some large datatypes

  // 197 bytes (including tag)
  datatype Big = Big { a0: u64, a1: u64, a2: u64, a3: u64,
                       a4: u64, a5: u64, a6: u64, a7: u64,
                       b0: u64, b1: u64, b2: u64, b3: u64,
                       b4: u64, b5: u64, b6: u64, b7: u64,
                       c0: u64, c1: u64, c2: u64, c3: u64,
                       c4: u64, c5: u64, c6: u64, c7: u64,
                       odd: u32
                     };

  // 4729 bytes (including tag)
  datatype VeryBig = VeryBig { x0: Big, x1: Big, x2: Big, x3: Big,
                               x4: Big, x5: Big, x6: Big, x7: Big,
                               y0: Big, y1: Big, y2: Big, y3: Big,
                               y4: Big, y5: Big, y6: Big, y7: Big, 
                               z0: Big, z1: Big, z2: Big, z3: Big,
                               z4: Big, z5: Big, z6: Big, z7: Big };

  // Frame between 32K and 64K, with some spilled variables
  function big_frame(): i32
  {
    var v0: VeryBig;
    var v1: VeryBig;
    var v2: VeryBig;
    var v3: VeryBig;
    var v4: VeryBig;
    var v5: VeryBig;
    var v6: VeryBig;
    var v7: VeryBig;
    var v8: VeryBig;
    var v9: VeryBig;

    var a0: i32;    var a1: i32;    var a2: i32;    var a3: i32;
    var b0: i32;    var b1: i32;    var b2: i32;    var b3: i32;
    var c0: i32;    var c1: i32;    var c2: i32;    var c3: i32;
    var d0: i32;    var d1: i32;    var d2: i32;    var d3: i32;

    a0 = 10;
    d3 = 20;
    return a0 + d3;
  }

  function main()
  {
    Test.print_i32(big_frame());
  }
}
