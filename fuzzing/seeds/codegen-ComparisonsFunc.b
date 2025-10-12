module Main
interface { function main(); }

// Testing comparison operators, and if-then-else expressions

import Test;

function main()
{
    var eq1 =  1 == 1;
    var eq2 =  1 == 2;
    var eq3 =  true == true;
    var eq4 =  true == false;

    var ne1 =  1 != 1;
    var ne2 =  1 != 2;
    var ne3 =  true != true;
    var ne4 =  true != false;

    var gt1 =  1 > 2;
    var gt2 =  2 > 2;
    var gt3 =  3 > 2;
    var gt_neg1 = -1 > 2;
    var gt_neg2 = -1 > -1;
    var gt_neg3 = 2 > -1;
    var gt_un1 = u32(100) > u32(200);
    var gt_un2 = u32(100) > u32(100);
    var gt_un3 = u32(200) > u32(100);

    var ge1 =  1 >= 2;
    var ge2 =  2 >= 2;
    var ge3 =  3 >= 2;
    var ge_neg1 = -1 >= 2;
    var ge_neg2 = -1 >= -1;
    var ge_neg3 = 2 >= -1;
    var ge_un1 = u32(100) >= u32(200);
    var ge_un2 = u32(100) >= u32(100);
    var ge_un3 = u32(200) >= u32(100);

    var lt1 =  1 < 2;
    var lt2 =  2 < 2;
    var lt3 =  3 < 2;
    var lt_neg1 = -1 < 2;
    var lt_neg2 = -1 < -1;
    var lt_neg3 = 2 < -1;
    var lt_un1 = u32(100) < u32(200);
    var lt_un2 = u32(100) < u32(100);
    var lt_un3 = u32(200) < u32(100);

    var le1 =  1 <= 2;
    var le2 =  2 <= 2;
    var le3 =  3 <= 2;
    var le_neg1 = -1 <= 2;
    var le_neg2 = -1 <= -1;
    var le_neg3 = 2 <= -1;
    var le_un1 = u32(100) <= u32(200);
    var le_un2 = u32(100) <= u32(100);
    var le_un3 = u32(200) <= u32(100);

    var ite1: i32 = if 1 < 2 then 10-(6+2) else 1/0;
    var ite2: i32 = if 1 > 2 then 1/0 else 99;
    var ite3: i32 = if 1 == 1 then (if 9>6 then 100 else 200)
                      else if 2 == 2 then 300 else 400;

    var less_chain_true:  bool = 1 < 2 <= 3;
    var less_chain_false: bool = 1 < 2 < 1;
    var long_chain: bool = 1 < 2 < 3 < 4;

    Test.print_bool(eq1);
    Test.print_bool(eq2);
    Test.print_bool(eq3);
    Test.print_bool(eq4);
    Test.print_bool(ne1);
    Test.print_bool(ne2);
    Test.print_bool(ne3);
    Test.print_bool(ne4);
    Test.print_bool(gt1);
    Test.print_bool(gt2);
    Test.print_bool(gt3);
    Test.print_bool(gt_neg1);
    Test.print_bool(gt_neg2);
    Test.print_bool(gt_neg3);
    Test.print_bool(gt_un1);
    Test.print_bool(gt_un2);
    Test.print_bool(gt_un3);
    Test.print_bool(ge1);
    Test.print_bool(ge2);
    Test.print_bool(ge3);
    Test.print_bool(ge_neg1);
    Test.print_bool(ge_neg2);
    Test.print_bool(ge_neg3);
    Test.print_bool(ge_un1);
    Test.print_bool(ge_un2);
    Test.print_bool(ge_un3);
    Test.print_bool(lt1);
    Test.print_bool(lt2);
    Test.print_bool(lt3);
    Test.print_bool(lt_neg1);
    Test.print_bool(lt_neg2);
    Test.print_bool(lt_neg3);
    Test.print_bool(lt_un1);
    Test.print_bool(lt_un2);
    Test.print_bool(lt_un3);
    Test.print_bool(le1);
    Test.print_bool(le2);
    Test.print_bool(le3);
    Test.print_bool(le_neg1);
    Test.print_bool(le_neg2);
    Test.print_bool(le_neg3);
    Test.print_bool(le_un1);
    Test.print_bool(le_un2);
    Test.print_bool(le_un3);
    Test.print_i32(ite1);
    Test.print_i32(ite2);
    Test.print_i32(ite3);
    Test.print_bool(less_chain_true);
    Test.print_bool(less_chain_false);
    Test.print_bool(long_chain);
}
