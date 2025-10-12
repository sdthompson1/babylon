module Main
interface { function main(); }

// Testing comparison operators, and if-then-else expressions

import Test;

const eq1 =  1 == 1;
const eq2 =  1 == 2;
const eq3 =  true == true;
const eq4 =  true == false;

const ne1 =  1 != 1;
const ne2 =  1 != 2;
const ne3 =  true != true;
const ne4 =  true != false;

const gt1 =  1 > 2;
const gt2 =  2 > 2;
const gt3 =  3 > 2;
const gt_neg1 = -1 > 2;
const gt_neg2 = -1 > -1;
const gt_neg3 = 2 > -1;
const gt_un1 = u32(100) > u32(200);
const gt_un2 = u32(100) > u32(100);
const gt_un3 = u32(200) > u32(100);

const ge1 =  1 >= 2;
const ge2 =  2 >= 2;
const ge3 =  3 >= 2;
const ge_neg1 = -1 >= 2;
const ge_neg2 = -1 >= -1;
const ge_neg3 = 2 >= -1;
const ge_un1 = u32(100) >= u32(200);
const ge_un2 = u32(100) >= u32(100);
const ge_un3 = u32(200) >= u32(100);

const lt1 =  1 < 2;
const lt2 =  2 < 2;
const lt3 =  3 < 2;
const lt_neg1 = -1 < 2;
const lt_neg2 = -1 < -1;
const lt_neg3 = 2 < -1;
const lt_un1 = u32(100) < u32(200);
const lt_un2 = u32(100) < u32(100);
const lt_un3 = u32(200) < u32(100);

const le1 =  1 <= 2;
const le2 =  2 <= 2;
const le3 =  3 <= 2;
const le_neg1 = -1 <= 2;
const le_neg2 = -1 <= -1;
const le_neg3 = 2 <= -1;
const le_un1 = u32(100) <= u32(200);
const le_un2 = u32(100) <= u32(100);
const le_un3 = u32(200) <= u32(100);

const ite1: i32 = if 1 < 2 then 10-(6+2) else 1/0;
const ite2: i32 = if 1 > 2 then 1/0 else 99;
const ite3: i32 = if 1 == 1 then (if 9>6 then 100 else 200)
                  else if 2 == 2 then 300 else 400;

const less_chain_true:  bool = 1 < 2 <= 3;
const less_chain_false: bool = 1 < 2 < 1;
const long_chain: bool = 1 < 2 < 3 < 4;
const chain_including_equals: bool = 1 <= 2 == 2 < 3 == 3 < 4;
const false_chain_including_equals: bool = 1 <= 2 == 3 < 4;
const chain_including_not_equal: bool = 3 >= 2 != 3 > 1;
const false_chain_including_not_equal: bool = 3 > 2 != 2 > 1;

function main()
{
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
    Test.print_bool(chain_including_equals);
    Test.print_bool(false_chain_including_equals);
    Test.print_bool(chain_including_not_equal);
    Test.print_bool(false_chain_including_not_equal);
}
