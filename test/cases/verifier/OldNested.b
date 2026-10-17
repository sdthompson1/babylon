module OldNested
interface {}
  function f(ref x: i32)
    requires 0 <= x <= 1000;
    ensures x == old(x) + 1;

    // Inside the outer 'old', x refers to the old value of x, even after
    // the inner 'old' has ended.
    ensures old(old(x) + x) == 2 * old(x);

    // Negative case.
    ensures old(old(x) + x) == old(x) + x;
  {
    x = x + 1;
  }
