module PrePostErrors
interface {
  function f()
    requires 100;
    ensures 200;

  function g(): bool
    ensures return;           // OK
    ensures return == 1;      // Error

  function pre_after_post()
    requires 1 < 2;
    ensures 2 < 3;
    requires 3 < 4;    // Error
}
