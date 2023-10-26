// "extern" is considered to be providing an implementation for a function,
// so defining a function as "extern" in both interface and impl is considered
// a "multiple implementation" error.

module DoubleExtern
interface {
    extern function foo();
}

extern function foo();
