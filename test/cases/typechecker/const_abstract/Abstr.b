module Abstr

interface {
    type Abstr;

    const c: Abstr;  // Allowed (no initializer yet)
    ghost const g: Abstr;  // Allowed (ghost)

    extern type ExternType;
}

type Abstr = i32;

const c: Abstr = 1000;
  // Allowed, because Abstr is no longer abstract, and in any
  // case, Abstr is not explicitly mentioned in the initializer.

ghost const g: Abstr = 2000;
  // Also allowed.
