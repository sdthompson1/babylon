module TraitExport

interface {
    type Type1: Copy + Default;  // error: the underlying type doesn't have Copy

    type Type2: Move;   // ok: "hides" Default but exports Move

    function f1<T: Move>();  // error: doesn't pass on the requirement for Default

    function f2<T: Move + Default>();  // ok: having "surplus" requirements is allowed

    type Type3: Copy;    // error: the underlying type doesn't have Copy
}

extern type Type1 : Move + Default;
type Type2 = Type1;
type Type3 = Type1;

function f1<T: Move + Default>() {}
function f2<T: Move>() {}

