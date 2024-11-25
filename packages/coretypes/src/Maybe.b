module Maybe

// Defines a "Maybe" type and some helper functions.

interface {
    datatype Maybe<T> = Nothing | Just(T);

    function is_nothing<T>(x: Maybe<T>): bool
    {
        match x {
        case Nothing => return true;
        case Just(_) => return false;
        }
    }

    function is_just<T>(x: Maybe<T>): bool
    {
        match x {
        case Nothing => return false;
        case Just(_) => return true;
        }
    }

    function from_just<T>(x: Maybe<T>): T
        requires is_just<T>(x);
        requires !allocated(x);
    {
        match x {
        case Just(j) => return j;
        }
    }

    ghost function from_just_ghost<T>(x: Maybe<T>): T
        requires is_just<T>(x);
    {
        match x {
        case Just(j) => return j;
        }
    }

    function from_maybe<T>(x: Maybe<T>, def: T): T
        requires !allocated(x);
        requires !allocated(def);
    {
        match x {
        case Just(j) => return j;
        case Nothing => return def;
        }
    }

    ghost function from_maybe_ghost<T>(x: Maybe<T>, def: T): T
    {
        match x {
        case Just(j) => return j;
        case Nothing => return def;
        }
    }
}
