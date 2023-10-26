module Maybe

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

    ghost function from_just<T>(x: Maybe<T>): T
        requires is_just<T>(x);
    {
        match x {
        case Just(j) => return j;
        }
    }
}
