module Default

interface {

    // Sometimes we need to refer to the "default" value of a given type in pre-
    // or post-conditions, and this function is useful for that.

    ghost function default<T>(): T
    {
        var x: T;
        return x;
    }

}
