module Default

interface {
    ghost function default<T>(): T;
}

ghost function default<T>(): T
{
    var d: T;
    return d;
}
