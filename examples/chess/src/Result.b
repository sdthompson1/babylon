module Result

import String;

interface {
    datatype Result<T> = Ok(T) | Error(u8[*]);

    function is_ok<T> (r: Result<T>): bool
    {
        match r {
        case Error(_) => return false;
        case Ok(_) => return true;
        }
    }

    function is_error<T> (r: Result<T>): bool
    {
        return !is_ok<T>(r);
    }

    ghost function from_ok<T> (r: Result<T>) : T
        requires is_ok<T>(r);
    {
        match r {
        case Ok(value) =>
            return value;
        }
    }

    // this says that the error message, if it exists, is a valid C string
    ghost function valid_c_result<T> (r: Result<T>): bool
    {
        return match r {
        case Ok(_) => true
        case Error(msg) => valid_string(msg)
        };
    }
}
