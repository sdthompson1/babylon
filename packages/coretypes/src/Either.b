module Either

interface {
    datatype Either<L, R> = Left(L) | Right(R);

    function is_left<L, R> (e: Either<L, R>): bool
    {
        match e {
        case Left(_) => return true;
        case Right(_) => return false;
        };
    }

    function is_right<L, R> (e: Either<L, R>): bool
    {
        match e {
        case Left(_) => return false;
        case Right(_) => return true;
        };
    }

    function from_left<L, R> (e: Either<L, R>) : L
        requires is_left(e);
        requires !allocated(e);
    {
        match e {
        case Left(value) => return value;
        }
    }

    function from_right<L, R> (e: Either<L, R>) : R
        requires is_right(e);
        requires !allocated(e);
    {
        match e {
        case Right(value) => return value;
        }
    }

    ghost function from_left_ghost<L, R> (e: Either<L, R>) : L
        requires is_left(e);
    {
        match e {
        case Left(value) => return value;
        }
    }

    ghost function from_right_ghost<L, R> (e: Either<L, R>) : R
        requires is_right(e);
    {
        match e {
        case Right(value) => return value;
        }
    }
}
