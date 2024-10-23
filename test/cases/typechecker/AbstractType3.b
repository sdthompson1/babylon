module AbstractType3

interface {
    type Abs1: Copy;
    type Abs2: Copy;
}

type Abs1 = {x: i32[], y: bool};  // error, doesn't have Copy trait (but interface says it does)

datatype Abs2 = Abs5Ctor(i32[]);  // error, doesn't have Copy trait (but interface says it does)

