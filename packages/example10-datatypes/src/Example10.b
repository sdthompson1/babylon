// Example 10 -- Datatypes and Typedefs.

module Example10

interface {
    function main();
}

import Console;


// The datatype keyword allows one to invent new types.

// The simplest case is where the new type takes one of a given (finite) set
// of values (this is a so-called enumerated type).

// For example:

datatype Colour = Red | Green | Blue;
datatype Fruit = Apple | Banana | Pear;

// The different values ("Red", "Green" and so on) are known as constructors.

// We can use the new type(s) anywhere a normal type could be used.
// For example they can be function parameters:

function colour_func(col: Colour)
{
    // Datatypes can be used in a match statement:
    match col {
    case Red =>
        println("The colour is red");

    case Green =>
        println("The colour is green");

    case Blue =>
        println("The colour is blue");
    }
}

function fruit_func(fruit: Fruit)
{
    // Note that (similar to records and tuples) it is not currently supported
    // to use == with datatypes, in executable code (although it is allowed
    // in verification contexts). So for example, this is allowed:

    assert fruit == Apple || fruit == Banana || fruit == Pear;

    // But this is not, because == can only be used with numbers and booleans
    // in executable code (currently):

    // if fruit == Banana { println("Got a banana"); }

    // Instead you would have to do something like:

    match fruit {
    case Banana =>
        println("Got a banana");
    case _ =>
    }
}

function fun1()
{
    // We can also (of course) make variables of a datatype.
    
    var col1: Colour = Green;
    var col2: Colour = Blue;

    var fruit1 = Apple;
    var fruit2 = Banana;

    colour_func(col1);
    colour_func(col2);

    fruit_func(fruit1);
    fruit_func(fruit2);
}


// Datatypes also have a feature where each constructor can carry a "payload"
// of some given type. For example, the following datatype has three
// constructors, each of which carries a payload of type i32.

datatype Payload = A(i32) | B(i32) | C(i32);

// It might be used as follows:

function fun2()
{
    var p: Payload = B(100);

    match p {
    case A(x) =>
        println("case A");
        
    case B(x) =>
        println("case B");
        print("the payload is: ");
        print_i32(x);
        println("");

    case C(_) =>
    }
}

// Often we want a constructor to carry two or more values in its payload.
// In that case we would make the payload be a tuple or record type. e.g.

datatype MultiPayload = X(i32) | Y({i32,i32}) | Z({p:i32, q:i32, r:i32});

// As a shortcut, if the payload is a tuple or record, it is allowed
// to omit the round brackets ( ), so in the above I could have written
// Y{i32,i32} instead of Y({i32,i32}).


// Here is an example application of a datatype. The following datatype
// represents a simple class of mathematical expressions.

datatype Expr =
    Constant(i32) |
    Plus{i32, i32} |
    Times{i32, i32} |
    Negative(i32);

// Here is a function that can evaluate such expressions. (The function returns
// a 64-bit result, because e.g. adding or multiplying two i32's might result
// in a number bigger than 32 bits.)

function eval_expr(expr: Expr): i64
{
    match expr {
    case Constant(x) =>
        // x will be converted to i64 automatically.
        return x;

    case Plus{x, y} =>
        // If we write x + y, this will attempt to do i32 addition, which
        // might overflow (and the verifier will catch this).
        // We convert x and y to i64 to avoid this.
        return i64(x) + i64(y);

    case Times{x, y} =>
        return i64(x) * i64(y);

    case Negative(x) =>
        // Technically -x could also overflow
        // (because -I32_MIN is equal to I32_MAX + 1).
        // So converting to i64 before we negate is necessary.
        return -i64(x);
    }
}

// Example of usage of the above.

function fun3()
{
    print_i64(eval_expr(Plus{100, 200}));   // prints 300
    println("");

    print_i64(eval_expr(Negative(123456789)));  // prints -123456789
    println("");

    print_i64(eval_expr(Times{1000000, 2000000}));  // prints 2000000000000
    println("\n");
}


// At this point some readers might be wondering why we didn't define Expr
// recursively, perhaps like this:

// datatype Expr = Constant(i32) | Plus{Expr,Expr} | Times{Expr,Expr} | Negative(Expr)

// Unfortunately Babylon does not support recursion at the moment, so the above
// would be rejected. This is something I would like to address in a future
// version of the language, but for now neither recursive datatypes, nor
// recursive functions, are allowed.


// The final thing to mention for this demo is typedefs.

// A typedef is simply a synonym for another type.

// For example if we were using a lot of records of type
// {item_id: u32, price:i32, quantity:i32} in our application, we might like to give
// that type a name, to save typing (no pun intended):

type StockInfo = {item_id: u32, price: i32, quantity: i32};

// Then we would be able to use "StockInfo" instead of typing out the full
// record name, e.g.

function print_stock(info: StockInfo)
{
    print("We have ");
    print_i32(info.quantity);
    print(" units of item id ");
    print_u32(info.item_id);
    println(" in stock.");
}

function fun4()
{
    // Note: the explicit casts to u32 (in the item_ids below) are required,
    // because otherwise the record would end up with type {item_id:i32, ...}
    // instead of {item_id:u32, ...}, and a type mismatch error would be
    // generated. (Record fields must always match exactly -- they are never
    // automatically converted from one type to another.)
    
    var stock1: StockInfo = {item_id = u32(99), price = 100, quantity = 25};
    var stock2: StockInfo = {item_id = u32(456), price = 120, quantity = 50};
    
    print_stock(stock1);
    print_stock(stock2);
}


function main()
{
    fun1();
    fun2();
    fun3();
    fun4();
}
