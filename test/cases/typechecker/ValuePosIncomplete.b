module ValuePosIncomplete

// In executable code, a term in a "value position" must have a complete
// type (i.e. the type must not contain any incomplete array type such
// as i32[]).
//
// A value position is one where the value of the term might be copied.
// For expressions, the value positions include:
//  - the right-hand-sides of the cases of a 'match' expression, and the
//    'then' and 'else' parts of an 'if' expression;
//  - the body of a 'let' expression (the part after 'in');
//  - the fields of a tuple or record expression (including the fields
//    that a record update expression carries over unchanged);
//  - the elements of an array literal;
//  - the payload of a datatype constructor (not tested here: datatype
//    declarations with incomplete payloads are already illegal, see
//    DatatypeIncompletePayload.b).

// None of these rules apply to ghost code.

// The statement-level value positions -- 'var' initialisers and the
// right-hand-sides of assignments -- are tested elsewhere.




interface {}

datatype ABC = A | B | C;

function size_of(a: i32[]): u64
{
    return sizeof(a);
}

function alloc_size(a: i32[*]): u64
{
    return sizeof(a);
}

function pair_size(p: {i32[], i32}): u64
{
    return sizeof(p.0);
}

function rec_size(p: {arr: i32[], n: i32}): u64
{
    return sizeof(p.arr);
}

function ghost_arg(n: i32, ghost a: i32[], ghost p: {i32[], i32})
{
}



// ---------------------------------------------------------------------
// 'if' expressions

function if_sizeof(c: bool, ref r: i32[], ref s: i32[]): u64
{
    return sizeof(if c then r else s);          // Error
}

function if_index(c: bool, ref r: i32[], ref s: i32[]): i32
    requires sizeof(r) > u64(0);
    requires sizeof(s) > u64(0);
{
    return (if c then r else s)[0];             // Error
}

function if_argument(c: bool, ref r: i32[], ref s: i32[]): u64
{
    // The 'if' itself is in a place position, but the 'then' and 'else'
    // terms are still in value positions.
    return size_of(if c then r else s);         // Error
}

function if_let_rhs(c: bool, ref r: i32[], ref s: i32[]): u64
{
    return let x = (if c then r else s) in sizeof(x);   // Error (in the 'if', not the 'let')
}

function if_nested(c: bool, d: bool, ref r: i32[], ref s: i32[]): u64
{
    return if c then u64(0) else sizeof(if d then r else s);   // Error (in the inner 'if' only)
}


// ---------------------------------------------------------------------
// 'match' expressions

function match_sizeof(c: ABC, ref r: i32[], ref s: i32[]): u64
{
    return sizeof(match c { case A => r  case _ => s });   // Error
}

function match_index(c: ABC, ref r: i32[], ref s: i32[]): i32
    requires sizeof(r) > u64(0);
    requires sizeof(s) > u64(0);
{
    return (match c { case A => r  case _ => s })[0];      // Error
}

function match_converted(c: ABC, ref r: i32[], ref s: i32[10], ref t: i32[*]): u64
{
    // The second and third arms are converted to the type of the first, i32[].
    return sizeof(match c { case A => r  case B => s  case C => t });   // Error
}

function match_pattern_var(ref r: i32[]): u64
{
    return sizeof(match r { case x => x });                // Error
}

function match_scrutinee(c: bool, ref r: i32[], ref s: i32[]): u64
{
    return match (if c then r else s) { case x => sizeof(x) };   // Error (in the 'if', not the 'match')
}


// ---------------------------------------------------------------------
// 'let' expressions

function let_sizeof(ref r: i32[]): u64
{
    return sizeof(let n = 1 in r);              // Error
}

function let_argument(ref r: i32[]): u64
{
    return size_of(let x = r in x);             // Error
}


// ---------------------------------------------------------------------
// Tuple and record expressions

function tuple_argument(ref r: i32[]): u64
{
    return pair_size({r, 1});                   // Error
}

function tuple_projection(ref r: i32[]): i32
{
    return {r, 1}.1;                            // Error (even though the i32[] field is never used)
}

function record_argument(ref r: i32[]): u64
{
    return rec_size({arr = r, n = 1});          // Error
}

function record_update_other_field(ref p: {arr: i32[], n: i32}): u64
{
    // The 'arr' field is copied from p into the new record.
    return rec_size({p with n = 2});            // Error
}

function record_update_same_field(ref p: {arr: i32[], n: i32}, ref r: i32[]): u64
{
    return rec_size({p with arr = r});          // Error
}


// ---------------------------------------------------------------------
// Array literals

function array_literal(ref r: i32[], ref s: i32[]): u64
{
    return sizeof([r, s]);                      // Error
}

function array_literal_one(ref r: i32[]): u64
{
    return sizeof([r]);                         // Error
}

function array_literal_nested(ref p: {arr: i32[], n: i32}): u64
{
    // The element type contains an incomplete array type.
    return sizeof([p]);                         // Error
}

function array_literal_index(ref r: i32[], ref s: i32[]): u64
{
    return sizeof([r, s][0]);                   // Error
}


// ---------------------------------------------------------------------
// Place positions: these are all fine

function places(ref r: i32[], ref p: {arr: i32[], n: i32}, ref q: {i32[], i32}): u64
    requires sizeof(r) > u64(0);
{
    var n1 = size_of(r);                        // function argument
    var n2 = sizeof(r);                         // operand of sizeof
    var x1 = r[0];                              // array being indexed
    var n3 = sizeof(p.arr);                     // record in a field projection
    var n4 = rec_size(p);
    var n5 = pair_size(q);
    var n6 = let x = r in sizeof(x);            // right-hand-side of a let
    var n7 = let x = p in sizeof(x.arr);
    var n8 = match r { case x => sizeof(x) };   // scrutinee of a match
    var n9 = match q { case {x, _} => sizeof(x) };
    ref r2 = r;
    return n1;
}


// ---------------------------------------------------------------------
// Value positions with complete types: these are all fine

function complete(c: ABC, b: bool, ref r: i32[], ref s: i32[],
                  ref f1: i32[10], ref f2: i32[10], ref a1: i32[*], ref a2: i32[*]): u64
    requires sizeof(r) > u64(0);
    requires sizeof(s) > u64(0);
{
    // The arms use incomplete arrays, but do not have incomplete types.
    var n1 = if b then sizeof(r) else sizeof(s);
    var x1 = match c { case A => r[0]  case _ => s[0] };
    var n2 = let x = r in sizeof(x);
    var t1 = {sizeof(r), r[0]};

    // Fixed-size and allocatable array types are complete.
    var n3 = sizeof(if b then f1 else f2);
    var n4 = alloc_size(if b then a1 else a2);
    var n5 = alloc_size(let n = 1 in a1);
    var x2 = {f1, 1}.1;

    // The arms are converted to the type of the first arm, which is complete.
    var n6 = sizeof(match c { case A => f1  case B => r  case C => a1 });

    // Array literals with complete element types. In the second one, r is
    // converted to the type of the first element, which is complete.
    var n7 = sizeof([f1, f2]);
    var n8 = sizeof([f1, r]);

    return n1;
}


// ---------------------------------------------------------------------
// Ghost code: these are all fine

ghost function ghost_function(c: bool, r: i32[], s: i32[], p: {arr: i32[], n: i32}): u64
{
    var n1 = sizeof(if c then r else s);
    var n2 = sizeof(match c { case true => r  case false => s });
    var n3 = sizeof(let n = 1 in r);
    var t1 = {r, 1};
    var t2 = {p with n = 2};
    return n1;
}

function ghost_statements(c: bool, ref r: i32[], ref s: i32[], ref p: {arr: i32[], n: i32})
    requires sizeof(if c then r else s) > u64(0);
    ensures sizeof(let n = 1 in r) == sizeof(r);
{
    ghost var n1 = sizeof(if c then r else s);
    ghost var t1 = {r, 1};
    ghost var t2 = {p with n = 2};
    assert sizeof(match c { case true => r  case false => s }) > u64(0);

    // Ghost arguments of an executable call
    ghost_arg(1, if c then r else s, {r, 1});
}
