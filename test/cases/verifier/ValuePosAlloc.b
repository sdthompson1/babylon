module ValuePosAlloc

// In executable code, a term in a "value position" must not be allocated.
// (A value position is one where the value might be copied, such as the
// body of a 'let', the fields of a tuple or record expression, the
// payload of a data constructor.)

// For more info on value positions, see typechecker/ValuePosIncomplete.b.


interface {}


import Test;


datatype ABC = A | B | C;
datatype Maybe<a> = Nothing | Just(a);


function alloc_size(a: i32[*]): u64
{
    return sizeof(a);
}

function pair_size(p: {i32[*], i32}): u64
{
    return sizeof(p.0);
}

function rec_size(p: {arr: i32[*], n: i32}): u64
{
    return sizeof(p.arr);
}

function maybe_size(m: Maybe<i32[*]>): u64
{
    return match m { case Just(a) => sizeof(a)  case Nothing => u64(0) };
}

function first_size(p: (i32[*])[2]): u64
{
    return sizeof(p[0]);
}


function is_just(m: MaybeAllocTest): bool
{
    return match m { case MA_Just(_) => true  case MA_Nothing => false };
}


function ghost_arg(n: i32, ghost a: i32[*], ghost p: {i32[*], i32})
{
}



// ---------------------------------------------------------------------
// Tuple and record expressions

function tuple_argument(ref a: i32[*]): u64
{
    // The tuple itself is in a place position, but its fields are
    // in value positions.
    return pair_size({a, 1});                   // Error
}

function tuple_argument_not_allocated(ref a: i32[*]): u64
    requires !allocated(a);
{
    return pair_size({a, 1});                   // OK
}

function tuple_argument_empty(ref a: i32[*]): u64
    requires sizeof(a) == u64(0);
{
    return pair_size({a, 1});                   // OK, an empty array is not allocated
}

function tuple_projection(ref a: i32[*]): i32
{
    return {a, 1}.1;                            // Error (even though the i32[*] field is never used)
}

function record_argument(ref a: i32[*]): u64
{
    return rec_size({arr = a, n = 1});          // Error
}

function record_update_other_field(ref p: {arr: i32[*], n: i32}): u64
{
    // The 'arr' field is copied from p into the new record.
    return rec_size({p with n = 2});            // Error
}

function record_update_other_field_ok(ref p: {arr: i32[*], n: i32}): u64
    requires !allocated(p.arr);
{
    return rec_size({p with n = 2});            // OK
}

function record_update_same_field(ref p: {arr: i32[*], n: i32}, ref a: i32[*]): u64
{
    return rec_size({p with arr = a});          // Error, a might be allocated
}

function record_update_same_field_ok(ref p: {arr: i32[*], n: i32}, ref a: i32[*]): u64
    requires !allocated(a);
{
    // p.arr might be allocated, but it is not copied.
    return rec_size({p with arr = a});          // OK
}


// ---------------------------------------------------------------------
// Datatype constructors

function payload(ref a: i32[*]): u64
{
    return maybe_size(Just(a));                 // Error
}

function payload_ok(ref a: i32[*]): u64
    requires !allocated(a);
{
    return maybe_size(Just(a));                 // OK
}

function payload_extern(ref h: AllocTest): bool
{
    // Nothing is known about whether a value of type AllocTest is allocated.
    return is_just(MA_Just(h));                 // Error
}

function payload_extern_ok(ref h: AllocTest): bool
    requires !allocated(h);
{
    return is_just(MA_Just(h));                 // OK
}


// ---------------------------------------------------------------------
// Array literals

function array_literal(ref a: i32[*], ref b: i32[*]): u64
{
    return first_size([a, b]);                  // Error (twice)
}

function array_literal_one(ref a: i32[*], ref b: i32[*]): u64
    requires !allocated(a);
{
    return first_size([a, b]);                  // Error, b might be allocated
}

function array_literal_ok(ref a: i32[*], ref b: i32[*]): u64
    requires !allocated(a);
    requires !allocated(b);
{
    return first_size([a, b]);                  // OK
}


// ---------------------------------------------------------------------
// 'let' expressions

function let_body(ref a: i32[*]): u64
{
    return alloc_size(let n = 1 in a);          // Error
}

function let_body_var(ref a: i32[*]): u64
{
    return alloc_size(let x = a in x);          // Error
}

function let_body_ok(ref a: i32[*]): u64
    requires !allocated(a);
{
    return alloc_size(let x = a in x);          // OK
}


// ---------------------------------------------------------------------
// 'if' and 'match' expressions

function if_arms(c: bool, ref a: i32[*], ref b: i32[*]): u64
{
    return alloc_size(if c then a else b);      // Error (twice)
}

function if_one_arm(c: bool, ref a: i32[*], ref b: i32[*]): u64
    requires !allocated(a);
{
    return alloc_size(if c then a else b);      // Error, b might be allocated
}

function if_arm_not_taken(c: bool, ref a: i32[*], ref b: i32[*]): u64
    requires c ==> !allocated(a);
    requires !c ==> !allocated(b);
{
    // OK, the value only has to be non-allocated if the branch is taken
    return alloc_size(if c then a else b);
}

function match_arms(c: ABC, ref a: i32[*], ref b: i32[*]): u64
{
    return alloc_size(match c { case A => a  case _ => b });   // Error (twice)
}

function match_arms_index(c: ABC, ref a: i32[*], ref b: i32[*]): i32
    requires sizeof(a) > u64(0);
    requires sizeof(b) > u64(0);
{
    return (match c { case A => a  case _ => b })[0];          // Error (twice)
}

function match_arm_not_taken(c: ABC, ref a: i32[*], ref b: i32[*]): u64
    requires c == A;
    requires !allocated(a);
{
    return alloc_size(match c { case A => a  case _ => b });   // OK
}

function match_pattern_var(ref m: Maybe<i32[*]>, ref b: i32[*]): u64
    requires !allocated(b);
{
    // Binding x is fine (nothing is copied), but using it as the result
    // of the arm is not.
    return alloc_size(match m { case Just(x) => x  case Nothing => b });   // Error, x might be allocated
}

function match_converted(c: bool, ref f: i32[3], ref a: i32[*]): u64
    requires sizeof(a) == u64(3);
{
    // OK. The second arm is converted to the type of the first, i32[3],
    // and a value of that type is never allocated.
    return sizeof(match c { case true => f  case false => a });
}


// ---------------------------------------------------------------------
// Generic code

function generic<T>(ref x: T): i32
{
    return {x, 1}.1;                            // Error, x might be allocated
}

function generic_ok<T>(ref x: T): i32
    requires !allocated(x);
{
    return {x, 1}.1;                            // OK
}


// ---------------------------------------------------------------------
// Place positions: these are all fine

function places(ref a: i32[*], ref p: {arr: i32[*], n: i32}, ref q: {i32[*], i32},
                ref m: Maybe<i32[*]>): u64
    requires sizeof(a) > u64(0);
{
    var n1 = alloc_size(a);                     // function argument
    var n2 = sizeof(a);                         // operand of sizeof
    var x1 = a[0];                              // array being indexed
    var n3 = sizeof(p.arr);                     // record in a field projection
    var n4 = rec_size(p);
    var n5 = pair_size(q);
    var n6 = maybe_size(m);
    var n7 = let x = a in sizeof(x);            // right-hand-side of a let
    var n8 = let x = p in sizeof(x.arr);
    var n9 = match a { case x => sizeof(x) };   // scrutinee of a match
    var n10 = match q { case {x, _} => sizeof(x) };
    return n1;
}


// ---------------------------------------------------------------------
// Value positions that cannot be allocated: these are all fine

function not_allocated(c: bool, ref a: i32[*], ref b: i32[*], ref f: i32[3]): u64
    requires sizeof(a) > u64(0);
    requires sizeof(b) > u64(0);
{
    var n1 = if c then sizeof(a) else sizeof(b);
    var x1 = match c { case true => a[0]  case false => b[0] };
    var t1 = {sizeof(a), a[0]};
    var m1 = Just(a[0]);
    var x2 = {f, 1}.1;
    var n2 = sizeof(if c then f else f);
    return n1;
}


// ---------------------------------------------------------------------
// Ghost code: these are all fine

ghost function ghost_function(c: bool, a: i32[*], b: i32[*], p: {arr: i32[*], n: i32}): u64
{
    var t1 = {a, 1};
    var t2 = {p with n = 2};
    var m1 = Just(a);
    var l1 = [a, b];
    var x1 = if c then a else b;
    var x2 = let n = 1 in a;
    return sizeof(x1);
}

function ghost_statements(c: bool, ref a: i32[*], ref b: i32[*])
    requires sizeof({a, 1}.0) == sizeof(a);
    ensures sizeof(let n = 1 in a) == sizeof(a);
{
    ghost var t1 = {a, 1};
    ghost var m1 = Just(a);
    ghost var x1 = if c then a else b;
    assert sizeof(match c { case true => a  case false => a }) == sizeof(a);

    // Ghost arguments of an executable call
    ghost_arg(1, if c then a else b, {a, 1});
}
