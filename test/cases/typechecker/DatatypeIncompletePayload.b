module DatatypeIncompletePayload

// Datatype payloads must be complete types: they must not be, or
// contain, an incomplete array type.

interface {}

type T = i32[];

datatype D1 = D1(i32[]);                    // Error
datatype D2 = D2({i32[], bool});            // Error
datatype D3 = D3((i32[])[3]);               // Error
datatype D4 = D4(T);                        // Error, incomplete type hidden in a typedef
datatype D5 = D5a(i32[]) | D5b({i32, T});   // Error (twice)

// These are all fine.
datatype Ok1 = Ok1a(i32[*]) | Ok1b(i32[3]) | Ok1c;
datatype Ok2 = Ok2({(i32[*])[2], bool});
datatype Ok3<a> = Ok3(a[*]);
