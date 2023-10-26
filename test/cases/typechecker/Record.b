module Record
interface {}
  const a: {f1: i32, f2: bool} = {f1=1, f2=false};
  const b: {f1: i32} = {f1=false};   // Error, type mismatch

  const c: {f1: i32, f2: bool} = { a with f1 = 2 };
  const d: {f1: i32, f2: bool} = { a with f1 = false };  // Error, type mismatch
  const e: {f1: i32, f2: bool} = { a with xx = false };  // Error, updating nonexistent field
  const f: {f1: i32, f2: bool} = { a with f1 = 1, f1 = 2 };  // Error, updating same field twice
  const g: {f1: i32, f2: bool} = { 100 with f1 = 1 };   // Error, updating something that's not a record
  const h: {f1: i32, f2: bool} = { a with 1, false };   // Error, trying to update without using the field-names

  const i = a(1);          // Error, trying to "call" a record
  const j = a(1,2);        // Error, trying to "call" a record
  const k = a({f1=1},{f2=false});   // Error, trying to "call" a record
  const l = a({f1=1});   // Error, trying to "call" a record

  const m = {(1+true) with a=1};  // Type error in the lhs of a record-update expr

  function func() {}
  const n = { func, 1 };    // Functions not allowed in records
