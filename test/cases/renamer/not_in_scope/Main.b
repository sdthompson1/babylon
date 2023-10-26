module Main
interface {}

import Import as Imp1;

// Unqualified name doesn't exist
const foo: i32 = bar;

// Qualified name from self-module, doesn't exist
// Error will mention "Main.notexist" because the compiler noticed that Main is a module name.
const a: i32 = Main.notexist;

// Qualified name from an imported module, doesn't exist
// Error will mention "Imp1.wrongname" becaues the compiler noticed that Imp1 is a module name.
const b: i32 = Imp1.wrongname;

// Using "Imp1" as a variable. Reports "Not in scope Imp1" which isn't quite right I guess,
// but good enough.
const c: i32 = Imp1;

// Wrong names to left or right of dot (or both)
const d: i32 = foo.wrong1;   // This is a type error: trying to project field "wrong1" from an i32.
const e: i32 = wrong2.foo;
const f: i32 = wrong3.wrong4;   // 'wrong3' not in scope, but for all we know, wrong4 might be a field name (this isn't checked by the renamer), so 'wrong4' is ok.
