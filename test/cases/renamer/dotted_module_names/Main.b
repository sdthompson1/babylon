module Main

interface {}

import Foo.Bar.Mod1;
import Foo.Bar.Mod2;

import Foo.Bar.Mod1 as Alias.One;  // Dotted alias

const a: i32 = x;   // Error, could be Mod1.x or Mod2.x

const b: i32 = Foo.Bar.Mod1.x;   // Valid
const c: i32 = Foo.Bar.Mod2.x;   // Valid

const d: i32 = Foo.Bar.Mod1.y;   // Not found: y is not part of Foo.Bar.Mod1
const e: i32 = Foo.Bad.Mod1.y;   // Not found: Foo.Bad.Mod1 isn't an imported module

const p: IntAlias = 0;    // Error, could be Mod1.IntAlias or Mod2.IntAlias
const q: Foo.Bar.Mod1.IntAlias = 0;  // ok
const r: Foo.Bar.Mod2.IntAlias = 0;  // ok

const s: Foo.Bar.Mod1.OtherType = 0;  // Not found: OtherType is not part of Foo.Bar.Mod1
const t: Foo.Bad.Mod1.OtherType = 0;  // Not found: Foo.Bad.Mod1 isn't an imported module

const a1: i32 = Alias.One.x;   // valid
const a2: i32 = Alias.One.y;   // y not found in Alias.One (Foo.Bar.Mod1)

const a3: Alias.One.IntAlias = 0;  // valid
const a4: Alias.One.OtherType = 0; // OtherType not found in Alias.One (Foo.Bar.Mod1)
