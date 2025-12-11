-- test suggest_for independently of any library annotations

@[suggest_for String.test0 String.test1 String.test2]
public def String.foo (x: String) := x.length + 1

@[simp, grind, suggest_for test1 String.test2]
public def String.bar (x: String) := x.length + 1

@[suggest_for String.test1 String.test2, inline]
public def String.baz (x: String) := x.length + 1

@[suggest_for String.test2, always_inline]
public def otherFoo (x: String) := x.length + 1

@[suggest_for String.test2]
public def otherBaz (x: String) := x.length + 1

@[suggest_for _root_.String.test2]
public def Nat.otherBar (x: String) := x.length + 1

-- Single suggested replacement
/--
error: Invalid field `test0`: The environment does not contain `String.test0`, so it is not possible to project the field `test0` from an expression
  "abc"
of type `String`

Hint: Perhaps you meant `String.foo` in place of `String.test0`:
  .t̵e̵s̵t̵0̵f̲o̲o̲
-/
#guard_msgs in
#check "abc".test0

/--
error: Unknown constant `String.test0`

Hint: Perhaps you meant `String.foo` in place of `String.test0`:
  [apply] `String.foo`
-/
#guard_msgs in
#check String.test0

/--
error: Unknown constant `String.test0`

Hint: Perhaps you meant `String.foo` in place of `String.test0`:
  [apply] `String.foo`
---
info: fun x1 x2 x3 => sorry : (x1 : ?m.1) → (x2 : ?m.5 x1) → (x3 : ?m.6 x1 x2) → ?m.7 x1 x2 x3
-/
#guard_msgs in
#check (String.test0 · · ·)

-- Two suggested replacements: the bar replacement is for `test1`, which does not apply
/--
error: Invalid field `test1`: The environment does not contain `String.test1`, so it is not possible to project the field `test1` from an expression
  "abc"
of type `String`

Hint: Perhaps you meant one of these in place of `String.test1`:
  [apply] `String.foo`
  [apply] `String.baz`
-/
#guard_msgs in
#check "abc".test1

/--
error: Unknown constant `String.test1`

Hint: Perhaps you meant one of these in place of `String.test1`:
  [apply] `String.foo`
  [apply] `String.baz`
-/
#guard_msgs in
#check String.test1

-- Three suggested replacements (filters the ones with other types)
/--
error: Invalid field `test2`: The environment does not contain `String.test2`, so it is not possible to project the field `test2` from an expression
  "abc"
of type `String`

Hint: Perhaps you meant one of these in place of `String.test2`:
  [apply] `String.foo`
  [apply] `String.baz`
  [apply] `String.bar`
-/
#guard_msgs in
#check "abc".test2

-- Five suggested replacements: does not filter out non-`String` functions, but `_root_` prefix won't ever match.
/--
error: Unknown constant `String.test2`

Hint: Perhaps you meant one of these in place of `String.test2`:
  [apply] `otherBaz`
  [apply] `String.foo`
  [apply] `otherFoo`
  [apply] `String.baz`
  [apply] `String.bar`
-/
#guard_msgs in
#check String.test2


namespace Foo
inductive Bar where | one | two | three

attribute [suggest_for Foo.Bar.first] Bar.one
end Foo

namespace Foo.Bar
attribute [suggest_for Foo.Bar.second Foo.more] Bar.two

@[suggest_for Foo.Bar.toStr]
def toString : Foo.Bar → String
 | .one => "one"
 | .two => "two"
 | .three => "three"
end Foo.Bar

attribute [suggest_for Foo.Bar.third Foo.more] Foo.Bar.three

@[suggest_for Foo.Bar.toNum]
def Foo.Bar.toNat : Foo.Bar → Nat
  | .one => 1
  | .two => 2
  | .three => 3

/--
error: Invalid field `toNum`: The environment does not contain `Foo.Bar.toNum`, so it is not possible to project the field `toNum` from an expression
  Foo.Bar.three
of type `Foo.Bar`

Hint: Perhaps you meant `Foo.Bar.toNat` in place of `Foo.Bar.toNum`:
  .t̵o̵N̵u̵m̵t̲o̲N̲a̲t̲
-/
#guard_msgs in
#eval Foo.Bar.three.toNum

/--
error: Invalid field `toStr`: The environment does not contain `Foo.Bar.toStr`, so it is not possible to project the field `toStr` from an expression
  Foo.Bar.two
of type `Foo.Bar`

Hint: Perhaps you meant `Foo.Bar.toString` in place of `Foo.Bar.toStr`:
  .t̵o̵S̵t̵r̵t̲o̲S̲t̲r̲i̲n̲g̲
-/
#guard_msgs in
#eval Foo.Bar.two.toStr

/- ----- -/

/--
error: Unknown constant `Foo.Bar.first`

Hint: Perhaps you meant `Foo.Bar.one` in place of `Foo.Bar.first`:
  [apply] `Foo.Bar.one`
-/
#guard_msgs in
#check Foo.Bar.first

/-- error: Unknown identifier `Bar.second` -/
#guard_msgs in
#check Bar.second

/-- error: Unknown identifier `third` -/
#guard_msgs in
#check third

/- ----- -/

namespace Foo
/--
error: Unknown constant `Foo.Bar.first`

Hint: Perhaps you meant `Bar.one` in place of `Foo.Bar.first`:
  [apply] `Bar.one`
-/
#guard_msgs in
#check Foo.Bar.first

/--
error: Unknown constant `Foo.Bar.second`

Hint: Perhaps you meant `Bar.two` in place of `Bar.second`:
  [apply] `Bar.two`
-/
#guard_msgs in
#check Bar.second

/-- error: Unknown identifier `third` -/
#guard_msgs in
#check third
end Foo

/- ----- -/

namespace Foo.Bar
/--
error: Unknown constant `Foo.Bar.first`

Hint: Perhaps you meant `one` in place of `Foo.Bar.first`:
  [apply] `one`
-/
#guard_msgs in
#check Foo.Bar.first

/--
error: Unknown constant `Foo.Bar.second`

Hint: Perhaps you meant `two` in place of `Bar.second`:
  [apply] `two`
-/
#guard_msgs in
#check Bar.second

-- TODO: give a suggestion here!
/-- error: Unknown identifier `third` -/
#guard_msgs in
#check third
end Foo.Bar

/- ----- -/

-- Don't suggest an ambiguous replacement
namespace Foo2
inductive Bar where | one | two | three
attribute [suggest_for Foo2.Bar.first] Bar.one
end Foo2

namespace Whatever
open Foo
open Foo2
/--
error: overloaded, errors ⏎
  Unknown constant `Foo2.Bar.first`
  ⏎
  Hint: Perhaps you meant `Foo2.Bar.one` in place of `Bar.first`:
    [apply] `Foo2.Bar.one`
  ⏎
  Unknown constant `Foo.Bar.first`
  ⏎
  Hint: Perhaps you meant `Foo.Bar.one` in place of `Bar.first`:
    [apply] `Foo.Bar.one`
-/
#guard_msgs in
#eval Bar.first
end Whatever

-- Limitation: we ought to suggest `Foo2.Bar.one` here, but we're relying on the upstream
-- infrastructure that decides that `Bar.first` means `Foo.Bar.first` in this context.
namespace Foo
open Foo2
/--
error: Unknown constant `Foo.Bar.first`

Hint: Perhaps you meant `Bar.one` in place of `Bar.first`:
  [apply] `Bar.one`
-/
#guard_msgs in
#eval Bar.first
end Foo


inductive MyBool where | tt | ff

attribute [suggest_for MyBool.true] MyBool.tt
attribute [suggest_for MyBool.false] MyBool.ff

@[suggest_for MyBool.not]
def MyBool.swap : MyBool → MyBool
  | tt => ff
  | ff => tt

/--
error: Unknown constant `MyBool.true`

Hint: Perhaps you meant `MyBool.tt` in place of `MyBool.true`:
  [apply] `MyBool.tt`
-/
#guard_msgs in
example := MyBool.true

/--
error: Invalid field `not`: The environment does not contain `MyBool.not`, so it is not possible to project the field `not` from an expression
  MyBool.tt
of type `MyBool`

Hint: Perhaps you meant `MyBool.swap` in place of `MyBool.not`:
  .n̵o̵t̵s̲w̲a̲p̲
-/
#guard_msgs in
example := MyBool.tt.not

/--
error: Invalid field `not`: The environment does not contain `MyBool.not`, so it is not possible to project the field `not` from an expression
  (fun x => if x < 3 then MyBool.tt else MyBool.ff) 4
of type `MyBool`

Hint: Perhaps you meant `MyBool.swap` in place of `MyBool.not`:
  .n̵o̵t̵s̲w̲a̲p̲
-/
#guard_msgs in
example := ((fun x => if x < 3 then MyBool.tt else .ff) 4).not


@[suggest_for MyBool.not]
def MyBool.justFalse : MyBool → MyBool
  | _ => ff

/--
error: Invalid field `not`: The environment does not contain `MyBool.not`, so it is not possible to project the field `not` from an expression
  (fun x => if x < 3 then MyBool.tt else MyBool.ff) 4
of type `MyBool`

Hint: Perhaps you meant one of these in place of `MyBool.not`:
  [apply] `MyBool.justFalse`
  [apply] `MyBool.swap`
-/
#guard_msgs in
example := ((fun x => if x < 3 then MyBool.tt else .ff) 4).not
