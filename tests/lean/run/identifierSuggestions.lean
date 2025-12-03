@[suggest_for String.test0, String.test1, String.test2]
public def String.foo (x: String) := x.length + 1

@[suggest_for test1, String.test2]
public def String.bar (x: String) := x.length + 1

@[suggest_for String.test1, String.test2]
public def String.baz (x: String) := x.length + 1

@[suggest_for String.test2]
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

Hint: Perhaps you meant one of these in place of `String.test0`:
  [apply] `String.foo`: "abc".foo
-/
#guard_msgs in
#check "abc".test0

/--
error: Unknown constant `String.test0`

Hint: Perhaps you meant `String.foo` in place of `String.test0`:
  S̵t̵r̵i̵n̵g̵.̵t̵e̵s̵t̵0̵S̲t̲r̲i̲n̲g̲.̲f̲o̲o̲
-/
#guard_msgs in
#check String.test0

-- Two suggested replacements: the bar replacement is for `test1`, which does not apply
/--
error: Invalid field `test1`: The environment does not contain `String.test1`, so it is not possible to project the field `test1` from an expression
  "abc"
of type `String`

Hint: Perhaps you meant one of these in place of `String.test1`:
  [apply] `String.baz`: "abc".baz
  [apply] `String.foo`: "abc".foo
-/
#guard_msgs in
#check "abc".test1

/--
error: Unknown constant `String.test1`

Hint: Perhaps you meant one of these in place of `String.test1`:
  • S̵t̵r̵i̵n̵g̵.̵t̵e̵s̵t̵1̵S̲t̲r̲i̲n̲g̲.̲b̲a̲z̲
  • S̵t̵r̵i̵n̵g̵.̵t̵e̵s̵t̵1̵S̲t̲r̲i̲n̲g̲.̲f̲o̲o̲
-/
#guard_msgs in
#check String.test1

-- Three suggested replacements (filters the ones with other types)
/--
error: Invalid field `test2`: The environment does not contain `String.test2`, so it is not possible to project the field `test2` from an expression
  "abc"
of type `String`

Hint: Perhaps you meant one of these in place of `String.test2`:
  [apply] `String.bar`: "abc".bar
  [apply] `String.baz`: "abc".baz
  [apply] `String.foo`: "abc".foo
-/
#guard_msgs in
#check "abc".test2

-- Five suggested replacements: does not filter out non-`String` functions, but `_root_` prefix won't ever match.
/--
error: Unknown constant `String.test2`

Hint: Perhaps you meant one of these in place of `String.test2`:
  • S̵t̵r̵i̵n̵g̵.̵t̵e̵s̵t̵2̵S̲t̲r̲i̲n̲g̲.̲b̲a̲r̲
  • S̵t̵r̵i̵n̵g̵.̵t̵e̵s̵t̵2̵S̲t̲r̲i̲n̲g̲.̲b̲a̲z̲
  • S̵t̵r̵i̵n̵g̵.̵t̵e̵s̵t̵2̵S̲t̲r̲i̲n̲g̲.̲f̲o̲o̲
  • S̵t̵r̵i̵n̵g̵.̵t̵e̵s̵t̵2̵o̲t̲h̲e̲r̲B̲a̲z̲
  • S̵t̵r̵i̵n̵g̵.̵t̵e̵s̵t̵2̵o̲t̲h̲e̲r̲F̲o̲o̲
-/
#guard_msgs in
#check String.test2


namespace Foo
inductive Bar where | one | two | three

attribute [suggest_for Foo.Bar.first] Bar.one
end Foo

namespace Foo.Bar
attribute [suggest_for Foo.Bar.second, Foo.more] Bar.two

@[suggest_for Foo.Bar.toStr]
def toString : Foo.Bar → String
 | .one => "one"
 | .two => "two"
 | .three => "three"
end Foo.Bar

attribute [suggest_for Foo.Bar.third, Foo.more] Foo.Bar.three

@[suggest_for Foo.Bar.toNum]
def Foo.Bar.toNat : Foo.Bar → Nat
  | .one => 1
  | .two => 2
  | .three => 3

/--
error: Invalid field `toNum`: The environment does not contain `Foo.Bar.toNum`, so it is not possible to project the field `toNum` from an expression
  Foo.Bar.three
of type `Foo.Bar`

Hint: Perhaps you meant one of these in place of `Foo.Bar.toNum`:
  [apply] `Foo.Bar.toNat`: Foo.Bar.three.toNat
-/
#guard_msgs in
#eval Foo.Bar.three.toNum

/--
error: Invalid field `toStr`: The environment does not contain `Foo.Bar.toStr`, so it is not possible to project the field `toStr` from an expression
  Foo.Bar.two
of type `Foo.Bar`

Hint: Perhaps you meant one of these in place of `Foo.Bar.toStr`:
  [apply] `Foo.Bar.toString`: Foo.Bar.two.toString
-/
#guard_msgs in
#eval Foo.Bar.two.toStr

/- ----- -/

/--
error: Unknown constant `Foo.Bar.first`

Hint: Perhaps you meant `Foo.Bar.one` in place of `Foo.Bar.first`:
  F̵o̵o̵.̵B̵a̵r̵.̵f̵i̵r̵s̵t̵F̲o̲o̲.̲B̲a̲r̲.̲o̲n̲e̲
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
  F̵o̵o̵.̵B̵a̵r̵.̵f̵i̵r̵s̵t̵F̲o̲o̲.̲B̲a̲r̲.̲o̲n̲e̲
-/
#guard_msgs in
#check Foo.Bar.first

/--
error: Unknown constant `Foo.Bar.second`

Hint: Perhaps you meant `Bar.two` in place of `Bar.second`:
  B̵a̵r̵.̵s̵e̵c̵o̵n̵d̵B̲a̲r̲.̲t̲w̲o̲
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
  F̵o̵o̵.̵B̵a̵r̵.̵f̵i̵r̵s̵t̵F̲o̲o̲.̲B̲a̲r̲.̲o̲n̲e̲
-/
#guard_msgs in
#check Foo.Bar.first

/--
error: Unknown constant `Foo.Bar.second`

Hint: Perhaps you meant `two` in place of `Bar.second`:
  B̵a̵r̵.̵s̵e̵c̵o̵n̵d̵B̲a̲r̲.̲t̲w̲o̲
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
    B̵a̵r̵.̵f̵i̵r̵s̵t̵F̲o̲o̲2̲.̲B̲a̲r̲.̲o̲n̲e̲
  ⏎
  Unknown constant `Foo.Bar.first`
  ⏎
  Hint: Perhaps you meant `Foo.Bar.one` in place of `Bar.first`:
    B̵a̵r̵.̵f̵i̵r̵s̵t̵F̲o̲o̲.̲B̲a̲r̲.̲o̲n̲e̲
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
  B̵a̵r̵.̵f̵i̵r̵s̵t̵B̲a̲r̲.̲o̲n̲e̲
-/
#guard_msgs in
#eval Bar.first
end Foo
