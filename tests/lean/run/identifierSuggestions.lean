import Lean

@[suggest_for test0, test1, test2]
public def String.foo (x: String) := x.length + 1

@[suggest_for String.test1, test2]
public def String.bar (x: String) := x.length + 1

@[suggest_for _root_.String.test1, test2]
public def String.baz (x: String) := x.length + 1

@[suggest_for _root_.String.test2]
public def otherFoo (x: String) := x.length + 1

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
  [apply] `String.foo`
-/
#guard_msgs in
#check String.test0

-- Two suggested replacements: the bar replacement is for String.String.test1, which does not apply
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
  [apply] `String.baz`
  [apply] `String.foo`
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

-- Five suggested replacements: does not filter out non-`String` functions
/--
error: Unknown constant `String.test2`

Hint: Perhaps you meant one of these in place of `String.test2`:
  [apply] `String.bar`
  [apply] `String.baz`
  [apply] `String.foo`
  [apply] `Nat.otherBar`
  [apply] `otherFoo`
-/
#guard_msgs in
#check String.test2

namespace Foo
inductive Bar where | one | two | three

attribute [suggest_for first] Bar.one
end Foo

namespace Foo.Bar
attribute [suggest_for second, more] Bar.two

@[suggest_for toStr]
def toString : Foo.Bar → String
 | .one => "one"
 | .two => "two"
 | .three => "three"
end Foo.Bar

attribute [suggest_for third, more] Foo.Bar.three

@[suggest_for toNum]
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

namespace Foo
/--
error: Unknown constant `Foo.Bar.first`

Hint: Perhaps you meant `Foo.Bar.one` in place of `Foo.Bar.first`:
  [apply] `Foo.Bar.one`
-/
#guard_msgs in
#check Foo.Bar.first

/--
error: Unknown constant `Foo.Bar.second`

Hint: Perhaps you meant `Foo.Bar.two` in place of `Foo.Bar.second`:
  [apply] `Bar.two`
-/
#guard_msgs in
#check Bar.second

/-- error: Unknown identifier `third` -/
#guard_msgs in
#check third
end Foo

namespace Foo.Bar
/--
error: Unknown constant `Foo.Bar.first`

Hint: Perhaps you meant `Foo.Bar.one` in place of `Foo.Bar.first`:
  [apply] `Foo.Bar.one`
-/
#guard_msgs in
#check Foo.Bar.first

/--
error: Unknown constant `Foo.Bar.second`

Hint: Perhaps you meant `Foo.Bar.two` in place of `Foo.Bar.second`:
  [apply] `Bar.two`
-/
#guard_msgs in
#check Bar.second

-- TODO: give a suggestion here!
/-- error: Unknown identifier `third` -/
#guard_msgs in
#check third
end Foo.Bar
