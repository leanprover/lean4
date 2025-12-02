import Lean

@[suggest_for test0, test1, test2]
public def String.foo (x: String) := x.length + 1

@[suggest_for String.test1, test2]
public def String.bar (x: String) := x.length + 1

@[suggest_for _root_.String.test1, test2]
public def String.baz (x: String) := x.length + 1

/--
error: Invalid field `test0`: The environment does not contain `String.test0`, so it is not possible to project the field `test0` from an expression
  "abc"
of type `String`

Hint: One of these replacements for `String.test0` may be appropriate:
  [apply] `String.foo`: "abc".foo
-/
#guard_msgs in
#check "abc".test0

/--
error: Invalid field `test1`: The environment does not contain `String.test1`, so it is not possible to project the field `test1` from an expression
  "abc"
of type `String`

Hint: One of these replacements for `String.test1` may be appropriate:
  [apply] `String.baz`: "abc".baz
  [apply] `String.foo`: "abc".foo
-/
#guard_msgs in
#check "abc".test1

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

Hint: One of these replacements for `Foo.Bar.toNum` may be appropriate:
  [apply] `Foo.Bar.toNat`: Foo.Bar.three.toNat
-/
#guard_msgs in
#eval Foo.Bar.three.toNum

/--
error: Invalid field `toStr`: The environment does not contain `Foo.Bar.toStr`, so it is not possible to project the field `toStr` from an expression
  Foo.Bar.two
of type `Foo.Bar`

Hint: One of these replacements for `Foo.Bar.toStr` may be appropriate:
  [apply] `Foo.Bar.toString`: Foo.Bar.two.toString
-/
#guard_msgs in
#eval Foo.Bar.two.toStr

/-
#check Foo.Bar.first
#check Bar.second
#check third

namespace Foo
#check Foo.Bar.first
#check Bar.second
#check third
end Foo

namespace Foo.Bar
#check Foo.Bar.first
#check Bar.second
#check third
end Foo
-/
