import Lean

namespace Foo
inductive Bar where | one | two | three
end Foo

namespace Foo.Bar

/--
error: invalid declaration name `_root_`, `_root_` is a prefix used to refer to the 'root' namespace
-/
#guard_msgs in
@[suggest_for x, y.z, _root_.q.x, _root_, ff]
public def _root_.String.blah (x: String) := x.length + 1

@[suggest_for gloom, fidget, whiz]
public def baz : Bar → Nat
  | .one => 1
  | .two => 2
  | .three => 3

@[suggest_for gloom, bang, kaboom,]
public def beep : Bar → Nat
  | .one => 10
  | .two => 20
  | .three => 30

@[suggest_for _root_.String.test1, test2]
public def _root_.String.test3 (x : String) := x ++ "3"

end Foo.Bar

@[suggest_for x, y, test2,]
public def blah (x: String) := x.length + 1

/-- info: #[`Foo.Bar.baz, `Foo.Bar.beep] -/
#guard_msgs in
#eval Lean.getSuggestions `Foo.Bar.gloom

/-- info: #[`Foo.Bar.beep] -/
#guard_msgs in
#eval Lean.getSuggestions `Foo.Bar.kaboom

#eval Foo.Bar.three.whiz

#eval [1,2,7].flibbet

#eval ``_root_.String.blah

#check HAdd.hAdd.curry
