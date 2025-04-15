import UserAttr.BlaAttr

@[bar] def f (x : Nat) := x + 2
@[bar] def g (x : Nat) := x + 1

attribute [local irreducible] myFun

set_option pp.mvars false
/--
error: type mismatch
  rfl
has type
  ?_ = ?_ : Prop
but is expected to have type
  myFun x = x + 1 : Prop
-/
#guard_msgs in
example : myFun x = x + 1 :=
  rfl
