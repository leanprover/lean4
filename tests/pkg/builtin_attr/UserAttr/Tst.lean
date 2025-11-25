import UserAttr.BlaAttr

@[bar] def f (x : Nat) := x + 2
@[bar] def g (x : Nat) := x + 1

attribute [local irreducible] myFun

set_option pp.mvars false
/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  myFun x = x + 1
-/
#guard_msgs in
example : myFun x = x + 1 :=
  rfl
