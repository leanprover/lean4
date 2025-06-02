module

prelude
import all Module.Basic

/-! `import all` should import private information, privately. -/

/--
info: theorem t : f = 1 :=
sorry
-/
#guard_msgs in
#print t

/--
error: type mismatch
  y
has type
  Vector Unit 1 : Type
but is expected to have type
  Vector Unit f : Type
-/
#guard_msgs in
theorem v (x : Vector Unit f) (y : Vector Unit 1) : x = y := sorry
