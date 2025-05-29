module

prelude
import Module.Basic

/-! Definitions should be exported without their bodies by default -/

/--
info: def f : Nat :=
<not imported>
-/
#guard_msgs in
#print f

/-! Theorems should be exported without their bodies -/

/--
info: theorem t : f = 1 :=
<not imported>
-/
#guard_msgs in
#print t

/--
info: theorem trfl : f = 1 :=
<not imported>
-/
#guard_msgs in
#print trfl

/-- error: dsimp made no progress -/
#guard_msgs in
example : P f := by dsimp only [t]; exact hP1
example : P f := by simp only [t]; exact hP1

/-- error: dsimp made no progress -/
#guard_msgs in
example : P f := by dsimp only [trfl]; exact hP1
/-- error: dsimp made no progress -/
#guard_msgs in
example : P f := by dsimp only [trfl']; exact hP1

example : P fexp := by dsimp only [fexp_trfl]; exact hP1
example : P fexp := by dsimp only [fexp_trfl']; exact hP1
