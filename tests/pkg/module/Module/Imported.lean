module

prelude
import Module.Basic

/-! Theorems should be exported without their bodies -/

/--
info: theorem t : f = 1 :=
<not imported>
-/
#guard_msgs in
#print t

/-- error: dsimp made no progress -/
#guard_msgs in
example : f = 1 := by dsimp only [t]

example : t = t := by dsimp only [trfl]
