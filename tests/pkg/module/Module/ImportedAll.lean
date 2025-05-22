module

prelude
import all Module.Basic

/-! `import all` should import private information, privately. -/

/--
info: theorem t : f = 1 :=
testSorry
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

/--
error: unknown identifier 'trflprivate'
---
error: dsimp made no progress
-/
#guard_msgs in
example : P f := by dsimp only [trflprivate]; exact hP1
/--
error: unknown identifier 'trflprivate''
---
error: dsimp made no progress
-/
#guard_msgs in
example : P f := by dsimp only [trflprivate']; exact hP1


example : P fexp := by dsimp only [fexp_trfl]; exact hP1
example : P fexp := by dsimp only [fexp_trfl']; exact hP1
