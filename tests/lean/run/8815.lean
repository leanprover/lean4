/-!
Assortion of tests to make sure the #8815 simp arg elaboration refactoring did not change
behavior.
-/

set_option linter.unusedVariables false

example (P Q : Prop) (hQ : Q) (hP : P) : P := by simp [*, -hQ]

/-- error: simp made no progress -/
#guard_msgs in example (P Q : Prop) (hQ : Q) (hP : P) : P := by simp [*, -hP]

/-- error: unknown constant 'hQ' -/
#guard_msgs in example (P Q : Prop) (hQ : Q) (hP : P) : P := by simp [-hQ, *]

#guard_msgs in example (P Q : Prop) (hQ : Q) (hP : P) : P := by simp_all [-hQ]

/--
error: unknown constant 'hQ'
---
error: simp made no progress
-/
#guard_msgs in example (P Q : Prop) (hQ : Q) (hP : P) : P := by simp [-hQ]


theorem a_thm : True := trivial

def f : Nat → Nat
| 0 => 1
| n + 1 => f n + 1

example : f 0 > 0 := by simp [f]
example : f 0 > 0 := by simp!


-- NB: simp! disables all warnings, not just for declarations to unfold
-- Mild bug, but not a regresion.

/--
error: unsolved goals
⊢ 0 < f 0
-/
#guard_msgs in example : f 0 > 0 := by simp! [-f, -a_thm]

/--
warning: 'f' does not have [simp] attribute
---
warning: 'a_thm' does not have [simp] attribute
---
error: unsolved goals
⊢ 0 < f 0
-/
#guard_msgs in example : f 0 > 0 := by
  simp [-f, -a_thm]


/--
error: invalid 'simp', proposition expected
  Type 32
-/
#guard_msgs in
example : True := by simp [Sort 32] -- mostly about error location, once guard_msgs shows that
