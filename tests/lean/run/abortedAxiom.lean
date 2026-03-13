/-! An elaboration abort should not lead to an empty `#print axioms`. -/

universe u

/--
error: AddConstAsyncResult.commitConst: constant has level params [u] but expected []
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
theorem f : True := by
  have := Type u
  sorry

/-- error: unknown constant 'f' -/
#guard_msgs in
#print axioms f
