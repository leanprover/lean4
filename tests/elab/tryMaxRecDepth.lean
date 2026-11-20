/-!
`try?` treats a candidate tactic that exceeds the maximum recursion depth as having failed, and
moves on to the next candidate instead of aborting.
-/

section UInt16

variable (lo hi : UInt16) (h : lo ≤ hi)
include h

/--
info: Try this:
  [apply] impossible by decide
---
warning: declaration uses `sorry`
-/
#guard_msgs in
/-- The naive mid-point calculation cannot be proven, and Lean tells you that it is impossible -/
theorem mid_exact_bad :
    lo ≤ (lo + hi) / 2 ∧ (lo + hi) / 2 ≤ hi := by
  try?

/-- The correct calculation is easily proven using automation -/
theorem mid_exact_good :
    lo ≤ lo + (hi - lo) / 2 ∧ lo + (hi - lo) / 2 ≤ hi := by grind

end UInt16

section UInt64

variable (lo hi : UInt64) (h : lo ≤ hi)
include h

/-
Here `impossible by decide` exceeds the maximum recursion depth evaluating
`UInt64.instDecidableForall`; `try?` used to abort with that error.
-/
/--
error: Tactic `try?` failed: consider using `grind` manually, or `try? +missing` for partial proofs containing `sorry`

lo hi : UInt64
h : lo ≤ hi
⊢ lo ≤ (lo + hi) / 2 ∧ (lo + hi) / 2 ≤ hi
-/
#guard_msgs in
theorem mid_exact_bad64 :
    lo ≤ (lo + hi) / 2 ∧ (lo + hi) / 2 ≤ hi := by
  try?

theorem mid_exact_good64 :
    lo ≤ lo + (hi - lo) / 2 ∧ lo + (hi - lo) / 2 ≤ hi := by grind

end UInt64
