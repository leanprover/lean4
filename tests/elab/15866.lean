import Lean

/-!
Regression test for #15866: with `Elab.async false`, `addDecl` did not advance the aux declaration
name generator, so aux lemma names were reused after backtracking and stale cache entries referring
to the discarded declarations led to kernel errors.
-/

set_option Elab.async false

#guard_msgs (drop info, drop warning) in
example (x y : BitVec 4) (h1 : x ≠ 7#4 ∨ y = 7#4) (h2 : 0#2 ++ BitVec.twoPow 2 0 ≠ x) : False := by
  grind?

open Lean Meta in
/-- info: false -/
#guard_msgs in
run_meta do
  let s ← saveState
  let n₁ ← mkAuxLemma [] (mkConst ``True) (mkConst ``True.intro)
  s.restore
  let n₂ ← mkAuxLemma [] (mkConst ``True) (mkConst ``True.intro)
  logInfo m!"{n₁ == n₂}"
