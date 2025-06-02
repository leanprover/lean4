/-!
# Tests of `pp.showLetValues`
-/

-- Ensure default values
set_option pp.showLetValues false
set_option pp.showLetValues.threshold 0
set_option pp.showLetValues.tactic.threshold 255

/-!
Non-tactic context. No let value (see ⋯)
-/
example (x : Nat) : Nat :=
  let y := x + x
  y
--^ $/lean/plainTermGoal

/-!
Non-tactic context. Enable showing values (see x + x)
-/
set_option pp.showLetValues true in
example (x : Nat) : Nat :=
  let y := x + x
  y
--^ $/lean/plainTermGoal

/-!
Non-tactic context. Turn up threshold (see x + x)
-/
set_option pp.showLetValues.threshold 10 in
example (x : Nat) : Nat :=
  let y := x + x
  y
--^ $/lean/plainTermGoal

/-!
Tactic context. See x + x
-/
example (x : Nat) : Nat := by
  let y := x + x
  exact y
--^ $/lean/plainGoal

/-!
Tactic context. Turn down threshold (see ⋯)
-/
set_option pp.showLetValues.tactic.threshold 0 in
example (x : Nat) : Nat := by
  let y := x + x
  exact y
--^ $/lean/plainGoal

/-!
Tactic context. Uses max of both thresholds (see x + x)
-/
set_option pp.showLetValues.threshold 10 in
set_option pp.showLetValues.tactic.threshold 0 in
example (x : Nat) : Nat := by
  let y := x + x
  exact y
--^ $/lean/plainGoal

/-!
Non-tactic context. Atomic always shown (see x)
-/
set_option pp.showLetValues.threshold 0 in
set_option pp.showLetValues.tactic.threshold 0 in
example (x : Nat) : Nat :=
  let y := x
  y
--^ $/lean/plainTermGoal

/-!
Tactic context. Atomic always shown (see x)
-/
set_option pp.showLetValues.threshold 0 in
set_option pp.showLetValues.tactic.threshold 0 in
example (x : Nat) : Nat := by
  let y := x
  exact y
--^ $/lean/plainGoal
