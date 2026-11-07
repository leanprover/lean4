/-!
Tests that `grind?` only suggests tactics that close the goal. Generated tactics that fail are
reported in a warning, and if none of them works, `grind?` suggests `grind`. The failures are
simulated using the debugging options `grind.debug.badAnchors`, `grind.debug.dropParams`, and
`grind.debug.dropSteps`.
-/

-- Suggestions that work are unchanged.
/--
info: Try these:
  [apply] grind only [= Nat.min_def, #35e2, #10ba]
  [apply] grind only [= Nat.min_def]
  [apply] grind =>
    instantiate only [= Nat.min_def]
    cases #35e2 <;> cases #10ba
-/
#guard_msgs in
example (a b c : Nat) (h : a ≤ b) : min a c ≤ min b c := by grind?

-- Only the suggestions without anchors work.
/--
warning: generated tactics cannot close the goal
  grind only [= Nat.min_def, #0000, #0000]
  grind =>
    instantiate only [= Nat.min_def]
    cases #0000 <;> cases #0000
---
info: Try this:
  [apply] grind only [= Nat.min_def]
-/
#guard_msgs in
set_option grind.debug.badAnchors true in
example (a b c : Nat) (h : a ≤ b) : min a c ≤ min b c := by grind?

-- Only the `grind only` suggestions work.
/--
warning: generated tactic cannot close the goal
  grind => instantiate only [= Nat.min_def]
---
info: Try these:
  [apply] grind only [= Nat.min_def, #35e2, #10ba]
  [apply] grind only [= Nat.min_def]
-/
#guard_msgs in
set_option grind.debug.dropSteps true in
example (a b c : Nat) (h : a ≤ b) : min a c ≤ min b c := by grind?

-- No suggestion works, and `grind?` suggests `grind` with the original parameters.
def mn (a b : Nat) := min a b

theorem mn_eq (a b : Nat) : mn a b = min a b := rfl

/--
warning: generated tactics cannot close the goal
  grind only [#0000, #0000]
  grind only
  grind =>
    instantiate only [mn_eq]
    instantiate only [= Nat.min_def]
    cases #0000 <;> cases #0000
---
info: Try this:
  [apply] grind [mn_eq]
-/
#guard_msgs in
set_option grind.debug.badAnchors true in
set_option grind.debug.dropParams true in
example (a b c : Nat) (h : a ≤ b) : mn a c ≤ mn b c := by grind? [mn_eq]

example (a b c : Nat) (h : a ≤ b) : mn a c ≤ mn b c := by grind [mn_eq]

-- Partial scripts with `sorry` mark where the search got stuck, and are still suggested.
/--
info: Try this:
  [apply] grind => sorry
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (p : Nat → Prop) : p 0 := by grind?

-- Only the search of `grind?` is traced, not the runs checking its suggestions.
/--
info: Try this:
  [apply] grind only
---
trace: [grind.assert] a = b
[grind.assert] ¬b = a
-/
#guard_msgs in
set_option trace.grind.assert true in
example (a b : Nat) (h : a = b) : b = a := by grind?
