/-!
# Improve zeta-delta tracking for `simp?`

https://github.com/leanprover/lean4/issues/6655 reports issues with `simp?` where
it would over-report local variables. This comes down to two kinds of issues:
- zeta-delta tracking wasn't being reset, so previous `simp?`s would contribute variables
- `simp?` would report variables that weren't explicitly mentioned,
  because `whnf` would be run with different configurations during the tracking.
  (e.g. `withInferTypeConfig` enables `zetaDelta`.)

This file tests that it resets the tracking and filters the list.
-/

set_option linter.unusedSimpArgs false

/-!
Example from #6655. This used to suggest `simp only [e, d]`.
-/
/--
info: Try this: simp only [e]
---
trace: α : Type
c : α → α
x : α
d : α → α := c
e : α → α := d
⊢ d x = x
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example {α : Type} (c : α → α) (x : α) : c x = x := by
  let d := c
  let e := d
  change e x = x
  simp? [e]
  trace_state
  sorry

/-!
Example from #6655. This used to suggest `simp only [d]`.
-/
/--
info: Try this: simp only
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example {α : Type} (c : α → α) (x : α) : c x = x := by
  let d := c
  change d x = x
  simp [d]
  have : x = x := by
    simp?
  sorry

/-!
Example from comments of #6655. This used to suggest `simp only [Int.add_sub_cancel, p]`.
(N.B. the goal at that point does not have `p` in it!)
-/
/-- info: Try this: simp only [Int.add_sub_cancel] -/
#guard_msgs in
example (a b : Int) : a + b - b = a := by
  let p := 1
  have h : p = 1 := by
    simp only [p]
  simp?

/-!
Example from https://github.com/leanprover/lean4/pull/7539 by JovanGerb.
This used to suggest `simp only [a, b] ` and `simp only [a, b]`
-/
/--
info: Try this: simp only [a]
---
info: Try this: simp only
-/
#guard_msgs in
example : True := by
  let a := 1
  let b := 2
  have : b = 2 := by simp [a,b]
  have : a = 1 := by simp? [a]
  have : 1 = 1 := by simp?
  trivial

/-!
Test that there is still a deficiency. This should say `simp only [e]`.
-/
/--
info: Try this: simp only [e, c]
---
trace: α : Type
b : α → α
x : α
c : α → α := b
d : α → α := c
e : α → α := d
⊢ d x = x
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example {α : Type} (b : α → α) (x : α) : b x = x := by
  let c := b
  let d := c
  let e := d
  change e x = x
  simp? [e, c]
  trace_state
  sorry
