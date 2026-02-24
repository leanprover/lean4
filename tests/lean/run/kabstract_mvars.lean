/-!
# Test for metavariable assignments in kabstract

Tests that `kabstract` prefers to assign metavariables in the pattern rather than the value.
This is made sure by putting the pattern first in `isDefEq` calls.
-/

/-!
Test for `rw` (the main user of `kabstract`).
-/

/--
trace: case h
⊢ 1 ≤ Nat.succ ?n
---
trace: case h
⊢ 1 ≤ ?n + 1
-/
#guard_msgs in
example : True := by
  -- introduce a metavariable `?n : Nat`
  apply fun (n : Nat) (h : 1 ≤ n.succ) => trivial
  · trace_state -- the state before uses `Nat.succ ?n`
    rewrite [Nat.succ_eq_add_one]
    trace_state -- and the state after uses `?n + 1`, not a new metavariable
    apply Nat.le_add_left 1
  · exact 2 -- and the goal for `?n` is still left open

/-!
Test for `generalize` (the other important user of `kabstract`).
-/

example : True := by
  -- introduce a metavariable `?n : Nat`
  apply fun (n : Nat) (h : 0 ≤ n.succ) => trivial
  · generalize Nat.succ _ = a -- `generalize` simply sets `_ := ?n`
    exact Nat.zero_le a
  · exact 2 -- and the goal for `?n` is still left open
