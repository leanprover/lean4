/-!
Regression test for #15622: `lia` creates new variables during its case-split search (here via
nonlinear `%` propagation). Backtracking dropped these variables but kept their values in the
assignment, so the next search indexed past the end of the variable arrays and looped forever.
-/

#guard_msgs (drop warning) in
example (y : BitVec 1) (h : y % y < -(y * y)) : y + 1 = ~~~y + 1 := by
  fail_if_success grind
  sorry
