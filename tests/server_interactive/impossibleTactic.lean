/-!
Tests that `impossible by ...` provides the same hover / goal info as a regular
`by` block, via the term elaborator.
-/

example (n : Nat) : n = n + 1 := by
  impossible by
            --^ $/lean/plainGoal
    intro h
   --^ textDocument/hover
    exact Nat.succ_ne_zero _ ((h 0).symm)
   --^ textDocument/hover
