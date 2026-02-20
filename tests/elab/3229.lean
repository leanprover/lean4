-- This example exposed a caching issue with the `discharge?` method used by the `split` tactic.
example (b : Bool) :
    (if b then 1 else if b then 1 else 0) = (if b then 1 else 0) := by
  split <;> rfl
