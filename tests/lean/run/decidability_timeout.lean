
-- Prior to leanprover/lean4#2552 there was a performance trap
-- depending on the implementation details in `decidableBallLT`.
-- We keep this example (which would have gone over maxHeartbeats)
-- as a regression test for the instance.
example : ∀ m, m < 25 → ∀ n, n < 25 → ∀ c, c < 25 → m ^ 2 + n ^ 2 + c ^ 2 ≠ 7 := by decide
