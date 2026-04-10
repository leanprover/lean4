module

public import Lean

set_option linter.unusedVariables false

-- Basic test: simp applies the theorem and spawns a goal for the undischarged hypothesis
@[expect_true h, simp]
theorem foo_bound (n : Nat) (h : n < 10) : n + 0 = n := by omega

example (n : Nat) (h : n < 5) : n + 0 = n := by
  simp only [foo_bound]
  -- The undischarged expect_true goal `n < 10` should remain
  omega

-- Test: expect_true hypothesis can be filled with exact
example (n : Nat) (h : n < 10) : n + 0 = n := by
  simp only [foo_bound]
  exact h

-- Test: attribute validation - hypothesis name must exist in binders
/--
error: expect_true: hypothesis 'nonexistent' not found in the binders of '_private.elab.simp_expect_true.0.bad_attr_test'
-/
#guard_msgs in
@[expect_true nonexistent]
theorem bad_attr_test (n : Nat) : n = n := rfl

-- Test: multiple expect_true hypotheses
@[expect_true h₁ h₂, simp]
theorem multi_hyp (n m : Nat) (h₁ : n < 100) (h₂ : m < 100) : n + m + 0 = n + m := by omega

example (n m : Nat) (hn : n < 50) (hm : m < 50) : n + m + 0 = n + m := by
  simp only [multi_hyp]
  -- Two goals: n < 100 and m < 100
  · omega
  · omega
