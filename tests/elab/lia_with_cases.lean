-- Test that lia now uses grind tactic script with cases_next

-- Basic linear arithmetic - should still work without case-splits
example (x y : Int) : 2 * x + 4 * y ≠ 5 := by
  lia

example (x y : Int) : 2 * x + 3 * y = 0 → 1 ≤ x → y < 1 := by
  lia

example (a b : Int) : 2 ∣ a + 1 → 2 ∣ b + a → ¬ 2 ∣ b + 2 * a := by
  lia

-- Tests that require case-splitting
-- These require the `cases_next` to split on hypotheses before lia can solve

-- Case-split on hypothesis, then solve with lia
example (x : Nat) (h : x = 0 ∨ x = 1) : x ≤ 1 := by
  lia

-- Multiple nested case-splits
example (x y : Nat) (h1 : x = 0 ∨ x = 1) (h2 : y = 0 ∨ y = 1) : x + y ≤ 2 := by
  lia

-- Case-split on if-then-else
example (x : Int) : (if x > 0 then x else -x) ≥ 0 := by
  lia

-- Case-split with arithmetic in branches
example (x : Int) : (if x > 0 then 2*x else 0) ≥ 0 := by
  lia
