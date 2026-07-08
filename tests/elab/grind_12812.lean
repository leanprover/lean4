-- Tests for https://github.com/leanprover/lean4/issues/12812
-- `grind` and `simp +arith` should not loop on already-normalized Int equalities

-- The original report: deep recursion on negative integer literal
example (xs : List Int) (h : xs[0]? = some (-1)) : xs[0]? = some (-1) := by grind

-- Variant with simp +arith
example (xs : List Int) (h : xs[0]? = some (-1)) : xs[0]? = some (-1) := by simp +arith [h]

-- norm_eq_var branch: x = y already normalized
example (a b : Int) (h : a = b) : a = b := by grind

-- norm_eq_var_const branch: x = -k already normalized
example (a : Int) (h : a = -1) : a = -1 := by grind
example (a : Int) (h : a = -42) : a = -42 := by grind
