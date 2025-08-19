-- This fails unless we manually substitute `hb`.
-- `grind` doesn't recognise this as a linear arithmetic problem.

-- Remark: we will handle this kind of example when we add support for
-- nonlinear monomials to cutsat

example (a : Nat) (ha : a < 8) (b : Nat) (hb : b = 2) : a * b < 8 * b := by
  grind -- fails
