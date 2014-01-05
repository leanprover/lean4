import Int
import tactic
definition a : Nat := 10
-- Trivial indicates a "proof by evaluation"
theorem T1 : a > 0 := Trivial
theorem T2 : a - 5 > 3 := Trivial
-- The next one is commented because it fails
-- theorem T3 : a > 11 := Trivial
