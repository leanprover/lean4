Import Int
Import tactic
Definition a : Nat := 10
-- Trivial indicates a "proof by evaluation"
Theorem T1 : a > 0 := Trivial
Theorem T2 : a - 5 > 3 := Trivial
-- The next one is commented because it fails
-- Theorem T3 : a > 11 := Trivial
