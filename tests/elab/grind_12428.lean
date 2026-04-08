import Std.Do

-- `grind` should not panic on this example (issue #12428).
-- The bug was that `sreifyCore?` could encounter power subterms
-- not yet internalized in the E-graph during nested propagation.
example
  (n x' y : Nat)
  (pref : List Nat)
  (cur : Nat)
  (suff : List Nat)
  (h : List.range' 0 n 1 = pref ++ cur :: suff) :
  y ^ x' * n ^ x' = x' ^ n := by
  fail_if_success grind
  sorry
