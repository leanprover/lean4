example (xs : List Nat) (x : Nat)
    (i : Nat) (hi : i < (xs ++ [x]).length)
    (h : 1 ≤ (List.drop i xs).sum + x) :
    1 ≤ (List.drop i (List.take (xs ++ [x]).length (xs ++ [x]))).sum := by
  grind
