open nat

#eval [1, 2, 3]

#eval to_bool $ 1 ∈ [1, 2, 3]

#eval to_bool $ 4 ∈ [1, 2, 3]

#eval [1, 2, 3] ++ [3, 4]

#eval 2 :: [3, 4]

#eval ([] : list nat)

#eval (∅ : list nat)

#eval ({1, 3, 2, 2, 3, 1} : list nat)

#eval [1, 2, 3] ∪ [3, 4, 1, 5]

#eval [1, 2, 3] ∩ [3, 4, 1, 5]

#eval (mul 10) <$> [1, 2, 3]

#check ({1, 2, 3} : list nat)

#check ({1, 2, 3, 4} : set nat)
