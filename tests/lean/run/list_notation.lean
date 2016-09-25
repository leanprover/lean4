open nat

vm_eval [1, 2, 3]

vm_eval to_bool $ 1 ∈ [1, 2, 3]

vm_eval to_bool $ 4 ∈ [1, 2, 3]

vm_eval [1, 2, 3] ++ [3, 4]

vm_eval 2 :: [3, 4]

vm_eval ([] : list nat)

vm_eval (∅ : list nat)

vm_eval ({1, 3, 2, 2, 3, 1} : list nat)

vm_eval [1, 2, 3] ∪ [3, 4, 1, 5]

vm_eval [1, 2, 3] ∩ [3, 4, 1, 5]

vm_eval (mul 10) <$> [1, 2, 3]

check ({1, 2, 3} : list nat)

check ({1, 2, 3, 4} : set nat)
