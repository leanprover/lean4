open list

vm_eval filter (< 10) [20, 5, 10, 3, 2, 14, 1]
vm_eval qsort (<) [20, 5, 10, 3, 2, 14, 1]
vm_eval foldl (+) 0 [1, 2, 3]

example : foldl (+) 0 [3, 4, 1] = 8 :=
rfl

example : foldl (*) 2 [3, 4, 1] = 24 :=
rfl
