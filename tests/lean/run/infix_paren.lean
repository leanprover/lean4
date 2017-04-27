open list

#eval filter (< 10) [20, 5, 10, 3, 2, 14, 1]
#eval qsort (λ x y, x < y) [20, 5, 10, 3, 2, 14, 1]
#eval foldl (+) 0 [1, 2, 3]

example : foldl (+) 0 [3, 4, 1] = 8 :=
rfl

example : foldl (*) 2 [3, 4, 1] = 24 :=
rfl

#check (+) 1 2

example : (+) 1 2 = 3 :=
rfl

example : (*) 3 4 = 12 :=
rfl

example : (++) [1,2] [3,4] = [1,2,3,4] :=
rfl

example : (++) [1,2] [3,4] = [1,2] ++ [3,4] :=
rfl

/-
(-) is rejected since we have prefix notation for -
-/

example : list.foldr (::) [] [1, 2, 3, 4] = [1, 2, 3, 4] :=
rfl
