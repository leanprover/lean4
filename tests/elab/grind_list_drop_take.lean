module
example : (List.range' 1 n).drop (List.range' 1 n).length = [] := by grind -- solves
example : [].sum = 0 := by grind -- solves
example : ((List.range' 1 n).drop (List.range' 1 n).length).sum = 0 := by grind -- solves
example : ((List.range' 1 n).take (List.range' 1 n).length).sum = (List.range' 1 n).sum := by grind -- solves
example (as bs : List Nat) : ((as ++ bs).take (as ++ bs).length).sum = (as ++ bs).sum := by grind -- solves
example (as bs : List Nat) : ((as ++ bs).take (as ++ bs).length).sum = bs.sum + as.sum := by grind -- solves
