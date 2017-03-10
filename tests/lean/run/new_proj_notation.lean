variable x : list nat

#check x^.map (+1)

#check x^.foldl (+) 0

#eval [1, 2, 3]^.map (+3)
