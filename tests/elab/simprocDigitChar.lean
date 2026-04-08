variable {n : Nat}

-- Simp lemmas for digitChar: each valid output character
example : n.digitChar = '0' ↔ n = 0 := by simp
example : n.digitChar = '1' ↔ n = 1 := by simp
example : n.digitChar = '2' ↔ n = 2 := by simp
example : n.digitChar = '3' ↔ n = 3 := by simp
example : n.digitChar = '4' ↔ n = 4 := by simp
example : n.digitChar = '5' ↔ n = 5 := by simp
example : n.digitChar = '6' ↔ n = 6 := by simp
example : n.digitChar = '7' ↔ n = 7 := by simp
example : n.digitChar = '8' ↔ n = 8 := by simp
example : n.digitChar = '9' ↔ n = 9 := by simp
example : n.digitChar = 'a' ↔ n = 10 := by simp
example : n.digitChar = 'b' ↔ n = 11 := by simp
example : n.digitChar = 'c' ↔ n = 12 := by simp
example : n.digitChar = 'd' ↔ n = 13 := by simp
example : n.digitChar = 'e' ↔ n = 14 := by simp
example : n.digitChar = 'f' ↔ n = 15 := by simp
example : n.digitChar = '*' ↔ 16 ≤ n := by simp

-- Reversed simp lemmas for digitChar
example : '0' = n.digitChar ↔ n = 0 := by simp
example : '1' = n.digitChar ↔ n = 1 := by simp
example : '2' = n.digitChar ↔ n = 2 := by simp
example : '3' = n.digitChar ↔ n = 3 := by simp
example : '4' = n.digitChar ↔ n = 4 := by simp
example : '5' = n.digitChar ↔ n = 5 := by simp
example : '6' = n.digitChar ↔ n = 6 := by simp
example : '7' = n.digitChar ↔ n = 7 := by simp
example : '8' = n.digitChar ↔ n = 8 := by simp
example : '9' = n.digitChar ↔ n = 9 := by simp
example : 'a' = n.digitChar ↔ n = 10 := by simp
example : 'b' = n.digitChar ↔ n = 11 := by simp
example : 'c' = n.digitChar ↔ n = 12 := by simp
example : 'd' = n.digitChar ↔ n = 13 := by simp
example : 'e' = n.digitChar ↔ n = 14 := by simp
example : 'f' = n.digitChar ↔ n = 15 := by simp
example : '*' = n.digitChar ↔ 16 ≤ n := by simp

-- Simproc: characters not in the range of digitChar simplify to False
example : (n.digitChar = '!') = False := by simp
example : (n.digitChar = 'z') = False := by simp
example : (n.digitChar = 'A') = False := by simp
example : (n.digitChar = ' ') = False := by simp
example : (n.digitChar = 'g') = False := by simp

-- Reversed direction: c = n.digitChar
example : ('!' = n.digitChar) = False := by simp
example : ('z' = n.digitChar) = False := by simp
example : ('A' = n.digitChar) = False := by simp
example : (' ' = n.digitChar) = False := by simp
example : ('g' = n.digitChar) = False := by simp

-- Using the lemmas in proofs
example (h : n = 0) : n.digitChar = '0' := by simp [h]
example (h : n.digitChar = '0') : n = 0 := by simp_all
example (h : 16 ≤ n) : n.digitChar = '*' := by simp [h]
example (h : n.digitChar = '!') : False := by simp_all
example : n.digitChar ≠ '!' := by simp
