example (h : 2000 = 2001) : False := by
  cases h

example (h : 20000 = 20001) : False := by
  cases h

example (h : x + 20000 = 20001) : x = 1 := by
  cases h
  rfl
