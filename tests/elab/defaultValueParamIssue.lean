structure Something (i: Nat) where
  n1: Nat := 1
  n2: Nat := 1 + i

def s : Something 10 := {}

example : s.n2 = 11 := rfl
