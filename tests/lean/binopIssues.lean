axiom Int.add_comm (i j : Int) : i + j = j + i

example (n : Nat) (i : Int) : n + i = i + n := by
  rw [Int.add_comm]

def f1 (a : Int) (b c : Nat) : Int :=
  a + (b - c)

def f2 (a : Int) (b c : Nat) : Int :=
  (b - c) + a

#print f1
#print f2
