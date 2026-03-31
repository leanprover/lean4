def Commute (a b : Nat) := a * b = b * a

example : Commute m n :=
  calc m * n = n * m := Nat.mul_comm ..
