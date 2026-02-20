axiom A : Nat
axiom B : Nat
axiom equality : A = B

example : A = 3 -> B = 3 := by
  intro h
  rewrite [equality] at *
