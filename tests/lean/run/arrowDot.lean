def test (f : Nat → Nat) (g : Nat → Nat) :=
  f.comp g $ 10

example : test (·+1) (·*2) = 21 :=
  rfl
