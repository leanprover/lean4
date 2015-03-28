import data.nat
open nat
variables (f : nat → nat → nat → nat) (a b c : nat)

example (H₁ : a = b) (H₂ : f b a b = 0) : f a a a = 0 :=
by rewrite [H₁ at -{2}, H₂]

example (H₁ : a = b) (H₂ : f b a b = 0) (H₃ : c = f a a a) : c = 0 :=
by rewrite [H₁ at H₃ -{2}, H₂ at H₃, H₃]
