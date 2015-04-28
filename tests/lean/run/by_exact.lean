import data.nat
open nat

example (a b c : nat) (h₁ : a + 0 = b) (h₂ : b = c) : a = c :=
by esimp at h₁; rewrite h₂ at h₁; exact h₁
