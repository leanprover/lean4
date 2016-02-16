open nat eq
infixr + := sum

theorem add_assoc₁ : Π (a b c : ℕ), (a + b) + c = a + (b + c)
| a b 0 := eq.refl (nat.rec a (λ x, succ) b)
| a b (succ n) :=
  calc (a + b) + (succ n) = succ ((a + b) + n) : rfl
                      ... = succ (a + (b + n)) : ap succ (add_assoc₁ a b n)
                      ... = a + (succ (b + n)) : rfl
                      ... = a + (b + (succ n)) : rfl

theorem add_assoc₂ : Π (a b c : ℕ), (a + b) + c = a + (b + c)
| a b 0        := eq.refl (nat.rec a (λ x, succ) b)
| a b (succ n) := ap succ (add_assoc₂ a b n)

theorem add_assoc₃ : Π (a b c : ℕ), (a + b) + c = a + (b + c)
| a b nat.zero := eq.refl (nat.add a b)
| a b (succ n) := ap succ (add_assoc₃ a b n)
