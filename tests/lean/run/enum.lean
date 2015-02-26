import logic

inductive Three :=
| zero : Three
| one  : Three
| two  : Three

namespace Three

  theorem disj (a : Three) : a = zero ∨ a = one ∨ a = two :=
  Three.rec (or.inl rfl) (or.inr (or.inl rfl)) (or.inr (or.inr rfl)) a

  example (a : Three) : a ≠ zero → a ≠ one → a = two :=
  Three.rec (λ h₁ h₂, absurd rfl h₁) (λ h₁ h₂, absurd rfl h₂) (λ h₁ h₂, rfl) a

end Three
