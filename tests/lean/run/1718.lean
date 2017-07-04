theorem my_theorem : ∀ (a b c d : ℕ),
  d = c → a = b * c → a = b * d :=
take a b c d,
assume h₀ : d = c,
assume h₁ : a = b * c,
eq.substr h₀ h₁

example : ∀ (a b c d : ℕ),
  d = c → a = b * c → a = b * d :=
take a b c d, assume h₀ : d = c, assume h₁ : a = b * c,
h₀.substr h₁
