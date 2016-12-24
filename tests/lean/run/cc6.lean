open tactic

example (a b c a' b' c' : nat) : a = a' → b = b' → c = c' → a + b + c + a = a' + b' + c' + a' :=
by cc

example (a b : unit) : a = b :=
by cc

example (a b : nat) (h₁ : a = 0) (h₂ : b = 0) : a = b → h₁ == h₂ :=
by cc

constant inv' : ∀ (a : nat), a ≠ 0 → nat

example (a b : nat) (h₁ : a ≠ 0) (h₂ : b ≠ 0) : a = b → inv' a h₁ = inv' b h₂ :=
by cc

example (C : nat → Type) (f : Π n, C n → C n) (n m : nat) (c : C n) (d : C m) :
        f n == f m → c == d → n == m → f n c == f m d :=
by cc
