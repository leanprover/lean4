open nat

example (q p : Type) (h₁ : p) (h₂ : ¬ p) : q :=
by contradiction

example (q p : Type) (h₁ : p) (h₂ : p → empty) : q :=
by contradiction

example (q : Type) (a b : nat) (h₁ : a + b = 0) (h₂ : ¬ a + b = 0) : q :=
by contradiction

example (q : Type) (a b : nat) (h₁ : a + b = 0) (h₂ : a + b ≠ 0) : q :=
by contradiction

example (q : Type) (a b : nat) (h₁ : a + b = 0) (h₂ : a + b = 0 → empty) : q :=
by contradiction
