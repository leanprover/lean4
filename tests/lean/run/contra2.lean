open nat

example (q p : Prop) (h₁ : p) (h₂ : ¬ p) : q :=
by contradiction

example (q p : Prop) (h₁ : p) (h₂ : p → false) : q :=
by contradiction

example (q : Prop) (a b : nat) (h₁ : a + b = 0) (h₂ : ¬ a + b = 0) : q :=
by contradiction

example (q : Prop) (a b : nat) (h₁ : a + b = 0) (h₂ : a + b ≠ 0) : q :=
by contradiction

example (q : Prop) (a b : nat) (h₁ : a + b = 0) (h₂ : a + b = 0 → false) : q :=
by contradiction
