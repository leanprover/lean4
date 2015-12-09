open eq

example (a b : nat) (h : empty) : a = b :=
by contradiction

example : ∀ (a b : nat), empty → a = b :=
by contradiction

example : ∀ (a b : nat), 0 = 1 :> ℕ → a = b :=
by contradiction

example : ∀ (a b : nat), id empty → a = b :=
by contradiction

example : ∀ (a b : nat), id (0 = 1 :> ℕ) → a = b :=
by contradiction
