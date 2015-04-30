example (a b : nat) (h : empty) : a = b :=
by contradiction

example : ∀ (a b : nat), empty → a = b :=
by contradiction

example : ∀ (a b : nat), 0 = 1 → a = b :=
by contradiction

definition id {A : Type} (a : A) := a

example : ∀ (a b : nat), id empty → a = b :=
by contradiction

example : ∀ (a b : nat), id (0 = 1) → a = b :=
by contradiction
