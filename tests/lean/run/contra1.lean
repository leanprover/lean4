open nat

example (a b : nat) (h : false) : a = b :=
by contradiction

example : ∀ (a b : nat), false → a = b :=
by contradiction

example : ∀ (a b : nat), (0:nat) = 1 → a = b :=
by contradiction

definition id {A : Type} (a : A) := a

example : ∀ (a b : nat), id false → a = b :=
by contradiction

example : ∀ (a b : nat), id ((0:nat) = 1) → a = b :=
by contradiction
