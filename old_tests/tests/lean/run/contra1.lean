open nat tactic

example (a b : nat) (h : false) : a = b :=
by contradiction

example : ∀ (a b : nat), false → a = b :=
by do intros, contradiction

example : ∀ (a b : nat), (0:nat) = 1 → a = b :=
by do intros, contradiction
