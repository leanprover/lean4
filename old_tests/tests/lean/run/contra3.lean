open tactic nat

example (a b c : Prop) : a → b → ¬ a → c :=
by do intros, contradiction

example (a b c : Prop) : a → false → b → c :=
by do intros, contradiction

example (a b : nat) : succ a = 0 → b = 0 :=
by do intro `H, contradiction

example (a b : nat) : succ a = succ b → succ a = 0 → b = 0 :=
by do intros, contradiction
