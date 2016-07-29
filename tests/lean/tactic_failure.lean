open tactic

example (A B : Type) : B → A :=
by do intro `Hb, assumption
