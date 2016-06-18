open tactic

example (p q : Prop) : p → q → p ∧ q :=
by do intros, constructor, assumption, assumption

example (p q : Prop) : p → q → p ∧ q :=
by do intros, split, assumption, assumption

example (p q : Prop) : p → p ∨ q :=
by do intros, left, assumption

example (p q : Prop) : q → p ∨ q :=
by do intros, right, assumption

example (p q : Prop) : p → p ∨ q :=
by do intros, constructor_idx 1, assumption

example (p q : Prop) : q → p ∨ q :=
by do intros, constructor_idx 2, assumption
