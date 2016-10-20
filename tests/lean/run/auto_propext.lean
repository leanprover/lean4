example (p q : Prop) (h : p) : q ∨ p :=
by simp [h]

example (p q : Prop) : p → q ∨ p :=
by ctx_simp
