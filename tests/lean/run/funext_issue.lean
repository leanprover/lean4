universes u

example (α : Type u) (p : Prop) (a b : α) (h : p → a = b) : (λ x : p, a) = (λ x : p, b) :=
funext h
