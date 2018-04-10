def all (p : ℕ → Prop) : Prop := ∀x, p x
example {p : ℕ → Prop} (h : all p) : p 0 := ‹all p› 0
