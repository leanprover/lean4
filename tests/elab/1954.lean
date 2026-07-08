

def all (p : Nat → Prop) : Prop := ∀x, p x
example {p : Nat → Prop} (h : all p) : p 0 := h 0
