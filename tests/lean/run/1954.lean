

def All (p : Nat → Prop) : Prop := ∀x, p x
example {p : Nat → Prop} (h : All p) : p 0 := h 0
