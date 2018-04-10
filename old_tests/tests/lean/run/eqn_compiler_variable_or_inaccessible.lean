example {α : Type} {p q : α → Prop} {x : α} (h : ∀ y, p y → q y) (hx : q x) :
  ∀ y, x = y ∨ p y → q y
| x  (or.inr p)   := h x p
| ._ (or.inl rfl) := hx
