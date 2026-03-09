example : Nat := ( .zero : Nat)
example : Nat := ( .zero : _)
example : Nat := ( .zero :) -- fail
example : Nat := by have' := .zero; exact this -- fail

def add (x y : Nat) := x + y

example (h₁ : z = x + y) (h₂ : w = z) : w = add x y := have := h₁ ▸ h₂; by exact this
example (h₁ : z = x + y) (h₂ : w = z) : w = add x y := have := h₁ ▸ h₂; this -- fail
example (h₁ : z = x + y) (h₂ : w = z) : w = add x y := h₁ ▸ h₂ -- fail
example (h₁ : z = x + y) (h₂ : w = z) : w = add x y := (h₁ ▸ h₂ :)
