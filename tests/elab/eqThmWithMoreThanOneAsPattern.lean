@[simp] def foo: Nat → Nat → Nat
| p1@(t₁ + 1), p2@(t₂ + 1) => foo t₁ t₂
| _, _ => 0
