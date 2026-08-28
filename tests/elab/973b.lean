opaque f : Nat → Nat
opaque q : Nat → (Nat → Prop) → Nat

@[simp]
theorem ex {x : Nat} {p : Nat → Prop} (h₁ : p x) (h₂ : q x p = x) : f x = x :=
  sorry

set_option trace.Meta.Tactic.simp.discharge true
theorem foo : f (f x) = x := by
  simp (config := { failIfUnchanged := false })
  sorry
