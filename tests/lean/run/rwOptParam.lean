axiom P : Prop
axiom p : P
axiom f : P → Nat
axiom Q : Nat → Prop
axiom q : ∀ n, Q n
theorem r (p : P := p) : 0 = f p := sorry
example : Q 0 := by
  rw [r]
  apply q
