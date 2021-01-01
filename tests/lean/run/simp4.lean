constant f : Nat → Nat
constant q : Nat → Prop
constant r : Nat → Prop

@[simp] axiom ax1 (p : Prop) : (p ∧ True) ↔ p
@[simp] axiom ax2 (x : Nat) : q (f x)
@[simp] axiom ax3 (x : Nat) : ¬ r (f x)
@[simp] axiom ax4 (p : Prop) : (p ∨ False) ↔ p

theorem ex1 (x : Nat) (h : q x) : q x ∧ q (f x) := by
  simp [h]

theorem ex2 (x : Nat) : q (f x) ∨ r (f x) := by
  simp
