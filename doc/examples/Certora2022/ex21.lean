/- Simplifier -/

example (p : Nat → Prop) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example (p : Nat → Prop) (h : p (x * y)) : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; assumption

example (p : Nat → Prop) (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
  simp at h; assumption

def f (m n : Nat) : Nat :=
  m + n + m

example (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [h, ←h', f]

example (p : Nat → Prop) (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
  simp at *
  simp [*]
