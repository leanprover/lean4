example  (p : Nat → Prop) (h : ∀ n, p (n+1) = p n) : (p m ↔ p 0) := by
  induction m
  case succ ih => rw [h, ih]
  case zero => exact Iff.rfl
