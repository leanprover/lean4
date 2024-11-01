universe u

axiom elimEx (motive : Nat → Nat → Sort u) (x y : Nat)
  (diag  : (a : Nat) → motive a a)
  (upper : (delta a : Nat) → motive a (a + delta.succ))
  (lower : (delta a : Nat) → motive (a + delta.succ) a)
  : motive y x

/-- error: invalid alternative name 'lower2', expected 'diag', 'upper' or 'lower' -/
#guard_msgs in
theorem invalidAlt (p: Nat) : p ≤ q ∨ p > q := by
  cases p, q using elimEx with
  | lower2 /- error -/ d => apply Or.inl; admit
  | upper d => apply Or.inr
  | diag    => apply Or.inl; apply Nat.le_refl
