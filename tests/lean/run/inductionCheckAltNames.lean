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

/-- error: invalid alternative name 'lower2', expected 'lower' -/
#guard_msgs in
theorem oneMissingAlt (p: Nat) : p ≤ q ∨ p > q := by
  cases p, q using elimEx with
  | upper d => apply Or.inl; admit
  | diag    => apply Or.inl; apply Nat.le_refl
  | lower2  /- error -/ => apply Or.inr

/-- error: duplicate alternative name 'upper' -/
#guard_msgs in
theorem doubleAlt (p: Nat) : p ≤ q ∨ p > q := by
  cases p, q using elimEx with
  | upper d => apply Or.inl; admit
  | upper d /- error -/  => apply Or.inr
  | diag    => apply Or.inl; apply Nat.le_refl

/-- error: invalid occurrence of wildcard alternative, it must be the last alternative -/
#guard_msgs in
theorem invalidWildCard (p: Nat) : p ≤ q ∨ p > q := by
  cases p, q using elimEx with
  | upper d => apply Or.inl; admit
  | _ /- error -/  => apply Or.inr
  | diag    => apply Or.inl; apply Nat.le_refl


/-- error: invalid alternative name 'lower2', no unhandled alternatives -/
#guard_msgs in
theorem noAlt (p: Nat) : p ≤ q ∨ p > q := by
  cases p, q using elimEx with
  | upper d => apply Or.inl; admit
  | lower  => apply Or.inr
  | diag    => apply Or.inl; apply Nat.le_refl
  | lower2  /- error -/ => apply Or.inr
