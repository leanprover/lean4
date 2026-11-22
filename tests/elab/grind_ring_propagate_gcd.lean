/-!
Regression test: the `grind` ring solver must propagate `a = b` when `a` and `b` simplify to
the same polynomial up to a common constant factor, e.g., `3*a ↦ 3*p` and `b ↦ p`.
This came up in Mathlib's `Stirling.lean` after lean4#16525 changed which basis equation is used
to simplify a monomial.
-/

opaque HasSum : (Nat → Rat) → Rat → Prop

example (n : Nat) (r : Rat) (hr : r = ((1 : Rat) / (2 * ((n : Rat) + 1) + 1)) ^ 2) (hr1 : r < 1)
    (h : HasSum (fun i => r ^ i * r / 3) ((1 - r)⁻¹ * r / 3)) :
    HasSum (fun j ↦ r ^ (j + 1) / 3)
      ((1 : Rat) / (12 * ((n + 1 : Nat) : Rat) * (((n + 1 : Nat) : Rat) + 1))) := by
  grind
