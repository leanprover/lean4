set_option warn.sorry false

/-!
`grind` must fail quickly on problems containing high degree polynomials
-/

theorem explosion (r p t3 t19 : Nat) : t19 % p = r ^ (2 ^ 250 - 1) % p ∧ t3 % p = r ^ 11 % p := by
  fail_if_success grind
  sorry
