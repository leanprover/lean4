example (n : Nat)
    (f : Nat → Rat → Rat)
    (x : Rat)
    (H : ∀ (x : Rat), 0 ≤ x →
         (4 < x → f n x < 2 * x) ∧ (x = 4 → f n x = 2 * x) ∧ (x < 4 → 2 * x < f n x)) :
    x ∈ [4] ↔ f n x = 2 * x := by
  fail_if_success grind
  sorry

example (n : Nat)
    (f : Nat → Rat → Rat)
    (x : Rat)
    (_ : x ≥ 0)
    (H : ∀ (x : Rat), 0 ≤ x →
         (4 < x → f n x < 2 * x) ∧ (x = 4 → f n x = 2 * x) ∧ (x < 4 → 2 * x < f n x)) :
    x ∈ [4] ↔ f n x = 2 * x := by
  grind

example (n : Nat)
    (f : Nat → Rat → Rat)
    (x : Rat)
    (_ : x ≥ 0)
    (H : ∀ (x : Rat), 0 ≤ x →
         (4 < x → f n x < 2 * x) ∧ (x = 4 → f n x = 2 * x) ∧ (x < 4 → 2 * x < f n x)) :
    f n x = 2 * x → x ∈ [4] := by
  grind

example (n : Nat)
    (f : Nat → Rat → Rat)
    (x : Rat)
    (H : ∀ (x : Rat), 0 ≤ x →
         (4 < x → f n x < 2 * x) ∧ (x = 4 → f n x = 2 * x) ∧ (x < 4 → 2 * x < f n x)) :
    x ∈ [4] → f n x = 2 * x := by
  grind
