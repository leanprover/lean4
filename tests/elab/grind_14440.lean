module

/-!
https://github.com/leanprover/lean4/issues/14440
It has already been fixed by #14390
-/

set_option warn.sorry false

open Lean.Grind

example {S : Type} [CommRing S] (a b v : S)
    (ha : a ^ 3 = 0) (hab : a ^ 2 * b + 2 = 0) (hv : v ^ 2 = a ^ 2 * v) :
    (v * (1 + b * v)) ^ 2 = a ^ 2 * (v * (1 + b * v)) := by
  grind

-- Simple consequences in the same ring.
example {S : Type} [CommRing S] (a b : S)
    (ha : a ^ 3 = 0) (hab : a ^ 2 * b + 2 = 0) : 2 * a = 0 := by
  grind

example {S : Type} [CommRing S] (a b : S)
    (ha : a ^ 3 = 0) (hab : a ^ 2 * b + 2 = 0) : (a * b) ^ 2 * a ^ 2 = 0 := by
  grind

-- Goals requiring coefficient cancellation are not provable without `NoNatZeroDivisors`
-- (`NoNatZeroDivisors` is false in this ring: `2 • (2 * b) = 0` with `2 ≠ 0`).
-- They must fail gracefully, not with an internal error.
example {S : Type} [CommRing S] (a b : S)
    (ha : a ^ 3 = 0) (hab : a ^ 2 * b + 2 = 0) : a = 0 := by
  fail_if_success grind
  sorry

-- Disequality path.
example {S : Type} [CommRing S] (a b : S)
    (ha : a ^ 3 = 0) (hab : a ^ 2 * b + 2 = 0) (h : 2 * b ≠ 0) : b = 0 := by
  fail_if_success grind
  sorry
