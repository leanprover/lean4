/-!
Model-based theory combination must treat casts into types that `lia` does not interpret
(e.g., a generic ring `R` or `ZMod n`) as uninterpreted functions, and case-split on their
arguments. This applies to both `NatCast.natCast` and `IntCast.intCast`. The first example is
reduced from `DihedralGroup.center_eq_closure_of_even_ne_two` in Mathlib.
-/

open Lean Grind
attribute [instance] Semiring.natCast Ring.intCast

variable [CommRing R]

/-! `NatCast.natCast` -/

example (n m k : Nat) (h : n = 2 * m) (h₂ : 2 * k = n) : (m : R) = (k : R) := by
  grind

/-- trace: [grind.mbtc] m = k -/
#guard_msgs in
set_option trace.grind.mbtc true in
example (m k : Nat) (h₁ : m ≤ k) (h₂ : k ≤ m + 1) (h₃ : 2 ∣ k - m) : (m : R) = (k : R) := by
  grind

/-! `IntCast.intCast` -/

/-- trace: [grind.mbtc] m = k -/
#guard_msgs in
set_option trace.grind.mbtc true in
example (m k : Int) (h₁ : m ≤ k) (h₂ : k ≤ m + 1) (h₃ : 2 ∣ k - m) : (m : R) = (k : R) := by
  grind

/-- trace: [grind.mbtc] m = k -/
#guard_msgs in
set_option trace.grind.mbtc true in
example (m k : Int) (h₁ : m ≤ k) (h₂ : k ≤ m + 1) (h₃ : 2 ∣ k - m) (h : (m : R) ≠ (k : R)) :
    False := by
  grind

/-- trace: [grind.mbtc] m = ↑k -/
#guard_msgs in
set_option trace.grind.mbtc true in
example (m : Int) (k : Nat) (h₁ : m ≤ k) (h₂ : k ≤ m + 1) (h₃ : 2 ∣ k - m) :
    (m : R) = ((k : Int) : R) := by
  grind

/-- trace: [grind.mbtc] m = k -/
#guard_msgs in
set_option trace.grind.mbtc true in
example (m k : Int) (x : R) (h₁ : m ≤ k) (h₂ : k ≤ m + 1) (h₃ : 2 ∣ k - m) :
    x * (m : R) + 1 = x * (k : R) + 1 := by
  grind

/-! Only arguments with the same value in the `lia` model are split on: `c` is not. -/

/-- trace: [grind.mbtc] a = b -/
#guard_msgs in
set_option trace.grind.mbtc true in
example (a b c : Int) (h₁ : a ≤ b) (h₂ : b ≤ a + 1) (h₃ : 2 ∣ b - a) (_ : c = a + 3) :
    (a : R) + (c : R) = (b : R) + (c : R) := by
  grind

/-! `lia` interprets casts from `Nat` into `Int` and `Fin 5`, so no case split is needed. -/

#guard_msgs in
set_option trace.grind.mbtc true in
example (m k : Nat) (h₁ : m ≤ k) (h₂ : k ≤ m + 1) (h₃ : 2 ∣ k - m) : (m : Int) = (k : Int) := by
  grind

open Fin.NatCast in
#guard_msgs in
set_option trace.grind.mbtc true in
example (m k : Nat) (h₁ : m ≤ k) (h₂ : k ≤ m + 1) (h₃ : 2 ∣ k - m) : (m : Fin 5) = (k : Fin 5) := by
  grind

/-!
`lia` does not interpret casts from `Int` into `Fin 5`, but `grind` reduces their `Fin.val` to
`(m % 5).toNat`, so no case split is needed either.
-/

open Fin.IntCast in
#guard_msgs in
set_option trace.grind.mbtc true in
example (m k : Int) (h₁ : m ≤ k) (h₂ : k ≤ m + 1) (h₃ : 2 ∣ k - m) : (m : Fin 5) = (k : Fin 5) := by
  grind
