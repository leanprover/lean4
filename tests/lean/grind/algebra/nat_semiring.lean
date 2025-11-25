-- Remark: we need some support for nonlinear in `cutsat`

example {a b c d : Nat} (h : a = b + c * d) (w : 1 ≤ d) : a ≥ c := by
  -- grind -- fails, but would be lovely
  subst h
  apply Nat.le_add_left_of_le
  apply Nat.le_mul_of_pos_right
  assumption

example {a b c d : Int} (h : a = b + c * d) (hb : 0 ≤ b) (hc : 0 ≤ c) (w : 1 ≤ d) : a ≥ c := by
  -- grind -- fails also
  subst h
  conv => rhs; rw [← Int.zero_add c]
  apply Int.add_le_add
  · assumption
  · have : 0 ≤ c * (d - 1) := Int.mul_nonneg (by omega) (by omega)
    rw [Int.mul_sub, Int.mul_one, Int.sub_nonneg] at this
    exact this

-- Note: if we can automate the `Int` version here, we can also automate the `Nat` version just by embedding in `Int`.

open Std Lean Grind

example {α : Type} [IntModule α] [LE α] [IsPreorder α] [OrderedAdd α] {a b c : α} {d : Int}
    (wb : 0 ≤ b) (wc : 0 ≤ c)
    (h : a = b + d • c) (w : 1 ≤ d) : a ≥ c := by
  subst h
  conv => rhs; rw [← AddCommMonoid.zero_add c]
  apply OrderedAdd.add_le_add
  · exact wb
  · have := OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg w (le_refl c) (by decide) wc
    rwa [IntModule.one_zsmul] at this

-- We can prove this directly in an ordered NatModule, from the axioms. (But shouldn't, see below.)
example {α : Type} [NatModule α] [LE α] [IsPreorder α] [OrderedAdd α] {a b c : α} {d : Nat}
    (wb : 0 ≤ b) (wc : 0 ≤ c)
    (h : a = b + d • c) (w : 1 ≤ d) : a ≥ c := by
  subst h
  conv => rhs; rw [← AddCommMonoid.zero_add c]
  apply OrderedAdd.add_le_add
  · exact wb
  · have := OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg w (le_refl c) wc
    rwa [NatModule.one_nsmul] at this

-- The correct proof is to embed a NatModule in its IntModule envelope.

-- From Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
theorem HomogeneousLocalization.Away.isLocalization_mul.extracted_1 (d e : Nat) : (d + e) • (d + e) = e • e + (2 * e + d) • d := by grind
