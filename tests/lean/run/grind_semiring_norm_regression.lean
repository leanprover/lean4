section Mathlib.Data.Nat.Init

namespace Nat

class AtLeastTwo (n : Nat) : Prop where
  prop : 2 ≤ n

instance (n : Nat) [NeZero n] : (n + 1).AtLeastTwo :=
  ⟨add_le_add (one_le_iff_ne_zero.mpr (NeZero.ne n)) (Nat.le_refl 1)⟩

end Nat

end Mathlib.Data.Nat.Init

section Mathlib.Data.Nat.Cast.Defs

instance {R : Type} {n : Nat} [NatCast R] [Nat.AtLeastTwo n] :
    OfNat R n where
  ofNat := n.cast

end Mathlib.Data.Nat.Cast.Defs
section Mathlib.Algebra.GroupWithZero.Defs

class MulZeroClass (α : Type) extends Mul α, Zero α where
  mul_zero : ∀ a : α, a * 0 = 0

end Mathlib.Algebra.GroupWithZero.Defs

section Mathlib.Algebra.Ring.Defs

class Semiring (α : Type) extends
    One α, NatCast α, Add α, Mul α, MulZeroClass α

end Mathlib.Algebra.Ring.Defs

section Mathlib.Algebra.Ring.GrindInstances

instance Semiring.toGrindSemiring (α : Type) [s : Semiring α] :
    Lean.Grind.Semiring α :=
  { s with
    nsmul := sorry
    npow := sorry
    ofNat | 0 | 1 | n + 2 => inferInstance
    natCast := sorry
    add_zero := sorry
    mul_one := sorry
    zero_mul := sorry
    pow_zero := sorry
    pow_succ := sorry
    ofNat_eq_natCast := sorry
    ofNat_succ := sorry
    nsmul_eq_natCast_mul := sorry
    add_comm := sorry
    left_distrib := sorry
    right_distrib := sorry
    mul_zero := sorry
    add_assoc := sorry
    mul_assoc := sorry
    one_mul := sorry }

end Mathlib.Algebra.Ring.GrindInstances

section Mathlib.Algebra.Polynomial.Coeff

theorem coeff_mul_X_pow {R : Type} [Semiring R] (p : R) (n d : Nat) :
    ∀ b, b.1 + b.2 = d + n → b ≠ (d, n) → p * (if n = b.2 then 1 else 0) = 0 := by
  grind only [MulZeroClass.mul_zero]

theorem coeff_mul_X_pow' {R : Type} [Semiring R] (p : R) (n d : Nat) :
    ∀ b, b.1 + b.2 = d + n → b ≠ (d, n) → p * (if n = b.2 then 1 else 0) = 0 := by
  grind only

example [Semiring α] (a b c : α) : b = 0 → a * b * c = 0 := by
  grind only

example [Semiring α] (a b c : α) : c = 1 → a = 1 → a * b * c = b := by
  grind only
