section Mathlib.Algebra.Group.Defs

class Monoid (M : Type u) extends Mul M where

class AddGroup (G : Type u) extends Add G, Neg G, Sub G where

theorem add_sub_assoc {G : Type} [AddGroup G] (a b c : G) : a + b - c = a + (b - c) := by
  sorry

end Mathlib.Algebra.Group.Defs

abbrev Function.swap {φ : α → β → Sort u₃} (f : ∀ x y, φ x y) : ∀ y x, φ x y := fun y x => f x y

section Mathlib.Algebra.Group.Basic

@[simp]
theorem add_sub_cancel {G} [AddGroup G](a b : G) : a + (b - a) = b := by
  sorry

end Mathlib.Algebra.Group.Basic

section Mathlib.Algebra.Order.Monoid.Unbundled.Defs

open Function

variable (M N : Type) (μ : M → N → N) (r : N → N → Prop)

def Covariant : Prop :=
  ∀ (m) {n₁ n₂}, r n₁ n₂ → r (μ m n₁) (μ m n₂)

class CovariantClass : Prop where
  protected elim : Covariant M N μ r

abbrev AddLeftMono [Add M] [LE M] : Prop :=
  CovariantClass M M (· + ·) (· ≤ ·)

abbrev AddRightMono [Add M] [LE M] : Prop :=
  CovariantClass M M (swap (· + ·)) (· ≤ ·)

instance covariant_swap_add_of_covariant_add [Add N]
    [CovariantClass N N (· + ·) r] : CovariantClass N N (swap (· + ·)) r where
  elim := sorry

end Mathlib.Algebra.Order.Monoid.Unbundled.Defs

section Mathlib.Algebra.Order.Monoid.Unbundled.Basic

instance Int.instAddLeftMono : AddLeftMono Int where
  elim := sorry

end Mathlib.Algebra.Order.Monoid.Unbundled.Basic

section Mathlib.Algebra.Order.Sub.Defs

class OrderedSub (α : Type) [LE α] [Add α] [Sub α] : Prop where

@[simp]
theorem tsub_le_iff_right {α : Type}  [LE α] [Add α] [Sub α] [OrderedSub α] {a b c : α} :
    a - b ≤ c ↔ a ≤ c + b := sorry

end Mathlib.Algebra.Order.Sub.Defs

section Mathlib.Algebra.Order.Monoid.Unbundled.Basic

instance AddGroup.toOrderedSub {α : Type} [AddGroup α] [LE α]
    [AddRightMono α] : OrderedSub α := sorry

end Mathlib.Algebra.Order.Monoid.Unbundled.Basic

section Mathlib.Data.Nat.Cast.Defs

class AddMonoidWithOne (R : Type) extends NatCast R, Add R where

theorem Nat.cast_add [AddMonoidWithOne R] (m n : Nat) : ((m + n : Nat) : R) = m + n := sorry

end Mathlib.Data.Nat.Cast.Defs

section Mathlib.Data.Int.Cast.Defs

class AddGroupWithOne (R : Type) extends IntCast R, AddMonoidWithOne R, AddGroup R where

end Mathlib.Data.Int.Cast.Defs

section Mathlib.Data.Int.Cast.Basic

namespace Int

variable {R : Type} [AddGroupWithOne R]

@[norm_cast]
theorem cast_subNatNat (m n) : ((Int.subNatNat m n : Int) : R) = m - n := sorry

end Int

end Mathlib.Data.Int.Cast.Basic

section Mathlib.Algebra.Group.Int.Defs

namespace Int

instance instCommMonoid : Monoid Int where

instance instAddCommGroup : AddGroup Int where

instance instCommSemigroup : Mul Int := by infer_instance

end Int

end Mathlib.Algebra.Group.Int.Defs

section Mathlib.Algebra.Ring.Defs

class NonAssocSemiring (α : Type) extends Add α, Mul α, Zero α

class NonAssocRing (α : Type) extends AddGroup α, NonAssocSemiring α

class Ring (R : Type) extends NonAssocSemiring R, AddGroupWithOne R

section NonAssocRing

variable {α : Type} [NonAssocRing α]

theorem mul_sub_left_distrib (a b c : α) : a * (b - c) = a * b - a * c := sorry

end NonAssocRing

section Ring

variable {α : Type} [Ring α]

instance (priority := 100) Ring.toNonAssocRing : NonAssocRing α :=
  { ‹Ring α› with }

end Ring

class CommRing (α : Type) extends Ring α, Monoid α

end Mathlib.Algebra.Ring.Defs

section Mathlib.Algebra.Ring.Int.Defs

namespace Int

instance instCommRing : CommRing Int where
  intCast := (·)

end Int

end Mathlib.Algebra.Ring.Int.Defs

example {a b : Nat}
  (this : (b : Int) + ↑b * (↑a - ↑b) ≤ (↑b + (↑a - ↑b))) :
    a * b ≤ a + b * b := by
  simp [mul_sub_left_distrib, ← add_sub_assoc] at this
  norm_cast at this
  grind

/--
info: Try this:
  [apply] simp only [mul_sub_left_distrib, ← add_sub_assoc, add_sub_cancel, tsub_le_iff_right] at this
-/
#guard_msgs in
example {a b : Nat}
  (this : (b : Int) + ↑b * (↑a - ↑b) ≤ (↑b + (↑a - ↑b))) :
    a * b ≤ a + b * b := by
  simp? [mul_sub_left_distrib, ← add_sub_assoc] at this
  norm_cast at this
  grind

example {a b : Nat}
  (this : (b : Int) + ↑b * (↑a - ↑b) ≤ (↑b + (↑a - ↑b))) :
    a * b ≤ a + b * b := by
  simp only [mul_sub_left_distrib, ← add_sub_assoc, add_sub_cancel, tsub_le_iff_right] at this
  norm_cast at this
  grind
