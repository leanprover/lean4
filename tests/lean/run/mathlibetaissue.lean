/-!
# An etaExperiment timeout

The purpose of this file is to demonstrate a typeclass search that
* times out with `etaExperiment`
* is fast on `lean-toolchain` `gebner/lean4:reenableeta230506`
* is realistic, i.e. is a minimisation of something appearing in mathlib.

I've taken the example Matthew Ballard showed me:
```
import Mathlib

#synth Zero ℤ
```
and minimised it.

I've used `sorry` liberally,
but not changed the typeclass inheritance structure at all relative to mathlib4.
(It could probably be minimized further, but I think this is not the point?)

This file is minimised in the sense that:
* removing any command should either cause a new error, or remove the timeout.
* removing any field of a structure, and sorrying a field of an instance, should do the same.

Section titles correspond to the files the material came from the mathlib4/std4.
-/

section Std.Classes.Cast

class NatCast2 (R : Type u) where
class IntCast2 (R : Type u) where

end Std.Classes.Cast

section Std.Data.Int.Lemmas

end Std.Data.Int.Lemmas

section Std.Classes.RatCast

class RatCast (K : Type u) where

end Std.Classes.RatCast

section Mathlib.Init.ZeroOne

class One (α : Type u) where
  one : α
instance One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

end Mathlib.Init.ZeroOne

section Mathlib.Algebra.Group.Defs

class Inv (α : Type u) where
class Semigroup (G : Type u) extends Mul G where
class AddSemigroup (G : Type u) extends Add G where
class CommSemigroup (G : Type u) extends Semigroup G where
  mul_comm : ∀ a b : G, a * b = b * a
class AddCommSemigroup (G : Type u) extends AddSemigroup G where
class MulOneClass (M : Type u) extends One M, Mul M where
  mul_one : ∀ a : M, a * 1 = a
class AddZeroClass (M : Type u) extends Zero M, Add M where
  add_zero : ∀ a : M, a + 0 = a
class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
class AddCommMonoid (M : Type u) extends AddMonoid M, AddCommSemigroup M
class CommMonoid (M : Type u) extends Monoid M, CommSemigroup M
class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G where
class SubNegMonoid (G : Type u) extends AddMonoid G, Neg G, Sub G where
class Group (G : Type u) extends DivInvMonoid G where
class AddGroup (A : Type u) extends SubNegMonoid A where
class AddCommGroup (G : Type u) extends AddGroup G, AddCommMonoid G

end Mathlib.Algebra.Group.Defs

section Mathlib.Logic.Nontrivial

class Nontrivial (α : Type _) : Prop where

end Mathlib.Logic.Nontrivial

section Mathlib.Algebra.GroupWithZero.Defs

class MulZeroClass (M₀ : Type u) extends Mul M₀, Zero M₀ where
class IsLeftCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop where
class IsRightCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop where
class IsCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀]
  extends IsLeftCancelMulZero M₀, IsRightCancelMulZero M₀ : Prop
class NoZeroDivisors (M₀ : Type _) [Mul M₀] [Zero M₀] : Prop where
class SemigroupWithZero (S₀ : Type u) extends Semigroup S₀, MulZeroClass S₀
class MulZeroOneClass (M₀ : Type u) extends MulOneClass M₀, MulZeroClass M₀
class MonoidWithZero (M₀ : Type u) extends Monoid M₀, MulZeroOneClass M₀, SemigroupWithZero M₀
class CommMonoidWithZero (M₀ : Type _) extends CommMonoid M₀, MonoidWithZero M₀
class CancelCommMonoidWithZero (M₀ : Type _) extends CommMonoidWithZero M₀, IsLeftCancelMulZero M₀

end Mathlib.Algebra.GroupWithZero.Defs

section Mathlib.Data.Nat.Cast.Defs

class AddMonoidWithOne (R : Type u) extends NatCast2 R, AddMonoid R, One R where
class AddCommMonoidWithOne (R : Type _) extends AddMonoidWithOne R, AddCommMonoid R

end Mathlib.Data.Nat.Cast.Defs

section Mathlib.Data.Int.Cast.Defs

class AddGroupWithOne (R : Type u) extends IntCast2 R, AddMonoidWithOne R, AddGroup R where

end Mathlib.Data.Int.Cast.Defs

section Mathlib.Algebra.Ring.Defs

class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, MulZeroClass α
class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α
class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, MulZeroOneClass α,
    AddCommMonoidWithOne α
class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α
class Ring (R : Type u) extends Semiring R, AddCommGroup R, AddGroupWithOne R
class CommSemiring (R : Type u) extends Semiring R, CommMonoid R
class CommRing (α : Type u) extends Ring α, CommMonoid α
instance CommRing.toCommSemiring [s : CommRing α] : CommSemiring α :=
  { s with }
class IsDomain (α : Type u) [Semiring α] extends IsCancelMulZero α, Nontrivial α : Prop

end Mathlib.Algebra.Ring.Defs

section Mathlib.Data.Int.Basic

instance : CommRing Int where
  mul_comm := sorry
  mul_one := Int.mul_one -- Replacing this with `sorry` makes the timeout go away!
  add_zero := Int.add_zero -- Similarly here.

end Mathlib.Data.Int.Basic

section Mathlib.Algebra.Ring.Regular

section IsDomain

instance IsDomain.toCancelCommMonoidWithZero [CommSemiring α] [IsDomain α] :
    CancelCommMonoidWithZero α := { }

end IsDomain

end Mathlib.Algebra.Ring.Regular

section Mathlib.Algebra.Field.Defs

class DivisionRing (K : Type u) extends Ring K, DivInvMonoid K, Nontrivial K, RatCast K where
class Field (K : Type u) extends CommRing K, DivisionRing K

end Mathlib.Algebra.Field.Defs

section Mathlib.Algebra.Field.Basic

instance Field.isDomain [Field K] : IsDomain K :=
  sorry

end Mathlib.Algebra.Field.Basic

set_option synthInstance.maxHeartbeats 200 in
/-- info: MulZeroClass.toZero -/
#guard_msgs in
#synth Zero Int
