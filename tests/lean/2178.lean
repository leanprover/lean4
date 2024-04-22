class Zero (α : Type u) where
  zero : α
class AddZeroClass (M : Type u) extends Zero M, Add M
class AddMonoid (M : Type u) extends AddZeroClass M where
  nsmul : Nat → M → M := fun _ _ => Zero.zero
class AddCommMonoid (M : Type u) extends Zero M, AddMonoid M
class AddMonoidWithOne (R : Type u) extends AddMonoid R
class AddCommMonoidWithOne (R : Type u) extends AddMonoidWithOne R, AddCommMonoid R
class NonAssocSemiring (α : Type u) extends Zero α, AddCommMonoidWithOne α
class Semiring (α : Type u) extends Zero α, NonAssocSemiring α
