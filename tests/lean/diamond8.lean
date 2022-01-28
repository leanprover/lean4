class One (M : Type u) where one : M
instance {M} [One M] : OfNat M (nat_lit 1) := ⟨One.one⟩

class Zero (A : Type u) where zero : A
instance {A} [Zero A] : OfNat A (nat_lit 0) := ⟨Zero.zero⟩

class Monoid (M : Type u) extends Mul M, One M where
  mul_one (m : M) : m * 1 = m

class AddCommMonoid (A : Type u) extends Add A, Zero A

class MonoidWithZero (M₀ : Type u) extends Monoid M₀, Zero M₀

class Semiring (R : Type u) extends AddCommMonoid R, MonoidWithZero R, One R

#print Semiring -- only toMonoid field, no duplicate toOne

def oneViaMonoid {M} [Monoid M] : M := 1
example {R} [Semiring R] : (1 : R) = oneViaMonoid := rfl

example : Semiring Nat where
  mul_one := by simp
  zero := 0
  one := 1
