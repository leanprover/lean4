class Semigroup (α : Type u) extends Mul α where
  mul_assoc (a b c : α) : a * b * c = a * (b * c)

class CommSemigroup (α : Type u) extends Semigroup α where
  mul_comm (a b : α) : a * b = b * a

class One (α : Type u) where
  one : α

instance [One α] : OfNat α (nat_lit 1) where
  ofNat := One.one

class Monoid (α : Type u) extends Semigroup α, One α where
  one_mul (a : α) : 1 * a = a
  mul_one (a : α) : a * 1 = a

class CommMonoid (α : Type u) extends Monoid α, CommSemigroup α

set_option pp.all true
#check CommMonoid.mk
#print CommMonoid.toCommSemigroup

class Inv (α : Type u) where
  inv : α → α

postfix:100 "⁻¹" => Inv.inv

class Group (α : Type u) extends Monoid α, Inv α where
  mul_left_inv (a : α) : a⁻¹ * a = 1

class CommGroup (α : Type u) extends Group α, CommMonoid α

#check CommGroup.mk
#print CommGroup.toCommMonoid

class AddSemigroup (α : Type u) extends Add α where
  add_assoc (a b c : α) : a + b + c = a + (b + c)

class AddCommSemigroup (α : Type u) extends AddSemigroup α where
  add_comm (a b : α) : a + b = b + a

class AddMonoid (α : Type u) extends AddSemigroup α, Zero α where
  zero_add (a : α) : 0 + a = a
  add_zero (a : α) : a + 0 = a

class AddCommMonoid (α : Type u) extends AddMonoid α, AddCommSemigroup α

class AddGroup (α : Type u) extends AddMonoid α, Neg α where
  add_left_neg (a : α) : -a + a = 0

class AddCommGroup (α : Type u) extends AddGroup α, AddCommMonoid α

class Distrib (α : Type u) extends Mul α, Add α where
  left_distrib ( a b c : α) : a * (b + c) = (a * b) + (a * c)
  right_distrib (a b c : α) : (a + b) * c = (a * c) + (b * c)

class MulZero (α : Type u) extends Mul α, Zero α where
  zero_mul (a : α) : 0 * a = 0
  mul_zero (a : α) : a * 0 = 0

class ZeroNeOne (α : Type u) extends Zero α, One α where
  zero_ne_one : (0:α) ≠ 1

class Semiring (α : Type u) extends AddCommMonoid α, Monoid α, Distrib α, MulZero α

class CommSemiring (α : Type u) extends Semiring α, CommMonoid α

class Ring (α : Type u) extends AddCommGroup α, Monoid α, Distrib α

class CommRing (α : Type u) extends Ring α, CommSemigroup α

class NoZeroDivisors (α : Type u) extends Mul α, Zero α where
  eq_zero_or_eq_zero_of_mul_eq_zero (a b : α) : a * b = 0 → a = 0 ∨ b = 0

class IntegralDomain (α : Type u) extends CommRing α, NoZeroDivisors α, ZeroNeOne α

class DivisionRing (α : Type u) extends Ring α, Inv α, ZeroNeOne α where
  mul_inv_cancel {a : α} : a ≠ 0 → a * a⁻¹ = 1
  inv_mul_cancel {a : α} : a ≠ 0 → a⁻¹ * a = 1

class Field (α : Type u) extends DivisionRing α, CommRing α

set_option pp.all false in
#check Field.mk
#print Field.toDivisionRing
#print Field.toCommRing
