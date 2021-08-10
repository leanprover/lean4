class Semigroup (α : Type u) extends Mul α where
  mul_assoc (a b c : α) : a * b * c = a * (b * c)

class CommSemigroup (α : Type u) extends Semigroup α where
  mul_comm (a b : α) : a * b = b * a

class One (α : Type u) where
  one : α

class Monoid (α : Type u) extends Semigroup α, One α where
  one_mul (a : α) : one * a = a
  mul_one (a : α) : a * one = a

class CommMonoid (α : Type u) extends Monoid α, CommSemigroup α

set_option pp.all true
#check @CommMonoid.mk
#print CommMonoid.toCommSemigroup
