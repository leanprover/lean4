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

class Inv (α : Type u) where
  inv : α → α

postfix:100 "⁻¹" => Inv.inv

class Group (α : Type u) extends Monoid α, Inv α where
  mul_left_inv (a : α) : a⁻¹ * a = one

class CommGroup (α : Type u) extends Group α, CommMonoid α

#check @CommGroup.mk
#print CommGroup.toCommMonoid
