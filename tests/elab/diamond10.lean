class AddMonoid (A : Type u) extends Add A, Zero A
class Semiring (R : Type u) extends AddMonoid R
class SubNegMonoid (A : Type u) extends AddMonoid A, Neg A
class AddGroup (A : Type u) extends SubNegMonoid A where
  add_left_neg (a : A) : -a + a = 0

class Ring (R : Type u) extends Semiring R, AddGroup R

#print Ring.mk
