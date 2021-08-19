class Semigroup (G : Type u) extends Mul G

class Numeric (α : Type u)

class Monoid (M : Type u) extends Semigroup M, Numeric M where
  mul_one (m : M) : m * m = m

class AddMonoid (A : Type u) extends Numeric A

class Semiring (R : Type u) extends AddMonoid R, Monoid R
