class Semigroup (M : Type u) extends Mul M where
  mul_assoc (a b c : M) : (a * b) * c = a * (b * c)
export Semigroup (mul_assoc)

class CommSemigroup (M : Type u) extends Semigroup M where
  mul_comm (a b : M) : a * b = b * a
export CommSemigroup (mul_comm)

class Monoid (M : Type u) extends Semigroup M, OfNat M 1 where
  mul_one (m : M) : m * 1 = m
  one_mul (m : M) : 1 * m = m

class CommMonoid (M : Type u) extends Monoid M, CommSemigroup M

theorem mul_left_comm {M} [CommSemigroup M] (a b c : M) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]

example {M} [CommMonoid M] (a b c d : M) : a * (b * (c * d)) = (a * c) * (b * d) := by
  simp only [mul_left_comm, mul_comm, mul_assoc]

example {M} [CommMonoid M] (a b c d : M) : (b * (c * d)) = (c) * (b * d) := by
  simp only [mul_left_comm, mul_comm, mul_assoc]
