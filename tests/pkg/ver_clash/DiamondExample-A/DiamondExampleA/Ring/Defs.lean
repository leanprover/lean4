module

public class Ring (A : Type) extends Add A, Mul A, Neg A, Zero A, One A where
  add_assoc : ∀ a b c : A, a + b + c = a + (b + c)
  add_comm : ∀ a b : A, a + b = b + a
  add_zero : ∀ a : A, a + 0 = a
  add_neg : ∀ a : A, a + -a = 0
  mul_assoc : ∀ a b c : A, a * b * c = a * (b * c)
  mul_comm : ∀ a b : A, a * b = b * a
