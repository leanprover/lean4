class Semiring (R : Type u) extends Add R, HPow R Nat R, Mul R where
  zero : R

instance [Semiring R] : OfNat R n where
  ofNat := Semiring.zero

def Nat.cast [Semiring R] (n : Nat) : R := let _ := n = n; Semiring.zero

@[default_instance high] instance [Semiring R] : HPow R Nat R := inferInstance

instance [Semiring R] : CoeTail Nat R where
  coe n := n.cast

variable (R) [Semiring R]
#check (8 + 2 ^ 2 * 3 : R) = 20
