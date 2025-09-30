/-!
# Issue 4861: slow elaboration of large arithmetic expressions

https://github.com/leanprover/lean4/issues/4861
-/

-- set_option trace.profiler true

/-!
Example from the issue. This used to time out, but now it takes less than 0.25s
-/
set_option maxHeartbeats 10000 in
theorem foo (x y z p q : Int) : False :=
  have : (1 * x ^ 1 + z ^ 1 * p) *
        (1 / 1 * p ^ 1 * x ^ 1 + 1 * q * p ^ 1 * x * z + 1 * q ^ 1 * p ^ 1 * x ^ 1 +
                            1 * q ^ 1 * p ^ 1 * x * z -
                          1 * q * p ^ 1 * y ^ 1 +
                        1 * q ^ 1 * p ^ 1 * x ^ 1 +
                      1 * q ^ 1 * p ^ 1 * x * z -
                    1 * q ^ 1 * p ^ 1 * y ^ 1 +
                  1 * q ^ 1 * p ^ 1 * x ^ 1 +
                1 * q ^ 1 * p ^ 1 * x * z -
              1 * q ^ 1 * p ^ 1 * y ^ 1 +
            1 * q ^ 1 * x ^ 1 -
          1 * q ^ 1 * p * y ^ 1) +
      z * (1 * y) *
        (-(1 / 1 * p ^ 1 * x * y) + 1 * q * p ^ 1 * z * y - 1 * q ^ 1 * p ^ 1 * x * y +
                  1 * q ^ 1 * p ^ 1 * z * y -
                1 * q ^ 1 * p ^ 1 * x * y +
              1 * q ^ 1 * p ^ 1 * z * y -
            1 * q ^ 1 * p ^ 1 * x * y +
          1 / 1 * q ^ 1 * p ^ 1 * z * y) +
    (-y ^ 1 + p * x * (1 * z) + q * (1 * z ^ 1)) *
      (-(1 / 1 * p ^ 1 * x * z) - 1 * q * p ^ 1 * x ^ 1 - 1 * q ^ 1 * p ^ 1 * x * z -
                1 * q ^ 1 * p ^ 1 * x ^ 1 -
              1 * q ^ 1 * p ^ 1 * x * z -
            1 * q ^ 1 * p ^ 1 * x ^ 1 -
          1 * q ^ 1 * p ^ 1 * x * z -
        1 * q ^ 1 * p * x ^ 1) =
  1 *
        (1 / 1 * p ^ 1 * x ^ 1 + 1 * q * p ^ 1 * x * z + 1 * q ^ 1 * p ^ 1 * x ^ 1 +
                            1 * q ^ 1 * p ^ 1 * x * z -
                          1 * q * p ^ 1 * y ^ 1 +
                        1 * q ^ 1 * p ^ 1 * x ^ 1 +
                      1 * q ^ 1 * p ^ 1 * x * z -
                    1 * q ^ 1 * p ^ 1 * y ^ 1 +
                  1 * q ^ 1 * p ^ 1 * x ^ 1 +
                1 * q ^ 1 * p ^ 1 * x * z -
              1 * q ^ 1 * p ^ 1 * y ^ 1 +
            1 * q ^ 1 * x ^ 1 -
          1 * q ^ 1 * p * y ^ 1) +
      1 *
        (-(1 / 1 * p ^ 1 * x * y) + 1 * q * p ^ 1 * z * y - 1 * q ^ 1 * p ^ 1 * x * y +
                  1 * q ^ 1 * p ^ 1 * z * y -
                1 * q ^ 1 * p ^ 1 * x * y +
              1 * q ^ 1 * p ^ 1 * z * y -
            1 * q ^ 1 * p ^ 1 * x * y +
          1 / 1 * q ^ 1 * p ^ 1 * z * y) +
    1 *
      (-(1 / 1 * p ^ 1 * x * z) - 1 * q * p ^ 1 * x ^ 1 - 1 * q ^ 1 * p ^ 1 * x * z -
                1 * q ^ 1 * p ^ 1 * x ^ 1 -
              1 * q ^ 1 * p ^ 1 * x * z -
            1 * q ^ 1 * p ^ 1 * x ^ 1 -
          1 * q ^ 1 * p ^ 1 * x * z -
        1 * q ^ 1 * p * x ^ 1) := sorry
  sorry

/-!
Example from Leo. This used to take 1.7s on my machine, now it takes 0.11s.
-/
set_option maxHeartbeats 5000 in
def foo2 : Type :=
  BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) →
  BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) →
  BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) →
  BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) →
  BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) →
  BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) →
  BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) →
  BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) →
  BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) →
  BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) →
  BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8) → BitVec (2 ^ 3 * 8)

/-!
Example from Leo. This used to take 1.67s on my machine, now it takes 0.12s.
-/
set_option maxHeartbeats 5000 in
def bla : Nat :=
  2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 +
  2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 +
  2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 +
  2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 +
  2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 +
  2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 +
  2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8

/-!
Make sure that the speedup is also observed when in the exponent.
The `n` causes the exponent to infer `Nat` as the max type, otherwise elaboration is still slow (~1.6s).
-/
def bla2 (n : Nat) : Nat :=
  2 ^ (n + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 +
  2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 +
  2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 +
  2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 +
  2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 +
  2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 +
  2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8 + 2 ^ 3 * 8)

/-!
Check that these work with `leftact%` as well. `bla'` has the same profiling speedup as `bla` (~1.7s to ~0.12s).
-/
class HRevPow (α β : Type _) (γ : outParam (Type _)) where
  hRevPow : α → β → γ
infixl:80 " ⩛ " => HRevPow.hRevPow
macro_rules | `($x ⩛ $y)   => `(leftact% HRevPow.hRevPow $x $y)
class RevPow (α β : Type _) where
  revPow : α → β → β
class NatRevPow (α : Type u) where
  protected revPow : Nat → α → α
class HomogeneousRevPow (α : Type u) where
  protected revPow : α → α → α
@[default_instance]
instance [RevPow α β] : HRevPow α β β where
  hRevPow := RevPow.revPow
@[default_instance]
instance [NatRevPow α] : RevPow Nat α where
  revPow := NatRevPow.revPow
@[default_instance]
instance [HomogeneousRevPow α] : RevPow α α where
  revPow := HomogeneousRevPow.revPow

instance : NatRevPow Nat where
  revPow a b := b ^ a

def bla' : Nat :=
  3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 +
  3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 +
  3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 +
  3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 +
  3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 +
  3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 +
  3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8 + 3 ⩛ 2 * 8
