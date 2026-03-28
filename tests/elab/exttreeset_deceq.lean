import Std.Data.ExtTreeSet

open Std

instance : TransOrd Nat := inferInstance

@[ext]
structure A where
  a : Nat
  b : Nat
deriving Ord

instance : BEq A where
  beq x y := x.b == y.b && x.a == y.a

instance : TransOrd A := sorry

instance : LawfulEqOrd A := sorry

@[simp]
theorem A.beq_eq {x y : A} : (x == y) = (x.b == y.b && x.a == y.a) := rfl

instance : LawfulBEq A where
  rfl {x} := by simp
  eq_of_beq {x y} := by grind [A.beq_eq, A.ext]

example : Decidable (ExtTreeSet.ofList [A.mk 1 2] = ExtTreeSet.ofList [A.mk 1 2]) := by
  infer_instance
