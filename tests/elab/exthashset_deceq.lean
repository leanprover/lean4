import Std.Data.ExtHashSet
open Std

@[ext]
structure A where
  a : Nat
  b : Nat
deriving Hashable

instance : BEq A where
  beq x y := x.b == y.b && x.a == y.a

@[simp]
theorem A.beq_eq {x y : A} : (x == y) = (x.b == y.b && x.a == y.a) := rfl

instance : LawfulBEq A where
  rfl {x} := by simp
  eq_of_beq {x y} := by grind [A.beq_eq, A.ext]

instance : DecidableEq A :=
  fun x y => by simp [A.ext_iff]; infer_instance

example : Decidable (ExtHashSet.ofList [A.mk 1 2] = ExtHashSet.ofList [A.mk 1 2]) := by
  infer_instance
