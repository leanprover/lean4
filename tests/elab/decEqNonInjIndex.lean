/-!
This test checks that deriving comparison type classes on a type with non-injective
indices *just* works.
-/

opaque f : Nat → Nat

set_option deriving.comparisons.linear_construction_threshold 0

inductive T : (n : Nat) → Type where
  | mk1 : Fin n → T (f n)
  | mk2 : Fin (2*n) → T (f n)
deriving BEq, Ord, DecidableEq, ReflBEq, LawfulBEq, Std.ReflOrd, Std.LawfulEqOrd

example : (instBEqOfDecidableEq : BEq (T n)) = (inferInstance : BEq (T n)) := by
  with_implicit rfl

set_option deriving.comparisons.linear_construction_threshold 10000

inductive T' : (n : Nat) → Type where
  | mk1 : Fin n → T' (f n)
  | mk2 : Fin (2*n) → T' (f n)
deriving BEq, Ord, DecidableEq, ReflBEq, LawfulBEq, Std.ReflOrd, Std.LawfulEqOrd

example : (instBEqOfDecidableEq : BEq (T' n)) = (inferInstance : BEq (T' n)) := by
  with_implicit rfl
