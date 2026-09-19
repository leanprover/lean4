/-!
This test checks that `DecidableEq` actually *just* works when the inductive type has
non-injective indices.
-/

opaque f : Nat → Nat

inductive T : (n : Nat) → Type where
  | mk1 : Fin n → T (f n)
  | mk2 : Fin (2*n) → T (f n)
deriving BEq, DecidableEq, LawfulBEq, Ord, Std.LawfulEqOrd
