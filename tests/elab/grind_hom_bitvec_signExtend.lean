/-!
Tests for the `BitVec.toInt_signExtend` homomorphism rule in `grind`: the signed value of
`x.signExtend v` is `x.toInt.bmod (2 ^ min v w)`, so narrowing reduces modulo `2 ^ v` and
widening is the identity on `toInt`.
-/

example (x : BitVec 16) : (x.signExtend 32).toInt = x.toInt := by grind

example (x : BitVec 16) : (x.signExtend 8).toInt = x.toInt.bmod (2 ^ 8) := by grind

example (x : BitVec 16) : (x.signExtend 8).toInt < 128 := by grind

example (x : BitVec 16) : -128 ≤ (x.signExtend 8).toInt := by grind

example (x : BitVec 16) (v : Nat) (h : v ≤ 16) : (x.signExtend v).toInt = x.toInt.bmod (2 ^ v) := by grind

example (x : BitVec 16) (v : Nat) (h : 16 ≤ v) : (x.signExtend v).toInt = x.toInt := by grind

example (x : BitVec 16) (v : Nat) : (x.signExtend v).toInt = x.toInt.bmod (2 ^ min v 16) := by grind
