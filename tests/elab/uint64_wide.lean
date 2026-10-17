module

import Lean.Util.TestExtern

/-!
Tests the wide `UInt64` operations: `mulHi` against its Lean reference implementation, and the
pair-returning operations (compiled via `csimp` to their wrapping-arithmetic implementations)
against the corresponding `Nat` arithmetic and against the reference definitions by `decide`.
-/

test_extern UInt64.mulHi 0 0
test_extern UInt64.mulHi 1 18446744073709551615
test_extern UInt64.mulHi 4294967296 4294967296
test_extern UInt64.mulHi 9223372036854775808 2
test_extern UInt64.mulHi 18446744073709551615 18446744073709551615
test_extern UInt64.mulHi 1311768467463790320 1147797409030816545

def checkMulFull (a b : UInt64) : Bool :=
  let (lo, hi) := UInt64.mulFull a b
  lo.toNat + hi.toNat * UInt64.size == a.toNat * b.toNat

#guard checkMulFull 0 18446744073709551615
#guard checkMulFull 18446744073709551615 18446744073709551615
#guard checkMulFull 1311768467463790320 1147797409030816545
#guard UInt64.mulFull 4294967296 4294967296 == (0, 1)
example : UInt64.mulFull 4294967296 4294967296 = (0, 1) := by decide

def checkAddCarry (a b : UInt64) (carry : Bool) : Bool :=
  let (sum, c) := UInt64.addCarry a b carry
  sum.toNat + c.toNat * UInt64.size == a.toNat + b.toNat + carry.toNat

#guard checkAddCarry 0 0 false
#guard checkAddCarry 18446744073709551615 0 true
#guard checkAddCarry 18446744073709551615 18446744073709551615 true
#guard checkAddCarry 1311768467463790320 1147797409030816545 false
#guard UInt64.addCarry 18446744073709551615 0 true == (0, true)
#guard UInt64.addCarry 0 0 true == (1, false)
#guard UInt64.addCarry 18446744073709551615 1 false == (0, true)
#guard UInt64.addCarry 18446744073709551615 18446744073709551615 true == (18446744073709551615, true)
example : UInt64.addCarry 18446744073709551615 0 true = (0, true) := by decide

def checkSubBorrow (a b : UInt64) (borrow : Bool) : Bool :=
  let (diff, c) := UInt64.subBorrow a b borrow
  a.toNat + c.toNat * UInt64.size == diff.toNat + b.toNat + borrow.toNat

#guard checkSubBorrow 0 0 false
#guard checkSubBorrow 0 0 true
#guard checkSubBorrow 0 18446744073709551615 true
#guard checkSubBorrow 1311768467463790320 1147797409030816545 false
#guard UInt64.subBorrow 0 0 true == (18446744073709551615, true)
#guard UInt64.subBorrow 1 0 true == (0, false)
#guard UInt64.subBorrow 0 1 false == (18446744073709551615, true)
#guard UInt64.subBorrow 1 1 false == (0, false)
#guard UInt64.subBorrow 0 18446744073709551615 true == (0, true)
example : UInt64.subBorrow 0 0 true = (18446744073709551615, true) := by decide
