module

import Lean.Util.TestExtern

/-!
Tests that the native wide `UInt64` operations agree with their Lean reference implementations.
-/

test_extern UInt64.mulHi 0 0
test_extern UInt64.mulHi 1 18446744073709551615
test_extern UInt64.mulHi 4294967296 4294967296
test_extern UInt64.mulHi 9223372036854775808 2
test_extern UInt64.mulHi 18446744073709551615 18446744073709551615
test_extern UInt64.mulHi 1311768467463790320 1147797409030816545

test_extern UInt64.mulFull 0 18446744073709551615
test_extern UInt64.mulFull 18446744073709551615 18446744073709551615
test_extern UInt64.mulFull 1311768467463790320 1147797409030816545

test_extern UInt64.addCarry 0 0 false
test_extern UInt64.addCarry 18446744073709551615 0 true
test_extern UInt64.addCarry 18446744073709551615 18446744073709551615 true
test_extern UInt64.addCarry 1311768467463790320 1147797409030816545 false

test_extern UInt64.subBorrow 0 0 false
test_extern UInt64.subBorrow 0 0 true
test_extern UInt64.subBorrow 0 18446744073709551615 true
test_extern UInt64.subBorrow 1311768467463790320 1147797409030816545 false
