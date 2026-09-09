module

import Lean.Util.TestExtern
import Init.Data.UInt.Modular

/-!
Tests that the native modular `UInt64` operations agree with their Lean reference implementations.
-/

test_extern UInt64.mulMod 0 0 0
test_extern UInt64.mulMod 18446744073709551615 18446744073709551615 0
test_extern UInt64.mulMod 18446744073709551615 18446744073709551615 1
test_extern UInt64.mulMod 18446744073709551615 18446744073709551615 18446744073709551557
test_extern UInt64.mulMod 1311768467463790320 1147797409030816545 18446744073709551557

test_extern UInt64.powMod 3 0 5
test_extern UInt64.powMod 3 4 5
test_extern UInt64.powMod 18446744073709551615 18446744073709551616 1
test_extern UInt64.powMod 2 10 1000
test_extern UInt64.powMod 18446744073709551615 3 0
test_extern UInt64.powMod 1311768467463790320 123456789 18446744073709551557
test_extern UInt64.powMod 3 18446744073709551616 97
test_extern UInt64.powMod 3 18446744073709563961 18446744073709551557

test_extern UInt64.invMod? 3 11
test_extern UInt64.invMod? 1 0
test_extern UInt64.invMod? 6 15
test_extern UInt64.invMod? 0 1
test_extern UInt64.invMod? 0 7
test_extern UInt64.invMod? 18446744073709551614 18446744073709551615
test_extern UInt64.invMod? 2 18446744073709551615
test_extern UInt64.invMod? 1311768467463790320 18446744073709551557

#guard UInt64.mulMod 18446744073709551615 18446744073709551615 18446744073709551557 == 3364
#guard UInt64.powMod 3 18446744073709551616 97 == 61
#guard UInt64.invMod? 3 11 == some 4
#guard UInt64.invMod? 6 15 == none
#guard UInt64.invMod? 1 0 == none
