module

import Lean.Util.TestExtern

/-!
Tests the numeric results of move-aware bignum allocation against unfolded Lean definitions, including
positive and negative heap results, cancellation to scalar results, and scalar/bignum boundaries.
-/

test_extern Int.add (2 ^ 128) (2 ^ 128 + 1)
test_extern Int.add (-(2 ^ 128)) (-(2 ^ 128 + 1))
test_extern Int.add (2 ^ 128) (-(2 ^ 128))
test_extern Int.add (2 ^ 128) (-(2 ^ 128 - 1))
test_extern Int.add (2 ^ 31 - 1) 1
test_extern Int.sub (2 ^ 128) (2 ^ 128 + 1)
test_extern Int.sub (-(2 ^ 128)) (2 ^ 128 + 1)
test_extern Int.mul (2 ^ 64 + 1) (-(2 ^ 64 + 3))
test_extern Int.mul (2 ^ 128) 0
test_extern Int.neg (2 ^ 128 + 1)
test_extern Int.neg (-(2 ^ 31))
test_extern Int.tdiv (-(2 ^ 256 + 1)) (2 ^ 64 + 3)
test_extern Int.tmod (-(2 ^ 256 + 1)) (2 ^ 64 + 3)
test_extern Int.ediv (-(2 ^ 256 + 1)) (2 ^ 64 + 3)
test_extern Int.emod (-(2 ^ 256 + 1)) (2 ^ 64 + 3)
test_extern Int.ediv (2 ^ 256 + 1) (-(2 ^ 64 + 3))
test_extern Int.emod (2 ^ 256 + 1) (-(2 ^ 64 + 3))
test_extern Nat.sub (2 ^ 128 + 1) 3
test_extern Nat.sub 3 5
test_extern Nat.mul (2 ^ 63 - 1) 3
test_extern Nat.mul (2 ^ 128 + 1) 3
test_extern Nat.div (3 * 2 ^ 128 + 7) (2 ^ 128 + 3)
test_extern Nat.mod (2 ^ 128 + 1) (2 ^ 128 + 3)
test_extern Nat.land (2 ^ 128 + 3) (2 ^ 128 + 5)
test_extern Nat.lor (2 ^ 128 + 3) (2 ^ 128 + 5)
test_extern Nat.xor (2 ^ 128 + 3) (2 ^ 128 + 5)
test_extern Nat.gcd (3 * 2 ^ 128) (5 * 2 ^ 128)
test_extern Nat.pow (2 ^ 64 + 1) 3
