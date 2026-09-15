module

import Lean.Util.TestExtern

/-! Numeric smoke tests for bignum results and heap-to-scalar normalization. -/

test_extern Int.add (2 ^ 128) (2 ^ 128 + 1)
test_extern Int.sub (-(2 ^ 128)) (2 ^ 128 + 1)
test_extern Int.add (2 ^ 128) (-(2 ^ 128))
test_extern Int.sub (2 ^ 128) (2 ^ 128 + 1)

test_extern Nat.sub (2 ^ 128 + 1) 3
test_extern Nat.div (3 * 2 ^ 128 + 7) (2 ^ 128 + 3)
