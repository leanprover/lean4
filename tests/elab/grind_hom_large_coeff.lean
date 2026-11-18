/-!
The `[grind hom]` injection of `UIntN`/`BitVec` into `Nat` turns a product by a numeral
`c ≥ 2^(w-1)` (e.g. `-1 * a`, whose literal is `2^w - 1`) into `c * a.toNat % 2^w`, where
`cutsat` has to split on the coefficient `c` to eliminate `a.toNat`. The builtin simproc
`mulLargeCoeffSimproc` rewrites it to `(2^w - (2^w - c) * a.toNat % 2^w) % 2^w`, the image of
`-((2^w - c) * a)`, so these goals do not depend on how the coefficient was written. Before,
the examples with `-1 * a` and `4294967295 * a` reached the `liaSteps` limit.
-/
set_option backward.grind.normalizer false

example (a b c : UInt32) : a ≤ 2 → b ≤ 3 → -1 * a + -1 * b + c = 0 → c ≤ 5 := by grind
example (a b c : UInt32) : a ≤ 2 → b ≤ 3 → 4294967295 * a + 4294967295 * b + c = 0 → c ≤ 5 := by grind
example (a b c : UInt32) : a ≤ 2 → b ≤ 3 → a * 4294967295 + b * 4294967295 + c = 0 → c ≤ 5 := by grind
example (a b c : UInt64) : a ≤ 2 → b ≤ 3 → 18446744073709551615 * a + 18446744073709551615 * b + c = 0 → c ≤ 5 := by grind
example (a b c : UInt32) : a ≤ 2 → b ≤ 3 → -2 * a + -1 * b + c = 0 → c ≤ 7 := by grind
example (a b : UInt8) : a ≤ 2 → 255 * a = b → b = 0 ∨ b = 255 ∨ b = 254 := by grind
example (a b : BitVec 16) : a ≤ 2 → 65535 * a = b → b = 0 ∨ b = 65535 ∨ b = 65534 := by grind
-- coefficient at most half the modulus is left alone
example (a b : UInt8) : a ≤ 1 → 128 * a = b → b = 0 ∨ b = 128 := by grind

set_option backward.grind.normalizer true

example (a b c : UInt32) : a ≤ 2 → b ≤ 3 → -1 * a + -1 * b + c = 0 → c ≤ 5 := by grind
example (a b c : UInt32) : a ≤ 2 → b ≤ 3 → 4294967295 * a + 4294967295 * b + c = 0 → c ≤ 5 := by grind
example (a b c : UInt32) : a ≤ 2 → b ≤ 3 → a * 4294967295 + b * 4294967295 + c = 0 → c ≤ 5 := by grind
example (a b c : UInt64) : a ≤ 2 → b ≤ 3 → 18446744073709551615 * a + 18446744073709551615 * b + c = 0 → c ≤ 5 := by grind
example (a b c : UInt32) : a ≤ 2 → b ≤ 3 → -2 * a + -1 * b + c = 0 → c ≤ 7 := by grind
example (a b : UInt8) : a ≤ 2 → 255 * a = b → b = 0 ∨ b = 255 ∨ b = 254 := by grind
example (a b : BitVec 16) : a ≤ 2 → 65535 * a = b → b = 0 ∨ b = 65535 ∨ b = 65534 := by grind
-- coefficient at most half the modulus is left alone
example (a b : UInt8) : a ≤ 1 → 128 * a = b → b = 0 ∨ b = 128 := by grind
