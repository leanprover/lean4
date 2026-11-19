import Lean.Util.TestExtern

/-!
Cross-checks the native `@[extern]` implementations of the integer
operations against their Lean reference implementations, using `test_extern`.

Existing tests (`sint_div_overflow.lean`, `sint-abs.lean`, `bitwise.lean`,
`307.lean`, ...) check these corners against hand-written literals; here we
instead tie native ↔ reference together with no expected values, so a
divergence introduced on either side is caught automatically.

Some references are not reachable through `test_extern` and are noted inline:
`Nat.mod`/`Nat.modCore` and `Nat.log2` do not survive the code generator,
`Nat.div` with a large quotient exhausts the stack, and `String.push`/
`String.extract` route through noncomputable or proof-carrying definitions.
-/

/-! ## Signed fixed-width integers: the classic C-undefined-behavior corners. -/

-- INT_MIN / -1 and INT_MIN % -1 (would SIGFPE on x86_64 without care)
test_extern Int8.div (-128) (-1)
test_extern Int8.mod (-128) (-1)
test_extern Int16.div (-32768) (-1)
test_extern Int16.mod (-32768) (-1)
test_extern Int32.div (-2147483648) (-1)
test_extern Int32.mod (-2147483648) (-1)
test_extern Int64.div (-9223372036854775808) (-1)
test_extern Int64.mod (-9223372036854775808) (-1)
test_extern ISize.div (-9223372036854775808) (-1)
test_extern ISize.mod (-9223372036854775808) (-1)

-- division/modulo by zero: div -> 0, mod -> dividend
test_extern Int8.div (-128) 0
test_extern Int8.mod (-128) 0
test_extern Int8.div 10 0
test_extern Int8.mod 10 0
test_extern Int64.div (-9223372036854775808) 0
test_extern Int64.mod (-9223372036854775808) 0

-- rounding-toward-zero across all four sign combinations
test_extern Int8.div (-10) 3
test_extern Int8.div 10 (-3)
test_extern Int8.mod (-5) 2
test_extern Int8.mod 5 (-2)

-- neg / abs of minValue both wrap back to minValue
test_extern Int8.neg (-128)
test_extern Int8.abs (-128)
test_extern Int16.neg (-32768)
test_extern Int16.abs (-32768)
test_extern Int32.neg (-2147483648)
test_extern Int32.abs (-2147483648)
test_extern Int64.neg (-9223372036854775808)
test_extern Int64.abs (-9223372036854775808)

-- add/sub/mul overflow wraparound
test_extern Int8.add 127 1
test_extern Int8.sub (-128) 1
test_extern Int8.mul 127 127
test_extern Int64.add 9223372036854775807 1

-- shifts: amount is reduced mod width (signed-modular), right shift is arithmetic
test_extern Int8.shiftLeft 1 7
test_extern Int8.shiftLeft 1 8
test_extern Int8.shiftLeft (-1) 100
test_extern Int8.shiftRight (-128) 1
test_extern Int8.shiftRight (-128) 8
test_extern Int64.shiftLeft 1 64
test_extern Int64.shiftRight (-9223372036854775808) 100

-- complement and bitwise
test_extern Int8.complement 0
test_extern Int8.complement (-128)
test_extern Int8.land (-128) 127
test_extern Int8.lor (-1) 0
test_extern Int8.xor (-1) (-1)

-- conversions: sign extension and truncation
test_extern Int8.toInt16 (-128)
test_extern Int8.toInt64 (-1)
test_extern Int16.toInt8 (-32768)
test_extern Int64.toInt8 255
test_extern Int8.toInt (-128)

/-! ## Unsigned fixed-width integers. -/

-- division/modulo by zero
test_extern UInt8.div 10 0
test_extern UInt8.mod 10 0
test_extern UInt64.div 7 0
test_extern UInt64.mod 7 0

-- wraparound and two's-complement negation
test_extern UInt8.add 255 1
test_extern UInt8.sub 0 1
test_extern UInt8.mul 255 255
test_extern UInt8.neg 1
test_extern UInt64.add 18446744073709551615 1
test_extern UInt64.mul 18446744073709551615 18446744073709551615
test_extern UInt64.neg 1

-- shifts: amount reduced mod width
test_extern UInt8.shiftLeft 1 8
test_extern UInt8.shiftLeft 255 100
test_extern UInt8.shiftRight 255 8
test_extern UInt32.shiftLeft 1 32
test_extern UInt64.shiftLeft 1 64
test_extern UInt64.shiftRight 18446744073709551615 64
test_extern USize.shiftLeft 1 64

-- complement and truncating conversions
test_extern UInt8.complement 0
test_extern UInt64.toUInt8 511
test_extern UInt64.toUInt32 4294967296
test_extern UInt32.toUInt8 256

/-! ## Int (arbitrary precision): the four division/modulo families. -/

-- truncating (toward zero)
test_extern Int.tdiv (-7) 2
test_extern Int.tdiv 7 (-2)
test_extern Int.tmod (-7) 2
test_extern Int.tmod 7 (-2)
test_extern Int.tdiv 7 0
test_extern Int.tmod 7 0

-- Euclidean (remainder always nonnegative)
test_extern Int.ediv (-7) 2
test_extern Int.ediv 7 (-2)
test_extern Int.emod (-7) 2
test_extern Int.emod 7 (-2)
test_extern Int.ediv 7 0
test_extern Int.emod 7 0

-- big operands across the scalar/GMP boundary (small quotient keeps the
-- reference cheap; a large quotient would exhaust the stack)
test_extern Int.neg (2^63)
test_extern Int.neg (-(2^63))
test_extern Int.mul (-(2^63)) (-1)
test_extern Int.ediv (-(2^63)) (2^62)
test_extern Int.emod (-(2^63)) (2^62)
test_extern Int.tdiv (-(2^63)) (2^62)
test_extern Int.tmod (-(2^64)) (2^63)

/-! ## Nat: the tagged/GMP boundary at 2^63 and 2^64.

Reachable through operations whose reference recursion is bounded by the
operand's bit width (shifts, gcd, pow of a small base) or by a small operand,
rather than by the operand's magnitude. -/

test_extern Nat.add (2^63 - 1) 1
test_extern Nat.add (2^63) (2^63)
test_extern Nat.add (2^64 - 1) 1
test_extern Nat.mul (2^32) (2^32)
test_extern Nat.mul (2^63) 2
test_extern Nat.sub 0 1
test_extern Nat.sub (2^63) (2^63 - 1)
test_extern Nat.sub (2^63 - 1) (2^63)
test_extern Nat.pred (2^64)
test_extern Nat.div 7 0
test_extern Nat.div (2^63) (2^63)
test_extern Nat.pow 2 63
test_extern Nat.pow 2 64
test_extern Nat.pow 0 0
test_extern Nat.gcd (2^63) (2^62)
test_extern Nat.gcd (2^64 - 1) (2^63)
test_extern Nat.beq (2^63) (2^63)
test_extern Nat.ble (2^63 - 1) (2^63)
test_extern Nat.land (2^64 - 1) (2^63)
test_extern Nat.lor (2^63 - 1) (2^63)
test_extern Nat.shiftLeft 1 63
test_extern Nat.shiftLeft 1 64
test_extern Nat.shiftRight (2^64 - 1) 1
