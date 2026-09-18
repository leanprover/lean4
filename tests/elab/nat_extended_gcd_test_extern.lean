module

import Init.Data.Nat.ExtendedGcd
import Lean.Util.TestExtern

/-!
Tests exact agreement of `Nat.extendedGcd`'s extern and Lean reference implementation, including
zero and equal inputs, half-size coefficient ties, scalar/bignum boundaries, signed coefficients,
and long Euclidean chains. Retained inputs also exercise the extern's borrowed-input ABI.
-/

test_extern Nat.extendedGcd 0 0
test_extern Nat.extendedGcd 0 19
test_extern Nat.extendedGcd 19 0
test_extern Nat.extendedGcd 19 19
test_extern Nat.extendedGcd 240 46
test_extern Nat.extendedGcd 46 240
test_extern Nat.extendedGcd 2 5
test_extern Nat.extendedGcd 5 2
test_extern Nat.extendedGcd 2 (2 ^ 32 - 1)
test_extern Nat.extendedGcd 2 (2 ^ 32 + 1)
test_extern Nat.extendedGcd 2 (2 ^ 32 + 3)
test_extern Nat.extendedGcd (2 ^ 64) (2 ^ 64)
test_extern Nat.extendedGcd 0 (2 ^ 128)
test_extern Nat.extendedGcd (2 ^ 128) 0
test_extern Nat.extendedGcd (2 ^ 64) (2 ^ 64 + 1)
test_extern Nat.extendedGcd (2 ^ 128 + 1) (2 ^ 64)
test_extern Nat.extendedGcd 65537 (2 ^ 128 + 1)
test_extern Nat.extendedGcd (2 ^ 128 + 1) 65537
-- A half-size tie after the initial zero quotient, with both operands heap-allocated.
test_extern Nat.extendedGcd ((2 ^ 128 + 1) * 2 ^ 64) (2 ^ 65)
test_extern Nat.extendedGcd (2 ^ 65) ((2 ^ 128 + 1) * 2 ^ 64)

private def reference (a b : Nat) : Nat.ExtendedGcdResult :=
  Nat.extendedGcd.go a 1 0 b 0 1

private def agrees (a b : Nat) : Bool :=
  decide (Nat.extendedGcd a b = reference a b)

#guard (List.range 129).all fun a => (List.range 129).all fun b => agrees a b

private def values : List Nat :=
  [0, 1, 2, 3, 6, 15, 46, 97, 240, 65535, 65536, 65537,
    2 ^ 31 - 1, 2 ^ 31, 2 ^ 31 + 1, 2 ^ 31 + 3,
    2 ^ 32 - 1, 2 ^ 32, 2 ^ 32 + 1, 2 ^ 32 + 3,
    2 ^ 63 - 1, 2 ^ 63, 2 ^ 63 + 1, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 1,
    2 ^ 128 - 1, 2 ^ 128, 2 ^ 128 + 1, 2 ^ 256 - 1, 2 ^ 256 + 1]

#guard values.all fun a => values.all fun b => agrees a b

-- Scaling preserves the exceptional cases while forcing bignum operands and gcds.
#guard [1, 2 ^ 64, 2 ^ 128].all fun g =>
  (List.range 33).all fun a => (List.range 33).all fun b => agrees (a * g) (b * g)

private def fibPair (n : Nat) : Nat × Nat :=
  match n with
  | 0 => (0, 1)
  | n + 1 => let (a, b) := fibPair n; (b, a + b)

#guard [100, 256, 512, 1024].all fun n =>
  let (a, b) := fibPair n
  agrees a b && agrees b a

-- All three result fields require heap allocation in these examples.
#guard [256, 512].all fun n =>
  let (a, b) := fibPair n
  agrees (a * 2 ^ 128) (b * 2 ^ 128) && agrees (b * 2 ^ 128) (a * 2 ^ 128)

-- The operands remain live after the call, including when the gcd aliases an input.
#guard values.all fun a => values.all fun b =>
  let r := Nat.extendedGcd a b
  r.gcd == Nat.gcd a b && decide ((r.gcd : Int) = a * r.coeffA + b * r.coeffB)
