/-!
Boundary cases of the runtime's arbitrary-precision `Nat` and `Int` primitives. They target code
paths of the built-in bignum implementation (`src/runtime/mpz.cpp`) that Lean uses when built with
`-DUSE_GMP=OFF`; GMP builds run the same checks through the GMP-backed implementation.

The wrappers are `@[noinline]` so that each primitive is applied to runtime values.
-/

@[noinline] def natPow (b e : Nat) : Nat := b ^ e
@[noinline] def intNeg (a : Int) : Int := -a
@[noinline] def intAdd (a b : Int) : Int := a + b
@[noinline] def intSub (a b : Int) : Int := a - b
@[noinline] def intMul (a b : Int) : Int := a * b
@[noinline] def intTDiv (a b : Int) : Int := a.tdiv b
@[noinline] def intEDiv (a b : Int) : Int := a / b
@[noinline] def intTMod (a b : Int) : Int := a.tmod b
@[noinline] def usizeOfNat (n : Nat) : USize := USize.ofNat n

/-! `Nat.pow` accepts exponents up to `2 ^ 32 - 1`. Bases `0` and `1` keep the result small even
for exponents that do not fit in 31 bits. -/
#guard natPow 1 (2 ^ 31) = 1
#guard natPow 1 (2 ^ 31 + 1) = 1
#guard natPow 1 (2 ^ 32 - 1) = 1
#guard natPow 0 (2 ^ 31) = 0
#guard natPow 0 (2 ^ 32 - 1) = 0

/-! `Nat.pow` agrees with repeated multiplication, for exponents around powers of two and for
bases spanning one or more 32-bit digits. -/
#guard Id.run do
  let bases := [0, 1, 2, 3, 10, 2 ^ 31, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 32 + 1, 2 ^ 64 - 1, 2 ^ 64 + 1, 3 ^ 50]
  let exps := List.range 70 ++ (List.range 12).flatMap fun k => [2 ^ (k + 1) - 1, 2 ^ (k + 1), 2 ^ (k + 1) + 1]
  bases.all fun b => exps.all fun e => natPow b e == Nat.repeat (· * b) e 1

/-! Operations on big `Int`s whose result is `-2 ^ 31`, the smallest unboxed `Int` on 64-bit
platforms, and neighbouring results. -/
#guard toString (intNeg (2 ^ 31)) == "-2147483648"
#guard toString (intAdd (-(2 ^ 31) - 1) 1) == "-2147483648"
#guard toString (intSub (2 ^ 31) (2 ^ 32)) == "-2147483648"
#guard toString (intMul (2 ^ 31) (-1)) == "-2147483648"
#guard toString (intTDiv (-(2 ^ 32)) 2) == "-2147483648"
#guard toString (intEDiv (-(2 ^ 32)) 2) == "-2147483648"
#guard toString (intTMod (-(2 ^ 32) - 2 ^ 31) (2 ^ 32)) == "-2147483648"
#guard toString (intAdd (-(2 ^ 31) - 2) 1) == "-2147483649"
#guard toString (intAdd (2 ^ 31) (-1)) == "2147483647"

/-! `USize.ofNat` wraps around for `Nat`s that do not fit in a machine word. The inputs are
multiples of `2 ^ 64` plus an offset, so the expected values hold on 32- and 64-bit platforms. -/
#guard usizeOfNat (2 ^ 64) = 0
#guard usizeOfNat (2 ^ 64 + 5) = 5
#guard usizeOfNat (3 * 2 ^ 64 + 7) = 7
#guard usizeOfNat (2 ^ 128 + 2 ^ 64 + 9) = 9
#guard usizeOfNat (2 ^ 64 - 1) = 0 - 1
#guard usizeOfNat (2 ^ 128 - 1) = 0 - 1
