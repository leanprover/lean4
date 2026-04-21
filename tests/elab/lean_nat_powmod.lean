import Lean

/-! Basic tests, including edge cases. -/
example : Nat.powMod 0 0 1  = 0  := rfl
example : Nat.powMod 0 1 5  = 0  := rfl
example : Nat.powMod 1 0 5  = 1  := rfl
example : Nat.powMod 1 17 5 = 1  := rfl
example : Nat.powMod 2 10 1 = 0  := rfl
example : Nat.powMod 2 10 3 = 1  := rfl
example : Nat.powMod 3 4 5   = 1  := rfl
example : Nat.powMod 7 5 13  = 11 := rfl

/-!
The kernel can only evaluate `Nat.powMod` for small inputs (it unfolds to
`b ^ e % m` and relies on the kernel's bignum override of `Nat.pow`).
Larger inputs are tested via `#eval` below, which uses the `lean_nat_powmod`
extern.
-/


/-! `m = 0` follows `_ % 0 = _`, so `powMod b e 0 = b ^ e`. -/
example : Nat.powMod 2 10 0 = 1024 := rfl
example : Nat.powMod 3 4 0  = 81   := rfl

/-! `b = 0` with positive exponent is `0 % m`. -/
example : Nat.powMod 0 5 7 = 0 := rfl

/-! `e = 0` is `1 % m`. -/
example : Nat.powMod 100 0 7 = 1 := rfl
example : Nat.powMod 100 0 1 = 0 := rfl

abbrev hugeExp : Nat := 4294967296

-- Regression test: the runtime override must stay total for `m = 0`,
-- even when the exponent exceeds `UINT_MAX`.
#eval Nat.powMod 1 hugeExp 0 = 1
#eval Nat.powMod 0 hugeExp 0 = 0
example : Nat.powMod 1 hugeExp 0 = 1 := by native_decide
example : Nat.powMod 0 hugeExp 0 = 0 := by native_decide

/-!
Cross-check the compiled extern against the kernel's unfolding for
inputs that exercise bignum arithmetic on both sides. A divergence here
would make `native_decide` unsound.
-/
-- Fermat's little theorem on a small prime: `3^100 ≡ 1 (mod 101)`.
example : Nat.powMod 3 100 101 = 1 := by native_decide
example : Nat.powMod 3 100 101 = 1 := by decide
-- Bignum base and modulus with a small exponent, so `decide` stays
-- within the default exponentiation threshold.
set_option exponentiation.threshold 400 in
example :
    Nat.powMod 1234567890123456789 5 (2^63 - 1) = 3256532376055551519 := by native_decide
set_option exponentiation.threshold 400 in
example :
    Nat.powMod 1234567890123456789 5 (2^63 - 1) = 3256532376055551519 := by decide

/-!
Large modular exponentiation (1024-bit prime), motivated by Mathlib's ZMod test.
Prior to adding `lean_nat_powmod`, `Nat.powMod` would unfold to `b ^ e % m`
which fails to terminate for this size of exponent.
-/
open Lean Elab Command in
elab "#fast" c:command : command => do
  let start ← IO.monoMsNow
  elabCommand c
  let elapsed := (← IO.monoMsNow) - start
  if elapsed > 1000 then throwError m!"Too slow! {elapsed}ms"

abbrev M : Nat := 0xb10b8f96a080e01dde92de5eae5d54ec52c99fbcfb06a3c69a6a9dca52d23b616073e28675a23d189838ef1e2ee652c013ecb4aea906112324975c3cd49b83bfaccbdd7d90c4bd7098488e9c219a73724effd6fae5644738faa31a4ff55bccc0a151af5f0dc8b4bd45bf37df365c1a65e68cfda76d4da708df1fb2bc2e4a4371

abbrev g : Nat := 0xa4d1cbd5c3fd34126765a442efb99905f8104dd258ac507fd6406cff14266d31266fea1e5c41564b777e690f5504f213160217b4b01b886a5e91547f9e2749f4d7fbd7d3b9a92ee1909d0d2263f80a76a6a24c087a091f531dbf0a0169b6a28ad662a4d18e73afa32d779d5918d08bc8858f4dcef97c2a24855e6eeb22b3b2e5

-- Fermat's little theorem: if M is prime, `g^(M-1) ≡ 1 (mod M)`.
#fast #eval Nat.powMod g (M - 1) M = 1

-- And via `Fin`, which is the main motivating use case.
#fast #eval ((Fin.ofNat _ g : Fin M) ^ (M - 1) = 1 : Bool)
example : ((Fin.ofNat _ g : Fin M) ^ (M - 1)) = 1 := by native_decide
