/-!
Tests for `Nat.powMod` (GMP-backed modular exponentiation from
`Init.Data.Nat.PowMod`): the square-and-multiply kernel model (`decide`/`rfl`),
the `lean_nat_powmod` extern (`#guard`/`native_decide`), edge cases, and the
1024-bit ZMod case from Mathlib that motivated the feature.
-/

/-! Basic values and edge cases. `powMod b e m = b ^ e % m`, and `n % 0 = n`. -/
example : Nat.powMod 0 0 1   = 0    := rfl
example : Nat.powMod 0 5 7    = 0    := rfl  -- `b = 0`, positive exponent
example : Nat.powMod 1 0 5    = 1    := rfl  -- `e = 0`
example : Nat.powMod 1 17 5   = 1    := rfl
example : Nat.powMod 2 10 1   = 0    := rfl  -- `m = 1`
example : Nat.powMod 100 0 1  = 0    := rfl  -- `e = 0` and `m = 1`
example : Nat.powMod 2 10 3   = 1    := rfl
example : Nat.powMod 3 4 5    = 1    := rfl
example : Nat.powMod 7 5 13   = 11   := rfl
example : Nat.powMod 3 4 0    = 81   := rfl  -- `m = 0` behaves like `^`
example : Nat.powMod 2 10 0   = 1024 := rfl

/-! The runtime override stays total for `m = 0` even when the exponent exceeds
`UINT_MAX` (`2 ^ 32`). -/
#guard Nat.powMod 1 (2 ^ 32) 0 = 1
#guard Nat.powMod 0 (2 ^ 32) 0 = 0

/-! Kernel reduction (`decide`) and the compiled extern (`native_decide`) must
agree, cross-validating the square-and-multiply model against `mpz_powm`. A
divergence here would make `native_decide` unsound. -/
-- Fermat's little theorem on a small prime: `3 ^ 100 ≡ 1 (mod 101)`.
example : Nat.powMod 3 100 101 = 1 := by decide
example : Nat.powMod 3 100 101 = 1 := by native_decide
-- A large exponent with a small base: square-and-multiply never materializes the
-- astronomically large `b ^ e`, so `decide` succeeds where `b ^ e % m` could not.
example : Nat.powMod 3 1000 1000003 = 73216 := by decide
example : Nat.powMod 3 1000 1000003 = 73216 := by native_decide

/-! `decide` of `Nat.powMod` is efficient even for very large exponents: the
square-and-multiply model reduces in `O(log e)` steps and never materializes
`b ^ e`, which the naive `b ^ e % m` model could never `decide`. -/
example : Nat.powMod 7 65537 1000003 = 881993 := by decide
-- `b ^ (2 ^ 40)` and `b ^ (10 ^ 12)` are astronomically large.
example : Nat.powMod 3 (2 ^ 40) 1000003 = 378344 := by decide
example : Nat.powMod 3 (10 ^ 12) 1000003 = 81 := by decide
-- The reduction is `O(log e)` deep, so cryptographic-scale exponents need
-- `maxRecDepth` raised; no exponentiation algorithm is shallower than `log₂ e`.
-- The `maxHeartbeats` bound (heartbeats are deterministic, unlike wall-clock
-- time) is a regression guard: a fallback to the naive `b ^ e % m` model would
-- blow far past it.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000 in
example : Nat.powMod 2 (2 ^ 200) 1000000007 = 988385428 := by decide

/-! Large modular exponentiation (1024-bit prime), motivated by Mathlib's ZMod
test. With the naive `b ^ e % m` model this exponent never terminates; the extern
runs it in milliseconds. -/
abbrev M : Nat := 0xb10b8f96a080e01dde92de5eae5d54ec52c99fbcfb06a3c69a6a9dca52d23b616073e28675a23d189838ef1e2ee652c013ecb4aea906112324975c3cd49b83bfaccbdd7d90c4bd7098488e9c219a73724effd6fae5644738faa31a4ff55bccc0a151af5f0dc8b4bd45bf37df365c1a65e68cfda76d4da708df1fb2bc2e4a4371

abbrev g : Nat := 0xa4d1cbd5c3fd34126765a442efb99905f8104dd258ac507fd6406cff14266d31266fea1e5c41564b777e690f5504f213160217b4b01b886a5e91547f9e2749f4d7fbd7d3b9a92ee1909d0d2263f80a76a6a24c087a091f531dbf0a0169b6a28ad662a4d18e73afa32d779d5918d08bc8858f4dcef97c2a24855e6eeb22b3b2e5

-- Fermat's little theorem: if `M` is prime, `g ^ (M - 1) ≡ 1 (mod M)`.
#guard Nat.powMod g (M - 1) M = 1
-- And via `Fin`, the main motivating use case.
#guard ((Fin.ofNat _ g : Fin M) ^ (M - 1) = 1 : Bool)
