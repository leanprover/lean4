import Lean

/-! Basic tests, including edge cases. -/
example : Nat.gcd 0  0  = 0  := rfl
example : Nat.gcd 0  1  = 1  := rfl
example : Nat.gcd 0  17 = 17 := rfl
example : Nat.gcd 1  0  = 1  := rfl
example : Nat.gcd 17 0  = 17 := rfl
example : Nat.gcd 1  1  = 1  := rfl
example : Nat.gcd 1  17 = 1  := rfl
example : Nat.gcd 17 1  = 1  := rfl
example : Nat.gcd 2  2  = 2  := rfl
example : Nat.gcd 2  3  = 1  := rfl
example : Nat.gcd 2  4  = 2  := rfl
example : Nat.gcd 9  6  = 3  := rfl

/-!
We check that `Nat.gcd` is evaluated using bignum functions in the kernel.

Because of variations in run time on different operating systems during CI,
for the larger calculations we don't attempt to do any timing.

All of the "large" calculations below used to fail with
```
maximum recursion depth has been reached (use `set_option maxRecDepth <num>` to increase limit)
```
prior to lean4#2533.
-/

open Lean Elab Command in
elab "#fast" c:command : command => do
  let start ← IO.monoMsNow
  elabCommand c
  let elapsed := (← IO.monoMsNow) - start
  if elapsed > 1000 then throwError m!"Too slow! {elapsed}ms"

-- Used to take ~1500ms, now takes ~3ms.
#fast example : Nat.gcd 45 (Nat.gcd 15 85) = 5 := rfl

example : Nat.gcd (115249 * 180811) (115249*181081) = 115249 := rfl

/-- Mersenne primes. -/
def m (p : Nat) := 2^p - 1

/-- Largish primes, targeting <100ms GCD calculations. -/
def p_29 := 110503
def p_30 := 132049
def p_31 := 216091
def p_32 := 756839
def p_33 := 859433

/- GCD with large prime factors on one side, and small primes on the other. -/
example : Nat.gcd (p_29 * p_30 * p_31 * p_32 * p_33) 2^(2^20) = 1 := rfl
/- GCD with two prime factors on both sides, including one in common. -/
example : Nat.gcd (m p_31 * m p_33) (m p_32 * m p_33) - m p_33 = 0 := rfl
/- GCD with many small prime factors. -/
example :
    Nat.gcd (2^1 * 3^1 * 5^2 * 7^3 * 11^5 * 13^8) (2^8 * 3^5 * 5^3 * 7^2 * 11^1 * 13^1) =
      2 * 3 * 5^2 * 7^2 * 11 * 13 := rfl

-- #eval Lean.maxSmallNat -- 9223372036854775807
def maxSmallNat := 9223372036854775807

example : maxSmallNat = 7^2 * 73 * 127 * 337 * 92737 * 649657 := rfl
-- Calculate GCDs of numbers on either side of `maxSmallNat`.
example : Nat.gcd (maxSmallNat - 92737) (maxSmallNat + 92737) = 185474 := rfl
example : Nat.gcd (maxSmallNat / 649657) (maxSmallNat * 649657) = 14197294936951 := rfl
