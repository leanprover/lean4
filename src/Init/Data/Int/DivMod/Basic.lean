/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
prelude
import Init.Data.Int.Basic

open Nat

namespace Int

/-! ## Quotient and remainder

There are three main conventions for integer division,
referred here as the E, F, T rounding conventions.
All three pairs satisfy the identity `x % y + (x / y) * y = x` unconditionally,
and satisfy `x / 0 = 0` and `x % 0 = x`.

### Historical notes
In early versions of Lean, the typeclasses provided by `/` and `%`
were defined in terms of `tdiv` and `tmod`, and these were named simply as `div` and `mod`.

However we decided it was better to use `ediv` and `emod` for the default typeclass instances,
as they are consistent with the conventions used in SMTLib, and Mathlib,
and often mathematical reasoning is easier with these conventions.
At that time, we did not rename `div` and `mod` to `tdiv` and `tmod` (along with all their lemma).

In September 2024, we decided to do this rename (with deprecations in place),
and later we intend to rename `ediv` and `emod` to `div` and `mod`, as nearly all users will only
ever need to use these functions and their associated lemmas.

In December 2024, we removed `div` and `mod`, but have not yet renamed `ediv` and `emod`.
-/

/-! ### E-rounding division
This pair satisfies `0 ≤ emod x y < natAbs y` for `y ≠ 0`.
-/

/--
Integer division. This version of integer division uses the E-rounding convention
(euclidean division), in which `Int.emod x y` satisfies `0 ≤ emod x y < natAbs y` for `y ≠ 0`
and `Int.ediv` is the unique function satisfying `emod x y + (ediv x y) * y = x` for `y ≠ 0`.

This means that `Int.ediv x y = floor (x / y)` when `y > 0` and `Int.ediv x y = ceil (x / y)` when `y < 0`.

This is the function powering the `/` notation on integers.

Examples:
```
#eval (7 : Int) / (0 : Int) -- 0
#eval (0 : Int) / (7 : Int) -- 0

#eval (12 : Int) / (6 : Int) -- 2
#eval (12 : Int) / (-6 : Int) -- -2
#eval (-12 : Int) / (6 : Int) -- -2
#eval (-12 : Int) / (-6 : Int) -- 2

#eval (12 : Int) / (7 : Int) -- 1
#eval (12 : Int) / (-7 : Int) -- -1
#eval (-12 : Int) / (7 : Int) -- -2
#eval (-12 : Int) / (-7 : Int) -- 2
```

Implemented by efficient native code.
-/
@[extern "lean_int_ediv"]
def ediv : (@& Int) → (@& Int) → Int
  | ofNat m, ofNat n => ofNat (m / n)
  | ofNat m, -[n+1]  => -ofNat (m / succ n)
  | -[_+1],  0       => 0
  | -[m+1],  ofNat (succ n) => -[m / succ n +1]
  | -[m+1],  -[n+1]  => ofNat (succ (m / succ n))

/--
Integer modulus. This version of integer modulus uses the E-rounding convention
(euclidean division), in which `Int.emod x y` satisfies `0 ≤ emod x y < natAbs y` for `y ≠ 0`
and `Int.ediv` is the unique function satisfying `emod x y + (ediv x y) * y = x`.

This is the function powering the `%` notation on integers.

Examples:
```
#eval (7 : Int) % (0 : Int) -- 7
#eval (0 : Int) % (7 : Int) -- 0

#eval (12 : Int) % (6 : Int) -- 0
#eval (12 : Int) % (-6 : Int) -- 0
#eval (-12 : Int) % (6 : Int) -- 0
#eval (-12 : Int) % (-6 : Int) -- 0

#eval (12 : Int) % (7 : Int) -- 5
#eval (12 : Int) % (-7 : Int) -- 5
#eval (-12 : Int) % (7 : Int) -- 2
#eval (-12 : Int) % (-7 : Int) -- 2
```

Implemented by efficient native code.
-/
@[extern "lean_int_emod"]
def emod : (@& Int) → (@& Int) → Int
  | ofNat m, n => ofNat (m % natAbs n)
  | -[m+1],  n => subNatNat (natAbs n) (succ (m % natAbs n))

/--
The Div and Mod syntax uses ediv and emod for compatibility with SMTLIb and mathematical
reasoning tends to be easier.
-/
instance : Div Int where
  div := Int.ediv
instance : Mod Int where
  mod := Int.emod

@[norm_cast] theorem ofNat_ediv (m n : Nat) : (↑(m / n) : Int) = ↑m / ↑n := rfl

theorem ofNat_ediv_ofNat {a b : Nat} : (↑a / ↑b : Int) = (a / b : Nat) := rfl
@[norm_cast]
theorem negSucc_ediv_ofNat_succ {a b : Nat} : ((-[a+1]) / ↑(b+1) : Int) = -[a / succ b +1] := rfl
theorem negSucc_ediv_negSucc {a b : Nat} : ((-[a+1]) / (-[b+1]) : Int) = ((a / (b + 1)) + 1 : Nat) := rfl
theorem ofNat_ediv_negSucc {a b : Nat} : (ofNat a / (-[b+1])) = -(a / (b + 1) : Nat) := rfl
theorem negSucc_emod_ofNat {a b : Nat} : -[a+1] % (b : Int) = subNatNat b (succ (a % b)) := rfl
theorem negSucc_emod_negSucc {a b : Nat} : -[a+1] % -[b+1] = subNatNat (b + 1) (succ (a % (b + 1))) := rfl

/-! ### T-rounding division -/

/--
`tdiv` uses the [*"T-rounding"*][t-rounding]
(**T**runcation-rounding) convention, meaning that it rounds toward
zero. Also note that division by zero is defined to equal zero.

  The relation between integer division and modulo is found in
  `Int.tmod_add_tdiv` which states that
  `tmod a b + b * (tdiv a b) = a`, unconditionally.

  [t-rounding]: https://dl.acm.org/doi/pdf/10.1145/128861.128862
  [theo tmod_add_tdiv]: https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Int.tmod_add_tdiv#doc

  Examples:

  ```
  #eval (7 : Int).tdiv (0 : Int) -- 0
  #eval (0 : Int).tdiv (7 : Int) -- 0

  #eval (12 : Int).tdiv (6 : Int) -- 2
  #eval (12 : Int).tdiv (-6 : Int) -- -2
  #eval (-12 : Int).tdiv (6 : Int) -- -2
  #eval (-12 : Int).tdiv (-6 : Int) -- 2

  #eval (12 : Int).tdiv (7 : Int) -- 1
  #eval (12 : Int).tdiv (-7 : Int) -- -1
  #eval (-12 : Int).tdiv (7 : Int) -- -1
  #eval (-12 : Int).tdiv (-7 : Int) -- 1
  ```

  Implemented by efficient native code.
-/
@[extern "lean_int_div"]
def tdiv : (@& Int) → (@& Int) → Int
  | ofNat m, ofNat n =>  ofNat (m / n)
  | ofNat m, -[n +1] => -ofNat (m / succ n)
  | -[m +1], ofNat n => -ofNat (succ m / n)
  | -[m +1], -[n +1] =>  ofNat (succ m / succ n)

/-- Integer modulo. This function uses the
  [*"T-rounding"*][t-rounding] (**T**runcation-rounding) convention
  to pair with `Int.tdiv`, meaning that `tmod a b + b * (tdiv a b) = a`
  unconditionally (see [`Int.tmod_add_tdiv`][theo tmod_add_tdiv]). In
  particular, `a % 0 = a`.

  `tmod` satisfies `natAbs (tmod a b) = natAbs a % natAbs b`,
  and when `b` does not divide `a`, `tmod a b` has the same sign as `a`.

  [t-rounding]: https://dl.acm.org/doi/pdf/10.1145/128861.128862
  [theo tmod_add_tdiv]: https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Int.tmod_add_tdiv#doc

  Examples:

  ```
  #eval (7 : Int).tmod (0 : Int) -- 7
  #eval (0 : Int).tmod (7 : Int) -- 0

  #eval (12 : Int).tmod (6 : Int) -- 0
  #eval (12 : Int).tmod (-6 : Int) -- 0
  #eval (-12 : Int).tmod (6 : Int) -- 0
  #eval (-12 : Int).tmod (-6 : Int) -- 0

  #eval (12 : Int).tmod (7 : Int) -- 5
  #eval (12 : Int).tmod (-7 : Int) -- 5
  #eval (-12 : Int).tmod (7 : Int) -- -5
  #eval (-12 : Int).tmod (-7 : Int) -- -5
  ```

  Implemented by efficient native code. -/
@[extern "lean_int_mod"]
def tmod : (@& Int) → (@& Int) → Int
  | ofNat m, ofNat n =>  ofNat (m % n)
  | ofNat m, -[n +1] =>  ofNat (m % succ n)
  | -[m +1], ofNat n => -ofNat (succ m % n)
  | -[m +1], -[n +1] => -ofNat (succ m % succ n)

theorem ofNat_tdiv (m n : Nat) : ↑(m / n) = tdiv ↑m ↑n := rfl

/-! ### F-rounding division
This pair satisfies `fdiv x y = floor (x / y)`.
-/

/--
Integer division. This version of division uses the F-rounding convention
(flooring division), in which `Int.fdiv x y` satisfies `fdiv x y = floor (x / y)`
and `Int.fmod` is the unique function satisfying `fmod x y + (fdiv x y) * y = x`.

Examples:
```
#eval (7 : Int).fdiv (0 : Int) -- 0
#eval (0 : Int).fdiv (7 : Int) -- 0

#eval (12 : Int).fdiv (6 : Int) -- 2
#eval (12 : Int).fdiv (-6 : Int) -- -2
#eval (-12 : Int).fdiv (6 : Int) -- -2
#eval (-12 : Int).fdiv (-6 : Int) -- 2

#eval (12 : Int).fdiv (7 : Int) -- 1
#eval (12 : Int).fdiv (-7 : Int) -- -2
#eval (-12 : Int).fdiv (7 : Int) -- -2
#eval (-12 : Int).fdiv (-7 : Int) -- 1
```
-/
def fdiv : Int → Int → Int
  | 0,       _       => 0
  | ofNat m, ofNat n => ofNat (m / n)
  | ofNat (succ m), -[n+1] => -[m / succ n +1]
  | -[_+1],  0       => 0
  | -[m+1],  ofNat (succ n) => -[m / succ n +1]
  | -[m+1],  -[n+1]  => ofNat (succ m / succ n)

/--
Integer modulus. This version of integer modulus uses the F-rounding convention
(flooring division), in which `Int.fdiv x y` satisfies `fdiv x y = floor (x / y)`
and `Int.fmod` is the unique function satisfying `fmod x y + (fdiv x y) * y = x`.

Examples:

```
#eval (7 : Int).fmod (0 : Int) -- 7
#eval (0 : Int).fmod (7 : Int) -- 0

#eval (12 : Int).fmod (6 : Int) -- 0
#eval (12 : Int).fmod (-6 : Int) -- 0
#eval (-12 : Int).fmod (6 : Int) -- 0
#eval (-12 : Int).fmod (-6 : Int) -- 0

#eval (12 : Int).fmod (7 : Int) -- 5
#eval (12 : Int).fmod (-7 : Int) -- -2
#eval (-12 : Int).fmod (7 : Int) -- 2
#eval (-12 : Int).fmod (-7 : Int) -- -5
```
-/
def fmod : Int → Int → Int
  | 0,       _       => 0
  | ofNat m, ofNat n => ofNat (m % n)
  | ofNat (succ m),  -[n+1]  => subNatNat (m % succ n) n
  | -[m+1],  ofNat n => subNatNat n (succ (m % n))
  | -[m+1],  -[n+1]  => -ofNat (succ m % succ n)

theorem ofNat_fdiv : ∀ m n : Nat, ↑(m / n) = fdiv ↑m ↑n
  | 0, _ => by simp [fdiv]
  | succ _, _ => rfl

/-!
# `bmod` ("balanced" mod)

Balanced mod (and balanced div) are a division and modulus pair such
that `b * (Int.bdiv a b) + Int.bmod a b = a` and
`-b/2 ≤ Int.bmod a b < b/2` for all `a : Int` and `b > 0`.

Note that unlike `emod`, `fmod`, and `tmod`,
`bmod` takes a natural number as the second argument, rather than an integer.

This function is used in `omega` as well as signed bitvectors.
-/

/--
Balanced modulus.  This version of integer modulus uses the
balanced rounding convention, which guarantees that
`-m/2 ≤ bmod x m < m/2` for `m ≠ 0` and `bmod x m` is congruent
to `x` modulo `m`.

If `m = 0`, then `bmod x m = x`.

Examples:
```
#eval (7 : Int).bdiv 0 -- 0
#eval (0 : Int).bdiv 7 -- 0

#eval (12 : Int).bdiv 6 -- 2
#eval (12 : Int).bdiv 7 -- 2
#eval (12 : Int).bdiv 8 -- 2
#eval (12 : Int).bdiv 9 -- 1

#eval (-12 : Int).bdiv 6 -- -2
#eval (-12 : Int).bdiv 7 -- -2
#eval (-12 : Int).bdiv 8 -- -1
#eval (-12 : Int).bdiv 9 -- -1
```
-/
def bmod (x : Int) (m : Nat) : Int :=
  let r := x % m
  if r < (m + 1) / 2 then
    r
  else
    r - m

/--
Balanced division.  This returns the unique integer so that
`b * (Int.bdiv a b) + Int.bmod a b = a`.

Examples:
```
#eval (7 : Int).bmod 0 -- 7
#eval (0 : Int).bmod 7 -- 0

#eval (12 : Int).bmod 6 -- 0
#eval (12 : Int).bmod 7 -- -2
#eval (12 : Int).bmod 8 -- -4
#eval (12 : Int).bmod 9 -- 3

#eval (-12 : Int).bmod 6 -- 0
#eval (-12 : Int).bmod 7 -- 2
#eval (-12 : Int).bmod 8 -- -4
#eval (-12 : Int).bmod 9 -- -3
```
-/
def bdiv (x : Int) (m : Nat) : Int :=
  if m = 0 then
    0
  else
    let q := x / m
    let r := x % m
    if r < (m + 1) / 2 then
      q
    else
      q + 1

end Int
