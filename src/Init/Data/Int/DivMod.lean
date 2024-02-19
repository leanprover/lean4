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
-/

/-! ### T-rounding division -/

/--
`div` uses the [*"T-rounding"*][t-rounding]
(**T**runcation-rounding) convention, meaning that it rounds toward
zero. Also note that division by zero is defined to equal zero.

  The relation between integer division and modulo is found in
  `Int.mod_add_div` which states that
  `a % b + b * (a / b) = a`, unconditionally.

  [t-rounding]: https://dl.acm.org/doi/pdf/10.1145/128861.128862 [theo
  mod_add_div]:
  https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Int.mod_add_div#doc

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
  #eval (-12 : Int) / (7 : Int) -- -1
  #eval (-12 : Int) / (-7 : Int) -- 1
  ```

  Implemented by efficient native code.
-/
@[extern "lean_int_div"]
def div : (@& Int) → (@& Int) → Int
  | ofNat m, ofNat n =>  ofNat (m / n)
  | ofNat m, -[n +1] => -ofNat (m / succ n)
  | -[m +1], ofNat n => -ofNat (succ m / n)
  | -[m +1], -[n +1] =>  ofNat (succ m / succ n)

/-- Integer modulo. This function uses the
  [*"T-rounding"*][t-rounding] (**T**runcation-rounding) convention
  to pair with `Int.div`, meaning that `a % b + b * (a / b) = a`
  unconditionally (see [`Int.mod_add_div`][theo mod_add_div]). In
  particular, `a % 0 = a`.

  [t-rounding]: https://dl.acm.org/doi/pdf/10.1145/128861.128862
  [theo mod_add_div]: https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Int.mod_add_div#doc

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

  Implemented by efficient native code. -/
@[extern "lean_int_mod"]
def mod : (@& Int) → (@& Int) → Int
  | ofNat m, ofNat n =>  ofNat (m % n)
  | ofNat m, -[n +1] =>  ofNat (m % succ n)
  | -[m +1], ofNat n => -ofNat (succ m % n)
  | -[m +1], -[n +1] => -ofNat (succ m % succ n)

/-! ### F-rounding division
This pair satisfies `fdiv x y = floor (x / y)`.
-/

/--
Integer division. This version of division uses the F-rounding convention
(flooring division), in which `Int.fdiv x y` satisfies `fdiv x y = floor (x / y)`
and `Int.fmod` is the unique function satisfying `fmod x y + (fdiv x y) * y = x`.
-/
def fdiv : Int → Int → Int
  | 0,       _       => 0
  | ofNat m, ofNat n => ofNat (m / n)
  | ofNat (succ m), -[n+1] => -[m / succ n +1]
  | -[_+1],  0       => 0
  | -[m+1],  ofNat (succ n) => -[m / succ n +1]
  | -[m+1],  -[n+1]  => ofNat (succ m / succ n)

/--
Integer modulus. This version of `Int.mod` uses the F-rounding convention
(flooring division), in which `Int.fdiv x y` satisfies `fdiv x y = floor (x / y)`
and `Int.fmod` is the unique function satisfying `fmod x y + (fdiv x y) * y = x`.
-/
def fmod : Int → Int → Int
  | 0,       _       => 0
  | ofNat m, ofNat n => ofNat (m % n)
  | ofNat (succ m),  -[n+1]  => subNatNat (m % succ n) n
  | -[m+1],  ofNat n => subNatNat n (succ (m % n))
  | -[m+1],  -[n+1]  => -ofNat (succ m % succ n)

/-! ### E-rounding division
This pair satisfies `0 ≤ mod x y < natAbs y` for `y ≠ 0`.
-/

/--
Integer division. This version of `Int.div` uses the E-rounding convention
(euclidean division), in which `Int.emod x y` satisfies `0 ≤ mod x y < natAbs y` for `y ≠ 0`
and `Int.ediv` is the unique function satisfying `emod x y + (ediv x y) * y = x`.
-/
def ediv : Int → Int → Int
  | ofNat m, ofNat n => ofNat (m / n)
  | ofNat m, -[n+1]  => -ofNat (m / succ n)
  | -[_+1],  0       => 0
  | -[m+1],  ofNat (succ n) => -[m / succ n +1]
  | -[m+1],  -[n+1]  => ofNat (succ (m / succ n))

/--
Integer modulus. This version of `Int.mod` uses the E-rounding convention
(euclidean division), in which `Int.emod x y` satisfies `0 ≤ emod x y < natAbs y` for `y ≠ 0`
and `Int.ediv` is the unique function satisfying `emod x y + (ediv x y) * y = x`.
-/
def emod : Int → Int → Int
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

end Int
