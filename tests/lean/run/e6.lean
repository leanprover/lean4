prelude
precedence `+`:65

namespace nat
  constant nat : Type.{1}
  constant add : nat → nat → nat
  infixl + := add
end nat

namespace int
  open nat (nat)
  constant int : Type.{1}
  constant add : int → int → int
  infixl + := add
  constant of_nat : nat → int
  attribute of_nat [coercion]
end int

open int
open nat

constants n m : nat
constants i j : int

check n + m
check i + j
check i + n
check i + n + n + n + n + n + n + n + n + n + n + n +
      n + n + n + n + n + n + n + n + n + n + n + n +
      n + n + n + n + n + n + n + n + n + n + n + n +
      n + n + n + n + n + n + n + n + n + n + n + n
