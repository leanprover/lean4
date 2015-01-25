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
  namespace coercions
attribute of_nat [coercion]
  end coercions
end int

open nat
open int
constants n m : nat
check n+m -- coercion nat -> int is not available
open int.coercions
check n+m -- coercion nat -> int is available
