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
end int

namespace int_coercions
  attribute int.of_nat [coercion]
end int_coercions

-- Open "only" the notation and declarations from the namespaces nat and int
open nat
open int

constants n m : nat
constants i j : int
check n + m
check i + j

section
  -- Temporarily use the int_coercions
  open int_coercions
  check n + i
end

-- The following one is an error
-- check n + i
