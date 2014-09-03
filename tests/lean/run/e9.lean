precedence `+`:65

namespace nat
  variable nat : Type.{1}
  variable add : nat → nat → nat
  infixl + := add
end nat

namespace int
  open nat (nat)
  variable int : Type.{1}
  variable add : int → int → int
  infixl + := add
  variable of_nat : nat → int
end int

namespace int_coercions
  coercion int.of_nat
end int_coercions

-- Open "only" the notation and declarations from the namespaces nat and int
open nat
open int

variables n m : nat
variables i j : int
check n + m
check i + j

section
  -- Temporarily use the int_coercions
  open int_coercions
  check n + i
end

-- The following one is an error
-- check n + i
