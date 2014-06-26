precedence `+`:65

namespace nat
  variable nat : Type.{1}
  variable add : nat → nat → nat
  infixl + := add
end

namespace int
  using nat (nat)
  variable int : Type.{1}
  variable add : int → int → int
  infixl + := add
  variable of_nat : nat → int
end

namespace int_coercions
  coercion int.of_nat
end

-- Using "only" the notation and declarations from the namespaces nat and int
using nat
using int

variables n m : nat
variables i j : int
check n + m
check i + j

section
  -- Temporarily use the int_coercions
  using int_coercions
  check n + i
end

-- The following one is an error
-- check n + i

