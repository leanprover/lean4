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
  coercion of_nat
end

-- Using "only" the notation and declarations from the namespaces nat and int
using [notation] nat
using [notation] int
using [decls] nat
using [decls] int

variables n m : nat
variables i j : int
check n + m
check i + j

-- The following check does not work, since we are not using the coercions
-- check n + i

-- Here is a possible trick for this kind of configuration
definition add_ni (a : nat) (b : int) := (of_nat a) + b
definition add_in (a : int) (b : nat) := a + (of_nat b)
infixl + := add_ni
infixl + := add_in

check i + n
check n + i
