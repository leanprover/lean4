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
  coercion of_nat
end int

section
  -- Open "only" the notation and declarations from the namespaces nat and int
  open [notation] nat
  open [notation] int
  open [decls] nat
  open [decls] int

  variables n m : nat
  variables i j : int
  check n + m
  check i + j

  -- The following check does not work, since we are not open the coercions
  -- check n + i

  -- Here is a possible trick for this kind of configuration
  definition add_ni (a : nat) (b : int) := (of_nat a) + b
  definition add_in (a : int) (b : nat) := a + (of_nat b)
  infixl + := add_ni
  infixl + := add_in
  check add_ni

  check i + n
  check n + i
end
