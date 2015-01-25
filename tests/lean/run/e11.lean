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

section
  -- Open "only" the notation and declarations from the namespaces nat and int
  open [notations] nat
  open [notations] int
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
