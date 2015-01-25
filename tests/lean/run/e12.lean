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

constants n m : nat.nat
constants i j : int.int

section
  open [notations] nat
  open [notations] int
  open [decls] nat
  open [decls] int
  check n+m
  check i+j
  --  check i+n -- Error
end

namespace int
  open [decls] nat (nat)
  -- Here is a possible trick for this kind of configuration
  definition add_ni (a : nat) (b : int) := (of_nat a) + b
  definition add_in (a : int) (b : nat) := a + (of_nat b)
  infixl + := add_ni
  infixl + := add_in
end int

section
  open [notations] nat
  open [notations] int
  open [declarations] nat
  open [declarations] int
  check n+m
  check i+n
  check n+i
end

section
  open nat
  open int
  check n+m
  check i+n
end
