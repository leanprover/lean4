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

variables n m : nat.nat
variables i j : int.int

section
  open [notation] nat
  open [notation] int
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
  open [notation] nat
  open [notation] int
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
