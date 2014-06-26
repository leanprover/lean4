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

variables n m : nat.nat
variables i j : int.int

section
  using [notation] nat
  using [notation] int
  using [decls] nat
  using [decls] int
  check n+m
  check i+j
  --  check i+n -- Error
end

namespace int
  using [decls] nat (nat)
  -- Here is a possible trick for this kind of configuration
  definition add_ni (a : nat) (b : int) := (of_nat a) + b
  definition add_in (a : int) (b : nat) := a + (of_nat b)
  infixl + := add_ni
  infixl + := add_in
end

section
  using [notation] nat
  using [notation] int
  using [declarations] nat
  using [declarations] int
  check n+m
  check i+n
  check n+i
end

section
  using nat
  using int
  check n+m
  check i+n
end