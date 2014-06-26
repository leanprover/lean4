
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

using int
using nat

variables n m : nat
variables i j : int

check n + m
check i + j
check i + n
check i + n + n + n + n + n + n + n + n + n + n + n +
      n + n + n + n + n + n + n + n + n + n + n + n +
      n + n + n + n + n + n + n + n + n + n + n + n +
      n + n + n + n + n + n + n + n + n + n + n + n


