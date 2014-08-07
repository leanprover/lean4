precedence `+`:65

namespace nat
  variable nat : Type.{1}
  variable add : nat → nat → nat
  infixl + := add
end nat

namespace int
  using nat (nat)
  variable int : Type.{1}
  variable add : int → int → int
  infixl + := add
  variable of_nat : nat → int
  namespace coercions
    coercion of_nat
  end coercions
end int

using nat
using int
variables n m : nat
check n+m -- coercion nat -> int is not available
using int.coercions
check n+m -- coercion nat -> int is available

