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

open nat
open int

constants n m : nat
constants i j : int

-- 'Most recent' are always tried first
print raw i + n
-- So, in the following one int.add is tried first, and we
-- get int.add (int.of_nat n) (int.of_nat m)
check n + m

print ">>> Forcing nat notation"
-- Force natural numbers
check #nat n + m

-- Moving 'nat' to the 'front'
print ">>> Moving nat notation to the 'front'"
open nat
print raw i + n
check n + m
