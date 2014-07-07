
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

section
  using nat
  using int

  variables n m : nat
  variables i j : int

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
  using nat
  print raw i + n
  check n + m
end


variables a b : nat.nat
check #nat a + b
