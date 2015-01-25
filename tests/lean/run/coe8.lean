import logic
namespace experiment
constant nat : Type.{1}
constant int : Type.{1}
constant of_nat : nat → int
attribute of_nat [coercion]
constant nat_add : nat → nat → nat
constant int_add : int → int → int
infixl `+` := int_add
infixl `+` := nat_add

print "================"
constant tst (n m : nat) : @eq int (of_nat n + of_nat m) (n + m)

check tst
exit
