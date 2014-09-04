import logic

variable nat : Type.{1}
variable int : Type.{1}
variable of_nat : nat → int
coercion of_nat
variable nat_add : nat → nat → nat
variable int_add : int → int → int
infixl `+`:65 := int_add
infixl `+`:65 := nat_add

print "================"
variable tst (n m : nat) : @eq int (of_nat n + of_nat m) (n + m)

check tst
exit
