import logic

variable nat : Type.{1}
variable int : Type.{1}

variable nat_add : nat → nat → nat
infixl `+`:65 := nat_add

variable int_add : int → int → int
infixl `+`:65 := int_add

variable of_nat : nat → int
coercion of_nat

variables a b : nat
variables i j : int

abbreviation c1 := a + b

theorem T1 : c1 = nat_add a b :=
eq.refl _

abbreviation c2 := i + j

theorem T2 : c2 = int_add i j :=
eq.refl _
