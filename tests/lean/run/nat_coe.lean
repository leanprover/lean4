import logic
namespace experiment
constant nat : Type.{1}
constant int : Type.{1}

constant nat_add : nat → nat → nat
infixl `+` := nat_add

constant int_add : int → int → int
infixl `+` := int_add

constant of_nat : nat → int
attribute of_nat [coercion]

constants a b : nat
constants i j : int

definition c1 := a + b

theorem T1 : c1 = nat_add a b :=
eq.refl _

definition c2 := i + j

theorem T2 : c2 = int_add i j :=
eq.refl _
exit
