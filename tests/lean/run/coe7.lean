import logic

variable nat : Type.{1}
variable int : Type.{1}
variable of_nat : nat → int
coercion of_nat

theorem tst (n : nat) : n = n :=
have H : true, from trivial,
calc n    = n : refl _
      ... = n : refl _