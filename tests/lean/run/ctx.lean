import data.nat logic.classes.inhabited
open nat inhabited

variable N : Type.{1}
variable a : N

section s1
  set_option pp.implicit true

  definition f (a b : nat) := a

  theorem nat_inhabited [instance] : inhabited nat :=
  inhabited.mk zero

  definition to_N [coercion] (n : nat) : N := a

  infixl `$$`:65 := f
end s1

theorem tst : inhabited nat
variables n m : nat
check n = a
