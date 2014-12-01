import data.nat
open nat inhabited

constant N : Type.{1}
constant a : N

section s1
  set_option pp.implicit true

  definition f (a b : nat) := a

  theorem nat_inhabited [instance] : inhabited nat :=
  inhabited.mk zero

  definition to_N [coercion] (n : nat) : N := a

  infixl `$$`:65 := f
end s1

theorem tst : inhabited nat
constants n m : nat
check n = a
