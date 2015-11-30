import data.nat
open algebra nat

section
open nat
set_option blast.simp   false
set_option blast.subst  false
set_option blast.ematch true

attribute add.comm  [forward]
attribute add.assoc [forward]

example (a b c : nat) : a + b + b + c = c + b + a + b :=
by blast

end
