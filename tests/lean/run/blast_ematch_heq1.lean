import data.nat
open algebra nat

section
open nat
set_option blast.strategy "ematch"
set_option blast.cc.heq true

attribute add.comm  [forward]
attribute add.assoc [forward]

example (a b c : nat) : a + b + b + c = c + b + a + b :=
by blast

end
