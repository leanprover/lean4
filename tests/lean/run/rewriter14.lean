import data.nat
open nat

definition f [unfold-c 2] (x y z : nat) : nat :=
x + y + z

attribute of_num [unfold-c 1]

example (x y : nat) (H1 : f x 0 0 = 0) : x = 0 :=
begin
  rewrite [▸* at H1, 4>add_zero at H1, H1]
end
