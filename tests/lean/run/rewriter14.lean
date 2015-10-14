import data.nat
open nat

definition f [unfold 2] (x y z : nat) : nat :=
x + y + z

attribute of_num [unfold 1]

example (x y : nat) (H1 : f x 0 0 = 0) : x = 0 :=
begin
  rewrite [↑f at H1, 4>nat.add_zero at H1, H1]
end
