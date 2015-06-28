import data.nat
open nat

example (a b : nat) : 0 + a + 0 = a :=
begin
  rewrite [add_zero, zero_add,]
end
