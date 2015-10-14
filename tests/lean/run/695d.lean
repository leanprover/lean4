import data.nat
open nat

example (a b : nat) : 0 + a + 0 = a :=
begin
  rewrite [nat.add_zero, nat.zero_add,]
end
