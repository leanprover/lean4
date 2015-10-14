import data.nat
open nat algebra

example (a b : nat) : a = b → 0 + a = 0 + b :=
begin
  rewrite zero_add at {2} -- Should fail since nothing is rewritten
end
