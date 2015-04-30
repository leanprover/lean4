import data.nat
open nat

example (x y : nat) : x + y + y ≥ 0 :=
begin
  generalize x + y + y as n,
  state,
  intro n, exact zero_le n
end
