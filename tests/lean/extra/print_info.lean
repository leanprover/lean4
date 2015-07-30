import data.int
open nat int

variables a b : nat
variables i j : int

definition foo := add a i
definition f₁ := a + i

example (n : nat) : n + n = 2 * n :=
begin
  unfold [nat.add,mul],
  apply sorry
end

example (n : nat) : n + n = n + n :=
rfl
