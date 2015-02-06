open nat

definition foo [irreducible] (x : nat) := x + 1

example (a b : nat) (H : foo a = b) : a + 1 = b :=
begin
  rewrite ↓foo a,
  exact H
end
