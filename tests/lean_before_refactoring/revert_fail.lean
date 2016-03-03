import data.examples.vector

example (A : Type) (n : nat) (v : vector A n) : v = v :=
begin
  revert n
end

example (n : nat) : n = n :=
begin
  esimp,
  revert n
end

example (n : nat) : n = n :=
begin
  revert m
end
