open nat

example (a b : nat) (Ha : a = 0) (Hb : b = 0) : a + b = 0 :=
begin
  rewrite [Ha, Ha]
end

example (a : nat) : a = a :=
begin
  esimp,
  esimp
end
