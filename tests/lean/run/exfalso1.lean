open nat

example (a b : nat) : a = 0 → b = 1 → a = b → a + b * b ≤ 10000 :=
begin
  intro a0 b1 ab,
  exfalso, state,
  rewrite [a0 at ab, b1 at ab],
  contradiction
end
