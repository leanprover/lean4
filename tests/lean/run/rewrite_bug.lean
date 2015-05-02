open nat

example (a b c : nat) : a = 0 → b = 1 + a → a = b → false :=
begin
  intro a0 b1 ab,
  rewrite a0 at *,
  rewrite b1 at *,
  contradiction
end
