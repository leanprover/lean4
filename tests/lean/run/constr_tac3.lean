open nat

example (n m : ℕ) (H : n < m) : n < succ m :=
begin
  constructor,
  exact H
end
