open nat

example (n m : ℕ) (H : n < m) : n < succ m :=
begin
  constructor 2,
  exact H
end
