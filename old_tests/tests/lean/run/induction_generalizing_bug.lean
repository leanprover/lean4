open nat

example (n : nat) (h : n > 0) : succ n > 0 ∧ n = n :=
begin
  split,
  induction n generalizing h,
  all_goals { admit },
end
