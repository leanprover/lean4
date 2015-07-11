open nat

definition f (a n : ℕ) : ℕ := nat.rec_on n (λa', a') (λn' f' a', f' (a' * 2)) a

example (a n : nat) : a = 2 → f a (succ n) = f 4 n :=
begin
  unfold f at {1},
  state,
  intros, subst a
end
