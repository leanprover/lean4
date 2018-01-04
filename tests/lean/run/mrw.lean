example (n : nat) : ∃ x, x + n = n + 1 :=
begin
  constructor,
  fail_if_success {rw [zero_add] {unify := ff}},
  rw [add_comm]
end
