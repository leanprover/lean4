example (a b : nat) (h : a = b) : (λ x, x) a = b :=
begin
  simp,
  exact h
end

example (a b : nat) (h : a = b) : (λ x, x) a = b :=
begin
  fail_if_success {simp {beta := ff}},
  exact h
end
