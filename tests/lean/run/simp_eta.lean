example (f g : nat → nat) (h : f = g) : (λ x, f x) = g :=
begin
  simp,
  guard_target f = g,
  exact h
end

example (f g : nat → nat) (h : f = g) : (λ x, f x) = g :=
begin
  fail_if_success {simp {eta := ff}},
  exact h
end
