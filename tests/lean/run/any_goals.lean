constant f : nat → nat
axiom fax : ∀ x, f x = x

example (a b c : nat) : b = c → f a = a ∧ c = b :=
begin
  intros,
  constructor,
  any_goals {rw fax},
  {symmetry, assumption}
end
