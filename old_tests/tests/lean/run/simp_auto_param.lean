constant f : nat → nat
axiom fax (x : nat) (h : x > 0 . tactic.assumption) : f x = x

example (a : nat) (h : a > 0) : f (f a) = a :=
begin
  simp [fax]
end
