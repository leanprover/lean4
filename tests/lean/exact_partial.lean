example (a b : Prop) : a → b → a ∧ b :=
begin
  intros,
  exact (and.intro _ _),
end
