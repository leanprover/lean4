example (a b : Prop) : a → b → a ∧ b :=
begin
  intros [Ha, Hb],
  refine (and.intro _ Hb),
  exact Ha
end
