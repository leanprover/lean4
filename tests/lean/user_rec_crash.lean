example (a b : Prop) (h : a ∧ b) : a :=
begin
  induction h using and.rec_on with h₁ h₂,
end
