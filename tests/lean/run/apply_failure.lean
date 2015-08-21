example (a b c : Prop) : a ∧ b → b ∧ a :=
begin
  intro H,
  repeat (apply or.elim H | apply and.elim H | intro H | split | assumption)
end
