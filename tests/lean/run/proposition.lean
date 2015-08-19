proposition tst {a b : Prop} : a → b → a ∧ b :=
begin
  intros, split, repeat assumption
end
