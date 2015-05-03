import logic

theorem tst1 (a b c : Prop) : a → b → a ∧ b :=
begin
  intros,
  apply and.intro,
  repeat assumption
end

theorem tst2 (a b c : Prop) : a → b → a ∧ b :=
by intros; apply and.intro; repeat assumption
