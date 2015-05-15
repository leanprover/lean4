import logic

example (a b : Prop) : a ∧ b → b ∧ a :=
begin
  intros, rewrite and.comm, assumption
end

example (a b c : Prop) : a ∧ b ∧ c → b ∧ a ∧ c :=
begin
  intros, rewrite [-and.assoc, {b ∧ a}and.comm, and.assoc], assumption
end
