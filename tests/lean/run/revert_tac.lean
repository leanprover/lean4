import logic

theorem tst {a b c : Prop} : a → b → c → a ∧ b :=
begin
  intros [Ha, Hb, Hc],
  revert Ha,
  intro Ha2,
  apply (and.intro Ha2 Hb),
end

theorem foo1 {A : Type} (a b c : A) (P : A → Prop) : P a → a = b → P b :=
begin
  intros [Hp, Heq],
  revert Hp,
  apply (eq.rec_on Heq),
  intro Hpa,
  apply Hpa
end

theorem foo2 {A : Type} (a b c : A) (P : A → Prop) : P a → a = b → P b :=
begin
  intros [Hp, Heq],
  apply (eq.rec_on Heq Hp)
end

print definition foo1
print definition foo2
