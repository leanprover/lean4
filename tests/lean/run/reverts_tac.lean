import logic

theorem tst {a b c : Prop} : a → b → c → a ∧ b :=
begin
  intros [Ha, Hb, Hc],
  reverts [Hb, Ha],
  intros [Hb2, Ha2],
  apply (and.intro Ha2 Hb2),
end

theorem foo1 {A : Type} (a b c : A) (P : A → Prop) : P a → a = b → P b :=
begin
  intros  [Hp, Heq],
  reverts [Heq, Hp],
  intro Heq,
  eapply (eq.rec_on Heq),
  intro Pa,
  apply Pa
end

theorem foo2 {A : Type} (a b c : A) (P : A → Prop) : P a → a = b → P b :=
begin
  intros [Hp, Heq],
  apply (eq.rec_on Heq Hp)
end

reveal foo1 foo2
print definition foo1
print definition foo2
