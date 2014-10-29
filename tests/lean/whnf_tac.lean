import logic

definition id {A : Type} (a : A) := a

theorem tst (a : Prop) : a → id a :=
begin
  intro Ha,
  whnf,
  state,
  apply Ha
end
