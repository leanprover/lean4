import logic

set_option pp.notation false
set_option pp.implicit true

theorem tst (A B : Type) (a : A) (b : B) : a == b → b == a :=
begin
  intro H,
  generalize B, -- Should produce an error
  intro B',
  apply (heq.symm H),
end

theorem tst2 (A B : Type) (a : A) (b : B) : a == b → b == a :=
begin
  generalize a,
  generalize b,
  generalize B,
  intro B',
  intro b,
  intro a,
  intro H,
  apply (heq.symm H),
end
