open eq

example (A : Type) (C : A → Type) (a : A) (f g : C a → C a) (c : C a) : f = g → f (eq.rec_on idp c) = g c :=
begin
  intros,
  esimp,
  state, -- simplified goal to f c = g c
  congruence,
  assumption
end
