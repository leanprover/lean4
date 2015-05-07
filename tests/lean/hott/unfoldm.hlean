definition rr [constructor] {A : Type} {a : A} := eq.refl a

constants f g : Π {A : Type}, A → A

example (A : Type) (a b : A) (C : A → Type) (H : C a) (f g : C a → C a) : f = g → f (eq.rec H rr) = g H :=
begin
  intros,
  esimp,
  state,
  congruence,
  assumption
end

example (A : Type) (a b : A) (C : A → Type) (H : C a) (f g : C a → C a) : f = g → f (eq.rec_on rr H) = g H :=
begin
  intros,
  esimp,
  state,
  congruence,
  assumption
end
