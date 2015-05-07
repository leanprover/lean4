open prod
variables {A B C : Type} (f : A → B → C) (a : A) (b b' : B)

example (p : b = b') : prod.cases_on (a, b) f = f a b' :=
begin
  esimp,
  state,
  rewrite p
end
