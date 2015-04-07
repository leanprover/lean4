import logic

example {A : Type} (f : A → A) (a b : A) : f a = b → f (f a) = f b :=
begin
  intro fa_eq_b,
  refine (congr_arg f _),
  exact fa_eq_b
end
