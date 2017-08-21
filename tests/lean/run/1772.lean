example (p : Prop) (f : ∀ q : Prop, q → q) : p = p :=
by apply f _ _; refl

example (p : Prop) (f : ∀ q : Prop, q → q) : p = p :=
by apply f _ _; transitivity; refl

example (p r : Prop) (f : ∀ q : Prop, (r = q → q) → q) (h2 : r): p :=
by apply f _ (λ h, _); subst h; assumption
