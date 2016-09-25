constant g : nat → nat

noncomputable definition f := g

example : f = g := rfl

attribute [irreducible] f

example : f = g := rfl  -- Error

example (a : nat) (H : a = g a) : f a = a :=
eq.subst H rfl -- Error

attribute [semireducible] f

example (a : nat) (H : a = g a) : f a = a :=
eq.subst H rfl -- Error

example : f = g := rfl

attribute [reducible] f

example : f = g := rfl

example (a : nat) (H : a = g a) : f a = a :=
@@eq.subst (λ x, f a = x) (eq.symm H) (eq.refl (f a))
