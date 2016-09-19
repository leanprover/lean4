set_option new_elaborator true
constant g : nat → nat

noncomputable definition f := g

example : f = g := rfl

attribute f [irreducible]

example : f = g := rfl  -- Error

example (a : nat) (H : a = g a) : f a = a :=
eq.subst H rfl -- Error

attribute f [semireducible]

example (a : nat) (H : a = g a) : f a = a :=
eq.subst H rfl -- Error

example : f = g := rfl

attribute f [reducible]

example : f = g := rfl

example (a : nat) (H : a = g a) : f a = a :=
@@eq.subst (λ x, f a = x) (eq.symm H) (eq.refl (f a))
