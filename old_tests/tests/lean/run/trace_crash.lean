constant f : nat → nat → nat
constant fax1 : ∀ x, f x x = f x 0
constant fax2 : ∀ x, f x 0 = x

set_option trace.type_context.is_def_eq true

example (a : nat) : f a a = a :=
by simp [fax1, fax2]
