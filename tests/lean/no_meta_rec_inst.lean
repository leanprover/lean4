class has_false (α : Type) :=
(f : false)

meta def n_has_false : has_false ℕ :=
by apply_instance -- Error, the "recursive" instance (n_has_false : has_false ℕ) should not be used in type class resolution
