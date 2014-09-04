import logic

theorem symm2 {A : Type} {a b : A} (H : a = b) : b = a
:= subst H (eq.refl a)
