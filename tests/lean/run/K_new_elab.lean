set_option new_elaborator true

theorem ex2 {A : Type} (H : A = A) (a : A) : cast H a = a :=
rfl
