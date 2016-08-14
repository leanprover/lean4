set_option new_elaborator true

section
  parameter (A : Type)

  definition f : A → A :=
  λ x, x

  check f
  check f (0:nat) -- error

  parameter {A}

  definition g : A → A :=
  λ x, x

  check g
  check g (0:nat) -- error
end

check f
check f _ (0:nat)
check g 0
