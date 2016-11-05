section
  universe variables u
  variable {A : Type u}

  example [add_semigroup A] (a : A) : a + a = a + a := rfl
  example [add_comm_semigroup A] (a : A) : a + a = a + a := rfl
end

section
  variable {A : Type}

  example [add_semigroup A] (a : A) : a + a = a + a := rfl
  example [add_comm_semigroup A] (a : A) : a + a = a + a := rfl
end
