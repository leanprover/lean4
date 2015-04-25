open eq

section
  parameter (A : Type)

  definition foo (a : A) : a = a := refl a

  definition bar (a : A) : foo a = refl a :=
  begin
    unfold foo
  end
end
