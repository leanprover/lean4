import data.vector namespace test
universes u v

section
  open vector
  variable  α : Type u
  variables m n k : ℕ
  variable  v : vector α m
  variable  w : vector α n

  theorem append_nil : append v nil = v :=
  by cases v; simp [vector.append, vector.nil]; reflexivity
end
end test
