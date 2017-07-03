namespace test
universes u v

def vector (α : Type u) (n : ℕ) := { l : list α // list.length l = n }

namespace vector
  open subtype list
  variable {α : Type u}

  def nil : vector α 0 := ⟨[], rfl⟩

  def append {m n : ℕ} : vector α m → vector α n → vector α (m + n)
  | ⟨v, _⟩ ⟨w, _⟩ := ⟨v ++ w, by abstract {simp [*]}⟩

end vector

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
