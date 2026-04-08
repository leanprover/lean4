axiom f {α : Type} : List α → List α

theorem t (a : α) (as : List α) : f (a :: as) = as :=
  sorry

theorem tt {a : α} {as : List α} : f (a :: as) = as :=
  by simp [t _ as]
