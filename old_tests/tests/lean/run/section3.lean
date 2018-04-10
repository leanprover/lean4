section
  parameter (A : Type)
  definition foo := A
  definition bar {X : Type} {A : X} : foo :=
  sorry
end
