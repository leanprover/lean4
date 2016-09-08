section
  parameter (A : Type)
  definition foo := A
  noncomputable definition bar {X : Type} {A : X} : foo :=
  sorry
end
