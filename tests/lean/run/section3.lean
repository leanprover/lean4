section
  parameter (A : Type)
  definition foo := A
  theorem bar {X : Type} {A : X} : foo :=
  sorry
end
