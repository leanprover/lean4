inductive List (T : Type) : Type :=
| nil {} : List T
| cons : T → List T → List T


section
  variable {T : Type}

  definition concat (s t : List T) : List T
  := List.rec t (fun x l u, List.cons x u) s

  attribute concat [reducible]
end
