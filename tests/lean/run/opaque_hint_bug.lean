inductive List (T : Type) : Type
| nil {} : List
| cons : T → List → List


section
  variable {T : Type}

  definition concat (s t : List T) : List T
  := List.rec t (fun x l u, List.cons x u) s

  attribute [reducible] concat
end
