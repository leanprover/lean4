inductive list (T : Type) : Type :=
| nil {} : list T
| cons : T → list T → list T


section
  variable {T : Type}

  definition concat (s t : list T) : list T
  := list.rec t (fun x l u, list.cons x u) s

  attribute concat [reducible]
end
