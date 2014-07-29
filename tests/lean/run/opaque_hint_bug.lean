

inductive list (T : Type) : Type :=
| nil {} : list T
| cons : T → list T → list T


section
  variable {T : Type}

  definition concat (s t : list T) : list T
  := list_rec t (fun x l u, cons x u) s

  opaque_hint (hiding concat)

end