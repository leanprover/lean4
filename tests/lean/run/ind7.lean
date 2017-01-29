namespace list
  inductive {u} list (A : Type u) : Type u
  | nil  : list
  | cons : A → list → list

  check list.{1}
  check list.cons.{1}
  check list.rec.{1 1}
end list

check list.list.{1}
