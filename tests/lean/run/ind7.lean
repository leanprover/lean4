namespace list
  inductive list (A : Type) : Type
  | nil  : list
  | cons : A → list → list

  check list.{1}
  check list.cons.{1}
  check list.rec.{1 1}
end list

check list.list.{1}
