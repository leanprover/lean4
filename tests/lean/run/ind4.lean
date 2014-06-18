section
  parameter A : Type
  inductive list : Type :=
  | nil  : list
  | cons : A → list → list
end

check list.{1}
check cons.{1}

section
  parameter A : Type
  inductive tree : Type :=
  | node : A → forest → tree
  with forest : Type :=
  | fnil  : forest
  | fcons : tree → forest → forest
  check tree
  check forest
end

check tree.{1}
check forest.{1}