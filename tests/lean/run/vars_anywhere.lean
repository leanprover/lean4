variable {A : Type}

definition id (a : A) := a

check @id

inductive list :=
| nil : list
| cons : A → list → list

check @list.cons
