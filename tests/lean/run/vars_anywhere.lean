variable {A : Type}

check @id

inductive list :=
| nil : list
| cons : A → list → list

check @list.cons
