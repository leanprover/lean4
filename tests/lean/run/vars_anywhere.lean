variable {A : Type}

#check @id

inductive List
| nil : List
| cons : A → List → List

#check @List.cons
