import data.list data.examples.vector
open list vector nat

variables (A : Type) (a b c : A)

check [a, b, c]
check (#list [a, b, c])
check (#vector [a, b, c])
check ([a, b, c] : vector A _)
check ([a, b, c] : list A)
