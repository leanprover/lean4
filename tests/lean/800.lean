import data.matrix data.list
open matrix nat list

variables {A : Type} {m n : nat}

definition row_vector [reducible] (A : Type) (n : nat) := matrix A 1 n
definition get_row [reducible] (M : matrix A m n) (row : fin m) : row_vector A n :=
λ i j, M row j

variables (M : matrix A m n) (row : fin m) (col : fin n)

notation M `[` i `,` j `]` := val M i j
check M[row,col]
notation M `[` i `,` `:` `]` := get_row M i
check M[row,:]
check M[row,col]
check [(1:nat), 2, 3]
