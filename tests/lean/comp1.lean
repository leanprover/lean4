import data.real data.vector data.list
open nat int rat

#compose int.of_nat nat.of_num → num_to_int
#compose int.of_nat nat.of_num → num_to_int_2
set_option pp.all true

print num_to_int

check num_to_int
check num_to_int_2 -- Error

constant to_list {A : Type} {n : nat} : vector A n → list A
constant to_vector {A : Type} (l : list A) : vector A (list.length l)
constant matrix.{l} : Type.{l} → nat → nat → Type.{l}
constant to_matrix {A : Type} {n : nat} : vector A n → matrix A n 1

#compose list.length to_list → vec_len
#compose to_matrix to_vector → list_to_matrix
#compose to_matrix to_vector → list_to_matrix_2

print vec_len
print list_to_matrix
check list_to_matrix_2 -- Error
