import data.nat
open nat

constant list.{l} : Type.{l} → Type.{l}
constant vector.{l} : Type.{l} → nat → Type.{l}
constant matrix.{l} : Type.{l} → nat → nat → Type.{l}
constant length : Pi {A : Type}, list A → nat

constant list_to_vec {A : Type} (l : list A) : vector A (length l)
constant to_row {A : Type} {n : nat} : vector A n → matrix A 1 n
constant to_col {A : Type} {n : nat} : vector A n → matrix A n 1
constant to_list {A : Type} {n : nat} : vector A n → list A

attribute to_row [coercion]
attribute to_col [coercion]
attribute list_to_vec [coercion]
attribute to_list [coercion]

constant f {A : Type} {n : nat} (M : matrix A n 1) : nat
constant g {A : Type} {n : nat} (M : matrix A 1 n) : nat
constant v : vector nat 10
constant l : list nat

check f v
check g v
check f l
check g l
