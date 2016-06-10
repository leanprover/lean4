import data.nat
open nat

constant List.{l} : Type.{l} → Type.{l}
constant vector.{l} : Type.{l} → nat → Type.{l}
constant matrix.{l} : Type.{l} → nat → nat → Type.{l}
constant length : Pi {A : Type}, List A → nat

constant List_to_vec {A : Type} (l : List A) : vector A (length l)
constant to_row {A : Type} {n : nat} : vector A n → matrix A 1 n
constant to_col {A : Type} {n : nat} : vector A n → matrix A n 1
constant to_List {A : Type} {n : nat} : vector A n → List A

attribute to_row [coercion]
attribute to_col [coercion]
attribute List_to_vec [coercion]
attribute to_List [coercion]

constant f {A : Type} {n : nat} (M : matrix A n 1) : nat
constant g {A : Type} {n : nat} (M : matrix A 1 n) : nat
constant v : vector nat 10
constant l : List nat

check f v
check g v
check f l
check g l
