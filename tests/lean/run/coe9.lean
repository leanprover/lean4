import data.nat
open nat

variable list.{l} : Type.{l} → Type.{l}
variable vector.{l} : Type.{l} → nat → Type.{l}
variable matrix.{l} : Type.{l} → nat → nat → Type.{l}
variable length : Pi {A : Type}, list A → nat

variable list_to_vec {A : Type} (l : list A) : vector A (length l)
variable to_row {A : Type} {n : nat} : vector A n → matrix A 1 n
variable to_col {A : Type} {n : nat} : vector A n → matrix A n 1
variable to_list {A : Type} {n : nat} : vector A n → list A

coercion to_row
coercion to_col
coercion list_to_vec
coercion to_list

variable f {A : Type} {n : nat} (M : matrix A n 1) : nat
variable g {A : Type} {n : nat} (M : matrix A 1 n) : nat
variable v : vector nat 10
variable l : list nat

check f v
check g v
check f l
check g l
