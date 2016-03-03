import data.matrix
open algebra fin nat

namespace matrix

definition vector [reducible] (A : Type) (n : nat) := fin n → A

definition to_cvec [reducible] [coercion] {A : Type} {n : nat} (v : vector A n)
: matrix A n 1 := λ i o, v i

definition to_rvec [reducible] [coercion] {A : Type} {n : nat} (v : vector A n)
: matrix A 1 n := λ o i, v i

variables (A : Type) (n : nat)
variable [r : comm_ring A]
include r
variables (M : matrix A n n) (v : vector A n)

print "----------------"

check matrix.mul M v
check (λ f, f v) (matrix.mul M)
check (λ v, matrix.mul M v) v

end matrix
