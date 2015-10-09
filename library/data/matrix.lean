/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Matrices
-/
import algebra.ring data.fin data.fintype
open algebra fin nat

definition matrix [reducible] (A : Type) (m n : nat) := fin m → fin n → A

namespace matrix
variables {A B C : Type} {m n p : nat}

definition val [reducible] (M : matrix A m n) (i : fin m) (j : fin n) : A :=
M i j

namespace ops
notation M `[` i `, ` j `]` := val M i j
end ops

open ops

protected lemma ext {M N : matrix A m n} (h : ∀ i j, M[i,j] = N[i, j]) : M = N :=
funext (λ i, funext (λ j, h i j))

protected lemma has_decidable_eq [h : decidable_eq A] (m n : nat) : decidable_eq (matrix A m n) :=
_

definition to_matrix (f : fin m → fin n → A) : matrix A m n :=
f

definition map (f : A → B) (M : matrix A m n) : matrix B m n :=
λ i j, f (M[i,j])

definition map₂ (f : A → B → C) (M : matrix A m n) (N : matrix B m n) : matrix C m n :=
λ i j, f (M[i, j]) (N[i,j])

definition transpose (M : matrix A m n) : matrix A n m :=
λ i j, M[j, i]

definition symmetric (M : matrix A n n) :=
transpose M = M

section
variable [r : comm_ring A]
include r

definition identity (n : nat) : matrix A n n :=
λ i j, if i = j then 1 else 0

definition I {n : nat} : matrix A n n :=
identity n

protected definition zero (m n : nat) : matrix A m n :=
λ i j, 0

protected definition add (M : matrix A m n) (N : matrix A m n) : matrix A m n :=
λ i j, M[i, j] + N[i, j]

protected definition sub (M : matrix A m n) (N : matrix A m n) : matrix A m n :=
λ i j, M[i, j] - N[i, j]

protected definition mul (M : matrix A m n) (N : matrix A n p) : matrix A m p :=
λ i j, fin.foldl has_add.add 0 (λ k : fin n, M[i,k] * N[k,j])

definition smul (a : A) (M : matrix A m n) : matrix A m n :=
λ i j, a * M[i, j]

definition matrix_has_zero [reducible] [instance] (m n : nat) : has_zero (matrix A m n) :=
has_zero.mk (matrix.zero m n)

definition matrix_has_one [reducible] [instance] (n : nat) : has_one (matrix A n n) :=
has_one.mk (identity n)

definition matrix_has_add [reducible] [instance] (m n : nat) : has_add (matrix A m n) :=
has_add.mk matrix.add

definition matrix_has_mul [reducible] [instance] (n : nat) : has_mul (matrix A n n) :=
has_mul.mk matrix.mul

infix ` × ` := mul
infix `⬝`    := smul

lemma add_zero (M : matrix A m n) : M + 0 = M :=
matrix.ext (λ i j, !algebra.add_zero)

lemma zero_add (M : matrix A m n) : 0 + M = M :=
matrix.ext (λ i j, !algebra.zero_add)

lemma add.comm (M : matrix A m n) (N : matrix A m n) : M + N = N + M :=
matrix.ext (λ i j, !algebra.add.comm)

lemma add.assoc (M : matrix A m n) (N : matrix A m n) (P : matrix A m n) : (M + N) + P = M + (N + P) :=
matrix.ext (λ i j, !algebra.add.assoc)

definition is_diagonal (M : matrix A n n) :=
∀ i j, i = j ∨ M[i, j] = 0

definition is_zero (M : matrix A m n) :=
∀ i j, M[i, j] = 0

definition is_upper_triangular (M : matrix A n n) :=
∀ i j : fin n, i > j → M[i, j] = 0

definition is_lower_triangular (M : matrix A n n) :=
∀ i j : fin n, i < j → M[i, j] = 0

definition inverse (M : matrix A n n) (N : matrix A n n) :=
M * N = I ∧ N * M = I

definition invertible (M : matrix A n n) :=
∃ N, inverse M N

end
end matrix
