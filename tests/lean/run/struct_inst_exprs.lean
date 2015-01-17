open nat prod

set_option pp.coercions true

definition s : nat × nat := {| prod, pr1 := 10, pr2 := 20 |}

structure test :=
(A : Type) (a : A) (B : A → Type) (b : B a)

definition s2 := ⦃ test, a := 3, b := 10 ⦄

eval s2

definition s3 := {| test, a := 20, s2 |}

eval s3

definition s4 := ⦃ test, A := nat, B := λ a, nat, a := 10, b := 10 ⦄

definition s5 : Σ a : nat, a > 0 :=
 ⦃ sigma, pr1 := 10, pr2 := of_is_true trivial ⦄

eval s5

check ⦃ unit ⦄
