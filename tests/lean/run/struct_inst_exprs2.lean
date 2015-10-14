import data.nat.basic
open nat

structure s1 (A : Type) :=
(x : A) (y : A) (h : x = y)

structure s2 (A : Type) :=
(mul : A → A → A) (one : A)

structure s3 (A : Type) extends s1 A, s2 A :=
(mul_one : ∀ a : A, mul a one = a)

definition v1 : s1 nat := {| s1, x := 10, y := 10, h := rfl |}
definition v2 : s2 nat := {| s2, mul := nat.add, one := zero |}
definition v3 : s3 nat := {| s3, mul_one := nat.add_zero, v1, v2 |}

example : s3.x v3 = 10 := rfl
example : s3.y v3 = 10 := rfl
example : s3.mul v3 = nat.add  := rfl
example : s3.one v3 = nat.zero := rfl
