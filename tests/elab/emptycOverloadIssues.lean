structure A :=
(x : Nat := 10)

abbrev B := A

structure C :=
(a : A := {})
(b : B := {})
