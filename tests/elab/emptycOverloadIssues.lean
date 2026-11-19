structure A where
(x : Nat := 10)

abbrev B := A

structure C where
(a : A := {})
(b : B := {})
