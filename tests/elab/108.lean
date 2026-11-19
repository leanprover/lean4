macro "m" n:ident : command => `(def $n := 1)

m foo

/-- info: foo : Nat -/
#guard_msgs in
#check foo
