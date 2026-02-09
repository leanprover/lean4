macro "test%" n:ident : command =>
  `(def foo := 42
    def $n := foo
  )

test% bar

/--
info: def bar : Nat :=
foo✝
-/
#guard_msgs in
#print bar
