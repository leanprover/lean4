macro "foo" : term => `(have := 1; this)

/--
info: let_fun this := 1;
this : Nat
-/
#guard_msgs in
#check foo
