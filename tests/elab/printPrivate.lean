module

-- Test that `pp.privateNames` affects the name in the output of `#print`, `#print sig`, and `#check`.

private def foo : Nat := 42

-- Without pp.privateNames, commands show the user name
/--
info: private def foo : Nat :=
42
-/
#guard_msgs in
#print foo

/--
info: private def foo : Nat
-/
#guard_msgs in
#print sig foo

/--
info: foo : Nat
-/
#guard_msgs in
#check @foo

-- With pp.privateNames, commands should show the full private name
set_option pp.privateNames true in
/--
info: private def _private.elab.printPrivate.0.foo : Nat :=
42
-/
#guard_msgs in
#print foo

set_option pp.privateNames true in
/--
info: private def _private.elab.printPrivate.0.foo : Nat
-/
#guard_msgs in
#print sig foo

set_option pp.privateNames true in
/--
info: _private.elab.printPrivate.0.foo : Nat
-/
#guard_msgs in
#check @foo
