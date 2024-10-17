def f : IO Nat := do
  IO.println "foo"
  return 0

abbrev M := StateRefT Nat IO

def g (a : Nat) : M Unit :=
  pure ()

/--
info: id do
  let a ← liftM f
  g a : M Unit
-/
#guard_msgs in
#check id (α := M Unit) do let a ← f; g a

set_option autoLift false

set_option pp.mvars false in
/--
warning: type mismatch
  f
has type
  IO Nat : Type
but is expected to have type
  M ?_ : Type
---
info: id do
  let a ← sorry
  g a : M Unit
-/
#guard_msgs in
#check_failure id (α := M Unit) do let a ← f; g a

/--
info: id do
  let a ← liftM f
  g a : M Unit
-/
#guard_msgs in
#check id (α := M Unit) do let a ← liftM f; g a
