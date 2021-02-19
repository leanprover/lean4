def f : IO Nat := do
  IO.println "foo"
  return 0

abbrev M := StateRefT Nat IO

def g (a : Nat) : M Unit :=
  pure ()

#check id (α := M Unit) do let a ← f; g a

set_option autoLift false

#check_failure id (α := M Unit) do let a ← f; g a

#check id (α := M Unit) do let a ← liftM f; g a
