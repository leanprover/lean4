import Lean

open Lean

-- initialize discard <| registerTagAttribute `foo ""

initialize registerBuiltinAttribute {
    name := `bar,
    descr := "",
    add := fun _ _ _ => pure ()
  }

def myFun (x : Nat) :=
  x + 1

example : myFun x = x + 1 :=
  rfl
