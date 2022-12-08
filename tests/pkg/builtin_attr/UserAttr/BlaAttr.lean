import Lean

open Lean

-- initialize discard <| registerTagAttribute `foo ""

initialize registerBuiltinAttribute {
    name := `bar,
    descr := "",
    add := fun _ _ _ => pure ()
  }
