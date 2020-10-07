import Lean.Data.Format
new_frontend
open Lean.Format

-- hard line breaks should re-evaluate flattening behavior within group
#eval (IO.println $ (group (text "a" ++ line ++ text "b\nlooooooooong" ++ line ++ text "c") ++ line ++ text "d").prettyAux 10 : IO _)

