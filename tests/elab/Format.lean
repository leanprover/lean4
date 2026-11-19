open Lean
open Std
open Std.Format

def eval (w : Nat) (f : Format) : IO Unit := do
IO.println $ f.pretty w

-- hard line breaks should re-evaluate flattening behavior within group
#eval eval 5 $ fill (text "a" ++ line ++ text "b\nlooooooooong" ++ line ++ text "c") ++ line ++ text "d"

-- basic `fill` test
#eval eval 20 $ fill (Format.joinSep ((List.range 13).map fun i => i.repeat (fun s => s ++ "a") "a") line)
-- `fill` items that are too big should get dedicated
#eval eval 8 $ fill (Format.joinSep [text "a", text "b", paren (text "ccccc" ++ line ++ text "d"), text "e"] line)
