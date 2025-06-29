import Lean.Elab.Command

open Lean Elab Command

def test (stx : Syntax) : CommandElabM Unit := do
  let fmt : Option Format := ←
        liftCoreM <| PrettyPrinter.ppCategory `command stx
  if let some fmt := fmt then
  let st := fmt.pretty
  dbg_trace st


/--
info: @[grind =]
example :=
  0
-/
#guard_msgs in
run_cmd test (← `(@[grind =] example := 0))

/--
info: @[grind _=_]
example :=
  0
-/
#guard_msgs in
run_cmd test (← `(@[grind _=_] example := 0))

/--
info: @[grind =_]
example :=
  0
-/
#guard_msgs in
run_cmd test (← `(@[grind =_] example := 0))

/--
info: @[grind →]
example :=
  0
-/
#guard_msgs in
run_cmd test (← `(@[grind →] example := 0))

/--
info: @[grind ←]
example :=
  0
-/
#guard_msgs in
run_cmd test (← `(@[grind ←] example := 0))

/--
info: @[grind ←=]
example :=
  0
-/
#guard_msgs in
run_cmd test (← `(@[grind ←=] example := 0))
