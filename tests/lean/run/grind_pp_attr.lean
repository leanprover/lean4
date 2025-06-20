import Lean.Elab.Command

open Lean Elab Command

/--
info: @[grind =]
example :=
  0
-/
#guard_msgs in
run_cmd
  let stx ← `(@[grind =] example := 0)
  let fmt : Option Format := ←
        liftCoreM <| PrettyPrinter.ppCategory `command stx
  if let some fmt := fmt then
  let st := fmt.pretty
  dbg_trace st
