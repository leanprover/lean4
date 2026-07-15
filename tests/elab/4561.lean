import Lean.Elab.Command
/-!
# 4561: group(ppSpace) was not pretty printing with a space
-/

/-!
Example from the issue. Here, ppSpace is wrapped in a group due to macro argument handling.
-/
macro (name := useSyntax) "use0" ppSpace arg:term : tactic => `(tactic| sorry)

/-- info: use0 .succ✝ 0 -/
#guard_msgs in
run_cmd do
  Lean.logInfo <| ← `(tactic| use0 .succ 0)

/-!
Version of this using `syntax` to test it without macro argument handling.
-/

syntax "use1" ppSpace term,+ : tactic
syntax "use2" group(ppSpace) term,+ : tactic

/--
info: use1 .succ✝ 0
---
info: use2 .succ✝ 0
-/
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.logInfo <| ← `(tactic| use1 .succ 0)
  Lean.logInfo <| ← `(tactic| use2 .succ 0)

/-!
Check that fix even works inside other nodes.
-/

syntax myPPSpace := ppSpace

syntax "use3" myPPSpace term,+ : tactic
syntax "use4" group(myPPSpace) term,+ : tactic

/--
info: use3 .succ✝ 0
---
info: use4 .succ✝ 0
-/
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.logInfo <| ← `(tactic| use3 .succ 0)
  Lean.logInfo <| ← `(tactic| use4 .succ 0)
