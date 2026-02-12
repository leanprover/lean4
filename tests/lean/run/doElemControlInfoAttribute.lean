import Lean

open Lean Parser Meta Elab Do

syntax (name := myReturn) "myreturn" : doElem

@[doElem_elab myReturn] def elabMyReturn : DoElab := fun _stx dec => do
  elabDoElem (← `(doElem| return 42)) dec

/--
error: No `ControlInfo` inference handler found for `myReturn` in syntax ⏎
  myreturn
Register a handler with `@[doElem_control_info myReturn]`.
-/
#guard_msgs (error) in
#eval Id.run do
  for i in [1, 2, 3] do
    myreturn
  return 0

@[doElem_control_info myReturn] def controlInfoMyReturn : ControlInfoHandler := fun _stx => do
  return { exitsRegularly := false, returnsEarly := true }

/-- info: 42 -/
#guard_msgs in
#eval Id.run do
  for i in [1, 2, 3] do
    myreturn
  return 0

syntax (name := myIf) "myif" term " then" doSeq " else" doSeq : doElem

@[doElem_elab myIf] def elabMyIf : DoElab := fun stx dec => do
  let `(doElem| myif $cond:term then $thenSeq else $elseSeq) := stx | throwUnsupportedSyntax
  elabDoElem (← `(doElem| if $cond then $thenSeq else $elseSeq)) dec

/--
error: No `ControlInfo` inference handler found for `myIf` in syntax ⏎
  myif i > 1 then
    return 23 else
    continue
Register a handler with `@[doElem_control_info myIf]`.
-/
#guard_msgs (error) in
#eval Id.run do
  for i in [1, 2, 3] do
    myif i > 1 then return 23 else continue
  return 0

@[doElem_control_info myIf] def controlInfoMyIf : ControlInfoHandler := fun stx => do
  let `(doElem| myif $_:term then $thenSeq else $elseSeq) := stx | throwUnsupportedSyntax
  let thenInfo ← inferControlInfoSeq thenSeq
  let elseInfo ← inferControlInfoSeq elseSeq
  return thenInfo.alternative elseInfo

/-- info: 26 -/
#guard_msgs in
#eval Id.run do
  let mut x := 0
  for i in [1, 2, 3] do
    myif i > 2 then return x + 23 else x := x + i; continue
  return 0
