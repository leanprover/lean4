import Lean.Meta

open Lean Meta

/--
info: Test

Hint: Message
  r̵u̵n̵_̵m̵e̵t̵a̵r̲u̲n̲_̲e̲l̲a̲b̲
-/
#guard_msgs in
run_meta do
--^ codeAction
  let hint ← MessageData.lazyHint do
    return {
      msg := m!"Message"
      suggestions := #["run_elab"]
    }
  logInfo <| m!"Test" ++ hint

open Elab.Command in
elab "hint_at_term " t:term : command => do
  let hint ← liftTermElabM <| MessageData.lazyHint (ref? := t) do
    return {
      msg := m!"Message"
      suggestions := #[(← `(42)), "57"]
    }
  logInfo <| m!"Test" ++ hint

/--
info: Test

Hint: Message
  • 41̵2̲
  • 4̵1̵5̲7̲
-/
#guard_msgs in
hint_at_term 41
--^ codeAction

open Elab.Command in
elab k1:"hint" k2:"at" k3:"multiple" k4:"refs" : command => do
  let hint ← liftTermElabM <| MessageData.lazyHint (ref? := k1) do
    return {
      msg := m!"Message"
      suggestions := #[
        "hints",
        { suggestion := "foo", span? := k2 },
        { suggestion := "multiples", span? := k3 },
        { suggestion := "ref", span? := k4 },
        { suggestion := "in", span? := k2 },
      ]
    }
  logInfo <| m!"Test" ++ hint

/--
info: Test

Hint: Message
  • hints̲
  • a̵t̵f̲o̲o̲
  • multiples̲
  • refs̵
  • a̵t̵i̲n̲
-/
#guard_msgs in
hint at multiple refs
--^ codeAction
