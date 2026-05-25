import Lean

open Lean

#eval show IO Unit from do
  let msg : MessageData := .trace { cls := `trace.test, result? := some .success } "header" #[]
  let rendered ← (MessageData.toString msg).toIO
  let expected := s!"[trace.test] {checkEmoji} header"
  unless rendered == expected do
    throw <| IO.userError s!"expected {expected}, got {rendered}"

#eval show IO Unit from do
  let msg : MessageData := .trace { cls := `trace.test } "header" #[]
  let rendered ← (MessageData.toString msg).toIO
  let expected := "[trace.test] header"
  unless rendered == expected do
    throw <| IO.userError s!"expected {expected}, got {rendered}"
