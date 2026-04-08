import Lean.Meta

/-!
# Preview spans for hints in messages

Tests rendering of hint suggestion preview spans in message data.
-/

open Lean Meta Hint

/-! ## Valid span appears -/

elab "suggest_id_insertion" _id:ident t:term : term <= tp => do
  let p := t.raw.getPos?.get!
  let hint ← MessageData.hint "Insert `id`" #[{
    suggestion := "id "
    span? := Syntax.ofRange ⟨p, p⟩
    previewSpan? := t
  }]
  logInfo <| m!"Message" ++ hint
  Lean.Elab.Term.elabTerm t tp

/--
info: Message

Hint: Insert `id`
  i̲d̲ ̲true
-/
#guard_msgs in
example := suggest_id_insertion Foo true

elab "one" "two" tk:"three" "four" "five" : term => do
  let hint ← MessageData.hint "Insert `id`" #[{
    suggestion := "ee"
    span? := tk
    previewSpan? := (← getRef)
  }]
  logInfo m!"Message{hint}"
  return .const ``Unit.unit []

/--
info: Message

Hint: Insert `id`
  one two t̵h̵r̵ee four five
-/
#guard_msgs in
example := one two three four five

/-! ## Fallback appears in case of erroneous span -/

elab "bad_suggest_id_insertion" id:ident t:term : term <= tp => do
  let p := t.raw.getPos?.get!
  let hint ← MessageData.hint "Insert `id`" #[{
    suggestion := "id "
    span? := Syntax.ofRange ⟨p, p⟩
    previewSpan? := id  -- does not include edit range
  }]
  logInfo <| m!"Message" ++ hint
  Lean.Elab.Term.elabTerm t tp

/--
info: Message

Hint: Insert `id`
  i̲d̲ ̲
-/
#guard_msgs in
example := bad_suggest_id_insertion Foo true
