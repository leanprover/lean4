import Lean.Meta

/-!
# Tests for hint suggestion messages

Tests rendering of hint suggestions in message data. Note that we can only assess the Unicode
versions here.
-/

open Lean Meta Hint

elab foo:"foo" bar:"bar" "baz" : term => do
  let sug : Suggestions := {
    ref := foo
    suggestions := #[
      { suggestion := "hi", preInfo? := "generic: " },
      { suggestion := "cheers", postInfo? := " (at `bar`)", span? := bar }
    ],
    codeActionPrefix? := "Add greeting: "
  }
  let msg := m!"Your program is insufficiently friendly" ++
    (← MessageData.hint m!"Consider adding a greeting to your program to make it friendlier" sug)
  throwErrorAt foo msg

/--
error: Your program is insufficiently friendly

Hint: Consider adding a greeting to your program to make it friendlier
  • generic: f̵o̵o̵h̲i̲
  • b̵a̵c̲h̲e̲e̲rs̲ (at `bar`)
-/
#guard_msgs in
#eval foo bar baz

/--
info: Top level
  Upper
  Lower

Hint: Hint message
  r̵s̲un̵_̵m̵g̲g̲es̲ta̵i̲o̲n̲
-/
#guard_msgs in
run_meta do
  let sug : Suggestions := {
    ref := (← getRef)
    suggestions := #["suggestion"]
  }
  let hint ← MessageData.hint m!"Hint message" sug
  let msg := "Top level" ++ indentD "Upper\nLower" ++ hint
  logInfo msg

/--
info: Outer
  Inner

Hint: Hint message
  r̵s̲un̵_̵m̵g̲g̲es̲ta̵i̲o̲n̲
-/
#guard_msgs in
run_meta do
  let nest := .group (.nest 2 "Outer\nInner")
  let hint ← MessageData.hint m!"Hint message" { ref := (← getRef), suggestions := #["suggestion"] }
  logInfo (nest ++ hint)

/--
info: Outer
  A
  B
    C
    D

Hint: Hint message
  r̵s̲un̵_̵m̵g̲g̲es̲ta̵i̲o̲n̲
-/
#guard_msgs in
run_meta do
  let hint ← MessageData.hint m!"Hint message" { ref := (← getRef), suggestions := #["suggestion"]}
  let msg := MessageData.compose m!"Outer" <| (indentD <| m!"A\nB" ++ indentD "C\nD")
  logInfo (msg ++ hint)

/--
info: Outer
  A
  B
    C
    D

Hint: Hint message
  • r̵s̲un̵_̵m̵g̲g̲es̲ta̵i̲o̲n̲1̲
  • r̵s̲un̵_̵m̵g̲g̲es̲ta̵i̲o̲n̲2̲
-/
#guard_msgs in
run_meta do
  let hint ← MessageData.hint m!"Hint message" { ref := (← getRef), suggestions := #["suggestion1", "suggestion2"]}
  let msg := MessageData.compose m!"Outer" <| (indentD <| m!"A\nB" ++ indentD "C\nD")
  logInfo (msg ++ hint)

-- Generally, we should avoid nesting hints, but we nonetheless check that it works in principle:
/--
info: Outer error
  Nested error
  ⏎
  Hint: Inner hint
    r̵s̲un̵_̵m̵g̲g̲es̲ta̵i̲o̲n̲1̲
  ⏎
  Note: internal note

Hint: Outer hint
  r̵s̲un̵_̵m̵g̲g̲es̲ta̵i̲o̲n̲2̲
-/
#guard_msgs in
run_meta do
  let hint₁ ← MessageData.hint m!"Inner hint" { ref := (← getRef), suggestions := #["suggestion1"]}
  let hint₂ ← MessageData.hint m!"Outer hint" { ref := (← getRef), suggestions := #["suggestion2"]}
  let msg := m!"Outer error" ++ (indentD ("Nested error" ++ hint₁ ++ .note "internal note")) ++ hint₂
  logInfo msg
