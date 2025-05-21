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
