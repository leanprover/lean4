import Lean

/-!
Tests `Lean.Fmt.checkUnitRanges`, which checks that each unit of the rendering of a command (a part
that the formatter produced from one input syntax node or token) parses back as one node or token
at the same range.
-/

open Lean Lean.Fmt Lean.Elab.Command

/-- Removes the markers `⟦` and `⟧` from `s` and returns the byte ranges between matching markers. -/
def parseMarkers (s : String) : String × Array (Nat × Nat) := Id.run do
  let mut out := ""
  let mut starts : List Nat := []
  let mut ranges := #[]
  for c in s.toList do
    if c == '⟦' then
      starts := out.utf8ByteSize :: starts
    else if c == '⟧' then
      if let start :: rest := starts then
        ranges := ranges.push (start, out.utf8ByteSize)
        starts := rest
    else
      out := out.push c
  return (out, ranges)

/--
Parses `marked` without the markers as a command and checks the marked units, in the order of their
closing markers.
-/
def check (marked : String) : CommandElabM Unit := do
  let (rendering, ranges) := parseMarkers marked
  let ictx := Parser.mkInputContext rendering "<test>"
  let (stx, _, msgs) := Parser.parseCommand ictx { env := ← getEnv, options := {} } {} {}
  if msgs.hasErrors || stx.hasMissing then
    logInfo "parse error"
    return
  let units := ranges.map fun (start, stop) =>
    { input := .missing, start := ⟨start⟩, stop := ⟨stop⟩ : RenderedUnit }
  match checkUnitRanges stx units with
  | none => logInfo "ok"
  | some (unit, mismatch) =>
    logInfo m!"{(String.Pos.Raw.extract rendering unit.start unit.stop).quote}: {repr mismatch}"

/-! Added parens keep the `do` block a unit. -/

/-- info: ok -/
#guard_msgs in
run_cmd check "def f := ⟦g (⟦do pure 1⟧) ⟦fun _ => 2⟧⟧"

/-! Without the parens, the parser puts `fun _ => 2` into the `do` block. -/

/-- info: "do pure 1": Lean.Fmt.UnitMismatch.noNodeOrToken -/
#guard_msgs in
run_cmd check "def f := ⟦g ⟦do pure 1⟧ ⟦fun _ => 2⟧⟧"

/-! Without the parens, `*` takes `b` as its left operand. -/

/-- info: "a + b": Lean.Fmt.UnitMismatch.noNodeOrToken -/
#guard_msgs in
run_cmd check "def f := ⟦⟦a + b⟧ * c⟧"

/-! Without the space, `a` and `b` become one identifier. -/

/-- info: "a": Lean.Fmt.UnitMismatch.tokenCrossesStop -/
#guard_msgs in
run_cmd check "def f := ⟦a⟧⟦b⟧"

/-- info: "b": Lean.Fmt.UnitMismatch.tokenCrossesStart -/
#guard_msgs in
run_cmd check "def f := a⟦b⟧"

/-! Whitespace and comments at the ends of a unit are not part of its range. -/

/-- info: ok -/
#guard_msgs in
run_cmd check "def f := g⟦ /- c -/ x -- d\n ⟧y"

/-! A unit without tokens is not checked. -/

/-- info: ok -/
#guard_msgs in
run_cmd check "def f := g ⟦/- c -/⟧ x"

/-!
The check only sees the tokens of the reparsed command, so it does not notice that the command stops
before its rendering stops. `Lean.Fmt.checkReparse` checks the stop position separately.
-/

/-- info: ok -/
#guard_msgs in
run_cmd check "⟦theorem foo : True := by\n  skip\ntrivial⟧"

-- Two term syntaxes that accept the same input, so the parser produces a `choice` node.
syntax (name := choiceA) "choiceTest " term : term
syntax (name := choiceB) "choiceTest " term : term

/-! The tokens of a choice node are checked once, so units in it and after it are checked as usual. -/

/-- info: ok -/
#guard_msgs in
run_cmd check "def f := (⟦choiceTest ⟦1⟧⟧) + ⟦x⟧"

/-- info: "1 +": Lean.Fmt.UnitMismatch.noNodeOrToken -/
#guard_msgs in
run_cmd check "def f := (choiceTest ⟦1 +⟧ 2) + x"
