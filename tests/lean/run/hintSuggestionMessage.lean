import Lean.Meta

/-!
# Tests for hint suggestion messages

Tests rendering of hint suggestions in message data. Note that we can only assess the Unicode
versions here.
-/

open Lean Meta Hint

/-! ## Basic hint functionality -/

elab foo:"foo" bar:"bar" "baz" : term => do
  let suggestions := #[
    { suggestion := "hi", preInfo? := "generic: " },
    { suggestion := "cheers", postInfo? := " (at `bar`)", span? := bar }
  ]
  let hint ← MessageData.hint
    m!"Consider adding a greeting to your program to make it friendlier"
    suggestions
    foo
    "Add greeting: "
  let msg := m!"Your program is insufficiently friendly" ++ hint
  throwErrorAt foo msg

/--
error: Your program is insufficiently friendly

Hint: Consider adding a greeting to your program to make it friendlier
  • generic: f̵o̵o̵h̲i̲
  • b̵a̵r̵c̲h̲e̲e̲r̲s̲ (at `bar`)
-/
#guard_msgs (whitespace := exact) in
#check foo bar baz

/-! ## Well-behavedness with preceding nested environments -/

/--
info: Top level
  Upper
  Lower

Hint: Hint message
  r̵u̵n̵_̵m̵e̵t̵a̵s̲u̲g̲g̲e̲s̲t̲i̲o̲n̲
-/
#guard_msgs (whitespace := exact) in
run_meta do
  let hint ← MessageData.hint m!"Hint message" #["suggestion"]
  let msg := "Top level" ++ indentD "Upper\nLower" ++ hint
  logInfo msg

/--
info: Outer
  A
  B
    C
    D

Hint: Hint message
  r̵u̵n̵_̵m̵e̵t̵a̵s̲u̲g̲g̲e̲s̲t̲i̲o̲n̲
-/
#guard_msgs (whitespace := exact) in
run_meta do
  let hint ← MessageData.hint m!"Hint message" #["suggestion"]
  let msg := MessageData.compose m!"Outer" <| (indentD <| m!"A\nB" ++ indentD "C\nD")
  logInfo (msg ++ hint)

/--
info: Outer
  A
  B
    C
    D

Hint: Hint message
  • r̵u̵n̵_̵m̵e̵t̵a̵s̲u̲g̲g̲e̲s̲t̲i̲o̲n̲1̲
  • r̵u̵n̵_̵m̵e̵t̵a̵s̲u̲g̲g̲e̲s̲t̲i̲o̲n̲2̲
-/
#guard_msgs (whitespace := exact) in
run_meta do
  let hint ← MessageData.hint m!"Hint message" #["suggestion1", "suggestion2"]
  let msg := MessageData.compose m!"Outer" <| (indentD <| m!"A\nB" ++ indentD "C\nD")
  logInfo (msg ++ hint)

/-! ## Multi-line suggestion alignment -/

/--
info:

Hint: Hint message
  r̵u̵n̵_̵m̵e̵t̵a̵A̲
  ̲B̲
  ̲C̲
-/
#guard_msgs (whitespace := exact) in
run_meta do
  let hint ← MessageData.hint m!"Hint message" #["A\nB\nC"]
  logInfo hint

/--
info:

Hint: Hint message
  • r̵u̵n̵_̵m̵e̵t̵a̵A̲
    ̲B̲
    ̲C̲
  • r̵u̵n̵_̵m̵e̵t̵a̵D̲
    ̲ ̲ ̲E̲
    ̲ ̲ ̲F̲
-/
#guard_msgs (whitespace := exact) in
run_meta do
  let hint ← MessageData.hint m!"Hint message" #["A\nB\nC", "D\n  E\n  F"]
  logInfo hint

/-! ## Well-behavedness with other message subcomponents -/

set_option pp.fieldNotation.generalized false in
/--
info: Message with expression
  Nat.succ Nat.zero

Hint: Before
  Nat.succ Nat.zero
After
  r̵u̵n̵_̵m̵e̵t̵a̵s̲u̲g̲g̲e̲s̲t̲i̲o̲n̲

Note: Before
  Nat.succ Nat.zero
After
-/
#guard_msgs (whitespace := exact) in
run_meta do
  let e := Expr.app (.const `Nat.succ []) (.const `Nat.zero [])
  let hint ← MessageData.hint m!"Before{indentExpr e}\nAfter" #["suggestion"]
  logInfo (m!"Message with expression{indentExpr e}" ++ hint ++ .note m!"Before{indentExpr e}\nAfter")

-- Generally, we should avoid nesting hints, but we nonetheless check that it works in principle:
/--
info: Outer error
  Nested error
  ⏎
  Hint: Inner
    test
  hint
    r̵u̵n̵_̵m̵e̵t̵a̵s̲u̲g̲g̲e̲s̲t̲i̲o̲n̲1̲a̲
    ̲s̲u̲g̲g̲e̲s̲t̲i̲o̲n̲1̲b̲
  ⏎
  Note: internal
    test
  note

Hint: Outer
  test
hint
  r̵u̵n̵_̵m̵e̵t̵a̵s̲u̲g̲g̲e̲s̲t̲i̲o̲n̲2̲a̲
  ̲s̲u̲g̲g̲e̲s̲t̲i̲o̲n̲2̲b̲
-/
#guard_msgs (whitespace := exact) in
run_meta do
  let hint₁ ← MessageData.hint m!"Inner{indentD "test"}\nhint" #["suggestion1a\nsuggestion1b"]
  let hint₂ ← MessageData.hint m!"Outer{indentD "test"}\nhint" #["suggestion2a\nsuggestion2b"]
  let note := MessageData.note m!"internal{indentD "test"}\nnote"
  let msg := m!"Outer error" ++ (indentD ("Nested error" ++ hint₁ ++ note)) ++ hint₂
  logInfo msg

/-! ## Diff behavior -/

elab "longWordWithoutAnySpaces" : term => do
  let hint ← MessageData.hint m!"Use one of these instead"
    #["longWordWithoutSpaces", "longWord", "paces", "ordSpaces"]
  throwError m!"Invalid" ++ hint

/--
error: Invalid

Hint: Use one of these instead
  • longWordWithoutA̵n̵y̵Spaces
  • longWordW̵i̵t̵h̵o̵u̵t̵A̵n̵y̵S̵p̵a̵c̵e̵s̵
  • l̵o̵n̵g̵W̵o̵r̵d̵W̵i̵t̵h̵o̵u̵t̵A̵n̵y̵S̵paces
  • l̵o̵n̵g̵W̵o̵r̵d̵W̵i̵t̵h̵o̵u̵t̵A̵n̵y̵S̵p̵a̵c̵e̵s̵o̲r̲d̲S̲p̲a̲c̲e̲s̲
-/
#guard_msgs (whitespace := exact) in
#check longWordWithoutAnySpaces

elab "first" "second" "third" "fourth" "fifth" : term => do
  let hint ← MessageData.hint m!"Use one of these instead"
    #["first second thi", "second fourth fifth", "fi se th fo fi", "second"]
  throwError m!"Invalid" ++ hint

/--
error: Invalid

Hint: Use one of these instead
  • first second thir̵d̵ ̵f̵o̵u̵r̵t̵h̵ ̵f̵i̵f̵t̵h̵
  • f̵i̵r̵s̵t̵ ̵second t̵h̵i̵r̵d̵ ̵fourth fifth
  • f̵i̵r̵s̵t̵ ̵s̵e̵c̵o̵n̵d̵ ̵t̵h̵i̵r̵d̵ ̵f̵o̵u̵r̵t̵h̵ ̵f̵i̵f̵t̵h̵f̲i̲ ̲s̲e̲ ̲t̲h̲ ̲f̲o̲ ̲f̲i̲
  • f̵i̵r̵s̵t̵ ̵s̵e̵c̵o̵n̵d̵ ̵t̵h̵i̵r̵d̵ ̵f̵o̵u̵r̵t̵h̵ ̵f̵i̵f̵t̵h̵s̲e̲c̲o̲n̲d̲
-/
#guard_msgs (whitespace := exact) in
#check first second third fourth fifth

elab "suggest_replacement%" t:term : term => do
  let msg ← MessageData.hint m!"Try one of these"
    #["let x := 31; x", "let (a, b, c) := (1, 2, 3)\n  b", "x"] t
  throwErrorAt t m!"Invalid{msg}"

/--
error: Invalid

Hint: Try one of these
  • let x := 4̵2̵
    ̵ ̵ ̵2̵ ̵*̵3̲1̲;̲ x
  • l̵e̵t̵ ̵x̵ ̵:̵=̵ ̵4̵2̵
    ̵ ̵ ̵2̵ ̵*̵ ̵x̵l̲e̲t̲ ̲(̲a̲,̲ ̲b̲,̲ ̲c̲)̲ ̲:̲=̲ ̲(̲1̲,̲ ̲2̲,̲ ̲3̲)̲
    ̲ ̲ ̲b̲
  • l̵e̵t̵ ̵x ̵:̵=̵ ̵4̵2̵
    ̵ ̵ ̵2̵ ̵*̵ ̵x̵
-/
#guard_msgs (whitespace := exact) in
#check suggest_replacement%
  let x := 42
  2 * x

/-! ## Forced diff granularities -/

namespace DiffGranularity
scoped syntax "select " "granularity " term : command

open Elab in
elab_rules : command
  | `(command| select granularity $t) => do
    let tp := mkConst ``DiffGranularity
    let g ← unsafe Command.runTermElabM (fun _ =>
      Term.elabTerm t tp >>= monadLift ∘ evalExpr DiffGranularity tp)
    let hint ← Command.liftCoreM <| MessageData.hint m!"Hint" #[{
      suggestion :=
        if g matches .all then
          -- Ensure we wouldn't have used `.all` by default
          "selected granularity .all"
        else
          "many granularity words not matching the source"
      diffGranularity := g
    }]
    logInfo hint

/--
info:

Hint: Hint
  s̵e̵m̲a̲n̲y̲ ̲g̲r̲a̲n̲u̲le̵c̵a̲r̲i̲ty̲ w̲o̲r̲d̲s̲ ̲n̲o̲t̲ ̲m̲a̲t̲c̲h̲i̲n̲gr̵a̵n̵u̵l̵a̵r̵i̵ ̲ty̵h̲e̲ .̵c̵h̵a̵s̲o̲u̲rc̲e̲
-/
#guard_msgs (whitespace := exact) in
select granularity .char

/--
info:

Hint: Hint
  s̵e̵l̵e̵c̵t̵m̲a̲n̲y̲ granularity .̵w̵o̵r̵d̵w̲o̲r̲d̲s̲ ̲n̲o̲t̲ ̲m̲a̲t̲c̲h̲i̲n̲g̲ ̲t̲h̲e̲ ̲s̲o̲u̲r̲c̲e̲
-/
#guard_msgs (whitespace := exact) in
select granularity .word

/--
info:

Hint: Hint
  s̵e̵l̵e̵c̵t̵ ̵g̵r̵a̵n̵u̵l̵a̵r̵i̵t̵y̵ ̵.̵a̵l̵l̵s̲e̲l̲e̲c̲t̲e̲d̲ ̲g̲r̲a̲n̲u̲l̲a̲r̲i̲t̲y̲ ̲.̲a̲l̲l̲
-/
#guard_msgs (whitespace := exact) in
select granularity .all


end DiffGranularity
