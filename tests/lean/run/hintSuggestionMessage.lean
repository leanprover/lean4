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
#guard_msgs (whitespace := exact) in
#eval foo bar baz

/--
info: Top level
  Upper
  Lower

Hint: Hint message
  r̵s̲un̵_̵m̵g̲g̲es̲ta̵i̲o̲n̲
-/
#guard_msgs (whitespace := exact) in
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
#guard_msgs (whitespace := exact) in
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
#guard_msgs (whitespace := exact) in
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
#guard_msgs (whitespace := exact) in
run_meta do
  let hint ← MessageData.hint m!"Hint message" { ref := (← getRef), suggestions := #["suggestion1", "suggestion2"]}
  let msg := MessageData.compose m!"Outer" <| (indentD <| m!"A\nB" ++ indentD "C\nD")
  logInfo (msg ++ hint)


/--
info: Message

Hint: Hint message
  r̵s̲un̵_̵m̵g̲g̲es̲ta̵i̲o̲n̲1̲

Note: Note message
-/
#guard_msgs (whitespace := exact) in
run_meta do
  let hint ← MessageData.hint m!"Hint message" { ref := (← getRef), suggestions := #["suggestion1"]}
  let note := MessageData.note "Note message"
  logInfo ("Message" ++ hint ++ note)

set_option pp.fieldNotation.generalized false in
/--
info: Message with expression
  Nat.succ Nat.zero

Hint: Before
  Nat.succ Nat.zero
After
  r̵s̲un̵_̵m̵g̲g̲es̲ta̵i̲o̲n̲

Note: Before
  Nat.succ Nat.zero
After
-/
#guard_msgs (whitespace := exact) in
run_meta do
  let e := Expr.app (.const `Nat.succ []) (.const `Nat.zero [])
  let hint ← MessageData.hint m!"Before{indentExpr e}\nAfter" { ref := (← getRef), suggestions := #["suggestion"] }
  logInfo (m!"Message with expression{indentExpr e}" ++ hint ++ .note m!"Before{indentExpr e}\nAfter")

-- Generally, we should avoid nesting hints, but we nonetheless check that it works in principle:
/--
info: Outer error
  Nested error
  ⏎
  Hint: Inner
    test
  hint
    r̵s̲un̵_̵m̵g̲g̲es̲ta̵i̲o̲n̲1̲
  ⏎
  Note: internal
    test
  note

Hint: Outer
  test
hint
  r̵s̲un̵_̵m̵g̲g̲es̲ta̵i̲o̲n̲2̲
-/
#guard_msgs (whitespace := exact) in
run_meta do
  let hint₁ ← MessageData.hint m!"Inner{indentD "test"}\nhint" { ref := (← getRef), suggestions := #["suggestion1"]}
  let hint₂ ← MessageData.hint m!"Outer{indentD "test"}\nhint" { ref := (← getRef), suggestions := #["suggestion2"]}
  let note := MessageData.note m!"internal{indentD "test"}\nnote"
  let msg := m!"Outer error" ++ (indentD ("Nested error" ++ hint₁ ++ note)) ++ hint₂
  logInfo msg


def Std.Format.repr : Format → String
  | .line => "⏎"
  | .tag t f => s!"tag {t} {repr f}"
  | .nil => "[nil]"
  | .align force => s!"align_{force}"
  | .group f b => s!"group({if b matches .fill then "fill" else "allOrNone"})[{repr f}]"
  | .text s => s!"{_root_.repr s}"
  | .nest n f => s!"nest({n})[{repr f}]"
  | .append f f' => s!"{repr f} ++ {repr f'}"

open Lean Meta in
partial def _root_.Lean.MessageData.printCtors : MessageData → IO String
  | .ofFormatWithInfos {fmt, infos} => return s!"ofwi {repr fmt.repr}"
  | .ofGoal mvid => return s!"ofGoal {mvid.name}"
  | .ofWidget wi fallback => return "widget"
  | .withContext ctx md => return s!"withContext ({← md.printCtors})"
  | .withNamingContext nc md => return s!"withNamingContext ({← md.printCtors})"
  | .nest n md => return s!"nest {n} ({← md.printCtors})"
  | .group md => return s!"group ({← md.printCtors})"
  | .compose md1 md2 => return s!"{← md1.printCtors} ++ {← md2.printCtors}"
  | .tagged nm md => return s!"tagged {nm} ({← md.printCtors})"
  | .trace .. => return "trace"
  | .ofLazy f _ => return s!"lazy {← ((← f none).get? MessageData).mapM (·.printCtors)}"

run_meta do
  logInfo <| m!"A{indentD "B"}" ++ Format.line ++ "C"

run_meta do
  let msg := MessageData.note m!"Before{indentD "hi"}\nAfter"
  let msg := m!"\n\n" ++ m!"Note: Before{indentD "hi"}\nAfter"
  let leader := "" --.nest 2 "foo\nshould nest"
  let msg := leader ++ msg
  logInfo (← msg.printCtors)
  logInfo <| (← msg.format).repr
  logInfo msg

open MessageData in
run_meta do
  let text := toMessageData
  let line := toMessageData Format.line
  logInfo <| text m!"hi" ++ line ++ nest 2 (m!"hello" ++ line ++ m!"nested") ++ line ++ m!"bye"

def foob : MessageData :=
  .compose (.nest 2 m!"\nfoo") "bar"
run_meta show MetaM Unit from do
  IO.println (← foob.printCtors)
  throwError foob
run_meta do logInfo (m!"a" ++ Format.line ++ m!"b" ++ Format.line ++ .group m!"a\nb")

/-
Ideal Behavior:
* All `Format.line`s in hint are rendered as newlines
* Hint does not "inherit" any preceding group in a `compose`; it can only end up in a group/nest
  if it is explicitly passed to that constructor (which it never should be)
* Hint is preceded by two new lines that always render as such

Issue:

If we just use string-literal `\n`s, then any `Format.line`s within the note -- which assume they're
at top level -- might turn into spaces

If we use `Format.line`s, then sometimes it seems we get swallowed into a preceding `nest` or `group`
and don't get line breaks preceding the secondary message
-/

namespace Testing

def hint (msg : MessageData) (items : List MessageData) :=
  m!"\n\nHint: {msg}" ++
    if _ : items.length = 1 then
      indentD items[0]
    else
      items.foldl (init := m!"") fun acc item => m!"{acc}\n• {item}"

run_meta do
  let hint₁ := hint "Do this" ["suggestion"]
  let hint₂ := hint "Do the other thing" ["other"]
  logInfo (m!"Here is an important message{indentD "some code"}\nAnd more text" ++ hint₁ ++ hint₂)

run_meta do
  let e := Expr.app (.const `Nat.succ []) (.const `Nat.zero [])
  let hint₁ := hint m!"Before{indentExpr e}\nAfter" ["suggestion"]
  logInfo (m!"Message with expression{indentExpr e}" ++ hint₁ ++ hint m!"Before{indentExpr e}\nAfter" [])

run_meta do
  let hint := hint m!"Hint message" ["sug"]
  let msg := .group ("Top level" ++ indentD "Upper\nLower") ++ hint
  logInfo msg

run_meta do
  let hint := m!"\nD\nD"
  logInfo <| m!"A" ++ indentD (indentD "B\nC") ++ hint

run_meta do
  logInfo m!"A\n{.nest 2 "\nB"}\nC"
