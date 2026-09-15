import Lean

/-!
Checks that a command with a Verso doc comment pretty-prints its doc comment, both when the markup
parses and when it is kept as the text that was written because it did not.
-/

open Lean Parser Elab Command

/--
Parses `src` as a command with Verso doc comments enabled, and logs the pretty-printed result.
-/
def ppVersoCommand (src : String) : CommandElabM Unit := do
  let env ← getEnv
  let pmctx : ParserModuleContext :=
    { env, options := (← getOptions).setBool `doc.verso true,
      currNamespace := ← getCurrNamespace, openDecls := ← getOpenDecls }
  let s := (andthenFn whitespace (categoryParserFnImpl `command)).run
    (mkInputContext src "<test>") pmctx (getTokenTable env) (mkParserState src)
  if let some err := s.errorMsg then throwError "parse error: {err}"
  logInfo (← liftCoreM <| PrettyPrinter.ppCommand ⟨s.stxStack.back⟩)

/-!
Markup that parses is printed from its syntax. A comment that fits on one line keeps its delimiters
on that line, and a comment whose content spans lines puts each delimiter on a line of its own.
-/

/--
info: /-- Some *emphasis* text. -/
def x :=
  1
-/
#guard_msgs in #eval ppVersoCommand "/-- Some *emphasis* text. -/ def x := 1"

/--
info: /--
First paragraph.

Second paragraph.
-/
def x :=
  1
-/
#guard_msgs in #eval ppVersoCommand "/-- First paragraph.\n\nSecond paragraph. -/ def x := 1"

/-! Markup that did not parse is printed as the text that was written. -/

/--
info: /-- An *unclosed emphasis. -/
def x :=
  1
-/
#guard_msgs in #eval ppVersoCommand "/-- An *unclosed emphasis. -/ def x := 1"

/--
info: /--
An *unclosed
emphasis.
-/
def x :=
  1
-/
#guard_msgs in #eval ppVersoCommand "/-- An *unclosed\nemphasis. -/ def x := 1"

/-!
An indented comment keeps its delimiters and its content at the column where the comment starts.
-/

/--
info: structure S where
  /--
  First paragraph.
  ⏎
  Second paragraph.
  -/
  x : Nat
  /-- One line. -/
  y : Nat
-/
#guard_msgs in
#eval ppVersoCommand <|
  "structure S where\n  /-- First paragraph.\n\n  Second paragraph. -/\n  x : Nat\n" ++
  "  /-- One line. -/\n  y : Nat"
