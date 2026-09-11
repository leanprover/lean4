import Lean

/-!
Tests that the whitespace after a doc comment's opening delimiter is the delimiter's trailing
whitespace, and that text which reads as a Lean comment is part of the comment's body.
-/

open Lean Elab Command

def parseCommand (src : String) : CommandElabM Syntax := do
  match Parser.runParserCategory (← getEnv) `command src with
  | .ok stx => pure stx
  | .error e => throwError e

/--
Shows the opening delimiter of the first doc comment in `src`, the whitespace that follows it, and
the body.
-/
def showDocAtoms (src : String) : CommandElabM Unit := do
  let stx ← parseCommand src
  let some doc := stx.find? fun s =>
      s.isOfKind ``Parser.Command.docComment || s.isOfKind ``Parser.Command.moduleDoc
    | throwError "no doc comment"
  let trailing := (doc[0].getTrailing?.map (·.toString)).getD ""
  logInfo m!"delimiter {repr doc[0].getAtomVal}, whitespace {repr trailing}, \
    body {repr doc[1].getAtomVal}"

def ppCommandSrc (src : String) : CommandElabM Unit := do
  logInfo (← liftCoreM <| PrettyPrinter.ppCommand ⟨← parseCommand src⟩)

/-! The delimiter records the whitespace, and the body starts at the text. -/

/-- info: delimiter "/--", whitespace " ", body "foo -/" -/
#guard_msgs in #eval showDocAtoms "/-- foo -/ def x := 1"

/-- info: delimiter "/--", whitespace "\n", body "a\n  b\n    c\n-/" -/
#guard_msgs in #eval showDocAtoms "/--\na\n  b\n    c\n-/\ndef x := 1"

/-- info: delimiter "/-!", whitespace " ", body "Module doc -/" -/
#guard_msgs in #eval showDocAtoms "/-! Module doc -/"

/-!
Text right after the opening delimiter that looks like a comment is part of the body, not a comment.
-/

/-- info: delimiter "/--", whitespace " ", body "--verbose turns on logging -/" -/
#guard_msgs in #eval showDocAtoms "/-- --verbose turns on logging -/ def x := 1"

/-- info: delimiter "/--", whitespace " ", body "/- nested -/ text -/" -/
#guard_msgs in #eval showDocAtoms "/-- /- nested -/ text -/ def x := 1"

/-! The stored doc strings do not include the whitespace after the opening delimiter. -/

/-- foo -/
def a := 1

/--
  Indented text.
  More text.
-/
def b := 1

/-- --verbose turns on logging -/
def c := 1

/-- /- nested -/ text -/
def d := 1

/-!   Module doc with leading spaces. -/

/--
info: some "foo "
some "Indented text.\nMore text.\n"
some "--verbose turns on logging "
some "/- nested -/ text "
-/
#guard_msgs in
#eval show MetaM Unit from do
  for n in [``a, ``b, ``c, ``d] do
    IO.println (repr (← findDocString? (← getEnv) n))

/-- info: some "Module doc with leading spaces. " -/
#guard_msgs in
#eval show MetaM Unit from do
  IO.println (repr ((getMainModuleDoc (← getEnv)).toList.getLast?.map (·.doc)))

/-! Errors in manual links are reported at the position of the link. -/

/--
@ +2:25...40
error: Unknown documentation type `f`. Expected one of the following: `section`, `errorExplanation`
-/
#guard_msgs (positions := true) in
/--
    See the manual at [](lean-manual://f).
-/
def e := 1

/-! The pretty printer puts one space after the opening delimiter. -/

/--
info: /-- A doc -/
def x :=
  1
-/
#guard_msgs in #eval ppCommandSrc "/-- A doc -/ def x := 1"

/--
info: /-- A doc
  more
-/
def x :=
  1
-/
#guard_msgs in #eval ppCommandSrc "/--\nA doc\n  more\n-/ def x := 1"

/-- info: /-! Module doc -/ -/
#guard_msgs in #eval ppCommandSrc "/-! Module doc -/"

/-! A Verso docstring reads the same text. -/

def printVersoBlocks (name : Name) : CommandElabM Unit := do
  match (← findInternalDocString? (← getEnv) name) with
  | some (.inr v) => IO.println (repr v.text)
  | some (.inl md) => IO.println s!"Markdown: {md}"
  | none => IO.println "no docstring"

set_option doc.verso true in
/-- --verbose turns on logging -/
def versoLine := 1

set_option doc.verso true in
/-- /- nested -/ text -/
def versoBlock := 1

/--
info: #[Lean.Doc.Block.para #[Lean.Doc.Inline.text "--verbose turns on logging "]]
#[Lean.Doc.Block.para #[Lean.Doc.Inline.text "/- nested -/ text "]]
-/
#guard_msgs in
#eval do printVersoBlocks ``versoLine; printVersoBlocks ``versoBlock
