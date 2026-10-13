import Lean

/-!
Tests how a doc comment's whitespace is divided from its text. The opening delimiter's trailing
whitespace runs up to the text, and the text's trailing whitespace runs up to the closing delimiter,
so the stored doc string includes neither. Text that reads as a Lean comment belongs to the body.
-/

open Lean Elab Command

def parseCommand (src : String) : CommandElabM Syntax := do
  match Parser.runParserCategory (← getEnv) `command src with
  | .ok stx => pure stx
  | .error e => throwError e

/--
Shows the atoms of the first doc comment in `src`: its opening delimiter, its text, and its closing
delimiter, the first two with the whitespace that follows them.
-/
def showDocAtoms (src : String) : CommandElabM Unit := do
  let stx ← parseCommand src
  let some doc := stx.find? fun s =>
      s.isOfKind ``Parser.Command.docComment || s.isOfKind ``Parser.Command.moduleDoc
    | throwError "no doc comment"
  let trailing (a : Syntax) := (a.getTrailing?.map (·.toString)).getD ""
  logInfo m!"delimiter {repr doc[0].getAtomVal}, whitespace {repr (trailing doc[0])}, \
    text {repr doc[1][0].getAtomVal}, whitespace {repr (trailing doc[1][0])}, \
    closer {repr doc[1][1].getAtomVal}"

def ppCommandSrc (src : String) : CommandElabM Unit := do
  logInfo (← liftCoreM <| PrettyPrinter.ppCommand ⟨← parseCommand src⟩)

/-!
The delimiter records the whitespace before the text, and the text records the whitespace before
the closing delimiter.
-/

/-- info: delimiter "/--", whitespace " ", text "foo", whitespace " ", closer "-/" -/
#guard_msgs in #eval showDocAtoms "/-- foo -/ def x := 1"

/-- info: delimiter "/--", whitespace "\n", text "a\n  b\n    c", whitespace "\n", closer "-/" -/
#guard_msgs in #eval showDocAtoms "/--\na\n  b\n    c\n-/\ndef x := 1"

/-- info: delimiter "/-!", whitespace " ", text "Module doc", whitespace " ", closer "-/" -/
#guard_msgs in #eval showDocAtoms "/-! Module doc -/"

/-!
Text right after the opening delimiter that looks like a comment is part of the body, not a comment.
-/

/-- info: delimiter "/--", whitespace " ", text "--verbose turns on logging", whitespace " ", closer "-/" -/
#guard_msgs in #eval showDocAtoms "/-- --verbose turns on logging -/ def x := 1"

/-- info: delimiter "/--", whitespace " ", text "/- nested -/ text", whitespace " ", closer "-/" -/
#guard_msgs in #eval showDocAtoms "/-- /- nested -/ text -/ def x := 1"

/-!
The stored doc strings do not include the whitespace after the opening delimiter or before the
closing one.
-/

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
info: some "foo"
some "Indented text.\nMore text."
some "--verbose turns on logging"
some "/- nested -/ text"
-/
#guard_msgs in
#eval show MetaM Unit from do
  for n in [``a, ``b, ``c, ``d] do
    IO.println (repr (← findDocString? (← getEnv) n))

/-- info: some "Module doc with leading spaces." -/
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

/-!
A documentation comment built in code reads back its text, and takes a position from `src` only.
-/

/--
info: "Built text", has a position: false
"Built text", position copied: true
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let src ← parseCommand "def x := 1"
  let loose := mkMarkdownDocComment "Built text"
  let placed := mkMarkdownDocCommentFrom src "Built text"
  IO.println s!"{repr loose.getDocString}, has a position: {loose.raw.getPos?.isSome}"
  let copied := placed.raw.getPos? == src.getPos?
  IO.println s!"{repr placed.getDocString}, position copied: {copied}"
