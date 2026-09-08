import Lean

/-!
This file tests that the name of a footnote or link reference is limited to the characters that
Verso's concrete syntax represents. Names that come from parsing are limited by the parser, and
names that come from quotation are checked while the document is elaborated.
-/

set_option doc.verso true

open Lean Doc Elab Term
open scoped Lean.Doc.Syntax

def target := ()

-- Elaborates the given blocks as documentation for `target`.
def runBlocks (blocks : TSyntaxArray ``Parser.block) : TermElabM Unit :=
  discard <| (elabBlocks blocks).exec ``target (mkNullNode #[])

-- A backslash is an ordinary character everywhere that Verso escapes it, so it is not a name
-- character.

/--
@ +2:3...4
error: expected a character other than '^', '[', '\', or a tab
-/
#guard_msgs (positions := true) in
/--
[^a\b]: note
-/
def backslashInFootnoteName := 0

/--
@ +2:9...10
error: expected a character other than '^', '[', '\', or a tab
-/
#guard_msgs (positions := true) in
/--
See [t][a\b] here.
-/
def backslashInRefTarget := 0

/--
@ +2:2...3
error: expected a character other than '^', '[', '\', or a tab
-/
#guard_msgs (positions := true) in
/--
[a\b]: http://example.com
-/
def backslashInLinkRefName := 0

-- Quotation builds a name from a string, which may contain any character at all.

/-- error: A reference name may not contain ']' -/
#guard_msgs in
#eval show TermElabM Unit from do
  runBlocks #[↑(← `(block| [^"a]b"]: "note"))]

/-- error: A reference name may not contain '\\' -/
#guard_msgs in
#eval show TermElabM Unit from do
  runBlocks #[↑(← `(block| ["a\\b"]: "http://example.com"))]

/-- error: A reference name may not be empty -/
#guard_msgs in
#eval show TermElabM Unit from do
  runBlocks #[↑(← `(block| [^""]: "note"))]

/-- error: A reference name may not contain '\n' -/
#guard_msgs in
#eval show TermElabM Unit from do
  runBlocks #[↑(← `(block| para[footnote("a\nb")]))]

-- A name of ordinary characters elaborates.

/-- info: ok -/
#guard_msgs in
#eval show TermElabM Unit from do
  runBlocks #[↑(← `(block| para[footnote("a b")])), ↑(← `(block| [^"a b"]: "note"))]
  logInfo "ok"
