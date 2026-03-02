-- Tests that file-start whitespace and comments are associated with the leading
-- of the first actual token in the file (in the module header or first command).
import Lean

open Lean Parser

/-- Parse a header string and return the leading Substring.Raw of the first token. -/
def getFirstTokenLeading (input : String) : IO (Option Substring.Raw) := do
  let inputCtx := mkInputContext input "<test>"
  let (header, _, _) ← parseHeader inputCtx
  return match header.raw.getHeadInfo? with
    | some (.original leading ..) => some leading
    | _ => none

-- Test 1: file-start line comment before import
-- The leading of the `import` keyword should start at position 0 and contain the comment.
/--
info: leading startPos: 0
leading content: -- file-start comment
 -/
#guard_msgs in
#eval do
  let some leading ← getFirstTokenLeading "-- file-start comment\nimport Foo\n"
    | IO.println "no leading found"
  IO.println s!"leading startPos: {leading.startPos.byteIdx}"
  IO.println s!"leading content: {Substring.Raw.toString leading}"

-- Test 2: file-start block comment before import
/--
info: leading startPos: 0
leading content: /- block comment -/
 -/
#guard_msgs in
#eval do
  let some leading ← getFirstTokenLeading "/- block comment -/\nimport Foo\n"
    | IO.println "no leading found"
  IO.println s!"leading startPos: {leading.startPos.byteIdx}"
  IO.println s!"leading content: {Substring.Raw.toString leading}"

-- Test 3: no file-start whitespace (import is the very first thing)
-- The leading should start at position 0 with stopPos 0 (empty leading).
/--
info: leading startPos: 0
leading stopPos: 0 -/
#guard_msgs in
#eval do
  let some leading ← getFirstTokenLeading "import Foo\n"
    | IO.println "no leading found"
  IO.println s!"leading startPos: {leading.startPos.byteIdx}"
  IO.println s!"leading stopPos: {leading.stopPos.byteIdx}"

-- Test 4: file with only newlines at the start (no comments)
/--
info: leading startPos: 0
leading content:

 -/
#guard_msgs in
#eval do
  let some leading ← getFirstTokenLeading "\n\nimport Foo\n"
    | IO.println "no leading found"
  IO.println s!"leading startPos: {leading.startPos.byteIdx}"
  IO.println s!"leading content: {Substring.Raw.toString leading}"

-- Test 5: entirely empty file (only a comment, no header or body)
-- The EOI token's leading should include the file-start comment.
/--
info: first token leading startPos: 0
first token leading content: -- just a comment
 -/
#guard_msgs in
#eval do
  let env ← mkEmptyEnvironment
  let stx ← testParseModule env "<test>" "-- just a comment\n"
  match stx.getHeadInfo? with
  | some (.original leading ..) =>
    IO.println s!"first token leading startPos: {leading.startPos.byteIdx}"
    IO.println s!"first token leading content: {Substring.Raw.toString leading}"
  | _ => IO.println "no original leading found"

-- Test 6: empty header (no imports) - file-start comment before a def
-- The leading of the first command token should include the file-start comment.
/--
info: first token leading startPos: 0
first token leading content: -- file-start comment
 -/
#guard_msgs in
#eval do
  let env ← mkEmptyEnvironment
  let stx ← testParseModule env "<test>" "-- file-start comment\ndef foo := 1\n"
  match stx.getHeadInfo? with
  | some (.original leading ..) =>
    IO.println s!"first token leading startPos: {leading.startPos.byteIdx}"
    IO.println s!"first token leading content: {Substring.Raw.toString leading}"
  | _ => IO.println "no original leading found"
