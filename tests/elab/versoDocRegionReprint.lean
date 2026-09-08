import Lean

/-!
Checks that parsing a docstring region of a larger file produces syntax that reprints to exactly
that region. Docstring elaboration starts the parser after the opening `/--`, bounds it before the
closing `-/`, and derives a base column for indented docstrings. The parser corpus tests parse
whole files from position zero, so only this test covers the region and the indentation.
-/

open Lean Doc Parser Elab Command

/--
Checks that exactly one token's source info accounts for every byte of the region between
`startPos` and `endPos`, in order. Each token's leading whitespace begins where the previous
token's trailing whitespace ended, and the final trailing whitespace ends at `endPos`.
-/
partial def checkCoverage (startPos endPos : String.Pos.Raw) (stx : Syntax) :
    Except String Unit := do
  let frontier ← go stx startPos
  unless frontier == endPos do
    throw s!"bytes [{frontier.byteIdx}, {endPos.byteIdx}) are not covered by any token"
where
  tokenInfo (info : SourceInfo) (frontier : String.Pos.Raw) : Except String String.Pos.Raw := do
    let .original leading pos trailing stop := info
      | throw "token without original source info"
    unless leading.startPos == frontier && leading.stopPos == pos do
      throw s!"leading of token at {pos.byteIdx} covers \
        [{leading.startPos.byteIdx}, {leading.stopPos.byteIdx}), \
        expected [{frontier.byteIdx}, {pos.byteIdx})"
    unless trailing.startPos == stop do
      throw s!"trailing of token at {pos.byteIdx} starts at {trailing.startPos.byteIdx}, \
        expected {stop.byteIdx}"
    return trailing.stopPos
  go (stx : Syntax) (frontier : String.Pos.Raw) : Except String String.Pos.Raw := do
    match stx with
    | .node _ _ args => args.foldlM (fun f a => go a f) frontier
    | .atom info _ => tokenInfo info frontier
    | .ident info _ _ _ => tokenInfo info frontier
    | .missing => return frontier

/--
Parses the region of `source` between the first `/--` and the first following `-/` the way
docstring elaboration does, and reports whether the result reprints to exactly the region.
-/
def regionRoundTrip (label : String) (source : String) : IO Unit := do
  let openBytes := (source.splitOn "/--").head!.utf8ByteSize
  let startPos : String.Pos.Raw := ⟨openBytes + 3⟩
  let closeBytes := (source.splitOn "-/").head!.utf8ByteSize
  let endPos : String.Pos.Raw := ⟨closeBytes⟩
  if h : endPos ≤ source.rawEndPos then
    let text := FileMap.ofString source
    let ictx : InputContext := ⟨source, "<input>", text, endPos, h⟩
    let env : Environment ← mkEmptyEnvironment
    let pmctx : ParserModuleContext := {env, options := {}}
    let blockCtxt := BlockCtxt.forDocString text startPos endPos
    let s := mkParserState source |>.setPos startPos
    let s := (documentFn blockCtxt).run ictx pmctx (getTokenTable env) s
    unless s.allErrors.isEmpty do
      throw <| IO.userError s!"{label}: parse errors: {s.allErrors.map (fun (p, _, e) => (p, toString e))}"
    let stop :=
      if (String.Pos.Raw.extract source s.pos endPos).all Char.isWhitespace then endPos else s.pos
    let expected := String.Pos.Raw.extract source startPos stop
    let reprintVerdict :=
      match s.stxStack.back.reprint with
      | some actual =>
        if actual == expected then "reprints to the region"
        else s!"MISMATCH\n  region:  {expected.quote}\n  reprint: {actual.quote}"
      | none => "REPRINT FAILED"
    let coverageVerdict :=
      match checkCoverage startPos stop s.stxStack.back with
      | .ok () => "every byte covered"
      | .error e => s!"COVERAGE FAILED: {e}"
    IO.println s!"{label}: {reprintVerdict}; {coverageVerdict}"
  else
    throw <| IO.userError s!"{label}: no doc comment found"

/--
info: plain: reprints to the region; every byte covered
multi-block: reprints to the region; every byte covered
leading blank line: reprints to the region; every byte covered
trailing blank lines: reprints to the region; every byte covered
indented: reprints to the region; every byte covered
indented with list: reprints to the region; every byte covered
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  regionRoundTrip "plain" "def foo := 3\n/-- Hello *world*! -/\ndef bar := 4\n"
  regionRoundTrip "multi-block"
    "/-- First paragraph.\n\n* a\n* b\n\n```\ncode\n```\n-/\ndef bar := 4\n"
  regionRoundTrip "leading blank line" "/--\n\nText after a blank line. -/\ndef x := ()\n"
  regionRoundTrip "trailing blank lines" "/-- Text before blank lines.\n\n\n-/\ndef x := ()\n"
  regionRoundTrip "indented"
    "structure S where\n  /-- An indented docstring.\n      With a second line. -/\n  f : Nat\n"
  regionRoundTrip "indented with list"
    "structure S where\n  /-- Indented.\n\n  * a\n  * b\n  -/\n  f : Nat\n"
