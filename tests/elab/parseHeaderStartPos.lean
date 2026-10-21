module

import Lean

/-!
Tests parsing module headers and subsequent commands in bounded regions of a larger source string,
including leading trivia, UTF-8 byte positions, and absolute diagnostic positions.
-/

open Lean Parser

private def check (ok : Bool) (what : String) : IO Unit :=
  unless ok do throw <| IO.userError what

private def fixture (content : String) : InputContext × String.Pos.Raw × String.Pos.Raw := Id.run do
  let preamble := "Verso λ before\n```leanInit\n"
  let source := preamble ++ content ++ "```\nimport OutsideTheRegion\n"
  let start := preamble.rawEndPos
  let stop := (preamble ++ content).rawEndPos
  if h : stop ≤ source.rawEndPos then
    return (InputContext.mk source "fixture" stop h, start, stop)
  else
    panic! "invalid fixture"

private def checkLeading (stx : Syntax) (start : String.Pos.Raw) (content : String) : IO Unit := do
  let some (.original leading ..) := stx.getHeadInfo?
    | throw <| IO.userError "missing original source information"
  check (leading.startPos == start && leading.toString == content) "incorrect leading trivia"

#eval do
  let ctx := mkInputContext "-- file comment\nimport Init\n#check Nat\n" "ordinary"
  let (header, state, messages) ← parseHeader ctx
  let (explicitHeader, explicitState, explicitMessages) ← parseHeader ctx 0
  check (!messages.hasErrors && !explicitMessages.hasErrors &&
    header.raw.eqWithInfo explicitHeader.raw &&
    state.pos == explicitState.pos && state.recovering == explicitState.recovering &&
    state.hasLeading == explicitState.hasLeading) "default start differs from explicit zero"
  checkLeading header 0 "-- file comment\n"

-- Each first header token must retain the region's comments, including the `module` token.
#eval do
  for content in ["import Init\n", "prelude\n", "module\npublic import Init\n"] do
    let trivia := "  /- embedded λ -/\n"
    let (ctx, start, stop) := fixture (trivia ++ content)
    let (header, state, messages) ← parseHeader ctx start
    check (!messages.hasErrors && state.pos == stop && !state.hasLeading)
      "header did not stop at the region boundary"
    checkLeading header start trivia
    check (header.raw.getPos? == some (start + trivia))
      "header token lost its absolute byte position"

-- Adjacent import tokens outside the region must not become part of the header.
#eval do
  let source := "λ\nimport Init\nimport Outside\n"
  let start := "λ\n".rawEndPos
  let stop := "λ\nimport Init\n".rawEndPos
  let ctx := InputContext.mk source "imports" stop (by decide)
  let (header, state, messages) ← parseHeader ctx start
  check (!messages.hasErrors && header.raw[2].getArgs.size == 1 && state.pos == stop)
    "parsed an import beyond the region boundary"

-- An empty header defers its leading trivia to the first command, but not the second.
#eval do
  let trivia := "  -- embedded λ\n  "
  let (ctx, start, stop) := fixture (trivia ++ "def α := 1\ndef β := 2\n")
  let (_, state, messages) ← parseHeader ctx start
  check (!messages.hasErrors && state.hasLeading && state.leadingStartPos == start)
    "empty header lost the region start"
  let env ← mkEmptyEnvironment
  let (first, state, messages) := parseCommand ctx { env, options := {} } state messages
  check (!messages.hasErrors && !state.hasLeading && state.leadingStartPos == start)
    "first command did not consume initial trivia"
  checkLeading first start trivia
  check (first.getPos? == some (start + trivia)) "command position is not absolute"
  let (second, state, messages) := parseCommand ctx { env, options := {} } state messages
  check (!messages.hasErrors && state.pos == stop) "second command did not reach the region end"
  checkLeading second (start + trivia + "def α := 1\n") ""
  let (eoi, state, messages) := parseCommand ctx { env, options := {} } state messages
  check (!messages.hasErrors && eoi.isOfKind ``Command.eoi && state.pos == stop)
    "command parser escaped the region"

-- Empty and trivia-only regions transfer their leading trivia to the end-of-input token.
#eval do
  let env ← mkEmptyEnvironment
  for content in ["", " \n", "-- comment λ\n", "/- comment λ -/"] do
    let (ctx, start, stop) := fixture content
    let (_, state, messages) ← parseHeader ctx start
    check (!messages.hasErrors && state.pos == stop && state.hasLeading)
      "empty region did not produce an empty header"
    let (eoi, state, messages) := parseCommand ctx { env, options := {} } state messages
    check (!messages.hasErrors && eoi.isOfKind ``Command.eoi && eoi.getPos? == some stop &&
      state.pos == stop && !state.hasLeading) "incorrect end-of-input token"
    checkLeading eoi start content

-- Both header validation and parser errors use the enclosing source's file map.
#eval do
  let (ctx, start, _) := fixture "public import Init\n"
  let (_, _, messages) ← parseHeader ctx start
  let [message] := messages.toList
    | throw <| IO.userError "expected one header validation error"
  check (message.fileName == ctx.fileName && message.pos == ctx.fileMap.toPosition start &&
    message.endPos == some (ctx.fileMap.toPosition (start + "public")))
    "header validation error lost its absolute range"
  let (ctx, start, stop) := fixture "import\n"
  let (_, state, messages) ← parseHeader ctx start
  let [message] := messages.toList
    | throw <| IO.userError "expected one parser error"
  check (state.recovering && message.pos == ctx.fileMap.toPosition stop)
    "parser error lost its absolute position"

-- The whole parsed region must round-trip without including the surrounding source.
#eval do
  let env ← mkEmptyEnvironment
  for content in ["", "  -- comment λ\n", "  /- comment λ -/\nimport Init\n",
      "  -- comment λ\ndef α := 1\ndef β := 2\n",
      "module\nprelude\nimport Init\n-- command comment\ndef α := 1\n"] do
    let (ctx, start, _) := fixture content
    let (header, state, messages) ← parseHeader ctx start
    let commands ← testParseModuleAux env ctx state messages #[]
    let stx := mkNode ``Module.module #[header, mkListNode commands]
    check (stx.raw.reprint == some content) "parsed region did not round-trip"

-- Starting positions must use the context's normalized source, rather than the original bytes.
#eval do
  let original := "λ\r\nimport Init\r\n"
  let originalStart := "λ\r\n".rawEndPos
  let ctx := mkInputContext original "crlf"
  let start := ctx.fileMap.ofPosition ((FileMap.ofString original).toPosition originalStart)
  let (header, state, messages) ← parseHeader ctx start
  check (!messages.hasErrors && header.raw[2].getArgs.size == 1 &&
    header.raw.getPos? == some start && state.pos == ctx.endPos)
    "header position did not use the normalized source"
  check (header.raw.reprint == some "import Init\n") "normalized header did not round-trip"
