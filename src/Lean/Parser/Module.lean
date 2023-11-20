/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Message
import Lean.Parser.Command

namespace Lean
namespace Parser

namespace Module
def «prelude»  := leading_parser "prelude"
-- `optional (checkNoWsBefore >> "." >> checkNoWsBefore >> ident)`
-- can never fully succeed but ensures that `import (runtime)? <ident>.`
-- produces a partial syntax that contains the dot.
-- The partial syntax is useful for import dot-auto-completion.
def «import»   := leading_parser "import " >> optional "runtime" >> ident >> optional (checkNoWsBefore >> "." >> checkNoWsBefore >> ident)
def header     := leading_parser optional («prelude» >> ppLine) >> many («import» >> ppLine) >> ppLine
/--
  Parser for a Lean module. We never actually run this parser but instead use the imperative definitions below that
  return the same syntax tree structure, but add error recovery. Still, it is helpful to have a `Parser` definition
  for it in order to auto-generate helpers such as the pretty printer. -/
@[run_builtin_parser_attribute_hooks]
def module     := leading_parser header >> many (commandParser >> ppLine >> ppLine)

def updateTokens (tokens : TokenTable) : TokenTable :=
  match addParserTokens tokens header.info with
    | Except.ok tables => tables
    | Except.error _   => unreachable!

end Module

structure ModuleParserState where
  pos        : String.Pos := 0
  recovering : Bool       := false
  deriving Inhabited

private def mkErrorMessage (c : InputContext) (s : ParserState) (e : Parser.Error) : Message := Id.run do
  let mut pos := s.pos
  let mut endPos? := none
  let mut e := e
  unless e.unexpectedTk.isMissing do
    -- calculate error parts too costly to do eagerly
    if let some r := e.unexpectedTk.getRange? then
      pos := r.start
      endPos? := some r.stop
    let unexpected := match e.unexpectedTk with
      | .ident .. => "unexpected identifier"
      | .atom _ v => s!"unexpected token '{v}'"
      | _         => "unexpected token"  -- TODO: categorize (custom?) literals as well?
    e := { e with unexpected }
    -- if there is an unexpected token, include preceding whitespace as well as the expected token could
    -- be inserted at any of these places to fix the error; see tests/lean/1971.lean
    if let .original (trailing := trailing) .. := s.stxStack.back.getTailInfo then
      if trailing.stopPos == pos then
        pos := trailing.startPos
  { fileName := c.fileName
    pos := c.fileMap.toPosition pos
    endPos := c.fileMap.toPosition <$> endPos?
    keepFullRange := true
    data := toString e }

def parseHeader (inputCtx : InputContext) : IO (Syntax × ModuleParserState × MessageLog) := do
  let dummyEnv ← mkEmptyEnvironment
  let p   := andthenFn whitespace Module.header.fn
  let tokens := Module.updateTokens (getTokenTable dummyEnv)
  let s   := p.run inputCtx { env := dummyEnv, options := {} } tokens (mkParserState inputCtx.input)
  let stx := if s.stxStack.isEmpty then .missing else s.stxStack.back
  match s.errorMsg with
  | some errorMsg =>
    let msg := mkErrorMessage inputCtx s errorMsg
    pure (stx, { pos := s.pos, recovering := true }, { : MessageLog }.add msg)
  | none =>
    pure (stx, { pos := s.pos }, {})

private def mkEOI (pos : String.Pos) : Syntax :=
  let atom := mkAtom (SourceInfo.original "".toSubstring pos "".toSubstring pos) ""
  mkNode ``Command.eoi #[atom]

def isTerminalCommand (s : Syntax) : Bool :=
  s.isOfKind ``Command.exit || s.isOfKind ``Command.import || s.isOfKind ``Command.eoi

private def consumeInput (inputCtx : InputContext) (pmctx : ParserModuleContext) (pos : String.Pos) : String.Pos :=
  let s : ParserState := { cache := initCacheForInput inputCtx.input, pos := pos }
  let s := tokenFn [] |>.run inputCtx pmctx (getTokenTable pmctx.env) s
  match s.errorMsg with
  | some _ => pos + ' '
  | none   => s.pos

def topLevelCommandParserFn : ParserFn :=
  commandParser.fn

partial def parseCommand (inputCtx : InputContext) (pmctx : ParserModuleContext) (mps : ModuleParserState) (messages : MessageLog) : Syntax × ModuleParserState × MessageLog := Id.run do
  let mut pos := mps.pos
  let mut recovering := mps.recovering
  let mut messages := messages
  let mut stx := Syntax.missing  -- will always be assigned below
  repeat
    if inputCtx.input.atEnd pos then
      stx := mkEOI pos
      break
    let pos' := pos
    let p := andthenFn whitespace topLevelCommandParserFn
    let s := p.run inputCtx pmctx (getTokenTable pmctx.env) { cache := initCacheForInput inputCtx.input, pos }
    pos := s.pos
    if recovering && !s.stxStack.isEmpty && s.stxStack.back.isAntiquot then
      -- top-level antiquotation during recovery is most likely remnant from unfinished quotation, ignore
      continue
    match s.errorMsg with
    | none =>
      stx := s.stxStack.back
      recovering := false
      break
    | some errorMsg =>
      -- advance at least one token to prevent infinite loops
      if pos == pos' then
        pos := consumeInput inputCtx pmctx pos
      /- We ignore commands where `getPos?` is none. This happens only on commands that have a prefix comprised of optional elements.
          For example, unification hints start with `optional («scoped» <|> «local»)`.
          We claim a syntactically incorrect command containing no token or identifier is irrelevant for intellisense and should be ignored. -/
      let ignore := s.stxStack.isEmpty || s.stxStack.back.getPos?.isNone
      unless recovering && ignore do
        messages := messages.add <| mkErrorMessage inputCtx s errorMsg
      recovering := true
      if ignore then
        continue
      else
        stx := s.stxStack.back
        break
  return (stx, { pos, recovering }, messages)

-- only useful for testing since most Lean files cannot be parsed without elaboration

partial def testParseModuleAux (env : Environment) (inputCtx : InputContext) (s : ModuleParserState) (msgs : MessageLog) (stxs  : Array Syntax) : IO (Array Syntax) :=
  let rec parse (state : ModuleParserState) (msgs : MessageLog) (stxs : Array Syntax) :=
    match parseCommand inputCtx { env := env, options := {} } state msgs with
    | (stx, state, msgs) =>
      if isTerminalCommand stx then
        if msgs.isEmpty then
          pure stxs
        else do
          msgs.forM fun msg => msg.toString >>= IO.println
          throw (IO.userError "failed to parse file")
      else
        parse state msgs (stxs.push stx)
  parse s msgs stxs

def testParseModule (env : Environment) (fname contents : String) : IO (TSyntax ``Parser.Module.module) := do
  let inputCtx := mkInputContext contents fname
  let (header, state, messages) ← parseHeader inputCtx
  let cmds ← testParseModuleAux env inputCtx state messages #[]
  let stx := mkNode `Lean.Parser.Module.module #[header, mkListNode cmds]
  pure ⟨stx.raw.updateLeading⟩

def testParseFile (env : Environment) (fname : System.FilePath) : IO (TSyntax ``Parser.Module.module) := do
  let contents ← IO.FS.readFile fname
  testParseModule env fname.toString contents

end Parser
end Lean
