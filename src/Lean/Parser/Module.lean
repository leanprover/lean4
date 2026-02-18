/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
module

prelude
public import Lean.Parser.Command
import Init.While
meta import Lean.Parser.Extra

public section

set_option compiler.postponeCompile false  -- TODO

namespace Lean
namespace Parser

namespace Module
def moduleTk   := leading_parser "module"
def «prelude»  := leading_parser "prelude"
def «public»   := leading_parser (withAnonymousAntiquot := false) "public"
def «meta»     := leading_parser (withAnonymousAntiquot := false) "meta"
def «all»      := leading_parser (withAnonymousAntiquot := false) "all"
def «import»   := leading_parser
  atomic (optional «public» >> optional «meta» >> "import ") >>
  optional all >>
  identWithPartialTrailingDot
def header     := leading_parser optional (moduleTk >> ppLine >> ppLine) >>
  optional («prelude» >> ppLine) >>
  many («import» >> ppLine) >>
  ppLine

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
  pos        : String.Pos.Raw := 0
  recovering : Bool       := false
  deriving Inhabited

private partial def mkErrorMessage (c : InputContext) (pos : String.Pos.Raw) (stk : SyntaxStack) (e : Parser.Error) : Message := Id.run do
  let mut pos := pos
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
    if let some trailing := lastTrailing stk then
      if trailing.stopPos == pos then
        pos := trailing.startPos
  { fileName := c.fileName
    pos := c.fileMap.toPosition pos
    endPos := c.fileMap.toPosition <$> endPos?
    keepFullRange := true
    data := toString e }
where
  -- Error recovery might lead to there being some "junk" on the stack
  lastTrailing (s : SyntaxStack) : Option Substring.Raw :=
    Id.run <| s.toSubarray.findSomeRevM? fun stx =>
      if let .original (trailing := trailing) .. := stx.getTailInfo then pure (some trailing)
        else none

def parseHeader (inputCtx : InputContext) : IO (TSyntax ``Module.header × ModuleParserState × MessageLog) := do
  let dummyEnv ← mkEmptyEnvironment
  let p   := andthenFn whitespace Module.header.fn
  let tokens := Module.updateTokens (getTokenTable dummyEnv)
  let s   := p.run inputCtx { env := dummyEnv, options := {} } tokens (mkParserState inputCtx.inputString)
  let stx := if s.stxStack.isEmpty then .missing else s.stxStack.back
  let mut messages : MessageLog := {}
  for (pos, stk, err) in s.allErrors do
    messages := messages.add <| mkErrorMessage inputCtx pos stk err
  if let `(Module.header| $[module%$moduleTk?]? $[prelude]? $importsStx*) := stx then
    let mkError ref msg : Message :=
      let pos := ref.getPos?.getD 0
      {
        fileName := inputCtx.fileName
        pos := inputCtx.fileMap.toPosition pos
        endPos := inputCtx.fileMap.toPosition <| ref.getTailPos?.getD pos
        keepFullRange := true
        data := msg
      }
    for stx in importsStx do
      if let `(Module.import| $[public%$pubTk?]? $[meta%$metaTk?]? import $[all%$allTk?]? $mod) := stx then
        let mod := mod.getId
        if moduleTk?.isNone then
          if let some tk := pubTk? then
            messages := messages.add <| mkError tk "cannot use `public import` without `module`"
          if let some tk := metaTk? then
            messages := messages.add <| mkError tk "cannot use `meta import` without `module`"
          if let some tk := allTk? then
            messages := messages.add <| mkError tk "cannot use `import all` without `module`"
        else
          if let some tk := allTk? then
            if pubTk?.isSome then
              messages := messages.add <| mkError tk s!"cannot use `all` with `public import`; \
                consider using separate `public import {mod}` and `import all {mod}` directives \
                in order to import public data into the public scope and private data into the \
                private scope."
  pure (⟨stx⟩, {pos := s.pos, recovering := s.hasError}, messages)

private def mkEOI (pos : String.Pos.Raw) : Syntax :=
  let atom := mkAtom (SourceInfo.original "".toRawSubstring pos "".toRawSubstring pos) ""
  mkNode ``Command.eoi #[atom]

def isTerminalCommand (s : Syntax) : Bool :=
  s.isOfKind ``Command.exit || s.isOfKind ``Command.import || s.isOfKind ``Command.eoi

private def consumeInput (inputCtx : InputContext) (pmctx : ParserModuleContext) (pos : String.Pos.Raw) : String.Pos.Raw :=
  let s : ParserState := { cache := initCacheForInput inputCtx.inputString, pos := pos }
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
    if inputCtx.atEnd pos then
      stx := mkEOI pos
      break
    let pos' := pos
    let p := andthenFn whitespace topLevelCommandParserFn
    let s := p.run inputCtx pmctx (getTokenTable pmctx.env) { cache := initCacheForInput inputCtx.inputString, pos }
    -- save errors from sub-recoveries
    for (rpos, rstk, recovered) in s.recoveredErrors do
      messages := messages.add <| mkErrorMessage inputCtx rpos rstk recovered
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
        messages := messages.add <| mkErrorMessage inputCtx s.pos s.stxStack errorMsg
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
        if !msgs.hasUnreported then
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
