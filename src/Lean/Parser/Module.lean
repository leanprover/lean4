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
def «import»   := leading_parser "import " >> optional "runtime" >> ident
def header     := leading_parser optional («prelude» >> ppLine) >> many («import» >> ppLine) >> ppLine
/--
  Parser for a Lean module. We never actually run this parser but instead use the imperative definitions below that
  return the same syntax tree structure, but add error recovery. Still, it is helpful to have a `Parser` definition
  for it in order to auto-generate helpers such as the pretty printer. -/
@[runBuiltinParserAttributeHooks]
def module     := leading_parser header >> many (commandParser >> ppLine >> ppLine)

def updateTokens (c : ParserContext) : ParserContext :=
  { c with
    tokens := match addParserTokens c.tokens header.info with
      | Except.ok tables => tables
      | Except.error _   => unreachable! }

end Module

structure ModuleParserState where
  pos        : String.Pos := 0
  recovering : Bool       := false
  deriving Inhabited

private def mkErrorMessage (c : ParserContext) (pos : String.Pos) (errorMsg : String) : Message :=
  let pos := c.fileMap.toPosition pos
  { fileName := c.fileName, pos := pos, data := errorMsg }

def parseHeader (inputCtx : InputContext) : IO (Syntax × ModuleParserState × MessageLog) := do
  let dummyEnv ← mkEmptyEnvironment
  let ctx := mkParserContext inputCtx { env := dummyEnv, options := {} }
  let ctx := Module.updateTokens ctx
  let s   := mkParserState ctx.input
  let s   := whitespace ctx s
  let s   := Module.header.fn ctx s
  let stx := s.stxStack.back
  match s.errorMsg with
  | some errorMsg =>
    let msg := mkErrorMessage ctx s.pos (toString errorMsg)
    pure (stx, { pos := s.pos, recovering := true }, { : MessageLog }.add msg)
  | none =>
    pure (stx, { pos := s.pos }, {})

private def mkEOI (pos : String.Pos) : Syntax :=
  let atom := mkAtom (SourceInfo.original "".toSubstring pos "".toSubstring pos) ""
  Syntax.node `Lean.Parser.Module.eoi #[atom]

def isEOI (s : Syntax) : Bool :=
  s.isOfKind `Lean.Parser.Module.eoi

def isExitCommand (s : Syntax) : Bool :=
  s.isOfKind `Lean.Parser.Command.exit

private def consumeInput (c : ParserContext) (pos : String.Pos) : String.Pos :=
  let s : ParserState := { cache := initCacheForInput c.input, pos := pos }
  let s := tokenFn [] c s
  match s.errorMsg with
  | some _ => pos + 1
  | none   => s.pos

def topLevelCommandParserFn : ParserFn :=
  commandParser.fn

partial def parseCommand (inputCtx : InputContext) (pmctx : ParserModuleContext) (s : ModuleParserState) (messages : MessageLog) : Syntax × ModuleParserState × MessageLog :=
  let rec parse (s : ModuleParserState) (messages : MessageLog) :=
    let { pos := pos, recovering := recovering } := s
    if inputCtx.input.atEnd pos then
      (mkEOI pos, s, messages)
    else
      let c   := mkParserContext inputCtx pmctx
      let s   := { cache := initCacheForInput c.input, pos := pos : ParserState }
      let s   := whitespace c s
      let s   := topLevelCommandParserFn c s
      match s.errorMsg with
      | none =>
         (s.stxStack.back, { pos := s.pos }, messages)
      | some errorMsg =>
        -- advance at least one token to prevent infinite loops
        let pos := if s.pos == pos then consumeInput c s.pos else s.pos
        /- We ignore commands where `getPos?` is none. This happens only on commands that have a prefix comprised of optional elements.
           For example, unification hints start with `optional («scoped» <|> «local»)`.
           We claim a syntactically incorrect command containing no token or identifier is irrelevant for intellisense and should be ignored. -/
        let ignore := s.stxStack.isEmpty || s.stxStack.back.getPos?.isNone
        let messages := if recovering && ignore then messages else messages.add <| mkErrorMessage c s.pos (toString errorMsg)
        if ignore then
          parse { pos := pos, recovering := true } messages
        else
          (s.stxStack.back, { pos := pos, recovering := true }, messages)
  parse s messages

-- only useful for testing since most Lean files cannot be parsed without elaboration

partial def testParseModuleAux (env : Environment) (inputCtx : InputContext) (s : ModuleParserState) (msgs : MessageLog) (stxs  : Array Syntax) : IO (Array Syntax) :=
  let rec parse (state : ModuleParserState) (msgs : MessageLog) (stxs : Array Syntax) :=
    match parseCommand inputCtx { env := env, options := {} } state msgs with
    | (stx, state, msgs) =>
      if isEOI stx then
        if msgs.isEmpty then
          pure stxs
        else do
          msgs.forM fun msg => msg.toString >>= IO.println
          throw (IO.userError "failed to parse file")
      else
        parse state msgs (stxs.push stx)
  parse s msgs stxs

def testParseModule (env : Environment) (fname contents : String) : IO Syntax := do
  let inputCtx := mkInputContext contents fname
  let (header, state, messages) ← parseHeader inputCtx
  let cmds ← testParseModuleAux env inputCtx state messages #[]
  let stx := Syntax.node `Lean.Parser.Module.module #[header, mkListNode cmds]
  pure stx.updateLeading

def testParseFile (env : Environment) (fname : System.FilePath) : IO Syntax := do
  let contents ← IO.FS.readFile fname
  testParseModule env fname.toString contents

end Parser
end Lean
