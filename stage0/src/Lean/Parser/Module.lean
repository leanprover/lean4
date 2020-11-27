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
def «prelude»  := parser! "prelude"
def «import»   := parser! "import " >> optional "runtime" >> ident
def header     := parser! optional («prelude» >> ppLine) >> many («import» >> ppLine) >> ppLine
/--
  Parser for a Lean module. We never actually run this parser but instead use the imperative definitions below that
  return the same syntax tree structure, but add error recovery. Still, it is helpful to have a `Parser` definition
  for it in order to auto-generate helpers such as the pretty printer. -/
@[runBuiltinParserAttributeHooks]
def module     := parser! header >> many (commandParser >> ppLine >> ppLine)

def updateTokens (c : ParserContext) : ParserContext :=
  { c with
    tokens := match addParserTokens c.tokens header.info with
      | Except.ok tables => tables
      | Except.error _   => unreachable! }

end Module

structure ModuleParserState where
  pos        : String.Pos := 0
  recovering : Bool       := false

instance : Inhabited ModuleParserState := ⟨{}⟩

private def mkErrorMessage (c : ParserContext) (pos : String.Pos) (errorMsg : String) : Message :=
  let pos := c.fileMap.toPosition pos
  { fileName := c.fileName, pos := pos, data := errorMsg }

def parseHeader (inputCtx : InputContext) : IO (Syntax × ModuleParserState × MessageLog) := do
  let dummyEnv ← mkEmptyEnvironment
  let ctx := mkParserContext dummyEnv inputCtx
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
  let atom := mkAtom { pos := pos, trailing := "".toSubstring, leading := "".toSubstring } ""
  Syntax.node `Lean.Parser.Module.eoi #[atom]

def isEOI (s : Syntax) : Bool :=
  s.isOfKind `Lean.Parser.Module.eoi

def isExitCommand (s : Syntax) : Bool :=
  s.isOfKind `Lean.Parser.Command.exit

private def consumeInput (c : ParserContext) (pos : String.Pos) : String.Pos :=
  let s : ParserState := { cache := initCacheForInput c.input, pos := pos }
  let s := tokenFn c s
  match s.errorMsg with
  | some _ => pos + 1
  | none   => s.pos

def topLevelCommandParserFn : ParserFn :=
  orelseFnCore
    commandParser.fn
    (andthenFn (lookaheadFn termParser.fn) (errorFn "expected command, but found term; this error may be due to parsing precedence levels, consider parenthesizing the term"))
    false /- do not merge errors -/

partial def parseCommand (env : Environment) (inputCtx : InputContext) (s : ModuleParserState) (messages : MessageLog) : Syntax × ModuleParserState × MessageLog :=
  let rec parse (s : ModuleParserState) (messages : MessageLog) :=
    let { pos := pos, recovering := recovering } := s
    if inputCtx.input.atEnd pos then
      (mkEOI pos, s, messages)
    else
      let c   := mkParserContext env inputCtx
      let s   := { cache := initCacheForInput c.input, pos := pos : ParserState }
      let s   := whitespace c s
      let s   := topLevelCommandParserFn c s
      let stx := s.stxStack.back
      match s.errorMsg with
      | none => (stx, { pos := s.pos }, messages)
      | some errorMsg =>
        -- advance at least one token to prevent infinite loops
        let pos := if s.pos == pos then consumeInput c s.pos else s.pos
        if recovering then
          parse { pos := pos, recovering := true } messages
        else
          let msg      := mkErrorMessage c s.pos (toString errorMsg)
          let messages := messages.add msg
          -- We should replace the following line with commented one if we want to elaborate commands containing Syntax errors.
          -- This is useful for implementing features such as autocompletion.
          -- Right now, it is disabled since `match_syntax` fails on "partial" `Syntax` objects.
          parse { pos := pos, recovering := true } messages
          -- (stx, { pos := pos, recovering := true }, messages)
  parse s messages

private partial def testModuleParserAux (env : Environment) (inputCtx : InputContext) (displayStx : Bool) (s : ModuleParserState) (messages : MessageLog) : IO Bool :=
  let rec loop (s : ModuleParserState) (messages : MessageLog) := do
    match parseCommand env inputCtx s messages with
    | (stx, s, messages) =>
      if isEOI stx || isExitCommand stx then
        messages.forM fun msg => msg.toString >>= IO.println
        pure (!messages.hasErrors)
      else
        if displayStx then IO.println stx
        loop s messages
  loop s messages

@[export lean_test_module_parser]
def testModuleParser (env : Environment) (input : String) (fileName := "<input>") (displayStx := false) : IO Bool :=
  timeit (fileName ++ " parser") do
    let inputCtx           := mkInputContext input fileName
    let (stx, s, messages) ← parseHeader inputCtx
    if displayStx then IO.println stx
    testModuleParserAux env inputCtx displayStx s messages

partial def parseModuleAux (env : Environment) (inputCtx : InputContext) (s : ModuleParserState) (msgs : MessageLog) (stxs  : Array Syntax) : IO (Array Syntax) :=
  let rec parse (state : ModuleParserState) (msgs : MessageLog) (stxs : Array Syntax) :=
    match parseCommand env inputCtx state msgs with
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

def parseModule (env : Environment) (fname contents : String) : IO Syntax := do
  let fname ← IO.realPath fname
  let inputCtx := mkInputContext contents fname
  let (header, state, messages) ← parseHeader inputCtx
  let cmds ← parseModuleAux env inputCtx state messages #[]
  let stx := Syntax.node `Lean.Parser.Module.module #[header, mkListNode cmds]
  pure stx.updateLeading

def parseFile (env : Environment) (fname : String) : IO Syntax := do
  let contents ← IO.FS.readFile fname
  parseModule env fname contents

end Parser
end Lean
