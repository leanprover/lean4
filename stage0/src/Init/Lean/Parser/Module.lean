/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Message
import Init.Lean.Parser.Command

namespace Lean
namespace Parser

namespace Module
def «prelude»  := parser! "prelude"
def «import»   := parser! "import " >> optional "runtime" >> ident
def header     := parser! optional «prelude» >> many «import»

def updateTokens (c : ParserContext) : ParserContext :=
{ tokens := match addParserTokens c.tokens header.info with
    | Except.ok tables => tables
    | Except.error _   => unreachable!,
  .. c }

end Module

structure ModuleParserState :=
(pos        : String.Pos := 0)
(recovering : Bool       := false)

instance ModuleParserState.inhabited : Inhabited ModuleParserState :=
⟨{}⟩

private def mkErrorMessage (c : ParserContext) (pos : String.Pos) (errorMsg : String) : Message :=
let pos := c.fileMap.toPosition pos;
{ fileName := c.fileName, pos := pos, data := errorMsg }

def parseHeader (env : Environment) (inputCtx : InputContext) : Syntax × ModuleParserState × MessageLog :=
let ctx := mkParserContext env inputCtx;
let ctx := Module.updateTokens ctx;
let s   := mkParserState ctx.input;
let s   := whitespace ctx s;
let s   := Module.header.fn (0:Nat) ctx s;
let stx := s.stxStack.back;
match s.errorMsg with
| some errorMsg =>
  let msg := mkErrorMessage ctx s.pos (toString errorMsg);
  (stx, { pos := s.pos, recovering := true }, { MessageLog . }.add msg)
| none =>
  (stx, { pos := s.pos }, {})

private def mkEOI (pos : String.Pos) : Syntax :=
let atom := mkAtom { pos := pos, trailing := "".toSubstring, leading := "".toSubstring } "";
Syntax.node `Lean.Parser.Module.eoi #[atom]

def isEOI (s : Syntax) : Bool :=
s.isOfKind `Lean.Parser.Module.eoi

def isExitCommand (s : Syntax) : Bool :=
s.isOfKind `Lean.Parser.Command.exit

private def consumeInput (c : ParserContext) (pos : String.Pos) : String.Pos :=
let s : ParserState := { cache := initCacheForInput c.input, pos := pos };
let s := tokenFn c s;
match s.errorMsg with
| some _ => pos + 1
| none   => s.pos

partial def parseCommand (env : Environment) (inputCtx : InputContext) : ModuleParserState → MessageLog → Syntax × ModuleParserState × MessageLog
| s@{ pos := pos, recovering := recovering }, messages =>
  if inputCtx.input.atEnd pos then
    (mkEOI pos, s, messages)
  else
    let c  := mkParserContext env inputCtx;
    let s  := { ParserState . cache := initCacheForInput c.input, pos := pos };
    let s  := whitespace c s;
    let s  := (commandParser : Parser).fn (0:Nat) c s;
    match s.errorMsg with
    | none =>
      let stx := s.stxStack.back;
      (stx, { pos := s.pos }, messages)
    | some errorMsg =>
      if recovering then
        parseCommand { pos := consumeInput c s.pos, recovering := true } messages
      else
        let msg      := mkErrorMessage c s.pos (toString errorMsg);
        let messages := messages.add msg;
        parseCommand { pos := consumeInput c s.pos, recovering := true } messages

private partial def testModuleParserAux (env : Environment) (inputCtx : InputContext) (displayStx : Bool) : ModuleParserState → MessageLog → IO Bool
| s, messages =>
  match parseCommand env inputCtx s messages with
  | (stx, s, messages) =>
    if isEOI stx || isExitCommand stx then do
      messages.forM $ fun msg => IO.println msg;
      pure (!messages.hasErrors)
    else do
      when displayStx (IO.println stx);
      testModuleParserAux s messages

@[export lean_test_module_parser]
def testModuleParser (env : Environment) (input : String) (fileName := "<input>") (displayStx := false) : IO Bool :=
timeit (fileName ++ " parser") $ do
  let inputCtx           := mkInputContext input fileName;
  let (stx, s, messages) := parseHeader env inputCtx;
  when displayStx (IO.println stx);
  testModuleParserAux env inputCtx displayStx s messages

partial def parseFileAux (env : Environment) (inputCtx : InputContext) : ModuleParserState → MessageLog → Array Syntax → IO Syntax
| state, msgs, stxs =>
  match parseCommand env inputCtx state msgs with
  | (stx, state, msgs) =>
    if isEOI stx then
      if msgs.isEmpty then
        let stx := mkListNode stxs;
        pure stx.updateLeading
      else do
        msgs.forM $ fun msg => IO.println msg;
        throw (IO.userError "failed to parse file")
    else
      parseFileAux state msgs (stxs.push stx)

def parseFile (env : Environment) (fname : String) : IO Syntax := do
fname ← IO.realPath fname;
contents ← IO.readTextFile fname;
let inputCtx := mkInputContext contents fname;
let (stx, state, messages) := parseHeader env inputCtx;
parseFileAux env inputCtx state messages #[stx]

end Parser
end Lean
