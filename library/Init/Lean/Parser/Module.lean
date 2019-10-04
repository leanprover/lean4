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
def importPath := parser! many (rawCh '.' true) >> ident
def «import»   := parser! "import " >> many1 importPath
def header     := parser! optional «prelude» >> many «import»

def updateTokens (c : ParserContext) : ParserContext :=
{ tokens := match header.info.updateTokens c.tokens with
    | Except.ok tables => tables
    | Except.error _   => {}, -- unreachable
  .. c }

end Module

structure ModuleParserState :=
(pos        : String.Pos := 0)
(recovering : Bool       := false)

instance ModuleParserState.inhabited : Inhabited ModuleParserState :=
⟨{}⟩

private def mkErrorMessage (c : ParserContext) (pos : String.Pos) (errorMsg : String) : Message :=
let pos := c.fileMap.toPosition pos;
{ fileName := c.fileName, pos := pos, text := errorMsg }

def parseHeader (env : Environment) (c : ParserContextCore) : Syntax × ModuleParserState × MessageLog :=
let c   := c.toParserContext env;
let c   := Module.updateTokens c;
let s   := mkParserState c.input;
let s   := whitespace c s;
let s   := Module.header.fn (0:Nat) c s;
let stx := s.stxStack.back;
match s.errorMsg with
| some errorMsg =>
  let msg := mkErrorMessage c s.pos (toString errorMsg);
  (stx, { pos := s.pos, recovering := true }, { MessageLog . }.add msg)
| none =>
  (stx, { pos := s.pos }, {})

private def mkEOI (pos : String.Pos) : Syntax :=
let atom := mkAtom { pos := pos, trailing := "".toSubstring, leading := "".toSubstring } "";
Syntax.node `Lean.Parser.Module.eoi [atom].toArray

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

partial def parseCommand (env : Environment) (c : ParserContextCore) : ModuleParserState → MessageLog → Syntax × ModuleParserState × MessageLog
| s@{ pos := pos, recovering := recovering }, messages =>
  if c.input.atEnd pos then
    (mkEOI pos, s, messages)
  else
    let c  := c.toParserContext env;
    let s  := { ParserState . cache := initCacheForInput c.input, pos := pos };
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

private partial def testModuleParserAux (env : Environment) (c : ParserContextCore) (displayStx : Bool) : ModuleParserState → MessageLog → IO Bool
| s, messages =>
  match parseCommand env c s messages with
  | (stx, s, messages) =>
    if isEOI stx || isExitCommand stx then do
      messages.toList.mfor $ fun msg => IO.println msg;
      pure (!messages.hasErrors)
    else do
      when displayStx (IO.println stx);
      testModuleParserAux s messages

@[export lean_test_module_parser]
def testModuleParser (env : Environment) (input : String) (fileName := "<input>") (displayStx := false) : IO Bool :=
timeit (fileName ++ " parser") $ do
  let ctx                := mkParserContextCore env input fileName;
  let (stx, s, messages) := parseHeader env ctx;
  when displayStx (IO.println stx);
  testModuleParserAux env ctx displayStx s messages

partial def parseFileAux (env : Environment) (ctx : ParserContextCore) : ModuleParserState → MessageLog → Array Syntax → IO Syntax
| state, msgs, stxs =>
  match parseCommand env ctx state msgs with
  | (stx, state, msgs) =>
    if isEOI stx then
      if msgs.isEmpty then
        let stx := mkListNode stxs;
        pure stx.updateLeading
      else do
        msgs.toList.mfor $ fun msg => IO.println msg;
        throw (IO.userError "failed to parse file")
    else
      parseFileAux state msgs (stxs.push stx)

def parseFile (env : Environment) (fname : String) : IO Syntax :=
do
fname ← IO.realPath fname;
contents ← IO.readTextFile fname;
let ctx := mkParserContextCore env contents fname;
let (stx, state, messages) := parseHeader env ctx;
parseFileAux env ctx state messages (Array.singleton stx)

end Parser
end Lean
