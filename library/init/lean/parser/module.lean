/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.lean.message
import init.lean.parser.command

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

structure ModuleParser :=
(context    : ParserContextCore)
(pos        : String.Pos := 0)
(messages   : MessageLog := {})
(recovering : Bool := false)

instance ModuleParser.inhabited : Inhabited ModuleParser :=
⟨{context := default _}⟩

private def mkErrorMessage (c : ParserContext) (pos : String.Pos) (errorMsg : String) : Message :=
let pos := c.fileMap.toPosition pos;
{ filename := c.filename, pos := pos, text := errorMsg }

def mkModuleParser (env : Environment) (input : String) (fileName := "<input>") : Option Syntax × ModuleParser :=
let c   := mkParserContext env input fileName;
let c   := Module.updateTokens c;
let s   := mkParserState input;
let s   := whitespace c s;
let s   := Module.header.fn (0:Nat) c s;
match s.errorMsg with
| some errorMsg =>
  let msg := mkErrorMessage c s.pos errorMsg;
  (none, { context := c.toParserContextCore, pos := s.pos, messages := { MessageLog . }.add msg, recovering := true })
| none =>
  let stx := s.stxStack.back;
  (stx, { context := c.toParserContextCore, pos := s.pos })

private def mkEOI (pos : String.Pos) : Syntax :=
let atom := Syntax.atom (some { pos := pos, trailing := "".toSubstring, leading := "".toSubstring }) "";
Syntax.node `Lean.Parser.Module.eoi [atom].toArray

def isEOI (s : Syntax) : Bool :=
s.isOfKind `Lean.Parser.Module.eoi

private def consumeInput (c : ParserContext) (pos : String.Pos) : String.Pos :=
let s : ParserState := { cache := initCacheForInput c.input, pos := pos };
let s := tokenFn c s;
match s.errorMsg with
| some _ => pos + 1
| none   => s.pos

partial def parseCommand (env : Environment) : ModuleParser → Syntax × ModuleParser
| p :=
  if p.context.input.atEnd p.pos then
    (mkEOI p.pos, p)
  else
    let c : ParserContext := { env := env, .. p.context };
    let s : ParserState   := { cache := initCacheForInput c.input, pos := p.pos };
    let s := (commandParser : Parser).fn (0:Nat) c s;
    match s.errorMsg with
    | none =>
      let stx := s.stxStack.back;
      let p   := { pos := s.pos, recovering := false, .. p };
      (stx, p)
    | some errorMsg =>
      if p.recovering then
        let p := { pos := consumeInput c s.pos, .. p };
        parseCommand p
      else
        let msg := mkErrorMessage c s.pos errorMsg;
        let p   := { pos := s.pos, recovering := true, messages := p.messages.add msg, .. p };
        parseCommand p

end Parser
end Lean
