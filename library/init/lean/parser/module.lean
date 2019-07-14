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

structure ModuleReader :=
(context  : ParserContext)
(state    : ParserState)
(messages : MessageLog := {})

private def checkResult (r : ModuleReader) : Option Syntax × ModuleReader :=
let s   := r.state;
match r.state.errorMsg with
| some msg =>
  let c   := r.context;
  let pos := c.fileMap.toPosition s.pos;
  let msg := { Message . filename := c.filename, pos := pos, text := msg, caption := "parser" };
  (none, { messages := r.messages.add msg, .. r })
| none =>
  let stx := s.stxStack.back;
  let s   := s.popSyntax;
  (some stx, { state := s, .. r })

def mkModuleReader (env : Environment) (input : String) (fileName := "<input>") : Option Syntax × ModuleReader :=
let c := mkParserContext env input fileName;
let c := Module.updateTokens c;
let s := mkParserState input;
let s := whitespace c s;
let s := Module.header.fn (0:Nat) c s;
checkResult { context := c, state := s }

namespace ModuleReader

def isEOI (r : ModuleReader) : Bool :=
r.context.input.atEnd r.state.pos

def nextCommand : ModuleReader → Option Syntax × ModuleReader
| ⟨c, s, m⟩ :=
  let s := (commandParser : Parser).fn (0:Nat) c s;
  checkResult { context := c, state := s, messages := m }

end ModuleReader

end Parser
end Lean
