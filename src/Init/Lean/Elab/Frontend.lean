/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Elab.Import
import Init.Lean.Elab.Command

namespace Lean
namespace Elab
namespace Frontend

structure State :=
(commandState : Command.State)
(parserState  : Parser.ModuleParserState)

abbrev FrontendM := ReaderT Parser.ParserContextCore (StateM State)

private def getCmdContext : FrontendM Command.Context := do
c ← read;
pure { fileName := c.fileName, fileMap := c.fileMap }

@[inline] def runCommandElabM (x : Command.CommandElabM Unit) : FrontendM Unit := do
fun ctx s =>
  let parserState := s.parserState;
  match x { fileName := ctx.fileName, fileMap := ctx.fileMap } s.commandState with
  | EStateM.Result.ok _ newCmdState     => ((), { commandState := newCmdState, parserState := parserState })
  | EStateM.Result.error ex newCmdState =>
    let newCmdState := { messages := newCmdState.messages.add ex, .. newCmdState };
    ((), { commandState := newCmdState, parserState := parserState })

def elabCommandAtFrontend (stx : Syntax) : FrontendM Unit :=
runCommandElabM (Command.elabCommand stx)

def updateCmdPos : FrontendM Unit :=
modify $ fun s => { commandState := { cmdPos := s.parserState.pos, .. s.commandState }, .. s }

def processCommand : FrontendM Bool := do
updateCmdPos;
s ← get;
let cs := s.commandState;
let ps := s.parserState;
c ← read;
match Parser.parseCommand cs.env c ps cs.messages with
| (cmd, ps, messages) => do
  set { commandState := { messages := messages, .. cs }, parserState := ps };
  if Parser.isEOI cmd || Parser.isExitCommand cmd then do
    pure true -- Done
  else do
    elabCommandAtFrontend cmd;
    pure false

partial def processCommandsAux : Unit → FrontendM Unit
| () => do
  done ← processCommand;
  if done then pure ()
  else processCommandsAux ()

def processCommands : FrontendM Unit :=
processCommandsAux ()

end Frontend

open Frontend

def process (input : String) (env : Environment) (opts : Options) (fileName : Option String := none) : Environment × MessageLog :=
let fileName        := fileName.getD "<input>";
let ctx             := Parser.mkParserContextCore env input fileName;
let cmdState        := Command.mkState env {} opts;
match (processCommands ctx).run { commandState := cmdState, parserState := {} } with
| (_, { commandState := { env := env, messages := messages, .. }, .. }) => (env, messages)

def testFrontend (input : String) (opts : Options := {}) (fileName : Option String := none) : IO (Environment × MessageLog) := do
env ← mkEmptyEnvironment;
let fileName := fileName.getD "<input>";
let ctx := Parser.mkParserContextCore env input fileName;
match Parser.parseHeader env ctx with
| (header, parserState, messages) => do
  (env, messages) ← processHeader header messages ctx;
  let cmdState := Command.mkState env messages opts;
  match (processCommands ctx).run { commandState := cmdState, parserState := parserState } with
  | (_, { commandState := { env := env, messages := messages, .. }, .. }) => pure (env, messages)

end Elab
end Lean
