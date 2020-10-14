/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Elab.Import
import Lean.Elab.Command

namespace Lean
namespace Elab
namespace Frontend

structure State :=
(commandState : Command.State)
(parserState  : Parser.ModuleParserState)
(cmdPos       : String.Pos)

structure Context :=
(inputCtx     : Parser.InputContext)

abbrev FrontendM := ReaderT Context $ StateRefT State IO

def setCommandState (commandState : Command.State) : FrontendM Unit :=
modify fun s => { s with commandState := commandState }

@[inline] def runCommandElabM (x : Command.CommandElabM Unit) : FrontendM Unit := do
ctx ← read;
s ← get;
let cmdCtx : Command.Context := { cmdPos := s.cmdPos, fileName := ctx.inputCtx.fileName, fileMap := ctx.inputCtx.fileMap };
sNew? ← liftM $ EIO.toIO (fun _ => IO.Error.userError "unexpected error") (do (_, s) ← (x cmdCtx).run s.commandState; pure $ some s);
match sNew? with
| some sNew => setCommandState sNew
| none      => pure ()

def elabCommandAtFrontend (stx : Syntax) : FrontendM Unit :=
runCommandElabM (Command.elabCommand stx)

def updateCmdPos : FrontendM Unit := do
modify fun s => { s with cmdPos := s.parserState.pos }

def getParserState : FrontendM Parser.ModuleParserState := do s ← get; pure s.parserState
def getCommandState : FrontendM Command.State := do s ← get; pure s.commandState
def setParserState (ps : Parser.ModuleParserState) : FrontendM Unit := modify fun s => { s with parserState := ps }
def setMessages (msgs : MessageLog) : FrontendM Unit := modify fun s => { s with commandState := { s.commandState with messages := msgs } }
def getInputContext : FrontendM Parser.InputContext := do ctx ← read; pure ctx.inputCtx

def processCommand : FrontendM Bool := do
updateCmdPos;
cmdState    ← getCommandState;
parserState ← getParserState;
inputCtx    ← getInputContext;
match Parser.parseCommand cmdState.env inputCtx parserState cmdState.messages with
| (cmd, ps, messages) => do
  setParserState ps;
  setMessages messages;
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

def IO.processCommands (inputCtx : Parser.InputContext) (parserState : Parser.ModuleParserState) (commandState : Command.State) : IO Command.State := do
(_, s) ← (processCommands.run { inputCtx := inputCtx }).run { commandState := commandState, parserState := parserState, cmdPos := parserState.pos };
pure s.commandState

def process (input : String) (env : Environment) (opts : Options) (fileName : Option String := none) : IO (Environment × MessageLog) := do
let fileName   := fileName.getD "<input>";
let inputCtx   := Parser.mkInputContext input fileName;
commandState ← IO.processCommands inputCtx { : Parser.ModuleParserState } (Command.mkState env {} opts);
pure (commandState.env, commandState.messages)

@[export lean_process_input]
def processExport (env : Environment) (input : String) (opts : Options) (fileName : String) : IO (Environment × List Message) := do
(env, messages) ← process input env opts fileName;
pure (env, messages.toList)

@[export lean_run_frontend]
def runFrontend (env : Environment) (input : String) (opts : Options) (fileName : String) : IO (Environment × List Message) := do
let inputCtx := Parser.mkInputContext input fileName;
match Parser.parseHeader env inputCtx with
| (header, parserState, messages) => do
  (env, messages) ← processHeader header messages inputCtx;
  cmdState ← IO.processCommands inputCtx parserState (Command.mkState env messages opts);
  pure (cmdState.env, cmdState.messages.toList)

end Elab
end Lean
