/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Elab.Import
import Lean.Elab.Command
import Lean.Util.Profile

namespace Lean.Elab.Frontend

structure State :=
  (commandState : Command.State)
  (parserState  : Parser.ModuleParserState)
  (cmdPos       : String.Pos)
  (commands     : Array Syntax := #[])

structure Context :=
  (inputCtx     : Parser.InputContext)

abbrev FrontendM := ReaderT Context $ StateRefT State IO

def setCommandState (commandState : Command.State) : FrontendM Unit :=
  modify fun s => { s with commandState := commandState }

@[inline] def runCommandElabM (x : Command.CommandElabM Unit) : FrontendM Unit := do
  let ctx ← read
  let s ← get
  let cmdCtx : Command.Context := { cmdPos := s.cmdPos, fileName := ctx.inputCtx.fileName, fileMap := ctx.inputCtx.fileMap }
  let sNew? ← liftM $ EIO.toIO (fun _ => IO.Error.userError "unexpected error") (do let (_, s) ← (x cmdCtx).run s.commandState; pure $ some s)
  match sNew? with
  | some sNew => setCommandState sNew
  | none      => pure ()

def elabCommandAtFrontend (stx : Syntax) : FrontendM Unit := do
  runCommandElabM (Command.elabCommand stx)

def updateCmdPos : FrontendM Unit := do
  modify fun s => { s with cmdPos := s.parserState.pos }

def getParserState : FrontendM Parser.ModuleParserState := do pure (← get).parserState
def getCommandState : FrontendM Command.State := do pure (← get).commandState
def setParserState (ps : Parser.ModuleParserState) : FrontendM Unit := modify fun s => { s with parserState := ps }
def setMessages (msgs : MessageLog) : FrontendM Unit := modify fun s => { s with commandState := { s.commandState with messages := msgs } }
def getInputContext : FrontendM Parser.InputContext := do pure (← read).inputCtx

def processCommand : FrontendM Bool := do
  updateCmdPos
  let cmdState ← getCommandState
  let ictx ← getInputContext
  let pstate ← getParserState
  let pos := ictx.fileMap.toPosition pstate.pos
  match profileit "parsing" pos fun _ => Parser.parseCommand cmdState.env ictx pstate cmdState.messages with
  | (cmd, ps, messages) =>
    modify fun s => { s with commands := s.commands.push cmd }
    setParserState ps
    setMessages messages
    if Parser.isEOI cmd || Parser.isExitCommand cmd then
      pure true -- Done
    else
      profileitM IO.Error "elaboration" pos $ elabCommandAtFrontend cmd
      pure false

partial def processCommands : FrontendM Unit := do
  let done ← processCommand
  unless done do
    processCommands

end Frontend

open Frontend

def IO.processCommands (inputCtx : Parser.InputContext) (parserState : Parser.ModuleParserState) (commandState : Command.State) : IO State := do
  let (_, s) ← (Frontend.processCommands.run { inputCtx := inputCtx }).run { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }
  pure s

def process (input : String) (env : Environment) (opts : Options) (fileName : Option String := none) : IO (Environment × MessageLog) := do
  let fileName   := fileName.getD "<input>"
  let inputCtx   := Parser.mkInputContext input fileName
  let s ← IO.processCommands inputCtx { : Parser.ModuleParserState } (Command.mkState env {} opts)
  pure (s.commandState.env, s.commandState.messages)

@[export lean_process_input]
def processExport (env : Environment) (input : String) (opts : Options) (fileName : String) : IO (Environment × List Message) := do
  let (env, messages) ← process input env opts fileName
  pure (env, messages.toList)

@[export lean_run_frontend]
def runFrontend (input : String) (opts : Options) (fileName : String) (mainModuleName : Name) : IO (Environment × List Message × Module) := do
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx
  let env := env.setMainModule mainModuleName
  let s ← IO.processCommands inputCtx parserState (Command.mkState env messages opts)
  pure (s.commandState.env, s.commandState.messages.toList, { header := header, commands := s.commands })

end Lean.Elab
