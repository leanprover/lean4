/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Language.Lean
import Lean.Util.Profile
import Lean.Server.References

namespace Lean.Elab.Frontend

structure State where
  commandState : Command.State
  parserState  : Parser.ModuleParserState
  cmdPos       : String.Pos
  commands     : Array Syntax := #[]

structure Context where
  inputCtx : Parser.InputContext

abbrev FrontendM := ReaderT Context $ StateRefT State IO

def setCommandState (commandState : Command.State) : FrontendM Unit :=
  modify fun s => { s with commandState := commandState }

@[inline] def runCommandElabM (x : Command.CommandElabM α) : FrontendM α := do
  let ctx ← read
  let s ← get
  let cmdCtx : Command.Context := {
    cmdPos       := s.cmdPos
    fileName     := ctx.inputCtx.fileName
    fileMap      := ctx.inputCtx.fileMap
    tacticCache? := none
  }
  match (← liftM <| EIO.toIO' <| (x cmdCtx).run s.commandState) with
  | Except.error e      => throw <| IO.Error.userError s!"unexpected internal error: {← e.toMessageData.toString}"
  | Except.ok (a, sNew) => setCommandState sNew; return a

def elabCommandAtFrontend (stx : Syntax) : FrontendM Unit := do
  runCommandElabM do
    let initMsgs ← modifyGet fun st => (st.messages, { st with messages := {} })
    Command.elabCommandTopLevel stx
    let mut msgs := (← get).messages
    -- `stx.hasMissing` should imply `initMsgs.hasErrors`, but the latter should be cheaper to check
    -- in general
    if !Language.Lean.showPartialSyntaxErrors.get (← getOptions) && initMsgs.hasErrors &&
        stx.hasMissing then
      -- discard elaboration errors, except for a few important and unlikely misleading ones, on
      -- parse error
      msgs := ⟨msgs.msgs.filter fun msg =>
        msg.data.hasTag (fun tag => tag == `Elab.synthPlaceholder ||
          tag == `Tactic.unsolvedGoals || (`_traceMsg).isSuffixOf tag)⟩
    modify ({ · with messages := initMsgs ++ msgs })

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
  let scope := cmdState.scopes.head!
  let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  match profileit "parsing" scope.opts fun _ => Parser.parseCommand ictx pmctx pstate cmdState.messages with
  | (cmd, ps, messages) =>
    modify fun s => { s with commands := s.commands.push cmd }
    setParserState ps
    setMessages messages
    elabCommandAtFrontend cmd
    pure (Parser.isTerminalCommand cmd)

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

builtin_initialize
  registerTraceClass `Elab.info

@[export lean_run_frontend]
def runFrontend
    (input : String)
    (opts : Options)
    (fileName : String)
    (mainModuleName : Name)
    (trustLevel : UInt32 := 0)
    (ileanFileName? : Option String := none)
    (messagesAsJson : Bool := false)
    : IO (Environment × Bool) := do
  let inputCtx := Parser.mkInputContext input fileName
  -- TODO: replace with `#lang` processing
  if /- Lean #lang? -/ true then
    -- Temporarily keep alive old cmdline driver for the Lean language so that we don't pay the
    -- overhead of passing the environment between snapshots until we actually make good use of it
    -- outside the server
    let (header, parserState, messages) ← Parser.parseHeader inputCtx
    -- allow `env` to be leaked, which would live until the end of the process anyway
    let (env, messages) ← processHeader (leakEnv := true) header opts messages inputCtx trustLevel
    let env := env.setMainModule mainModuleName
    let mut commandState := Command.mkState env messages opts

    if ileanFileName?.isSome then
      -- Collect InfoTrees so we can later extract and export their info to the ilean file
      commandState := { commandState with infoState.enabled := true }

    let s ← IO.processCommands inputCtx parserState commandState
    Language.reportMessages s.commandState.messages opts messagesAsJson

    if let some ileanFileName := ileanFileName? then
      let trees := s.commandState.infoState.trees.toArray
      let references ←
        Lean.Server.findModuleRefs inputCtx.fileMap trees (localVars := false) |>.toLspModuleRefs
      let ilean := { module := mainModuleName, references : Lean.Server.Ilean }
      IO.FS.writeFile ileanFileName $ Json.compress $ toJson ilean

    return (s.commandState.env, !s.commandState.messages.hasErrors)

  let ctx := { inputCtx with mainModuleName, opts, trustLevel }
  let processor := Language.Lean.process
  let snap ← processor none ctx
  let snaps := Language.toSnapshotTree snap
  snaps.runAndReport opts messagesAsJson
  if let some ileanFileName := ileanFileName? then
    let trees := snaps.getAll.concatMap (match ·.infoTree? with | some t => #[t] | _ => #[])
    let references := Lean.Server.findModuleRefs inputCtx.fileMap trees (localVars := false)
    let ilean := { module := mainModuleName, references := ← references.toLspModuleRefs : Lean.Server.Ilean }
    IO.FS.writeFile ileanFileName $ Json.compress $ toJson ilean

  let hasErrors := snaps.getAll.any (·.diagnostics.msgLog.hasErrors)
  -- TODO: remove default when reworking cmdline interface in Lean; currently the only case
  -- where we use the environment despite errors in the file is `--stats`
  let env := Language.Lean.waitForFinalEnv? snap |>.getD (← mkEmptyEnvironment)
  pure (env, !hasErrors)


end Lean.Elab
