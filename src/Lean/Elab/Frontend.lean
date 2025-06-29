/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Language.Lean
import Lean.Util.Profile
import Lean.Server.References
import Lean.Util.Profiler

namespace Lean.Elab.Frontend

structure State where
  commandState : Command.State
  parserState  : Parser.ModuleParserState
  cmdPos       : String.Pos
  commands     : Array Syntax := #[]
deriving Nonempty

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
    snap?        := none
    cancelTk?    := none
  }
  match (← liftM <| EIO.toIO' <| (x cmdCtx).run s.commandState) with
  | Except.error e      => throw <| IO.Error.userError s!"unexpected internal error: {← e.toMessageData.toString}"
  | Except.ok (a, sNew) => setCommandState sNew; return a

def elabCommandAtFrontend (stx : Syntax) : FrontendM Unit := do
  runCommandElabM do
    let initMsgs ← modifyGet fun st => (st.messages, { st with messages := {} })
    Command.elabCommandTopLevel stx
    let mut msgs := (← get).messages
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

structure IncrementalState extends State where
  inputCtx    : Parser.InputContext
  initialSnap : Language.Lean.CommandParsedSnapshot
deriving Nonempty

open Language in
/--
Variant of `IO.processCommands` that allows for potential incremental reuse. Pass in the result of a
previous invocation done with the same state (but usually different input context) to allow for
reuse.
-/
partial def IO.processCommandsIncrementally (inputCtx : Parser.InputContext)
    (parserState : Parser.ModuleParserState) (commandState : Command.State)
    (old? : Option IncrementalState) :
    BaseIO IncrementalState := do
  let task ← Language.Lean.processCommands inputCtx parserState commandState
    (old?.map fun old => (old.inputCtx, old.initialSnap))
  go task.get task #[]
where
  go initialSnap t commands :=
    let snap := t.get
    let commands := commands.push snap
    if let some next := snap.nextCmdSnap? then
      go initialSnap next.task commands
    else
      -- Opting into reuse also enables incremental reporting, so make sure to collect messages from
      -- all snapshots
      let messages := toSnapshotTree initialSnap
        |>.getAll.map (·.diagnostics.msgLog)
        |>.foldl (· ++ ·) {}
      -- In contrast to messages, we should collect info trees only from the top-level command
      -- snapshots as they subsume any info trees reported incrementally by their children.
      let trees := commands.map (·.elabSnap.infoTreeSnap.get.infoTree?) |>.filterMap id |>.toPArray'
      return {
        commandState := { snap.elabSnap.resultSnap.get.cmdState with messages, infoState.trees := trees }
        parserState := snap.parserState
        cmdPos := snap.parserState.pos
        commands := commands.map (·.stx)
        inputCtx, initialSnap
      }

def IO.processCommands (inputCtx : Parser.InputContext) (parserState : Parser.ModuleParserState)
    (commandState : Command.State) : IO State := do
  let st ← IO.processCommandsIncrementally inputCtx parserState commandState none
  return st.toState

def process (input : String) (env : Environment) (opts : Options) (fileName : Option String := none) : IO (Environment × MessageLog) := do
  let fileName   := fileName.getD "<input>"
  let inputCtx   := Parser.mkInputContext input fileName
  let s ← IO.processCommands inputCtx { : Parser.ModuleParserState } (Command.mkState env {} opts)
  pure (s.commandState.env, s.commandState.messages)

def runFrontend
    (input : String)
    (opts : Options)
    (fileName : String)
    (mainModuleName : Name)
    (trustLevel : UInt32 := 0)
    (oleanFileName? : Option System.FilePath := none)
    (ileanFileName? : Option System.FilePath := none)
    (jsonOutput : Bool := false)
    (errorOnKinds : Array Name := #[])
    (plugins : Array System.FilePath := #[])
    (printStats : Bool := false)
    (setup? : Option ModuleSetup := none)
    : IO (Option Environment) := do
  let startTime := (← IO.monoNanosNow).toFloat / 1000000000
  let inputCtx := Parser.mkInputContext input fileName
  let opts := Lean.internal.cmdlineSnapshots.setIfNotSet opts true
  -- default to async elaboration; see also `Elab.async` docs
  let opts := Elab.async.setIfNotSet opts true
  let ctx := { inputCtx with }
  let setup stx := do
    if let some setup := setup? then
      liftM <| setup.dynlibs.forM Lean.loadDynlib
      return .ok {
        trustLevel
        mainModuleName := setup.name
        isModule := strictOr setup.isModule stx.isModule
        imports := setup.imports?.getD stx.imports
        plugins := plugins ++ setup.plugins
        importArts := setup.importArts
        -- override cmdline options with setup options
        opts := opts.mergeBy (fun _ _ hOpt => hOpt) setup.options.toOptions
      }
    else
      return .ok {
        imports := stx.imports
        isModule := stx.isModule
        mainModuleName, opts, trustLevel, plugins
      }
  let processor := Language.Lean.process
  let snap ← processor setup none ctx
  let snaps := Language.toSnapshotTree snap
  let severityOverrides := errorOnKinds.foldl (·.insert · .error) {}

  -- reporting should be done before any early exit from the function
  let hasErrors ← snaps.runAndReport opts jsonOutput severityOverrides

  let some cmdState := Language.Lean.waitForFinalCmdState? snap
    | return none
  let env := cmdState.env
  let finalOpts := cmdState.scopes[0]!.opts

  -- stats should be displayed even if there are (non-import) errors
  if printStats then
    env.displayStats

  if hasErrors then
    return none

  if let some oleanFileName := oleanFileName? then
    profileitIO ".olean serialization" finalOpts do
      writeModule env oleanFileName

  if let some ileanFileName := ileanFileName? then
    let trees := snaps.getAll.flatMap (match ·.infoTree? with | some t => #[t] | _ => #[])
    let references := Lean.Server.findModuleRefs inputCtx.fileMap trees (localVars := false)
    let ilean := {
      module        := mainModuleName
      directImports := Server.collectImports ⟨snap.stx⟩
      references    := ← references.toLspModuleRefs
      : Lean.Server.Ilean
    }
    IO.FS.writeFile ileanFileName $ Json.compress $ toJson ilean

  if let some out := trace.profiler.output.get? opts then
    let traceStates := snaps.getAll.map (·.traces)
    let profile ← Firefox.Profile.export mainModuleName.toString startTime traceStates opts
    IO.FS.writeFile ⟨out⟩ <| Json.compress <| toJson profile

  -- no point in freeing the snapshot graph and all referenced data this close to process exit
  Runtime.forget snaps
  return some env

end Lean.Elab
