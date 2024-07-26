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
    tacticCache? := none
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

def IO.processCommands (inputCtx : Parser.InputContext) (parserState : Parser.ModuleParserState) (commandState : Command.State) : IO State := do
  let (_, s) ← (Frontend.processCommands.run { inputCtx := inputCtx }).run { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }
  pure s

structure IncrementalState extends State where
  inputCtx    : Parser.InputContext
  initialSnap : Language.Lean.CommandParsedSnapshot
deriving Nonempty

open Language in
/--
Variant of `IO.processCommands` that uses the new Lean language processor implementation for
potential incremental reuse. Pass in result of a previous invocation done with the same state
(but usually different input context) to allow for reuse.
-/
-- `IO.processCommands` can be reimplemented on top of this as soon as the additional tasks speed up
-- things instead of slowing them down
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
    let commands := commands.push snap.data.stx
    if let some next := snap.nextCmdSnap? then
      go initialSnap next commands
    else
      -- Opting into reuse also enables incremental reporting, so make sure to collect messages from
      -- all snapshots
      let messages := toSnapshotTree initialSnap
        |>.getAll.map (·.diagnostics.msgLog)
        |>.foldl (· ++ ·) {}
      let trees := toSnapshotTree initialSnap
        |>.getAll.map (·.infoTree?) |>.filterMap id |>.toPArray'
      return {
        commandState := { snap.data.finishedSnap.get.cmdState with messages, infoState.trees := trees }
        parserState := snap.data.parserState
        cmdPos := snap.data.parserState.pos
        inputCtx, initialSnap, commands
      }

def process (input : String) (env : Environment) (opts : Options) (fileName : Option String := none) : IO (Environment × MessageLog) := do
  let fileName   := fileName.getD "<input>"
  let inputCtx   := Parser.mkInputContext input fileName
  let s ← IO.processCommands inputCtx { : Parser.ModuleParserState } (Command.mkState env {} opts)
  pure (s.commandState.env, s.commandState.messages)

/--
Parses values of options registered during import and left by the C++ frontend as strings, fails if
any option names remain unknown.
-/
def reparseOptions (opts : Options) : IO Options := do
  let mut opts := opts
  let decls ← getOptionDecls
  for (name, val) in opts do
    let .ofString val := val
      | continue  -- Already parsed by C++
    -- Options can be prefixed with `weak` in order to turn off the error when the option is not
    -- defined
    let weak := name.getRoot == `weak
    if weak then
      opts := opts.erase name
    let name := name.replacePrefix `weak Name.anonymous
    let some decl := decls.find? name
      | unless weak do
          throw <| .userError s!"invalid -D parameter, unknown configuration option '{name}'"

    match decl.defValue with
    | .ofBool _ =>
      match val with
      | "true"  => opts := opts.insert name true
      | "false" => opts := opts.insert name false
      | _ =>
        throw <| .userError s!"invalid -D parameter, invalid configuration option '{val}' value, \
          it must be true/false"
    | .ofNat _ =>
      let some val := val.toNat?
        | throw <| .userError s!"invalid -D parameter, invalid configuration option '{val}' value, \
            it must be a natural number"
      opts := opts.insert name val
    | .ofString _ => opts := opts.insert name val
    | _ => throw <| .userError s!"invalid -D parameter, configuration option '{name}' \
              cannot be set in the command line, use set_option command"

  return opts

@[export lean_run_frontend]
def runFrontend
    (input : String)
    (opts : Options)
    (fileName : String)
    (mainModuleName : Name)
    (trustLevel : UInt32 := 0)
    (ileanFileName? : Option String := none)
    (jsonOutput : Bool := false)
    : IO (Environment × Bool) := do
  let startTime := (← IO.monoNanosNow).toFloat / 1000000000
  let inputCtx := Parser.mkInputContext input fileName
  if true then
    -- Temporarily keep alive old cmdline driver for the Lean language so that we don't pay the
    -- overhead of passing the environment between snapshots until we actually make good use of it
    -- outside the server
    let (header, parserState, messages) ← Parser.parseHeader inputCtx
    -- allow `env` to be leaked, which would live until the end of the process anyway
    let (env, messages) ← processHeader (leakEnv := true) header opts messages inputCtx trustLevel
    -- now that imports have been loaded, check options again
    let opts ← reparseOptions opts
    let env := env.setMainModule mainModuleName
    let mut commandState := Command.mkState env messages opts
    let elabStartTime := (← IO.monoNanosNow).toFloat / 1000000000

    if ileanFileName?.isSome then
      -- Collect InfoTrees so we can later extract and export their info to the ilean file
      commandState := { commandState with infoState.enabled := true }

    let s ← IO.processCommands inputCtx parserState commandState
    Language.reportMessages s.commandState.messages opts jsonOutput

    if let some ileanFileName := ileanFileName? then
      let trees := s.commandState.infoState.trees.toArray
      let references ←
        Lean.Server.findModuleRefs inputCtx.fileMap trees (localVars := false) |>.toLspModuleRefs
      let ilean := { module := mainModuleName, references : Lean.Server.Ilean }
      IO.FS.writeFile ileanFileName $ Json.compress $ toJson ilean

    if let some out := trace.profiler.output.get? opts then
      let traceState := s.commandState.traceState
      -- importing does not happen in an elaboration monad, add now
      let traceState := { traceState with
        traces := #[{
          ref := .missing,
          msg := .trace { cls := `Import, startTime, stopTime := elabStartTime }
            (.ofFormat "importing") #[]
        }].toPArray' ++ traceState.traces
      }
      let profile ← Firefox.Profile.export mainModuleName.toString startTime traceState opts
      IO.FS.writeFile ⟨out⟩ <| Json.compress <| toJson profile

    return (s.commandState.env, !s.commandState.messages.hasErrors)

  let ctx := { inputCtx with }
  let processor := Language.Lean.process
  let snap ← processor (fun _ => pure <| .ok { mainModuleName, opts, trustLevel }) none ctx
  let snaps := Language.toSnapshotTree snap
  snaps.runAndReport opts jsonOutput
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
