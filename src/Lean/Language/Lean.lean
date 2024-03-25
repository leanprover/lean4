/-
Copyright (c) 2023 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Implementation of the Lean language: parsing and processing of header and commands, incremental
recompilation

Authors: Sebastian Ullrich
-/

prelude
import Lean.Language.Basic
import Lean.Parser.Module
import Lean.Elab.Command
import Lean.Elab.Import

/-!
# Note [Incremental Parsing]

In the language server, we want to minimize the work we do after each edit by reusing previous state
where possible. This is true for both parsing, i.e. reusing syntax trees without running the parser,
and elaboration. For both, we currently assume that we have to reprocess at least everything from
the point of change downwards. This note is about how to find the correct starting point for
incremental parsing; for elaboration, we then start with the first changed syntax tree.

One initial thought about incremental parsing could be that it's not necessary as parsing is very
fast compared to elaboration; on mathlib we average 41ms parsing per 1000 LoC. But there are quite a
few files >= 1kloc (up to 4.5kloc) in there, so near the end of such files lag from always reparsing
from the beginning may very well be noticeable.

So if we do want incremental parsing, another thought might be that a user edit can only invalidate
commands at or after the location of the change. Unfortunately, that's not true; take the (partial)
input `def a := b private def c`. If we remove the space after `private`, the two commands
syntactically become one with an application of `privatedef` to `b` even though the edit was
strictly after the end of the first command.

So obviously we must include at least the extent of the token that made the parser stop parsing a
command as well such that invalidating the private token invalidates the preceding command.
Unfortunately this is not sufficient either, given the following input:
```
structure a where /-- b -/ @[c] private axiom d : Nat
```
This is a syntactically valid sequence of a field-less structure and a declaration. If we again
delete the space after private, it becomes a syntactically correct structure with a single field
privateaxiom! So clearly, because of uses of atomic in the grammar, an edit can affect a command
syntax tree even across multiple tokens.

Now, what we do today, and have done since Lean 3, is to always reparse the last command completely
preceding the edit location. If its syntax tree is unchanged, we preserve its data and reprocess all
following commands only, otherwise we reprocess it fully as well. This seems to have worked well so
far but it does seem a bit arbitrary given that even if it works for our current grammar, it can
certainly be extended in ways that break the assumption.

Finally, a more actually principled and generic solution would be to invalidate a syntax tree when
the parser has reached the edit location during parsing. If it did not, surely the edit cannot have
an effect on the syntax tree in question. Sadly such a "high-water mark" parser position does not
exist currently and likely it could at best be approximated by e.g. "furthest `tokenFn` parse". Thus
we remain at "go two commands up" at this point.
-/

set_option linter.missingDocs true

namespace Lean.Language.Lean
open Lean.Elab Command
open Lean.Parser

private def pushOpt (a? : Option α) (as : Array α) : Array α :=
  match a? with
  | some a => as.push a
  | none   => as

/-- Option for capturing output to stderr during elaboration. -/
register_builtin_option stderrAsMessages : Bool := {
  defValue := true
  group    := "server"
  descr    := "(server) capture output to the Lean stderr channel (such as from `dbg_trace`) during elaboration of a command as a diagnostic message"
}

/-- Option for showing elaboration errors from partial syntax errors. -/
register_builtin_option showPartialSyntaxErrors : Bool := {
  defValue := false
  descr    := "show elaboration errors from partial syntax trees (i.e. after parser recovery)"
}

/-! The hierarchy of Lean snapshot types -/

/-- Snapshot after elaboration of the entire command. -/
structure CommandFinishedSnapshot extends Language.Snapshot where
  /-- Resulting elaboration state. -/
  cmdState : State
deriving Nonempty
instance : Language.ToSnapshotTree CommandFinishedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot, #[]⟩

/-- State after a command has been parsed. -/
structure CommandParsedSnapshotData extends Snapshot where
  /-- Syntax tree of the command. -/
  stx : Syntax
  /-- Resulting parser state. -/
  parserState : Parser.ModuleParserState
  /--
  Snapshot for incremental reporting and reuse during elaboration, type dependent on specific
  elaborator.
   -/
  elabSnap : SnapshotTask DynamicSnapshot
  /-- State after processing is finished. -/
  finishedSnap : SnapshotTask CommandFinishedSnapshot
deriving Nonempty

/-- State after a command has been parsed. -/
-- workaround for lack of recursive structures
inductive CommandParsedSnapshot where
  /-- Creates a command parsed snapshot. -/
  | mk (data : CommandParsedSnapshotData)
    (nextCmdSnap? : Option (SnapshotTask CommandParsedSnapshot))
deriving Nonempty
/-- The snapshot data. -/
abbrev CommandParsedSnapshot.data : CommandParsedSnapshot → CommandParsedSnapshotData
  | mk data _ => data
/-- Next command, unless this is a terminal command. -/
abbrev CommandParsedSnapshot.next? : CommandParsedSnapshot →
    Option (SnapshotTask CommandParsedSnapshot)
  | mk _ next? => next?
partial instance : ToSnapshotTree CommandParsedSnapshot where
  toSnapshotTree := go where
    go s := ⟨s.data.toSnapshot,
      #[s.data.elabSnap.map (sync := true) toSnapshotTree,
        s.data.finishedSnap.map (sync := true) toSnapshotTree] |>
        pushOpt (s.next?.map (·.map (sync := true) go))⟩


/-- Cancels all significant computations from this snapshot onwards. -/
partial def CommandParsedSnapshot.cancel (snap : CommandParsedSnapshot) : BaseIO Unit := do
  -- This is the only relevant computation right now
  -- TODO: cancel additional elaboration tasks if we add them without switching to implicit
  -- cancellation
  snap.data.finishedSnap.cancel
  if let some next := snap.next? then
    -- recurse on next command (which may have been spawned just before we cancelled above)
    let _ ← IO.mapTask (sync := true) (·.cancel) next.task

/-- State after successful importing. -/
structure HeaderProcessedState where
  /-- The resulting initial elaboration state. -/
  cmdState : Command.State
  /-- First command task (there is always at least a terminal command). -/
  firstCmdSnap : SnapshotTask CommandParsedSnapshot

/-- State after the module header has been processed including imports. -/
structure HeaderProcessedSnapshot extends Snapshot where
  /-- State after successful importing. -/
  result? : Option HeaderProcessedState
  isFatal := result?.isNone
instance : ToSnapshotTree HeaderProcessedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot, #[] |>
    pushOpt (s.result?.map (·.firstCmdSnap.map (sync := true) toSnapshotTree))⟩

/-- State after successfully parsing the module header. -/
structure HeaderParsedState where
  /-- Resulting parser state. -/
  parserState : Parser.ModuleParserState
  /-- Header processing task. -/
  processedSnap : SnapshotTask HeaderProcessedSnapshot

/-- State after the module header has been parsed. -/
structure HeaderParsedSnapshot extends Snapshot where
  /-- Parser input context supplied by the driver, stored here for incremental parsing. -/
  ictx : Parser.InputContext
  /-- Resulting syntax tree. -/
  stx : Syntax
  /-- State after successful parsing. -/
  result? : Option HeaderParsedState
  isFatal := result?.isNone

instance : ToSnapshotTree HeaderParsedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot,
    #[] |> pushOpt (s.result?.map (·.processedSnap.map (sync := true) toSnapshotTree))⟩

/-- Shortcut accessor to the final header state, if successful. -/
def HeaderParsedSnapshot.processedResult (snap : HeaderParsedSnapshot) :
    SnapshotTask (Option HeaderProcessedState) :=
  snap.result?.bind (·.processedSnap.map (sync := true) (·.result?)) |>.getD (.pure none)

/-- Initial snapshot of the Lean language processor: a "header parsed" snapshot. -/
abbrev InitialSnapshot := HeaderParsedSnapshot

/-- Lean-specific processing context. -/
structure LeanProcessingContext extends ProcessingContext where
  /-- Position of the first file difference if there was a previous invocation. -/
  firstDiffPos? : Option String.Pos

/-- Monad transformer holding all relevant data for Lean processing. -/
abbrev LeanProcessingT m := ReaderT LeanProcessingContext m
/-- Monad holding all relevant data for Lean processing. -/
abbrev LeanProcessingM := LeanProcessingT BaseIO

instance : MonadLift LeanProcessingM (LeanProcessingT IO) where
  monadLift := fun act ctx => act ctx

instance : MonadLift (ProcessingT m) (LeanProcessingT m) where
  monadLift := fun act ctx => act ctx.toProcessingContext

/--
Embeds a `LeanProcessingT` action into `ProcessingT`, optionally using the old input string to
speed up reuse analysis.
-/
def LeanProcessingT.run [Monad m] (act : LeanProcessingT m α) (oldInputCtx? : Option InputContext) :
    ProcessingT m α := do
  -- compute position of syntactic change once
  let firstDiffPos? := oldInputCtx?.map (·.input.firstDiffPos (← read).input)
  ReaderT.adapt ({ · with firstDiffPos? }) act

/--
Returns true if there was a previous run and the given position is before any textual change
compared to it.
-/
def isBeforeEditPos (pos : String.Pos) : LeanProcessingM Bool := do
  return (← read).firstDiffPos?.any (pos < ·)

/--
  Adds unexpected exceptions from header processing to the message log as a last resort; standard
  errors should already have been caught earlier. -/
private def withHeaderExceptions (ex : Snapshot → α) (act : LeanProcessingT IO α) :
    LeanProcessingM α := do
  match (← (act (← read)).toBaseIO) with
  | .error e => return ex { diagnostics := (← diagnosticsOfHeaderError e.toString) }
  | .ok a => return a

/-- Entry point of the Lean language processor. -/
/-
General notes:
* For each processing function we pass in the previous state, if any, in order to reuse still-valid
  state. As there is no cheap way to check whether the `Environment` is unchanged, i.e. *semantic*
  change detection is currently not possible, we must make sure to pass `none` as all follow-up
  "previous states" from the first *syntactic* change onwards.
* We must make sure to use `CommandParsedSnapshot.cancel` on such tasks when discarding them, i.e.
  when not passing them along in `old?`.
* Control flow up to finding the last still-valid snapshot (which should be quick) is synchronous so
  as not to report this "fast forwarding" to the user as well as to make sure the next run sees all
  fast-forwarded snapshots without having to wait on tasks.
-/
partial def process
    (setupImports : Syntax → ProcessingT IO (Except HeaderProcessedSnapshot Options) :=
      fun _ => pure <| .ok {})
    (old? : Option InitialSnapshot) : ProcessingM InitialSnapshot := do
  parseHeader old? |>.run (old?.map (·.ictx))
where
  parseHeader (old? : Option HeaderParsedSnapshot) : LeanProcessingM HeaderParsedSnapshot := do
    let ctx ← read
    let ictx := ctx.toInputContext
    let unchanged old :=
      -- when header syntax is unchanged, reuse import processing task as is and continue with
      -- parsing the first command, synchronously if possible
      if let some oldSuccess := old.result? then
        return { old with ictx, result? := some { oldSuccess with
          processedSnap := (← oldSuccess.processedSnap.bindIO (sync := true) fun oldProcessed => do
            if let some oldProcSuccess := oldProcessed.result? then
              -- also wait on old command parse snapshot as parsing is cheap and may allow for
              -- elaboration reuse
              oldProcSuccess.firstCmdSnap.bindIO (sync := true) fun oldCmd =>
                return .pure { oldProcessed with result? := some { oldProcSuccess with
                  firstCmdSnap := (← parseCmd oldCmd oldSuccess.parserState oldProcSuccess.cmdState ctx) } }
            else
              return .pure oldProcessed) } }
      else return old

    -- fast path: if we have parsed the header successfully...
    if let some old := old? then
      if let some (some processed) ← old.processedResult.get? then
        -- ...and the edit location is after the next command (see note [Incremental Parsing])...
        if let some nextCom ← processed.firstCmdSnap.get? then
          if (← isBeforeEditPos nextCom.data.parserState.pos) then
            -- ...go immediately to next snapshot
            return (← unchanged old)

    withHeaderExceptions ({ · with ictx, stx := .missing, result? := none }) do
      -- parsing the header should be cheap enough to do synchronously
      let (stx, parserState, msgLog) ← Parser.parseHeader ictx
      if msgLog.hasErrors then
        return {
          ictx, stx
          diagnostics := (← Snapshot.Diagnostics.ofMessageLog msgLog)
          result? := none
        }

      -- semi-fast path: go to next snapshot if syntax tree is unchanged AND we're still in front
      -- of the edit location
      -- TODO: dropping the second condition would require adjusting positions in the state
      -- NOTE: as `parserState.pos` includes trailing whitespace, this forces reprocessing even if
      -- only that whitespace changes, which is wasteful but still necessary because it may
      -- influence the range of error messages such as from a trailing `exact`
      if let some old := old? then
        if (← isBeforeEditPos parserState.pos) && old.stx == stx then
          return (← unchanged old)
        -- on first change, make sure to cancel all further old tasks
        if let some oldSuccess := old.result? then
          oldSuccess.processedSnap.cancel
          let _ ← BaseIO.mapTask (t := oldSuccess.processedSnap.task) fun processed => do
            if let some oldProcSuccess := processed.result? then
              let _ ← BaseIO.mapTask (·.cancel) oldProcSuccess.firstCmdSnap.task

      return {
        ictx, stx
        diagnostics := (← Snapshot.Diagnostics.ofMessageLog msgLog)
        result? := some {
          parserState
          processedSnap := (← processHeader stx parserState)
        }
      }

  processHeader (stx : Syntax) (parserState : Parser.ModuleParserState) :
      LeanProcessingM (SnapshotTask HeaderProcessedSnapshot) := do
    let ctx ← read
    SnapshotTask.ofIO (some ⟨0, ctx.input.endPos⟩) <|
    ReaderT.run (r := ctx) <|  -- re-enter reader in new task
    withHeaderExceptions (α := HeaderProcessedSnapshot) ({ · with result? := none }) do
      let opts ← match (← setupImports stx) with
        | .ok opts => pure opts
        | .error snap => return snap
      -- override context options with file options
      let opts := ctx.opts.mergeBy (fun _ _ fileOpt => fileOpt) opts
      -- allows `headerEnv` to be leaked, which would live until the end of the process anyway
      let (headerEnv, msgLog) ← Elab.processHeader (leakEnv := true) stx opts .empty
        ctx.toInputContext ctx.trustLevel
      let diagnostics := (← Snapshot.Diagnostics.ofMessageLog msgLog)
      if msgLog.hasErrors then
        return { diagnostics, result? := none }

      let headerEnv := headerEnv.setMainModule ctx.mainModuleName
      let cmdState := Elab.Command.mkState headerEnv msgLog opts
      let cmdState := { cmdState with infoState := {
        enabled := true
        trees := #[Elab.InfoTree.context (.commandCtx {
          env     := headerEnv
          fileMap := ctx.fileMap
          ngen    := { namePrefix := `_import }
        }) (Elab.InfoTree.node
            (Elab.Info.ofCommandInfo { elaborator := `header, stx })
            (stx[1].getArgs.toList.map (fun importStx =>
              Elab.InfoTree.node (Elab.Info.ofCommandInfo {
                elaborator := `import
                stx := importStx
              }) #[].toPArray'
            )).toPArray'
        )].toPArray'
      }}
      return {
        diagnostics
        infoTree? := cmdState.infoState.trees[0]!
        result? := some {
          cmdState
          firstCmdSnap := (← parseCmd none parserState cmdState)
        }
      }

  parseCmd (old? : Option CommandParsedSnapshot) (parserState : Parser.ModuleParserState)
      (cmdState : Command.State) : LeanProcessingM (SnapshotTask CommandParsedSnapshot) := do
    let ctx ← read

    -- check for cancellation, most likely during elaboration of previous command, before starting
    -- processing of next command
    if (← IO.checkCanceled) then
      -- this is a bit ugly as we don't want to adjust our API with `Option`s just for cancellation
      -- (as no-one should look at this result in that case) but anything containing `Environment`
      -- is not `Inhabited`
      return .pure <| .mk (nextCmdSnap? := none) {
        diagnostics := .empty, stx := .missing, parserState
        elabSnap := .pure <| .ofTyped { diagnostics := .empty : SnapshotLeaf }
        finishedSnap := .pure { diagnostics := .empty, cmdState }
      }

    let unchanged old : BaseIO CommandParsedSnapshot :=
      -- when syntax is unchanged, reuse command processing task as is
      if let some oldNext := old.next? then
        return .mk (data := old.data)
          (nextCmdSnap? := (← old.data.finishedSnap.bindIO (sync := true) fun oldFinished =>
            -- also wait on old command parse snapshot as parsing is cheap and may allow for
            -- elaboration reuse
            oldNext.bindIO (sync := true) fun oldNext => do
              parseCmd oldNext old.data.parserState oldFinished.cmdState ctx))
      else return old  -- terminal command, we're done!

    -- fast path, do not even start new task for this snapshot
    if let some old := old? then
      if let some nextCom ← old.next?.bindM (·.get?) then
        if (← isBeforeEditPos nextCom.data.parserState.pos) then
          return .pure (← unchanged old)

    SnapshotTask.ofIO (some ⟨parserState.pos, ctx.input.endPos⟩) do
      let beginPos := parserState.pos
      let scope := cmdState.scopes.head!
      let pmctx := {
        env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace
        openDecls := scope.openDecls
      }
      let (stx, parserState, msgLog) := Parser.parseCommand ctx.toInputContext pmctx parserState
        .empty

      -- semi-fast path
      if let some old := old? then
        if (← isBeforeEditPos parserState.pos ctx) && old.data.stx == stx then
          return (← unchanged old)
        -- on first change, make sure to cancel all further old tasks
        old.cancel

      -- definitely assigned in `doElab` task
      let headers ← IO.Promise.new
      let finishedSnap ←
        doElab stx cmdState msgLog.hasErrors beginPos
          { old? := old?.map (·.data.elabSnap), new := headers } ctx

      let next? ← if Parser.isTerminalCommand stx then pure none
        -- for now, wait on "command finished" snapshot before parsing next command
        else some <$> finishedSnap.bindIO fun finished =>
          parseCmd none parserState finished.cmdState ctx
      return .mk (nextCmdSnap? := next?) {
        diagnostics := (← Snapshot.Diagnostics.ofMessageLog msgLog)
        stx
        parserState
        elabSnap := { range? := none, task := headers.result }
        finishedSnap
      }

  doElab (stx : Syntax) (cmdState : Command.State) (hasParseError : Bool) (beginPos : String.Pos)
      (snap : SnapshotBundle DynamicSnapshot) :
      LeanProcessingM (SnapshotTask CommandFinishedSnapshot) := do
    let ctx ← read
    SnapshotTask.ofIO (stx.getRange?.getD ⟨beginPos, beginPos⟩) do
      let scope := cmdState.scopes.head!
      let cmdStateRef ← IO.mkRef { cmdState with messages := .empty }
      let cmdCtx : Elab.Command.Context := { ctx with
        cmdPos       := beginPos
        tacticCache? := none
        snap?        := some snap
      }
      let (output, _) ←
        IO.FS.withIsolatedStreams (isolateStderr := stderrAsMessages.get scope.opts) do
          liftM (m := BaseIO) do
            Elab.Command.catchExceptions
              (getResetInfoTrees *> Elab.Command.elabCommandTopLevel stx)
              cmdCtx cmdStateRef
      let cmdState ← cmdStateRef.get
      let mut messages := cmdState.messages
      -- `stx.hasMissing` should imply `hasParseError`, but the latter should be cheaper to check in
      -- general
      if !showPartialSyntaxErrors.get cmdState.scopes[0]!.opts && hasParseError &&
          stx.hasMissing then
        -- discard elaboration errors, except for a few important and unlikely misleading ones, on
        -- parse error
        messages := ⟨messages.msgs.filter fun msg =>
          msg.data.hasTag (fun tag => tag == `Elab.synthPlaceholder ||
            tag == `Tactic.unsolvedGoals || (`_traceMsg).isSuffixOf tag)⟩
      if !output.isEmpty then
        messages := messages.add {
          fileName := ctx.fileName
          severity := MessageSeverity.information
          pos      := ctx.fileMap.toPosition beginPos
          data     := output
        }
      let cmdState := { cmdState with messages }
      -- only has an effect if actual `resolve` was skipped from fatal exception (caught by
      -- `catchExceptions` above) or it not being a mutual def
      snap.new.resolve <| .ofTyped { diagnostics := .empty : SnapshotLeaf }
      return {
        diagnostics := (← Snapshot.Diagnostics.ofMessageLog cmdState.messages)
        infoTree? := some cmdState.infoState.trees[0]!
        cmdState
      }

/--
Convenience function for tool uses of the language processor that skips header handling.
-/
def processCommands (inputCtx : Parser.InputContext) (parserState : Parser.ModuleParserState)
    (commandState : Command.State)
    (old? : Option (Parser.InputContext × CommandParsedSnapshot) := none) :
    BaseIO (SnapshotTask CommandParsedSnapshot) := do
  process.parseCmd (old?.map (·.2)) parserState commandState
    |>.run (old?.map (·.1))
    |>.run { inputCtx with
      mainModuleName := commandState.env.mainModule
      opts := commandState.scopes.head!.opts
    }


/-- Waits for and returns final environment, if importing was successful. -/
partial def waitForFinalEnv? (snap : InitialSnapshot) : Option Environment := do
  let snap ← snap.result?
  let snap ← snap.processedSnap.get.result?
  goCmd snap.firstCmdSnap.get
where goCmd snap :=
  if let some next := snap.next? then
    goCmd next.get
  else
    snap.data.finishedSnap.get.cmdState.env

end Lean
