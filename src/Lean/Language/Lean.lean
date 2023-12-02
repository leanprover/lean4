/-
Copyright (c) 2023 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Implementation of the Lean language: parsing and processing of header and commands, incremental
recompilation

Authors: Sebastian Ullrich
-/

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
open Lean.Elab
open Lean.Parser

private def pushOpt (a? : Option α) (as : Array α) : Array α :=
  match a? with
  | some a => as.push a
  | none   => as

/-- Option for capturing output to stderr during elaboration. -/
register_builtin_option stderrAsMessages : Bool := {
  defValue := false
  group    := "server"
  descr    := "(server) capture output to the Lean stderr channel (such as from `dbg_trace`) during elaboration of a command as a diagnostic message"
}

/-- Option for showing elaboration errors from partial syntax errors. -/
register_builtin_option showPartialSyntaxErrors : Bool := {
  defValue := false
  descr    := "show elaboration errors from partial syntax trees (i.e. after parser recovery)"
}

/-! The hierarchy of Lean snapshot types -/

/-- Final state of processing of a command. -/
structure CommandFinishedSnapshot extends Snapshot where
  /-- Resulting elaboration state. -/
  cmdState : Command.State
deriving Nonempty
instance : ToSnapshotTree CommandFinishedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot, #[]⟩

/--
  State after processing a command's signature and before executing its tactic body, if any. Other
  commands should immediately proceed to `finished`. -/
-- TODO: tactics
structure CommandSignatureProcessedSnapshot extends Snapshot where
  /-- State after processing is finished. -/
  finished : SnapshotTask CommandFinishedSnapshot
deriving Nonempty
instance : ToSnapshotTree CommandSignatureProcessedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot, #[s.finished.map (sync := true) toSnapshotTree]⟩

/-- State after a command has been parsed. -/
structure CommandParsedSnapshotData extends Snapshot where
  /-- Syntax tree of the command. -/
  stx : Syntax
  /-- Resulting parser state. -/
  parserState : Parser.ModuleParserState
  /-- Signature processing task. -/
  sig : SnapshotTask CommandSignatureProcessedSnapshot
deriving Nonempty
/-- State after a command has been parsed. -/
-- workaround for lack of recursive structures
inductive CommandParsedSnapshot where
  /-- Creates a command parsed snapshot. -/
  | mk (data : CommandParsedSnapshotData) (next? : Option (SnapshotTask CommandParsedSnapshot))
deriving Nonempty
/-- The snapshot data. -/
abbrev CommandParsedSnapshot.data : CommandParsedSnapshot → CommandParsedSnapshotData
  | mk data _ => data
/-- Next command, unless this is a terminal command. -/
-- It would be really nice to not make this depend on `sig.finished` where possible
abbrev CommandParsedSnapshot.next? : CommandParsedSnapshot →
    Option (SnapshotTask CommandParsedSnapshot)
  | mk _ next? => next?
partial instance : ToSnapshotTree CommandParsedSnapshot where
  toSnapshotTree := go where
    go s := ⟨s.data.toSnapshot,
      #[s.data.sig.map (sync := true) toSnapshotTree] |>
        pushOpt (s.next?.map (·.map (sync := true) go))⟩

/-- State after successful importing. -/
structure HeaderProcessedSucessfully where
  /-- The resulting initial elaboration state. -/
  cmdState : Command.State
  /-- The search path communicated by `lake setup-file`, if any. -/
  srcSearchPath : SearchPath
  /-- First command task (there is always at least a terminal command). -/
  next : SnapshotTask CommandParsedSnapshot

/-- State after the module header has been processed including imports. -/
structure HeaderProcessedSnapshot extends Snapshot where
  /-- State after successful importing. -/
  success? : Option HeaderProcessedSucessfully
instance : ToSnapshotTree HeaderProcessedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot, #[] |>
    pushOpt (s.success?.map (·.next.map (sync := true) toSnapshotTree))⟩

/-- State after successfully parsing the module header. -/
structure HeaderParsedSucessfully where
  /-- Resulting parser state. -/
  parserState : Parser.ModuleParserState
  /-- Header processing task. -/
  processed : SnapshotTask HeaderProcessedSnapshot

/-- State after the module header has been parsed. -/
structure HeaderParsedSnapshot extends Snapshot where
  /-- Parser input context supplied by the driver, stored here for incremental parsing. -/
  ictx : Parser.InputContext
  /-- Resulting syntax tree. -/
  stx : Syntax
  /-- State after successful parsing. -/
  success? : Option HeaderParsedSucessfully
instance : ToSnapshotTree HeaderParsedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot,
    #[] |> pushOpt (s.success?.map (·.processed.map (sync := true) toSnapshotTree))⟩

/-- Shortcut accessor to the final header state, if successful. -/
def HeaderParsedSnapshot.processedSuccessfully (snap : HeaderParsedSnapshot) :
    SnapshotTask (Option HeaderProcessedSucessfully) :=
  snap.success?.bind (·.processed.map (sync := true) (·.success?)) |>.getD (.pure none)

/-- Initial snapshot of the Lean language processor: a "header parsed" snapshot. -/
abbrev InitialSnapshot := HeaderParsedSnapshot

private def msglogOfHeaderError (data : MessageData) : MessageLog :=
  MessageLog.empty.add { fileName := "<input>", pos := ⟨0, 0⟩, data }

/--
  Adds unexpected exceptions from header processing to the message log as a last resort; standard
  errors should already have been caught earlier. -/
private def withHeaderExceptions (ex : Snapshot → α) (act : IO α) : BaseIO α := do
  match (← act.toBaseIO) with
  | .error e => return ex { msgLog := msglogOfHeaderError e.toString }
  | .ok a => return a

/-- Makes sure we load imports at most once per process as they cannot be unloaded. -/
private builtin_initialize importsLoadedRef : IO.Ref Bool ← IO.mkRef false

/-- Entry point of the Lean language processor. -/
/-
General notes:
* For each processing function we pass in the previous state, if any, in order to reuse still-valid
  state. As there is no cheap way to check whether the `Environment` is unchanged, i.e. *semantic*
  change detection is currently not possible, we must make sure to pass `none` as all follow-up
  "previous states" from the first *syntactic* change onwards.
* We (try to remember to) cancel tasks that we cannot reuse proactively even though they are
  auto-canceled when the last reference to them is dropped; but it is not always easy to ensure that
  the last drop happens precisely where we expect it.
* Control flow up to finding the last still-valid snapshot (which should be quick) is synchronous so
  as not to report this "fast forwarding" to the user as well as to make sure the next run sees all
  fast-forwarded snapshots without having to wait on tasks.
-/
partial def processLean
    (ctx : ProcessingContext) (old? : Option InitialSnapshot) (ictx : Parser.InputContext) :
    BaseIO InitialSnapshot :=
  parseHeader old?
where
  -- compute position of syntactic change once
  firstDiffPos? := old?.map (·.ictx.input.firstDiffPos ictx.input)

  parseHeader (old? : Option HeaderParsedSnapshot) := do
    let unchanged old :=
      -- when header syntax is unchanged, reuse import processing task as is and continue with
      -- parsing the first command, synchronously if possible
      if let some success := old.success? then
        return { old with ictx, success? := some { success with
          processed := (← success.processed.bindIO (sync := true) fun processed => do
            if let some procSuccess := processed.success? then
              let oldCmd? ← getOrCancel? procSuccess.next
              return .pure { processed with success? := some { procSuccess with
                next := (← parseCmd oldCmd? success.parserState procSuccess.cmdState) } }
            else
              return .pure processed) } }
      else return old

    -- fast path: if we have parsed the header successfully...
    if let some old := old? then
      if let some (some processed) ← old.processedSuccessfully.get? then
        -- ...and the edit location is after the next command (see note [Incremental Parsing])...
        if let some nextCom ← processed.next.get? then
          if firstDiffPos?.any (nextCom.data.parserState.pos < ·) then
            -- ...go immediately to next snapshot
            return (← unchanged old)

    withHeaderExceptions ({ · with ictx, stx := .missing, success? := none }) do
      -- parsing the header should be cheap enough to do synchronously
      let (stx, parserState, msgLog) ← Parser.parseHeader ictx
      if msgLog.hasErrors then
        return { ictx, stx, msgLog, success? := none }

      -- semi-fast path: go to next snapshot if syntax tree is unchanged AND we're still in front
      -- of the edit location
      -- TODO: dropping the second condition would require adjusting positions in the state
      if let some old := old? then
        if firstDiffPos?.any (parserState.pos < ·) && old.stx == stx then
          return (← unchanged old)

      return {
        ictx, stx, msgLog
        success? := some {
          parserState
          processed := (← processHeader stx parserState)
        }
      }

  processHeader (stx : Syntax) (parserState : Parser.ModuleParserState) :=
    SnapshotTask.ofIO ⟨0, ictx.input.endPos⟩ <|
    withHeaderExceptions ({ · with success? := none }) do
      -- use `lake setup-file` if in language server
      let fileSetupResult ← if let some handler := ctx.fileSetupHandler? then
        handler (Elab.headerToImports stx)
      else
        pure { kind := .success, srcSearchPath := ∅, fileOptions := .empty }
      match fileSetupResult.kind with
      | .importsOutOfDate =>
        return {
          msgLog := msglogOfHeaderError
            "Imports are out of date and must be rebuilt; use the \"Restart File\" command in your editor."
          success? := none
        }
      | .error msg =>
        return {
          msgLog := msglogOfHeaderError msg
          success? := none
        }
      | _ => pure ()

      let importsAlreadyLoaded ← importsLoadedRef.modifyGet ((·, true))
      if importsAlreadyLoaded then
        -- As we never unload imports in the server, we should not run the code below twice in the
        -- same process and instead ask the watchdog to restart the worker
        IO.sleep 200  -- give user time to make further edits before restart
        unless (← IO.checkCanceled) do
          IO.Process.exit 2  -- signal restart request to watchdog
        -- should not be visible to user as task is already canceled
        return { msgLog := .empty, success? := none }

      -- override context options with file options
      let opts := ctx.opts.mergeBy (fun _ _ fileOpt => fileOpt) fileSetupResult.fileOptions

      -- allows `headerEnv` to be leaked, which would live until the end of the process anyway
      let (headerEnv, msgLog) ← Elab.processHeader (leakEnv := true) stx opts .empty ictx
        ctx.trustLevel

      let headerEnv := headerEnv.setMainModule ctx.mainModuleName
      let cmdState := Elab.Command.mkState headerEnv msgLog opts
      let cmdState := { cmdState with infoState := {
        enabled := true
        trees := #[Elab.InfoTree.context ({
          env     := headerEnv
          fileMap := ictx.fileMap
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
        msgLog := cmdState.messages
        infoTree? := cmdState.infoState.trees[0]!
        success? := some {
          cmdState
          srcSearchPath := fileSetupResult.srcSearchPath
          next := (← parseCmd none parserState cmdState)
        }
      }

  parseCmd (old? : Option CommandParsedSnapshot) (parserState : Parser.ModuleParserState)
      (cmdState : Command.State) :
      BaseIO (SnapshotTask CommandParsedSnapshot) := do
    let unchanged old : BaseIO CommandParsedSnapshot :=
      -- when syntax is unchanged, reuse command processing task as is
      if let some oldNext := old.next? then
        return .mk (data := old.data)
          (next? := (← old.data.sig.bindIO (sync := true) fun sig =>
            sig.finished.bindIO (sync := true) fun finished => do
              parseCmd (← getOrCancel? oldNext) old.data.parserState finished.cmdState))
      else return old  -- terminal command, we're done!

    -- fast path, do not even start new task for this snapshot
    if let some old := old? then
      if let some nextCom ← old.next?.bindM (·.get?) then
        if firstDiffPos?.any (nextCom.data.parserState.pos < ·) then
          return .pure (← unchanged old)

    SnapshotTask.ofIO ⟨parserState.pos, ictx.input.endPos⟩ do
      let beginPos := parserState.pos
      let scope := cmdState.scopes.head!
      let pmctx := {
        env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace
        openDecls := scope.openDecls
      }
      let (stx, parserState, msgLog) := Parser.parseCommand ictx pmctx parserState .empty

      -- semi-fast path
      if let some old := old? then
        if firstDiffPos?.any (parserState.pos < ·) && old.data.stx == stx then
          return (← unchanged old)

      let _ ← old?.map (·.data.sig) |> getOrCancel?
      let sig ← processCmdSignature stx cmdState msgLog.hasErrors beginPos
      let next? ← if Parser.isTerminalCommand stx then pure none
        -- for now, wait on "command finished" snapshot before parsing next command
        else some <$> sig.bindIO fun sig => do
          sig.finished.bindIO fun finished =>
            parseCmd none parserState finished.cmdState
      return .mk (next? := next?) {
        msgLog
        stx
        parserState
        sig
      }

  processCmdSignature (stx : Syntax) (cmdState : Command.State) (hasParseError : Bool)
      (beginPos : String.Pos) :=
    -- signature elaboration task; for now, does full elaboration
    -- TODO: do tactic snapshots, reuse old state for them
    SnapshotTask.ofIO (stx.getRange?.getD ⟨beginPos, beginPos⟩) do
      let scope := cmdState.scopes.head!
      let cmdStateRef ← IO.mkRef { cmdState with messages := .empty }
      let cmdCtx : Elab.Command.Context := { ictx with cmdPos := beginPos, tacticCache? := none }
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
          fileName := ictx.fileName
          severity := MessageSeverity.information
          pos      := ictx.fileMap.toPosition beginPos
          data     := output
        }
      let cmdState := { cmdState with messages }
      return {
        msgLog := .empty
        finished := .pure {
          msgLog := cmdState.messages
          infoTree? := some cmdState.infoState.trees[0]!
          cmdState
        }
      }

private partial def getFinalEnv? (snap : InitialSnapshot) : Option Environment := do
  let snap ← snap.success?
  let snap ← snap.processed.get.success?
  goCmd snap.next.get
where goCmd snap :=
  if let some next := snap.next? then
    goCmd next.get
  else
    snap.data.sig.get.finished.get.cmdState.env

end Lean

/-- The Lean language processor. -/
abbrev Lean : Language where
  process := Lean.processLean
  getFinalEnv? := Lean.getFinalEnv?
