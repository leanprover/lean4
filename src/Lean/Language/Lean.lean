/-
Copyright (c) 2023 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Sebastian Ullrich
-/

import Lean.Language.Basic
import Lean.Parser.Module
import Lean.Elab.Command
import Lean.Elab.Import

namespace Lean.Language.Lean
open Lean.Elab
open Lean.Parser

def pushOpt (a? : Option α) (as : Array α) : Array α :=
  match a? with
  | some a => as.push a
  | none   => as

register_builtin_option stderrAsMessages : Bool := {
  defValue := false
  group    := "server"
  descr    := "(server) capture output to the Lean stderr channel (such as from `dbg_trace`) during elaboration of a command as a diagnostic message"
}

register_builtin_option showPartialSyntaxErrors : Bool := {
  defValue := false
  descr    := "show elaboration errors from partial syntax trees (i.e. after parser recovery)"
}

/-! The hierarchy of Lean snapshot types -/

/-- Final state of processing of a command. -/
structure CommandFinishedSnapshot extends Snapshot where
  cmdState : Command.State
deriving Nonempty
instance : ToSnapshotTree CommandFinishedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot, #[]⟩

/-- State after execution of a single synchronous tactic step. -/
inductive TacticEvaluatedSnapshot where
  | mk (toSnapshot : Snapshot) (next : Array (SnapshotTask TacticEvaluatedSnapshot))
/-- Potential, potentially parallel, follow-up tactic executions. -/
-- In the first, non-parallel version, each task will depend on its predecessor
abbrev TacticEvaluatedSnapshot.next : TacticEvaluatedSnapshot → Array (SnapshotTask TacticEvaluatedSnapshot)
  | mk _ next => next
partial instance : ToSnapshotTree TacticEvaluatedSnapshot where
  toSnapshotTree := go where
    go := fun ⟨s, next⟩ => ⟨s, next.map (·.map go)⟩

/--
  State after processing a command's signature and before executing its tactic
  body, if any. Other commands should immediately proceed to `finished`. -/
structure CommandSignatureProcessedSnapshot extends Snapshot where
  /-- Potential, potentially parallel, follow-up tactic executions. -/
  tacs : Array (SnapshotTask TacticEvaluatedSnapshot)
  /-- State after processing is finished. -/
  -- If we make proofs completely opaque, this will not have to depend on `tacs`
  finished : SnapshotTask CommandFinishedSnapshot
deriving Nonempty
instance : ToSnapshotTree CommandSignatureProcessedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot, s.tacs.map (·.map toSnapshotTree) |>.push (s.finished.map toSnapshotTree)⟩

/-- State after a command has been parsed. -/
structure CommandParsedSnapshotData extends Snapshot where
  stx : Syntax
  parserState : Parser.ModuleParserState
  /-- Furthest position the parser has looked at; used for incremental parsing. -/
  stopPos : String.Pos
  sig : SnapshotTask CommandSignatureProcessedSnapshot
deriving Nonempty
inductive CommandParsedSnapshot where
  | mk (data : CommandParsedSnapshotData) (next? : Option (SnapshotTask CommandParsedSnapshot))
deriving Nonempty
abbrev CommandParsedSnapshot.data : CommandParsedSnapshot → CommandParsedSnapshotData
  | mk data _ => data
/-- Next command, unless this is a terminal command. -/
-- It would be really nice to not make this depend on `sig.finished` where possible
abbrev CommandParsedSnapshot.next? : CommandParsedSnapshot → Option (SnapshotTask CommandParsedSnapshot)
  | mk _ next? => next?
partial instance : ToSnapshotTree CommandParsedSnapshot where
  toSnapshotTree := go where
    go s := ⟨s.data.toSnapshot, #[s.data.sig.map toSnapshotTree] |> pushOpt (s.next?.map (·.map go))⟩

structure HeaderProcessedSucessfully where
  cmdState : Command.State
  next : SnapshotTask CommandParsedSnapshot

/-- State after the module header has been processed including imports. -/
structure HeaderProcessedSnapshot extends Snapshot where
  success? : Option HeaderProcessedSucessfully
instance : ToSnapshotTree HeaderProcessedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot, #[] |> pushOpt (s.success?.map (·.next.map toSnapshotTree))⟩

structure HeaderParsedSucessfully where
  parserState : Parser.ModuleParserState
  /-- Furthest position the parser has looked at; used for incremental parsing. -/
  stopPos : String.Pos
  next : SnapshotTask HeaderProcessedSnapshot

/-- State after the module header has been parsed. -/
structure HeaderParsedSnapshot extends Snapshot where
  stx : Syntax
  success? : Option HeaderParsedSucessfully
instance : ToSnapshotTree HeaderParsedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot, #[] |> pushOpt (s.success?.map (·.next.map toSnapshotTree))⟩

abbrev InitialSnapshot := HeaderParsedSnapshot

/-- Entry point of the Lean language processor. -/
-- As a general note, for each processing function we pass in the previous
-- state, if any, in order to reuse still-valid state. Thus the logic of
-- what snapshots to reuse is completely moved out of the server into the
-- language-specific processor. As there is no cheap way to check whether
-- the `Environment` is unchanged, we must make sure to pass `none` as all
-- follow-up "previous states" when we do change it.
partial def processLean
  (ctx : ProcessingContext) (old? : Option InitialSnapshot) (ictx : Parser.InputContext) :
    BaseIO InitialSnapshot :=
  parseHeader old?
where
  parseHeader (old? : Option HeaderParsedSnapshot) := do
    let unchanged old success :=
      -- when header syntax is unchanged, reuse import processing task as is
      return { old with success? := some { success with
        next := (← success.next.bindIO (processHeader · old.stx success.parserState)) } }

    -- fast path: if we have parsed the header sucessfully...
    if let some old@{ success? := some success, .. } := old? then
      -- ...and the header syntax appears unchanged...
      if unchangedParse old.stx success.stopPos ictx.input then
        -- ...go immediately to next snapshot
        return (← unchanged old success)

    withFatalExceptions ({ · with stx := .missing, success? := none }) do
      let (stx, parserState, msgLog) ← Parser.parseHeader ictx
      -- TODO: move into `parseHeader`; it should add the length of `peekToken`,
      -- which is the full extent the parser considered before stopping
      let stopPos := parserState.pos + (⟨1⟩ : String.Pos)

      if msgLog.hasErrors then
        return { stx, msgLog, success? := none }

      -- semi-fast path: go to next snapshot if syntax tree is unchanged
      if let some old@{ success? := some success, .. } := old? then
        if old.stx == stx then
          return (← unchanged old success)
        success.next.cancel

      return { stx, msgLog, success? := some {
        parserState
        stopPos
        next := (← processHeader none stx parserState) } }

  processHeader (old? : Option HeaderProcessedSnapshot) (stx : Syntax) (parserState : Parser.ModuleParserState) := do
    -- fast path, do not even start new task for this snapshot
    if let some old := old? then
      if let some success := old.success? then
        return .pure { old with success? := some { success with
          next := (← success.next.bindIO (parseCmd · parserState success.cmdState)) } }
      else
        return .pure old

    SnapshotTask.ofIO ⟨0, ictx.input.endPos⟩ do
    withFatalExceptions ({ · with success? := none }) do
    -- discard existing continuation if any, there is nothing to reuse
    let _ ← old?.bind (·.success?) |>.map (·.next) |> getOrCancel
    -- function copied from current implementation, see below
    -- TODO: we should do this at most once per process
    let cmdState ← doImport stx
    return {
      msgLog := cmdState.messages
      infoTree? := cmdState.infoState.trees[0]!
      success? := some { cmdState, next := (← parseCmd none parserState cmdState) } }

  parseCmd (old? : Option CommandParsedSnapshot) (parserState : Parser.ModuleParserState) (cmdState : Command.State) :
      BaseIO (SnapshotTask CommandParsedSnapshot) := do
    let unchanged old : BaseIO CommandParsedSnapshot :=
      -- when syntax is unchanged, reuse command processing task as is
      if let some oldNext := old.next? then
        return .mk (data := old.data)
          (next? := (← old.data.sig.bindIO fun sig =>
            sig.finished.bindIO fun finished => do
              parseCmd (← getOrCancel oldNext) old.data.parserState finished.cmdState))
      else return old  -- terminal command, we're done!

    -- fast path, do not even start new task for this snapshot
    if let some old := old? then
      if unchangedParse old.data.stx old.data.stopPos ictx.input then
        return .pure (← unchanged old)

    SnapshotTask.ofIO ⟨parserState.pos, ictx.input.endPos⟩ do
      let beginPos := parserState.pos
      let scope := cmdState.scopes.head!
      let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
      let (stx, parserState, msgLog) := Parser.parseCommand ictx pmctx parserState .empty

      -- TODO: move into `parseCommand`; it should add the length of `peekToken`,
      -- which is the full extent the parser considered before stopping
      let stopPos := parserState.pos + (⟨1⟩ : String.Pos)
      if let some old := old? then
        if old.data.stx == stx then
          return (← unchanged old)

      -- signature elaboration task; for now, does full elaboration
      -- TODO: do tactic snapshots, reuse old state for them
      let _ ← old?.map (·.data.sig) |> getOrCancel
      let sig ← SnapshotTask.ofIO (stx.getRange?.getD ⟨parserState.pos, parserState.pos⟩) do
        let cmdState ← doElab stx cmdState msgLog.hasErrors beginPos scope
        return {
          msgLog := .empty
          -- TODO
          tacs := #[]
          finished := .pure {
            msgLog := cmdState.messages
            infoTree? := some cmdState.infoState.trees[0]!
            cmdState
          }
        }

      let next? ← if Parser.isTerminalCommand stx then pure none
        -- for now, wait on "command finished" snapshot before parsing next command
        else some <$> sig.bindIO fun sig => do
          sig.finished.bindIO fun finished =>
            parseCmd none parserState finished.cmdState
      return .mk (next? := next?) {
        msgLog
        stx
        parserState
        stopPos
        sig
      }

  doImport stx := do
    let (headerEnv, msgLog) ← Elab.processHeader stx ctx.opts .empty ictx
    let mut headerEnv := headerEnv
    headerEnv := headerEnv.setMainModule ctx.mainModuleName
    let cmdState := Elab.Command.mkState headerEnv msgLog ctx.opts
    return { cmdState with infoState := {
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

  doElab stx cmdState hasParseError beginPos scope := do
    let cmdStateRef ← IO.mkRef { cmdState with messages := .empty }
    let cmdCtx : Elab.Command.Context := { ictx with
      cmdPos       := beginPos
      tacticCache? := none
    }
    let (output, _) ← IO.FS.withIsolatedStreams (isolateStderr := stderrAsMessages.get scope.opts) <| liftM (m := BaseIO) do
      Elab.Command.catchExceptions
        (getResetInfoTrees *> Elab.Command.elabCommandTopLevel stx)
        cmdCtx cmdStateRef
    let postCmdState ← cmdStateRef.get
    let mut msgs := postCmdState.messages
    -- `stx.hasMissing` should imply `initMsgs.hasErrors`, but the latter should be cheaper to check in general
    if !showPartialSyntaxErrors.get postCmdState.scopes[0]!.opts && hasParseError && stx.hasMissing then
      -- discard elaboration errors, except for a few important and unlikely misleading ones, on parse error
      msgs := ⟨msgs.msgs.filter fun msg =>
        msg.data.hasTag (fun tag => tag == `Elab.synthPlaceholder || tag == `Tactic.unsolvedGoals || (`_traceMsg).isSuffixOf tag)⟩
    if !output.isEmpty then
      msgs := msgs.add {
        fileName := ictx.fileName
        severity := MessageSeverity.information
        pos      := ictx.fileMap.toPosition beginPos
        data     := output
      }
    return { postCmdState with messages := msgs }

partial def getFinalEnv? (snap : InitialSnapshot) : Option Environment := do
  let snap ← snap.success?
  let snap ← snap.next.get.success?
  goCmd snap.next.get
where goCmd snap :=
  if let some next := snap.next? then
    goCmd next.get
  else
    snap.data.sig.get.finished.get.cmdState.env

end Lean

abbrev Lean : Language where
  process := Lean.processLean
  getFinalEnv? := Lean.getFinalEnv?
