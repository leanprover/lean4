/-
Copyright (c) 2023 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Implementation of the Lean language: parsing and processing of header and commands, incremental
recompilation

Authors: Sebastian Ullrich
-/

prelude
import Lean.Language.Basic
import Lean.Elab.Command

set_option linter.missingDocs true

namespace Lean.Language.Lean
open Lean.Elab Command
open Lean.Parser

private def pushOpt (a? : Option α) (as : Array α) : Array α :=
  match a? with
  | some a => as.push a
  | none   => as

/-! The hierarchy of Lean snapshot types -/

/--
Snapshot after command elaborator has returned. Also contains diagnostics from the elaborator's main
task. Asynchronous elaboration tasks may not yet be finished.
-/
structure CommandResultSnapshot extends Language.Snapshot where
  /-- Resulting elaboration state. -/
  cmdState : Command.State
deriving Nonempty
instance : ToSnapshotTree CommandResultSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot, #[]⟩

/--
State before a command is elaborated. This is separate from `CommandParsedSnapshot` so that all
snapshots belonging to a command are grouped below a task with the command's syntax tree.
-/
structure CommandElaboratingSnapshot extends Snapshot where
  /--
  Snapshot for incremental reporting and reuse during elaboration, type dependent on specific
  elaborator.
   -/
  elabSnap : SnapshotTask DynamicSnapshot
  /-- State after command elaborator has returned. -/
  resultSnap : SnapshotTask CommandResultSnapshot
  /--
  State after all elaborator tasks are finished. In particular, contains the complete info tree.
  -/
  infoTreeSnap : SnapshotTask SnapshotLeaf
  /-- Additional, untyped snapshots used for reporting, not reuse. -/
  reportSnap : SnapshotTask SnapshotTree
deriving Nonempty
instance : ToSnapshotTree CommandElaboratingSnapshot where
  toSnapshotTree := go where
    go s := ⟨s.toSnapshot,
      #[s.elabSnap.map (sync := true) toSnapshotTree,
        s.resultSnap.map (sync := true) toSnapshotTree,
        s.infoTreeSnap.map (sync := true) toSnapshotTree,
        s.reportSnap]⟩

/-- State after a command has been parsed. -/
structure CommandParsedSnapshot extends Snapshot where
  /-- Syntax tree of the command. -/
  stx : Syntax
  /-- Resulting parser state. -/
  parserState : Parser.ModuleParserState
  /-- State before the command is elaborated. This snapshot is always fulfilled immediately. -/
  elabSnap : CommandElaboratingSnapshot
  /-- Next command, unless this is a terminal command. -/
  nextCmdSnap? : Option (SnapshotTask CommandParsedSnapshot)
deriving Nonempty
partial instance : ToSnapshotTree CommandParsedSnapshot where
  toSnapshotTree := go where
    go s := ⟨s.toSnapshot,
      #[.finished s.stx (toSnapshotTree s.elabSnap)] |>
        pushOpt (s.nextCmdSnap?.map (·.map (sync := true) go))⟩

/-- State after successful importing. -/
structure HeaderProcessedState where
  /-- The resulting initial elaboration state. -/
  cmdState : Command.State
  /-- First command task (there is always at least a terminal command). -/
  firstCmdSnap : SnapshotTask CommandParsedSnapshot

/-- State after the module header has been processed including imports. -/
structure HeaderProcessedSnapshot extends Snapshot where
  /--
  Holds produced diagnostics and info tree. Separate snapshot so that it can be tagged with the
  header syntax, which should not be done for this snapshot containing `firstCmdSnap`.
  -/
  metaSnap : SnapshotTask SnapshotLeaf
  /-- State after successful importing. -/
  result? : Option HeaderProcessedState
  isFatal := result?.isNone
instance : ToSnapshotTree HeaderProcessedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot, #[s.metaSnap.map (sync := true) toSnapshotTree] |>
    pushOpt (s.result?.map (·.firstCmdSnap.map (sync := true) toSnapshotTree))⟩

/-- State after successfully parsing the module header. -/
structure HeaderParsedState where
  /-- Resulting parser state. -/
  parserState : Parser.ModuleParserState
  /-- Header processing task. -/
  processedSnap : SnapshotTask HeaderProcessedSnapshot

/-- State after the module header has been parsed. -/
structure HeaderParsedSnapshot extends Snapshot where
  /--
  Holds produced diagnostics. Separate snapshot so that it can be tagged with the header syntax,
  which should not be done for this snapshot containing `firstCmdSnap`.
  -/
  metaSnap : SnapshotTask SnapshotLeaf
  /-- Parser input context supplied by the driver, stored here for incremental parsing. -/
  ictx : Parser.InputContext
  /-- Resulting syntax tree. -/
  stx : Syntax
  /-- State after successful parsing. -/
  result? : Option HeaderParsedState
  isFatal := result?.isNone

instance : ToSnapshotTree HeaderParsedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot, #[s.metaSnap.map (sync := true) toSnapshotTree] |>
    pushOpt (s.result?.map (·.processedSnap.map (sync := true) toSnapshotTree))⟩

/-- Shortcut accessor to the final header state, if successful. -/
def HeaderParsedSnapshot.processedResult (snap : HeaderParsedSnapshot) :
    SnapshotTask (Option HeaderProcessedState) :=
  snap.result?.bind (·.processedSnap.map (sync := true) (·.result?)) |>.getD (.finished none none)

/-- Initial snapshot of the Lean language processor: a "header parsed" snapshot. -/
abbrev InitialSnapshot := HeaderParsedSnapshot
