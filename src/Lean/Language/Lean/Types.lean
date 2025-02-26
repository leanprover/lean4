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

/-- Snapshot after elaboration of the entire command. -/
structure CommandFinishedSnapshot extends Language.Snapshot where
  /-- Resulting elaboration state. -/
  cmdState : Command.State
deriving Nonempty
instance : ToSnapshotTree CommandFinishedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot, #[]⟩

/-- State after a command has been parsed. -/
structure CommandParsedSnapshot extends Snapshot where
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
  /-- Additional, untyped snapshots used for reporting, not reuse. -/
  reportSnap : SnapshotTask SnapshotTree
  /-- Next command, unless this is a terminal command. -/
  nextCmdSnap? : Option (SnapshotTask CommandParsedSnapshot)
deriving Nonempty
partial instance : ToSnapshotTree CommandParsedSnapshot where
  toSnapshotTree := go where
    go s := ⟨s.toSnapshot,
      #[s.elabSnap.map (sync := true) toSnapshotTree,
        s.finishedSnap.map (sync := true) toSnapshotTree,
        s.reportSnap] |>
        pushOpt (s.nextCmdSnap?.map (·.map (sync := true) go))⟩

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
  snap.result?.bind (·.processedSnap.map (sync := true) (·.result?)) |>.getD (.finished none none)

/-- Initial snapshot of the Lean language processor: a "header parsed" snapshot. -/
abbrev InitialSnapshot := HeaderParsedSnapshot
