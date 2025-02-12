/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
prelude
import Init.System.IO

import Lean.Elab.Import
import Lean.Elab.Command

import Lean.Widget.InteractiveDiagnostic

/-! One can think of this module as being a partial reimplementation
of Lean.Elab.Frontend which also stores a snapshot of the world after
each command. Importantly, we allow (re)starting compilation from any
snapshot/position in the file for interactive editing purposes. -/

namespace Lean.Server.Snapshots

open Elab

/-- What Lean knows about the world after the header and each command. -/
structure Snapshot where
  stx : Syntax
  mpState : Parser.ModuleParserState
  cmdState : Command.State

namespace Snapshot

def endPos (s : Snapshot) : String.Pos :=
  s.mpState.pos

def env (s : Snapshot) : Environment :=
  s.cmdState.env

def msgLog (s : Snapshot) : MessageLog :=
  s.cmdState.messages

def infoTree (s : Snapshot) : InfoTree :=
  -- the parser returns exactly one command per snapshot, and the elaborator creates exactly one node per command
  assert! s.cmdState.infoState.trees.size == 1
  s.cmdState.infoState.trees[0]!

def isAtEnd (s : Snapshot) : Bool :=
  Parser.isTerminalCommand s.stx

open Command in
/-- Use the command state in the given snapshot to run a `CommandElabM`.-/
def runCommandElabM (snap : Snapshot) (meta : DocumentMeta) (c : CommandElabM α) : EIO Exception α := do
  let ctx : Command.Context := {
    cmdPos := snap.stx.getPos? |>.getD 0,
    fileName := meta.uri,
    fileMap := meta.text,
    snap? := none
    cancelTk? := none
  }
  c.run ctx |>.run' snap.cmdState

/-- Run a `CoreM` computation using the data in the given snapshot.-/
def runCoreM (snap : Snapshot) (meta : DocumentMeta) (c : CoreM α) : EIO Exception α :=
  snap.runCommandElabM meta <| Command.liftCoreM c

/-- Run a `TermElabM` computation using the data in the given snapshot.-/
def runTermElabM (snap : Snapshot) (meta : DocumentMeta) (c : TermElabM α) : EIO Exception α :=
  snap.runCommandElabM meta <| Command.liftTermElabM c

end Snapshot

end Lean.Server.Snapshots
