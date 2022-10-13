/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
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

/- For `Inhabited Snapshot` -/
builtin_initialize dummyTacticCache : IO.Ref Tactic.Cache ← IO.mkRef {}

/-- What Lean knows about the world after the header and each command. -/
structure Snapshot where
  /-- Where the command which produced this snapshot begins. Note that
  neighbouring snapshots are *not* necessarily attached beginning-to-end,
  since inputs outside the grammar advance the parser but do not produce
  snapshots. -/
  beginPos : String.Pos
  stx : Syntax
  mpState : Parser.ModuleParserState
  cmdState : Command.State
  /-- We cache interactive diagnostics in order not to invoke the pretty-printer again on messages
  from previous snapshots when publishing diagnostics for every new snapshot (this is quadratic),
  as well as not to invoke it once again when handling `$/lean/interactiveDiagnostics`. -/
  interactiveDiags : PersistentArray Widget.InteractiveDiagnostic
  tacticCache : IO.Ref Tactic.Cache

instance : Inhabited Snapshot where
  default := {
    beginPos         := default
    stx              := default
    mpState          := default
    cmdState         := default
    interactiveDiags := default
    tacticCache      := dummyTacticCache
  }

namespace Snapshot

def endPos (s : Snapshot) : String.Pos :=
  s.mpState.pos

def env (s : Snapshot) : Environment :=
  s.cmdState.env

def msgLog (s : Snapshot) : MessageLog :=
  s.cmdState.messages

def diagnostics (s : Snapshot) : PersistentArray Lsp.Diagnostic :=
  s.interactiveDiags.map fun d => d.toDiagnostic

def infoTree (s : Snapshot) : InfoTree :=
  -- the parser returns exactly one command per snapshot, and the elaborator creates exactly one node per command
  assert! s.cmdState.infoState.trees.size == 1
  s.cmdState.infoState.trees[0]!

def isAtEnd (s : Snapshot) : Bool :=
  Parser.isEOI s.stx || Parser.isTerminalCommand s.stx

open Command in
/-- Use the command state in the given snapshot to run a `CommandElabM`.-/
def runCommandElabM (snap : Snapshot) (meta : DocumentMeta) (c : CommandElabM α) : EIO Exception α := do
  let ctx : Command.Context := {
    cmdPos := snap.beginPos,
    fileName := meta.uri,
    fileMap := meta.text,
    tacticCache? := snap.tacticCache,
  }
  c.run ctx |>.run' snap.cmdState

/-- Run a `CoreM` computation using the data in the given snapshot.-/
def runCoreM (snap : Snapshot) (meta : DocumentMeta) (c : CoreM α) : EIO Exception α :=
  snap.runCommandElabM meta <| Command.liftCoreM c

/-- Run a `TermElabM` computation using the data in the given snapshot.-/
def runTermElabM (snap : Snapshot) (meta : DocumentMeta) (c : TermElabM α) : EIO Exception α :=
  snap.runCommandElabM meta <| Command.liftTermElabM c

end Snapshot

/-- Parses the next command occurring after the given snapshot
without elaborating it. -/
def parseNextCmd (inputCtx : Parser.InputContext) (snap : Snapshot) : IO Syntax := do
  let cmdState := snap.cmdState
  let scope := cmdState.scopes.head!
  let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  let (cmdStx, _, _) :=
    Parser.parseCommand inputCtx pmctx snap.mpState snap.msgLog
  return cmdStx

register_builtin_option server.stderrAsMessages : Bool := {
  defValue := true
  group    := "server"
  descr    := "(server) capture output to the Lean stderr channel (such as from `dbg_trace`) during elaboration of a command as a diagnostic message"
}

/-- Compiles the next command occurring after the given snapshot. If there is no next command
(file ended), `Snapshot.isAtEnd` will hold of the return value. -/
-- NOTE: This code is really very similar to Elab.Frontend. But generalizing it
-- over "store snapshots"/"don't store snapshots" would likely result in confusing
-- isServer? conditionals and not be worth it due to how short it is.
def compileNextCmd (inputCtx : Parser.InputContext) (snap : Snapshot) (hasWidgets : Bool) : IO Snapshot := do
  let cmdState := snap.cmdState
  let scope := cmdState.scopes.head!
  let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  let (cmdStx, cmdParserState, msgLog) :=
    Parser.parseCommand inputCtx pmctx snap.mpState snap.msgLog
  let cmdPos := cmdStx.getPos?.get!
  if Parser.isEOI cmdStx then
    let endSnap : Snapshot := {
      beginPos := cmdPos
      stx := cmdStx
      mpState := cmdParserState
      cmdState := snap.cmdState
      interactiveDiags := ← withNewInteractiveDiags msgLog
      tacticCache := snap.tacticCache
    }
    return endSnap
  else
    let cmdStateRef ← IO.mkRef { snap.cmdState with messages := msgLog }
    /- The same snapshot may be executed by different tasks. So, to make sure `elabCommandTopLevel` has exclusive
       access to the cache, we create a fresh reference here. Before this change, the
       following `snap.tacticCache.modify` would reset the tactic post cache while another snapshot was still using it. -/
    let tacticCacheNew ← IO.mkRef (← snap.tacticCache.get)
    let cmdCtx : Elab.Command.Context := {
      cmdPos       := snap.endPos
      fileName     := inputCtx.fileName
      fileMap      := inputCtx.fileMap
      tacticCache? := some tacticCacheNew
    }
    let (output, _) ← IO.FS.withIsolatedStreams (isolateStderr := server.stderrAsMessages.get scope.opts) <| liftM (m := BaseIO) do
      Elab.Command.catchExceptions
        (getResetInfoTrees *> Elab.Command.elabCommandTopLevel cmdStx)
        cmdCtx cmdStateRef
    let postNew := (← tacticCacheNew.get).post
    snap.tacticCache.modify fun _ => { pre := postNew, post := {} }
    let mut postCmdState ← cmdStateRef.get
    if !output.isEmpty then
      postCmdState := {
        postCmdState with
        messages := postCmdState.messages.add {
          fileName := inputCtx.fileName
          severity := MessageSeverity.information
          pos      := inputCtx.fileMap.toPosition snap.endPos
          data     := output
        }
      }
    let postCmdSnap : Snapshot := {
      beginPos := cmdPos
      stx := cmdStx
      mpState := cmdParserState
      cmdState := postCmdState
      interactiveDiags := ← withNewInteractiveDiags postCmdState.messages
      tacticCache := (← IO.mkRef {})
    }
    return postCmdSnap

where
  /-- Compute the current interactive diagnostics log by finding a "diff" relative to the parent
  snapshot. We need to do this because unlike the `MessageLog` itself, interactive diags are not
  part of the command state. -/
  withNewInteractiveDiags (msgLog : MessageLog) : IO (PersistentArray Widget.InteractiveDiagnostic) := do
    let newMsgCount := msgLog.msgs.size - snap.msgLog.msgs.size
    let mut ret := snap.interactiveDiags
    for i in List.iota newMsgCount do
      let newMsg := msgLog.msgs.get! (msgLog.msgs.size - i)
      ret := ret.push (← Widget.msgToInteractiveDiagnostic inputCtx.fileMap newMsg hasWidgets)
    return ret

end Lean.Server.Snapshots
