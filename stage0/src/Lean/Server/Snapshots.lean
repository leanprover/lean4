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
  interactiveDiags : Std.PersistentArray Widget.InteractiveDiagnostic
  deriving Inhabited

namespace Snapshot

def endPos (s : Snapshot) : String.Pos :=
  s.mpState.pos

def env (s : Snapshot) : Environment :=
  s.cmdState.env

def msgLog (s : Snapshot) : MessageLog :=
  s.cmdState.messages

def diagnostics (s : Snapshot) : Std.PersistentArray Lsp.Diagnostic :=
  s.interactiveDiags.map fun d => d.toDiagnostic

def isAtEnd (s : Snapshot) : Bool :=
  Parser.isEOI s.stx || Parser.isExitCommand s.stx

end Snapshot

/-- Reparses the header syntax but does not re-elaborate it. Used to ignore whitespace-only changes. -/
def reparseHeader (contents : String) (header : Snapshot) (opts : Options := {}) : IO Snapshot := do
  let inputCtx := Parser.mkInputContext contents "<input>"
  let (newStx, newMpState, _) ← Parser.parseHeader inputCtx
  pure { header with stx := newStx, mpState := newMpState }

private def ioErrorFromEmpty (ex : Empty) : IO.Error :=
  nomatch ex

/-- Parses the next command occurring after the given snapshot
without elaborating it. -/
def parseNextCmd (contents : String) (snap : Snapshot) : IO Syntax := do
  let inputCtx := Parser.mkInputContext contents "<input>"
  let cmdState := snap.cmdState
  let scope := cmdState.scopes.head!
  let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  let (cmdStx, _, _) :=
    Parser.parseCommand inputCtx pmctx snap.mpState snap.msgLog
  cmdStx

/--
  Parse remaining file without elaboration. NOTE that doing so can lead to parse errors or even wrong syntax objects,
  so it should only be done for reporting preliminary results! -/
partial def parseAhead (contents : String) (snap : Snapshot) : IO (Array Syntax) := do
  let inputCtx := Parser.mkInputContext contents "<input>"
  let cmdState := snap.cmdState
  let scope := cmdState.scopes.head!
  let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  go inputCtx pmctx snap.mpState #[]
  where
    go inputCtx pmctx cmdParserState stxs := do
      let (cmdStx, cmdParserState, _) := Parser.parseCommand inputCtx pmctx cmdParserState snap.msgLog
      if Parser.isEOI cmdStx || Parser.isExitCommand cmdStx then
        stxs.push cmdStx
      else
        go inputCtx pmctx cmdParserState (stxs.push cmdStx)

/-- Compiles the next command occurring after the given snapshot. If there is no next command
(file ended), `Snapshot.isAtEnd` will hold of the return value. -/
-- NOTE: This code is really very similar to Elab.Frontend. But generalizing it
-- over "store snapshots"/"don't store snapshots" would likely result in confusing
-- isServer? conditionals and not be worth it due to how short it is.
def compileNextCmd (text : FileMap) (snap : Snapshot) : IO Snapshot := do
  let inputCtx := Parser.mkInputContext text.source "<input>"
  let cmdState := snap.cmdState
  let scope := cmdState.scopes.head!
  let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  let (cmdStx, cmdParserState, msgLog) :=
    Parser.parseCommand inputCtx pmctx snap.mpState snap.msgLog
  let cmdPos := cmdStx.getPos?.get!
  if Parser.isEOI cmdStx || Parser.isExitCommand cmdStx then
    let endSnap : Snapshot := {
      beginPos := cmdPos
      stx := cmdStx
      mpState := cmdParserState
      cmdState := snap.cmdState
      interactiveDiags := ← withNewInteractiveDiags msgLog
    }
    endSnap
  else
    let cmdStateRef ← IO.mkRef { snap.cmdState with messages := msgLog }
    let cmdCtx : Elab.Command.Context := {
      cmdPos   := snap.endPos
      fileName := inputCtx.fileName
      fileMap  := inputCtx.fileMap
    }
    let (output, _) ← IO.FS.withIsolatedStreams do
      EIO.toIO ioErrorFromEmpty do
        Elab.Command.catchExceptions
          (Elab.Command.elabCommandTopLevel cmdStx)
          cmdCtx cmdStateRef
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
    }
    postCmdSnap

where
  /-- Compute the current interactive diagnostics log by finding a "diff" relative to the parent
  snapshot. We need to do this because unlike the `MessageLog` itself, interactive diags are not
  part of the command state. -/
  withNewInteractiveDiags (msgLog : MessageLog) : IO (Std.PersistentArray Widget.InteractiveDiagnostic) := do
    let newMsgCount := msgLog.msgs.size - snap.msgLog.msgs.size
    let mut ret := snap.interactiveDiags
    for i in List.iota newMsgCount do
      let newMsg := msgLog.msgs.get! (msgLog.msgs.size - i)
      ret := ret.push (← Widget.msgToInteractiveDiagnostic text newMsg)
    return ret

end Lean.Server.Snapshots
