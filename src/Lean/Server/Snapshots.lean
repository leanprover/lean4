/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Init.System.IO

import Lean.Elab.Import
import Lean.Elab.Command

/-! One can think of this module as being a partial reimplementation
of Lean.Elab.Frontend which also stores a snapshot of the world after
each command. Importantly, we allow (re)starting compilation from any
snapshot/position in the file for interactive editing purposes. -/

namespace Lean
namespace Server
namespace Snapshots

open Elab

/-- The data associated with a snapshot is different depending on whether
it was produced from the header or from a command. -/
inductive SnapshotData
| headerData : Environment → MessageLog → Options → SnapshotData
| cmdData : Command.State → SnapshotData

/-- What Lean knows about the world after the header and each command. -/
structure Snapshot :=
/- Where the command which produced this snapshot begins. Note that
neighbouring snapshots are *not* necessarily attached beginning-to-end,
since inputs outside the grammar advance the parser but do not produce
snapshots. -/
(beginPos : String.Pos)
(mpState : Parser.ModuleParserState)
(data : SnapshotData)

namespace Snapshot

def endPos (s : Snapshot) : String.Pos := s.mpState.pos

def env : Snapshot → Environment
| ⟨_, _, SnapshotData.headerData env_ _ _⟩ => env_
| ⟨_, _, SnapshotData.cmdData cmdState⟩ => cmdState.env

def msgLog : Snapshot → MessageLog
| ⟨_, _, SnapshotData.headerData _ msgLog_ _⟩ => msgLog_
| ⟨_, _, SnapshotData.cmdData cmdState⟩ => cmdState.messages

def toCmdState : Snapshot → Command.State
| ⟨_, _, SnapshotData.headerData env msgLog opts⟩ => Command.mkState env msgLog opts
| ⟨_, _, SnapshotData.cmdData cmdState⟩ => cmdState

end Snapshot

-- TODO(WN): fns here should probably take inputCtx and live
-- in some SnapshotsM := ReaderT Context (EIO Empty)

def compileHeader (contents : String) (opts : Options := {}) : IO Snapshot := do
let inputCtx := Parser.mkInputContext contents "<input>";
(headerStx, headerParserState, msgLog) ← Parser.parseHeader inputCtx;
(headerEnv, msgLog) ← Elab.processHeader headerStx msgLog inputCtx;
pure { beginPos := 0,
       mpState := headerParserState,
       data := SnapshotData.headerData headerEnv msgLog opts
     }

private def ioErrorFromEmpty (ex : Empty) : IO.Error :=
Empty.rec _ ex

/-- Compiles the next command occurring after the given snapshot.
If there is no next command (file ended), returns messages produced
through the file. -/
-- NOTE: This code is really very similar to Elab.Frontend. But generalizing it
-- over "store snapshots"/"don't store snapshots" would likely result in confusing
-- isServer? conditionals and not be worth it due to how short it is.
def compileNextCmd (contents : String) (snap : Snapshot) : IO (Sum Snapshot MessageLog) := do
let inputCtx := Parser.mkInputContext contents "<input>";
let (cmdStx, cmdParserState, msgLog) :=
  Parser.parseCommand snap.env inputCtx snap.mpState snap.msgLog;
let cmdPos := cmdStx.getHeadInfo.get!.pos.get!; -- TODO(WN): always `some`?
if Parser.isEOI cmdStx || Parser.isExitCommand cmdStx then
  pure $ Sum.inr msgLog
else do
  cmdStateRef ← IO.mkRef { snap.toCmdState with messages := msgLog };
  let cmdCtx : Elab.Command.Context :=
    { cmdPos := snap.endPos,
      fileName := inputCtx.fileName,
      fileMap := inputCtx.fileMap
    };
  adaptExcept
    ioErrorFromEmpty
    (Elab.Command.catchExceptions
      (Elab.Command.elabCommand cmdStx)
      cmdCtx cmdStateRef);
  postCmdState ← cmdStateRef.get;
  let postCmdSnap : Snapshot :=
    { beginPos := cmdPos,
      mpState := cmdParserState,
      data := SnapshotData.cmdData postCmdState
    };
  pure $ Sum.inl postCmdSnap

/-- Compiles all commands after the given snapshot. Returns them as a list, together with
the final message log. -/
partial def compileCmdsAfter (contents : String) : Snapshot → IO (List Snapshot × MessageLog)
| snap => do
  cmdOut ← compileNextCmd contents snap;
  match cmdOut with
  | Sum.inl snap => do
    (snaps, msgLog) ← compileCmdsAfter snap;
    pure $ (snap :: snaps, msgLog)
  | Sum.inr msgLog => pure ([], msgLog)

end Snapshots
end Server
end Lean
