/-
Copyright (c) 2023 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The generic interface of a `#lang` language processor used by the language server and cmdline
driver. See the [server readme](../Server/README.md#worker-architecture) for an overview.

Authors: Sebastian Ullrich
-/

prelude
import Init.System.Promise
import Lean.Message
import Lean.Language.Types
import Lean.Elab.InfoTree
import Lean.CoreM

set_option linter.missingDocs true

namespace Lean.Language

/--
Runs `act` with a newly created promise and finally resolves it to `default` if not done by `act`.

Always resolving promises involved in the snapshot tree is important to avoid deadlocking the
language server.
-/
def withAlwaysResolvedPromise [Monad m] [MonadLiftT BaseIO m] [MonadFinally m] [Inhabited α]
    (act : IO.Promise α → m β) : m β := do
  let p ← IO.Promise.new
  try
    act p
  finally
    p.resolve default

/--
Runs `act` with `count` newly created promises and finally resolves them to `default` if not done by
`act`.

Always resolving promises involved in the snapshot tree is important to avoid deadlocking the
language server.
-/
def withAlwaysResolvedPromises [Monad m] [MonadLiftT BaseIO m] [MonadFinally m] [Inhabited α]
    (count : Nat) (act : Array (IO.Promise α) → m Unit) : m Unit := do
  let ps ← List.iota count |>.toArray.mapM fun _ => IO.Promise.new
  try
    act ps
  finally
    for p in ps do
      p.resolve default

/-- Produces trace of given snapshot tree, synchronously waiting on all children. -/
partial def SnapshotTree.trace (s : SnapshotTree) : CoreM Unit :=
  go none s
where go range? s := do
  let file ← getFileMap
  let mut desc := f!"{s.element.desc}"
  if let some range := range? then
    desc := desc ++ f!"{file.toPosition range.start}-{file.toPosition range.stop} "
  desc := desc ++ .prefixJoin "\n• " (← s.element.diagnostics.msgLog.toList.mapM (·.toString))
  if let some t := s.element.infoTree? then
    trace[Elab.info] (← t.format)
  withTraceNode `Elab.snapshotTree (fun _ => pure desc) do
    s.children.toList.forM fun c => go c.range? c.get

/--
  Runs a tree of snapshots to conclusion, incrementally performing `f` on each snapshot in tree
  preorder. -/
@[specialize] partial def SnapshotTree.forM [Monad m] (s : SnapshotTree)
    (f : Snapshot → m PUnit) : m PUnit := do
  match s with
  | mk element children =>
    f element
    children.forM (·.get.forM f)

/--
  Option for printing end position of each message in addition to start position. Used for testing
  message ranges in the test suite. -/
register_builtin_option printMessageEndPos : Bool := {
  defValue := false, descr := "print end position of each message in addition to start position"
}

/-- Reports messages on stdout. If `json` is true, prints messages as JSON (one per line). -/
def reportMessages (msgLog : MessageLog) (opts : Options) (json := false) : IO Unit := do
  if json then
    msgLog.forM (·.toJson <&> (·.compress) >>= IO.println)
  else
    msgLog.forM (·.toString (includeEndPos := printMessageEndPos.get opts) >>= IO.print)

/--
  Runs a tree of snapshots to conclusion and incrementally report messages on stdout. Messages are
  reported in tree preorder.
  This function is used by the cmdline driver; see `Lean.Server.FileWorker.reportSnapshots` for how
  the language server reports snapshots asynchronously.  -/
def SnapshotTree.runAndReport (s : SnapshotTree) (opts : Options) (json := false) : IO Unit := do
  s.forM (reportMessages ·.diagnostics.msgLog opts json)

/-- Waits on and returns all snapshots in the tree. -/
def SnapshotTree.getAll (s : SnapshotTree) : Array Snapshot :=
  s.forM (m := StateM _) (fun s => modify (·.push s)) |>.run #[] |>.2

/-- Creates diagnostics from a single error message that should span the whole file. -/
def diagnosticsOfHeaderError (msg : String) : ProcessingM Snapshot.Diagnostics := do
  let msgLog := MessageLog.empty.add {
    fileName := "<input>"
    pos := ⟨1, 0⟩
    endPos := (← read).fileMap.toPosition (← read).fileMap.source.endPos
    data := msg
  }
  Snapshot.Diagnostics.ofMessageLog msgLog

/--
  Adds unexpected exceptions from header processing to the message log as a last resort; standard
  errors should already have been caught earlier. -/
def withHeaderExceptions (ex : Snapshot → α) (act : ProcessingT IO α) : ProcessingM α := do
  match (← (act (← read)).toBaseIO) with
  | .error e => return ex { diagnostics := (← diagnosticsOfHeaderError e.toString) }
  | .ok a => return a

end Language

/--
  Builds a function for processing a language using incremental snapshots by passing the previous
  snapshot to `Language.process` on subsequent invocations. -/
def Language.mkIncrementalProcessor (process : Option InitSnap → ProcessingM InitSnap) :
    BaseIO (Parser.InputContext → BaseIO InitSnap) := do
  let oldRef ← IO.mkRef none
  return fun ictx => do
    let snap ← process (← oldRef.get) { ictx with }
    oldRef.set (some snap)
    return snap
