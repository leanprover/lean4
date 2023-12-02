/-
Copyright (c) 2023 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The generic interface of a `#lang` language processor used by the language server and cmdline
driver. See the [server readme](../Server/README.md#worker-architecture) for an overview.

Authors: Sebastian Ullrich
-/

import Lean.Message
import Lean.Parser.Types

set_option linter.missingDocs true

-- early declarations for `fileSetupHandler?` below; as the field is used only by the worker, we
-- leave them in that namespace
namespace Lean.Server.FileWorker

/-- Categorizes possible outcomes of running `lake setup-file`. -/
inductive FileSetupResultKind where
  /-- File configuration loaded and dependencies updated successfully. -/
  | success
  /-- No Lake project found, no setup was done. -/
  | noLakefile
  /-- Imports must be rebuilt but `--no-build` was specified. -/
  | importsOutOfDate
  /-- Other error during Lake invocation. -/
  | error (msg : String)

/-- Result of running `lake setup-file`. -/
structure FileSetupResult where
  /-- Kind of outcome. -/
  kind          : FileSetupResultKind
  /-- Search path from successful setup, or else empty. -/
  srcSearchPath : SearchPath
  /-- Additional options from successful setup, or else empty. -/
  fileOptions   : Options

end Lean.Server.FileWorker

namespace Lean.Language

/--
  The base class of all snapshots: all the generic information the language server needs about a
  snapshot. -/
structure Snapshot where
  /--
    The messages produced by this step. The union of message logs of all finished snapshots is
    reported to the user. -/
  msgLog : MessageLog
  /-- General elaboration metadata produced by this step. -/
  infoTree? : Option Elab.InfoTree := none
  -- (`InfoTree` is quite Lean-specific at this point, but we want to make it more generic)
deriving Inhabited

/-- A task producing some snapshot type (usually a subclass of `Snapshot`). -/
-- Longer-term TODO: Give the server more control over the priority of tasks, depending on e.g. the
-- cursor position. This may require starting the tasks suspended (e.g. in `Thunk`). The server may
-- also need more dependency information for this in order to avoid priority inversion.
structure SnapshotTask (α : Type) where
  /-- Range that is marked as being processed by the server while the task is running. -/
  range : String.Range
  /-- Underlying task producing the snapshot. -/
  task : Task α
deriving Nonempty

/-- Creates a snapshot task from a range and a `BaseIO` action. -/
def SnapshotTask.ofIO (range : String.Range) (act : BaseIO α) : BaseIO (SnapshotTask α) := do
  return {
    range
    task := (← BaseIO.asTask act)
  }

/-- Creates a finished snapshot task. -/
def SnapshotTask.pure (a : α) : SnapshotTask α where
  -- irrelevant when already finished
  range := default
  task := .pure a

/--
  Explicitly cancels a tasks. Like with basic `Tasks`s, cancellation happens implicitly when the
  last reference to the task is dropped. -/
def SnapshotTask.cancel (t : SnapshotTask α) : BaseIO Unit :=
  IO.cancel t.task

/-- Transforms a task's output without changing the reporting range. -/
def SnapshotTask.map (t : SnapshotTask α) (f : α → β) (sync := false) : SnapshotTask β :=
  { t with task := t.task.map (sync := sync) f }

/--
  Chains two snapshot tasks. The range is taken from the first task if not specified; the range of
  the second task is discarded. -/
def SnapshotTask.bindIO (t : SnapshotTask α) (act : α → BaseIO (SnapshotTask β))
    (range : String.Range := t.range) (sync := false) : BaseIO (SnapshotTask β) :=
  return { range, task := (← BaseIO.bindTask (sync := sync) t.task fun a => (·.task) <$> (act a)) }

/-- Synchronously waits on the result of the task. -/
def SnapshotTask.get (t : SnapshotTask α) : α :=
  t.task.get

/-- Returns task result if already finished or else `none`. -/
def SnapshotTask.get? (t : SnapshotTask α) : BaseIO (Option α) :=
  return if (← IO.hasFinished t.task) then some t.task.get else none

/--
  Tree of snapshots where each snapshot comes with an array of asynchronous further subtrees. Used
  for asynchronously collecting information about the entirety of snapshots in the language server.
  The involved tasks may form a DAG on the `Task` dependency level but this is not captured by this
  data structure. -/
inductive SnapshotTree where
  /-- Creates a snapshot tree node. -/
  | mk (element : Snapshot) (children : Array (SnapshotTask SnapshotTree))
deriving Nonempty

/-- The immediately available element of the snapshot tree node. -/
abbrev SnapshotTree.element : SnapshotTree → Snapshot
  | mk s _ => s
/-- The asynchronously available children of the snapshot tree node. -/
abbrev SnapshotTree.children : SnapshotTree → Array (SnapshotTask SnapshotTree)
  | mk _ children => children

/--
  Helper class for projecting a heterogeneous hierarchy of snapshot classes to a homogeneous
  representation. -/
class ToSnapshotTree (α : Type) where
  /-- Transforms a language-specific snapshot to a homogeneous snapshot tree. -/
  toSnapshotTree : α → SnapshotTree
export ToSnapshotTree (toSnapshotTree)

/--
  Option for printing end position of each message in addition to start position. Used for testing
  message ranges in the test suite. -/
register_builtin_option printMessageEndPos : Bool := {
  defValue := false, descr := "print end position of each message in addition to start position"
}

/--
  Runs a tree of snapshots to conclusion and incrementally report messages on stdout. Messages are
  reported in tree preorder.
  This function is used by the cmdline driver; see `Lean.Server.FileWorker.reportSnapshots` for how
  the language server reports snapshots asynchronously.  -/
partial def SnapshotTree.runAndReport (s : SnapshotTree) (opts : Options) : IO Unit := do
  s.element.msgLog.forM (·.toString (includeEndPos := printMessageEndPos.get opts) >>= IO.print)
  for t in s.children do
    t.get.runAndReport opts

/-- Waits on and returns all snapshots in the tree. -/
partial def SnapshotTree.getAll (s : SnapshotTree) : Array Snapshot :=
  go s |>.run #[] |>.2
where
  go s : StateM (Array Snapshot) Unit := do
    modify (·.push s.element)
    for t in s.children do
      go t.get

/--
  Returns the value of a snapshot task if it has already finished and otherwise cancels the task.
  Tasks will be canceled implicitly when the last reference to them is dropped but being explicit
  here doesn't hurt. -/
def getOrCancel? (t? : Option (SnapshotTask α)) : BaseIO (Option α) := do
  let some t := t? | return none
  if (← IO.hasFinished t.task) then
    return t.get
  IO.cancel t.task
  return none

/-- Metadata that does not change during the lifetime of the language processing process. -/
structure ProcessingContext where
  /-- Module name of the file being processed. -/
  mainModuleName : Name
  /-- Options provided outside of the file content, e.g. on the cmdline or in the lakefile. -/
  opts : Options
  /-- Kernel trust level. -/
  trustLevel : UInt32 := 0
  /--
    Callback available in server mode for building imports and retrieving per-library options using
    `lake setup-file`. -/
  fileSetupHandler? : Option (Array Import → IO Server.FileWorker.FileSetupResult)

end Language
open Language

/-- Definition of a language processor that can be driven by the cmdline or language server. -/
structure Language where
  /--
    Type of snapshot returned by `process`. It can be converted to a graph of homogeneous snapshot
    types via `ToSnapshotTree`.  -/
  InitialSnapshot : Type
  /-- Instance for transforming the initial snapshot into a snapshot tree for reporting. -/
  [instToSnapshotTree : ToSnapshotTree InitialSnapshot]
  /--
    Processes input into snapshots, potentially reusing information from a previous run.
    Constructing the initial snapshot is assumed to be cheap enough that it can be done
    synchronously, which simplifies use of this function. -/
  process : ProcessingContext → (old? : Option InitialSnapshot) → Parser.InputContext →
    BaseIO InitialSnapshot
  -- TODO: is this the right interface for other languages as well?
  /-- Gets final environment, if any, that is to be used for persisting, code generation, etc. -/
  getFinalEnv? : InitialSnapshot → Option Environment

instance (lang : Language) : ToSnapshotTree lang.InitialSnapshot := lang.instToSnapshotTree

/--
  Builds a function for processing a language using incremental snapshots by passing the previous
  snapshot to `Language.process` on subsequent invocations. -/
partial def Language.mkIncrementalProcessor (lang : Language) (ctx: ProcessingContext) :
    BaseIO (Parser.InputContext → BaseIO lang.InitialSnapshot) := do
  let oldRef ← IO.mkRef none
  return fun doc => do
    let snap ← lang.process ctx (← oldRef.get) doc
    oldRef.set (some snap)
    return snap
