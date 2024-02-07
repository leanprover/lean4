/-
Copyright (c) 2023 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The generic interface of a `#lang` language processor used by the language server and cmdline
driver. See the [server readme](../Server/README.md#worker-architecture) for an overview.

Authors: Sebastian Ullrich
-/

import Lean.Message
import Lean.Parser.Types
import Lean.Server.Requests

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

/-- `MessageLog` with caching of interactive diagnostics. -/
structure Snapshot.Diagnostics where
  /-- Non-interactive message log. -/
  msgLog : MessageLog
  /--
  Unique ID used by the file worker for caching diagnostics per message log. If `none`, no caching
  is done, which should only be used for messages not containing any interactive elements.
  -/
  id? : Option Nat
deriving Inhabited

/-- The empty set of diagnostics. -/
def Snapshot.Diagnostics.empty : Snapshot.Diagnostics where
  msgLog := .empty
  -- nothing to cache
  id? := none

/--
  The base class of all snapshots: all the generic information the language server needs about a
  snapshot. -/
structure Snapshot where
  /--
    The messages produced by this step. The union of message logs of all finished snapshots is
    reported to the user. -/
  diagnostics : Snapshot.Diagnostics
  /-- General elaboration metadata produced by this step. -/
  infoTree? : Option Elab.InfoTree := none
  /--
  Whether it should be indicated to the user that a fatal error (which should be part of
  `diagnostics`) occurred that prevents processing of the remainder of the file.
  -/
  isFatal := false
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
  last reference to the task is dropped *if* it is not an I/O task. -/
def SnapshotTask.cancel (t : SnapshotTask α) : BaseIO Unit :=
  IO.cancel t.task

/-- Transforms a task's output without changing the reporting range. -/
def SnapshotTask.map (t : SnapshotTask α) (f : α → β) (range : String.Range := t.range)
    (sync := false) : SnapshotTask β :=
  { range, task := t.task.map (sync := sync) f }

/--
  Chains two snapshot tasks. The range is taken from the first task if not specified; the range of
  the second task is discarded. -/
def SnapshotTask.bind (t : SnapshotTask α) (act : α → SnapshotTask β)
    (range : String.Range := t.range) (sync := false) : SnapshotTask β :=
  { range, task := t.task.bind (sync := sync) (act · |>.task) }

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

instance : ToSnapshotTree Snapshot where
  toSnapshotTree snap := .mk snap #[]

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
  s.element.diagnostics.msgLog.forM
    (·.toString (includeEndPos := printMessageEndPos.get opts) >>= IO.print)
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

/-- Metadata that does not change during the lifetime of the language processing process. -/
structure ModuleProcessingContext where
  /-- Module name of the file being processed. -/
  mainModuleName : Name
  /-- Options provided outside of the file content, e.g. on the cmdline or in the lakefile. -/
  opts : Options
  /-- Kernel trust level. -/
  trustLevel : UInt32 := 0
  /-- Next ID to be used for `Snapshot.Diagnostics.id?`. -/
  nextDiagsIdRef : IO.Ref Nat
  /--
    Callback available in server mode for building imports and retrieving per-library options using
    `lake setup-file`. -/
  fileSetupHandler? : Option (Array Import → IO Server.FileWorker.FileSetupResult)

/-- Context of an input processing invocation. -/
structure ProcessingContext extends ModuleProcessingContext, Parser.InputContext

/-- Monad transformer holding all relevant data for processing. -/
abbrev ProcessingT m := ReaderT ProcessingContext m
/-- Monad holding all relevant data for processing. -/
abbrev ProcessingM := ProcessingT BaseIO

instance : MonadLift ProcessingM (ProcessingT IO) where
  monadLift := fun act ctx => act ctx

/--
Creates snapshot message log from non-interactive message log, caching derived interactive
diagnostics.
-/
def Snapshot.Diagnostics.ofMessageLog (msgLog : Lean.MessageLog) :
    ProcessingM Snapshot.Diagnostics := do
  let id ← (← read).nextDiagsIdRef.modifyGet fun id => (id, id + 1)
  return { msgLog, id? := some id }

/-- Creates diagnostics from a single error message that should span the whole file. -/
def diagnosticsOfHeaderError (msg : String) : ProcessingM Snapshot.Diagnostics := do
  let msgLog := MessageLog.empty.add {
    fileName := "<input>"
    pos := ⟨0, 0⟩
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
  process (old? : Option InitialSnapshot) : ProcessingM InitialSnapshot
  -- TODO: is this the right interface for other languages as well?
  /-- Gets final environment, if any, that is to be used for persisting, code generation, etc. -/
  getFinalEnv? : InitialSnapshot → Option Environment
  /-- Handles a language server request, returning a task that computes the response. -/
  handleRequest (method : String) (params : Json) :
    Server.RequestM InitialSnapshot (Server.RequestTask Json)

instance : Inhabited Language where
  default := {
    InitialSnapshot := Snapshot
    instToSnapshotTree := ⟨fun snap => .mk snap #[]⟩
    process := default
    getFinalEnv? := default
    handleRequest := default
  }

instance (lang : Language) : ToSnapshotTree lang.InitialSnapshot := lang.instToSnapshotTree

/--
  Builds a function for processing a language using incremental snapshots by passing the previous
  snapshot to `Language.process` on subsequent invocations. -/
partial def Language.mkIncrementalProcessor (lang : Language) (ctx : ModuleProcessingContext) :
    BaseIO (Parser.InputContext → BaseIO lang.InitialSnapshot) := do
  let oldRef ← IO.mkRef none
  return fun ictx => do
    let snap ← lang.process (← oldRef.get) { ctx, ictx with }
    oldRef.set (some snap)
    return snap
