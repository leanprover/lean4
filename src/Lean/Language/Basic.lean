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
import Lean.Parser.Types
import Lean.Elab.InfoTree

set_option linter.missingDocs true

namespace Lean.Language

/--
`MessageLog` with interactive diagnostics.

Can be created using `Diagnostics.empty` or `Diagnostics.ofMessageLog`.
-/
structure Snapshot.Diagnostics where
  private mk ::
  /-- Non-interactive message log. -/
  msgLog : MessageLog
  /--
  Dynamic mutable slot usable by the language server for memorizing interactive diagnostics. If
  `none`, interactive diagnostics are not remembered, which should only be used for messages not
  containing any interactive elements as client-side state will be lost on recreating a diagnostic.

  See also section "Communication" in Lean/Server/README.md.
  -/
  interactiveDiagsRef? : Option (IO.Ref (Option Dynamic))
deriving Inhabited

/-- The empty set of diagnostics. -/
def Snapshot.Diagnostics.empty : Snapshot.Diagnostics where
  msgLog := .empty
  -- nothing to memorize
  interactiveDiagsRef? := none

/--
  The base class of all snapshots: all the generic information the language server needs about a
  snapshot. -/
structure Snapshot where
  /-- Debug description shown by `trace.Elab.snapshotTree`, defaults to the caller's decl name. -/
  desc : String := by exact decl_name%.toString
  /--
    The messages produced by this step. The union of message logs of all finished snapshots is
    reported to the user. -/
  diagnostics : Snapshot.Diagnostics
  /-- General elaboration metadata produced by this step. -/
  infoTree? : Option Elab.InfoTree := none
  /--
  Trace data produced by this step. Currently used only by `trace.profiler.output`, otherwise we
  depend on the elaborator adding traces to `diagnostics` eventually.
  -/
  traces : TraceState := {}
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
  /--
  Range that is marked as being processed by the server while the task is running. If `none`,
  the range of the outer task if some or else the entire file is reported.
  -/
  range? : Option String.Range
  /-- Underlying task producing the snapshot. -/
  task : Task α
deriving Nonempty, Inhabited

/-- Creates a snapshot task from a reporting range and a `BaseIO` action. -/
def SnapshotTask.ofIO (range? : Option String.Range) (act : BaseIO α) : BaseIO (SnapshotTask α) := do
  return {
    range?
    task := (← BaseIO.asTask act)
  }

/-- Creates a finished snapshot task. -/
def SnapshotTask.pure (a : α) : SnapshotTask α where
  -- irrelevant when already finished
  range? := none
  task := .pure a

/--
  Explicitly cancels a tasks. Like with basic `Tasks`s, cancellation happens implicitly when the
  last reference to the task is dropped *if* it is not an I/O task. -/
def SnapshotTask.cancel (t : SnapshotTask α) : BaseIO Unit :=
  IO.cancel t.task

/-- Transforms a task's output without changing the reporting range. -/
def SnapshotTask.map (t : SnapshotTask α) (f : α → β) (range? : Option String.Range := t.range?)
    (sync := false) : SnapshotTask β :=
  { range?, task := t.task.map (sync := sync) f }

/--
  Chains two snapshot tasks. The range is taken from the first task if not specified; the range of
  the second task is discarded. -/
def SnapshotTask.bind (t : SnapshotTask α) (act : α → SnapshotTask β)
    (range? : Option String.Range := t.range?) (sync := false) : SnapshotTask β :=
  { range?, task := t.task.bind (sync := sync) (act · |>.task) }

/--
  Chains two snapshot tasks. The range is taken from the first task if not specified; the range of
  the second task is discarded. -/
def SnapshotTask.bindIO (t : SnapshotTask α) (act : α → BaseIO (SnapshotTask β))
    (range? : Option String.Range := t.range?) (sync := false) : BaseIO (SnapshotTask β) :=
  return {
    range?
    task := (← BaseIO.bindTask (sync := sync) t.task fun a => (·.task) <$> (act a))
  }

/-- Synchronously waits on the result of the task. -/
def SnapshotTask.get (t : SnapshotTask α) : α :=
  t.task.get

/-- Returns task result if already finished or else `none`. -/
def SnapshotTask.get? (t : SnapshotTask α) : BaseIO (Option α) :=
  return if (← IO.hasFinished t.task) then some t.task.get else none

/--
Arbitrary value paired with a syntax that should be inspected when considering the value for reuse.
-/
structure SyntaxGuarded (α : Type) where
  /-- Syntax to be inspected for reuse. -/
  stx : Syntax
  /-- Potentially reusable value. -/
  val : α

/--
Pair of (optional) old snapshot task usable for incremental reuse and new snapshot promise for
incremental reporting. Inside the elaborator, we build snapshots by carrying such bundles and then
checking if we can reuse `old?` if set or else redoing the corresponding elaboration step. In either
case, we derive new bundles for nested snapshots, if any, and finally `resolve` `new` to the result.

Note that failing to `resolve` a created promise will block the language server indefinitely!
We use `withAlwaysResolvedPromise`/`withAlwaysResolvedPromises` to ensure this doesn't happen.

In the future, the 1-element history `old?` may be replaced with a global cache indexed by strong
hashes but the promise will still need to be passed through the elaborator.
-/
structure SnapshotBundle (α : Type) where
  /--
  Snapshot task of corresponding elaboration in previous document version if any, paired with its
  old syntax to be considered for reuse. Should be set to `none` as soon as reuse can be ruled out.
  -/
  old? : Option (SyntaxGuarded (SnapshotTask α))
  /--
  Promise of snapshot value for the current document. When resolved, the language server will
  report its result even before the current elaborator invocation has finished.
  -/
  new  : IO.Promise α

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

/--
  Tree of snapshots where each snapshot comes with an array of asynchronous further subtrees. Used
  for asynchronously collecting information about the entirety of snapshots in the language server.
  The involved tasks may form a DAG on the `Task` dependency level but this is not captured by this
  data structure. -/
inductive SnapshotTree where
  /-- Creates a snapshot tree node. -/
  | mk (element : Snapshot) (children : Array (SnapshotTask SnapshotTree))
deriving Inhabited

/-- The immediately available element of the snapshot tree node. -/
abbrev SnapshotTree.element : SnapshotTree → Snapshot
  | mk s _ => s
/-- The asynchronously available children of the snapshot tree node. -/
abbrev SnapshotTree.children : SnapshotTree → Array (SnapshotTask SnapshotTree)
  | mk _ children => children

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
  Helper class for projecting a heterogeneous hierarchy of snapshot classes to a homogeneous
  representation. -/
class ToSnapshotTree (α : Type) where
  /-- Transforms a language-specific snapshot to a homogeneous snapshot tree. -/
  toSnapshotTree : α → SnapshotTree
export ToSnapshotTree (toSnapshotTree)

instance [ToSnapshotTree α] : ToSnapshotTree (Option α) where
  toSnapshotTree
    | some a => toSnapshotTree a
    | none   => default

/-- Snapshot type without child nodes. -/
structure SnapshotLeaf extends Snapshot
deriving Nonempty, TypeName

instance : ToSnapshotTree SnapshotLeaf where
  toSnapshotTree s := SnapshotTree.mk s.toSnapshot #[]

/-- Arbitrary snapshot type, used for extensibility. -/
structure DynamicSnapshot where
  /-- Concrete snapshot value as `Dynamic`. -/
  val  : Dynamic
  /--
  Snapshot tree retrieved from `val` before erasure. We do thunk even the first level as accessing
  it too early can create some unnecessary tasks from `toSnapshotTree` that are otherwise avoided by
  `(sync := true)` when accessing only after elaboration has finished. Early access can even lead to
  deadlocks when later forcing these unnecessary tasks on a starved thread pool.
  -/
  tree : Thunk SnapshotTree

instance : ToSnapshotTree DynamicSnapshot where
  toSnapshotTree s := s.tree.get

/-- Creates a `DynamicSnapshot` from a typed snapshot value. -/
def DynamicSnapshot.ofTyped [TypeName α] [ToSnapshotTree α] (val : α) : DynamicSnapshot where
  val := .mk val
  tree := ToSnapshotTree.toSnapshotTree val

/-- Returns the original snapshot value if it is of the given type. -/
def DynamicSnapshot.toTyped? (α : Type) [TypeName α] (snap : DynamicSnapshot) :
    Option α :=
  snap.val.get? α

instance : Inhabited DynamicSnapshot where
  default := .ofTyped { diagnostics := .empty : SnapshotLeaf }

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

/-- Context of an input processing invocation. -/
structure ProcessingContext extends Parser.InputContext

/-- Monad transformer holding all relevant data for processing. -/
abbrev ProcessingT m := ReaderT ProcessingContext m
/-- Monad holding all relevant data for processing. -/
abbrev ProcessingM := ProcessingT BaseIO

instance : MonadLift ProcessingM (ProcessingT IO) where
  monadLift := fun act ctx => act ctx

/--
Creates snapshot message log from non-interactive message log, also allocating a mutable cell
that can be used by the server to memorize interactive diagnostics derived from the log.
-/
def Snapshot.Diagnostics.ofMessageLog (msgLog : Lean.MessageLog) :
    BaseIO Snapshot.Diagnostics := do
  return { msgLog, interactiveDiagsRef? := some (← IO.mkRef none) }

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
